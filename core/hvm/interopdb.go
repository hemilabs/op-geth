package hvm

import (
	"database/sql"
	"fmt"
	"github.com/ethereum/go-ethereum/log"
	"github.com/jmoiron/sqlx"
	_ "github.com/lib/pq"
)

type HvmDb interface {
	GetBtcAddrUtxos(addr string, pg uint32, pgsize uint32) ([]DbOutput, error)
	GetBtcAddrBal(addr string) (uint64, error)
	GetTxByTxid(txid []byte) (*FullTransaction, error)
}

type PGHvmDb struct {
	pguri string
	db    *sqlx.DB
}

func (p *PGHvmDb) DB() *sqlx.DB {
	return p.db
}

func NewPGHvmDb(pguri string) *PGHvmDb {
	hvmdb := PGHvmDb{
		pguri: pguri,
	}

	return &hvmdb
}

func (h *PGHvmDb) Connect() error {
	db, err := sqlx.Connect("postgres", h.pguri)

	if err != nil {
		return err
	}

	if err := db.Ping(); err != nil {
		log.Error("Unable to ping hVM database!")
		return err
	}

	h.db = db
	return nil
}

func (h *PGHvmDb) GetTxByTxid(txid []byte) (*FullTransaction, error) {
	// TODO: Extract these queries to helper methods so they can be reused for other HVM queries
	dbTxQuery := fmt.Sprintf("SELECT * FROM txes WHERE txid=DECODE('%x', 'hex')", txid)

	dbTxRows, err := h.db.Queryx(dbTxQuery)
	if err != nil {
		log.Warn("unable to fetch transaction data from txes table", "transaction", fmt.Sprintf("%x", txid))
		return nil, err
	}
	defer dbTxRows.Close()

	dbTx := DbTransaction{}
	if dbTxRows.Next() {
		err := dbTxRows.StructScan(&dbTx)
		if err != nil {
			return nil, nil // TODO: Error handling
		}
	} else {
		log.Warn("Error scanning query from txes table", "transaction", fmt.Sprintf("%x", txid), "err", err)
		return nil, nil // TODO: Err
	}

	contBlockQuery := fmt.Sprintf("SELECT * FROM blocks WHERE hash=DECODE('%x', 'hex')", dbTx.Block)

	contBlockRows, err := h.db.Queryx(contBlockQuery)
	if err != nil {
		log.Warn("unable to fetch containing block data from blocks table", "block",
			fmt.Sprintf("%x", dbTx.Block), "tx", fmt.Sprintf("%x", txid))
		return nil, err
	}
	defer contBlockRows.Close()

	dbContBlock := DbBlock{}
	if contBlockRows.Next() {
		err := contBlockRows.StructScan(&dbContBlock)
		if err != nil {
			return nil, nil // TODO: Error handling
		}
	} else {
		log.Warn("Error scanning query from blocks table looking for containing block",
			"transaction", fmt.Sprintf("%x", txid), "err", err)
		return nil, nil // TODO: Err
	}

	// TODO: Better query, or keep separate entry for tip in db
	tipBlockQuery := fmt.Sprintf("SELECT * FROM blocks ORDER BY height DESC LIMIT 1")

	tipBlockRows, err := h.db.Queryx(tipBlockQuery)
	if err != nil {
		log.Warn("unable to fetch tip block data from blocks table")
		return nil, err
	}
	defer tipBlockRows.Close()

	dbTipBlock := DbBlock{}
	if tipBlockRows.Next() {
		err := tipBlockRows.StructScan(&dbTipBlock)
		if err != nil {
			return nil, nil // TODO: Error handling
		}
	} else {
		log.Warn("Error scanning query from blocks table looking for tip")
		return nil, nil // TODO: Err
	}

	inputsQuery := fmt.Sprintf("SELECT * FROM outputs WHERE spendtx=DECODE('%x', 'hex') ORDER BY spendindex ASC", txid)

	inputRows, err := h.db.Queryx(inputsQuery)
	if err != nil {
		log.Warn("unable to fetch outputs spent by transaction", "transaction", fmt.Sprintf("%x", txid))
	}
	defer inputRows.Close()

	var inputs []Input
	for inputRows.Next() {
		o := DbOutput{}
		err := inputRows.StructScan(&o)
		if err != nil {
			log.Warn("Error scanning query for inputs from outputs table", "transaction", fmt.Sprintf("%x", txid), "err", err)
			return nil, err
		}

		sequence := uint32(0)
		if o.Sequence.Valid {
			sequence = uint32(o.Sequence.Int64)
		}

		input := Input{
			Coinbase:    false,  // TODO: Implement in db, currently no Coinbase inputs returned
			Txid:        o.Txid, // Input references TxID of origination transaction
			SourceIndex: o.OutputIndex,
			ScriptSig:   o.ScriptSig,
			Sequence:    sequence,
			Value:       o.Value,
		}

		inputs = append(inputs, input)
	}

	outputsQuery := fmt.Sprintf("SELECT * FROM outputs WHERE txid=DECODE('%x', 'hex') ORDER BY outputindex ASC", txid)

	outputRows, err := h.db.Queryx(outputsQuery)
	if err != nil {
		log.Warn("unable to fetch outputs created by transaction", "transaction", fmt.Sprintf("%x", txid))
	}
	defer outputRows.Close()

	var outputs []Output
	for outputRows.Next() {
		o := DbOutput{}
		err := outputRows.StructScan(&o)
		if err != nil {
			log.Warn("Error scanning query for outputs from outputs table", "transaction", fmt.Sprintf("%x", txid), "err", err)
			return nil, err
		}

		spendIndex := uint32(0) // TODO: Max value and throw error if not changed
		if o.SpendIndex.Valid {
			spendIndex = uint32(o.SpendIndex.Int32)
		}

		output := Output{
			Txid:        o.Txid,
			OutputIndex: o.OutputIndex,
			Value:       o.Value,
			Spent:       o.Spent,
			SpendScript: o.SpendScript,
			SpendIndex:  spendIndex,
			Address:     &o.Address.String,
			SpendTx:     o.SpendTx,
		}

		outputs = append(outputs, output)
	}

	// TODO: Error handling if inputs or outputs have 0 rows

	transaction := FullTransaction{
		Txid:          dbTx.Txid,
		Size:          dbTx.Size,
		VSize:         dbTx.VSize,
		Version:       dbTx.Version,
		NLockTime:     dbTx.NLockTime,
		Block:         dbTx.Block,
		BlockIndex:    dbContBlock.Height,
		Confirmations: dbTipBlock.Height - dbContBlock.Height,
		Inputs:        inputs,
		Outputs:       outputs,
	}

	return &transaction, nil
}

type balResp struct {
	sum uint64 `db:"sum"`
}

func (h *PGHvmDb) GetBtcAddrUtxos(addr string, pg uint32, pgsize uint32) ([]DbOutput, error) {
	// TODO: Review pagination efficiency
	query := fmt.Sprintf("SELECT * FROM outputs WHERE address='%s' AND spent=false ORDER BY createBlock DESC, txindex DESC LIMIT %d OFFSET %d", addr, pgsize, pg*pgsize)
	rows, err := h.db.Queryx(query)
	if err != nil {
		return nil, err
	}
	defer rows.Close()

	var utxos []DbOutput
	for rows.Next() {
		o := DbOutput{}
		err := rows.StructScan(&o)
		if err != nil {
			log.Warn("unable to read a database row while getting UTXOs for BTC address %s, err: %v", addr, err)
			return nil, nil // TODO: Error handling
		}

		if o.Spent == false {
			utxos = append(utxos, o)
		}
	}

	return utxos, nil
}

type Sum struct {
	Sum uint64 `db:"sum"`
}

func (h *PGHvmDb) GetBtcAddrBal(addr string) (uint64, error) {
	query := fmt.Sprintf("SELECT COALESCE(SUM(value), 0) as sum FROM outputs WHERE address='%s' AND spent=false", addr)

	rows, err := h.db.Queryx(query)
	if err != nil {
		return 0, err
	}
	defer rows.Close()

	sum := Sum{}
	if rows.Next() {
		err := rows.StructScan(&sum)
		if err != nil {
			return 0, nil // TODO: Error handling
		}

		return sum.Sum, nil
	}

	return 0, nil
}

type DbBlock struct {
	Hash       []byte `db:"hash"`
	Height     uint32 `db:"height"`
	MerkleRoot []byte `db:"merkleroot"`
	Timestamp  uint32 `db:"timestamp"`
	NumTx      uint32 `db:"numtx"`
}

type Input struct {
	Coinbase    bool // TODO: Implement in DB
	Txid        []byte
	SourceIndex uint32
	ScriptSig   []byte
	Sequence    uint32
	Value       uint64
}

type DbOutput struct {
	Txid        []byte         `db:"txid"`
	OutputIndex uint32         `db:"outputindex"`
	TxIndex     uint32         `db:"txindex"`
	Value       uint64         `db:"value"`
	Spent       bool           `db:"spent"`
	SpendScript []byte         `db:"spendscript"`
	CreateBlock uint32         `db:"createblock"`
	Address     sql.NullString `db:"address"`
	ScriptSig   []byte         `db:"scriptsig"`
	Witness     []byte         `db:"witness"`
	SpendTx     []byte         `db:"spendtx"`
	SpendIndex  sql.NullInt32  `db:"spendindex"`
	Sequence    sql.NullInt64  `db:"sequence"`
}

type Output struct {
	Txid        []byte
	OutputIndex uint32
	Value       uint64
	Spent       bool
	SpendScript []byte
	SpendIndex  uint32
	Address     *string
	SpendTx     []byte
}

type FullTransaction struct {
	Txid          []byte
	Size          uint32
	VSize         uint32
	Version       uint32
	NLockTime     uint32
	Block         []byte
	BlockIndex    uint32
	Confirmations uint32
	Inputs        []Input
	Outputs       []Output
}

type DbTransaction struct {
	Txid      []byte `db:"txid"`
	Size      uint32 `db:"size"`
	VSize     uint32 `db:"vsize"`
	Version   uint32 `db:"version"`
	NLockTime uint32 `db:"nlocktime"`
	Block     []byte `db:"block"`
	Index     uint32 `db:"index"`
}
