package hvm

type output struct {
	txid        []byte
	index       uint32
	value       uint64
	spendScript []byte
	address     string
	scriptsig   []byte
	spent       bool
	spendtx     []byte
}
