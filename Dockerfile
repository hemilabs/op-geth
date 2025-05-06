# Support setting various labels on the final image
ARG COMMIT=""
ARG VERSION=""
ARG BUILDNUM=""

# Build Geth in a stock Go builder container
FROM golang:1.24.2-alpine3.21@sha256:7772cb5322baa875edd74705556d08f0eeca7b9c4b5367754ce3f2f00041ccee AS builder

RUN apk add --no-cache gcc musl-dev linux-headers git ca-certificates tzdata

# Get dependencies - will also be cached if we won't change go.mod/go.sum
COPY go.mod /go-ethereum/
COPY go.sum /go-ethereum/
RUN cd /go-ethereum && go mod download

ADD . /go-ethereum
RUN cd /go-ethereum && go run build/ci.go install -static ./cmd/geth

# Create non-root user
RUN addgroup --gid 65532 geth && \
    adduser --disabled-password --gecos "" \
        --home "/go-ethereum/" --shell "/sbin/nologin" \
        -G geth --uid 65532 geth

# Pull Geth into a second stage deploy stratch container
FROM alpine:3.20@sha256:77726ef6b57ddf65bb551896826ec38bc3e53f75cdde31354fbffb4f25238ebd

COPY --from=builder /etc/group /etc/group
COPY --from=builder /etc/passwd /etc/passwd
COPY --from=builder /etc/ssl/certs/ca-certificates.crt /etc/ssl/certs/
COPY --from=builder /usr/share/zoneinfo /usr/share/zoneinfo
COPY --from=builder /go-ethereum/build/bin/geth /usr/local/bin/geth

EXPOSE 8545 8546 30303 30303/udp

# Add some metadata labels to help programmatic image consumption
ARG COMMIT=""
ARG VERSION=""
ARG BUILDNUM=""

LABEL commit="$COMMIT" version="$VERSION" buildnum="$BUILDNUM"

USER geth:geth
WORKDIR /go-ethereum/
ENTRYPOINT ["/usr/local/bin/geth"]
