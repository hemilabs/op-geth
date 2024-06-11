# Support setting various labels on the final image
ARG COMMIT=""
ARG VERSION=""
ARG BUILDNUM=""

# Build Geth in a stock Go builder container
FROM golang:1.22.3-alpine@sha256:f1fe698725f6ed14eb944dc587591f134632ed47fc0732ec27c7642adbe90618 as builder

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
FROM alpine:latest

COPY --from=builder /etc/group /etc/group
COPY --from=builder /etc/passwd /etc/passwd
COPY --from=builder /etc/ssl/certs/ca-certificates.crt /etc/ssl/certs/
COPY --from=builder /usr/share/zoneinfo /usr/share/zoneinfo
COPY --from=builder /go-ethereum/build/bin/geth /usr/local/bin/geth

EXPOSE 8545 8546 30303 30303/udp

# Add some metadata labels to help programatic image consumption
ARG COMMIT=""
ARG VERSION=""
ARG BUILDNUM=""

LABEL commit="$COMMIT" version="$VERSION" buildnum="$BUILDNUM"

USER geth:geth
WORKDIR /go-ethereum/
ENTRYPOINT ["/usr/local/bin/geth"]
