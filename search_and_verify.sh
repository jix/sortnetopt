#!/bin/bash

if [[ -z "$2" ]]; then
    echo "usage: bash search_and_verify.sh CHANNELS DATADIR"
    exit 1
fi

set -euo pipefail

CHANNELS="$1"
DATADIR=$(realpath "$2")

cd "$(dirname "$0")"

if [[ ! -d "$DATADIR" ]]; then
    mkdir "$DATADIR"
fi

echo "Building sortnetopt binary..."

cargo build --release

echo "Searching lower bound..."

cargo run --release -- -m search "$CHANNELS" "$DATADIR/_search_$CHANNELS"

echo "Pruning search log..."

cargo run --release -- -m prune-all "$DATADIR/_search_$CHANNELS"

echo "Generating proof certificate..."

cargo run --release -- -m gen-proof "$DATADIR/_search_$CHANNELS"

echo "Verifying proof certificate..."

bash verify_proof_cert.sh "$DATADIR/_search_$CHANNELS/proof.bin"
