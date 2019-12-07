#!/bin/bash

if [[ -z "$1" ]]; then
    echo "usage: bash verify_proof_cert.sh CERTBIN"
    exit 1
fi

CERTBIN="$1"

set -euo pipefail

SWD=$(pwd)

cd "$(dirname "$0")"

cd checker/snocheck

echo 'Running verified proof certificate checker...'
echo
echo 'An output of `None` indicates verification failure.'
echo 'An output of `Some (w,b)` indicates successful verification of the'
echo 'lower bound b for w channels.'
echo

stack run --cwd "$SWD" -- -v "$CERTBIN"
