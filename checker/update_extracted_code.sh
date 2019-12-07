#!/bin/bash

set -euo pipefail

cd "$(dirname "$0")"

cd verified

echo "Running isabelle build ..."
isabelle build -D . -e

echo "-- Generated using update_extracted_code.sh, do not edit --" \
    > ../snocheck/src/Verified/Checker.hs

echo "Patch extracted source..."
patch -o- \
    export/Sorting_Networks.Checker_Codegen/code/checker/Verified/Checker.hs \
    strict_and_parallel.patch >> ../snocheck/src/Verified/Checker.hs

echo <<'EOM'
  The patch adds strictness annotations to a datatype and replaces
  `par a b = b` with `par = Control.Parallel.par`.

  Both changes only affect the evaluation order.
EOM
