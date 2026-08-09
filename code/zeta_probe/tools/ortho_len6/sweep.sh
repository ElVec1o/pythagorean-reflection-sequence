#!/bin/bash
# Exhaustive length-6 kernel census over boxes of integer leg tuples.
# Every positive rational tuple scales to a primitive integer tuple and rho_a(w) = 1 is
# scale invariant, so the boxes below cover every rational orthoscheme with legs in the
# stated ratio range.
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
CAP="$HERE/../runcap.sh"
BIN="$HERE/target/release/ortho_len6"

run () {  # run <n> <L>
    echo "=================== n=$1  L=$2 ==================="
    bash "$CAP" 3000 3600 "$BIN" "$1" "$2" --quiet
}

run 3 200
run 4 40
run 5 14
run 6 8
run 7 5
run 8 4
echo "=================== sweep complete ==================="
