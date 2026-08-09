#!/bin/bash
# emit_lean.sh -- turn the rank certificates of `nodfinite` into Lean data.
#
# Usage:  emit_lean.sh certificates.txt "3,7 4,6 5,5 6,4 7,3 9,2"
#
# Reads the certificate file produced by `nodfinite` (one line per (k,m) pair,
# format `(k, m, [row indices], [[inverse matrix rows]]),`) and writes, for each
# requested pair, the two Lean definitions consumed by
# lean/with_mathlib/NoDFiniteData.lean:
#
#     def rows_k_m : List Nat := [...]
#     def minv_k_m : List (List Nat) := [[...], ...]
#
# Output goes to stdout.  The certificate entries are already reduced modulo
# p = 2^31 - 1 and are therefore nonnegative, which is why the Lean side can
# work in Nat throughout.

set -euo pipefail

CERTS="${1:?usage: emit_lean.sh <certificates.txt> \"k,m k,m ...\"}"
PAIRS="${2:?usage: emit_lean.sh <certificates.txt> \"k,m k,m ...\"}"

for pair in $PAIRS; do
    k="${pair%,*}"
    m="${pair#*,}"
    awk -v K="$k" -v M="$m" '
    {
        line = $0
        sub(/^\(/, "", line)
        sub(/\),$/, "", line)
        # k
        i = index(line, ","); kk = substr(line, 1, i-1); line = substr(line, i+1)
        # m
        i = index(line, ","); mm = substr(line, 1, i-1); line = substr(line, i+1)
        gsub(/ /, "", kk); gsub(/ /, "", mm)
        if (kk != K || mm != M) next
        # rows: from the first "[" to the first "]"
        a = index(line, "["); b = index(line, "]")
        rows = substr(line, a, b - a + 1)
        rest = substr(line, b + 2)
        # inverse: the remainder, "[[...],...,[...]]" possibly with a leading space
        sub(/^ */, "", rest)
        printf("def rows_%s_%s : List Nat :=\n  %s\n\n", K, M, rows)
        printf("def minv_%s_%s : List (List Nat) :=\n  %s\n\n", K, M, rest)
        found = 1
        exit
    }
    END { if (!found) { printf("-- MISSING CERTIFICATE FOR (%s, %s)\n", K, M) > "/dev/stderr"; exit 1 } }
    ' "$CERTS"
done
