#!/usr/bin/env bash
# Build the Lean files for the triangle reflection paper.
#
# The first three files import nothing and are checked directly. The files
# under with_mathlib/ import Mathlib, and Bridge.lean also imports
# RotationRelations, so those need a Mathlib build and an olean search path.
#
# Point MATHLIB_PACKAGES at the .lake/packages directory of any Lean 4.30
# project that has Mathlib built, for example
#   MATHLIB_PACKAGES=~/some-project/.lake/packages ./build.sh
set -euo pipefail
cd "$(dirname "$0")"

LEANBIN="${LEANBIN:-lean}"
OUT="${OUT:-build}"
mkdir -p "$OUT"

echo "== core Lean, no imports =="
for f in TriangleFlowMetric EulerCircuit RotationRelations; do
  "$LEANBIN" -o "$OUT/$f.olean" "$f.lean"
  echo "   ok  $f.lean"
done

if [ -z "${MATHLIB_PACKAGES:-}" ]; then
  echo "== with_mathlib/ skipped: set MATHLIB_PACKAGES to a built Mathlib =="
  exit 0
fi

LP=""
for d in "$MATHLIB_PACKAGES"/*/.lake/build/lib/lean; do
  [ -d "$d" ] && LP="$LP$d:"
done
if [ -z "$LP" ]; then
  echo "no built packages under $MATHLIB_PACKAGES" >&2
  exit 1
fi
export LEAN_PATH="$LP$PWD/$OUT"

echo "== with Mathlib =="
for f in CoxeterTorsion Bridge; do
  [ -f "with_mathlib/$f.lean" ] || continue
  "$LEANBIN" -o "$OUT/$f.olean" "with_mathlib/$f.lean"
  echo "   ok  with_mathlib/$f.lean"
done

echo "== all files built, no sorry =="
