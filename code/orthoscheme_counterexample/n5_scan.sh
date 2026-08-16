#!/bin/bash
cd "/Users/vico/Documents/elvec1o/certify_run/code/zeta_probe/tools/pointgroup"
tot=0; fail=0
while read t; do
  IFS=, read a b c d e <<< "$t"; tot=$((tot+1))
  out=$(./target/release/pointgroup $t 12 200000000 1400 2>&1)
  dev=$(echo "$out"|grep -o "first deviates at depth [0-9]*"|head -1|grep -o "[0-9]*$")
  [ -z "$dev" ] && continue
  fail=$((fail+1))
  # test the n=4 loci read on consecutive 4-windows
  f1a=$((a*c-b*d)); f1b=$((b*d-c*e))
  echo "  ($t) dev=$dev  a1a3-a2a4=$f1a  a2a4-a3a5=$f1b"
done < /private/tmp/claude-501/-Users-vico-Documents-elvec1o-XXXXX-MATH-PROOF/600297f0-1b03-4b2c-8747-bbf6af9b3120/scratchpad/t5.txt
echo "TOTAL tested $tot ; failures $fail"
