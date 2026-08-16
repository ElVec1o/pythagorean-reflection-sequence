#!/bin/bash
cd "/Users/vico/Documents/elvec1o/certify_run/code/zeta_probe/tools/pointgroup"
tot=0; fail=0; unexp=0
while read t; do
  IFS=, read a b c d <<< "$t"; tot=$((tot+1))
  out=$(./target/release/pointgroup $t 13 200000000 1200 2>&1)
  dev=$(echo "$out"|grep -o "first deviates at depth [0-9]*"|head -1|grep -o "[0-9]*$")
  [ -z "$dev" ] && continue
  fail=$((fail+1))
  f1=$((a*c-b*d))
  l2=$((d*(a*a-b*b))); r2=$((2*a*b*c))
  l3=$((a*(c*c-d*d))); r3=$((2*b*c*d))
  if [ $f1 -eq 0 ]; then fam=I
  elif [ $((l2-r2)) -eq 0 ] || [ $((l2+r2)) -eq 0 ]; then fam=II
  elif [ $((l3-r3)) -eq 0 ] || [ $((l3+r3)) -eq 0 ]; then fam=III
  else fam=UNEXPLAINED; unexp=$((unexp+1)); fi
  echo "  ($t) dev=$dev family=$fam"
done < /private/tmp/claude-501/-Users-vico-Documents-elvec1o-XXXXX-MATH-PROOF/600297f0-1b03-4b2c-8747-bbf6af9b3120/scratchpad/tuples12.txt
echo "TOTAL tested $tot ; failures $fail ; unexplained $unexp"
