#!/bin/bash
# sequential runs: args "c,e,prime,dmax"; internal guard 2400MB, external 3000MB, 285s
cd "$(dirname "$0")"
for spec in "$@"; do
  IFS=, read c e pi dm <<< "$spec"
  perl -e 'alarm 290; exec @ARGV' ../runcap.sh 3000 285 ./target/release/wt_growth $c $e $dm $pi 2400 runs/c${c}e${e}_p${pi}.txt > runs/c${c}e${e}_p${pi}.log 2>&1
  tail -1 runs/c${c}e${e}_p${pi}.txt
done
echo LAB2DONE
