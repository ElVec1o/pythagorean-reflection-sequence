#!/bin/bash
# sequential laboratory runs; each capped (RSS 3000MB external, 2800MB internal guard, 285s wall)
cd "$(dirname "$0")"
for ce in "$@"; do
  c=${ce%,*}; e=${ce#*,}
  perl -e 'alarm 290; exec @ARGV' ../runcap.sh 3000 285 ./target/release/wt_growth $c $e 120 0 2800 runs/c${c}e${e}_p0.txt > runs/c${c}e${e}_p0.log 2>&1
  tail -2 runs/c${c}e${e}_p0.txt
done
echo LABDONE
