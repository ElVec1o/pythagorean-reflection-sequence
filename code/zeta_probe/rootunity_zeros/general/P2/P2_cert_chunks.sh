#!/bin/bash
# P2_cert_chunks.sh a N t0re t0im R0 M n0 prec chunk logfile : run P2_cert.py 'pieces' in chunks, each under alarm 290 s.
a=$1; N=$2; tr=$3; ti=$4; R0=$5; M=$6; n0=$7; prec=$8; ch=$9; log=${10}
i=0
while [ $i -lt $M ]; do
  j=$((i+ch))
  perl -e 'alarm 290; exec @ARGV' python3 P2_cert.py pieces $a $N $tr $ti $R0 $M $n0 $prec $i $j >> "$log" 2>&1 || { echo "chunk $i failed" >> "$log"; exit 1; }
  i=$j
done
echo "header: a/N=$a/$N circle |t-($tr+${ti}i)|=$R0 M=$M n0=$n0 prec=$prec" >> "$log"
python3 P2_cert.py combine "$log" $M >> "$log"
