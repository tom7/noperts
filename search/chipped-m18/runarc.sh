#!/bin/bash
# runarc.sh [THREADS] : the exact arc cap certificate of this directory (capcert-arc: U cap + wedge pieces W0, Wm, W1, W2 with
# M18's piece parameters, ArcCap.neoParams), concatenated into $WORK/arc.cert (WORK default ../../work-chipped-m18). Chord pools:
# the silhouette vertices at U (U, W0, Wm) and along the arc (W1, W2) -- for the Chipped M18; other chips need their own lists.
TH=${1:-16}
cd "$(dirname "$0")"
W=${WORK:-$(cd ../.. && pwd)/work-chipped-m18}
CVU="--chord_verts ${CVU:-0,1,2,3,5,6,8,10,11,12,13,15}"; CVA="--chord_verts ${CVA:-0,2,4,5,6,7,8,10,11,12,13}"
COMMON="${BLEND:-} --max_depth 44 --max_fail 2000 --try 16 --threads $TH --exact --model chipped-m18-model.txt --vscale 1"
WW="--family W --nu0 1/8 --R1 3 --R2 32 --R3 128 --Z 16 --Zc 16 --R2c 32 --R3c 128"
set -e
nice -n 17 ./capcert-arc.exe --family U --mu0 1/8 --nu0 1/8 --R1 3 --R2 32 --R3 128 --wedge_prune $CVU $COMMON --export $W/arc.cert.U > $W/arc.U.log 2>&1
nice -n 17 ./capcert-arc.exe $WW $CVU $COMMON --regime 0 --piece 0 --tlo 0 --thi 17/86 --zh 2 --export $W/arc.cert.W0 > $W/arc.W0.log 2>&1
nice -n 17 ./capcert-arc.exe $WW $CVU $COMMON --regime 0 --piece 1 --tlo 17/86 --thi 17/86 --tmid 6 --export $W/arc.cert.Wm > $W/arc.Wm.log 2>&1
nice -n 17 ./capcert-arc.exe $WW $CVA $COMMON --max_depth 50 --try 200 --combos 12 --topk 3000 --regime 1 --piece 2 --tlo 17/86 --zl 2 --thi 11/32 --export $W/arc.cert.W1 > $W/arc.W1.log 2>&1
nice -n 17 ./capcert-arc.exe $WW $CVA $COMMON --regime 1 --piece 3 --tlo 11/32 --thi 13/32 --export $W/arc.cert.W2 > $W/arc.W2.log 2>&1
for p in U W0 Wm W1 W2; do echo "$p: $(tail -n 1 $W/arc.$p.log)"; done
cat $W/arc.cert.U $W/arc.cert.W0 $W/arc.cert.Wm $W/arc.cert.W1 $W/arc.cert.W2 > $W/arc.cert
echo ARC DONE
