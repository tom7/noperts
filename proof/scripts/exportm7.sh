#!/bin/bash
# exportm7.sh TAG: M7 cap 1 (U + arc wedge), exact, with the Lean export: cert-TAG.txt (like capwork/exportall.sh).
tag=$1; shift
mu0=1/8; nu0=1/8; R1=3; R2=32; R3=128; Z=16; zh=2; zmid=6; tend=13/32; TS=1/5; TE=4/11
A="--max_depth 44 --max_fail 2000 --try 16 --threads 12 --exact $@"
W="--family W --nu0 $nu0 --R1 $R1 --R2 $R2 --R3 $R3 --Z $Z --Zc $Z --R2c $R2 --R3c $R3 $A"
C=/root/nopert-project/nopert229/out/bottleneck/neo/m7cap
s() { p=$1; shift
  ( time (cd /root/nopert-project/noperts-neo/search/m7 && nice -n 5 ./capcert-m7.exe --solid m7 "$@" --export $C/cert-$tag-$p.part) ) > $C/log-$tag-$p.txt 2>&1
  echo "$p: $(grep TOTAL $C/log-$tag-$p.txt) $(grep -c FAIL $C/log-$tag-$p.txt) failing, $(grep real $C/log-$tag-$p.txt)"; }
s U --family U --mu0 $mu0 --nu0 $nu0 --R1 $R1 --R2 $R2 --R3 $R3 --wedge_prune $A
s W0 $W --regime 0 --piece 0 --tlo 0 --thi $TS --zh $zh
s Wm $W --regime 0 --piece 1 --tlo $TS --thi $TS --tmid $zmid
s W1 $W --regime 1 --piece 2 --tlo $TS --zl $zh --thi $TE
s W2 $W --regime 1 --piece 3 --tlo $TE --thi $tend
cd $C; cat cert-$tag-U.part cert-$tag-W0.part cert-$tag-Wm.part cert-$tag-W1.part cert-$tag-W2.part > cert-$tag.txt
rm cert-$tag-*.part; ls -la cert-$tag.txt
