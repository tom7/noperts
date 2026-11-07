#!/bin/bash
# exportseptopertaxis.sh: Septopert cap 2 (the axis cap), exact, with the Lean export: cert-axx.txt.
# The tool numbers the sides' ids 1 (side 0) and 0 (sides 1, 2, 3); renumbered here to Lean's codes
# (ArcCapDecode.parseId): side 0 -> 1, side 1 -> 2, side 2 -> 3, side 3 -> 0.
C=/root/nopert-project/nopert229/out/bottleneck/neo/m7cap
cd "$(dirname "$0")/../../search/septopert"
nice -n 5 ./capcert-m12.exe --solid m7 --family U --frame axis --sides 0123 --mu0 1/16 --R 2 --S 16 --Rc 1 --Sc 16 \
  --max_depth 40 --max_fail 300 --try 16 --threads 12 --exact --export $C/cert-axx.raw > $C/log-axx-export.txt 2>&1
grep TOTAL $C/log-axx-export.txt
awk 'BEGIN{n=0} /^chart u /{ s=int(n/13); n++; $3 = (s==0?1:(s==1?2:(s==2?3:0))) } {print}' $C/cert-axx.raw > $C/cert-axx.txt
grep -c "^chart" $C/cert-axx.txt; ls -la $C/cert-axx.txt
