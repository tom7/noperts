#!/bin/bash
# Rebuilds the certificates for the Chipped M18 (the SeptopertM18 with its vertices (-18,9,9)/32 and C3 images cut by
# (-1,5,5).x = 209/64 and C3 images, i.e. normal (-1,k,k) with k = 5 and depth 7/64: 19 vertices, C3v, six acute dihedral
# edges with cos = 1/sqrt 51, 81.95 deg), as run on 2026-11-08. Stages:
#   model    codebdd on chipped-m18-model.txt (model-vertices.*, codebdd.json); rebuild every exe afterwards
#   tube     tubecode per code (21 codes; M18's caps: the mirror normal (1,0,-1)/sqrt2 radius 0.04 and arc-cap.txt)
#   idcap    idcap tree pass (M18's settings) on every code but 7 into trees_id; code 7's raw tree is copied (its pass
#            ran over an hour and was stopped); trees_id is the final tree set
#   tubepack export-codetrees-pack (trees_id)
#   cap      capcert-septopert-m18 (any vertex count), M18's settings plus --ratio_z 16 --try 200
#   arccert  runarc.sh (capcert-arc: U, W0, Wm, W1, W2, blend 4,6,5/19)
#   search   runsearch.sh on trees_id (M18's settings), then a tail pass with --subtree_budget 5000 and
#            --cone_samples 4 (the last subtree near the identity in code 1 was single-threaded at budget 200000)
#   pack     pack5d per chart
#   verify   Lean: constructChippedM18 <tube manifest> <packs> <cap.cert> <arc.cert>
# Usage: [WORK=DIR] [TH=N] ./rebuild.sh [STAGE ...] (default: all stages). Work dir WORK (default ../../work-chipped-m18). Threads: TH (default 36).
# Lean: cd ../../proof && lake build constructChippedM18 (in a memory-capped scope).
set -euo pipefail
cd "$(dirname "$0")"
W=${WORK:-$(cd ../.. && pwd)/work-chipped-m18}; export WORK=$W
TH=${TH:-36}
STAGES=${*:-model tube idcap tubepack cap arccert search pack verify}
mkdir -p $W
for s in $STAGES; do
  echo "== $s $(date)"
  case $s in
    model)
      make -j "$TH" codebdd.exe
      ./codebdd.exe --model_file=chipped-m18-model.txt codebdd.json
      make -j "$TH" codebdd.exe tubecode.exe idcap.exe export-codetrees-pack.exe capcert-septopert-m18.exe capcert-arc.exe \
        search5d.exe pack5d.exe dfwhere.exe scoreboard5d.exe ;;
    tube) ./runtube.sh "$TH" ;;
    idcap)
      systemd-run --scope -q -p MemoryMax=30G nice -n 17 ./idcap.exe --trees_in $W/trees_raw --trees_out $W/trees_id \
        --codes 0,1,2,3,4,5,6,8,9,10,11,12,13,14,15,16,17,18,19,20 --pass_depth 6 --max_leaves 2000 --rho 1/64 \
        --threads "$TH" --max_depth 40 > $W/idcap.log 2>&1
      cp $W/trees_raw/tree.7.json $W/trees_id/ ;;
    tubepack) ./export-codetrees-pack.exe --trees_dir $W/trees_id --out_dir $W/tube_packs --bdd codebdd.json ;;
    cap)
      nice -n 17 ./capcert-septopert-m18.exe --model chipped-m18-model.txt --mu0 1/16 --max_depth 38 --threads "$TH" \
        --ratio_z 16 --try 200 --export $W/cap-1_16.cert > $W/cap.log 2>&1 ;;
    arccert) BLEND="--blend 4,6,5/19" ./runarc.sh "$TH" ;;
    search)
      ./runsearch.sh "$TH" trees_id jobs
      BUDGET=5000 XOPT="--cone_samples 4" LOG=search_tail ./runsearch.sh "$TH" trees_id jobs ;;
    pack)
      for chart in 0 1 2 3; do
        nice -n 17 ./pack5d.exe --chart $chart --per_code $W/packs --journals $W/jobs --trees_dir $W/trees_id \
          --bdd codebdd.json --threads "$TH"
      done ;;
    verify)
      ../../proof/.lake/build/bin/constructChippedM18 $W/tube_packs/manifest.txt $W/packs $W/cap-1_16.cert $W/arc.cert \
        2>&1 | tee $W/verify.log ;;
    *) echo "unknown stage $s" >&2; exit 1 ;;
  esac
done
