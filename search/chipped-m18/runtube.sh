#!/bin/bash
# runtube.sh [THREADS] : identity tube for every code of this directory into $WORK (default ../../work-chipped-m18; M18's caps), one log per code.
TH=${1:-36}
cd "$(dirname "$0")"
W=${WORK:-$(cd ../.. && pwd)/work-chipped-m18}; mkdir -p $W/trees_raw
N=$(python3 -c "import json;print(json.load(open('codebdd.json'))['num_codes'])")
for code in $(seq 0 $((N-1))); do
  timeout ${TUBE_TIMEOUT:-1800} nice -n 17 ./tubecode.exe --code $code --output_dir $W/trees_raw --threads $TH --cap 0.70710678118654752,0,-0.70710678118654752,0.04 \
    --piece_caps arc-cap.txt --cap_r 1/46 --min_r 1/100000 --best_cage > $W/tube.$code.log 2>&1
  echo "code $code: $(grep -c FAILED $W/tube.$code.log) failed; $(tail -n 1 $W/tube.$code.log | cut -c1-200)"
done
echo TUBE DONE
