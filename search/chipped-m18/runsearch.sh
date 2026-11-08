#!/bin/bash
# runsearch.sh [THREADS [TREES [JOBS]]] : the 5D search of this directory (M18's settings: mirror cap file, arc pieces), rounds
# until nothing is deferred (at most 4). Work dir $WORK (default ../../work-chipped-m18); TREES defaults to trees_raw (the
# unrefined tube trees), JOBS to jobs.
# SEL: the jobs (default --all; e.g. SEL="--t 0,1,2"); LOG: log name prefix
cd "$(dirname "$0")"
TH=${1:-36}; W=${WORK:-$(cd ../.. && pwd)/work-chipped-m18}; TREES=$W/${2:-trees_raw}; JOBS=$W/${3:-jobs}
SEL=${SEL:---all}; LOG=${LOG:-search_round}
echo "1 0 -1 0 2 0 1 0 1 0.0625 0.01098901098901099 1 0 0 0 0 0 0 0 -1 0 0 0 0 0 0 0 2 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 1 0 0 0 1/16 1/8281" > $W/caps.txt
for round in 1 2 3 4; do
  nice -n 17 ./search5d.exe $SEL --charts 0,1,2,3 --threads $TH --commit_depth 12 --subtree_budget ${BUDGET:-200000} --max_depth 200 \
    --trees_dir $TREES --view_scale 4 --max_full_retry 1024 ${XOPT:-} --half_turn_prune --caps $W/caps.txt --piece_caps arc-cap.txt \
    --out_dir $JOBS --requeue_deferred --retry_deferred > $W/$LOG$round.log 2>&1
  echo "round $round: $(grep -E '^Finished' $W/$LOG$round.log)"
  grep -q "^Finished: .* 0 deferred leaves" $W/$LOG$round.log && break
done
echo SEARCH DONE
