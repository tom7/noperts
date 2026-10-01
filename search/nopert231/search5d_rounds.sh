#!/bin/bash
# Runs search5d in retry rounds until no deferred leaves remain (or the round
# limit is reached). Each round solves the unfinished top-level subtrees and
# every deferred leaf in the journals, with a small --subtree_budget so that
# an interrupted round loses at most that many nodes per thread: the solved
# part of each subtree is journaled, and its unexplored frontier becomes
# deferred leaves for the next round.
#
# Usage: search5d_rounds.sh <max rounds> <round log> <search5d args...>
#   e.g. search5d_rounds.sh 40 /tmp/round.log --all --charts 0 --threads 14 \
#          --commit_depth 12 --subtree_budget 200000 --max_depth 200 \
#          --trees_dir trees_r2 --out_dir jobs
set -u
max_rounds=$1
round_log=$2
shift 2
for round in $(seq 1 "$max_rounds"); do
  echo "=== round $round ($(date +%T))"
  ./search5d.exe "$@" --retry_deferred > "$round_log" 2>&1
  status=$?
  grep -v "subtrees, " "$round_log"
  if [ $status -ne 0 ]; then
    echo "=== search5d failed (status $status)"
    exit 1
  fi
  if grep -q "^Finished: [0-9]* nodes, 0 deferred leaves" "$round_log"; then
    echo "=== done after $round rounds"
    exit 0
  fi
done
echo "=== stopped after $max_rounds rounds with deferred leaves left"
exit 2
