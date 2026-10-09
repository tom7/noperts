#!/bin/bash
# Rebuilds the proof that the 7-vertex C3v candidate nopert_233 (K) is a
# Nopert, end to end (notes/NOPERT7.md, M5):
#
#   model    the exact model (c3v_model.py -> nopert233_model.txt, with the two
#            view triangles T1/T2) and codebdd (model_vertices.*, codebdd.json)
#   tube     identity tube per code (tubecode --min_r 1/100000, the cap at the
#            mirror normal n = (1,0,-1)/sqrt2 left to the cap certificate),
#            then tuberefine on the codes away from the cap (codes 7, 9, 11-13
#            touch n and are not refined: it only multiplies their leaves)
#   tubepack tube trees -> Lean tube packs + manifest (export_codetrees_pack)
#   cap      the cap certificate at n (capcert7 --mu0 1/16 --max_depth 38)
#            and the search's caps file (frame x = (1,0,-1), e1 = (0,2,0),
#            e2 = (1,0,1), mu0 = 1/16, |w| <= 1/91)
#   search   5D search, 22 code triangles x charts 0-3, rounds until nothing
#            is deferred (search5d --retry_deferred --requeue_deferred)
#   pack     per-code 5D packs c<C>/t<T>.pack (pack5d --per_code)
#   verify   Lean: constructNopert7 <tube manifest> <packs> <cap.cert>
#
# Every stage is restartable (tubecode and search5d journal their work; pack5d
# skips packs newer than their journals). search5d is not deterministic (work
# order); the others are.
#
# Usage: ./nopert7_rebuild.sh [--from STAGE] [--only STAGE] [--dry_run]
#        [--threads N] [--mem_gb G] [--work DIR]
#        (default: from tube, 12 threads, 40 GB, ../minimal-runs/m5)
# Long stages run in a systemd scope with MemoryMax (and no swap); each
# stage's wall time and the scope's peak memory are appended to
# WORK/stages.log.
set -euo pipefail

STAGES=(model tube tubepack cap search pack verify)
FROM=tube
ONLY=""
DRY=0
THREADS=12
MEM_GB=40
WORK=""
NOPERT=$(cd "$(dirname "$0")" && pwd)
LEAN=$NOPERT/../Noperthedron-nopert7
while [ $# -gt 0 ]; do
  case $1 in
    --from) FROM=$2; shift 2 ;;
    --only) ONLY=$2; shift 2 ;;
    --dry_run) DRY=1; shift ;;
    --threads) THREADS=$2; shift 2 ;;
    --mem_gb) MEM_GB=$2; shift 2 ;;
    --work) WORK=$2; shift 2 ;;
    *) echo "unknown argument $1" >&2; exit 1 ;;
  esac
done
[ -n "$WORK" ] || WORK=$NOPERT/../minimal-runs/m5
TREES_RAW=$WORK/trees_raw
TREES=$WORK/trees
TUBEPACKS=$WORK/tube_packs
JOBS=$WORK/jobs
PACKS=$WORK/packs
CAP_CERT=$WORK/cap-1_16.cert
CAPS_FILE=$WORK/caps.txt
STAGELOG=$WORK/stages.log

run() {
  echo "+ $*" >&2
  if [ $DRY -eq 0 ]; then "$@"; fi
}
# A command in a memory-capped scope (no swap); prints its peak memory.
capped() {
  # (Called in subshells: the unit name must not depend on a counter.)
  local unit="nopert7-$$-$(date +%s%N)"
  echo "+ [scope ${MEM_GB}G] $*" >&2
  if [ $DRY -eq 0 ]; then
    systemd-run --user --scope -q --unit="$unit" -p MemoryMax="${MEM_GB}G" -p MemorySwapMax=0 \
      bash -c '"$@"; rc=$?; f=/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup)/memory.peak;
               [ -r "$f" ] && echo "peak memory: $(( $(cat "$f") / 1048576 )) MiB" >&2; exit $rc' _ "$@"
  fi
}
want() {
  local stage=$1
  if [ -n "$ONLY" ]; then [ "$ONLY" = "$stage" ]; return; fi
  local reached=0
  for s in "${STAGES[@]}"; do
    [ "$s" = "$FROM" ] && reached=1
    [ "$s" = "$stage" ] && return $((1 - reached))
  done
  return 1
}
STAGE_T0=0
stage_begin() { echo "== $1 ($(date +%T))"; STAGE_T0=$(date +%s); }
stage_end() {
  local dt=$(( $(date +%s) - STAGE_T0 ))
  [ $DRY -eq 1 ] || echo "$1 $(date +%F_%T) ${dt}s" >> "$STAGELOG"
  echo "== $1 done in ${dt}s"
}

run mkdir -p "$WORK"
# The journals and packs are large (t3 alone: ~3 GB of journal); a full disk
# silently truncates them.
echo "== free space: $(df -h "$WORK" | awk 'NR == 2 {print $4}')"
echo "== $THREADS threads, memory cap ${MEM_GB} GB, work $WORK"
NCODES=15
NTRI=22

echo "== build"
run make -C "$NOPERT" -j "$THREADS" codebdd.exe tubecode.exe tuberefine.exe export_codetrees_pack.exe \
  capcert7.exe search5d.exe pack5d.exe dfwhere.exe

if want model; then
  stage_begin model
  # The candidate's coordinates (minimal-runs/candidates).
  XYZ=$NOPERT/../minimal-runs/candidates/7v-cocta-c3v-2.xyz
  if [ $DRY -eq 0 ]; then (cd "$NOPERT" && python3 c3v_model.py "$XYZ" > nopert233_model.txt); fi
  (cd "$NOPERT" && run ./codebdd.exe --model_file=nopert233_model.txt codebdd.json)
  run make -C "$NOPERT" -j "$THREADS" tubecode.exe tuberefine.exe export_codetrees_pack.exe search5d.exe pack5d.exe
  stage_end model
fi

# The cap at n for the tube (angular radius 0.04 < the cap cone's 0.044).
TUBE_CAP=(--cap 0.70710678118654752,0,-0.70710678118654752,0.04 --cap_r 1/46)

if want tube; then
  stage_begin tube
  run mkdir -p "$TREES_RAW" "$TREES"
  for code in $(seq 0 $((NCODES - 1))); do
    (cd "$NOPERT" && capped ./tubecode.exe --code "$code" --output_dir "$TREES_RAW" --threads "$THREADS" \
      "${TUBE_CAP[@]}" --min_r 1/100000)
  done
  # Refinement (larger certified radii) away from the cap; code 1 (the
  # first-order margin minimum) with a lower goal to keep its tree small.
  for code in $(seq 0 $((NCODES - 1))); do
    case $code in
      7|9|11|12|13) run cp "$TREES_RAW/tree.$code.json" "$TREES/tree.$code.json" ;;
      1) (cd "$NOPERT" && capped ./tuberefine.exe --code 1 --in_dir "$TREES_RAW" --out_dir "$TREES" \
            --goal 1/4000 --goal_frac 1/2 --levels 4 --threads "$THREADS") ;;
      10) (cd "$NOPERT" && capped ./tuberefine.exe --code 10 --in_dir "$TREES_RAW" --out_dir "$TREES" \
            --goal 1/1000 --goal_frac 1/2 --levels 4 --threads "$THREADS") ;;
      *) (cd "$NOPERT" && capped ./tuberefine.exe --code "$code" --in_dir "$TREES_RAW" --out_dir "$TREES" \
            --goal 1/1000 --goal_frac 1/2 --levels 6 --threads "$THREADS") ;;
    esac
  done
  stage_end tube
fi

if want tubepack; then
  stage_begin tubepack
  (cd "$NOPERT" && capped ./export_codetrees_pack.exe --trees_dir "$TREES" --out_dir "$TUBEPACKS" \
    --bdd codebdd.json)
  stage_end tubepack
fi

if want cap; then
  stage_begin cap
  (cd "$NOPERT" && capped ./capcert7.exe --model nopert233_model.txt --mu0 1/16 --max_depth 38 \
    --threads "$THREADS" --export "$CAP_CERT")
  # The search's caps file (search5d --caps): x e1 e2 mu0 wmax (doubles),
  # the exact frame (a b c d per coordinate, here rational: b = c = d = 0),
  # mu0 and wmax^2.
  if [ $DRY -eq 0 ]; then
    echo "1 0 -1 0 2 0 1 0 1 0.0625 0.01098901098901099 1 0 0 0 0 0 0 0 -1 0 0 0 0 0 0 0 2 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 1 0 0 0 1/16 1/8281" > "$CAPS_FILE"
  fi
  stage_end cap
fi

SEARCH=(--all --charts 0,1,2,3 --threads "$THREADS" --commit_depth 12 --subtree_budget 200000
        --max_depth 200 --trees_dir "$TREES" --view_scale 4 --max_full_retry 1024 --half_turn_prune
        --caps "$CAPS_FILE" --out_dir "$JOBS" --requeue_deferred)
if want search; then
  stage_begin search
  # Rounds until nothing is deferred (the requeue closes nearly everything in
  # the first round; later rounds pick up subtrees cut short).
  for round in 1 2 3 4 5 6; do
    log=$WORK/search_round$round.log
    # --retry_deferred: also the deferred leaves already in the journals
    # (e.g. after an interrupted run), so "0 deferred" means none anywhere.
    extra=(--retry_deferred)
    rc=0
    (cd "$NOPERT" && capped ./search5d.exe "${SEARCH[@]}" "${extra[@]}") > "$log" 2>&1 || rc=$?
    [ $DRY -eq 1 ] && break
    echo "search round $round: exit status $rc"
    grep -E "jobs|^Finished|peak memory" "$log"
    grep -q "^Finished: .* 0 deferred leaves" "$log" && break
  done
  stage_end search
fi

if want pack; then
  stage_begin pack
  for chart in 0 1 2 3; do
    (cd "$NOPERT" && capped ./pack5d.exe --chart "$chart" --per_code "$PACKS" --journals "$JOBS" \
      --trees_dir "$TREES" --bdd codebdd.json --threads "$THREADS")
  done
  stage_end pack
fi

if want verify; then
  stage_begin verify
  # Build the checker (no-op if current), never alongside another Lean build.
  if [ $DRY -eq 0 ]; then while pgrep -x lake > /dev/null; do sleep 30; done; fi
  (cd "$LEAN" && run timeout 6000 systemd-run --user --scope -q -p MemoryMax=48G -p MemorySwapMax=0 \
    lake build constructNopert7)
  [ -x "$LEAN/.lake/build/bin/constructNopert7" ] || {
    echo "missing $LEAN/.lake/build/bin/constructNopert7 (lake build constructNopert7)" >&2; exit 1; }
  capped "$LEAN/.lake/build/bin/constructNopert7" "$TUBEPACKS/manifest.txt" "$PACKS" "$CAP_CERT" \
    2>&1 | tee "$WORK/verify.log"
  stage_end verify
fi
