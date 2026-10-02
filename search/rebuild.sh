#!/bin/bash
# Rebuilds the proof that Nopert #231 is not Rupert, end to end, with the
# parameters that produced the verified result (see notes/R.md):
#
#   model   exact rational model, codes and code triangles (codebdd231), and
#           the Lean data generated from them
#   tube    identity tube: one quadtree of Tag 1 cages per code (tubecode231),
#           refined to radius 2e-5 (tuberefine231)
#   tubepack  tube trees -> Lean packs + manifest (export_codetrees_pack)
#   search  5D search, charts 0-2 (search5d), until nothing is deferred
#   pack    per-code 5D packs (pack5d --per_code)
#   verify  Lean: check every table and build the proof (constructNopert231)
#
# Every stage is restartable: tubecode231 and search5d journal their work,
# and pack5d skips packs newer than their journals.
#
# Usage: ./rebuild.sh [--from STAGE] [--only STAGE] [--dry_run] [--threads N]
#        [--work DIR]   (default /root/quad/tmp/rebuild)
#
# The model stage regenerates committed source files (vertices231_exact27.*,
# codebdd231.json, and Noperthedron's Vertices.lean etc.), so it only runs
# when asked for (--from model or --only model).
set -euo pipefail

STAGES=(model tube tubepack search pack verify)
FROM=tube
ONLY=""
DRY=0
THREADS=60
WORK=/root/quad/tmp/rebuild
NOPERT=$(cd "$(dirname "$0")" && pwd)
LEAN=$NOPERT/../Noperthedron
while [ $# -gt 0 ]; do
  case $1 in
    --from) FROM=$2; shift 2 ;;
    --only) ONLY=$2; shift 2 ;;
    --dry_run) DRY=1; shift ;;
    --threads) THREADS=$2; shift 2 ;;
    --work) WORK=$2; shift 2 ;;
    *) echo "unknown argument $1" >&2; exit 1 ;;
  esac
done

run() {
  echo "+ $*"
  if [ $DRY -eq 0 ]; then "$@"; fi
}
# Lean executables run under a memory cap (ulimit -v would stop Lean's threads).
lean_run() {
  run systemd-run --scope -q -p MemoryMax=100G -p MemorySwapMax=0 "$@"
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

ulimit -v 120000000
TREES1=$WORK/trees_r1
TREES2=$WORK/trees_r2
TUBEPACKS=$WORK/tube_packs
JOBS=$WORK/jobs
PACKS=$WORK/packs
run mkdir -p "$WORK"

echo "== build"
run make -C "$NOPERT" -j 16 codebdd231.exe tubecode231.exe tuberefine231.exe \
  export_codetrees_pack.exe search5d.exe pack5d.exe scoreboard5d.exe
(cd "$LEAN" && lean_run lake build constructNopert231 check_global_rows validate_code_pack)

if want model; then
  echo "== model"
  (cd "$NOPERT" && run ./codebdd231.exe --root_file=nopert231_root.txt)
  (cd "$LEAN" && run python3 scripts/nopert231_update_vertices.py \
    && run python3 scripts/nopert231_emit_tangent_cones.py Noperthedron/Nopert231/GeneratedTangentCones.lean \
    && run python3 scripts/nopert231_emit_wedge_cover.py Noperthedron/Nopert231/WedgeCoverData.lean)
  run make -C "$NOPERT" -j 16 codebdd231.exe tubecode231.exe tuberefine231.exe \
    export_codetrees_pack.exe search5d.exe pack5d.exe
  (cd "$LEAN" && lean_run lake build constructNopert231 check_global_rows validate_code_pack)
fi

NCODES=$(python3 -c "import json; print(len(json.load(open('$NOPERT/codebdd231.json'))['codes']))")

if want tube; then
  echo "== tube ($NCODES codes)"
  for code in $(seq 0 $((NCODES - 1))); do
    (cd "$NOPERT" && run ./tubecode231.exe --code "$code" --output_dir "$TREES1" --threads "$THREADS")
  done
  for code in $(seq 0 $((NCODES - 1))); do
    (cd "$NOPERT" && run ./tuberefine231.exe --code "$code" --in_dir "$TREES1" --out_dir "$TREES2" \
      --goal 1/50000 --threads "$THREADS")
  done
fi

if want tubepack; then
  echo "== tubepack"
  (cd "$NOPERT" && run ./export_codetrees_pack.exe --trees_dir "$TREES2" --out_dir "$TUBEPACKS" \
    --bdd codebdd231.json)
fi

if want search; then
  echo "== search"
  # One run solves every job; deferred leaves are retried in the same run.
  (cd "$NOPERT" && run ./search5d.exe --all --charts 0,1,2 --threads "$THREADS" --commit_depth 12 \
    --subtree_budget 5000 --max_depth 200 --trees_dir "$TREES2" --view_scale 4 \
    --max_full_retry 1024 --retry_deferred --requeue_deferred --out_dir "$JOBS")
  (cd "$NOPERT" && run ./scoreboard5d.exe --journals "$JOBS" | tail -1)
fi

if want pack; then
  echo "== pack"
  for chart in 0 1 2; do
    (cd "$NOPERT" && run ./pack5d.exe --chart "$chart" --per_code "$PACKS" --journals "$JOBS" \
      --trees_dir "$TREES2" --threads "$THREADS")
  done
fi

if want verify; then
  echo "== verify"
  (cd "$LEAN" && lean_run .lake/build/bin/constructNopert231 "$TUBEPACKS/manifest.txt" "$PACKS")
fi
