#!/bin/bash
# Rebuilds the proof that the snub cube is not Rupert, end to end:
#
#   model   the exact model and its rational model (sc_model), codes and code
#           triangles (codebdd), and the Lean data generated from them
#           (proof/SnubCube/ModelData.lean, WedgeCoverData.lean)
#   tube    identity tube: one quadtree of Tag 1 cages per code (tubecode),
#           with the views near u* left to the caps (--cap, --cap_r)
#   tubepack  tube trees -> Lean packs + manifest (export_codetrees_pack)
#   caps    the cap and tie-tube certificate over Q(t) (sccapcert --export)
#           and the search's exact cap domains (--caps)
#   search  5D search, charts 0-3 (search5d --trib_caps), until nothing is
#           deferred
#   pack    per-code 5D packs (pack5d --per_code)
#   verify  Lean: check every table and the cap certificate and build the
#           proof (constructSnubCube)
#
# Every stage is restartable: tubecode and search5d journal their work, and
# pack5d skips packs newer than their journals.
#
# Usage: ./rebuild.sh [--from STAGE] [--only STAGE] [--dry_run] [--threads N]
#        [--mem_gb G] [--work DIR]   (default ../../work-sc)
#
# Resources: --threads defaults to every core (nproc). --mem_gb caps every
# stage (default: the larger of 90% of RAM and 40 GB). C++ tools get it as
# ulimit -v plus 16 GB for virtual-only reservations; Lean runs in a systemd
# scope with MemoryMax. (Helpers: ../common/rebuild_lib.sh.)
set -euo pipefail

STAGES=(model tube tubepack caps search pack verify)
FROM=tube
ONLY=""
DRY=0
THREADS=$(nproc)
RAM_GB=$(awk '/MemTotal/ {print int($2 / 1048576)}' /proc/meminfo)
MEM_GB=$(( RAM_GB * 9 / 10 > 40 ? RAM_GB * 9 / 10 : 40 ))
WORK=""
NOPERT=$(cd "$(dirname "$0")" && pwd)
LEAN=$(cd "$NOPERT/../../proof" && pwd)
export MODEL_DIR=$NOPERT
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

run() {
  echo "+ $*"
  if [ $DRY -eq 0 ]; then "$@"; fi
}
source "$NOPERT/../common/rebuild_lib.sh"
lean_run() {
  if [ $HAVE_SCOPE -eq 1 ]; then
    run systemd-run --user --scope -q -p MemoryMax="${MEM_GB}G" "$@"
  else
    run "$@"
  fi
}
LEAN_BUILD=(lake build constructSnubCube)
[ $HAVE_SCOPE -eq 0 ] || LEAN_BUILD=(systemd-run --user --scope -q -p MemoryMax="${MEM_GB}G" "${LEAN_BUILD[@]}")

echo "== resources: $THREADS threads, memory cap ${MEM_GB} GB (RAM ${RAM_GB} GB)"
ulimit -v $(( (MEM_GB + 16) * 1048576 ))
[ -n "$WORK" ] || WORK=$NOPERT/../../work-sc
TREES=$WORK/trees_raw
TUBEPACKS=$WORK/tubepacks
CAPS=$WORK/caps
JOBS=$WORK/jobs
PACKS=$WORK/packs
run mkdir -p "$WORK" "$CAPS"

# The degenerate view u* (sc_model.txt's ustar) and the tube's cap there: the
# angular radius 0.055 is inside the cap box (mu0 = 1/8: atan(1/8) = 0.124),
# and so is the tube radius 1/10 (|w| <= 1/10 in a box of half-width
# R mu0 = 1/4 in frame coordinates; the frame vectors have length >= 0.88).
TUBE_CAP=(--cap 0.2834724367428329596,0,0.9589803843703376638,0.055 --cap_r 1/10)

echo "== build"
run make -C "$NOPERT" -j "$THREADS" sc_model.exe codebdd.exe tubecode.exe export_codetrees_pack.exe \
  sccapcert.exe search5d.exe pack5d.exe scoreboard5d.exe
if want verify && ! want model; then
  lean_build_start "$LEAN" "${LEAN_BUILD[@]}"
fi

if want model; then
  stage_begin model
  (cd "$NOPERT" && run ./sc_model.exe sc_model.txt symmetry_neighbors.h "$LEAN/SnubCube/ModelData.lean")
  (cd "$NOPERT" && run ./codebdd.exe --model_file=sc_model.txt codebdd.json)
  (cd "$NOPERT" && run python3 ../sd/scripts/emit_wedge_cover.py --bdd codebdd.json \
    --namespace SnubCube.WedgeCover "$LEAN/SnubCube/WedgeCoverData.lean")
  run make -C "$NOPERT" -j "$THREADS" codebdd.exe tubecode.exe export_codetrees_pack.exe \
    sccapcert.exe search5d.exe pack5d.exe
  lean_build_start "$LEAN" "${LEAN_BUILD[@]}"
  stage_end model
fi

require_codebdd tube tubepack search pack
if [ -f "$NOPERT/codebdd.json" ]; then
  NCODES=$(python3 -c "import json; print(len(json.load(open('$NOPERT/codebdd.json'))['codes']))")
else
  NCODES=22
fi

if want tube; then
  stage_begin tube
  echo "   $NCODES codes"
  for code in $(seq 0 $((NCODES - 1))); do
    (cd "$NOPERT" && run ./tubecode.exe --code "$code" --output_dir "$TREES" --threads "$THREADS" \
      "${TUBE_CAP[@]}" --min_r 1/100000)
  done
  stage_end tube
fi

if want tubepack; then
  stage_begin tubepack
  (cd "$NOPERT" && run ./export_codetrees_pack.exe --trees_dir "$TREES" --out_dir "$TUBEPACKS" \
    --bdd codebdd.json)
  stage_end tubepack
fi

if want caps; then
  stage_begin caps
  (cd "$NOPERT" && run ./sccapcert.exe --threads "$THREADS" --export "$CAPS/sc.cert" \
    --caps "$CAPS/trib_caps.txt")
  stage_end caps
fi

if want search; then
  stage_begin search
  # TODO: validate blended inner points (search5d's default --blend5d 2) for
  # this solid; its Lean decoder does not read pack tags 17 / 18 yet.
  (cd "$NOPERT" && run ./search5d.exe --all --charts 0,1,2,3 --threads "$THREADS" --commit_depth 12 \
    --subtree_budget 200000 --max_depth 200 --trees_dir "$TREES" --view_scale 4 \
    --max_full_retry 1024 --trib_caps "$CAPS/trib_caps.txt" --requeue_deferred --blend5d 0 --out_dir "$JOBS")
  (cd "$NOPERT" && run ./scoreboard5d.exe --journals "$JOBS" | tail -1)
  stage_end search
fi

if want pack; then
  stage_begin pack
  for chart in 0 1 2 3; do
    (cd "$NOPERT" && run ./pack5d.exe --chart "$chart" --per_code "$PACKS" --journals "$JOBS" \
      --trees_dir "$TREES" --threads "$THREADS")
  done
  stage_end pack
fi

if want verify; then
  stage_begin verify
  lean_build_wait
  (cd "$LEAN" && lean_run .lake/build/bin/constructSnubCube "$TUBEPACKS/manifest.txt" "$PACKS" \
    "$CAPS/sc.cert")
  stage_end verify
fi

lean_build_wait
