#!/bin/bash
# Rebuilds the proof that the pentagonal hexecontahedron is a Nopert (not
# Rupert), end to end:
#
#   model   the exact model (the polar dual of the snub dodecahedron,
#           ph-model.py, checked against McCooey's coordinates by
#           ph-crosscheck.py), codes and code triangles (codebdd), and the
#           Lean data generated from them
#   tube    identity tube: one quadtree of Tag 1 cages per code (tubecode),
#           refined to radius 2e-5 (tuberefine; larger for the codes in
#           TUBE_GOALS)
#   tubepack  tube trees -> Lean packs + manifest (export-codetrees-pack)
#   search  5D search, charts 0-2 (search5d), until nothing is deferred
#   pack    per-code 5D packs (pack5d --per_code)
#   verify  Lean: check every table and build the proof
#           (constructPentagonalHexecontahedron in ../../proof)
#
# Every stage is restartable: tubecode and search5d journal their work,
# and pack5d skips packs newer than their journals.
#
# Reproducibility: tubecode, tuberefine and pack5d are deterministic
# (independent of --threads); search5d is not (work order). To re-verify an
# existing result, start from its trees, journals or packs (--from pack /
# --from verify with --work pointing at them).
#
# Usage: ./rebuild.sh [--from STAGE] [--only STAGE] [--dry_run] [--threads N]
#        [--mem_gb G] [--work DIR]   (default ../../work-ph)
#        [--model_file FILE]  model stage: the model file (default ph-model.txt)
#
# Resources: --threads defaults to every core (nproc). The tools also use it
# for the build; the Lean verifier sizes its own pool to the machine.
# Measured peak memory (2026-10-03, 64 cores):
#   tube stages                        a few GB
#   search5d                           ~15 GB
#   pack5d chart 0                     ~10 GB (code 51.0; was ~50 GB before
#                                      interning view triangles and boxes)
#   the Lean verifier                  ~30 GB
# So the rebuild needs ~32 GB of RAM (or swap). --mem_gb caps every stage
# (default: the larger of 90% of RAM and 40 GB; never below what the
# rebuild needs, since swap can make up the difference). C++ tools get it
# as ulimit -v plus 16 GB for virtual-only reservations (thread stacks,
# malloc arenas); Lean runs in a systemd scope with MemoryMax (ulimit -v
# would stop Lean from creating threads).
#
# The model stage regenerates committed source files (model-vertices.* and the
# Lean data in ../../proof/PentagonalHexecontahedron/:
# SolidModel.lean (vertices), WedgeCoverData.lean, OrbitData.lean,
# PHStatementData.lean, and ../../proof/Pipeline/IcoGroupData.lean,
# by the scripts in scripts/), so it only runs when asked for (--from model
# or --only model). It also writes codebdd.json (not committed), which the
# other stages need: in a fresh clone, run --from model first.
#
# Each stage's wall time is appended to WORK/stages.log. The Lean build runs
# in the background while the C++ stages run (log WORK/lean_build.log); the
# verify stage waits for it, and the script fails if it fails. (Helpers:
# ../common/rebuild-lib.sh.)
set -euo pipefail

STAGES=(model tube tubepack search pack verify)
FROM=tube
ONLY=""
DRY=0
THREADS=$(nproc)
RAM_GB=$(awk '/MemTotal/ {print int($2 / 1048576)}' /proc/meminfo)
MEM_GB=$(( RAM_GB * 9 / 10 > 40 ? RAM_GB * 9 / 10 : 40 ))
WORK=""
MODEL_FILE=ph-model.txt
NOPERT=$(cd "$(dirname "$0")" && pwd)
LEAN=$NOPERT/../../proof
# The Lean generator scripts read codebdd's outputs and the model files here.
export MODEL_DIR=$NOPERT
while [ $# -gt 0 ]; do
  case $1 in
    --from) FROM=$2; shift 2 ;;
    --only) ONLY=$2; shift 2 ;;
    --dry_run) DRY=1; shift ;;
    --threads) THREADS=$2; shift 2 ;;
    --mem_gb) MEM_GB=$2; shift 2 ;;
    --work) WORK=$2; shift 2 ;;
    --model_file) MODEL_FILE=$2; shift 2 ;;
    *) echo "unknown argument $1" >&2; exit 1 ;;
  esac
done

run() {
  echo "+ $*"
  if [ $DRY -eq 0 ]; then "$@"; fi
}
# HAVE_SCOPE, want, stage_begin/stage_end, the background Lean build.
source "$NOPERT/../common/rebuild-lib.sh"
# Lean executables run under a memory cap (ulimit -v would stop Lean's threads).
lean_run() {
  if [ $HAVE_SCOPE -eq 1 ]; then
    run systemd-run --user --scope -q -p MemoryMax="${MEM_GB}G" "$@"
  else
    run "$@"
  fi
}
# The Lean build (in the background: lean_build_start), under the same cap.
LEAN_BUILD=(lake build constructPentagonalHexecontahedron)
[ $HAVE_SCOPE -eq 0 ] || LEAN_BUILD=(systemd-run --user --scope -q -p MemoryMax="${MEM_GB}G" "${LEAN_BUILD[@]}")

echo "== resources: $THREADS threads, memory cap ${MEM_GB} GB (RAM ${RAM_GB} GB)"
if [ "$RAM_GB" -lt 40 ]; then
  echo "warning: ${RAM_GB} GB of RAM; Lean verification needs ~30 GB at peak, so expect swapping" >&2
fi
ulimit -v $(( (MEM_GB + 16) * 1048576 ))
[ -n "$WORK" ] || WORK=$NOPERT/../../work-ph
TREES1=$WORK/trees_r1
TREES2=$WORK/trees_r2
TUBEPACKS=$WORK/tube_packs
JOBS=$WORK/jobs
PACKS=$WORK/packs
run mkdir -p "$WORK"

echo "== build"
run make -C "$NOPERT" -j "$THREADS" codebdd.exe tubecode.exe tuberefine.exe \
  export-codetrees-pack.exe search5d.exe pack5d.exe scoreboard5d.exe
# Lean is needed only by the model (generated sources) and verify stages; it
# builds in the background while the C++ stages run. (The model stage starts
# it after regenerating its data.)
if want verify && ! want model; then
  lean_build_start "$LEAN" "${LEAN_BUILD[@]}"
fi

if want model; then
  stage_begin model
  # The snub dodecahedron's model (its frame, view triangle and symmetry
  # neighbors), then its polar dual.
  (cd "$NOPERT" && run python3 ../common/snub-model.py snub-model.txt symmetry-neighbors.h)
  (cd "$NOPERT" && run python3 ph-model.py snub-model.txt "$MODEL_FILE")
  (cd "$NOPERT" && run python3 ph-crosscheck.py "$MODEL_FILE")
  (cd "$NOPERT" && run ./codebdd.exe --model_file="$MODEL_FILE" codebdd.json)
  (cd "$LEAN" && run python3 "$NOPERT/../common/update-vertices.py" PentagonalHexecontahedron/SolidModel.lean \
    && run python3 "$NOPERT/../common/emit-wedge-cover.py" --namespace PentagonalHexecontahedron.WedgeCover \
         PentagonalHexecontahedron/WedgeCoverData.lean \
    && run python3 "$NOPERT/scripts/snub-ico-group.py" \
    && run python3 "$NOPERT/scripts/ph-statement-data.py")
  run make -C "$NOPERT" -j "$THREADS" codebdd.exe tubecode.exe tuberefine.exe \
    export-codetrees-pack.exe search5d.exe pack5d.exe
  lean_build_start "$LEAN" "${LEAN_BUILD[@]}"
  stage_end model
fi

# Tube radius goals. Code 18's code triangle is certified by a single tube
# leaf of radius 8e-4, well above the default goal, so tuberefine would not
# split it; the 5D search must then certify rotations just past 8e-4 over
# the whole code triangle, which it does only very slowly. A larger goal
# splits the triangle (82 leaves, radius >= 1.5e-3) and the search finishes
# in a minute.
TUBE_GOALS="18:1/400"
tube_goal() {
  local entry
  for entry in $TUBE_GOALS; do
    if [ "${entry%%:*}" = "$1" ]; then echo "${entry#*:}"; return; fi
  done
  echo 1/50000
}

# codebdd.json is written by the model stage (it is not committed).
require_codebdd tube tubepack search pack
if [ -f "$NOPERT/codebdd.json" ]; then
  NCODES=$(python3 -c "import json; print(len(json.load(open('$NOPERT/codebdd.json'))['codes']))")
else
  NCODES=53  # (dry run before the model stage has written codebdd.json)
fi

if want tube; then
  stage_begin tube
  echo "   $NCODES codes"
  for code in $(seq 0 $((NCODES - 1))); do
    (cd "$NOPERT" && run ./tubecode.exe --code "$code" --output_dir "$TREES1" --threads "$THREADS")
  done
  for code in $(seq 0 $((NCODES - 1))); do
    (cd "$NOPERT" && run ./tuberefine.exe --code "$code" --in_dir "$TREES1" --out_dir "$TREES2" \
      --goal "$(tube_goal "$code")" --threads "$THREADS")
  done
  stage_end tube
fi

if want tubepack; then
  stage_begin tubepack
  (cd "$NOPERT" && run ./export-codetrees-pack.exe --trees_dir "$TREES2" --out_dir "$TUBEPACKS" \
    --bdd codebdd.json)
  stage_end tubepack
fi

if want search; then
  stage_begin search
  # One run solves every job; deferred leaves are retried in the same run.
  # search5d's default --blend5d 4 (escalate; validated here 2026-10-15):
  # packs 63.9 MB, vs 64.6 MB with --blend5d 0 and 66.3 MB with 2.
  (cd "$NOPERT" && run ./search5d.exe --all --charts 0,1,2 --threads "$THREADS" --commit_depth 12 \
    --subtree_budget 5000 --max_depth 200 --trees_dir "$TREES2" --view_scale 4 \
    --max_full_retry 1024 --retry_deferred --requeue_deferred --out_dir "$JOBS")
  (cd "$NOPERT" && run ./scoreboard5d.exe --journals "$JOBS" | tail -1)
  stage_end search
fi

if want pack; then
  stage_begin pack
  for chart in 0 1 2; do
    (cd "$NOPERT" && run ./pack5d.exe --chart "$chart" --per_code "$PACKS" --journals "$JOBS" \
      --trees_dir "$TREES2" --threads "$THREADS")
  done
  stage_end pack
fi

if want verify; then
  stage_begin verify
  lean_build_wait
  (cd "$LEAN" && lean_run .lake/build/bin/constructPentagonalHexecontahedron "$TUBEPACKS/manifest.txt" "$PACKS")
  stage_end verify
fi

# Wait for a background Lean build that the verify stage did not wait for.
lean_build_wait
