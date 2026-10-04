#!/bin/bash
# Rebuilds the proof that the snub dodecahedron is not Rupert, end to end:
#
#   model   exact rational model, codes and code triangles (codebdd), and
#           the Lean data generated from them
#   tube    identity tube: one quadtree of Tag 1 cages per code (tubecode),
#           refined to radius 2e-5 (tuberefine)
#   tubepack  tube trees -> Lean packs + manifest (export_codetrees_pack)
#   search  5D search, charts 0-2 (search5d), until nothing is deferred
#   pack    per-code 5D packs (pack5d --per_code)
#   verify  Lean: check every table and build the proof (constructSnubDodecahedron)
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
#        [--mem_gb G] [--work DIR]   (default ./rebuild-work)
#        [--model_file FILE]  model stage: the model file (default snub_model.txt)
#
# Resources: --threads defaults to every core (nproc). The tools also use it
# for the build; the Lean verifier sizes its own pool to the machine.
# Measured peak memory (2026-10-03, 64 cores):
#   tube stages                        a few GB
#   search5d                           ~15 GB
#   pack5d chart 0                     ~10 GB (code 51.0; was ~50 GB before
#                                      interning view triangles and boxes)
#   constructSnubDodecahedron          ~30 GB
# So the rebuild needs ~32 GB of RAM (or swap). --mem_gb caps every stage
# (default: the larger of 90% of RAM and 40 GB; never below what the
# rebuild needs, since swap can make up the difference). C++ tools get it
# as ulimit -v plus 16 GB for virtual-only reservations (thread stacks,
# malloc arenas); Lean runs in a systemd scope with MemoryMax (ulimit -v
# would stop Lean from creating threads).
#
# The model stage regenerates committed source files (model_vertices.*,
# codebdd.json, and Noperthedron's Vertices.lean etc.), so it only runs
# when asked for (--from model or --only model).
set -euo pipefail

STAGES=(model tube tubepack search pack verify)
FROM=tube
ONLY=""
DRY=0
THREADS=$(nproc)
RAM_GB=$(awk '/MemTotal/ {print int($2 / 1048576)}' /proc/meminfo)
MEM_GB=$(( RAM_GB * 9 / 10 > 40 ? RAM_GB * 9 / 10 : 40 ))
WORK=""
MODEL_FILE=snub_model.txt
NOPERT=$(cd "$(dirname "$0")" && pwd)
LEAN=$NOPERT/../Noperthedron
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
# Lean executables run under a memory cap (ulimit -v would stop Lean's threads).
lean_run() {
  run systemd-run --scope -q -p MemoryMax="${MEM_GB}G" "$@"
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

echo "== resources: $THREADS threads, memory cap ${MEM_GB} GB (RAM ${RAM_GB} GB)"
if [ "$RAM_GB" -lt 40 ]; then
  echo "warning: ${RAM_GB} GB of RAM; Lean verification needs ~30 GB at peak, so expect swapping" >&2
fi
ulimit -v $(( (MEM_GB + 16) * 1048576 ))
[ -n "$WORK" ] || WORK=$NOPERT/rebuild-work
TREES1=$WORK/trees_r1
TREES2=$WORK/trees_r2
TUBEPACKS=$WORK/tube_packs
JOBS=$WORK/jobs
PACKS=$WORK/packs
run mkdir -p "$WORK"

echo "== build"
run make -C "$NOPERT" -j "$THREADS" codebdd.exe tubecode.exe tuberefine.exe \
  export_codetrees_pack.exe search5d.exe pack5d.exe scoreboard5d.exe
# Lean is needed only by the model (generated sources) and verify stages.
# (The model stage builds Lean after regenerating its data.)
if want verify && ! want model; then
  (cd "$LEAN" && lean_run lake build constructSnubDodecahedron check_global_rows validate_code_pack)
fi

if want model; then
  echo "== model"
  (cd "$NOPERT" && run python3 snub_model.py "$MODEL_FILE" symmetry_neighbors.h)
  (cd "$NOPERT" && run ./codebdd.exe --model_file="$MODEL_FILE" codebdd.json)
  (cd "$LEAN" && run python3 scripts/update_vertices.py \
    && run python3 scripts/emit_tangent_cones.py Noperthedron/SnubDodecahedron/GeneratedTangentCones.lean \
    && run python3 scripts/emit_wedge_cover.py Noperthedron/SnubDodecahedron/WedgeCoverData.lean \
    && run python3 scripts/snub_ico_group.py)
  run make -C "$NOPERT" -j "$THREADS" codebdd.exe tubecode.exe tuberefine.exe \
    export_codetrees_pack.exe search5d.exe pack5d.exe
  (cd "$LEAN" && lean_run lake build constructSnubDodecahedron check_global_rows validate_code_pack)
fi

NCODES=$(python3 -c "import json; print(len(json.load(open('$NOPERT/codebdd.json'))['codes']))")

if want tube; then
  echo "== tube ($NCODES codes)"
  for code in $(seq 0 $((NCODES - 1))); do
    (cd "$NOPERT" && run ./tubecode.exe --code "$code" --output_dir "$TREES1" --threads "$THREADS")
  done
  for code in $(seq 0 $((NCODES - 1))); do
    (cd "$NOPERT" && run ./tuberefine.exe --code "$code" --in_dir "$TREES1" --out_dir "$TREES2" \
      --goal 1/50000 --threads "$THREADS")
  done
fi

if want tubepack; then
  echo "== tubepack"
  (cd "$NOPERT" && run ./export_codetrees_pack.exe --trees_dir "$TREES2" --out_dir "$TUBEPACKS" \
    --bdd codebdd.json)
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
  (cd "$LEAN" && lean_run .lake/build/bin/constructSnubDodecahedron "$TUBEPACKS/manifest.txt" "$PACKS")
fi
