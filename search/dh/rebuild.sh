#!/bin/bash
# Rebuilds the proof that the deltoidal hexecontahedron is a Nopert (not
# Rupert), end to end:
#
#   model    the exact model (dh_model.py: McCooey's coordinates in the snub's
#            frame), codes and code triangles (codebdd --model_faces), the
#            exact solid over K = Q(sqrt5, sin 72) (dh_exact.py), the tie data
#            (dh_tie_data.py), and the Lean data generated from them
#   tube     identity tube, one quadtree per code (tubecode), with the two
#            caps (u0, ux) left to the cap theorems
#   tubepack tube trees -> Lean packs + manifest (export_codetrees_pack)
#   caps     the three cap certificates (capcert --export: u0, ux, u0 wide),
#            the search's caps file (dh_caps.py) and Lean's CapData
#   ties     the tie tubes with their certificates (tietube --export_dir) and
#            Lean's TieData (dh_tie_lean.py)
#   search   5D search, charts 0-2 (search5d), until nothing is deferred
#   pack     per-code 5D packs (pack5d --per_code --tie_nodes)
#   verify   Lean: check caps, ties and every table and build the proof
#            (constructDeltoidalHexecontahedron in ../../proof)
#
# Every stage is restartable: tubecode and search5d journal their work, and
# pack5d skips packs newer than their journals. capcert, tietube, tubecode and
# pack5d are deterministic (independent of --threads); search5d is not (work
# order). To re-verify an existing result, start from its packs and
# certificates (--from verify with --work pointing at them).
#
# Usage: ./rebuild.sh [--from STAGE] [--only STAGE] [--dry_run] [--threads N]
#        [--mem_gb G] [--work DIR]   (default ../../work-dh)
#
# Resources (measured 2026-10-06, 64 cores, --from model: 8 h 10 min in all):
# model through ties ~6 min, search 4 h 36 min, pack 35 min (chart 0 2 GB),
# verify 2 h 52 min (caps 19 min, ties 4 min, chart 0 32.9 M rows; ~30 GB).
# Lean runs in a systemd scope with MemoryMax (ulimit -v would stop Lean from
# creating threads).
#
# The model, caps and ties stages regenerate committed source files (the model
# files, dh_exact.txt, dh_tie_data.txt, tie_normals.h, and
# ../../proof/DeltoidalHexecontahedron's SolidModel (vertices), WedgeCoverData,
# OrbitData, StatementData, CapData and TieData, and ../../proof/Pipeline/
# IcoGroupData; all but CapData and TieData with scripts/), so
# they only run when asked for (--from model, --only caps, ...); the default
# start is tube (with the committed data). The model stage also writes
# codebdd.json, which is not committed and which the later stages need: in a
# fresh clone, run --from model (or first --only model).
#
# Each stage's wall time is appended to WORK/stages.log. The Lean build runs
# in the background while the C++ stages run (log WORK/lean_build.log); the
# verify stage waits for it, and the script fails if it fails. (Helpers:
# ../common/rebuild_lib.sh.)
set -euo pipefail

STAGES=(model tube tubepack caps ties search pack verify)
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
export NOPERTS_PROOF=$LEAN
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
  echo "+ $*" >&2
  if [ $DRY -eq 0 ]; then "$@"; fi
}
# run, with stdout to the file $1 (not opened in a dry run).
run_to() {
  local out=$1; shift
  echo "+ $* > $out" >&2
  if [ $DRY -eq 0 ]; then "$@" > "$out"; fi
}
# HAVE_SCOPE, want, stage_begin/stage_end, the background Lean build.
source "$NOPERT/../common/rebuild_lib.sh"
lean_run() {
  if [ $HAVE_SCOPE -eq 1 ]; then
    run systemd-run --user --scope -q -p MemoryMax="${MEM_GB}G" -p MemorySwapMax=0 "$@"
  else
    run "$@"
  fi
}

echo "== resources: $THREADS threads, memory cap ${MEM_GB} GB (RAM ${RAM_GB} GB)"
[ -n "$WORK" ] || WORK=$(cd "$NOPERT/../.." && pwd)/work-dh
TREES=$WORK/trees
TUBEPACKS=$WORK/tube_packs
CERTS=$WORK/certs
TIES=$WORK/ties
JOBS=$WORK/jobs
PACKS=$WORK/packs
CAPS_FILE=$WORK/caps.txt
run mkdir -p "$WORK" "$CERTS" "$TIES"
# The two caps for the tube and tie stages: unit center, angular radius.
TUBE_CAPS=(--cap 0.30901699437494740,0.42532540417601999,0.85065080835203999,0.01
           --cap 0.42532540417601994,0.13819660112501050,0.89442719099991588,0.01)
# The cap certificates' options (u0: half-turn cell; ux: anisotropic, tie cones, tie scheme).
CAP_U0=(--cap u0 --mu0 41/4096 --strong_scale 200 --ratio_z 64 --max_depth 34 --try 32)
CAP_UX=(--cap ux --aniso --mu0 41/4096 --strong_scale 128 --ratio_z 64
        --z_override face:0:1:-1=1024,face:1:1:1=1024,face:2:1:1=32 --t0_mcone 0.5 --mcone_strong_mul 4
        --tie_charts face:2:1:1,face:2:1:-1 --tie_ratio 24 --tie_k 1024 --try 200 --max_depth 32)
CAP_U0W=(--cap u0 --mu0 41/1024 --strong_scale 2 --ratio_z 32 --max_depth 32 --try 24)

echo "== build"
run make -C "$NOPERT" -j "$THREADS" codebdd.exe tubecode.exe export_codetrees_pack.exe capcert.exe \
  tietube.exe search5d.exe pack5d.exe scoreboard5d.exe
# The Lean build (in the background: lean_build_start), under the same cap.
LEAN_BUILD=(lake build constructDeltoidalHexecontahedron)
[ $HAVE_SCOPE -eq 0 ] || LEAN_BUILD=(systemd-run --user --scope -q -p MemoryMax="${MEM_GB}G" -p MemorySwapMax=0 "${LEAN_BUILD[@]}")

if want model; then
  stage_begin model
  (cd "$NOPERT" && run python3 dh_model.py snub_model.txt dh_model.txt)
  (cd "$NOPERT" && run ./codebdd.exe --model_file=dh_model.txt --model_faces codebdd.json)
  (cd "$NOPERT" && run python3 dh_exact.py dh_model.txt dh_exact.txt)
  (cd "$NOPERT" && run python3 dh_tie_data.py dh_exact.txt dh_tie_data.txt)
  (cd "$NOPERT" && run python3 scripts/update_vertices.py \
    && run python3 ../common/emit_wedge_cover.py --bdd codebdd.json \
         --namespace DeltoidalHexecontahedron.WedgeCover "$LEAN/DeltoidalHexecontahedron/WedgeCoverData.lean" \
    && run python3 scripts/snub_ico_group.py --model_file dh_model.txt \
    && run python3 scripts/dh_statement_data.py)
  run make -C "$NOPERT" -j "$THREADS" codebdd.exe tubecode.exe export_codetrees_pack.exe capcert.exe \
    tietube.exe search5d.exe pack5d.exe
  stage_end model
fi

# codebdd.json is written by the model stage (it is not committed).
require_codebdd tube tubepack ties search pack

if want tube; then
  stage_begin tube
  if [ $DRY -eq 1 ] && [ ! -f "$NOPERT/codebdd.json" ]; then
    NCODES=20  # (dry run before the model stage has written codebdd.json)
  else
    NCODES=$(python3 -c "import json; print(len(json.load(open('$NOPERT/codebdd.json'))['codes']))")
  fi
  for code in $(seq 0 $((NCODES - 1))); do
    (cd "$NOPERT" && run ./tubecode.exe --code "$code" --output_dir "$TREES" --threads "$THREADS" \
      "${TUBE_CAPS[@]}" --cap_r 1/40 --min_r 1/10000)
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
  (cd "$NOPERT" && run_to "$WORK/frame_u0.txt" ./capcert.exe --cap u0 --frame_only)
  (cd "$NOPERT" && run_to "$WORK/frame_ux.txt" ./capcert.exe --cap ux --aniso --frame_only)
  (cd "$NOPERT" && run ./capcert.exe "${CAP_U0[@]}" --threads "$THREADS" --export "$CERTS/u0.cert")
  (cd "$NOPERT" && run ./capcert.exe "${CAP_UX[@]}" --threads "$THREADS" --export "$CERTS/ux.cert")
  (cd "$NOPERT" && run ./capcert.exe "${CAP_U0W[@]}" --threads "$THREADS" --export "$CERTS/u0_wide.cert")
  # The search's caps file: each base cap's 120 images (the order is Lean's dhCapImgs).
  if [ $DRY -eq 0 ]; then
    (cd "$NOPERT" && python3 dh_caps.py 41/4096 1/50 "$WORK/frame_u0.txt" \
      && python3 dh_caps.py 41/4096 1/80 "$WORK/frame_ux.txt" \
      && python3 dh_caps.py 41/1024 1/320 "$WORK/frame_u0.txt") > "$CAPS_FILE"
  fi
  (cd "$NOPERT" && run python3 dh_cap_lean.py \
    "$LEAN/DeltoidalHexecontahedron/CapData.lean" \
    "$WORK/frame_u0.txt:41/4096:1/50:prune" "$WORK/frame_ux.txt:41/4096:1/80" "$WORK/frame_u0.txt:41/1024:1/320:prune")
  stage_end caps
fi

if want ties; then
  stage_begin ties
  (cd "$NOPERT" && run ./tietube.exe --threads "$THREADS" --sigma_depth 6 --max_depth 12 "${TUBE_CAPS[@]}" \
    --trees_dir "$TREES" --out_dir "$TIES" --export_dir "$TIES/cert")
  (cd "$NOPERT" && run ./tietube.exe --t 37 --threads "$THREADS" --sigma_depth 6 --max_depth 14 \
    --min_rho 1/16384 "${TUBE_CAPS[@]}" --trees_dir "$TREES" --out_dir "$TIES" --export_dir "$TIES/cert")
  (cd "$NOPERT" && run python3 dh_tie_lean.py --export "$TIES/cert")
  run cp "$NOPERT/dh_tie_data.txt" "$TIES/cert/"
  stage_end ties
fi

# Lean (with the CapData and TieData just written) builds in the background
# while the search and pack stages run.
if want verify || want caps || want ties; then
  lean_build_start "$LEAN" "${LEAN_BUILD[@]}"
fi

if want search; then
  stage_begin search
  # Blended inner points (search5d's default --blend5d 2) do not pay here:
  # a blended run (2026-10-15) was stopped after 5 h 24 min at 22.1 M nodes,
  # past the unblended run's 22.06 M in all. (The decoder reads them.)
  # TODO: try --blend5d 4 (escalate), which computes blends only where the
  # plain choice fails, so it costs much less per node than 2.
  (cd "$NOPERT" && run ./search5d.exe --all --charts 0,1,2 --threads "$THREADS" --commit_depth 12 \
    --subtree_budget 50000 --max_depth 200 --trees_dir "$TREES" --view_scale 4 --max_full_retry 1024 \
    --half_turn_prune --tie_dir "$TIES" --caps "$CAPS_FILE" --blend5d 0 --out_dir "$JOBS" \
    --retry_deferred --requeue_deferred)
  (cd "$NOPERT" && run ./scoreboard5d.exe --journals "$JOBS" | tail -1)
  stage_end search
fi

if want pack; then
  stage_begin pack
  for chart in 0 1 2; do
    (cd "$NOPERT" && run ./pack5d.exe --chart "$chart" --per_code "$PACKS" --journals "$JOBS" \
      --trees_dir "$TREES" --bdd codebdd.json --tie_nodes "$TIES/cert/nodes.txt" --threads "$THREADS")
  done
  stage_end pack
fi

if want verify; then
  stage_begin verify
  lean_build_wait
  (cd "$LEAN" && lean_run .lake/build/bin/constructDeltoidalHexecontahedron "$TUBEPACKS/manifest.txt" "$PACKS" \
    "$CERTS" "$TIES/cert")
  stage_end verify
fi

# Wait for a background Lean build that the verify stage did not wait for.
lean_build_wait
