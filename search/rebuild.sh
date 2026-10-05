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
#            the search's caps file (dh_caps.py) and Lean's DHCapData
#   ties     the tie tubes with their certificates (tietube --export_dir) and
#            Lean's DHTieData (dh_tie_lean.py)
#   search   5D search, charts 0-2 (search5d), until nothing is deferred
#   pack     per-code 5D packs (pack5d --per_code --tie_nodes)
#   verify   Lean: check caps, ties and every table and build the proof
#            (constructDeltoidalHexecontahedron)
#
# Every stage is restartable: tubecode and search5d journal their work, and
# pack5d skips packs newer than their journals. capcert, tietube, tubecode and
# pack5d are deterministic (independent of --threads); search5d is not (work
# order). To re-verify an existing result, start from its packs and
# certificates (--from verify with --work pointing at them).
#
# Usage: ./rebuild.sh [--from STAGE] [--only STAGE] [--dry_run] [--threads N]
#        [--mem_gb G] [--work DIR]   (default ./rebuild-work)
#
# Resources (2026-10-05, 64 cores): capcert ux ~1 h (exact, 24 threads), the
# 5D search several hours, pack5d chart 0 ~45 min (2.2 GB of packs), the Lean
# verifier several hours (caps ~30 min, ties ~4 min, chart 0 ~36 M rows).
# Lean runs in a systemd scope with MemoryMax (ulimit -v would stop Lean from
# creating threads).
#
# The model, caps and ties stages regenerate committed source files (the model
# files, codebdd.json, dh_exact.txt, dh_tie_data.txt, tie_normals.h, and
# Noperthedron's Vertices.lean, DHStatementData, DHCapData, DHTieData etc.), so
# they only run when asked for (--from model, --only caps, ...); the default
# start is tube (with the committed data).
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
LEAN=$NOPERT/../Noperthedron
export MODEL_DIR=$NOPERT
export NOPERTHEDRON=$LEAN
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
lean_run() {
  run systemd-run --scope -q -p MemoryMax="${MEM_GB}G" -p MemorySwapMax=0 "$@"
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
[ -n "$WORK" ] || WORK=$NOPERT/rebuild-work
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
build_lean() {
  (cd "$LEAN" && lean_run lake build constructDeltoidalHexecontahedron check_global_rows dhBench)
}

if want model; then
  echo "== model"
  (cd "$NOPERT" && run python3 dh_model.py snub_model.txt dh_model.txt)
  (cd "$NOPERT" && run ./codebdd.exe --model_file=dh_model.txt --model_faces codebdd.json)
  (cd "$NOPERT" && run python3 dh_exact.py dh_model.txt dh_exact.txt)
  (cd "$NOPERT" && run python3 dh_tie_data.py dh_exact.txt dh_tie_data.txt)
  (cd "$LEAN" && run python3 scripts/update_vertices.py \
    && run python3 scripts/emit_wedge_cover.py --bdd "$NOPERT/codebdd.json" \
         Noperthedron/PentagonalHexecontahedron/WedgeCoverData.lean \
    && run python3 scripts/snub_ico_group.py --model_file dh_model.txt \
    && run python3 scripts/dh_statement_data.py)
  run make -C "$NOPERT" -j "$THREADS" codebdd.exe tubecode.exe export_codetrees_pack.exe capcert.exe \
    tietube.exe search5d.exe pack5d.exe
fi

if want tube; then
  echo "== tube"
  NCODES=$(python3 -c "import json; print(len(json.load(open('$NOPERT/codebdd.json'))['codes']))")
  for code in $(seq 0 $((NCODES - 1))); do
    (cd "$NOPERT" && run ./tubecode.exe --code "$code" --output_dir "$TREES" --threads "$THREADS" \
      "${TUBE_CAPS[@]}" --cap_r 1/40 --min_r 1/10000)
  done
fi

if want tubepack; then
  echo "== tubepack"
  (cd "$NOPERT" && run ./export_codetrees_pack.exe --trees_dir "$TREES" --out_dir "$TUBEPACKS" \
    --bdd codebdd.json)
fi

if want caps; then
  echo "== caps"
  (cd "$NOPERT" && run ./capcert.exe --cap u0 --frame_only > "$WORK/frame_u0.txt")
  (cd "$NOPERT" && run ./capcert.exe --cap ux --aniso --frame_only > "$WORK/frame_ux.txt")
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
    "$LEAN/Noperthedron/PentagonalHexecontahedron/DHCapData.lean" \
    "$WORK/frame_u0.txt:41/4096:1/50:prune" "$WORK/frame_ux.txt:41/4096:1/80" "$WORK/frame_u0.txt:41/1024:1/320:prune")
fi

if want ties; then
  echo "== ties"
  (cd "$NOPERT" && run ./tietube.exe --threads "$THREADS" --sigma_depth 6 --max_depth 12 "${TUBE_CAPS[@]}" \
    --trees_dir "$TREES" --out_dir "$TIES" --export_dir "$TIES/cert")
  (cd "$NOPERT" && run ./tietube.exe --t 37 --threads "$THREADS" --sigma_depth 6 --max_depth 14 \
    --min_rho 1/16384 "${TUBE_CAPS[@]}" --trees_dir "$TREES" --out_dir "$TIES" --export_dir "$TIES/cert")
  (cd "$NOPERT" && run python3 dh_tie_lean.py --export "$TIES/cert")
  run cp "$NOPERT/dh_tie_data.txt" "$TIES/cert/"
fi

if want verify || want caps || want ties; then
  echo "== build Lean"
  build_lean
fi

if want search; then
  echo "== search"
  (cd "$NOPERT" && run ./search5d.exe --all --charts 0,1,2 --threads "$THREADS" --commit_depth 12 \
    --subtree_budget 50000 --max_depth 200 --trees_dir "$TREES" --view_scale 4 --max_full_retry 1024 \
    --half_turn_prune --tie_dir "$TIES" --caps "$CAPS_FILE" --out_dir "$JOBS" \
    --retry_deferred --requeue_deferred)
  (cd "$NOPERT" && run ./scoreboard5d.exe --journals "$JOBS" | tail -1)
fi

if want pack; then
  echo "== pack"
  for chart in 0 1 2; do
    (cd "$NOPERT" && run ./pack5d.exe --chart "$chart" --per_code "$PACKS" --journals "$JOBS" \
      --trees_dir "$TREES" --bdd codebdd.json --tie_nodes "$TIES/cert/nodes.txt" --threads "$THREADS")
  done
fi

if want verify; then
  echo "== verify"
  (cd "$LEAN" && lean_run .lake/build/bin/constructDeltoidalHexecontahedron "$TUBEPACKS/manifest.txt" "$PACKS" \
    "$CERTS" "$TIES/cert")
fi
