#!/bin/bash
# Rebuilds the proof that the SeptopertM12 (the 7-vertex C3v solid) is a Nopert,
# end to end:
#
#   model    codebdd on the committed exact model septopert-m12-model.txt (with the
#            two view triangles T1/T2): model-vertices.*, codebdd.json, and
#            the Lean view cover proof/SeptopertM12/ViewCoverData.lean
#            (proof/scripts/emit_septopert_view_cover.py)
#   tube     identity tube per code (tubecode --min_r 1/100000, the cap at the
#            mirror normal n = (1,0,-1)/sqrt2 left to the cap certificate, and
#            the views of arc-cap.txt, where no first-order leaf exists, left
#            to the arc cap certificate),
#            then tuberefine on the codes away from the cap (codes 6, 9, 11-13
#            touch n and are not refined: it only multiplies their leaves)
#   idcap    identity blow-up certificates (idcap --trees_in/--trees_out,
#            rho 1/64; idcap's defaults: blended inner points, a retry
#            with per-contact blends where the pass cannot descend, 4 codes
#            at once): tube subtrees replaced by blow-up rows (Lean
#            Row.idcap) where they certify; the later stages use these trees
#   tubepack tube trees -> Lean tube packs + manifest (export-codetrees-pack)
#   cap      the cap certificate at n (capcert-septopert-m12 --mu0 1/16 --max_depth 38)
#            and the search's caps file (frame x = (1,0,-1), e1 = (0,2,0),
#            e2 = (1,0,1), mu0 = 1/16, |w| <= 1/91)
#   arccert  cap 1, the arc cap certificate near U = (2,2,-1)/3 and the arc from U
#            towards n: capcert-m12 --solid m12, one run per piece of the cover
#            (146 charts, t* = 4/19, 5/14). Claim: views of arc-cap.txt, |w| <= 1/46.
#   axiscert cap 2, the axis cap at (1,1,1): capcert-m12 --frame axis (52 charts)
#   pcapcert cap 3, the P cap at P = (2,1,0): capcert-m12 --frame P, wedge WP (26
#            charts) and U cap (52 charts), then leaf2cert.py (../common)
#   search   5D search, 16 code triangles x charts 0-3, rounds until nothing
#            is deferred (search5d --retry_deferred --requeue_deferred; its
#            default blended inner points: pack tags 17 / 18)
#   pack     per-code 5D packs c<C>/t<T>.pack (pack5d --per_code)
#   verify   Lean: constructSeptopertM12 <tube manifest> <packs> <cap.cert> <arc.cert> <axis> <pcap-wp> <pcap-u>
#            (the regenerated certificates of WORK, not proof/*/data)
#
# Every stage is restartable (tubecode and search5d journal their work; pack5d
# skips packs newer than their journals). search5d is not deterministic (work
# order); the others are.
#
# Usage: ./rebuild.sh [--from STAGE] [--only STAGE] [--dry_run]
#        [--threads N] [--mem_gb G] [--work DIR]
#        (default: from model, one thread per core, 100 GB, ../../work; a fresh
#        clone has no codebdd.json, which only the model stage writes)
# Long stages run in a systemd scope with MemoryMax (and no swap); each
# stage's wall time and the scope's peak memory are appended to
# WORK/stages.log.
# The Lean build runs in the background while the C++ stages run (log
# WORK/lean_build.log); the verify stage waits for it, and the script fails
# if it fails. (Helpers: ../common/rebuild-lib.sh.)
set -euo pipefail

STAGES=(model tube idcap tubepack cap arccert axiscert pcapcert search pack verify)
FROM=model
ONLY=""
DRY=0
THREADS=$(nproc)
MEM_GB=100
WORK=""
NOPERT=$(cd "$(dirname "$0")" && pwd)
LEAN=$NOPERT/../../proof
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
[ -n "$WORK" ] || WORK=$NOPERT/../../work
TREES_RAW=$WORK/trees_raw
TREES=$WORK/trees
TREES_ID=$WORK/trees_id
TUBEPACKS=$WORK/tube_packs
JOBS=$WORK/jobs
PACKS=$WORK/packs
CAP_CERT=$WORK/cap-1_16.cert
CAPS_FILE=$WORK/caps.txt
ARC_CERT=$WORK/arc.cert
AXIS_CERT=$WORK/axis-cap.cert
PCAP_WP=$WORK/pcap-wp.cert
PCAP_U=$WORK/pcap-u.cert
# The arc cap's views and rotations (tubecode, search5d). Index 1 in the trees
# and journals (after the cap at n); Lean routes it to arcLeafOk.
ARC_CAP=(--piece_caps arc-cap.txt)

# HAVE_SCOPE, want, stage_begin/stage_end, the background Lean build.
source "$NOPERT/../common/rebuild-lib.sh"
run() {
  echo "+ $*" >&2
  if [ $DRY -eq 0 ]; then "$@"; fi
}
# A command in a memory-capped scope (no swap); prints its peak memory.
# (Without systemd-run, just the command.)
capped() {
  # (Called in subshells: the unit name must not depend on a counter.)
  local unit="neosept-$$-$(date +%s%N)"
  echo "+ [scope ${MEM_GB}G] $*" >&2
  if [ $DRY -eq 1 ]; then return; fi
  if [ $HAVE_SCOPE -eq 0 ]; then "$@"; return; fi
  systemd-run --user --scope -q --unit="$unit" -p MemoryMax="${MEM_GB}G" -p MemorySwapMax=0 \
    bash -c '"$@"; rc=$?; f=/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup)/memory.peak;
             [ -r "$f" ] && echo "peak memory: $(( $(cat "$f") / 1048576 )) MiB" >&2; exit $rc' _ "$@"
}

# (Also in a dry run, so that df below has a directory to look at.)
mkdir -p "$WORK"
# The work directory needs a few GB (the refined tube trees ~2 GB; journals
# and packs under 200 MB); a full disk silently truncates them.
echo "== free space: $(df -h "$WORK" | awk 'NR == 2 {print $4}')"
echo "== $THREADS threads, memory cap ${MEM_GB} GB, work $WORK"
NCODES=13
NTRI=16

echo "== build"
run make -C "$NOPERT" -j "$THREADS" codebdd.exe tubecode.exe tuberefine.exe idcap.exe export-codetrees-pack.exe \
  capcert-septopert-m12.exe capcert-m12.exe search5d.exe pack5d.exe dfwhere.exe

if want model; then
  stage_begin model
  (cd "$NOPERT" && run ./codebdd.exe --model_file=septopert-m12-model.txt codebdd.json)
  # The view cover (Lean: SeptopertM12/ViewCoverData.lean) from codebdd.json.
  run python3 -B "$LEAN/scripts/emit_septopert_view_cover.py" --bdd "$NOPERT/codebdd.json" --solid SeptopertM12 --model_file septopert-m12-model.txt \
    "$LEAN/SeptopertM12/ViewCoverData.lean"
  run make -C "$NOPERT" -j "$THREADS" tubecode.exe tuberefine.exe idcap.exe export-codetrees-pack.exe search5d.exe pack5d.exe
  stage_end model
fi

# The checker's Lean build (no-op if current), in the background while the
# C++ stages run.
if want verify; then
  if [ $HAVE_SCOPE -eq 1 ]; then
    LEAN_CMD=(timeout 6000 systemd-run --user --scope -q -p MemoryMax=48G -p MemorySwapMax=0 lake build constructSeptopertM12)
  else
    LEAN_CMD=(timeout 6000 lake build constructSeptopertM12)
  fi
  lean_build_start "$LEAN" "${LEAN_CMD[@]}"
fi

# codebdd.json is written by the model stage (it is not committed).
require_codebdd tube idcap tubepack search pack

# The cap at n for the tube (angular radius 0.04 < the cap cone's 0.044), and
# the arc cap.
# EXPERIMENT (M12): a disc at the 3-fold axis view stands in for its cap, not yet built.
TUBE_CAP=(--cap 0.70710678118654752,0,-0.70710678118654752,0.04 "${ARC_CAP[@]}" --cap_r 1/46)

if want tube; then
  stage_begin tube
  run mkdir -p "$TREES_RAW" "$TREES"
  for code in $(seq 0 $((NCODES - 1))); do
    (cd "$NOPERT" && capped ./tubecode.exe --code "$code" --output_dir "$TREES_RAW" --threads "$THREADS" \
      "${TUBE_CAP[@]}" --min_r 1/100000 --best_cage)
  done
  # Refinement (larger certified radii) away from the cap; code 1 (the
  # first-order margin minimum) with a lower goal to keep its tree small.
  for code in $(seq 0 $((NCODES - 1))); do
    case $code in
      (0|5|7|9|10|11) run cp "$TREES_RAW/tree.$code.json" "$TREES/tree.$code.json" ;;
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

if want idcap; then
  stage_begin idcap
  (cd "$NOPERT" && capped ./idcap.exe --trees_in "$TREES" --trees_out "$TREES_ID" --pass_depth 6 \
    --max_leaves 2000 --rho 1/64 --threads "$THREADS" --max_depth 40)
  stage_end idcap
fi

if want tubepack; then
  stage_begin tubepack
  (cd "$NOPERT" && capped ./export-codetrees-pack.exe --trees_dir "$TREES_ID" --out_dir "$TUBEPACKS" \
    --bdd codebdd.json)
  stage_end tubepack
fi

if want cap; then
  stage_begin cap
  (cd "$NOPERT" && capped ./capcert-septopert-m12.exe --model septopert-m12-model.txt --mu0 1/16 --max_depth 38 \
    --threads "$THREADS" --export "$CAP_CERT")
  # The search's caps file (search5d --caps): x e1 e2 mu0 wmax (doubles),
  # the exact frame (a b c d per coordinate, here rational: b = c = d = 0),
  # mu0 and wmax^2.
  if [ $DRY -eq 0 ]; then
    echo "1 0 -1 0 2 0 1 0 1 0.0625 0.01098901098901099 1 0 0 0 0 0 0 0 -1 0 0 0 0 0 0 0 2 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 1 0 0 0 1/16 1/8281" > "$CAPS_FILE"
  fi
  stage_end cap
fi

# The arc cap certificate (cap 1): the U cap and the arc wedge, one capcert-m12 run
# per piece of the cover (U cap; wedge pieces W0, Wm, W1, W2, meeting at
# t* = 4/19 and 5/14), exact, with the parameters of Lean's ArcCap.neoParams. The
# pieces' exports, concatenated in this order, are the certificate.
CAPCERT=(./capcert-m12.exe --solid m12)
if want arccert; then
  stage_begin arccert
  ARC_MU0=1/8; ARC_NU0=1/8; ARC_R1=3; ARC_R2=32; ARC_R3=128; ARC_Z=16
  ARC_TS=4/19; ARC_TE=5/14
  ARC_COMMON=(--max_depth 44 --max_fail 2000 --try 16 --threads "$THREADS" --exact)
  ARC_W=(--family W --nu0 $ARC_NU0 --R1 $ARC_R1 --R2 $ARC_R2 --R3 $ARC_R3 --Z $ARC_Z --Zc $ARC_Z
         --R2c $ARC_R2 --R3c $ARC_R3 "${ARC_COMMON[@]}")
  (cd "$NOPERT" && capped "${CAPCERT[@]}" --family U --mu0 $ARC_MU0 --nu0 $ARC_NU0 --R1 $ARC_R1 --R2 $ARC_R2 \
    --R3 $ARC_R3 --wedge_prune "${ARC_COMMON[@]}" --export "$ARC_CERT.U")
  (cd "$NOPERT" && capped "${CAPCERT[@]}" "${ARC_W[@]}" --regime 0 --piece 0 --tlo 0 --thi $ARC_TS --zh 2 \
    --export "$ARC_CERT.W0")
  (cd "$NOPERT" && capped "${CAPCERT[@]}" "${ARC_W[@]}" --regime 0 --piece 1 --tlo $ARC_TS --thi $ARC_TS --tmid 6 \
    --export "$ARC_CERT.Wm")
  (cd "$NOPERT" && capped "${CAPCERT[@]}" "${ARC_W[@]}" --regime 1 --piece 2 --tlo $ARC_TS --zl 2 --thi $ARC_TE \
    --export "$ARC_CERT.W1")
  (cd "$NOPERT" && capped "${CAPCERT[@]}" "${ARC_W[@]}" --regime 1 --piece 3 --tlo $ARC_TE --thi 13/32 \
    --export "$ARC_CERT.W2")
  if [ $DRY -eq 0 ]; then
    cat "$ARC_CERT.U" "$ARC_CERT.W0" "$ARC_CERT.Wm" "$ARC_CERT.W1" "$ARC_CERT.W2" > "$ARC_CERT"
    rm "$ARC_CERT.U" "$ARC_CERT.W0" "$ARC_CERT.Wm" "$ARC_CERT.W1" "$ARC_CERT.W2"
  fi
  stage_end arccert
fi

# The axis cap certificate (cap 2): the U cap in the axis frame at the 3-fold
# axis (1,1,1), 4 sides x 13 chart kinds = 52 charts, exact. The tool numbers the
# sides' ids 1 (side 0) and 0 (sides 1, 2, 3); renumbered here to Lean's codes
# (ArcCapDecode.parseId): side 0 -> 1, side 1 -> 2, side 2 -> 3, side 3 -> 0.
if want axiscert; then
  stage_begin axiscert
  (cd "$NOPERT" && capped "${CAPCERT[@]}" --family U --frame axis --sides 0123 --mu0 1/16 --R 2 --S 16 --Rc 1 --Sc 16 \
    --max_depth 40 --max_fail 300 --try 16 --threads "$THREADS" --exact --export "$AXIS_CERT.raw")
  if [ $DRY -eq 0 ]; then
    awk 'BEGIN{n=0} /^chart u /{ s=int(n/13); n++; $3 = (s==0?1:(s==1?2:(s==2?3:0))) } {print}' \
      "$AXIS_CERT.raw" > "$AXIS_CERT"
    rm "$AXIS_CERT.raw"
    echo "axis cap: $(grep -c '^chart' "$AXIS_CERT") charts"
  fi
  stage_end axiscert
fi

# The P cap certificate (cap 3): P = (2,1,0), the wedge along face 024's
# circle (family WP, 26 charts) and the U cap at P with the wedge prune
# (52 charts), exact. The tool logs the closed leaves; leaf2cert.py turns them
# into the Lean certificate trees (pcap-wp.cert, pcap-u.cert).
if want pcapcert; then
  stage_begin pcapcert
  (cd "$NOPERT" && capped "${CAPCERT[@]}" --family WP --frame P --fpolar --nu0 1 --tlo 0 --thi 1/8 --R1 2 --R2 2 \
    --R3 16 --Z 8 --max_depth 40 --max_fail 60 --try 16 --threads "$THREADS" --exact --leaflog "$PCAP_WP.leaf")
  (cd "$NOPERT" && capped "${CAPCERT[@]}" --family U --frame P --sides 0123 --mu0 1/8 --R 0.5 --S 2 --Rc 0.25 --Sc 2 \
    --wp_prune --nu0 1 --thi 1/8 --R1 2 --R2 2 --R3 16 --max_depth 46 --max_fail 300 --try 16 --threads "$THREADS" \
    --exact --leaflog "$PCAP_U.leaf")
  run python3 -B "$NOPERT/../common/leaf2cert.py" "$PCAP_WP" WP "$PCAP_WP.leaf"
  run python3 -B "$NOPERT/../common/leaf2cert.py" "$PCAP_U" U "$PCAP_U.leaf"
  if [ $DRY -eq 0 ]; then
    echo "P cap: WP $(grep -c '^chart' "$PCAP_WP") charts, $(wc -l < "$PCAP_WP.leaf") leaves;" \
         "U $(grep -c '^chart' "$PCAP_U") charts, $(wc -l < "$PCAP_U.leaf") leaves"
    rm "$PCAP_WP.leaf" "$PCAP_U.leaf"
  fi
  stage_end pcapcert
fi

SEARCH=(--all --charts 0,1,2,3 --threads "$THREADS" --commit_depth 12 --subtree_budget 200000
        --max_depth 200 --trees_dir "$TREES_ID" --view_scale 4 --max_full_retry 1024 --half_turn_prune
        --caps "$CAPS_FILE" "${ARC_CAP[@]}" --out_dir "$JOBS" --requeue_deferred)
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
      --trees_dir "$TREES_ID" --bdd codebdd.json --threads "$THREADS")
  done
  stage_end pack
fi

if want verify; then
  stage_begin verify
  lean_build_wait
  [ $DRY -eq 1 ] || [ -x "$LEAN/.lake/build/bin/constructSeptopertM12" ] || {
    echo "missing $LEAN/.lake/build/bin/constructSeptopertM12 (lake build constructSeptopertM12)" >&2; exit 1; }
  capped "$LEAN/.lake/build/bin/constructSeptopertM12" "$TUBEPACKS/manifest.txt" "$PACKS" "$CAP_CERT" "$ARC_CERT" \
    "$AXIS_CERT" "$PCAP_WP" "$PCAP_U" \
    2>&1 | tee "$WORK/verify.log"
  stage_end verify
fi
