# Helpers shared by the solids' rebuild scripts (search/<solid>/rebuild.sh),
# which source this file after setting DRY (1: print the commands only),
# STAGES, FROM and ONLY, and set WORK before calling stage_begin/stage_end
# or the background Lean build.

# The memory caps need systemd-run --user (a systemd user session). Without
# one (e.g. in a container whose PID 1 is not systemd), run uncapped.
if systemd-run --user --scope -q true 2> /dev/null; then
  HAVE_SCOPE=1
else
  HAVE_SCOPE=0
  echo "== systemd-run --user is not available: running without memory caps" >&2
fi

# Whether to run STAGE (--only STAGE, or STAGE at or after --from).
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

# Stage banners; stage_end appends "<stage> <date> <seconds>s" to
# WORK/stages.log (not in a dry run).
STAGE_T0=0
stage_begin() { echo "== $1 ($(date +%T))"; STAGE_T0=$(date +%s); }
stage_end() {
  local dt=$(( $(date +%s) - STAGE_T0 ))
  [ "$DRY" -eq 1 ] || echo "$1 $(date +%F_%T) ${dt}s" >> "$WORK/stages.log"
  echo "== $1 done in ${dt}s"
}

# The Lean build (lake build construct<Solid>) in the background, so that it
# overlaps the C++ stages. lean_build_start DIR CMD... starts CMD in DIR
# (output to WORK/lean_build.log); lean_build_wait waits for it and fails
# the script if it failed (a no-op if none is running). A build still
# running when the script exits (e.g. after a failed stage) is stopped.
LEAN_BUILD_PID=""
lean_build_start() {
  local dir=$1; shift
  echo "+ [in $dir, in the background, log $WORK/lean_build.log] $*" >&2
  [ "$DRY" -eq 1 ] && return
  [ -z "$LEAN_BUILD_PID" ] || lean_build_wait
  (cd "$dir" && exec "$@") > "$WORK/lean_build.log" 2>&1 &
  LEAN_BUILD_PID=$!
}
lean_build_wait() {
  [ -n "$LEAN_BUILD_PID" ] || return 0
  echo "== waiting for the Lean build (log $WORK/lean_build.log)"
  local pid=$LEAN_BUILD_PID rc=0
  LEAN_BUILD_PID=""
  wait "$pid" || rc=$?
  if [ $rc -ne 0 ]; then
    tail -20 "$WORK/lean_build.log" >&2
    echo "the Lean build failed (exit status $rc; see $WORK/lean_build.log)" >&2
    exit 1
  fi
  echo "== Lean build done"
}
lean_build_stop() {
  if [ -n "$LEAN_BUILD_PID" ] && kill -0 "$LEAN_BUILD_PID" 2> /dev/null; then
    echo "== stopping the background Lean build" >&2
    pkill -P "$LEAN_BUILD_PID" 2> /dev/null || true
    kill "$LEAN_BUILD_PID" 2> /dev/null || true
  fi
}
trap lean_build_stop EXIT
