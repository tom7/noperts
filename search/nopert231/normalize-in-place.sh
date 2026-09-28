#!/usr/bin/env bash
# Driver script to normalize chart files in place with verification.
set -euo pipefail

usage() {
  cat <<EOF
Usage: $0 <chart.rows.log> [tmp_file_or_dir]

Normalizes a chart rows log to the compact chart229 format in place:
1. Streams input through normalize-chart.exe into a temporary file.
2. Verifies semantic equality of every row using compare-charts.exe in RAM.
3. Replaces the original file with the verified normalized file.

If [tmp_file_or_dir] is not specified, uses <chart.rows.log>.tmp.\$\$
EOF
  exit 1
}

if [ $# -lt 1 ] || [ "${1:-}" = "-h" ] || [ "${1:-}" = "--help" ]; then
  usage
fi

INPUT_FILE="$1"

if [ ! -f "$INPUT_FILE" ]; then
  echo "Error: Input file '$INPUT_FILE' not found or is not a regular file." >&2
  exit 1
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
NORMALIZE_BIN="${SCRIPT_DIR}/normalize-chart.exe"
COMPARE_BIN="${SCRIPT_DIR}/compare-charts.exe"

if [ ! -x "$NORMALIZE_BIN" ]; then
  echo "Error: Normalizer binary '$NORMALIZE_BIN' not found or not executable." >&2
  echo "Please build it with: make -C nopert229 -j 8 default" >&2
  exit 1
fi

if [ ! -x "$COMPARE_BIN" ]; then
  echo "Error: Comparator binary '$COMPARE_BIN' not found or not executable." >&2
  echo "Please build it with: make -C nopert229 -j 8 default" >&2
  exit 1
fi

# Determine temporary file path
if [ $# -ge 2 ]; then
  if [ -d "$2" ]; then
    TMP_FILE="$2/$(basename "$INPUT_FILE").tmp.$$"
  else
    TMP_FILE="$2"
  fi
else
  TMP_FILE="${INPUT_FILE}.tmp.$$"
fi

if [ "$INPUT_FILE" = "$TMP_FILE" ]; then
  echo "Error: Temporary file cannot be the same as input file." >&2
  exit 1
fi

KEEP_TMP=0
cleanup() {
  if [ -f "$TMP_FILE" ] && [ "$KEEP_TMP" -eq 0 ]; then
    echo "Cleaning up temporary file: $TMP_FILE"
    rm -f "$TMP_FILE"
  fi
}
trap cleanup EXIT INT TERM

echo "============================================================"
echo "Normalizing chart in place: $INPUT_FILE"
echo "Temporary file:             $TMP_FILE"
echo "============================================================"

echo ""
echo "--- Step 1: Normalizing to temporary file ---"
"$NORMALIZE_BIN" "$INPUT_FILE" "$TMP_FILE"

echo ""
echo "--- Step 2: Verifying in-memory semantic equivalence ---"
"$COMPARE_BIN" "$INPUT_FILE" "$TMP_FILE"

echo ""
echo "--- Step 3: Replacing original file with normalized file ---"
# Move/rename the verified normalized file over the original file
mv -f "$TMP_FILE" "$INPUT_FILE"
KEEP_TMP=1

echo "SUCCESS: $INPUT_FILE has been verified and updated in place."
