#!/bin/bash
# ONE-SHOT: copy M12 -> M7 (renaming). Do not re-run after editing M7 files.
set -e
cd "$(dirname "$0")/.."
[ -e M7 ] && { echo "M7 exists; refusing"; exit 1; }
mkdir M7
for f in M12/*.lean; do sed 's/M12/M7/g; s/m12/m7/g; s/h12cap/m7cap/g' "$f" > "M7/$(basename $f)"; done
for f in M12.lean constructM12.lean checkM12Arc.lean checkM12Axis.lean; do sed 's/M12/M7/g; s/m12/m7/g; s/h12cap/m7cap/g' "$f" > "${f//M12/M7}"; done
