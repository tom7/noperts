#!/bin/sh
# Checks out cc-lib (part of tom7misc, GPLv3) next to search/, at the svn
# revision the search code was built and tested with.
set -eu
REV=7488
cd "$(dirname "$0")"
if [ -d cc-lib/.svn ]; then
  svn update -q -r "$REV" cc-lib
else
  svn checkout -q -r "$REV" https://svn.code.sf.net/p/tom7misc/svn/trunk/cc-lib cc-lib
fi
echo "cc-lib at r$REV"
