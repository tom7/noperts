# search/septopert-m18: the SeptopertM18's certificate search

The C++ search that produced the SeptopertM18's certificate data (see
[`../../septopert-m18.md`](../../septopert-m18.md)). The code it shares with the other
solids' searches is in [`../common/`](../common/); this directory has the
SeptopertM18's model, its own tools and its rebuild script.

Main entry: `rebuild.sh` (model, tube, tubepack, cap, search, pack, verify;
the last stage runs the Lean checker in `../../proof`). Its output goes to
`../../work/` (`--work DIR` moves it).

Build with `make` (after `../../get-cc-lib.sh`; see `../../BUILDING.md`):
`make` builds the unit tests, `make test` runs them, `make all` builds every
tool and test.

- `septopert-m18-model.txt`: the exact model (rational vertices).
- `model-vertices.{h,json,lean}`: the model's vertices (the model stage
  regenerates them with `codebdd`, together with the Lean view cover
  `../../proof/SeptopertM18/ViewCoverData.lean`);
  `symmetry-neighbors.h`: the C3 rotations (the C3 cell prune);
  `mirror-q.h`: the mirror-tie rotations (the mirror prune).
- `solid.h`: the SeptopertM18's settings for the shared code (its tables, the
  four undivided charts, exact model, bridge contacts, ...).
- `codebdd.exe`: codes and code triangles (`codebdd.json`), model vertices.
- `tubecode.exe`, `tuberefine.exe`: identity-tube trees per code.
- `export-codetrees-pack.exe`: tube trees to Lean packs.
- `capcert-septopert-m18.exe` (`capcert-septopert-m18.cc`, the SeptopertM18's own):
  cap certificate at the mirror normal.
- `capcert-neo.exe` (`capcert-neo.cc`): the arc cap certificate, near the view
  (2, 2, -1)/3 and the arc from it towards the mirror normal.
  `arc-cap.txt`: the views and rotations the arc cap claims (`tubecode` and
  `search5d --piece_caps`; Lean: `SeptopertM18.arcLeafOk`).
- `search5d.exe`: parallel journaled 5D search.
- `pack5d.exe`: 5D journals to per-code Lean packs.
- `scoreboard5d.exe`, `dfwhere.exe`, `capleaf-check.exe`:
  status and diagnostic tools for the 5D journals.
- `*_test.cc` (in `../common/`): unit tests; some need `codebdd.json` in the
  current directory or a tube trees directory.
