# search/septopert: the Septopert's certificate search

The C++ search that produced the Septopert's certificate data (see
[`../../septopert.md`](../../septopert.md)). The code it shares with the other
solids' searches is in [`../common/`](../common/); this directory has the
Septopert's model, its own tools and its rebuild script.

Main entry: `rebuild.sh` (model, tube, tubepack, cap, search, pack, verify;
the last stage runs the Lean checker in `../../proof`). Its output goes to
`../../work/` (`--work DIR` moves it).

Build with `make` (after `../../get-cc-lib.sh`; see `../../BUILDING.md`):
`make` builds the unit tests, `make test` runs them, `make all` builds every
tool and test.

- `septopert-model.txt`: the exact model (rational vertices).
- `model-vertices.{h,json,lean}`: the model's vertices (the model stage
  regenerates them with `codebdd`, together with the Lean view cover
  `../../proof/Septopert/ViewCoverData.lean`);
  `symmetry-neighbors.h`: the C3 rotations (the C3 cell prune);
  `mirror-q.h`: the mirror-tie rotations (the mirror prune).
- `solid.h`: the Septopert's settings for the shared code (its tables, the
  four undivided charts, exact model, bridge contacts, ...).
- `codebdd.exe`: codes and code triangles (`codebdd.json`), model vertices.
- `tubecode.exe`, `tuberefine.exe`: identity-tube trees per code.
- `export-codetrees-pack.exe`: tube trees to Lean packs.
- `capcert-septopert.exe` (`capcert-septopert.cc`, the Septopert's own):
  cap certificate at the mirror normal.
- `search5d.exe`: parallel journaled 5D search.
- `pack5d.exe`: 5D journals to per-code Lean packs.
- `scoreboard5d.exe`, `dfwhere.exe`, `capleaf-check.exe`:
  status and diagnostic tools for the 5D journals. dfwhere also prints the
  first-order margin at each deferred leaf's view: leaves with m(u) ≈ 0 are
  cap candidates (e.g. without `--caps`, t18 chart 0 defers 530 leaves at the
  mirror normal with m(u) = 3.8e-8).
- `*_test.cc` (in `../common/`): unit tests; some need `codebdd.json` in the
  current directory or a tube trees directory.
