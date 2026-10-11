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

- `septopert_model.txt`: the exact model (rational vertices).
- `model_vertices.{h,json,lean}`: the model's vertices as `codebdd` writes
  them (the model stage regenerates them); `symmetry_neighbors.h`: the C3
  rotations (the C3 cell prune); `mirror_q.h`: the mirror-tie rotations (the
  mirror prune); `tie_normals.h`: the tie-leaf table the shared code expects
  (the deltoidal hexecontahedron's; the Septopert's search uses no tie
  leaves).
- `codebdd.exe`: codes and code triangles (`codebdd.json`), model vertices.
- `tubecode.exe`, `tuberefine.exe`: identity-tube trees per code.
- `export_codetrees_pack.exe`: tube trees to Lean packs.
- `capcert_septopert.exe` (`capcert_septopert.cc`, the Septopert's own):
  cap certificate at the mirror normal.
- `search5d.exe`: parallel journaled 5D search.
- `pack5d.exe`: 5D journals to per-code Lean packs.
- `scoreboard5d.exe`, `dfwhere.exe`, `tufix.exe`, `capleaf_check.exe`:
  status and diagnostic tools for the 5D journals.
- `*_test.cc` (in `../common/`): unit tests; some need `codebdd.json` in the
  current directory or a tube trees directory.
