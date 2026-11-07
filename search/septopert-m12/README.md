# search/septopert-m12: the SeptopertM12's certificate search (draft)

The C++ search that produced the SeptopertM12's certificate data (see
[`../../septopert-m12.md`](../../septopert-m12.md)). The code it shares with the other
solids' searches is in [`../common/`](../common/); this directory has the
SeptopertM12's model, its own tools and its rebuild script.

Main entry: `rebuild.sh`. Its stages are model, tube, idcap, tubepack, cap,
arccert, axiscert, pcapcert, search, pack and verify. The three cap stages
regenerate the extra cap certificates from scratch with `capcert-m12.exe`
(`--solid m12`): `arccert` (cap 1, the cube-corner arc and U cap, 146
charts), `axiscert` (cap 2, the axis cap at (1,1,1), 52 charts) and `pcapcert`
(cap 3, the P cap at P = (2,1,0): wedge WP, 26 charts, and U cap, 52 charts,
turned into Lean trees by `../common/leaf2cert.py`). The last stage runs the
Lean checker in `../../proof` on the **regenerated** certificates in the work
directory (`arc.cert`, `axis-cap.cert`, `pcap-wp.cert`, `pcap-u.cert`); the
copies committed in `../../proof/SeptopertM12/data/` are reference copies (the search is
multithreaded and need not reproduce them byte for byte). The separate
checkers `checkSeptopertM12*` / `checkSeptopert{Arc,Axis,PCap}` take any one
certificate file. Its output goes to
`../../work/` (`--work DIR` moves it).

Build with `make` (after `../../get-cc-lib.sh`; see `../../BUILDING.md`):
`make` builds the unit tests, `make test` runs them, `make all` builds every
tool and test.

- `septopert-m12-model.txt`: the exact model (rational vertices).
- `model-vertices.{h,json,lean}`: the model's vertices (the model stage
  regenerates them with `codebdd`, together with the Lean view cover
  `../../proof/SeptopertM12/ViewCoverData.lean`);
  `symmetry-neighbors.h`: the C3 rotations (the C3 cell prune);
  `mirror-q.h`: the mirror-tie rotations (the mirror prune).
- `solid.h`: the SeptopertM12's settings for the shared code (its tables, the
  four undivided charts, exact model, bridge contacts, ...).
- `codebdd.exe`: codes and code triangles (`codebdd.json`), model vertices.
- `tubecode.exe`, `tuberefine.exe`: identity-tube trees per code.
- `export-codetrees-pack.exe`: tube trees to Lean packs.
- `capcert-septopert-m12.exe` (`capcert-septopert-m12.cc`, the SeptopertM12's own):
  cap certificate at the mirror normal.
- `capcert-m12.exe` (`capcert-m12.cc`, multi-solid: `--solid m7|m12`): the arc,
  axis and P cap certificates (stages arccert, axiscert, pcapcert).
- `capcert-neo.exe` (`capcert-neo.cc`): the earlier arc cap tool (M18 constants).
- `arc-cap.txt`: the views near (2, 2, -1)/3 and the arc towards the mirror normal: the views and rotations the arc cap claims (`tubecode` and
  `search5d --piece_caps`; Lean: `SeptopertM12.arcLeafOk`).
- `search5d.exe`: parallel journaled 5D search.
- `pack5d.exe`: 5D journals to per-code Lean packs.
- `scoreboard5d.exe`, `dfwhere.exe`, `capleaf-check.exe`:
  status and diagnostic tools for the 5D journals.
- `*_test.cc` (in `../common/`): unit tests; some need `codebdd.json` in the
  current directory or a tube trees directory.
