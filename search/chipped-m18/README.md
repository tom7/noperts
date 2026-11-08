# search/chipped-m18: the Chipped M18's certificate search

The C++ search that produced the Chipped M18's certificate data (see
[`../../chipped-m18.md`](../../chipped-m18.md)). The code it shares with the other
solids' searches is in [`../common/`](../common/); this directory has the
Chipped M18's model, its own tools and its rebuild script.

The solid is the SeptopertM18 with its C3v vertex orbit (-36,18,18)/64 cut off by
the plane with normal (-1,k,k) and depth 7/64, and the plane's C3 images, with
k = 5 (the working name was "ChipM18K5"): 19 vertices, 13 faces, C3v.

Main entry: `rebuild.sh` (model, tube, idcap, tubepack, cap, arccert, search,
pack, verify; the last stage runs the Lean checker `constructChippedM18` in
`../../proof`). Its output goes to `../../work-chipped-m18/` (`WORK=DIR` moves it,
`TH=N` sets the threads).

Build with `make` (after `../../get-cc-lib.sh`; see `../../BUILDING.md`).

- `chipped-m18-model.txt`: the exact model (rational vertices).
- `model-vertices.{h,json,lean}`: the model's vertices (the model stage
  regenerates them with `codebdd`); `symmetry-neighbors.h`: the C3 rotations;
  `mirror-q.h`: the mirror-tie rotations.
- `solid.h`: the Chipped M18's settings for the shared code.
- `capcert-septopert-m18.exe`: cap certificate at the mirror normal
  (any vertex count).
- `capcert-arc.exe`: the arc cap certificate (any vertex count), run piece by piece by
  `runarc.sh`. `arc-cap.txt`: the views the arc cap claims (`tubecode` and
  `search5d --piece_caps`).
- `runtube.sh`, `runarc.sh`, `runsearch.sh`: the tube, arc and 5D search stages of `rebuild.sh`.
- `lean/emit_modeldata.py`: generates `proof/ChippedM18/ModelData.lean` from the model.
