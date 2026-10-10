# search/

The C++ certificate search for the Septopert. Main entry: `septopert_rebuild.sh` (model, tube, tubepack, cap, search, pack, verify; the last stage runs the Lean checker in `../proof`).

Build with `make` (after `../get-cc-lib.sh`; see `../BUILDING.md`). `make all` builds every tool and test.

- `c3v_model.py`: exact model from `septopert.xyz` to `septopert_model.txt`.
- `codebdd.exe`: codes and code triangles (`codebdd.json`), model vertices; `--texture` code texture (`blender_code_texture.py`).
- `tubecode.exe`, `tuberefine.exe`: identity-tube trees per code.
- `export_codetrees_pack.exe`: tube trees to Lean packs.
- `capcert_septopert.exe`: cap certificate at the mirror normal.
- `search5d.exe`: parallel journaled 5D search.
- `pack5d.exe`: 5D journals to per-code Lean packs.
- `scoreboard5d.exe`, `dfwhere.exe`, `tufix.exe`, `capleaf_check.exe`: status and diagnostic tools for the 5D journals.
- `turntable.exe`, `turntable_gif.py`: render the solid spinning.
- `*_test.cc`: unit tests (`make`); some need `codebdd.json` in the current directory or a tube trees directory.
