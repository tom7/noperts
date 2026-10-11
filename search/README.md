# search/

The C++ certificate searches that produced the data behind each result. None
of this code needs to be trusted: the Lean checkers in `../proof` check
whatever data it writes.

- This directory: the Septopert's search (below).
- [`dh/`](dh/): the deltoidal hexecontahedron's search (`dh/rebuild.sh`).
- [`ph/`](ph/): the pentagonal hexecontahedron's search (`ph/rebuild.sh`).
- [`sd/`](sd/): the snub dodecahedron's search (`sd/rebuild.sh`).
- [`nopert231/`](nopert231/): candidate #231's search
  (`nopert231/rebuild.sh`), with its history.

Each subdirectory has its own README, makefile and rebuild script, and the
result's page (in the repository root) says how to run it. The
subdirectories are copies of the code that produced each result's data, and
share much of their code with this directory and with each other.

License: GPLv3 (`COPYING`), except the Python scripts that generate Lean data
files, which derive from the Apache-2.0 Noperthedron project and say so in
their header (license text: `APACHE20.txt`).

## The Septopert's search

Main entry: `septopert_rebuild.sh` (model, tube, tubepack, cap, search, pack, verify; the last stage runs the Lean checker in `../proof`).

Build with `make` (after `../get-cc-lib.sh`; see `../BUILDING.md`). `make all` builds every tool and test.

- `septopert_model.txt`: the exact model (rational vertices).
- `codebdd.exe`: codes and code triangles (`codebdd.json`), model vertices.
- `tubecode.exe`, `tuberefine.exe`: identity-tube trees per code.
- `export_codetrees_pack.exe`: tube trees to Lean packs.
- `capcert_septopert.exe`: cap certificate at the mirror normal.
- `search5d.exe`: parallel journaled 5D search.
- `pack5d.exe`: 5D journals to per-code Lean packs.
- `scoreboard5d.exe`, `dfwhere.exe`, `tufix.exe`, `capleaf_check.exe`: status and diagnostic tools for the 5D journals.
- `*_test.cc`: unit tests (`make`); some need `codebdd.json` in the current directory or a tube trees directory.
