# search/

The C++ certificate searches that produced the data behind each result. None
of this code needs to be trusted: the Lean checkers in `../proof` check
whatever data it writes.

- [`common/`](common/): the code shared by the solids' searches (the
  identity tube, the 5D search and packing, and their tools and tests) and
  the shared build rules (`common/common.mk`).
- [`septopert/`](septopert/): the Septopert's search
  (`septopert/rebuild.sh`).
- [`dh/`](dh/): the deltoidal hexecontahedron's search (`dh/rebuild.sh`).
- [`ph/`](ph/): the pentagonal hexecontahedron's search (`ph/rebuild.sh`).
- [`sd/`](sd/): the snub dodecahedron's search (`sd/rebuild.sh`).
- [`nopert231/`](nopert231/): candidate #231's search
  (`nopert231/rebuild.sh`), with its history.

Each solid's directory has its own README, makefile and rebuild script, and
the result's page (in the repository root) says how to run it. The
Septopert's directory holds only its model files and its own tools and
builds the shared code from `common/`; the other directories are still
copies of the code that produced each result's data, and share much of it
with `common/` and with each other.

License: GPLv3 (`COPYING`), except the Python scripts that generate Lean data
files, which derive from the Apache-2.0 Noperthedron project and say so in
their header (license text: `APACHE20.txt`).
