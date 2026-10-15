# search/

The C++ certificate searches that produced the data behind each result. None
of this code needs to be trusted: the Lean checkers in `../proof` check
whatever data it writes.

- [`common/`](common/): the code the solids' searches share: the identity
  tube (`tube`, `tubetree`, `tubecode`, `tuberefine`,
  `export-codetrees-pack`), the 5D search and packing (`exact5d`, `geom5d`,
  `contacts5d`, `cert5d`, `rows5d`, `solve5d`, `search5d`, `pack5d`, ...),
  `codebdd` (all but #231's), the diagnostics and renderings, the unit tests,
  and the build rules (`common.mk`).
- [`septopert/`](septopert/): the Septopert's search
  (`septopert/rebuild.sh`).
- [`dh/`](dh/): the deltoidal hexecontahedron's search (`dh/rebuild.sh`).
- [`ph/`](ph/): the pentagonal hexecontahedron's search (`ph/rebuild.sh`).
- [`sd/`](sd/): the snub dodecahedron's search (`sd/rebuild.sh`).
- [`nopert231/`](nopert231/): candidate #231's search
  (`nopert231/rebuild.sh`), with its history.

Each solid's directory has its README, makefile, rebuild script, model
files and Lean data generators, and the solid's own tools (the Septopert's
and the DH's cap certificates, the DH's tie tubes, #231's `codebdd`). The
result's page (in the repository root) says how to run it; the rebuilds
write to `work/`, `work-dh/`, `work-ph/`, `work-sd/` and `work-231/` at the
repository root.

The shared code includes the solid's model headers by name
(`model-vertices.h`, written by `codebdd`; `symmetry-neighbors.h`,
`mirror-q.h`, `ico-group.h`, `tie-normals.h` where the solid has them) and
`solid.h`, the solid's settings: its exact or rounded model, its charts and
whether the fivefold symmetry narrows them, its symmetry tables (the
icosahedral or C3 cell prune, the half-turn or mirror prune, the tie
leaves), and the few choices in which the searches differed (bridge
contacts, outer dyadic triangles). So each solid builds the shared code in
its own directory: `make -C search/<solid>` (`make` builds the unit tests,
`make test` runs them, `make all` builds every tool). A source file in the
solid's directory takes precedence over one of the same name in `common/`
(make's `vpath`); only #231's `codebdd.cc` uses this.

License: GPLv3 (`COPYING`), except the scripts that carry the header "THIS
FILE ONLY: Uses APACHE 2.0 license" (Lean data generators derived from the
Apache-2.0 Noperthedron project; license text: `APACHE20.txt`). The other
scripts, including those that write Lean data (`dh/dh-cap-lean.py`,
`dh/dh-tie-lean.py`, `dh/ico-group.py`, ...), are GPLv3.
