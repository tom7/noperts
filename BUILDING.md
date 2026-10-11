# Building

How the repository is laid out and how to build it. Each result has its own
page with its statement, trust model and reproduction steps:

- [septopert.md](septopert.md): the Septopert, a 7-vertex nopert (a Lean
  verification backed by certificate data);
- [deltoidal-hexecontahedron.md](deltoidal-hexecontahedron.md): the deltoidal
  hexecontahedron is a nopert (a Lean verification backed by certificate
  data);
- [pentagonal-hexecontahedron.md](pentagonal-hexecontahedron.md): the
  pentagonal hexecontahedron, in both chiralities, is a nopert (a Lean
  verification backed by certificate data);
- [snub-dodecahedron.md](snub-dodecahedron.md): the snub dodecahedron, of
  either chirality, is a nopert (a Lean verification backed by certificate
  data);
- [nopert231.md](nopert231.md): candidate #231, a 20-vertex nopert with
  fivefold symmetry (a Lean verification backed by certificate data);
- [minimality.md](minimality.md): every nopert has at least 7 vertices (a
  Lean proof).

## Layout

- `proof/`: one Lean 4 + Mathlib project (`lakefile.toml`). Libraries:
  - `Noperts` (the modules directly in `proof/` and its subdirectories other
    than the six below): shared definitions and machinery. `IsRupert` is
    defined in `proof/MainTheorem.lean`. `Pipeline/` defines the certificate
    tables and their checks, used by the data-backed results other than
    candidate #231. It is generic over the solid: a solid is a `SolidModel`
    (`Pipeline/SolidModel.lean`: its rational vertices, cyclic symmetry and
    error bounds); the icosahedral solids are `IcosahedralSolid`s
    (`Pipeline/IcoModel.lean`, via `Pipeline/FivefoldModel.lean`); and each
    solid provides these as scoped instances, in effect only inside its own
    namespace. The pentagonal hexecontahedron and the snub dodecahedron also
    share the top layer (`Pipeline/AtlasProjectiveSolutionTree.lean`, the
    decoder `PackedSolutionTree`, `IsNotRupert`, the executable checker
    `NativeExecutable`) and Wikipedia's snub dodecahedron
    (`Pipeline/WikipediaSnub.lean`).
  - `Septopert`: entry point `proof/Septopert.lean`, details in
    `proof/Septopert/` (its model, `SolidModel.lean`; its own solution tree,
    with C3 and mirror reductions and caps).
  - `Minimality`: entry point `proof/Minimality.lean`, details in
    `proof/Minimality/`.
  - `DeltoidalHexecontahedron`: entry point
    `proof/DeltoidalHexecontahedron.lean`, details in
    `proof/DeltoidalHexecontahedron/` (its model and orbit data,
    `SolidModel.lean` and `OrbitData.lean`; its statement; and its own
    solution tree, with the half-turn reduction, caps and ties).
  - `PentagonalHexecontahedron`: entry point
    `proof/PentagonalHexecontahedron.lean`, details in
    `proof/PentagonalHexecontahedron/` (its model, orbit and view-cover data
    and its statement).
  - `SnubDodecahedron`: entry point `proof/SnubDodecahedron.lean`, details
    in `proof/SnubDodecahedron/` (likewise, plus its tangent-cone tables,
    with which its executable checks the identity-tube rows more cheaply).
  - `Nopert231`: entry point `proof/Nopert231.lean`, details in
    `proof/Nopert231/` (its own pipeline, which uses the core's `Atlas/`).
  - `Tests`: checks that run at build time: every headline uses only the
    standard axioms, no solid's model is in scope without opening its
    namespace, and the chart-3 table is valid for each solid that uses it.
  - Executables: `constructSeptopert` (checks the Septopert's certificate
    data), `checkSeptopertCap` (checks only its cap certificate),
    `constructDeltoidalHexecontahedron` (checks the deltoidal
    hexecontahedron's certificate data), `constructPentagonalHexecontahedron`
    (checks the pentagonal hexecontahedron's) and `constructSnubDodecahedron`
    (checks the snub dodecahedron's) and `constructNopert231` (checks
    candidate #231's).

  License: Apache-2.0 (`proof/LICENSE`). Derived from the
  [Noperthedron](https://github.com/jcreedcmu/Noperthedron) formalization,
  whose history it keeps.
- `search/`: the C++ certificate searches that produced the data.
  - `search/common/`: the code the searches share (the identity tube, the
    5D search and packing, `codebdd`, diagnostics, unit tests) and their
    build rules, `common.mk`.
  - `search/septopert/`, `search/dh/`, `search/ph/`, `search/sd/`,
    `search/nopert231/`: the searches for the Septopert, the deltoidal
    hexecontahedron, the pentagonal hexecontahedron, the snub dodecahedron
    and candidate #231, each with its `rebuild.sh` (see the result's page),
    model files, Lean data generators, own tools, and `solid.h` (the
    solid's settings for the shared code). The searches of the DH, PH and
    SD were imported from the corresponding branches of the author's search
    repository and #231's with its history; until 2026-10-10 each solid's
    directory had its own copy of the shared code (see
    [search/README.md](search/README.md)).
  - Each writes its output to a `work*/` directory at the repository root
    (`work/`, `work-dh/`, `work-ph/`, `work-sd/`, `work-231/`), ignored by
    git.

  License: GPLv3 (`search/COPYING`). Exception: the Python scripts that
  generate Lean data files (`search/dh/scripts/`, `search/ph/scripts/`,
  `search/sd/lean_scripts/`, `search/nopert231/scripts/`) derive from the
  Apache-2.0 Noperthedron project and say so in a header ("THIS FILE ONLY:
  Uses APACHE 2.0 license"); the license text is `search/APACHE20.txt`.
- `cc-lib/`: not in the repository. `./get-cc-lib.sh` checks out svn
  revision 7488 of tom7misc's `trunk/cc-lib`; the build expects it next to
  `search/`. It is GPLv3, with some files under other compatible licenses
  noted in their headers.
- `work/` (and `work-dh/`, `work-ph/`, `work-sd/`, `work-231/`): created by the
  rebuilds and ignored by git; they hold all generated data.

`proof/` and `search/` are separate programs that only exchange data files.

## Requirements

- Linux
- elan (the toolchain is pinned in `proof/lean-toolchain`, v4.32.0)
- for `search/`: clang, GMP, svn, python3 (python3 regenerates Lean data
  files: the Septopert's view cover in `proof/scripts/`, and the model
  stages of `search/dh/`, `search/ph/`, `search/sd/` and
  `search/nopert231/`)
- optionally `systemd-run --user`, which the rebuild scripts use to cap
  each stage's memory (and, for the Septopert, report its peak). Without a
  systemd user session (e.g. in a container), they run uncapped.
- network access for `./get-cc-lib.sh` (svn) and `lake exe cache get`.
  Offline, copy in a checkout of cc-lib at the revision in
  `get-cc-lib.sh` and an existing `proof/.lake/packages` (with its build
  cache) instead.

## Building the Lean project

```sh
cd proof
lake exe cache get      # Mathlib build cache
lake build              # all libraries and executables
```

To see what a theorem depends on, check its axioms, e.g. in a scratch file:

```lean
import Minimality
#print axioms seven_le_card_of_isNopert
```

Every theorem in the repository should list only `propext`,
`Classical.choice` and `Quot.sound`.

## Building the search

```sh
./get-cc-lib.sh
make -C search/septopert -j 16 all    # likewise search/dh, search/ph, ...
```

Each solid's directory builds its own copy of the shared code (which
includes the solid's model headers), so `make` runs in the solid's
directory; `make` builds the unit tests, `make test` runs them and `make
all` builds every tool. The tests that need `codebdd.json` (written by the
solid's model stage, `rebuild.sh --only model`) or tube trees print SKIPPED
without them; `exact5d_test` compares with a Lean executable
(`exact5d_golden`) that is not in this repository, and skips unless
`EXACT5D_GOLDEN` points at one.

The rebuild scripts append each stage's wall time to `WORK/stages.log` and
build the Lean checker in the background while the C++ stages run (log
`WORK/lean_build.log`), waiting for it before the verify stage.

## Former names

Until 2026-10-09 the code called the Septopert `Nopert7` (`constructNopert7`,
`checkNopert7Cap`, `Noperthedron/Nopert7/`, `nopert7_rebuild.sh`,
`capcert7`), K in comments, and `nopert_233` in the search database (model
`nopert233_model.txt`, coordinates `7v-cocta-c3v-2.xyz`); the shared Lean
library was namespaced `Noperthedron` (and its certificate pipeline
`Noperthedron.PentagonalHexecontahedron`), and the minimality library was
called `SmallRupert`. Archived data and logs (e.g.
`/mnt/nopertdata/archive/septopert/README.txt` on the 64-core VM), the
working notes and older branches (`nopert7` in Noperthedron at d7f04505 and
in nopert229 at 5a52be2) use those names.

The deltoidal hexecontahedron's Lean proof (`proof/DeltoidalHexecontahedron/`)
comes from the `deltoidalhexecontahedron` branch of Noperthedron (b45e0b34),
where it lived in `Noperthedron/PentagonalHexecontahedron/`: that directory
was the shared icosahedral pipeline, edited in place for each solid (snub
dodecahedron, then pentagonal hexecontahedron, then the DH), and was the
ancestor of `Pipeline/`. There the modules `Statement`, `StatementData`,
`Caps`, `CapData`, `Ties`, `TieData`, `Checks` and `Decode` had a `DH` prefix
(`DHStatement`, ...). The search that produced its data is on nopert229's
`deltoidalhexecontahedron` branch.

The pentagonal hexecontahedron's Lean proof (`proof/PentagonalHexecontahedron/`)
comes from the `pentagonalhexecontahedron` branch of Noperthedron (da2965b3),
where it lived in the same-named `Noperthedron/PentagonalHexecontahedron/`
(namespace `Noperthedron.PentagonalHexecontahedron`), before the DH reused
that directory. Its `IcoField` is now `Pipeline/IcoField`. Eight declarations
that the branch put at the root (`proj_xy_smul`, `proj_xy_add`,
`isRupert_image_{smul,add,rotation,similarity}`, `MatrixPose.bothRightIco`,
`MatrixPose.rightIcoSymmetry`) are in the `Noperts.Pipeline` namespace
here. The search that produced its data is on nopert229's
`pentagonalhexecontahedron` branch.

The snub dodecahedron's Lean proof (`proof/SnubDodecahedron/`) comes from
the `snubdodecahedron` branch of Noperthedron (bc31c747), where it lived in
`Noperthedron/SnubDodecahedron/` (namespace `Noperthedron.SnubDodecahedron`);
that branch is the first instantiation of the shared icosahedral pipeline.
Earlier commits of that branch called it `Nopert231`
(`Noperthedron/Nopert231/`, `constructNopert231`). Its `IcoField` is now
`Pipeline/IcoField`, and the same eight root declarations as the pentagonal
hexecontahedron's are in the `Noperts.Pipeline` namespace here. The search
that produced its data is on nopert229's `snubdodecahedron` branch.

Until 2026-10-10 the deltoidal and pentagonal hexecontahedra and the snub
dodecahedron each had their own copy of the certificate pipeline in their
directory (the branch's `PentagonalHexecontahedron/` or `SnubDodecahedron/`
directory, renamed), and `Pipeline/` was the Septopert's. They were merged
into `Pipeline/`, made generic over the solid (`SolidModel`,
`IcosahedralSolid`): each solid's `Vertices.lean` became its `SolidModel.lean`,
the per-solid part of its `IcoGroupData.lean` its `OrbitData.lean`, and the
rest of its copy was deleted. `C5Model` is now `CyclicModel`, the generic
`fivefoldMatrix` is `symmetryMatrix` and the generic
`InFivefoldFundamentalDomain` is `InSymmetryFundamentalDomain`. The
pentagonal hexecontahedron's `WikipediaSnub.lean` (a copy of the first half
of the snub dodecahedron's statement) is now `Pipeline/WikipediaSnub.lean`.
The generators of the solids' Lean data in `search/` were adapted to the new
layout on 2026-10-10: run from the committed model inputs they reproduce the
committed data files byte for byte (`SolidModel` and `RationalVertices` are
updated in place; `Pipeline/IcoGroupData.lean` is written identically by each
solid's `snub_ico_group.py`).

Candidate #231's Lean proof (`proof/Nopert231/`) comes, with its history,
from the `nopert231` branch of Noperthedron (0c83e4ba), where it lived in
`Noperthedron/Nopert231/` (namespace `Noperthedron.Nopert231`). That
pipeline started as candidate #76 and was renamed to #229 and then #231 in
place, so older commits call it `Nopert76` or `Nopert229`. Its search
(`search/nopert231/`), also with its history, comes from nopert229's
`nopert231` branch (e53dfda). This is a different `Nopert231` from the one
in the snub dodecahedron's branch history above.
