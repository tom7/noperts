# Building

How the repository is laid out and how to build it. Each result has its own
page with its statement, trust model and reproduction steps:

- [septopert.md](septopert.md): the Septopert, a 7-vertex nopert (a Lean
  verification backed by certificate data);
- [deltoidal-hexecontahedron.md](deltoidal-hexecontahedron.md): the deltoidal
  hexecontahedron is a nopert (a Lean verification backed by certificate
  data);
- [snub-dodecahedron.md](snub-dodecahedron.md): the snub dodecahedron, of
  either chirality, is a nopert (a Lean verification backed by certificate
  data);
- [minimality.md](minimality.md): every nopert has at least 7 vertices (a
  Lean proof).

## Layout

- `proof/`: one Lean 4 + Mathlib project (`lakefile.toml`). Libraries:
  - `Noperts` (the modules directly in `proof/` and its subdirectories other
    than the four below): shared definitions and machinery. `IsRupert` is
    defined in `proof/MainTheorem.lean`. `Pipeline/` defines the certificate
    tables and their checks, used by data-backed results.
  - `Septopert`: entry point `proof/Septopert.lean`, details in
    `proof/Septopert/`.
  - `Minimality`: entry point `proof/Minimality.lean`, details in
    `proof/Minimality/`.
  - `DeltoidalHexecontahedron`: entry point
    `proof/DeltoidalHexecontahedron.lean`, details in
    `proof/DeltoidalHexecontahedron/` (its own copy of the certificate
    pipeline; it shares the core and the model-independent parts of
    `Pipeline/`).
  - `SnubDodecahedron`: entry point `proof/SnubDodecahedron.lean`, details
    in `proof/SnubDodecahedron/` (likewise its own copy of the certificate
    pipeline, sharing the core, `Pipeline.IcoField` and
    `Pipeline.HalfTurnBasic`).
  - Executables: `constructSeptopert` (checks the Septopert's certificate
    data), `checkSeptopertCap` (checks only its cap certificate) and
    `constructDeltoidalHexecontahedron` (checks the deltoidal
    hexecontahedron's certificate data) and `constructSnubDodecahedron`
    (checks the snub dodecahedron's).

  License: Apache-2.0 (`proof/LICENSE`). Derived from the
  [Noperthedron](https://github.com/jcreedcmu/Noperthedron) formalization,
  whose history it keeps.
- `search/`: the C++ certificate search for data-backed results (currently
  the Septopert; the deltoidal hexecontahedron's and the snub dodecahedron's
  are still on the `deltoidalhexecontahedron` and `snubdodecahedron`
  branches of nopert229). License: GPLv3
  (`search/COPYING`).
- `cc-lib/`: not in the repository. `./get-cc-lib.sh` checks out svn
  revision 7488 of tom7misc's `trunk/cc-lib`; the build expects it next to
  `search/`. It is GPLv3, with some files under other compatible licenses
  noted in their headers.
- `work/`: created by the Septopert's rebuild and ignored by git; holds all
  generated data.

`proof/` and `search/` are separate programs that only exchange data files.

## Requirements

- Linux
- elan (the toolchain is pinned in `proof/lean-toolchain`, v4.32.0)
- for `search/`: clang, GMP, svn, python3 (only to regenerate the Septopert view-cover data in `proof/scripts`)
- `systemd-run --user`, which the Septopert's rebuild uses to cap each
  stage's memory

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
make -C search -j 16
```

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

The snub dodecahedron's Lean proof (`proof/SnubDodecahedron/`) comes from
the `snubdodecahedron` branch of Noperthedron (bc31c747), where it lived in
`Noperthedron/SnubDodecahedron/` (namespace `Noperthedron.SnubDodecahedron`);
that branch is the first instantiation of the shared icosahedral pipeline.
Earlier commits of that branch called it `Nopert231`
(`Noperthedron/Nopert231/`, `constructNopert231`). The search that produced
its data is on nopert229's `snubdodecahedron` branch.
