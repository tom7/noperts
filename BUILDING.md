# Building and verifying

Reference notes on building, rebuilding and verifying the proof.

The proof currently covers one solid, which the code calls `Nopert7`. It is
also called K, and `nopert_233` in the search database.

## Layout

- `proof/`: Lean 4 + Mathlib. It holds the definitions, the soundness
  theorems, the certificate checkers and the native driver
  `constructNopert7`. Imported with full history from Noperthedron, branch
  `nopert7` (commit d7f04505). License: Apache-2.0 (`proof/LICENSE`).
- `search/`: the C++ certificate search. Imported from nopert229, branch
  `nopert7` (commit 5a52be2), with history filtered to these files. License:
  GPLv3 (`search/COPYING`).
- `cc-lib/`: not in the repository. `./get-cc-lib.sh` checks out svn
  revision 7488 of tom7misc's `trunk/cc-lib`; the build expects it next to
  `search/`. It is GPLv3, with some files under other compatible licenses
  noted in their headers. `geom/hull-2d.cc` says "see LICENSES" for Miguel
  Vieira's MIT notice, but in svn that file is in `ruperts/LICENSES`, not
  `cc-lib/`.
- `work/`: created by the rebuild and ignored by git. It holds all
  generated data.

`proof/` and `search/` are separate programs. They only exchange data files
(tube packs, chart packs and the cap certificate).

## Requirements

- Linux
- elan (the toolchain is pinned in `proof/lean-toolchain`, v4.32.0)
- clang
- GMP
- python3
- svn
- `systemd-run --user`, which the rebuild uses to cap each stage's memory

## Rebuilding from scratch

```sh
./get-cc-lib.sh
(cd proof && lake exe cache get)      # Mathlib build cache
search/nopert7_rebuild.sh --from model --threads 64 --mem_gb 100
```

Stages, in order: `model`, `tube`, `tubepack`, `cap`, `search`, `pack`,
`verify`.

- `--from STAGE` restarts at a stage; `--only STAGE` runs just one.
- `--work DIR` puts the output somewhere other than `work/`.
- Every stage can be restarted: `tubecode` and `search5d` journal their work,
  and `pack5d` skips packs that are newer than their journals.
- `search5d` is not deterministic (its work order varies), so a rebuild
  produces different but equally checkable tables. The other stages are
  deterministic.

Each stage appends its wall time and peak memory to `work/stages.log`.

Measured times. The 64-core column is a from-scratch run in a fresh clone
(2ab73f4, 2026-10-09), 4 h 22 min in total:

| Stage | 16-core VM, 12 threads | 64-core VM, 64 threads |
|---|---|---|
| model | | 7 s |
| tube + tubepack | 11 min | 3.6 min |
| cap | 2 min | 33 s |
| search | about 2 h of compute | 28 min (one round) |
| pack | 2 h 20 min | 49 min |
| verify | 8 h 22 min, 15.7 GB peak | 3 h 1 min, including the Lean build; 15.2 GB peak |

Table sizes from both runs: chart 0 has 83,340,081 rows; charts 1–3 have
144,165, 124,872 and 104,577; tube tables total 1.39M rows.

## Verifying existing certificates

```sh
(cd proof && lake build constructNopert7)
cd work && LEAN_NUM_THREADS=64 ../proof/.lake/build/bin/constructNopert7 \
  tube_packs/manifest.txt packs cap-1_16.cert
```

The verifier checks, in order:

1. the cap certificate;
2. the 22 tube tables;
3. the four chart tables, one at a time. Chart 0 is about 83M rows.

On success it prints:

    instantiated: ¬ IsRupert Nopert7.verts (the 7-vertex solid is not Rupert)

## What is proved and what is trusted

`proof/Noperthedron/Nopert7/IsNotRupert.lean`:

```lean
theorem not_rupert_of_valid_tables (table : CayleyAtlas.ChartIndex → SolutionTree.Table)
    (hchart : ∀ chart, (table chart).chart = chart)
    (hvalid : ∀ chart, (table chart).Valid) (hcap : CapOk) :
    ¬ IsRupert verts
```

- `verts` is the set of the seven rational points `vertexQ` in
  `Nopert7/ModelData.lean`.
- `IsRupert` is defined in `proof/Noperthedron/MainTheorem.lean`.
- `#print axioms` on the theorem lists only `propext`, `Classical.choice`
  and `Quot.sound`.
- `Table.Valid` includes the coverage condition: row 0 is the root interval
  over the code triangles.

`constructNopert7` turns validity of the actual data into a value of type
`¬ IsRupert verts` at run time. If all checks return true, it applies the
theorem to the tables it checked. Trusted components:

- the Lean kernel, for the theorems;
- the Lean compiler and runtime, for evaluating the check functions. This is
  the same trust as `native_decide`, although neither `native_decide` nor
  `Lean.ofReduceBool` appears anywhere.

`search/` is untrusted. It only proposes certificates.

## Generated data

The certificate data (tube packs, chart packs, cap certificate) is machine
output, intended to be CC0. From the run that this import was verified on
(SHA-256 of all 112 files recorded separately):

- `cap-1_16.cert`: 540 KB
- `tube_packs/`: 382 MB, 22 tables
- `packs/`: 6.3 GB, 88 code packs. `packs/c0/t3.pack` alone is 5.2 GB,
  above GitHub's 2 GB release-asset limit.
