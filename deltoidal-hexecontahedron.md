# The deltoidal hexecontahedron

The deltoidal hexecontahedron (DH) is the Catalan solid with 60 kite-shaped
faces and 62 vertices, the dual of the rhombicosidodecahedron. It is not
Rupert. This page gives the exact statement, what Lean checked and how, and
how to verify the result.

Lean entry point:
[`proof/DeltoidalHexecontahedron.lean`](proof/DeltoidalHexecontahedron.lean).

## The solid

The statement is about the exact solid, with irrational coordinates. David
McCooey's vertices are the cyclic permutations, with all sign changes, of

```
(0, 0, √5)   (0, C1, C7)   (C3, 0, C6)   (C0, C2, C5)   (C4, C4, C4)
```

where

| | | | |
|---|---|---|---|
| C0 = (5 − √5)/4 | C1 = (15 + √5)/22 | C2 = √5/2 | C3 = (5 + √5)/6 |
| C4 = (5 + 4√5)/11 | C5 = (5 + √5)/4 | C6 = (5 + 3√5)/6 | C7 = (25 + 9√5)/22 |

- These are 62 points (`DH.deltoidalHexecontahedron` in
  `proof/DeltoidalHexecontahedron/Statement.lean`; `mcCooey` in the entry
  point is the same set as a `Finset`): 12 on the 5-fold axes, 30 on the
  2-fold axes and 20 on the 3-fold axes.
- Symmetry Ih (the full icosahedral group, of order 120), so the solid is
  centrally symmetric.

## The statement

In [`proof/DeltoidalHexecontahedron.lean`](proof/DeltoidalHexecontahedron.lean):

```lean
theorem isNopert_of_certificatesValid (h : CertificatesValid) :
    ∀ V : Finset ℝ³, DH.IsDeltoidalHexecontahedron V → IsNopert V
```

`DH.IsDeltoidalHexecontahedron V` says that `V` is the image of McCooey's
points under a similarity: an orthogonal map (possibly a reflection), a
positive scaling and a translation. So the theorem covers the exact solid in
any position, size and orientation, and nothing else. The corollary
`isNopert_mcCooey_of_certificatesValid` states it for McCooey's coordinates
themselves.

`IsNopert V` (in `proof/Nopert.lean`) says that the points of `V` are not all
in one plane, so their convex hull is a genuine solid, and that this solid is
not Rupert. `IsRupert` (in `proof/MainTheorem.lean`) is the Rupert property:
two copies of the solid, each rotated, can be placed so that the shadow of
one lies strictly inside the shadow of the other. `CertificatesValid` says
that the certificate data (four solution tables, three cap certificates and
the tie certificates) passes Lean's validity checks, and that the code
triangles cover the view domain.

## Why the exact solid

The DH is only just not Rupert. It has poses with clearance exactly 0
(*ties*), and moving its twelve 5-fold vertices outward by any amount
η > 0 gives a Rupert solid: next to a tie there is a passage with clearance
about 0.0695·η. `search/dh/dh-boundary.py` checks this numerically, with
60 digits, for η from 10⁻³ down to 10⁻¹⁸; it is not part of the Lean result.
So every neighbourhood of the DH, however small, contains Rupert solids.
Unlike for the Septopert, there is no true statement about all solids near a
rational model, and the proof uses the exact solid near the ties (the
techniques are described in [How the Nopert proofs work](nopert-proof.md)):

- The solution tables exclude every centrally symmetric solid with
  icosahedral symmetry whose vertices are within 6·10⁻¹⁶ of a rational model,
  provided exact claims hold for it near the ties (`ExactClaims`).
- For the exact DH, Lean's kernel decides by exact arithmetic in
  K = ℚ(√5, sin 72°) that it is such a solid (frame, 70 vertex slots, orbits,
  central symmetry, closeness to the rational model), and the cap and tie
  certificates, checked exactly over K, prove the exact claims.
- Near the 2-fold view and the view where the ties meet the identity, [*caps*](nopert-proof.md#caps)
  (blow-up charts with exact Bernstein bounds) cover the remaining rotations.
  Along each pinning tie, [*tie tubes*](nopert-proof.md#ties-and-tie-tubes) prove that no rotation close to the
  tie is a passage. The mirror ties are handled by a [*half-turn reduction*](nopert-proof.md#poses-and-symmetry-reductions),
  which uses the central symmetry: the relative rotation R may be replaced
  by H_u R g (H_u the half-turn about the view u, g a rotation of the
  solid).

## What is proved and what is verified

This is a **Lean verification**, not a plain Lean proof:

1. **Lean proof.** `isNopert_of_certificatesValid` is checked by Lean's
   kernel and depends only on the standard axioms (`propext`,
   `Classical.choice`, `Quot.sound`). Its "genuine solid" half needs no data
   at all. The facts about the exact solid are decided by the kernel.
2. **Verification of the data.** The data is about 20 GB (chart 0's table
   alone has tens of millions of rows), too much for the kernel. The program
   `constructDeltoidalHexecontahedron` runs the same Lean validity checks as
   compiled code on every row and certificate, and only if all pass does it
   construct `CertificatesValid`, and from it (via part 1)
   `∀ V, DH.IsDeltoidalHexecontahedron V → IsNopert V`. It then prints
   `instantiated: IsNopert V for every deltoidal hexecontahedron V (none is Rupert)`.
   This step trusts Lean's compiler and runtime to evaluate the checks
   correctly. That is the same trust as `native_decide`, though
   `native_decide` is not used.

The C++ search that produced the data does not need to be trusted: a mistake
there can only produce data that fails the checks.

## Status

- **2026-10-06:** verified on the `deltoidalhexecontahedron` branch of
  Noperthedron, on the 64-core VM. The Lean code there was
  `Noperthedron/PentagonalHexecontahedron/`; the branch records the result at
  4243292d, whose code differs from the run's only in a log message. The check
  covered 3 caps, 250 tie nodes, the view cover, 39 tube tables and 36.2
  million chart-0 rows, and took 3 h 05 min with a peak of 30 GB.
  - The branch tip, b45e0b34 (2026-10-08), replaces the inconsistent axiom
    `QuadCoverTree.covers_of_valid` by a proof. The shared core here
    includes that fix.
- **In this repository:** the same modules, renamed (see
  [BUILDING.md](BUILDING.md), "Former names"), and an entry point. Since
  the deduplication of 2026-10-10, its certificate pipeline is the shared
  `proof/Pipeline/`, instantiated at its model (`SolidModel.lean`); the
  shared modules were the DH's, made generic, so the check functions are the
  same. The code was moved, so the result must be verified again here on the
  VM before it can be recorded against a commit of this repository. That run
  has not been done yet.

## Verifying existing data

The data from the verified run is archived by the author (not in this
repository); to check it yourself, rebuild it (see "Reproducing the data"
below). The program expects these directories:

- tube packs: `manifest.txt`, one pack per code triangle (39);
- chart packs: `c<chart>/t<code>.pack` for charts 0–2, or `chart0.pack`
  through `chart2.pack` (chart 3 is a 4-row table built into Lean,
  `FundamentalChart3`);
- caps: `u0.cert`, `ux.cert`, `u0_wide.cert`;
- ties: `dh-tie-data.txt`, `nodes.txt` and the `n<node>_t<k>.cert` files.

```sh
(cd proof && lake build constructDeltoidalHexecontahedron)
proof/.lake/build/bin/constructDeltoidalHexecontahedron \
  TUBEPACKS/manifest.txt PACKS CAPS TIES
```

It checks the caps, then the ties, then the view cover, the tube tables and
the four chart tables. A run takes about 3 h on 64 cores, with a peak of
about 30 GB.

## Reproducing the data

The search that produced the data is in [`search/dh/`](search/dh/) (from
the `deltoidalhexecontahedron` branch of nopert229, c0d289a; its `README.md`
describes it), with the code the solids' searches share now in
[`search/common/`](search/common/). To run the whole pipeline:

```sh
./get-cc-lib.sh
search/dh/rebuild.sh --from model --work DIR
```

The stages are model, tube, tubepack, caps, ties, search, pack and
verify (`--from STAGE`, `--only STAGE`; `--dry_run` prints the commands;
`--work` defaults to `work-dh/`). Without `--from` it starts at tube,
with the committed model data. The model, caps and ties stages regenerate
committed files: the model files in `search/dh/` and the Lean data
in `proof/DeltoidalHexecontahedron/` (`SolidModel`'s vertex tables,
`WedgeCoverData`, `OrbitData`, `StatementData`, `CapData`, `TieData`)
and `proof/Pipeline/IcoGroupData.lean`. The verify stage builds and
runs `constructDeltoidalHexecontahedron` in `proof/`, in a memory-capped
`systemd-run --user` scope. Since the deduplication of 2026-10-10 (see
[BUILDING.md](BUILDING.md), "Former names"), the vertices are in
`SolidModel.lean` and the solid's orbit tables in `OrbitData.lean`; the
rest of `IcoGroupData` is the shared `proof/Pipeline/IcoGroupData.lean`.
The generators were adapted to this layout on 2026-10-10: run from
the committed model files (with the `codebdd.json` that `codebdd.exe`
writes from `dh-model.txt`, about 0.1 s), `scripts/update-vertices.py`,
`emit-wedge-cover.py`, `snub-ico-group.py` and `dh-statement-data.py`
reproduce `SolidModel.lean` (updated in place), `WedgeCoverData.lean`,
`OrbitData.lean`, `StatementData.lean` and `Pipeline/IcoGroupData.lean`
byte for byte. (`CapData` and `TieData`, from the caps and ties stages,
are unchanged by the deduplication and were not rerun.)

A from-scratch run on 64 cores (2026-10-06, then in nopert229 and
Noperthedron) took 8 h 10 min:

| Stage | 64 cores |
|---|---|
| model, tube, tubepack, caps, ties | about 6 min |
| search | 4 h 36 min (22.06 M nodes) |
| pack | 35 min |
| verify | 2 h 52 min (chart 0: 32.9 M rows), peak about 30 GB |

That run regenerated every committed data file byte for byte, and its cap and
tie certificates were identical to the verified run's. Its chart tables are
not the same as the verified run's (32.9 M against 36.2 M chart-0 rows); both
passed.

In this repository (2026-10-10, 16 cores, before the deduplication):
the model stage, the cap frames and the tube and tie stages (about
2 min together) regenerate the model files in `search/dh/` and all seven
generated Lean files in `proof/DeltoidalHexecontahedron/` byte for byte
(with 250 tie nodes). The cap certificates, the search, the packs and the
check have not been rerun here.
