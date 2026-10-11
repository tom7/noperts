# The snub dodecahedron

The snub dodecahedron is the Archimedean solid with 92 faces (12 pentagons
and 80 triangles), 150 edges and 60 vertices. It is not Rupert. This page
gives the exact statement, what Lean checked and how, and how to verify the
result.

Lean entry point: [`proof/SnubDodecahedron.lean`](proof/SnubDodecahedron.lean).

## The solid

The statement is about the exact solid, with irrational coordinates, in
Wikipedia's definition. With φ = (1 + √5)/2 and ξ ≈ 0.94315 the real zero of
x³ + 2x² − φ², the vertices are the images of

```
p = (φ² − φ²ξ, −φ³ + φξ + 2φξ², ξ)
```

under repeated multiplication by M₁ (the rotation by 2π/5 about (0, 1, φ))
and M₂ (the cyclic shift of coordinates, the rotation by 2π/3 about
(1, 1, 1)).

- These are 60 points (`snubDodecahedron` in
  `proof/Pipeline/WikipediaSnub.lean`, shared with the pentagonal
  hexecontahedron). `SnubOrbit` is the orbit defined
  literally as above, and `mem_snubDodecahedron_iff` shows it is the same
  set. ξ is defined as a root of the cubic, and `snubXiW_unique` shows it is
  the only real one.
- Symmetry I, the icosahedral rotation group of order 60, without
  reflections. So the solid is chiral (it has a left- and a right-handed
  form) and not centrally symmetric.
- It is the same solid as cc-lib's `SnubDodecahedron()` (checked
  numerically; not part of the Lean result).

## The statement

In [`proof/SnubDodecahedron.lean`](proof/SnubDodecahedron.lean):

```lean
theorem isNopert_of_certificatesValid (h : CertificatesValid) :
    ∀ V : Finset ℝ³, IsSnubDodecahedron V → IsNopert V
```

`IsSnubDodecahedron V` says that `V` is the image of Wikipedia's points under
a similarity: an orthogonal map, a positive scaling and a translation. The
orthogonal map may be a reflection, so **both chiralities** are covered
(`isSnubDodecahedron_mirror`: the mirror image of Wikipedia's solid is one).
So the theorem covers the exact solid, of either handedness, in any position,
size and orientation, and nothing else. The corollary
`isNopert_snubDodecahedron_of_certificatesValid` states it for Wikipedia's
coordinates themselves (`isSnubDodecahedron_snubDodecahedron`).

`IsNopert V` (in `proof/Nopert.lean`) says that the points of `V` are not all
in one plane, so their convex hull is a genuine solid, and that this solid is
not Rupert. `IsRupert` (in `proof/MainTheorem.lean`) is the Rupert property:
two copies of the solid, each rotated, can be placed so that the shadow of
one lies strictly inside the shadow of the other. `CertificatesValid` says
that the certificate data (four solution tables, sharing the identity-tube
tables) passes Lean's validity checks, and that the code triangles cover the
view domain.

## A neighborhood of a rational model

The certificates are checked against fixed rational vertices
(`proof/SnubDodecahedron/RationalVertices.lean`), not the irrational solid:

- In a frame where z is a 5-fold axis, the unit-circumradius solid, scaled by
  1 − 10⁻⁹, is rounded to multiples of 2⁻⁵², and its pentagons are made
  exactly planar. The result is within 2.7·10⁻¹⁶ of the exact solid.
- The solution tables exclude every *`IModel`*: every polyhedron whose 60
  vertices are an orbit of the icosahedral rotation group within 6·10⁻¹⁶ of
  this rational model (`not_isRupert_iModel_of_certificatesValid`).
- For the exact solid, Lean's kernel decides, by exact arithmetic in
  K = ℚ(√5, sin 72°) and a rational enclosure of ξ to 24 digits, that a
  rotation and scaling of Wikipedia's solid is such an `IModel`
  (`snubIModel`). Similarities, reflections included, preserve being Rupert,
  which gives every snub dodecahedron.

Unlike the deltoidal hexecontahedron, the snub dodecahedron is not on the
edge: the tables exclude a whole neighborhood of I-symmetric solids, so the
proof needs no exact claims (caps or ties) and no central symmetry.

## What is proved and what is verified

This is a **Lean verification**, not a plain Lean proof:

1. **Lean proof.** `isNopert_of_certificatesValid` is checked by Lean's
   kernel and depends only on the standard axioms (`propext`,
   `Classical.choice`, `Quot.sound`). Its "genuine solid" half needs no data
   at all: p and its images under the three half-turns about the coordinate
   axes span a tetrahedron. The facts about the exact solid are decided by
   the kernel.
2. **Verification of the data.** The data is too large for the kernel. The
   program `constructSnubDodecahedron` runs the same Lean validity checks as
   compiled code on every row, and only if all pass does it construct
   `CertificatesValid`, and from it (via part 1)
   `∀ V, IsSnubDodecahedron V → IsNopert V`. It then prints
   `instantiated: IsNopert V for every snub dodecahedron V (none is Rupert)`.
   This step trusts Lean's compiler and runtime to evaluate the checks
   correctly. That is the same trust as `native_decide`, though
   `native_decide` is not used.

The C++ search that produced the data does not need to be trusted: a mistake
there can only produce data that fails the checks.

## Status

- **2026-10-04:** verified on the `snubdodecahedron` branch of Noperthedron
  (the Lean code there was `Noperthedron/SnubDodecahedron/`), on the 64-core
  VM, by a from-scratch rebuild (below) whose last stage ran
  `constructSnubDodecahedron` on the packs, exit 0. The branch's tip
  (bc31c747, 2026-10-08) adds the QuadCoverTree fix, which replaced an axiom
  by a proved theorem; it is also in this repository's core.
- **In this repository:** the same modules, renamed (see
  [BUILDING.md](BUILDING.md), "Former names"), and an entry point. Since
  the deduplication of 2026-10-10, its certificate pipeline is the shared
  `proof/Pipeline/`, instantiated at its model (`SolidModel.lean`, one free
  orbit of I). The check functions are the same, except that the local-view
  tree now also accepts the deltoidal hexecontahedron's `empty` rows (pack
  tag 4), which the SD's data does not use; its identity-tube rows are still
  checked against the tangent-cone generators (`SparseSupport.lean`, which
  since the same day only provides the generators and their table to the
  check shared with candidate #231, `proof/Pipeline/SparseSupport.lean`). The
  code was moved, so the result had to be verified again here.
- **2026-10-10:** an independent from-scratch reproduction from a clone of
  this repository (after the move to the shared pipeline), on the 64-core VM:
  `search/sd/rebuild.sh --from model` regenerated every committed model and
  Lean data file byte for byte, and `constructSnubDodecahedron` checked the
  new packs (chart 0: 825,221 rows) and printed
  `instantiated: IsNopert V for every snub dodecahedron V (none is Rupert)`.

## Verifying existing data

The data is archived at `/mnt/nopertdata/archive/snub_dodecahedron/` on the
64-core VM, which is paused: verification needs Tom to unpause it. See the
archive's `README.txt` for its layout and checksums. The directories the
program expects:

- tube packs: `manifest.txt`, listing one pack per code triangle in code
  order;
- chart packs: `c<chart>/t<code>.pack` for charts 0–2, or `chart0.pack`
  through `chart2.pack` (chart 3 is a 4-row table built into Lean,
  `FundamentalChart3`).

```sh
(cd proof && lake build constructSnubDodecahedron)
proof/.lake/build/bin/constructSnubDodecahedron TUBEPACKS/manifest.txt PACKS
```

It checks the view cover, the tube tables and the four chart tables. On the
branch this took about 7 min on 64 cores.

Building the library takes longer than the check: the generated tangent-cone
table (`proof/SnubDodecahedron/GeneratedTangentCones.lean`, 4 MB) took about
18 min to build on the branch's VM, and 41 min with a peak of 25 GB on a
16-core workstation for this repository; the view-cover data
(`WedgeCoverData.lean`, 12 MB) took 4.5 min.

## Reproducing the data

The C++ search that produced the data is in [`search/sd/`](search/sd/), from
the `snubdodecahedron` branch of nopert229 (b8c9065); its
[`README.md`](search/sd/README.md) describes the method and the tools. The
generators of the Lean data are in `search/sd/lean_scripts/`; they reproduce
the committed generated files (`RationalVertices.lean`, `TangentCones.lean`'s
`supportGenerator`, `GeneratedTangentCones.lean`, `WedgeCoverData.lean`,
`OrbitData.lean`, the shared `proof/Pipeline/IcoGroupData.lean`, and the seed
count in `SolidModel.lean`) byte for byte (verified on 2026-10-10, after the
deduplication: the vertices are in `RationalVertices.lean`, the orbit tables
in `OrbitData.lean`, the tangent-cone generators in `TangentCones.lean`, and
`SparseSupport.lean` is now entirely hand-written, with the
`tangentCones` and `certificateViewCheck` instances). With cc-lib in place
(`./get-cc-lib.sh`, see [BUILDING.md](BUILDING.md)):

```sh
make -C search/sd -j 16
search/sd/rebuild.sh --from model --model_file snub_model.txt --work DIR
```

`rebuild.sh` runs the stages model, tube, tubepack, search, pack and verify;
each is restartable (`--from STAGE`, `--only STAGE`), and `--dry_run` prints
the commands. The work directory defaults to `work-sd/`. The model stage
rewrites the committed model and Lean data files in place and rebuilds
`constructSnubDodecahedron` (the tangent-cone table alone takes about 40 min
on 16 cores, see above); without `--from model` the run starts at the tube
stage, which needs `search/sd/codebdd.json` from the model stage
(`(cd search/sd && ./codebdd.exe --model_file=snub_model.txt codebdd.json)`,
about 30 s). The verify stage runs `proof/`'s `constructSnubDodecahedron` on
the packs.

A from-scratch run on the branch, on 64 cores (2026-10-04), took 1 h 3 min,
with a peak of about 26 GB:

| Stage | 64 cores (2026-10-04) | 64 cores, this repository (2026-10-10) |
|---|---|---|
| model (including the Lean build) | about 28 min | 26 min (Lean build 19 min) |
| tube | about 2.5 min | 2 min 20 s |
| tubepack | under 1 min | under 1 s |
| search | about 21 min | 22 min (452,068 nodes, 0 deferred) |
| pack | about 3 min | 3 min 43 s |
| verify | about 7 min | 6 min 56 s |
| total | 1 h 3 min | 1 h 1 min |

Both runs' model stages regenerated every committed data file byte for byte,
including the generated Lean files. Most of the model stage is the Lean
build of `GeneratedTangentCones.lean`, a single file that Lean compiles on
one core.
