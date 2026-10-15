# Candidate #231

Candidate #231 is a convex polyhedron with 20 vertices, 27 faces (2
pentagons, 20 triangles and 5 planar quadrilaterals) and fivefold rotational
symmetry about an axis. It looks identical to candidate #214, which turned
out to be Rupert, but it is not Rupert. This page gives the exact statement,
what Lean checked and how, and how to verify the result.

Lean entry point: [`proof/Nopert231.lean`](proof/Nopert231.lean).

## The solid

The proof works with fixed rational vertices, `rationalVertices` in
[`proof/Nopert231/Vertices.lean`](proof/Nopert231/Vertices.lean). They are four
*seeds* and, for each seed, its rotations by multiples of 72° about the z
axis. Vertex 4k + s is seed s rotated by k · 72°. The seeds (`seedVertex`), to
15 digits:

| Seed | x | y | z | |
|---|---|---|---|---|
| 0 | 0.042458186590289 | 0.567100719501790 | 0.564825745458003 | top pentagon |
| 1 | −0.170282101451297 | 0.938646125467219 | 0.299912408997539 | quadrilaterals |
| 2 | −0.279581442950743 | 0.891515040028923 | −0.042130745709452 | |
| 3 | 0.057446211266240 | 0.601378495420756 | −0.762954469906766 | bottom pentagon |

- **Rational model.** The search's `codebdd` computes it from
  [`search/nopert231/nopert231_root.txt`](search/nopert231/nopert231_root.txt),
  the seeds that Tom's optimizer produced. The seeds are rotated in floating
  point and rounded to multiples of 2⁻⁵², scaled so that every vertex lies
  inside the unit sphere. Then the five quadrilaterals are made exactly
  planar: each seed-1 vertex is projected onto the plane of the other three
  vertices of its quadrilateral, which gives those five vertices denominators
  of about 260 bits. The rounding breaks the fivefold symmetry very slightly,
  so the theorem below is not about the rational model itself.
- **`C5Model`** (in `proof/Nopert231/SolidModel.lean`): any polyhedron whose 20
  vertices are four real seeds rotated *exactly* by 2πk/5 about z, k = 0, …,
  4, with each vertex within 6·10⁻¹⁶ of the corresponding rational vertex.
  (It is the shared certificate pipeline's `CyclicModel` for this solid's
  model, the `FivefoldSolid` instance `Nopert231.fivefoldSolid`.) The theorem
  covers all of them. Two are named:
  - **The exact model** `exactVerts` (`exactModel`): the four rational seeds
    above, rotated exactly. Its quadrilaterals are planar only to about
    2·10⁻¹⁶.
  - **Idealized #231** `Ideal231.model` (`proof/Nopert231/Ideal231.lean`):
    seeds 0, 2 and 3 as above, with seed 1's height replaced by the unique
    height that puts it in the plane of its quadrilateral. It has exact
    fivefold symmetry and exactly planar quadrilaterals
    (`Ideal231.quad_planar`). Lean's kernel decides that it is within
    4.1·10⁻¹⁶ of the rational model.

## The statement

In [`proof/Nopert231.lean`](proof/Nopert231.lean):

```lean
theorem isNopert_of_certificatesValid (h : CertificatesValid) :
    ∀ P : C5Model, IsNopert P.verts
```

So, given the certificate data, every `C5Model` is a nopert. The corollaries
`isNopert_exactVerts_of_certificatesValid` and
`isNopert_ideal231_of_certificatesValid` state it for the exact model and for
idealized #231, and `nonempty_c5Model` shows that the hypothesis class is not
empty.

`IsNopert V` (in `proof/Nopert.lean`) says that the points of `V` are not all
in one plane, so their convex hull is a genuine solid, and that this solid is
not Rupert. `IsRupert` (in `proof/MainTheorem.lean`) is the Rupert property:
two copies of the solid, each rotated, can be placed so that the shadow of
one lies strictly inside the shadow of the other. `CertificatesValid` says
that the certificate data passes Lean's validity checks. The data is four
solution tables, one per Cayley chart of the rotations, which share the
identity-tube tables. That the code triangles cover the view domain
(`WedgeCover.codeTriangles_cover`) is decided by the kernel, so it is not part
of the hypothesis.

## What is proved and what is verified

This is a **Lean verification**, not a plain Lean proof:

1. **Lean proof.** `isNopert_of_certificatesValid` is checked by Lean's
   kernel and depends only on the standard axioms (`propext`,
   `Classical.choice`, `Quot.sound`). Its "genuine solid" half needs no data
   at all (`C5Model.not_coplanar`). Seed 0 rotated by 0°, 72° and −72° gives
   three points of one horizontal plane that are not on a line, and seed 3
   lies below that plane.
2. **Verification of the data.** The data is far too large for the kernel:
   chart 0 alone has about 25 million rows. The program `constructNopert231`
   runs the same Lean validity checks as compiled code on every row. Only if
   all pass does it construct `CertificatesValid`, and from it (via part 1)
   `∀ P : C5Model, IsNopert P.verts`. It then prints
   `instantiated: IsNopert P.verts for every C5Model P, including the exact model and idealized #231 (none is Rupert)`.
   This step trusts Lean's compiler and runtime to evaluate the checks
   correctly. That is the same trust as `native_decide`, though
   `native_decide` is not used.

The C++ search that produced the data does not need to be trusted: a mistake
there can only produce data that fails the checks.

## Status

- **2026-10-04:** verified on the `nopert231` branch of Noperthedron (the
  Lean code there was `Noperthedron/Nopert231/`, namespace
  `Noperthedron.Nopert231`), on the 64-core VM. `constructNopert231` checked
  the tube tables and the four chart tables in about 2 h 46 min, with a peak
  of about 32 GB. A from-scratch rebuild (below) also passed. The branch's tip
  (0c83e4ba, 2026-10-08) adds the QuadCoverTree fix, which replaced an axiom
  by a proved theorem. That fix is also in this repository's core.
- **In this repository:** the same modules, with their history (merged from
  that branch), renamed:
  - namespace `Nopert231`;
  - `QuadCoverTree` and `QuadraticBernstein` are the core's identical
    `Atlas/` modules;
  - the two unused `native_decide` proofs (chart 3 and the tangent cones,
    whose kernel proofs are what the proof uses) are deleted;
  - an entry point and an executable that establishes `CertificatesValid`.

  No check function changed.
- **2026-10-10, shared pipeline:** the modules that were copies of the
  shared certificate pipeline (`proof/Pipeline/`, used by the other
  data-backed results) were deleted, and #231 uses the pipeline through its
  model (`SolidModel.lean`, a `FivefoldSolid`). What stays in
  `proof/Nopert231/` is its data, its model, its tangent cones, and its own
  top layer (the solution tree over the fivefold-reduced domain, its decoder
  and the executable checker); see `proof/Nopert231/README.md`. The check
  functions are the same definitions, except that the identity-tube tables
  now also accept the pipeline's `empty` rows (tag 4, which #231's data does
  not use) and take the table's root from its first row (0 for #231's data).
  The statement is unchanged in meaning. The code was moved, so the result
  must be verified again here on the VM before it can be recorded against a
  commit of this repository. That run has not been done yet.

## Verifying existing data

The data from the verified run is archived by the author (not in this
repository); to check it yourself, rebuild it (see "Reproducing the data"
below). The program expects these directories:

- tube packs: `manifest.txt`, which lists one pack per code triangle (153) in
  code order;
- chart packs: `c<chart>/t<code>.pack` for charts 0–2, or `chart0.pack`
  through `chart2.pack`. Chart 3 is a 4-row table built into Lean
  (`FundamentalChart3`).

```sh
(cd proof && lake build constructNopert231)
proof/.lake/build/bin/constructNopert231 TUBEPACKS/manifest.txt PACKS
```

It checks the tube tables, then the four chart tables. On the branch this took
about 2 h 46 min on 64 cores, with a peak of about 32 GB.

## Reproducing the data

The search that produced the data is in
[`search/nopert231/`](search/nopert231/), with its history. It comes from the
`nopert231` branch of nopert229 (e53dfda), and its `README.md` describes it;
the code the solids' searches share is now in [`search/common/`](search/common/).
To run the whole pipeline:

```sh
./get-cc-lib.sh
search/nopert231/rebuild.sh --from model --work DIR
```

The stages are model, tube, tubepack, search, pack and verify. The options
are `--from STAGE` and `--only STAGE`; `--dry_run` prints the commands, and
`--work` defaults to `work-231/`. Without `--from`, the run starts at tube,
with the committed model data.

The model stage regenerates committed files:

- the model files in `search/nopert231/`;
- with `search/nopert231/scripts/`, the Lean data in `proof/Nopert231/`:
  `Vertices`, `GeneratedTangentCones` and `WedgeCoverData`.

The verify stage builds and runs `constructNopert231` in `proof/`, in a
memory-capped `systemd-run --user` scope.

A from-scratch run on 64 cores (2026-10-04, then in nopert229 and
Noperthedron) took 4 h 49 min:

| Stage | 64 cores |
|---|---|
| model (including the Lean build) | about 7 min |
| tube | about 8 min |
| tubepack | under 1 min |
| search | about 56 min (21.2 M nodes) |
| pack | about 52 min |
| verify | about 2 h 46 min, peak about 32 GB |

With blended inner points in the 5D rows (search5d's default since
2026-10-14), a from-scratch run on 64 cores (2026-10-14) took 2 h 33 min:
model 2.3 min, tube 8 min, search 17.5 min (9.3 M nodes), pack 31.5 min
(1.85 GB of packs; chart 0 has 10.6 M rows), verify 1 h 33 min (about
13 GB resident while checking chart 0).

The search is not deterministic, so a new run gives different but equally
checkable packs.

In this repository (2026-10-10, 16 cores):

- `codebdd` regenerates the model files `model_vertices.{h,json,lean}` byte
  for byte.
- From those files, the generators in `search/nopert231/scripts/` regenerate
  `Vertices.lean`, `GeneratedTangentCones.lean` and `WedgeCoverData.lean` in
  `proof/Nopert231/` byte for byte. After the shared-pipeline change (same
  day) `Vertices.lean` and `GeneratedTangentCones.lean` were regenerated again
  and are still identical (`update_vertices.py` rewrites only the two data
  bodies of `Vertices.lean`); `WedgeCoverData.lean` is unchanged and still
  imports `Nopert231.WedgeCover`, which now names the pipeline's checker.
- The tube stage, the search, the packs and the check have not been rerun
  here.
