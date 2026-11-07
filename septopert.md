# The Septopert
Tom 7, 7 Nov 2026

The Septopert is a convex polyhedron with 7 vertices that is not
Rupert (a "nopert"). It is an improved version of the [Septopert
Classic](septopert-classic.md), which was the first one we found in
this family. 7 vertices is the fewest possible vertices for a nopert.
This page gives the exact statement, what Lean checked and how, and
how to reproduce the result.

Lean entry point: [`proof/Septopert.lean`](proof/Septopert.lean).

<!-- TODO(Tom): credits/history -->

## The solid

![The Septopert, spinning around with confidence](septopert.gif)

Here is an exact [STL file](septopert.stl). On github, you can
rotate it around in your browser by just clicking on that. All the
members of the Septopert family look identical to human eyes (these
occupy only a tiny region of parameter space), but around here
we like to be precise!

The solid is the convex hull of these points (its vertices):

```
(-18,   9,   9)
(  9, -18,   9)
(  9,   9, -18)
( 17,   3,   3)
(  3,  17,   3)
(  3,   3,  17)
( -9,  -9,  -9)
```

The differences from the holotype [Septopert Classic](septopert-classic.md) are:
 * It has smaller integer coordinates
 * Its apex is a cube corner (dihedral edges are exactly 90°). It is in
   a special position at the edge of the Septopert family. This makes it
   harder to prove nopert; it needed a new kind of certificate.

The proof divides by 32 so that the maximum magnitude is below 1. In lowest
terms (the form used in Lean, `septopert` in `proof/Septopert.lean`):

| vertex |  x    |  y    |  z    |
|--------|-------|-------|-------|
| 0      | −9/16 | 9/32  | 9/32  |
| 1      | 9/32  | −9/16 | 9/32  |
| 2      | 9/32  | 9/32  | −9/16 |
| 3      | 17/32 | 3/32  | 3/32  |
| 4      | 3/32  | 17/32 | 3/32  |
| 5      | 3/32  | 3/32  | 17/32 |
| 6      | −9/32 | −9/32 | −9/32 |

- The statement is about these points (largest |v| = √486/32 ≈ 0.689).
  Any scale or rigid transformation of the solid is a Nopert.
- Symmetry C3v, as for Septopert Classic: a 3-fold axis along (1,1,1)
  and three mirror planes. Vertices 0–2 are the permutations of (a, b,
  b), vertices 3–5 those of (c, d, d), and vertex 6 is e·(1,1,1).
- 10 triangular faces, the same 10 as Septopert Classic's (vertex
  lists 015, 016, 024, 026, 045, 123, 126, 135, 234, 345); vertex
  degrees 5,5,5 (vertices 0–2), 4,4,4 (3–5) and 3 (vertex 6).
  Combinatorially a gyroelongated triangular pyramid, as before.
- **The special feature**: The apex, vertex 6, is a cube corner. Its
  three faces are mutually perpendicular, and equivalently the edges
  6–0, 6–1 and 6–2 are mutually orthogonal (each of length 27/32, and
  (v₀−v₆)·(v₁−v₆) = 0 exactly). Septopert Classic's apex edges are at
  90.33°; here the angle is exactly 90°.


### Edge info

Computed in exact arithmetic (rational face normals; dihedral angles
and lengths from the exact squared quantities). Relative edge lengths
are in units of the Lean coordinates (that is, the integer length
divided by 32).

![Line drawing of two views of the Septopert, with colored edges](septopert-edges.svg)

(Note: This is a schematic drawing used for any member of the Septopert family, not exact.)

| color | description | edges | dihedral angle | relative edge length |
|-------|-------------|-------|----------------|----------------------|
|![blue](swatch-apex.svg)| apex of pyramid | 6–0, 6–1, 6–2 | 90° (exactly) | 0.843750 (= 27/32) |
|![yellow](swatch-base.svg)| base of pyramid | 0–1, 0–2, 1–2 | 146.496544° | 1.193243 |
|![green](swatch-triforce-exterior.svg)| triforce exterior | 0–4, 0–5, 1–3, 1–5, 2–3, 2–4 | 106.945562° | 0.726856 |
|![red](swatch-triforce-center.svg)| triforce center | 3–4, 3–5, 4–5 | 140.882929° | 0.618718 |

(For comparison, Septopert Classic's apex dihedral is 90.333818°. The
squared lengths over 32² are 729, 1458, 541 and 392, so the apex edge
is the only rational length.)

## The statement

In [`proof/Septopert.lean`](proof/Septopert.lean):

```lean
theorem isNopert_of_certificatesValid (h : CertificatesValid) : IsNopert septopert
```

`IsNopert` and `IsRupert` are exactly as for Septopert Classic (see
[its page](septopert-classic.md#the-statement)): The points are not
all in one plane, and no rotated copy of the solid has a shadow that
fits strictly inside the shadow of another. `CertificatesValid` says
that the certificate data passes Lean's validity checks:

```lean
def CertificatesValid : Prop :=
  ∃ table : CayleyAtlas.ChartIndex → SolutionTree.Table,
    (∀ chart, (table chart).chart = chart) ∧
    (∀ chart, (table chart).Valid) ∧
    SolutionTree.CapOk ∧
    SolutionTree.ArcOk
```

That is: one solution table for each of the four charts that together
cover every rotation, each valid; `CapOk`, the cap certificate around the
mirror directions (as for Septopert Classic); and `ArcOk`, the new arc cap
certificate, which covers small rotations at views near an arc ending at
U = (2,2,−1)/3.

The trust model is the same as for Septopert Classic. The "genuine
solid" half is proved outright, and `isNopert_of_certificatesValid` is
checked by Lean's kernel and depends only on `propext`,
`Classical.choice` and `Quot.sound`. The data (about 844,000 table
rows in 43 MB of packs, 1 MB of tube packs and two cap certificates)
is too big for the kernel, so the program `constructSeptopert` runs
the same validity checks as compiled code and, only if every one
passes, builds `IsNopert septopert` and prints `instantiated: IsNopert
septopert (the Septopert is a Nopert: not Rupert)`. That step trusts
Lean's compiler and runtime (the trust of `native_decide`, which is
not used). The C++ search that produced the data does not need to be
trusted: A mistake there can only produce data that fails the checks.
The comments on Septopert Classic's page about the definition of
`IsRupert` and about degenerate point sets apply unchanged.

## How the proof works

The overall technique is the one described in [How the Nopert proofs
work](nopert-proof.md), and nearly everything is reused from Septopert
Classic, because the symmetry group, the combinatorics and the 22
view-code triangles (15 codes, numbered differently) are the same:

- the exact rational model, the view cover and the C3v reductions (C3 prune,
  mirror ties);
- the [identity tube](nopert-proof.md#the-identity-tube), replaced mostly by
  [identity blow-up rows](nopert-proof.md#identity-blow-up-certificates);
- the [cap](nopert-proof.md#caps) at the mirror normal (1, 0, −1)/√2, and the
  [5D search](nopert-proof.md#the-5d-search) with blended inner points for the
  rest.

The new piece is forced by the cube corner. The tube works by
first-order margins: Near the identity rotation, a view is ruled out
if some inner vertex must leave the outer shadow at first order, and
the margin says by how much. For Septopert Classic the margin is small
somewhere (about 3·10⁻⁴) but positive. For the Septopert it vanishes
outright along a sub-arc of views, the arc ending at U = (2,2,−1)/3,
the view straight down the apex edge 6–2. On this arc the face 0–2–6
is edge-on, and the right angle at the apex makes the first order
exactly zero: A tilt of the inner copy relative to the outer one moves
the apex and its two neighbours in the shadow by nothing at first
order, so there is a whole cone of first-order flexes that the first
order cannot rule out. Approaching the arc from the side where the
margin is positive, it goes to zero linearly with the distance, so the
tube radii shrink to nothing and no first-order certificate can reach
the arc.

The arc is not a passage, because the decision moves to second order,
where it is strictly negative: With the rotation angle θ, the best
clearance is about −3.69 θ² at U and between −4.46 θ² and −5.51 θ²
along the sub-arc (a floating-point and symbolic study, not part of
the proof; it explains why a certificate should exist). To prove that,
the **arc cap** blows up the rotation and the distance to the arc
together, along a rational parametrization of the arc: The view is
x(t) + μ·a·N, the rotation is μ·(s₁, s₂, s₃), and boxes in (t, a, s)
get width witnesses divided by μ, just as the point cap does at the
mirror normal but along a curve instead of at a point. The arc cap
claim is that no pose with any offset, whose view lies in a certain
convex polygon around U and the arc and whose rotation is within 1/46
in Cayley coordinates, is a passage. It is a certificate of 146 charts
(14,735 leaves, `capcert-neo`), and the exact cover of the polygon by
the pieces is proved in Lean (`proof/Pipeline/ArcCap.lean`,
`ArcCapClaim.lean`, `ArcCapCover.lean`, `ArcCapDecode.lean`; the
instance for this solid is `proof/Septopert/ArcCap.lean`). The tube
and the search leave that polygon (`search/septopert/arc-cap.txt`) to
the arc cap. See also [Arc caps](nopert-proof.md#arc-caps) in the
overview.

## Status

Verified on 2026-11-07: `constructSeptopert` checked the cap
certificate, the arc cap certificate (614 KB, 146 charts, 14,735 leaves;
Lean checking 344 s), the tube tables, and the four chart tables (472,636,
143,633, 123,513 and 104,558 rows), and printed `instantiated: IsNopert
septopert (the Septopert is a Nopert: not Rupert)`. Verification
took 548 s.

It was then reproduced from scratch (from the tube stage, with the model
files as committed) with 56 threads on a shared machine, giving the same row
counts and the same `instantiated` line:

```sh
./get-cc-lib.sh
(cd proof && lake exe cache get)    # Mathlib build cache
search/septopert/rebuild.sh --threads 56 --work work-fresh
```

The search is multithreaded and not deterministic, so other runs may
differ in details. Stages: `model`, `tube`, `idcap`, `tubepack`,
`cap`, `arccert`, `search`, `pack`, `verify` (`--from STAGE`, `--only
STAGE`, `--work DIR` as for Septopert Classic). The new stage
`arccert` runs `capcert-neo` once per piece of the arc cover.

Measured stage times of that run (2093 s in all, on a shared machine):

| Stage   | Time  |
|---------|-------|
| tube    | 158 s |
| idcap   | 640 s |
| cap     | 44 s  |
| arccert | 81 s  |
| search  | 143 s |
| pack    | 82 s  |
| verify  | 945 s |

The work directory was 2.1 GB.

## Verifying existing data

Given the data, only the last stage is needed:

```sh
(cd proof && lake build constructSeptopert)
cd work && ../proof/.lake/build/bin/constructSeptopert \
  tube_packs/manifest.txt packs cap-1_16.cert arc.cert
```

## The data

TODO(tom7): sizes and hosting. 

