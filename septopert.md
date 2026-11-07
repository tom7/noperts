# The Septopert
Tom 7, 7 Nov 2026

The Septopert is a convex polyhedron with 7 vertices that is not
Rupert (a "nopert"). It is an improved version of the [Septopert
Classic](septopert-classic.md), which was the first one we found in
this family. 7 vertices is the fewest possible vertices for a nopert.
This page gives the exact statement, what Lean checked and how, and
how to reproduce the result.

Lean entry point: [`proof/Septopert.lean`](proof/Septopert.lean).

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
 * Its apex is a cube corner (dihedral angles are exactly 90°). It is
   in a special position at the edge (we think) of the Septopert
   family. This makes it harder to prove nopert; it needed a new kind
   of certificate.

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

`IsNopert V` (in `proof/Nopert.lean`) says that the points of `V` are
not all in one plane, so their convex hull is a genuine solid, and
that this solid is not Rupert. `IsRupert` (in
`proof/MainTheorem.lean`) is the Rupert property: Two copies of the
solid, each rotated, can be placed so that the shadow of one lies
strictly inside the shadow of the other. `CertificatesValid` says that
the certificate data (four solution tables, a mirror cap certificate,
and an arc cap certificate) passes Lean's validity checks. The same
`IsNopert` is used by the [minimality](minimality.md) result, so the
[two together](proof/ProofOfMainTheorem.lean) say that the vertex
count of the smallest possible nopert is exactly 7.

## What is proved and what is verified

The main content is the non-existence of a rupert passage. This is a
**Lean verification**, not a direct kernel-only Lean proof:

1. **Lean proof.** `isNopert_of_certificatesValid` is checked by Lean's
   kernel and depends only on the standard axioms (`propext`,
   `Classical.choice`, `Quot.sound`).
2. **Verification of the data.** The data is about 850,000 table rows
   (45 MB), too much for the kernel. The program `constructSeptopert`
   runs the same Lean validity checks as compiled code on every row,
   and only if all pass does it construct `IsNopert septopert` (via
   part 1) and print `instantiated: IsNopert septopert (the Septopert
   is a Nopert: not Rupert)`. This step trusts Lean's compiler and
   runtime to evaluate the checks correctly. This is the same trust as
   `native_decide`, though `native_decide` is not used.

The C++ search in `search/septopert/` that produced the data does not
need to be trusted: A mistake there can only produce data that fails
the checks. That said, the C++ does its own independent checks of the
certificate conditions as it searches for them and prepares them for
Lean. It would be very unlikely that a bug in the Lean
compiler/runtime would also occur in the C++ search (perhaps something
like a bug in GMP's integer multiplication routines.)

We also need to trust that the proof statement itself matches the
pre-formal idea of what we mean by "Rupert" and "Nopert". I use the
same [definition](proof/MainTheorem.lean) from the Noperthedron
project. It is not very mysterious:

```lean
def IsRupert (vertices : Finset (EuclideanSpace ℝ (Fin 3))) : Prop :=
   ∃ inner_rotation ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
   ∃ inner_offset : EuclideanSpace ℝ (Fin 2),
   ∃ outer_rotation ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
   let hull := convexHull ℝ vertices
   let inner_shadow := { inner_offset + proj_xy (inner_rotation.toEuclideanLin p) | p ∈ hull }
   let outer_shadow := { proj_xy (outer_rotation.toEuclideanLin p) | p ∈ hull }
   inner_shadow ⊆ interior outer_shadow
```

A set of points (note: not a solid) is Rupert if there exist
rotations for the inner and outer copies (`specialOrthogonalGroup`
just means 3D rotation), and a 2D translation of the inner copy, such
that the inner shadow is contained in the interior of the outer
shadow. The shadows are just the 2D projections of the 3D convex
hulls. This is almost identical to how I describe it to people on
the whiteboard.

That said: There is certainly subtlety to be wary of! For example,
I could have presented you a proof like this:

```lean
noncomputable def CoolShape : Finset ℝ³ := { ... vertices ... }

theorem CoolShapeIsNotRupert : ¬ IsRupert CoolShape := by ...
```

And claimed that this `CoolShape` is a Nopert (not Rupert) with some
enormous meandering proof. But `¬ IsRupert` is also easily satisfied
by degenerate vertices! For example, if all the vertices are
collinear, then the convex hull is just a line, and its interior is
empty, so we can never have `line ⊆ ∅`. Our
[definition](proof/Nopert.lean) of `IsNopert` adds a condition that
the point set gives a genuine solid 
(`¬ Coplanar ℝ (V : Set ℝ³) ∧ ¬ IsRupert V`).

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
the apex and its two neighbours only along the shadow's edge (never
outward) at first order, so there is a whole cone of first-order
flexes that the first order cannot rule out. Approaching the arc from
the side where the margin is positive, it goes to zero linearly with
the distance, so the tube radii shrink to nothing and no first-order
certificate can reach the arc.

The arc is not a passage, because the decision moves to second order,
where it is strictly negative: With the rotation angle θ, the best
clearance is about −3.69 θ² at U and between −4.46 θ² and −5.51 θ²
along the sub-arc (a floating-point and symbolic study, not part of
the proof; it explains why a certificate should exist). To prove that,
the **arc cap** blows up the rotation and the distance to the arc
together, along a rational parametrization of the arc: The view is
x(t) + ν·t·α·N (a distance ν·t off the arc at position t along it),
and the rotation is ν·t·s₁ along the arc's first-order flex plus
ν²·t·s₂ and ν²·t²·s₃ in the two other directions. Boxes in (t, ν, α, s)
then get width witnesses with the common factors of ν divided out,
just as the point cap does at the mirror normal but along a curve
instead of at a point. At U itself, where the arc ends, a point cap of
the same kind takes views μ·(a, b) away from U, with a tilt μ·(s₁, s₂)
and a spin μ²·s₃ of the rotation. The arc cap
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

The certificate data is machine output, intended to be CC0 (but not
hosted here):

- `arc.cert`: 614 KB, the arc cap certificate (146 charts, 14,735 leaves);
- `cap-1_16.cert`: 520 KB, the cap certificate around the mirror directions;
- `tube_packs/`: 960 KB, 22 identity-tube tables and `manifest.txt`;
- `packs/`: 44 MB, 88 solution packs, one for each of the 4 charts and
  22 view-code triangles (`packs/c<chart>/t<triangle>.pack`; about
  844,000 rows; the largest, `packs/c0/t2.pack`, is 3.1 MB).

All four together compress to about 8 MB (`tar czf`).

To check it yourself, rebuild it (see "Status" above).

