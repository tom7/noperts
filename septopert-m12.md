# SeptopertM12
Tom 7, 7 Nov 2026

> [!NOTE]
> **SeptopertM12** is a 7-vertex nopert in the Septopert family, in the
> same doubly special position as the canonical [Septopert](septopert.md):
> a cube-corner apex and an exact Triforce. It was found by the height
> census a few hours before the Septopert, and its proof was developed
> first; the Septopert's proof reuses it with new constants.

SeptopertM12 is the convex hull of these points (its vertices):

```
(-11,  7,  7)
(  7,-11,  7)
(  7,  7,-11)
( 12,  3,  3)
(  3, 12,  3)
(  3,  3, 12)
( -5, -5, -5)
```

Its name is from its height in this frame (half the coordinate range,
rounded up: 12). It is congruent to the solid with vertices
(9, −9, −9), (−4, 5, 5), (−9, −9, −9) and their coordinate permutations,
of height 9, by the 180° rotation about (1,1,1) and a translation and
scaling.

The Lean statement uses the coordinates above divided by 16
(`vertexQ` in [`proof/SeptopertM12/Model.lean`](proof/SeptopertM12/Model.lean)).
Lean entry point: [`proof/SeptopertM12.lean`](proof/SeptopertM12.lean).

- Symmetry C3v and the same 10 faces as the rest of the family.
- *Cube corner*: the apex edges 6–0, 6–1, 6–2 are mutually orthogonal
  (each of length 18), so the apex dihedrals are exactly 90°.
- *Exact Triforce*: in the orthographic projection along the axis, the
  image of vertex 3 is −1/2 times the image of vertex 0, so triangle
  3–4–5 projects onto the medial triangle of 0–1–2; face 0–2–4 is parallel
  to the axis and perpendicular to face 3–4–5.
- Dihedral angles 90° (apex), 144.735610° (base, the same as the
  Septopert's), 107.993014° (triforce exterior) and 141.844193° (triforce
  center); edge lengths 18, 18√2, √237 and 9√2.

## The statement

In [`proof/SeptopertM12/IsNopert.lean`](proof/SeptopertM12/IsNopert.lean):

```lean
theorem isNopert_of_certificatesValid (h : CertificatesValid) : IsNopert verts
```

It depends only on the standard axioms (`propext`, `Classical.choice`,
`Quot.sound`). The trust model and the meaning of `IsNopert` are as for
the [Septopert](septopert.md#what-is-proved-and-what-is-verified).

## How the proof works

Exactly as for the [Septopert](septopert.md#how-the-proof-works): 13 view
codes and 16 view-code triangles, the mirror cap, and three special caps
(the cube-corner arc cap, the axis cap and the P cap along face 0–2–4's
edge-on circle). See also [How the Nopert proofs work](nopert-proof.md).

## Status

Verified on 2026-11-07: `constructSeptopertM12` (then `constructM12`)
checked the mirror cap, the arc cap (146 charts, 22,298 leaves), the axis
cap (52 charts, 3,450 leaves), the P cap (78 charts, 206,115 leaves), the
tube tables and the four chart tables (442,114, 124,955, 108,571 and
92,715 rows), and printed

```
instantiated: IsNopert SeptopertM12.verts (CapOk, ArcOk, AxisOk, PCapOk checked natively; tube and chart tables checked)
```

It took 99 minutes on 32 cores of a busy machine, 67 of them for the
P cap, most of that on a single chart. (The Septopert's P cap is about 5
times smaller.)

TODO: reproduction from scratch with `search/septopert-m12/rebuild.sh`.
