# search/ph: the pentagonal hexecontahedron's certificate search

This directory is the C++ search that produced the certificate data for the
pentagonal hexecontahedron ([../../pentagonal-hexecontahedron.md](../../pentagonal-hexecontahedron.md)).
It came from the `pentagonalhexecontahedron` branch of nopert229 at 04d115c,
without its working notes, and its Lean data generators from the same-named
branch of Noperthedron (da2965b3; Apache-2.0 there); the Lean formalization
is now in this repository's `../../proof/PentagonalHexecontahedron/` (former
names: `../../BUILDING.md`), and the top-level result is
`isNopert_of_certificatesValid` (see the page above). License: GPLv3
(`../COPYING`).

The C++ code that the solids' searches share is in
[`../common/`](../common/) (including the shared Lean data generators
`update-vertices.py` and `emit-wedge-cover.py`); the makefile builds it here,
with this solid's model headers (`model-vertices.h`,
`symmetry-neighbors.h`) and `solid.h` (its settings for the shared code).
This directory keeps the model files, the solid's own Lean data generators
(`scripts/`), `rebuild.sh` and the makefile.

## The pentagonal hexecontahedron is a Nopert

A polyhedron is *Rupert* if a hole can be cut through it through which a congruent copy can pass, and a *Nopert* if it is not Rupert (Lean: `¬ IsRupert`). This search, together with the Lean formalization in `../../proof/`, proves that **every pentagonal hexecontahedron is a Nopert**:

```lean
-- proof/PentagonalHexecontahedron/Statement.lean
theorem polarDualSnubDodecahedron_not_rupert (h : ∀ P : IModel, ¬ IsRupert P.toC5.verts) :
    ∀ V : Finset ℝ³, (V : Set ℝ³) = pentagonalHexecontahedron → ¬ IsRupert V
theorem pentagonalHexecontahedron_not_rupert (h : ∀ P : IModel, ¬ IsRupert P.toC5.verts) :
    ∀ V : Finset ℝ³, IsPentagonalHexecontahedron V → ¬ IsRupert V
```

- `IsRupert` is the Noperthedron project's statement of the Rupert property (`../../proof/MainTheorem.lean`, Mathlib only).
- `pentagonalHexecontahedron` is the polar dual of Wikipedia's snub dodecahedron: the set of poles of the facet planes of its convex hull (`facetPoles`), i.e. the points y with ⟨x, y⟩ ≤ 1 for every vertex x, with equality at three affinely independent vertices.
  - The snub dodecahedron is Wikipedia's definition, literally: ξ ≈ 0.94315 is the real zero of x³ + 2x² − φ², and the 60 vertices are the images of p = (φ² − φ²ξ, −φ³ + φξ + 2φξ², ξ) under repeated multiplication by M₁ (the rotation by 2π/5 about (0, 1, φ)) and M₂ (the cyclic shift of coordinates) (`WikipediaSnub.lean`).
  - Lean proves that this set has exactly the 92 expected points (`pentagonalHexecontahedron_eq`), so the theorem's hypothesis on `V` is satisfiable (`pentagonalHexecontahedron_finite`).
- `IsPentagonalHexecontahedron V` holds for any image of those points under a similarity: an orthogonal map (either chirality), a positive scale and a translation. The polar dual with respect to any sphere about the center (for instance the midsphere of the Catalan solid) is such an image.
- The hypothesis `∀ P : IModel, ¬ IsRupert P.toC5.verts` is what the executable `constructPentagonalHexecontahedron` checks.
  - An `IModel` is any polyhedron whose vertices are the orbits, under the icosahedral rotation group, of three points (on a 5-fold axis, on a 3-fold axis, and generic), each fixed by its stabilizer, within 6·10⁻¹⁶ of a fixed rational model.
  - The executable checks the certificate data natively, combines it with kernel-proved soundness theorems, and constructs this proposition.
  - The trust model is the same as for `native_decide`: Lean's kernel plus the compiled evaluation of the checkers. The statement's own facts (the 92 poles, their coordinates) are decided by the kernel.

The same solid is cc-lib's `PentagonalHexecontahedron()` (`geom/polyhedra.cc`, David McCooey's coordinates): `ph-crosscheck.py` recomputes McCooey's closed form to 60 digits and finds an orthogonal map taking one vertex set onto the other with mismatch 4·10⁻⁴⁰. The map is a reflection: McCooey's "laevo" form is the mirror image of the dual of Wikipedia's (and cc-lib's) snub dodecahedron. Both chiralities are covered.

## Reproducing the proof

Prerequisites:
- cc-lib at `../../cc-lib` (`../../get-cc-lib.sh`);
- clang with C++23, GMP and python3;
- the Lean project `../../proof`, with its toolchain (elan/lake).

```
./rebuild.sh --from model --work /path/to/work
```

`rebuild.sh` runs these stages. Each is restartable (`--from STAGE`, `--only STAGE`; `--dry_run` prints the commands).

| stage | what | time |
|---|---|---|
| build, model | `snub-model.py` writes the snub dodecahedron's exact model; `ph-model.py` its polar dual (`ph-model.txt`), which `ph-crosscheck.py` compares with McCooey's coordinates; `codebdd` computes the face-visibility codes and their triangles; the Lean data (vertices, the view-triangle cover, the icosahedral group and the orbits, the statement's certificates) is regenerated and Lean is built | 13 min |
| tube | `tubecode` and `tuberefine` build the identity tube, one tree per code | 11 min |
| tubepack | the tube trees become Lean packs | 1 min |
| search | `search5d`: the 5D search over (view, relative rotation) | 66 min |
| pack | `pack5d`: per-code certificate packs | 43 min |
| verify | `constructPentagonalHexecontahedron` on the packs | 23 min |

Measured on a from-scratch run (2026-10-05; 64 cores, 125 GB; Mathlib already built): 2 h 37 min in all, peak
memory 9.7 GB (one process), and every regenerated committed file came out byte-identical.

With blended inner points in the 5D rows (search5d's default since 2026-10-14), a from-scratch run on 64 cores
(2026-10-15, with the Lean build already up to date) took 1 h 08 min: model 8.1 min, tube 7.4 min, search 2.0 min (360,698 nodes), pack 30 min (chart 0:
591,252 rows; 66 MB of packs), verify 20 min. The time saved is mostly later search5d speedups, not the blends: from
the same tube trees, the search takes 2.0 min with or without them, and the packs are 64.6 MB without them (chart 0:
595,097 rows). search5d's later default, `--blend5d 4` ("escalate": a blended inner point only where the plain choice
fails), gives 63.9 MB (354,066 nodes; chart 0: 582,771 rows; search 2.0 min, pack 28 min, verify 18.5 min) and
verifies (2026-10-15); `rebuild.sh` uses it.

The verifier takes about 23 minutes on 64 cores (chart 0: 595,098 rows) and ends with:

```
constructed proof: no IModel (I-orbit within 6e-16 of the rational vertices) is Rupert
instantiated: no pentagonal hexecontahedron is Rupert
```

**Code texture (for rendering).** `./codebdd.exe --model_file=ph-model.txt --texture=BASE` writes an equirectangular image of all view directions colored by face-visibility code up to symmetry, a legend, and the solid as STL in the image's frame.

## How the proof works

### The model

The pentagonal hexecontahedron is the polar dual of the snub dodecahedron: its 92 vertices are the poles of the snub's 92 faces (12 pentagons, 80 triangles), and its 60 pentagonal faces are dual to the snub's vertices.
- `ph-model.py` takes the snub's exact model (`snub-model.txt`, 80 digits), rounds it to multiples of 2⁻⁶⁴, makes its pentagons exactly planar, and takes the poles in exact arithmetic. Each face of the dual (the plane v·x = 1 for a snub vertex v) is then *exactly* planar, which no independent rounding of the 92 vertices could achieve. The price: coordinates of up to 935 bits.
- The result is within 1.9·10⁻¹⁹ of the exact solid, scaled to circumradius just below 1.
- Frame: the snub's (z a 5-fold axis, x a 2-fold axis). Two vertices lie on the z axis; each is listed 5 times (exact copies) so that the fivefold indexing (vertex 20k + s is seed s rotated by 2πk/5) still applies: 100 vertex slots, 20 seeds. Certificates never use a copy of an axis vertex as a support vertex (it would fail against its own copies), and Lean's checks are unchanged.

### Symmetry reductions and the 5D search

As for the snub dodecahedron (the solids share the icosahedral group and frame):
1. **The view**, modulo Ih = I × {±1}, into the rational triangle T ⊇ one Schwarz (2,3,5) chamber.
2. **The relative rotation**, modulo I, into the max-trace (Dirichlet) cell around the identity, with the icosahedral prune.

`codebdd` splits T into 53 face-visibility codes (105 triangles). The identity tube is refined to radius 2·10⁻⁵, except code 18 (radius goal 1/400, see `rebuild.sh`). The 5D search covers (view triangle × Cayley box) with balanced and projective certificates, tube leaves and prunes. The exact checks are about three times slower than the snub's (the coordinates are much longer), and `PolyhedronEdges` needed a floating-point prefilter.

### The Lean side

- `IModel` (`IcoModel.lean`) is three base points with the I-orbits of the model: on a 5-fold axis (stabilizer C₅, 12 points), on a 3-fold axis (C₃, 20 points), generic (60 points); each base point is fixed by its stabilizer (a hypothesis), and the decided tables `orbitSlot`/`orbitStab` give the I-invariance of the hull.
- The identity tube's rows are checked against every vertex (`Box.ViewValid`); the snub's tangent-cone shortcut is not used.
- The statement (`Statement.lean`, `PolarDual.lean`): every facet pole has a vertex at level 1, which a rotation of the snub moves to p; for each pair of other vertices (S_j p, S_k p), either two vertices lie strictly on both sides of the plane through the three (Cramer's rule: no pole can exist), or the three lie on a known face and the pole is a rotated base pole. Conversely each base pole is a facet pole: the other vertices are strictly below its plane, and the pentagon's five vertices are exactly coplanar (an orbit of M₁, perpendicular to its axis). The facts are decided by the kernel with interval arithmetic (ξ to 10⁻²⁴), from `scripts/ph-statement-data.py`'s certificates.

## Code map

The shared files are in `../common/`; the solid's own are here.

- Model: `snub-model.txt` (the snub dodecahedron, from `../common/snub-model.py`), `ph-model.py`, `ph-model.txt` (its polar dual), `ph-crosscheck.py` (against McCooey's coordinates); `codebdd.cc` (codes; `rational_vertex` lines are used verbatim); `model.{h,cc}`.
- Identity tube: `tube.{h,cc}`, `tubecert.cc`, `tubetree.{h,cc}`, `tubecode.cc`, `tuberefine.cc`, `export-codetrees-pack.cc`.
- 5D search and packing: `exact5d`, `geom5d`, `contacts5d`, `bounds5d`, `cert5d`, `lp5d`, `rows5d`, `solve5d`, `tubeatlas5d`; `search5d.cc`, `pack5d.cc`, `scoreboard5d.cc`; `icoprune-check.cc`.
- Rendering: `codebdd --texture`.
- `rebuild.sh` runs the whole pipeline; `*_test.cc` are unit tests (`make`).
- Lean: `../../proof/PentagonalHexecontahedron/`, `../../proof/Pipeline/` and `../../proof/Atlas/`.
