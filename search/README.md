# The pentagonal hexecontahedron is a Nopert

A polyhedron is *Rupert* if a hole can be cut through it through which a congruent copy can pass, and a *Nopert* if it is not Rupert (Lean: `¬ IsRupert`). This repository, together with the Lean formalization on the `pentagonalhexecontahedron` branch of [Noperthedron](https://github.com/jcreedcmu/Noperthedron), proves that **every pentagonal hexecontahedron is a Nopert**:

```lean
-- Noperthedron/PentagonalHexecontahedron/Statement.lean
theorem polarDualSnubDodecahedron_not_rupert (h : ∀ P : IModel, ¬ IsRupert P.toC5.verts) :
    ∀ V : Finset ℝ³, (V : Set ℝ³) = pentagonalHexecontahedron → ¬ IsRupert V
theorem pentagonalHexecontahedron_not_rupert (h : ∀ P : IModel, ¬ IsRupert P.toC5.verts) :
    ∀ V : Finset ℝ³, IsPentagonalHexecontahedron V → ¬ IsRupert V
```

- `IsRupert` is the Noperthedron project's statement of the Rupert property (`Noperthedron/MainTheorem.lean`, Mathlib only).
- `pentagonalHexecontahedron` is the polar dual of Wikipedia's snub dodecahedron: the set of poles of the facet planes of its convex hull (`facetPoles`), i.e. the points y with ⟨x, y⟩ ≤ 1 for every vertex x, with equality at three affinely independent vertices.
  - The snub dodecahedron is Wikipedia's definition, literally: ξ ≈ 0.94315 is the real zero of x³ + 2x² − φ², and the 60 vertices are the images of p = (φ² − φ²ξ, −φ³ + φξ + 2φξ², ξ) under repeated multiplication by M₁ (the rotation by 2π/5 about (0, 1, φ)) and M₂ (the cyclic shift of coordinates) (`WikipediaSnub.lean`).
  - Lean proves that this set has exactly the 92 expected points (`pentagonalHexecontahedron_eq`), so the theorem's hypothesis on `V` is satisfiable (`pentagonalHexecontahedron_finite`).
- `IsPentagonalHexecontahedron V` holds for any image of those points under a similarity: an orthogonal map (either chirality), a positive scale and a translation. The polar dual with respect to any sphere about the center (for instance the midsphere of the Catalan solid) is such an image.
- The hypothesis `∀ P : IModel, ¬ IsRupert P.toC5.verts` is what the executable `constructPentagonalHexecontahedron` checks.
  - An `IModel` is any polyhedron whose vertices are the orbits, under the icosahedral rotation group, of three points (on a 5-fold axis, on a 3-fold axis, and generic), each fixed by its stabilizer, within 6·10⁻¹⁶ of a fixed rational model.
  - The executable checks the certificate data natively, combines it with kernel-proved soundness theorems, and constructs this proposition.
  - The trust model is the same as for `native_decide`: Lean's kernel plus the compiled evaluation of the checkers. The statement's own facts (the 92 poles, their coordinates) are decided by the kernel.

The same solid is cc-lib's `PentagonalHexecontahedron()` (`geom/polyhedra.cc`, David McCooey's coordinates): `ph_crosscheck.py` recomputes McCooey's closed form to 60 digits and finds an orthogonal map taking one vertex set onto the other with mismatch 4·10⁻⁴⁰. The map is a reflection: McCooey's "laevo" form is the mirror image of the dual of Wikipedia's (and cc-lib's) snub dodecahedron. Both chiralities are covered.

## Reproducing the proof

Prerequisites:
- this repository, with `../cc-lib`, `../ruperts`, `../codec` and `../sqlite` beside it (as for the other tom7 projects);
- clang with C++23, and GMP;
- a checkout of Noperthedron's `pentagonalhexecontahedron` branch at `../Noperthedron`, with its Lean toolchain (elan/lake).

```
./rebuild.sh --from model --work /path/to/work
```

`rebuild.sh` runs these stages. Each is restartable (`--from STAGE`, `--only STAGE`; `--dry_run` prints the commands).

| stage | what |
|---|---|
| model | `snub_model.py` writes the snub dodecahedron's exact model; `ph_model.py` its polar dual (`ph_model.txt`), which `ph_crosscheck.py` compares with McCooey's coordinates; `codebdd` computes the face-visibility codes and their triangles; the Lean data (vertices, the view-triangle cover, the icosahedral group and the orbits, the statement's certificates) is regenerated and Lean is built |
| tube | `tubecode` and `tuberefine` build the identity tube, one tree per code |
| tubepack | the tube trees become Lean packs |
| search | `search5d`: the 5D search over (view, relative rotation) |
| pack | `pack5d`: per-code certificate packs |
| verify | `constructPentagonalHexecontahedron` on the packs |

The verifier takes about 23 minutes on 64 cores (chart 0: 595,098 rows) and ends with:

```
constructed proof: no IModel (I-orbit within 6e-16 of the rational vertices) is Rupert
instantiated: no pentagonal hexecontahedron is Rupert
```

**Code texture and proof data (for rendering).** `./codebdd.exe --model_file=ph_model.txt --texture=BASE` writes an equirectangular image of all view directions colored by face-visibility code up to symmetry, a legend, and the solid as STL in the image's frame; `blender_code_texture.py` applies it in Blender. `viewmap.exe` maps the first-order margin (`--margin`), the 5D search density (`--search5d`) or the tube radius (`--tube`) over all views, as an equirectangular image and a UDIM-textured OBJ of the solid, with the most extreme views and the object rotations that show them (`_views.txt`).

## How the proof works

### The model

The pentagonal hexecontahedron is the polar dual of the snub dodecahedron: its 92 vertices are the poles of the snub's 92 faces (12 pentagons, 80 triangles), and its 60 pentagonal faces are dual to the snub's vertices.
- `ph_model.py` takes the snub's exact model (`snub_model.txt`, 80 digits), rounds it to multiples of 2⁻⁶⁴, makes its pentagons exactly planar, and takes the poles in exact arithmetic. Each face of the dual (the plane v·x = 1 for a snub vertex v) is then *exactly* planar, which no independent rounding of the 92 vertices could achieve. The price: coordinates of up to 935 bits.
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
- The statement (`Statement.lean`, `PolarDual.lean`): every facet pole has a vertex at level 1, which a rotation of the snub moves to p; for each pair of other vertices (S_j p, S_k p), either two vertices lie strictly on both sides of the plane through the three (Cramer's rule: no pole can exist), or the three lie on a known face and the pole is a rotated base pole. Conversely each base pole is a facet pole: the other vertices are strictly below its plane, and the pentagon's five vertices are exactly coplanar (an orbit of M₁, perpendicular to its axis). The facts are decided by the kernel with interval arithmetic (ξ to 10⁻²⁴), from `scripts/ph_statement_data.py`'s certificates.

## Code map

- Model: `snub_model.py`, `snub_model.txt` (the snub dodecahedron), `ph_model.py`, `ph_model.txt` (its polar dual), `ph_crosscheck.py` (against McCooey's coordinates); `codebdd.cc` (codes; `rational_vertex` lines are used verbatim); `model.{h,cc}`.
- Identity tube: `tube.{h,cc}`, `tubecert.cc`, `tubetree.{h,cc}`, `tubecode.cc`, `tuberefine.cc`, `export_codetrees_pack.cc`.
- 5D search and packing: `exact5d`, `geom5d`, `contacts5d`, `bounds5d`, `cert5d`, `lp5d`, `rows5d`, `solve5d`, `tubeatlas5d`; `search5d.cc`, `pack5d.cc`, `scoreboard5d.cc`; `icoprune_check.cc`.
- Rendering: `codebdd --texture`, `viewmap.cc`, `rigidity-margin.{h,cc}`, `blender_code_texture.py`.
- `rebuild.sh` runs the whole pipeline; `*_test.cc` are unit tests (`make`).
- Lean (Noperthedron `pentagonalhexecontahedron`): `Noperthedron/PentagonalHexecontahedron/`, plus the generic `Noperthedron/Atlas/`.

See `notes/HISTORY.md` for how this code came to be.
