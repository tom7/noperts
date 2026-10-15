> **Provenance.** This directory is the C++ certificate search that produced
> the snub dodecahedron's certificate data. It comes from the
> `snubdodecahedron` branch of nopert229 at commit b8c9065 (2026-10-04), minus
> the branch's private working notes. GPLv3 (`../COPYING`). Changes: build and
> script paths point into this repository (cc-lib at `../../cc-lib`, the Lean
> project at `../../proof`, work directory `../../work-sd`), and the Lean data
> generators, which were in Noperthedron's `scripts/` (`snubdodecahedron`
> branch, bc31c747), are in `scripts/`, emitting this repository's module
> names. They reproduce the committed `proof/SnubDodecahedron/` data byte for
> byte. The text below is the branch's README: Lean names and paths in it are
> the branch's (Noperthedron `Noperthedron/SnubDodecahedron/...` is
> `proof/SnubDodecahedron/...` here; see `../../BUILDING.md`, "Former names").
> For the statement as proved in this repository and how to run the pipeline
> here, see [`../../snub-dodecahedron.md`](../../snub-dodecahedron.md).
>
> Since 2026-10-10 the C++ code that the solids' searches share is in
> [`../common/`](../common/); the makefile builds it here, with this solid's
> model headers (`model_vertices.h`, `symmetry_neighbors.h`) and `solid.h`
> (its settings for the shared code). This directory keeps the model files,
> the Lean data generators, `rebuild.sh` and the makefile. The code map
> below names the files as in the branch.

# The snub dodecahedron is a Nopert

A polyhedron is *Rupert* if a hole can be cut through it through which a congruent copy can pass, and a *Nopert* if it is not Rupert (Lean: `¬ IsRupert`). This repository, together with the Lean formalization on the `snubdodecahedron` branch of [Noperthedron](https://github.com/jcreedcmu/Noperthedron), proves that **every snub dodecahedron is a Nopert**:

```lean
-- Noperthedron/SnubDodecahedron/Statement.lean
theorem wikipediaSnubDodecahedron_not_rupert (h : ∀ P : IModel, ¬ IsRupert P.toC5.verts) :
    ¬ IsRupert snubDodecahedron
theorem snubDodecahedron_not_rupert (h : ∀ P : IModel, ¬ IsRupert P.toC5.verts) :
    ∀ V : Finset ℝ³, IsSnubDodecahedron V → ¬ IsRupert V
```

- `IsRupert` is the Noperthedron project's statement of the Rupert property (`Noperthedron/MainTheorem.lean`, Mathlib only).
- `snubDodecahedron` is Wikipedia's definition, literally:
  - ξ ≈ 0.94315 is the real zero of x³ + 2x² − φ² (`snubXiW_unique`);
  - the 60 vertices are the images of p = (φ² − φ²ξ, −φ³ + φξ + 2φξ², ξ) under repeated multiplication by M₁ (the rotation by 2π/5 about (0, 1, φ)) and M₂ (the cyclic shift of coordinates). See `SnubOrbit` and `mem_snubDodecahedron_iff`.
- `IsSnubDodecahedron V` holds for any image of those vertices under a similarity: an orthogonal map (either chirality), a positive scale and a translation.
- The hypothesis `∀ P : IModel, ¬ IsRupert P.toC5.verts` is what the executable `constructSnubDodecahedron` checks.
  - An `IModel` is any polyhedron whose 60 vertices are an orbit of the icosahedral rotation group within 6·10⁻¹⁶ of a fixed rational model.
  - The executable checks the certificate data natively, combines it with kernel-proved soundness theorems, and constructs this proposition.
  - The trust model is the same as for `native_decide`: Lean's kernel plus the compiled evaluation of the checkers.

The same solid is cc-lib's `SnubDodecahedron()` (`geom/polyhedra.cc`). Checked numerically, its normalized vertices are a rotation of Wikipedia's.

## Reproducing the proof

Prerequisites:
- cc-lib at `../../cc-lib` (`../../get-cc-lib.sh`); `../../codec` only for `shadowanim.exe` (rendering), which is not part of the pipeline;
- clang with C++23, and GMP;
- the Lean project at `../../proof`, with its Lean toolchain (elan/lake).

From this directory (the work directory defaults to `../../work-sd`):

```
./rebuild.sh --from model --model_file snub_model.txt --work /tmp/snub
```

`rebuild.sh` runs these stages. Each is restartable (`--from STAGE`, `--only STAGE`).

| stage | what | time (64 cores) |
|---|---|---|
| model | `snub_model.py` writes the exact model; `codebdd` computes the rational model, the face-visibility codes and their triangles; the Lean data (vertices, tangent cones, the view-triangle cover, the icosahedral group) is regenerated and Lean is built | ~28 min (mostly the Lean build; the 60-vertex tangent-cone file alone takes ~18 min) |
| tube | `tubecode` and `tuberefine` build the identity tube, one tree per code | ~2.5 min |
| tubepack | the tube trees become Lean packs | <1 min |
| search | `search5d`: the 5D search over (view, relative rotation) | ~21 min |
| pack | `pack5d`: per-code certificate packs | ~3 min |
| verify | `constructSnubDodecahedron` on the packs | ~7 min |

Measured on 2026-10-04 from a clean checkout: 1 h 3 min in all, exit 0. The model stage regenerates every committed data file byte for byte (`snub_model.txt`, `symmetry_neighbors.h`, `model_vertices.*`, and the generated Lean files).

With blended inner points in the 5D rows (search5d's default since 2026-10-14), a from-scratch run on 64 cores
(2026-10-15, with the Lean build already up to date) took 24 min: model 7.5 min, tube 2.4 min, search 3.0 min
(454,496 nodes), pack 3.2 min (chart 0: 828,055 rows; 97 MB of packs), verify 7.9 min. For this solid the blends
do not pay: on an idle machine the search takes 2:16 with them and 2:14 without (452,068 nodes, as on 2026-10-04; the
earlier 22 min predates later search5d speedups), and the packs are 99.7 MB with them and 96.6 MB without (chart 0:
825,220 rows). search5d's later default, `--blend5d 4` ("escalate": a blended inner point only where the plain choice
fails), gives 96.4 MB (449,374 nodes; chart 0: 822,041 rows) and verifies (2026-10-15); `rebuild.sh` uses it.

Peak memory is about 26 GB. The verifier ends with:

```
constructed proof: no IModel (I-orbit within 6e-16 of the rational vertices) is Rupert
instantiated: no snub dodecahedron is Rupert
instantiated: Wikipedia's snub dodecahedron is not Rupert
```

`snub_model.py` regenerates the model file `snub_model.txt` (and `symmetry_neighbors.h`) from the exact solid to 80 digits.

**Code texture (for rendering).** `./codebdd.exe --model_file=snub_model.txt --texture=BASE` also writes `BASE.png`, an equirectangular image (8192×4096; `--texture_width`) of all view directions colored by face-visibility code up to the solid's symmetries and the antipode; `BASE.txt`, the legend (each class's color, area and `codebdd.json` codes); and `BASE.stl`, the solid in the image's frame. `../common/blender_code_texture.py` applies it to an object in Blender (an Environment Texture node fed with object coordinates, so each surface point takes the color of its direction).

**Proof data over the views (for rendering).** `viewmap.exe` maps a quantity over all view directions, each reduced into the view triangle by the solid's symmetries and the antipode as in the proof:
- `--margin`: the first-order rigidity margin of the identity pose (where it is small, the search works hardest);
- `--search5d`: the 5D search's leaves per unit view area, from the journals (`--journals WORK/jobs`, one `--chart` or all);
- `--tube`: the identity tube's certified radius (`--trees_dir WORK/trees_r2`).

It writes an equirectangular image (`--equirect W`, as above), a UDIM-textured OBJ of the solid (`--udim S`: one S×S tile per triangle; import the OBJ in Blender and set the image to UDIM tiles), a color bar, and `_views.txt`: the most extreme views, each with the object rotation (quaternion and XYZ Euler angles) that turns it toward a camera on the +z axis. For example, `./viewmap.exe --margin --trees_dir WORK/trees_r2 --grid 8192 --equirect 32768 --udim 8192 --out margin` needs about 3.5 GB; the grid (`--grid`) sets the resolution of the data, the image sizes that of the textures.

## How the proof works

### The rational model

The certificates are checked against fixed rational vertices, not the irrational solid.
- The frame: z is a 5-fold axis through a pentagon, and x is a 2-fold axis. Vertex 12k + s is seed s rotated by 2πk/5.
- `codebdd` rounds every coordinate of the unit-circumradius solid, scaled by 1 − 10⁻⁹, to a multiple of 2⁻⁵², then projects the pentagons exactly planar.
- The result is within 2.7·10⁻¹⁶ of the exact solid.
- Lean proves the result for every `IModel`: every I-orbit within 6·10⁻¹⁶ of this model. `Statement.lean` then shows that the exact solid is one of them, via a decided interval check.

### Symmetry reductions

A pose is a view direction (the outer rotation's third row) and a relative rotation R between the two copies. If R is a symmetry, the two shadows coincide and nothing can be certified there. So both are reduced modulo the solid's symmetry before any search.

1. **The view**, modulo Ih = I × {±1}, into one Schwarz (2,3,5) chamber, 1/120 of the sphere (`IcoView.lean`).
   - Choose the sign and g ∈ I maximizing ⟨±G_gᵀv, c⟩ for a rational point c inside the chamber.
   - The chamber's walls are mirrors −H_i of half-turns H_i ∈ I, so the reduced view w satisfies ⟨w, c + H_i c⟩ ≥ 0.
   - Exact Farkas multipliers (in K, decided by the kernel) turn this into membership in the rational triangle T ⊇ chamber, with corners (0,0,1), (500,160,683)/1343 and (250,345,686)/1281.
2. **The relative rotation**, modulo I, into the max-trace (Dirichlet) cell around the identity (`AtlasIcoPrune.lean`, `IcoReduction.lean`).
   - This cell lies in Cayley chart 0 (rotation angle ≤ 44.3°).
   - The search rejects boxes outside it with the *icosahedral prune*: for one of the 12 neighbors G_n (±72° about the six 5-fold axes), the trace advantage trace(R G_n) − trace R, times the Cayley denominator, is a quadratic in the Cayley coordinates, and is bounded below by Bernstein or tight-ball bounds.
   - The rounding of G_n to 10⁻¹² is covered by an allowance of 36·10⁻¹².

### Frame and exact algebra

Every rotation of I in this frame has entries in K = ℚ(√5, s), with s = sin 72° and s² = (5 + √5)/8.
- In this frame, every entry is an integer combination of 1, √5, s and s√5, divided by 20.
- `IcoField.lean` represents K by four integers, with computable arithmetic.
- `IcoGroup.lean` decides the group facts by kernel computation in seconds: closure (from the 180 generator products, by induction over breadth-first parents), SO(3) membership, and Σg = 0.
- Rational enclosures of √5 and s give signs and bounds.

### Codes, the identity tube and the 5D search

- **Codes.** `codebdd` splits T into the cells where the silhouette's combinatorics (the face-visibility code) is constant: 123 codes in 245 triangles.
- **The identity tube.** Near the identity relative rotation, `tubecode` and `tuberefine` certify, for each code, a tree of triangles with a first-order rigidity certificate and a radius.
- **The 5D search.** `search5d` covers (view triangle × Cayley box) in each chart with leaves of these kinds:
  - balanced and projective certificates;
  - tube leaves (inside the tube radius);
  - prunes: radius, fivefold and icosahedral.

  It runs in about 25 minutes with nothing deferred. Charts 1 and 2 are pruned entirely.
- **Packs and checking.** `pack5d` writes per-code Lean packs. The Lean checker validates every row natively, along with the cover of T by the code triangles (`WedgeCover`), and the kernel-proved soundness theorems (`AtlasProjectiveSolutionTree.valid_imp_noRupert_ix`) turn validity into non-Rupertness.

## Code map

- Model, codes, the C++ checkers and search:
  - `snub_model.py`, `snub_model.txt`: the exact model.
  - `codebdd.cc`: the rational model and the code database (`codebdd.json`, `model_vertices.*`).
  - `model.{h,cc}`: the rational vertices.
- Identity tube: `tube.{h,cc}`, `tubecert.cc`, `tubetree.{h,cc}`, `tubecode.cc`, `tuberefine.cc`, `export_codetrees_pack.cc`.
- 5D search and packing:
  - `exact5d` (the exact Lean-mirroring checks), `geom5d`, `contacts5d`, `bounds5d`, `cert5d`, `lp5d`, `rows5d`, `solve5d`, `tubeatlas5d`;
  - `search5d.cc`, `pack5d.cc`, `scoreboard5d.cc`;
  - `icoprune_check.cc` (a floating-point check of the icosahedral prune leaves).
- `rebuild.sh` runs the whole pipeline; `*_test.cc` are unit tests (`make`).
- Lean (Noperthedron `snubdodecahedron`): `Noperthedron/SnubDodecahedron/`, plus the generic `Noperthedron/Atlas/`. Its `README.md` maps the files. Here: `../../proof/SnubDodecahedron/`, `../../proof/Pipeline/` and `../../proof/Atlas/`.
- `scripts/`: the generators of the Lean data (`update_vertices.py`: `RationalVertices.lean` and the seed count in `SolidModel.lean`; `emit_tangent_cones.py`: `GeneratedTangentCones.lean` and `TangentCones.lean`'s `supportGenerator`; `emit_wedge_cover.py`: `WedgeCoverData.lean`, about 9 min; `snub_ico_group.py`: `Pipeline/IcoGroupData.lean` and `OrbitData.lean`), run by the model stage with `MODEL_DIR` set to this directory.
