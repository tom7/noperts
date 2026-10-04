# Nopert #231 is not Rupert

A convex polyhedron is *Rupert* if a hole can be cut through it through which a congruent copy can pass. Nopert #231 is a convex polyhedron with 20 vertices and 27 faces (2 pentagons, 20 triangles and 5 planar quadrilaterals) and fivefold rotational symmetry about the z axis. This repository, together with the Lean formalization on the `nopert231` branch of [Noperthedron](https://github.com/jcreedcmu/Noperthedron), proves that it is not Rupert.

## What is proved

The executable `constructNopert231` (Noperthedron, `constructNopert231.lean`) checks the certificate data and constructs a value of type

```lean
∀ P : C5Model, ¬ IsRupert P.verts
```

and instantiates it:

```lean
¬ IsRupert exactVerts            -- the exact model
¬ IsRupert Ideal231.model.verts  -- idealized #231
```

- `IsRupert` is the Noperthedron project's statement of the Rupert property (`Noperthedron/MainTheorem.lean`, Mathlib only).
- `C5Model` (`Noperthedron/Nopert231/Vertices.lean`) is any polyhedron made of four real seed vertices rotated by 2πk/5 about z (k = 0..4), with every vertex within `modelErrorQ` = 6·10⁻¹⁶ of the fixed rational vertices `rationalVertices`.
- `exactVerts` rotates the rational seeds exactly (`exactModel`, `TightApproximation.lean`). Its quads are planar only to about 2·10⁻¹⁶.
- `Ideal231.model` is idealized #231: exact fivefold symmetry and exactly planar quads (`Ideal231.quad_planar`). Its closeness to the rational vertices (about 4.1·10⁻¹⁶) is decided by the kernel.

**Trust model.** The proof is not a theorem in an `.olean`. It is a value built by a native program:
- the kernel proves the bridge `not_rupert_of_valid_tables` (valid certificate tables ⇒ ¬ IsRupert), the wedge cover (`codeTriangles_cover`, by `decide +kernel`), the closeness of the models and the symmetry reductions;
- the certificate tables themselves are checked by compiled Lean code (`Table.Valid` evaluated natively, as `native_decide` does), and the program carries the resulting proofs into the final proposition.

So the trusted base is Lean's kernel plus the compiled evaluation of the checkers: the same trust as `native_decide` (`Lean.ofReduceBool`). A few small fixed tables (chart 3, the tangent cones) use `native_decide` directly.

The verifier ends with:

```
constructed proof: no C5Model (fivefold-symmetric polyhedron within 6e-16 of the rational vertices) is Rupert
instantiated: the exact model (exactVerts) and idealized #231 are not Rupert
```

## Reproducing the proof

Prerequisites:
- this repository, with `../cc-lib`, `../ruperts`, `../codec` and `../sqlite` beside it (as for the other tom7 projects);
- clang with C++23, and GMP;
- a checkout of Noperthedron's `nopert231` branch at `../Noperthedron`, with its Lean toolchain (elan/lake).

```
./rebuild.sh --work /path/to/work
```

`rebuild.sh` runs these stages. Each is restartable (`--from STAGE`, `--only STAGE`; `--dry_run` prints the commands). Times were measured on a 64-core machine, partly while it was shared with other jobs.

| stage | what | time |
|---|---|---|
| model | `codebdd` computes the rational model, the face-visibility codes and their triangles; the Lean data (vertices, tangent cones, the wedge cover) is regenerated from them and Lean is rebuilt. Only on request (`--from model`), since it rewrites committed files. | under a second for `codebdd`; a few minutes for the scripts; then the Lean build |
| tube | `tubecode` and `tuberefine` build the identity tube, one tree per code | ~13 min (36 threads) |
| tubepack | `export_codetrees_pack`: the tube trees become Lean packs and a manifest | ~1 min |
| search | `search5d`: the 5D search over (view, relative rotation), charts 0-2 | ~1 h (40 threads) |
| pack | `pack5d --per_code`: per-code certificate packs | about 1 h |
| verify | `constructNopert231` on the tube packs and the per-code packs | ~3 h |

The build step builds the C++ tools and the Lean executables first. `codebdd.json` (the code database, 0.4 s to compute) is not committed; when it is missing, `rebuild.sh` regenerates it and checks that the vertex files it writes equal the committed `model_vertices.*` byte for byte.

Peak memory is about 30 GB (the Lean verifier); `--mem_gb` caps every stage. `tubecode`, `tuberefine`, `codebdd` and `pack5d` are deterministic (independent of the thread count). `search5d` is not, so a fresh search gives different but equally checkable packs. To re-check existing data, point `--work` at it and start from `pack` or `verify`.

**Unit tests.** `make` builds them and `make test` runs them. Tests that need generated data skip cleanly when it is absent; these environment variables point them at it:
- `CODEBDD_JSON` (default `codebdd.json`): contacts5d, cert5d, exact5d, solve5d, tubeatlas5d;
- `EXACT5D_GOLDEN` (default `../Noperthedron/.lake/build/bin/exact5d_golden`, built by `lake build exact5d_golden`): exact5d, which compares every exact check with Lean;
- `TREES_DIR` (default `trees_r2`; e.g. `work/trees_r2` after the tube stage): solve5d, tubeatlas5d;
- `TUBE_MANIFEST` (optional, e.g. `work/tube_packs/manifest.txt`): tubeatlas5d compares the tree radii with the exported packs.

## How the proof works

### The polyhedron and its rational model

`nopert231_root.txt` gives the four seed vertices (the `rootK` lines; the `params` line and comments record how the optimizer that produced it was called). Numerically (dense sampling of the views), its first-order rigidity margin is positive everywhere: no small rotation from the identity moves the inner shadow strictly inside the outer one to first order. The smallest margin, about 1.8·10⁻⁴, is at the *canyon*: views near the plane of a quad, on the side where two of its vertices are eclipsed. This is where the proof works hardest.

The certificates are checked against fixed rational vertices, not the irrational solid (`codebdd`, `GenerateBestPossibleRationalVertices`):
- The seeds are reordered to the Lean frame (seed 0 = top cap) and scaled so that every vertex has norm slightly below 1.
- Each seed is rotated by 2πk/5 in double precision and rounded to a multiple of 2⁻⁵². The caps get exactly equal heights.
- The five quads are made exactly planar in ℚ: the seed-1 vertex of each quad is projected onto the plane of the other three (these five vertices have ~260-bit denominators).
- `codebdd` tries slightly different overall scales and keeps the first whose rational vertices are within 3.6·10⁻¹⁶ of the exact rotations of the rational seeds (Lean needs 4·10⁻¹⁶).

The outputs are `model_vertices.{h,json,lean}` (committed; the C++ tools compile in `model_vertices.h`) and `codebdd.json`.

### Symmetry reductions

A pose is an outer view direction plus a relative rotation R between the two copies. Lean reduces both before any certificate is checked:
1. **The view.** Reversing the viewing direction reflects both shadows, so the view may point into the upper hemisphere. The fivefold rotation reduces its azimuth to [0, 2π/5]. The resulting wedge lies in the rational projective triangle (1,0,0), (10/41, 31/41, 0), (0,0,1) (`upperWedgeTriangle`).
2. **The relative rotation.** Composing the inner copy with a fivefold symmetry does not change its shadow, so R may be the representative of maximal trace (the identity's Dirichlet cell; `FundamentalDomain.lean`). R is written in one of four Cayley charts (`CayleyAtlas.lean`); in each chart the trace advantage over the two adjacent fivefold rotations is a quadratic, which the search uses to prune boxes outside the cell (`AtlasFundamentalPrune.lean`). Chart 3 is empty, and a fixed four-row table proves it (`FundamentalChart3.lean`).

### Codes

`codebdd` splits the view triangle into cells where the silhouette's combinatorics (which faces are visible: the face-visibility *code*) is constant: 27 facet planes, 77 codes, 153 projective triangles. Lean checks that the code triangles cover the view triangle with a decision tree over half-planes, generated by `emit_wedge_cover.py` and decided by the kernel (`WedgeCover.lean`, `WedgeCoverData.lean`; 2,143 nodes).

### The identity tube

Near R = identity no finite subdivision can work, since the two shadows coincide there. Instead, for each code triangle `tubecode` builds a quadtree of view sub-triangles. Each leaf carries a *Tag 1 cage*: four axis certificates, each a balanced triple of silhouette contacts, whose normalized centers span a tetrahedron containing the octahedron ±(7/4)(c + δ)eₖ, where δ bounds how far the centers move over the leaf triangle. The cage proves that no relative rotation within the tube radius r of the identity (r²(1 + c²) ≤ 4c²) gives a translated Rupert pose for any view in the leaf. Every certificate is audited in exact arithmetic with the same conditions as Lean's `Box.ViewValid`. `tuberefine` then subdivides leaves until every radius is at least the goal 1/50000 (2·10⁻⁵), so that the 5D search can stop there. `export_codetrees_pack` writes one Lean pack per code triangle, with each node's certified radius.

### The 5D search

`search5d` covers (view triangle × Cayley box) for each code triangle and chart 0-2, splitting the box or the view (the comparison scales the view diameter by the rotation's size, `--view_scale`). Its leaves are:
- balanced-triple certificates (projective global, and convex mixtures of them), checked exactly by the C++ port of Lean's checks (`exact5d`) before they are written;
- tube leaves (`tu`): the box lies within the tube radius of the identity, citing a node of the code's tube tree;
- prunes: outside the rotation radius, or outside the fivefold fundamental cell.

The search is journaled and restartable; deferred leaves are retried in the same run. A full run took 61 minutes (40 threads): 21.2M nodes, 12.7M leaves, none deferred.

### Packs and checking

`pack5d --per_code` turns the journals into Lean packs, one per code triangle and chart (chart 0 has about 25M rows). `constructNopert231` decodes them behind a `codeRoot` row (decoding is untrusted: the decoded table is what gets checked), checks every row of every chart and every tube table in parallel native code, and applies the kernel-proved soundness theorems (`AtlasProjectiveSolutionTree`, `IdentityTube.not_translated_rupert_of_tables`, `IsNotRupert.not_rupert_of_valid_tables`). `check_global_rows` checks individual per-code packs (bookkeeping for `scoreboard5d`), and `validate_code_pack` / `check_identity_tube` check the tube packs on their own.

## Code map

- `nopert231_root.txt`: the polyhedron's seed vertices.
- Model and codes:
  - `codebdd.cc`: the rational model (`model_vertices.*`) and the code database (`codebdd.json`);
  - `model.{h,cc}`: the vertices (double and exact) for the other tools.
- Identity tube:
  - `tube.{h,cc}`: silhouette contacts, axis certificates and cage synthesis;
  - `tubecert.cc` (included by `tubecode.cc`): candidate generation and exact audits for one view triangle;
  - `tubetree.{h,cc}`: tube trees and their JSON format;
  - `tubecode.cc`, `tuberefine.cc`, `export_codetrees_pack.cc`.
- 5D search and packing:
  - `exact5d` (the exact checks, mirroring Lean), `geom5d` (view triangles and Cayley boxes), `contacts5d`, `bounds5d`, `cert5d`, `lp5d`, `rows5d`, `solve5d`, `tubeatlas5d` (the tube as seen by the search);
  - `search5d.cc`, `pack5d.cc`, `scoreboard5d.cc` (per-job status from the journals and packs).
- `rebuild.sh` runs the whole pipeline; `*_test.cc` are the unit tests.
- Lean (Noperthedron `nopert231`): `Noperthedron/Nopert231/` and the generic `Noperthedron/Atlas/`, plus the executables `constructNopert231`, `validate_code_pack`, `check_identity_tube`, `check_global_rows` and `exact5d_golden`. `Noperthedron/Nopert231/README.md` maps the files.

See `notes/HISTORY.md` for how this code came to be.
