> **In this repository** the entry point is `../Nopert231.lean` (headline
> `Nopert231.isNopert_of_certificatesValid`; see `../../nopert231.md`). The text
> below is adapted from the README of Noperthedron's `nopert231` branch
> (0c83e4ba), whose names differ: `Noperthedron/Nopert231/` is
> `proof/Nopert231/` here (namespace `Nopert231`), `Noperthedron/Atlas/` is
> `proof/Atlas/` (which also holds `QuadCoverTree` and `QuadraticBernstein`), and
> the generator scripts are in `search/nopert231/scripts/`. No `native_decide`
> is used here: chart 3 and the tangent cones are checked by the kernel
> (`table_valid_kernel`). Since 2026-10-10 most of the branch's pipeline is the
> shared `proof/Pipeline/` (see "Files" below, which describes this
> repository's layout); the check functions are the same.

# Candidate #231 is a nopert

This directory, with the shared `proof/Atlas/` and `proof/Pipeline/` libraries, formalizes the proof that candidate #231 is a nopert (not Rupert, `¬ IsRupert`). Candidate #231 is a convex polyhedron with 20 vertices and 27 faces (2 pentagons, 20 triangles, 5 planar quadrilaterals) and fivefold symmetry about the z axis. The certificate data is produced by the C++ pipeline in `search/nopert231/`; its `README.md` explains how the proof works and how to rebuild it with `rebuild.sh`.

## The main result

The executable `constructNopert231 <tube manifest.txt> <chart directory>` (`constructNopert231.lean`) decodes and checks all certificate tables (with the checkers of `NativeExecutable.lean`), which establishes `CertificatesValid`, and so (`isNopert_of_certificatesValid`, in `../Nopert231.lean`)

```lean
∀ P : C5Model, IsNopert P.verts
```

and in particular

```lean
IsNopert exactVerts            -- isNopert_exactVerts_of_certificatesValid
IsNopert Ideal231.model.verts  -- idealized #231, exactly planar quads
```

- `IsRupert` is the upstream statement of the Rupert property (`proof/MainTheorem.lean`); `IsNopert` (`proof/Nopert.lean`) adds that the vertices are not coplanar.
- `C5Model` (`SolidModel.lean`): four real seeds rotated by 2πk/5 about z, with every vertex within `modelErrorQ` = 6·10⁻¹⁶ of the rational vertices `rationalVertices`.
- Trust: the kernel proves the bridge from valid tables to `¬ IsRupert` and every geometric lemma. The tables are checked by compiled code (`Table.Valid` decided natively, the same trust as `native_decide`), and the program carries the resulting proofs into the final value. It prints `constructed proof: no C5Model ... is Rupert` and then `instantiated: IsNopert P.verts for every C5Model P, ...`.

## Files

The certificate pipeline is the shared `../Pipeline/` (namespace
`Noperts.Pipeline`), generic over the solid's model. This directory holds what
is particular to candidate #231:

Model and approximation:
- `Vertices.lean` (data; generated bodies, see below): `rationalVertices` and
  `seedVertex`, with a table that compiled code reads instead of the literal.
- `SolidModel.lean`: the kernel-checked facts about the data and the scoped
  instance `fivefoldSolid : FivefoldSolid` (`Pipeline/FivefoldModel.lean`:
  rotations by 2πk/5 about z, rational Taylor symmetry matrices within κ/2,
  the rational vertices within 6·10⁻¹⁶ of the exactly rotated seeds via
  17-digit rotations); `C5Model` is the pipeline's `CyclicModel` for this
  model.
- `Ideal231.lean`: idealized #231 (seed 1's height chosen so that the quads
  are exactly planar, `quad_planar`) as a `C5Model`, with its closeness decided
  by the kernel.
- `SparseSupport.lean` and `GeneratedTangentCones.lean` (generated): the
  tangent-cone generators of each vertex and the kernel-checked table showing
  that every other vertex lies in their cone; `SparseViewCheck.lean` gives them
  to the shared sparse support check (`Pipeline/SparseSupport.lean`), which
  checks support against at most seven vertices.
- `WedgeCover.lean`, `WedgeCoverData.lean` (generated): `codeTriangles_cover`,
  the code triangles cover the upper wedge (decision tree checked by
  `decide +kernel`; the checker is `Pipeline/WedgeCover.lean`).

The top layer, which is particular to #231's fivefold reduction (the
icosahedral solids share another one in `Pipeline/`):
- `AtlasProjectiveSolutionTree.lean`: the 5D tables (rows: code root, view and
  Cayley splits, relaxed regions, certificates, tube citations, fivefold
  fundamental-domain prunes) and their soundness, over the domain of
  `Pipeline/FivefoldReduction.lean` (azimuths reduced modulo 2π/5, upper view,
  max-trace cell of C5, four Cayley charts).
- `FundamentalChart3.lean`: the fixed four-row table excluding chart 3.
- `IsNotRupert.lean`: `not_rupert_of_valid_tables`, from four valid chart
  tables to `¬ IsRupert P.verts`.
- `PackedSolutionTree.lean`: the decoder for the chart packs (untrusted: the
  decoded tables are what is checked); the tube packs use
  `Pipeline/PackedLocalViewTree.lean`.
- `NativeExecutable.lean`: the parallel native checker.

From the shared pipeline: the symmetry, tightening and Cayley atlas
(`Symmetry`, `FivefoldSymmetry`, `Tightening`, `CayleyAtlas`, `AtlasPose`,
`AtlasInterval`, `AtlasQuadratic`, `FundamentalDomain`,
`AtlasFundamentalPrune`), projective view triangles (`AtlasProjectiveView`),
the certificates (`Certificate`, `LocalCertificate`, `SymmetryLocal`,
`AtlasLocalCertificate`, `AtlasEdgeCertificate`,
`AtlasProjective{Edge,Global,MixedGlobal,Local,Annular}Certificate`,
`AtlasProjective{Global,Local}Rigidity`) and the identity-tube tables
(`AtlasProjectiveLocalViewTree`, `SparseLocalViewTree`,
`PackedLocalViewTree`).

`Atlas/` holds the polyhedron-independent pieces: Cayley poses and quadratics, projective view triangles, local rigidity, and the Bernstein, edge and local certificate arithmetic.

## Generated files

`Vertices.lean` (the `rationalVertices` and `seedVertex` bodies), `GeneratedTangentCones.lean` and `WedgeCoverData.lean` are written by `scripts/update_vertices.py`, `scripts/emit_tangent_cones.py` and `scripts/emit_wedge_cover.py` (in `search/nopert231/`) from the C++ pipeline's `codebdd` output. The scripts find it through `--model_dir DIR` or `$MODEL_DIR` (which the C++ `rebuild.sh` sets); `scripts/model_vertices.py` loads the vertices. `update_vertices.py` rewrites only the two bodies; the rest of `Vertices.lean` is written by hand.
