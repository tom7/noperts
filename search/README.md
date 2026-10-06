# The deltoidal hexecontahedron is a Nopert

**Status (2026-10-06): verified.** `constructDeltoidalHexecontahedron` checked every certificate (3 caps,
250 tie nodes, the view cover, 39 tube tables, 36.2 M chart-0 rows) in 3 h 05 min on 64 cores (peak 30 GB) and
printed `instantiated: no deltoidal hexecontahedron is Rupert`. A from-scratch reproduction with `rebuild.sh`
is still to be done.

A polyhedron is *Rupert* if a hole can be cut through it through which a congruent copy can pass, and a *Nopert*
if it is not Rupert (Lean: `¬ IsRupert`). This repository, together with the Lean formalization on the
`deltoidalhexecontahedron` branch of [Noperthedron](https://github.com/jcreedcmu/Noperthedron), proves that
**every deltoidal hexecontahedron is a Nopert**:

```lean
-- Noperthedron/PentagonalHexecontahedron/DHTies.lean
theorem deltoidalHexecontahedron_not_rupert_of_checks
    (htables : ∀ P : IModel, P.CentrallySymmetric →
      AtlasProjectiveSolutionTree.ExactClaims P.toC5.polyhedron.hull → ¬ IsRupert P.toC5.verts)
    (caps : Array CapCert) (hcaps : capsCheck caps = true)
    (ties : TieCerts) (hties : tiesCheck ties = true) :
    ∀ V : Finset ℝ³, IsDeltoidalHexecontahedron V → ¬ IsRupert V
```

- `IsDeltoidalHexecontahedron V` (`DHStatement.lean`): V is the image, under a similarity (an orthogonal map,
  possibly a reflection, a positive scale and a translation), of David McCooey's 62 vertices: the cyclic
  permutations with all sign changes of (0, 0, √5), (0, C₁, C₇), (C₃, 0, C₆), (C₀, C₂, C₅), (C₄, C₄, C₄), with
  C₀ = (5 − √5)/4, C₁ = (15 + √5)/22, C₂ = √5/2, C₃ = (5 + √5)/6, C₄ = (5 + 4√5)/11, C₅ = (5 + √5)/4,
  C₆ = (5 + 3√5)/6, C₇ = (25 + 9√5)/22.
- The three hypotheses are what the executable `constructDeltoidalHexecontahedron` checks natively: the solution
  tables (`htables`), the three cap certificates (`hcaps`) and the tie-tube certificates (`hties`); the executable
  then instantiates the theorem. The trust model is that of `native_decide`: Lean's kernel plus the compiled
  evaluation of the checkers. The statement's own facts (the frame, the 70 vertex slots over
  K = ℚ(√5, sin 72°), the orbits and the closeness to the rational model) are decided by the kernel.

## Why the deltoidal hexecontahedron needs more than the earlier solids

The DH lies exactly on the boundary of Rupert-ness. Folding its kites slightly (moving the twelve 5-fold vertices
out by 0.1%) gives a Rupert polyhedron (`dh_boundary.py` checks a passage in 50-digit arithmetic); the exact DH has
clearance exactly 0 at those poses. So the earlier pipeline's statement, "every model within 6·10⁻¹⁶ of the
rational model is a Nopert", is false here, and the proof uses the exact solid wherever such ties occur:

- **Mirror ties and the half-turn reduction.** For a mirror σ of K and any view v, σ_v σ maps K's shadow onto
  itself. Since −1 ∈ Ih, the relative rotation can be reduced modulo R ↦ H_v R g (H_v the half-turn about the view,
  g ∈ I): the *half-turn cell* (Lean `HalfTurnReduce`, `HalfTurnPose`; rows `Row.halfTurnPrune`, pack tag 14).
- **Pinning ties.** For x = ux = (cos 18°, sin 18°, 2)/√5 and its images, the plane x⊥ holds antipodal pairs of
  5-fold and 2-fold vertices; for views u in a wedge from x, R = H_u H_x is an exact tie. *Tie tubes*
  (`tietube.cc`; Lean `TieCheck`, `AtlasTiePrune`, `TieRow`; rows `Row.tieLeaf`, tag 15) certify, with the exact
  solid, that no rotation within ρ of a tie is a passage.
- **Caps** at the 2-fold view u0 and at ux, where the identity and the ties meet: weighted blow-up charts in
  (view offset, Cayley vector) with exact Bernstein bounds over K (`capcert.cc`; Lean `CapChart` … `CapCert`,
  `CapRow`; rows `Row.capLeaf`, tag 16). At ux the tie locus needs a second blow-up (the *tie scheme*,
  `--tie_charts`; Lean `tie_decomp`, `realize_tie`).

## Data and reproduction

The certificate data lives outside the repository (about 20 GB): cap certificates (`capcert --export`),
tie certificates (`tietube --export_dir`, `dh_tie_lean.py`), tube packs (`export_codetrees_pack`) and 5D packs
(`pack5d --per_code --tie_nodes`). Then

```
constructDeltoidalHexecontahedron tubepacks/manifest.txt packs certs tie_lean
```

checks caps, ties and tables and prints `instantiated: no deltoidal hexecontahedron is Rupert`.
`./rebuild.sh --from model --work DIR` runs the whole pipeline (stages model, tube, tubepack, caps, ties, search,
pack, verify; `--dry_run` prints the commands).

## Code map (DH-specific)

- Model and exact solid: `dh_model.py` (`dh_model.txt`), `dh_exact.py` (`dh_exact.txt`, over K), `kfield.py`.
- Half-turn prune: `exact5d::HalfTurnPruneValid`, `ico_group.py`, `halfturn_check.cc`.
- Caps: `capcert.cc`, `dh_caps.py`, `dh_cap_lean.py` (Lean `DHCapData`), `merge_caps_cert.py`, `capleaf_check.cc`.
- Ties: `dh_tie_data.py` (`dh_tie_data.txt`, `tie_normals.h`), `tietube.cc`, `tieatlas5d`, `dh_tie_lean.py`
  (Lean `DHTieData`), `tieviz.cc` (renderings).
- 5D search: as for the pentagonal hexecontahedron, plus cap and tie leaves; `tufix.cc` (tube leaves at cap nodes).
- Lean (Noperthedron `deltoidalhexecontahedron`, `Noperthedron/PentagonalHexecontahedron/`): `DHStatement`,
  `DHCaps`, `DHTies`, `DHChecks`, `DHDecode`, the cap and tie modules above, and `constructDeltoidalHexecontahedron`.

The working log `notes/T.md` records how this proof came to be.
