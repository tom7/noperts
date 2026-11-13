module

public import Minimality.Type21Cover
public import Minimality.UniformTilt

@[expose] public section

/-!
# Type 21: the switch surface (`FEWER-FACES-PROOFS.md` §16, parts L–M)

Labels as in `Type21Lemmas.lean`: `a, a', b, b', c, c', d = 0, 3, 4, 5, 1, 6, 2`;
`[s t] = galeD G.l G.m s t` for Gale data `G` of `O = K − 2`.  The switch surface is
`δ_014(2) = δ_014(5)` (`F.abc.f d = F.abc.f b'`): the view `u₀ = 5 − 2` along the edge `25` is
parallel to the plane `014`.  Three faces are seen edge-on: `0256` and `235` at `25`, and the far
face `014`, whose vertex `1` lies over the open far side `0 – 4`.

* **Lemma 16.28 (the view along 25)** — `type21_switch_view`: the four triple tests of the
  quadrilateral `(2, 0, 4, 3)` at `u₀` have one sign (the faces `0256`, `014`, `235` are parallel
  to `u₀`; each test is a facet value times a constant, `det3_facet_prop`), so the shadow is the
  strictly convex quadrilateral `(p, P0, P4, P3)`, counterclockwise or clockwise;
  `type21_switch_mid1`: `1 = 0 + s (4 − 0) + δ u₀` with `0 < s < 1` (from
  `δ_0256(4) < δ_0256(1)`, i.e. `|[3 1]| > |[3 4]|`) and `δ ≠ 0`;
  `type21_switch_mid6`: `6` lies over the open side from `p` to `P0`, at a nonzero offset from
  both chords `2 – 0` and `5 – 0`.
* **Lemma 16.29 (Lemma E at 25)** — `type21_switch_sep`: if `s_C(O) = +` (`CrossNorm`), `2` and
  `5` lie strictly on opposite sides of the plane `034` (the dependency `{1 ·}` of `K − 6`,
  `type21_depO2_c`, applied to that plane).
* **Theorem 16.30 (the switch surface)** — `cert_type21_switch`: on the switch surface,
  with `CrossNorm` and `|[3 1]| > |[3 4]|`, off `NoPlaneParallel`, `GenPosTie` and `NoHDNEdges`,
  `K` has a rim certificate (`CertV`): Lemma E with ties picks a robustly unimodal rim `(v, 0, 4, 3)` (`v = 2` or
  `5`), and the uniform tilt (Lemma 16.27, `isRupert_edgePair_uniform_robust`) handles the
  middles `6` (over the side at `p`) and `1` (over the far side `0 – 4`) together with the axle.
  This closes the halves `H⁻` (cap-face class, `Type21Cap.lean`) and `H⁻_c` (class (c),
  `Type21Pattern.lean`) of the switch surface; what remains at `25` is three far corners at
  one depth (in `GenPosTie`) and the horizontal double normals (`NoHDNEdges`).

Not formalized: the boundary cases of 16.30 (`s_C(O) = 0`, `|[3 1]| = |[3 4]|`: the latter is a
tie of `NoPlaneParallel`) and Lemma 16.31.

**Certificate form** (§18.2, §18.6 step 2): every theorem of the tier cover concludes a rim
certificate at a named view (`CertV`: a segment view or a view satisfying `L`, the named vertex
crossings) instead of Rupertness; no horizontal double normal is assumed.  The old statement
`isRupert_type21_facets` and the limit theorem are in `Type21Limit.lean`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

variable {L : ℝ³ → Prop}

/-- **A face parallel to the view.**  An affine `f` vanishing at `P`, `Q` with `⟪N, u⟫ = 0`:
the triple tests `det3 (Q − P) (y − P) u` are proportional to the facet values `f y`. -/
theorem det3_facet_prop {f : ℝ³ → ℝ} {N : ℝ³} (hf : ∀ y z, f y - f z = ⟪N, y - z⟫)
    {P Q u : ℝ³} (hP : f P = 0) (hQ : f Q = 0) (hu : ⟪N, u⟫ = 0) (y y' : ℝ³) :
    det3 (Q - P) (y - P) u * f y' = det3 (Q - P) (y' - P) u * f y := by
  have h1 : ⟪N, Q - P⟫ = 0 := by rw [← hf, hP, hQ, sub_self]
  have key := det3_mul_inner_eq (e := Q - P) (u := u) (w := y - P) (w' := y' - P) h1 hu
  rwa [← hf, ← hf, hP, sub_zero, sub_zero] at key

section Switch

variable {a a' b b' c c' d : ℝ³}

end Switch

end Minimality

end
