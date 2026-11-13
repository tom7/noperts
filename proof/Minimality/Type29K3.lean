module

public import Minimality.Type29K4

@[expose] public section

/-!
# Type 29, class K3 (`FEWER-FACES-PROOFS.md` §21.2)

In the normal coordinates of `NF29` class K3a is `a2 < 0 < b0`, `V > 0` (K3b is its `σ`-image).
On `R_G` every shape has a metric-free certificate (Theorem 21.22).  With
`R = Π ∩ {θ > α, f ≥ F4}`:

* Lemma 21.12 (`NF29.k3_facts`): `h0 < 1`, `G4 > 0 > G5`, `F4 > F5`, `h2 > h0`.
* Theorem 21.13 (`6 ∉ R`, `NF29.isRupert_k3_notR`): Lemma E at the edges `56`, `14`, `46` of `K`
  (`NF29.isRupert_k3_C56`, `_C14`, `_C46`; Corollary 14.1, `isRupert_edgePairσ`).
* Theorem 21.15 (i) (`h2 < 1`, `NF29.isRupert_k3_i`): the pair `P14 = {T1, T2}`
  (`NF29.isRupert_k3_P14`, Corollary 13.3 in general form, `not_both_depthSep_gen`) or a
  triangular `T2` (`_T2b`, `_T2c`); (ii) `R = ∅` for `h2 ≥ 1 + A2` (`NF29.k3_R_empty`).
* `1 < h2 < 1 + A2` (`NF29.isRupert_k3_open`): (iii) `h0 > F5`; (iv) P11 (`_P11`); (v) the planar
  `T3` (`_T3p`, `NF29.planar_unimodal`); Lemma 21.16 (`_X`), Lemma 21.17 (the planar `Y1`,
  `_Y1p`), Proposition 21.19 (P13, `_P13`), Lemma 21.20 with Proposition 21.21 (Y′, `_Yp`, the
  pattern argument in reals `k3_Y2_core`).
* Theorem 21.22: `NF29.isRupert_K3a` (special positions and genericity in `K3Gen`) and
  `NF29.isRupert_K3b`.

The views are `NF29.vT1`, `vT2`, `vT3`, `vY1` (vertex crossings) and the edges `5 − 0`, `6 − 4`.
Derived facts of each region (21.14, 21.18) are proved inline by explicit products, with a
multiplier where the paper divides (`pos_of_mul_pos_r`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Minimality

open scoped RealInnerProductSpace
open Finset

/-- **Corollary 13.3, two tests** (general form): two 4-corner rims whose diagonals meet along
both views cannot both be depth-separated when the four determinants have a negative product. -/
theorem not_both_depthSep_gen {d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ u v : ℝ³}
    (h1 : DepthSep d₀ d₁ e₀ e₁ u) (h2 : DepthSep f₀ f₁ g₀ g₁ v)
    (m1u : SegMeet d₀ d₁ e₀ e₁ u) (m1v : SegMeet d₀ d₁ e₀ e₁ v)
    (m2v : SegMeet f₀ f₁ g₀ g₁ v) (m2u : SegMeet f₀ f₁ g₀ g₁ u)
    (hdet : det3 u (d₁ - d₀) (e₁ - e₀) * det3 v (d₁ - d₀) (e₁ - e₀) *
      (det3 u (f₁ - f₀) (g₁ - g₀) * det3 v (f₁ - f₀) (g₁ - g₀)) < 0) : False := by
  obtain ⟨A, hne⟩ := depthSep_det_sign (a' := d₀) (a := d₁) (b := e₀) (b' := e₁) h1 m1u m1v
  obtain ⟨B, -⟩ := depthSep_det_sign (a' := f₀) (a := f₁) (b := g₀) (b' := g₁) h2 m2v m2u
  rw [real_inner_comm u v] at B
  have hsq : 0 < ⟪u, v⟫ * ⟪u, v⟫ := mul_self_pos.mpr hne
  have := mul_nonneg A B
  have e : ⟪u, v⟫ * (det3 u (d₁ - d₀) (e₁ - e₀) * det3 v (d₁ - d₀) (e₁ - e₀)) *
      (⟪u, v⟫ * (det3 v (f₁ - f₀) (g₁ - g₀) * det3 u (f₁ - f₀) (g₁ - g₀))) =
      (⟪u, v⟫ * ⟪u, v⟫) * (det3 u (d₁ - d₀) (e₁ - e₀) * det3 v (d₁ - d₀) (e₁ - e₀) *
        (det3 u (f₁ - f₀) (g₁ - g₀) * det3 v (f₁ - f₀) (g₁ - g₀))) := by ring
  rw [e] at this
  linarith [mul_neg_of_pos_of_neg hsq hdet]

variable {x : Fin 7 → ℝ³}

/-- The view of `T2 = 1456/234`: `u2 = (κ, B2, 0)`, `κ = 1 − h2 − a2`, along `aff 234 ∩ H`. -/
noncomputable def NF29.vT2 (N : NF29 x) : ℝ³ :=
  nfV N.E₁ N.E₂ N.E₃ (1 - N.h2 - N.a2) (-N.b2) 0

end Minimality

end
