module

public import Minimality.Type08S.P2SCXm

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# Lemma SC-X, open-side case: the foot `x̄` lies in the open top side `(ḡ, r̄)` (sp08f §3, "Open side")

Criterion (R) of Lemma SC (`lemmaSC_s`) with `Φ = σ(σ_line(X) - z) - μ` and `χ` separating `{f, r}` from `{g, x}`.
Uses `x ∉ Π'` (`hPi`, Lemma D: `σ(L) - z_f > 0`).
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

theorem open_params {a E qs c : ℝ} (ha : 0 < a) (hE : 0 < E) (hqs : 0 < qs) :
    ∃ l μ : ℝ, 0 < l ∧ 0 < μ ∧ μ < a ∧ μ < E ∧ μ ≤ l * qs ∧ 0 ≤ l * c + a - μ := by
  have hc : 0 < |c| + 1 := by positivity
  set l := a / (2 * (|c| + 1)) with hl
  have hlpos : 0 < l := by rw [hl]; positivity
  have hlc : l * (|c| + 1) = a / 2 := by rw [hl]; field_simp
  set μ := min (min a E / 2) (l * qs) with hμ
  have h1 : μ ≤ min a E / 2 := min_le_left _ _
  have h2 : μ ≤ l * qs := min_le_right _ _
  have hmin : 0 < min a E := lt_min ha hE
  have h3 : min a E ≤ a := min_le_left _ _
  have h4 : min a E ≤ E := min_le_right _ _
  refine ⟨l, μ, hlpos, lt_min (by positivity) (mul_pos hlpos hqs), by linarith, by linarith, h2, ?_⟩
  have := neg_abs_le c
  nlinarith [mul_pos hlpos hc, abs_nonneg c, mul_nonneg hlpos.le (abs_nonneg c)]

/-- **SC-X, open side.**  `x̄ = (0, z_x)` lies on the open segment `(ḡ, r̄)` of the top side
(`Yg = Yr`, `Xg < 0 < Xr`, `hline`: `ḡ, r̄, x̄` collinear in the `(λ, z)`-plane).  Robustness: `f`
on `r`'s side of `z_x`.  `hPi`: `x ∉ Π'`. -/
theorem lemmaSCX_open (hF : Fr e1 e2 e3) (o : ℝ³) (E : Finset ℝ³)
    {σ L zp zx zf Xr Yr zr Xg Yg zg : ℝ}
    (hL : 0 < L) (hzx : 0 < σ * (zx - zp)) (hYr : 0 < Yr) (hYrg : Yg = Yr)
    (hXg : Xg < 0) (hXr : 0 < Xr) (hline : (zg - zx) * Xr = (zr - zx) * Xg)
    (hrob : 0 < (zf - zx) * (zr - zx))
    (hPi : 0 < σ * ((zr - zx) * L - (zf - zx) * Xr))
    (hE : ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E)
      (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * s) (-σ) 0) y) :
    IsRupert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E) := by
  have hur : zr - zx ≠ 0 := fun h => by rw [h] at hrob; simp at hrob
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m * Xr = zr - zx := ⟨(zr - zx) / Xr, by field_simp⟩
  have hug : zg - zx = m * Xg := by
    apply mul_right_cancel₀ hXr.ne'
    linear_combination hline - Xg * hm
  have hq : 0 < (zf - zx) / (zr - zx) := by
    have : (zf - zx) / (zr - zx) = ((zf - zx) * (zr - zx)) / ((zr - zx) * (zr - zx)) := by
      field_simp
    rw [this]; exact div_pos hrob (mul_self_pos.2 hur)
  obtain ⟨qs, hqspos, hqs1, hqs2⟩ : ∃ qs : ℝ, 0 < qs ∧ qs ≤ 1 / 2 ∧ qs ≤ (zf - zx) / (zr - zx) / 2 :=
    ⟨min (1 / 2) ((zf - zx) / (zr - zx) / 2), lt_min (by norm_num) (by positivity),
      min_le_left _ _, min_le_right _ _⟩
  have hqg : (zg - zx) / (zr - zx) < 0 := by
    rw [hug]
    have : m * Xg / (zr - zx) = (Xg / Xr) := by
      field_simp; linear_combination Xg * hm
    rw [this]; exact div_neg_of_neg_of_pos hXg hXr
  have hmL : σ * ((zr - zx) * L - (zf - zx) * Xr) / Xr = σ * (m * L - (zf - zx)) := by
    field_simp; linear_combination (-σ * L) * hm
  obtain ⟨l, μ, hl, hμ, hμa, hμE, hμq, hμp⟩ := open_params (a := σ * (zx - zp))
    (E := σ * ((zr - zx) * L - (zf - zx) * Xr) / Xr) (qs := qs) (c := qs + (zx - zp) / (zr - zx))
    hzx (div_pos hPi hXr) hqspos
  rw [hmL] at hμE
  have hchi : ∀ z : ℝ, l * (qs - (z - zx) / (zr - zx)) =
      (l * (qs + zx / (zr - zx))) + (-l / (zr - zx)) * z := by
    intro z; field_simp; ring
  have hx0 : (zx - zx) / (zr - zx) = 0 := by simp
  have hr1 : (zr - zx) / (zr - zx) = 1 := div_self hur
  have hmXr : σ * m * Xr = σ * (zr - zx) := by rw [mul_assoc, hm]
  have hmXg : σ * m * Xg = σ * (zg - zx) := by rw [hug]; ring
  refine lemmaSC_s hF o E (σ := σ) (φ0 := σ * zx - μ) (φ1 := -σ) (θ := σ * m)
    (χ0 := l * (qs + zx / (zr - zx))) (χ1 := -l / (zr - zx)) hL hzx hYr hYrg
    (by linarith) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hE
  · rw [← hchi]; exact mul_neg_of_pos_of_neg hl (by linarith)
  · rw [← hchi, hr1]; exact mul_neg_of_pos_of_neg hl (by linarith)
  · rw [← hchi]; exact mul_pos hl (by linarith)
  · rw [← hchi, hx0]; exact mul_pos hl (by linarith)
  · linarith
  · linarith
  · linarith
  · linarith
  · rw [← hchi, hx0]; nlinarith
  · have : (zp - zx) / (zr - zx) = -((zx - zp) / (zr - zx)) := by ring
    rw [← hchi, this]; nlinarith

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.lemmaSCX_open
