module

public import Minimality.Type08S.C2K14P

@[expose] public section


/-!
# K16 / A: ParEndN2's `Coll5` gives `⟪a-d, b-d⟫ < 0` on the slice `α1 = 1`, `⟪a-d, b-c⟫ = 0`.
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem k16_inner_frame {e1 e2 e3 : ℝ³} (hF : Fr e1 e2 e3) (x y : ℝ³) :
    ⟪x, y⟫ = ⟪x, e1⟫ * ⟪y, e1⟫ + ⟪x, e2⟫ * ⟪y, e2⟫ + ⟪x, e3⟫ * ⟪y, e3⟫ := by
  have h := inner_pc hF ⟪x, e1⟫ ⟪x, e2⟫ ⟪x, e3⟫ ⟪y, e1⟫ ⟪y, e2⟫ ⟪y, e3⟫
  simp only [pc] at h
  rw [← hF.expand x, ← hF.expand y] at h
  exact h

/-- Core: `e2 ⟂ p, q`, `⟪r, p - q⟫ = 0`, `α1 r + β1 p - q` and `p - q` collinear in the `(e1, e3)`-plane,
`det3 r p q ≠ 0`  ⟹  `α1 ⟪r,p⟫ |p-q|² = -(β1-1) (|p|²|q|² - ⟪p,q⟫²)` and the Gram determinant is positive. -/
theorem k16_rel_core {e1 e2 e3 r p q : ℝ³} (hF : Fr e1 e2 e3) {α1 β1 : ℝ} (hα1 : 0 < α1) (hβ1 : 1 < β1)
    (hdet : det3 r p q ≠ 0) (hp2 : ⟪p, e2⟫ = 0) (hq2 : ⟪q, e2⟫ = 0) (hρ : ⟪r, p - q⟫ = 0)
    (hcoll : ⟪α1 • r + β1 • p - q, e3⟫ * ⟪p - q, e1⟫ = ⟪p - q, e3⟫ * ⟪α1 • r + β1 • p - q, e1⟫) :
    α1 * (⟪r, p⟫ * ⟪p - q, p - q⟫) = -(β1 - 1) * (⟪p, p⟫ * ⟪q, q⟫ - ⟪p, q⟫ ^ 2) ∧
      0 < ⟪p, p⟫ * ⟪q, q⟫ - ⟪p, q⟫ ^ 2 := by
  have hs : ⟪r, p⟫ = ⟪r, e1⟫ * ⟪p, e1⟫ + ⟪r, e3⟫ * ⟪p, e3⟫ := by
    rw [k16_inner_frame hF r p, hp2]; ring
  have hρ' : ⟪r, e1⟫ * (⟪p, e1⟫ - ⟪q, e1⟫) + ⟪r, e3⟫ * (⟪p, e3⟫ - ⟪q, e3⟫) = 0 := by
    rw [k16_inner_frame hF r (p - q)] at hρ
    simp only [inner_sub_left, inner_sub_right, hp2, hq2] at hρ
    linarith
  have hc' : (α1 * ⟪r, e3⟫ + β1 * ⟪p, e3⟫ - ⟪q, e3⟫) * (⟪p, e1⟫ - ⟪q, e1⟫) =
      (⟪p, e3⟫ - ⟪q, e3⟫) * (α1 * ⟪r, e1⟫ + β1 * ⟪p, e1⟫ - ⟪q, e1⟫) := by
    simpa only [inner_sub_left, inner_add_left, inner_smul_left, RCLike.conj_to_real] using hcoll
  have hD : ⟪p, e1⟫ * ⟪q, e3⟫ - ⟪q, e1⟫ * ⟪p, e3⟫ ≠ 0 := by
    intro h0
    apply hdet
    have e := det3_pc hF ⟪r, e1⟫ ⟪r, e2⟫ ⟪r, e3⟫ ⟪p, e1⟫ ⟪p, e2⟫ ⟪p, e3⟫ ⟪q, e1⟫ ⟪q, e2⟫ ⟪q, e3⟫
    simp only [pc] at e
    rw [← hF.expand r, ← hF.expand p, ← hF.expand q] at e
    rw [e, hp2, hq2]; linear_combination (-⟪r, e2⟫) * h0
  set xp := ⟪p, e1⟫; set zp := ⟪p, e3⟫; set xq := ⟪q, e1⟫; set zq := ⟪q, e3⟫
  set xr := ⟪r, e1⟫; set zr := ⟪r, e3⟫
  set Δ := xp * zq - xq * zp with hΔ
  have key : α1 * ((xr * xp + zr * zp) * ((xp - xq)^2 + (zp - zq)^2)) = -(β1 - 1) * Δ^2 := by
    linear_combination (α1 * ((xp - xq) * xp + (zp - zq) * zp)) * hρ' + Δ * hc'
  have g1 : ⟪p - q, p - q⟫ = (xp - xq)^2 + (zp - zq)^2 := by
    rw [k16_inner_frame hF (p - q) (p - q)]
    simp only [inner_sub_left, hp2, hq2]; ring
  have g2 : ⟪p, p⟫ * ⟪q, q⟫ - ⟪p, q⟫ ^ 2 = Δ ^ 2 := by
    rw [k16_inner_frame hF p p, k16_inner_frame hF q q, k16_inner_frame hF p q, hp2, hq2]; ring
  rw [g1, g2, hs]
  exact ⟨key, by positivity⟩

theorem k16_s_neg {e1 e2 e3 r p q : ℝ³} (hF : Fr e1 e2 e3) {α1 β1 : ℝ} (hα1 : 0 < α1) (hβ1 : 1 < β1)
    (hdet : det3 r p q ≠ 0) (hp2 : ⟪p, e2⟫ = 0) (hq2 : ⟪q, e2⟫ = 0) (hρ : ⟪r, p - q⟫ = 0)
    (hcoll : ⟪α1 • r + β1 • p - q, e3⟫ * ⟪p - q, e1⟫ = ⟪p - q, e3⟫ * ⟪α1 • r + β1 • p - q, e1⟫) :
    ⟪r, p⟫ < 0 := by
  obtain ⟨h1, h2⟩ := k16_rel_core hF hα1 hβ1 hdet hp2 hq2 hρ hcoll
  by_contra hneg
  push Not at hneg
  have : 0 ≤ α1 * (⟪r, p⟫ * ⟪p - q, p - q⟫) :=
    mul_nonneg hα1.le (mul_nonneg hneg (real_inner_self_nonneg))
  nlinarith

end C2
end Type08Sp
end Minimality
