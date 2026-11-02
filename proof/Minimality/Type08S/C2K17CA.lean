module

public import Minimality.Type08S.C2K16R

@[expose] public section


/-!
# K17C / P3A: `Coll5` at `β1 = 1` forces `⟪a-d, b-d⟫ = 0 = ⟪a-d, c-d⟫` (S3.1).
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

/-- `k16_rel_core` without `1 < β1`. -/
theorem k17c_rel_core {e1 e2 e3 r p q : ℝ³} (hF : Fr e1 e2 e3) {α1 β1 : ℝ}
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

theorem k17c_n2_rel {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hκ : det3 (c - b) (b' - b) (c' - b) = 0) (hN2 : ParEndN2 a a' b b' c c')
    (hρ : ⟪a - d, b - c⟫ = 0) {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0) (hc' : c' = d + α1 • (a - d) + β1 • (b - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d)) (hγ6 : 0 < γ6)
    (h3 : 1 < β6 + γ6) : K16Rel a b c d α1 β1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, e1, e2, e3, κ, hF, hκ0, hxe, hbe2, hL, hr, hYY, hcoll, -⟩ :=
    p0_n2_collpers W hκ hN2
  obtain ⟨hq1, hq2, hq3⟩ := p0_smul_e3 hF κ
  rw [← hxe] at hq1 hq2 hq3
  have hba : b - a' = (1 - β6) • (b - d) + (-γ6) • (c - d) := by rw [ha']; module
  have hca : c - a' = (-β6) • (b - d) + (1 - γ6) • (c - d) := by rw [ha']; module
  have E1 : (1 - β6) * ⟪b - d, e2⟫ + (-γ6) * ⟪c - d, e2⟫ = 0 := by
    have := hbe2; rw [hba, inner_add_left, inner_smul_left, inner_smul_left] at this; simpa using this
  have E2 : (-β6) * ⟪b - d, e2⟫ + (1 - γ6) * ⟪c - d, e2⟫ = 0 := by
    have := hq2; rw [hca, inner_add_left, inner_smul_left, inner_smul_left] at this; simpa using this
  have hx : ⟪b - d, e2⟫ = 0 := by
    have : ⟪b - d, e2⟫ * (1 - β6 - γ6) = 0 := by linear_combination (1 - γ6) * E1 + γ6 * E2
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exfalso; linarith
  have hy : ⟪c - d, e2⟫ = 0 := by
    rw [hx] at E1
    have : γ6 * ⟪c - d, e2⟫ = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hγ6.ne'
    · exact h
  have hu : α1 • (a - d) + β1 • (b - d) - (c - d) = (c' - a') - κ • e3 := by
    rw [hc', ← hxe]; rw [ha']; module
  have hw : (b - d) - (c - d) = (b - a') - κ • e3 := by rw [← hxe]; module
  refine k16_rel_norm (k17c_rel_core hF hdet hx hy ?_ ?_)
  · have : (b - d) - (c - d) = b - c := by abel
    rw [this]; exact hρ
  · obtain ⟨h1, -⟩ := hcoll
    rw [hu, hw]
    obtain ⟨k1, -, k3⟩ := p0_smul_e3 hF κ
    have m1 : ∀ v : ℝ³, ⟪v - κ • e3, e1⟫ = ⟪v, e1⟫ := fun v => by rw [inner_sub_left, k1]; ring
    have m3 : ∀ v : ℝ³, ⟪v - κ • e3, e3⟫ = ⟪v, e3⟫ - κ := fun v => by rw [inner_sub_left, k3]
    rw [m1, m1, m3, m3]
    linarith

theorem k17c_kb_rel {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hκ : det3 (c - b) (b' - b) (c' - b) = 0) (hKb : ParEndKb b b' c c' d)
    (hρ : ⟪a - d, b - c⟫ = 0) {α1 β1 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0) (hb' : b' = d + α1 • (a - d) + β1 • (c - d)) :
    K16Rel a b c d α1 β1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, e1, e2, e3, κ, hF, hκ0, hxe, hce2, hL, hr, hYY, hcoll, -⟩ :=
    p0_kb_collpers W hκ hKb
  obtain ⟨k1, k2, k3⟩ := p0_smul_e3 hF κ
  have hx : ⟪b - d, e2⟫ = 0 := by rw [hxe]; exact k2
  have hu : α1 • (a - d) + β1 • (c - d) - (b - d) = (b' - d) - κ • e3 := by
    rw [hb', ← hxe]; module
  have hw : (c - d) - (b - d) = (c - d) - κ • e3 := by rw [← hxe]
  have hdet' : det3 (a - d) (c - d) (b - d) ≠ 0 := by
    intro h; apply hdet
    simp only [det3_expand] at h ⊢; linarith
  have key := k17c_rel_core hF hdet' hce2 hx (r := a - d) (p := c - d) (q := b - d) (α1 := α1) (β1 := β1) ?_ ?_
  · obtain ⟨h1, h2⟩ := key
    have hs' : ⟪a - d, c - d⟫ = ⟪a - d, b - d⟫ := by
      have : ⟪a - d, b - c⟫ = ⟪a - d, b - d⟫ - ⟪a - d, c - d⟫ := by
        rw [← inner_sub_right]; congr 1; abel
      linarith
    have e : ⟪(c - d) - (b - d), (c - d) - (c - d) + ((c - d) - (b - d))⟫ = ⟪(c - d) - (b - d), (c - d) - (b - d)⟫ := by
      congr 1; abel
    have e2' : ⟪(c - d) - (b - d), (c - d) - (b - d)⟫ =
        ⟪b - d, b - d⟫ + ⟪c - d, c - d⟫ - 2 * ⟪b - d, c - d⟫ := by
      simp only [inner_sub_left, inner_sub_right]
      have := real_inner_comm b c; have := real_inner_comm b d; have := real_inner_comm c d
      linarith
    rw [hs', e2'] at h1
    have hcm := real_inner_comm (c - d) (b - d)
    rw [← hcm] at h1 h2
    refine ⟨?_, ?_⟩
    · linear_combination h1
    · linarith [h2]
  · have : (c - d) - (b - d) = c - b := by abel
    rw [this]
    have : ⟪a - d, c - b⟫ = -⟪a - d, b - c⟫ := by
      rw [← inner_neg_right]; congr 1; abel
    rw [this, hρ]; simp
  · obtain ⟨h1, -⟩ := hcoll
    rw [hu, hw]
    have m1 : ∀ v : ℝ³, ⟪v - κ • e3, e1⟫ = ⟪v, e1⟫ := fun v => by rw [inner_sub_left, k1]; ring
    have m3 : ∀ v : ℝ³, ⟪v - κ • e3, e3⟫ = ⟪v, e3⟫ - κ := fun v => by rw [inner_sub_left, k3]
    rw [m1, m1, m3, m3]
    linarith

/-- At `β1 = 1`: the Gram relation forces `⟪a-d, b-d⟫ = 0` (given `α1 > 0`). -/
theorem k17c_m_zero {a b c d : ℝ³} {α1 : ℝ} (hα1 : 0 < α1) (h : K16Rel a b c d α1 1) :
    ⟪a - d, b - d⟫ = 0 := by
  obtain ⟨h1, h2⟩ := h
  have hS : 0 < ⟪b - d, b - d⟫ + ⟪c - d, c - d⟫ - 2 * ⟪b - d, c - d⟫ := by
    by_contra hS; push Not at hS
    have : 0 ≤ ⟪b - d, b - d⟫ + ⟪c - d, c - d⟫ - 2 * ⟪b - d, c - d⟫ := by
      have e : ⟪b - d, b - d⟫ + ⟪c - d, c - d⟫ - 2 * ⟪b - d, c - d⟫ = ⟪(b - d) - (c - d), (b - d) - (c - d)⟫ := by
        simp only [inner_sub_left, inner_sub_right]
        have := real_inner_comm b c; have := real_inner_comm b d; have := real_inner_comm c d
        linarith
      rw [e]; exact real_inner_self_nonneg
    have h0 : ⟪b - d, b - d⟫ + ⟪c - d, c - d⟫ - 2 * ⟪b - d, c - d⟫ = 0 := le_antisymm hS this
    have hR : ⟪b - d, c - d⟫ = (⟪b - d, b - d⟫ + ⟪c - d, c - d⟫) / 2 := by linarith
    rw [hR] at h2
    nlinarith [sq_nonneg (⟪b - d, b - d⟫ - ⟪c - d, c - d⟫)]
  have : α1 * ⟪a - d, b - d⟫ * (⟪b - d, b - d⟫ + ⟪c - d, c - d⟫ - 2 * ⟪b - d, c - d⟫) = 0 := by
    rw [h1]; ring
  rcases mul_eq_zero.mp this with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact absurd h hα1.ne'
    · exact h
  · exact absurd h hS.ne'

end C2
end Type08Sp
end Minimality
