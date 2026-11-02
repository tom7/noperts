module

public import Minimality.Type08S.C2K16D

@[expose] public section


/-!
# K16 / E: the Coll5 relation `α1 s |b-c|² = -(β1-1) (QT - R²)` (`s = ⟪a-d,b-d⟫`, `Q = |b-d|²`, `T = |c-d|²`, `R = ⟪b-d,c-d⟫`)
for `ParEndN2` and `ParEndKb` with `κ_a = 0`, `ρ_a = 0`.
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

/-- The Gram relation forced by `Coll5` on the slice `ρ_a = 0`. -/
def K16Rel (a b c d : ℝ³) (α1 β1 : ℝ) : Prop :=
  α1 * ⟪a - d, b - d⟫ * (⟪b - d, b - d⟫ + ⟪c - d, c - d⟫ - 2 * ⟪b - d, c - d⟫) =
      -(β1 - 1) * (⟪b - d, b - d⟫ * ⟪c - d, c - d⟫ - ⟪b - d, c - d⟫ ^ 2) ∧
    0 < ⟪b - d, b - d⟫ * ⟪c - d, c - d⟫ - ⟪b - d, c - d⟫ ^ 2

theorem k16_rel_norm {a b c d : ℝ³} {α1 β1 : ℝ}
    (h : α1 * (⟪a - d, b - d⟫ * ⟪(b - d) - (c - d), (b - d) - (c - d)⟫) =
        -(β1 - 1) * (⟪b - d, b - d⟫ * ⟪c - d, c - d⟫ - ⟪b - d, c - d⟫ ^ 2) ∧
      0 < ⟪b - d, b - d⟫ * ⟪c - d, c - d⟫ - ⟪b - d, c - d⟫ ^ 2) : K16Rel a b c d α1 β1 := by
  obtain ⟨h1, h2⟩ := h
  have e : ⟪(b - d) - (c - d), (b - d) - (c - d)⟫ =
      ⟪b - d, b - d⟫ + ⟪c - d, c - d⟫ - 2 * ⟪b - d, c - d⟫ := by
    simp only [inner_sub_left, inner_sub_right]
    have := real_inner_comm b c; have := real_inner_comm b d; have := real_inner_comm c d
    linarith
  rw [e] at h1
  exact ⟨by linarith, h2⟩

theorem k16_n2_rel {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hκ : det3 (c - b) (b' - b) (c' - b) = 0) (hN2 : ParEndN2 a a' b b' c c')
    (hρ : ⟪a - d, b - c⟫ = 0) {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0) (hc' : c' = d + α1 • (a - d) + β1 • (b - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d)) (hα1 : 0 < α1) (hβ1 : 1 < β1) (hγ6 : 0 < γ6)
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
  refine k16_rel_norm (k16_rel_core hF hα1 hβ1 hdet hx hy ?_ ?_)
  · have : (b - d) - (c - d) = b - c := by abel
    rw [this]; exact hρ
  · obtain ⟨h1, -⟩ := hcoll
    rw [hu, hw]
    obtain ⟨k1, -, k3⟩ := p0_smul_e3 hF κ
    have m1 : ∀ v : ℝ³, ⟪v - κ • e3, e1⟫ = ⟪v, e1⟫ := fun v => by rw [inner_sub_left, k1]; ring
    have m3 : ∀ v : ℝ³, ⟪v - κ • e3, e3⟫ = ⟪v, e3⟫ - κ := fun v => by rw [inner_sub_left, k3]
    rw [m1, m1, m3, m3]
    linarith

theorem k16_kb_rel {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hκ : det3 (c - b) (b' - b) (c' - b) = 0) (hKb : ParEndKb b b' c c' d)
    (hρ : ⟪a - d, b - c⟫ = 0) {α1 β1 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (hα1 : 0 < α1) (hβ1 : 1 < β1) : K16Rel a b c d α1 β1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, e1, e2, e3, κ, hF, hκ0, hxe, hce2, hL, hr, hYY, hcoll, -⟩ :=
    p0_kb_collpers W hκ hKb
  obtain ⟨k1, k2, k3⟩ := p0_smul_e3 hF κ
  have hx : ⟪b - d, e2⟫ = 0 := by rw [hxe]; exact k2
  -- roles: r := a-d, p := c-d, q := b-d
  have hu : α1 • (a - d) + β1 • (c - d) - (b - d) = (b' - d) - κ • e3 := by
    rw [hb', ← hxe]; module
  have hw : (c - d) - (b - d) = (c - d) - κ • e3 := by rw [← hxe]
  have hdet' : det3 (a - d) (c - d) (b - d) ≠ 0 := by
    intro h; apply hdet
    simp only [det3_expand] at h ⊢; linarith
  have key := k16_rel_core hF hα1 hβ1 hdet' hce2 hx (r := a - d) (p := c - d) (q := b - d) ?_ ?_
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

end C2
end Type08Sp
end Minimality
