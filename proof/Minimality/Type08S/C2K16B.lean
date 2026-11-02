module

public import Minimality.Type08S.C2K16A

@[expose] public section


/-!
# K16 / B: `ParEndN2` + `κ_a = 0` + `ρ_a = 0` ⟹ `⟪a-d, b-d⟫ < 0` (for every `α1 > 0`, `β1 > 1`)
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

theorem k16_n2_s_neg {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hκ : det3 (c - b) (b' - b) (c' - b) = 0) (hN2 : ParEndN2 a a' b b' c c')
    (hρ : ⟪a - d, b - c⟫ = 0) {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0) (hc' : c' = d + α1 • (a - d) + β1 • (b - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d)) (hα1 : 0 < α1) (hβ1 : 1 < β1) (hγ6 : 0 < γ6) (h3 : 1 < β6 + γ6) :
    ⟪a - d, b - d⟫ < 0 := by
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
  refine k16_s_neg hF hα1 hβ1 hdet hx hy ?_ ?_
  · have : (b - d) - (c - d) = b - c := by abel
    rw [this]; exact hρ
  · obtain ⟨h1, -⟩ := hcoll
    rw [hu, hw]
    obtain ⟨k1, -, k3⟩ := p0_smul_e3 hF κ
    have m1 : ∀ v : ℝ³, ⟪v - κ • e3, e1⟫ = ⟪v, e1⟫ := fun v => by rw [inner_sub_left, k1]; ring
    have m3 : ∀ v : ℝ³, ⟪v - κ • e3, e3⟫ = ⟪v, e3⟫ - κ := fun v => by rw [inner_sub_left, k3]
    rw [m1, m1, m3, m3]
    linarith
end C2
end Type08Sp
end Minimality
