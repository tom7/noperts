module

public import Minimality.Type08S.C2K5AA

@[expose] public section


/-!
# K5a / B: P0-K2 extraction.  `ParEndK2` + `κ_a = 0` ⟹ CEf5 equations in W0 coordinates.
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- **P0 for `ParEndK2`.**  In W0 coordinates (`p = a-d, q = b-d, r = c-d`): `γ4 = 1`, `β1 = 1` and
`∃ s' ∈ [0,1]`, `λ := α1 - α4 + s' α4`, `λ A + B - C = 0 ∧ λ B + ⟪q,q⟫ - ⟪q,r⟫ = 0`. -/
theorem p0_comb_inner (p q r : ℝ³) (l : ℝ) :
    ⟪l • p + q - r, p⟫ = l * ⟪p, p⟫ + ⟪p, q⟫ - ⟪p, r⟫ ∧
    ⟪l • p + q - r, q⟫ = l * ⟪p, q⟫ + ⟪q, q⟫ - ⟪q, r⟫ := by
  simp only [inner_add_left, inner_sub_left, inner_smul_left, RCLike.conj_to_real]
  rw [real_inner_comm p q, real_inner_comm p r, real_inner_comm q r]
  exact ⟨by ring, by ring⟩

theorem p0_cef_inner (e : ℝ³) (s : ℝ) (u v t : ℝ³) :
    ⟪u - v - s • (t - v), e⟫ = ⟪u, e⟫ - ⟪v, e⟫ - s * (⟪t, e⟫ - ⟪v, e⟫) := by
  simp only [inner_sub_left, inner_smul_left, RCLike.conj_to_real]

theorem p0_k2_extract {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hκ : det3 (c - b) (b' - b) (c' - b) = 0) (h : ParEndK2 b b' c c' d) :
    ∃ α1 α4 β1 γ4 β6 γ6 : ℝ, det3 (a - d) (b - d) (c - d) ≠ 0 ∧
      c' = d + α1 • (a - d) + β1 • (b - d) ∧ b' = d + α4 • (a - d) + γ4 • (c - d) ∧
      a' = d + β6 • (b - d) + γ6 • (c - d) ∧
      0 < α1 ∧ 0 < β1 ∧ 1 < α1 + β1 ∧ 0 < α4 ∧ 0 < γ4 ∧ 1 < α4 + γ4 ∧ 0 < β6 ∧ 0 < γ6 ∧ 1 < β6 + γ6 ∧
      (W.F.abc'.f c < W.F.abc'.f a' → γ6 < 1) ∧ (W.F.a'bc.f c' < W.F.a'bc.f a → 1 < α1) ∧
      γ4 = 1 ∧ β1 = 1 ∧
      ∃ s' : ℝ, 0 ≤ s' ∧ s' ≤ 1 ∧
        (α1 - α4 + s' * α4) * ⟪a - d, a - d⟫ + ⟪a - d, b - d⟫ - ⟪a - d, c - d⟫ = 0 ∧
        (α1 - α4 + s' * α4) * ⟪a - d, b - d⟫ + ⟪b - d, b - d⟫ - ⟪b - d, c - d⟫ = 0 := by
  obtain ⟨α1, α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hα1, hβ1, h1, hα4, hγ4, h2, hβ6, hγ6, h3,
    hfa, hfb⟩ := norm08w_coords W
  obtain ⟨e1, e2, e3, κ, hF, hκ0, hxe, hf2, hL, hr, hrob, hpe⟩ := h
  obtain ⟨hYY, hce | hpar⟩ := hpe
  swap
  · exfalso
    exact p0_k2_par5_empty hF hdet hc' hb' hα4 hβ1 hxe hf2 hL hYY hpar.2.1
  obtain ⟨hqe, hpe2, hγ⟩ := p0_k2_basic hF hdet hc' hb' hα1 hxe hf2 hYY
  have hβ : β1 = 1 := by
    have := (planar_a_iff hdet hc' hb').mp hκ
    rw [hγ] at this
    have h0 : α4 * (1 - β1) = 0 := by linarith
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hα4.ne'
    · linarith
  obtain ⟨s', hs0, hs1, -, hL1, hz1⟩ := hce
  refine ⟨α1, α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hα1, hβ1, h1, hα4, hγ4, h2, hβ6, hγ6, h3,
    hfa, hfb, hγ, hβ, s', hs0, hs1, ?_⟩
  set w : ℝ³ := c' - (b' + s' • (c - b')) with hw
  have hwd : w = (c' - b) - (b' - b) - s' • ((c - b) - (b' - b)) := by rw [hw]; module
  have hw1 : ⟪w, e1⟫ = 0 := by
    rw [hwd, p0_cef_inner]; linarith
  have hw3 : ⟪w, e3⟫ = 0 := by
    rw [hwd, p0_cef_inner]; linarith
  have hwe : w = ⟪w, e2⟫ • e2 := by
    have := hF.expand w; rw [hw1, hw3] at this; simpa using this
  have hwp : ⟪w, a - d⟫ = 0 := by
    have h0 : ⟪e2, a - d⟫ = 0 := by rw [real_inner_comm]; exact hpe2
    rw [hwe, inner_smul_left, h0]; simp
  have hwq : ⟪w, b - d⟫ = 0 := by
    have h0 : ⟪e2, b - d⟫ = 0 := by rw [real_inner_comm]; exact hqe
    rw [hwe, inner_smul_left, h0]; simp
  have hwv : w = (α1 - α4 + s' * α4) • (a - d) + (b - d) - (c - d) := by
    rw [hw, hc', hb', hβ, hγ]; module
  rw [hwv] at hwp hwq
  obtain ⟨i1, i2⟩ := p0_comb_inner (a - d) (b - d) (c - d) (α1 - α4 + s' * α4)
  exact ⟨by rw [← i1]; exact hwp, by rw [← i2]; exact hwq⟩

end C2
end Type08Sp
end Minimality
