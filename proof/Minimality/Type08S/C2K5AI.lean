module

public import Minimality.Type08S.C2K5AH

@[expose] public section


/-!
# K5a / I: P0-N2: `ParEndN2` + `κ_a = 0` ⟹ `α4 = α1`, `γ4 = β1`, and in the frame (`x' = a'`, `x = c`, `f = b`, `r = c'`,
`g = b'`) `Yr = Yg ∧ Coll5 ∧ PersF`.
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem p0_n2_collpers {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hκ : det3 (c - b) (b' - b) (c' - b) = 0) (h : ParEndN2 a a' b b' c c') :
    ∃ α1 α4 β1 γ4 β6 γ6 : ℝ, P0Coords W α1 α4 β1 γ4 β6 γ6 ∧ α4 = α1 ∧ γ4 = β1 ∧
      ∃ (e1 e2 e3 : ℝ³) (κ : ℝ), Fr e1 e2 e3 ∧ κ ≠ 0 ∧ c - a' = κ • e3 ∧ ⟪b - a', e2⟫ = 0 ∧
        0 < ⟪b - a', e1⟫ ∧ 0 < ⟪c' - a', e2⟫ ∧ ⟪c' - a', e2⟫ = ⟪b' - a', e2⟫ ∧
        Coll5 ⟪b - a', e1⟫ κ ⟪b - a', e3⟫ ⟪c' - a', e1⟫ ⟪c' - a', e3⟫ ⟪b' - a', e1⟫ ⟪b' - a', e3⟫ ∧
        PersF ⟪b - a', e1⟫ κ ⟪b - a', e3⟫ ⟪c' - a', e1⟫ ⟪c' - a', e2⟫ ⟪c' - a', e3⟫ ⟪b' - a', e1⟫
          ⟪b' - a', e2⟫ ⟪b' - a', e3⟫ := by
  obtain ⟨α1, α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hα1, hβ1, h1, hα4, hγ4, h2, hβ6, hγ6, h3,
    hfa, hfb⟩ := norm08w_coords W
  obtain ⟨e1, e2, e3, κ, hF, hκ0, hxe, hbe2, hL, hr, hrob, hbr⟩ := h
  obtain ⟨hYY, hbr⟩ := hbr
  obtain ⟨hq1, hq2, hq3⟩ := p0_smul_e3 hF κ
  rw [← hxe] at hq1 hq2 hq3
  -- `e2 ⟂ b - d, c - d`
  have hba : b - a' = (1 - β6) • (b - d) + (-γ6) • (c - d) := by rw [ha']; module
  have hca : c - a' = (-β6) • (b - d) + (1 - γ6) • (c - d) := by rw [ha']; module
  have E1 : (1 - β6) * ⟪b - d, e2⟫ + (-γ6) * ⟪c - d, e2⟫ = 0 := by
    have := hbe2; rw [hba, inner_add_left, inner_smul_left, inner_smul_left] at this; simpa using this
  have E2 : (-β6) * ⟪b - d, e2⟫ + (1 - γ6) * ⟪c - d, e2⟫ = 0 := by
    have := hq2; rw [hca, inner_add_left, inner_smul_left, inner_smul_left] at this; simpa using this
  have hx : ⟪b - d, e2⟫ = 0 := by
    have : ⟪b - d, e2⟫ * (1 - β6 - γ6) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exfalso; linarith
  have hy : ⟪c - d, e2⟫ = 0 := by
    rw [hx] at E1
    have : γ6 * ⟪c - d, e2⟫ = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hγ6.ne'
    · exact h
  have hpne : ⟪a - d, e2⟫ ≠ 0 := fun hp => p0_e2_not_perp hF.n22 hdet hp hx hy
  have hc'a : c' - a' = α1 • (a - d) + (β1 - β6) • (b - d) + (-γ6) • (c - d) := by
    rw [hc', ha']; module
  have hb'a : b' - a' = α4 • (a - d) + (-β6) • (b - d) + (γ4 - γ6) • (c - d) := by
    rw [hb', ha']; module
  have hα : α4 = α1 := by
    have e1' : ⟪c' - a', e2⟫ = α1 * ⟪a - d, e2⟫ := by
      rw [hc'a, inner_add_left, inner_add_left, inner_smul_left, inner_smul_left, inner_smul_left, hx, hy]; simp
    have e2' : ⟪b' - a', e2⟫ = α4 * ⟪a - d, e2⟫ := by
      rw [hb'a, inner_add_left, inner_add_left, inner_smul_left, inner_smul_left, inner_smul_left, hx, hy]; simp
    have : (α4 - α1) * ⟪a - d, e2⟫ = 0 := by
      have := hYY; rw [e1', e2'] at this; linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hpne
  have hγ : γ4 = β1 := by
    have := (planar_a_iff hdet hc' hb').mp hκ
    rw [hα] at this
    have : α1 * (β1 - γ4) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hα1.ne'
    · linarith
  refine ⟨α1, α4, β1, γ4, β6, γ6, ⟨hdet, hc', hb', ha', hα1, hβ1, h1, hα4, hγ4, h2, hβ6, hγ6, h3, hfa, hfb⟩,
    hα, hγ, e1, e2, e3, κ, hF, hκ0, hxe, hbe2, hL, hr, hYY, ?_⟩
  rcases hbr with hce | hpar
  · obtain ⟨s', hs0, hs1, -, hL1, hz1⟩ := hce
    obtain ⟨w, hwdef⟩ : ∃ w : ℝ³, w = b - (c' + s' • (b' - c')) := ⟨_, rfl⟩
    have hwd : w = (b - a') - (c' - a') - s' • ((b' - a') - (c' - a')) := by rw [hwdef]; module
    have hw1 : ⟪w, e1⟫ = 0 := by rw [hwd, p0_cef_inner]; linarith
    have hw3 : ⟪w, e3⟫ = 0 := by rw [hwd, p0_cef_inner]; linarith
    have hc'id : c' - a' = (1 - (1 + s' * β1)) • (c - a') + (1 + s' * β1) • (b - a') - w := by
      rw [hwdef, hb', hc', ha', hα, hγ]; module
    have hb'id : b' - a' = (1 - (1 - β1 + s' * β1)) • (c - a') + (1 - β1 + s' * β1) • (b - a') - w := by
      rw [hwdef, hb', hc', ha', hα, hγ]; module
    have X1 : ⟪c' - a', e1⟫ = (1 + s' * β1) * ⟪b - a', e1⟫ := by
      rw [hc'id, p0_comb_e, hq1, hw1]; ring
    have Z1 : ⟪c' - a', e3⟫ = (1 - (1 + s' * β1)) * κ + (1 + s' * β1) * ⟪b - a', e3⟫ := by
      rw [hc'id, p0_comb_e, hq3, hw3]; ring
    have X2 : ⟪b' - a', e1⟫ = (1 - β1 + s' * β1) * ⟪b - a', e1⟫ := by
      rw [hb'id, p0_comb_e, hq1, hw1]; ring
    have Z2 : ⟪b' - a', e3⟫ = (1 - (1 - β1 + s' * β1)) * κ + (1 - β1 + s' * β1) * ⟪b - a', e3⟫ := by
      rw [hb'id, p0_comb_e, hq3, hw3]; ring
    refine ⟨⟨?_, ?_⟩, 1, s', zero_le_one, le_refl _, hs0, hs1, Or.inl hYY, ?_, ?_⟩
    · rw [Z1, X1]; ring
    · rw [Z2, X2]; ring
    · rw [one_mul]; exact hL1
    · linarith
  · obtain ⟨-, hcoll, hpers⟩ := hpar
    exact ⟨hcoll, hpers⟩

end C2
end Type08Sp
end Minimality
