module

public import Minimality.Type08S.C2K6HC

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2

set_option maxHeartbeats 6400000 in
/-- **H1 / H2 cell 1** (`α1, β1, β6 > 1`, `γ6 > 1`; view `a - b'`): literals `ζ(c, a') > 0` and `ζ(a, c') > 0` give the pentagon `(a, c', a', c, d)`. -/
theorem k6mh1_cell1 {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 1 < β6) (hγ6 : 1 < γ6)
    (hM : K6sM a a' b b' c c' d) (hpos : 0 < ⟪c - a', a - b'⟫) (hlit3 : 0 < ⟪a - c', a - b'⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  have hγ0 : 0 < γ6 := by linarith
  obtain ⟨m1, m2, m3⟩ := hM
  have hA1 : α1 - 1 ≠ 0 := by intro h; linarith
  have h1a : 1 - α1 ≠ 0 := by intro h; linarith
  set κ : ℝ := β1 / (1 - α1) with hκdef
  set σ : ℝ := 1 / (1 - α1) with hσdef
  have hκ : κ * (1 - α1) = β1 := by rw [hκdef]; field_simp
  have hσ : σ * (1 - α1) = 1 := by rw [hσdef]; field_simp
  have hκσ : κ = σ * β1 := by
    have : (κ - σ * β1) * (1 - α1) = 0 := by linear_combination hκ - β1 * hσ
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right h1a)
  obtain ⟨hκn, hσn, hbc, hcc, haa, hE⟩ := k6m_H2_conds hκ hσ hα1 hβ1 hβ6 hγ0
  set p := a - d with hp
  set q := b - d with hq
  set r := c - d with hr
  set R := a - b' with hR
  have hRv : R = (1 - α1) • p + (0:ℝ) • q + (-β1) • r := by rw [hR, hb']; simp only [hp, hr]; module
  have hΔ : det3 q r R ≠ 0 := by
    have e : det3 q r R = (1 - α1) * det3 (a - d) (b - d) (c - d) := by
      rw [hR, hb']
      simp only [hp, hq, hr, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e]; exact mul_ne_zero h1a hdet
  have eaR : σ • R + κ • r = p := by
    rw [hRv, hκσ]
    have : σ * (1 - α1) = 1 := hσ
    match_scalars <;> first | ring1 | linear_combination hσ | linear_combination (-1:ℝ) * hσ
  have eO : fpoint q r R d (0, 0, 0) = d := by simp [fpoint, fcomb]
  have eB : fpoint q r R d (1, 0, 0) = b := by simp only [fpoint, fcomb, hq]; module
  have eC : fpoint q r R d (0, 1, 0) = c := by simp only [fpoint, fcomb, hr]; module
  have eA' : fpoint q r R d (β6, γ6, 0) = a' := by rw [ha']; simp only [fpoint, fcomb, hq, hr]; module
  have eA : fpoint q r R d (0, κ, σ) = a := by
    simp only [fpoint, fcomb]
    have : κ • r + σ • R = p := by rw [add_comm]; exact eaR
    rw [zero_smul, zero_add, this, hp]; abel
  have eB' : fpoint q r R d (0, κ, σ - 1) = b' := by
    have : fpoint q r R d (0, κ, σ - 1) = fpoint q r R d (0, κ, σ) - R := by
      simp only [fpoint, fcomb]; module
    rw [this, eA, hR]; abel
  have eC' : fpoint q r R d (β1, κ * α1, α1 * σ) = c' := by
    have : fpoint q r R d (β1, κ * α1, α1 * σ) = d + β1 • q + α1 • (κ • r + σ • R) := by
      simp only [fpoint, fcomb]; module
    rw [this]
    have h2 : κ • r + σ • R = p := by rw [add_comm]; exact eaR
    rw [h2, hc', hp]; abel
  have hV : ∀ y ∈ V8 a a' b b' c c' d, y = fpoint q r R d (0, κ, σ) ∨ y = fpoint q r R d (β1, κ * α1, α1 * σ) ∨
      y = fpoint q r R d (β6, γ6, 0) ∨ y = fpoint q r R d (0, 1, 0) ∨ y = fpoint q r R d (0, 0, 0) ∨
      y = fpoint q r R d (1, 0, 0) ∨ y = fpoint q r R d (0, κ, σ - 1) := by
    intro y hy
    rw [eA, eC', eA', eC, eO, eB, eB']
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    tauto
  have hV2 : ∀ y ∈ V8 a a' b b' c c' d, y = fpoint q r R d (0, κ, σ - 1) ∨ y = fpoint q r R d (β1, κ * α1, α1 * σ) ∨
      y = fpoint q r R d (β6, γ6, 0) ∨ y = fpoint q r R d (0, 1, 0) ∨ y = fpoint q r R d (0, κ, σ) ∨
      y = fpoint q r R d (0, 0, 0) ∨ y = fpoint q r R d (1, 0, 0) := by
    intro y hy
    rw [eA, eC', eA', eC, eO, eB, eB']
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    tauto
  -- Gram data
  have key : ∀ x y z : ℝ, ⟪x • p + y • q + z • r, R⟫ =
      x * ((1 - α1) * ⟪p, p⟫ - β1 * ⟪p, r⟫) + y * ((1 - α1) * ⟪p, q⟫ - β1 * ⟪q, r⟫) +
        z * ((1 - α1) * ⟪p, r⟫ - β1 * ⟪r, r⟫) := by
    intro x y z
    rw [hRv, k6m_ip]; ring
  have hm1 : ⟪p, q⟫ = ⟪p, r⟫ := by
    have : ⟪p, b - c⟫ = ⟪p, q⟫ - ⟪p, r⟫ := by
      rw [← inner_sub_right]; congr 1; rw [hq, hr]; abel
    linarith
  have hm2 : 0 < ⟪q, q⟫ - ⟪q, r⟫ := by
    have e : ⟪c' - d, b - c⟫ = α1 * (⟪p, q⟫ - ⟪p, r⟫) + β1 * (⟪q, q⟫ - ⟪q, r⟫) := by
      have : c' - d = α1 • p + β1 • q + (0:ℝ) • r := by rw [hc']; simp only [hp, hq]; module
      have h2 : b - c = (0:ℝ) • p + (1:ℝ) • q + (-1:ℝ) • r := by rw [hq, hr]; module
      rw [this, h2, k6m_ip]; ring
    rw [hm1] at e
    nlinarith
  have hm3 : ⟪q, r⟫ - ⟪r, r⟫ < 0 := by
    have e : ⟪b' - d, b - c⟫ = α1 * (⟪p, q⟫ - ⟪p, r⟫) + β1 * (⟪q, r⟫ - ⟪r, r⟫) := by
      have : b' - d = α1 • p + (0:ℝ) • q + β1 • r := by rw [hb']; simp only [hp, hr]; module
      have h2 : b - c = (0:ℝ) • p + (1:ℝ) • q + (-1:ℝ) • r := by rw [hq, hr]; module
      rw [this, h2, k6m_ip]; ring
    rw [hm1] at e
    nlinarith
  have inner_lt : ∀ X Y : ℝ³, ⟪X - Y, R⟫ < 0 → ⟪X, R⟫ < ⟪Y, R⟫ := by
    intro X Y h; rw [inner_sub_left] at h; linarith
  have hcR : ⟪c - a', R⟫ = (-β6) * ((1 - α1) * ⟪p, q⟫ - β1 * ⟪q, r⟫) + (1 - γ6) * ((1 - α1) * ⟪p, r⟫ - β1 * ⟪r, r⟫) := by
    have : c - a' = (0:ℝ) • p + (-β6) • q + (1 - γ6) • r := by rw [ha', hp, hq, hr]; module
    rw [this, key]; ring
  -- zB - zC > 0
  have hBC : 0 < ((1 - α1) * ⟪p, q⟫ - β1 * ⟪q, r⟫) - ((1 - α1) * ⟪p, r⟫ - β1 * ⟪r, r⟫) := by
    rw [hm1]; nlinarith
  have hR0 : R ≠ 0 := by intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  have L1 : (1 - γ6) * ((1 - α1) * ⟪p, r⟫ - β1 * ⟪r, r⟫) > β6 * ((1 - α1) * ⟪p, q⟫ - β1 * ⟪q, r⟫) := by
    rw [hcR] at hpos; linarith
  set zB := (1 - α1) * ⟪p, q⟫ - β1 * ⟪q, r⟫ with hzB
  set zC := (1 - α1) * ⟪p, r⟫ - β1 * ⟪r, r⟫ with hzC
  have hzC0 : zC < 0 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ β6 + γ6 - 1) hh, mul_pos (by linarith : (0:ℝ) < β6) hBC]
  have hA : HasLexCellAt (V8 a a' b b' c c' d) R := by
    refine k6mh1_hc1_frame (V8 a a' b b' c c' d) q r R d hΔ hκn hσn hα1 (by linarith) hβ6 hγ0 hγ6 hbc hcc haa hE
      ?_ hV ?_ ?_ ?_
    · intro i
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · simp only [k6mHCyc1_0, eA]; simp [V8]
      · simp only [k6mHCyc1_1, eC']; simp [V8]
      · simp only [k6mHCyc1_2, eA']; simp [V8]
      · simp only [k6mHCyc1_3, eC]; simp [V8]
      · simp only [k6mHCyc1_4, eO]; simp [V8]
    · rw [eA', eC]
      apply inner_lt
      have : a' - c = (0:ℝ) • p + β6 • q + (γ6 - 1) • r := by rw [ha', hp, hq, hr]; module
      rw [this, key]; nlinarith
    · rw [eC, eO]
      apply inner_lt
      have : c - d = (0:ℝ) • p + (0:ℝ) • q + (1:ℝ) • r := by rw [hr]; module
      rw [this, key]; nlinarith
    · rw [eC', eA, eO]
      left
      rw [inner_sub_left] at hlit3
      linarith
  exact ⟨R, hR0, hA⟩

end C2
end Type08Sp
end Minimality
