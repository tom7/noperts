module

public import Minimality.Type08S.C2K14B

@[expose] public section


/-!
# K14 / C: the H2 tie `ζ_{a-b'}(c, a') = 0` with `ζ_{a-b'}(c', a') ≠ 0` (box `α1, β1, β6 > 1`, `0 < γ6 < 1`)
`a' < c'`: pentagon `(a, c', a', c, d)` (tilt with `c <lex a'`); `c' < a'`: quadrilateral `(b', c', a', c)`.
Remaining tie: `ζ(c, a') = ζ(c', a') = 0` at `a - b'`.
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

set_option maxHeartbeats 6400000 in
theorem k14_H2tie_hasLexCell {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 1 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hM : K6sM a a' b b' c c' d) (hlit : ⟪c - a', a - b'⟫ = 0) (hlit2 : ⟪c' - a', a - b'⟫ ≠ 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
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
  obtain ⟨hκn, hσn, hbc, hcc, haa, hE⟩ := k6m_H2_conds hκ hσ hα1 hβ1 hβ6 hγ6
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
  have hlit' : ⟪c - a', R⟫ = 0 := hlit
  have hcR0 : (-β6) * ((1 - α1) * ⟪p, q⟫ - β1 * ⟪q, r⟫) + (1 - γ6) * ((1 - α1) * ⟪p, r⟫ - β1 * ⟪r, r⟫) = 0 := by
    rw [← hcR]; exact hlit'
  set zB := (1 - α1) * ⟪p, q⟫ - β1 * ⟪q, r⟫ with hzB
  set zC := (1 - α1) * ⟪p, r⟫ - β1 * ⟪r, r⟫ with hzC
  have hzC0 : zC < 0 := by
    nlinarith [mul_pos (by linarith : (0:ℝ) < β6) hBC]
  have hzB0 : zB < 0 := by
    nlinarith [mul_pos (by linarith : (0:ℝ) < 1 - γ6) (neg_pos.2 hzC0)]
  have hm0 : κ * (α1 - 1) / β1 = -1 := by
    have : κ * (α1 - 1) = -β1 := by linarith
    rw [this]; field_simp
  rcases lt_or_gt_of_ne hlit2 with hneg | hpos
  · -- c' < a' : quadrilateral
    have hA : HasLexCellAt (V8 a a' b b' c c' d) R := by
      refine k14_hc2_frame (V8 a a' b b' c c' d) q r R d hΔ hκn hσn hα1 (by linarith) hβ6 hγ6 hγ61 hbc hcc haa hE
        ?_ hV2 ?_ ?_
      · intro i
        rcases z4_cases i with rfl | rfl | rfl | rfl
        · simp only [k6mHCyc2_0, eB']; simp [V8]
        · simp only [k6mHCyc2_1, eC']; simp [V8]
        · simp only [k6mHCyc2_2, eA']; simp [V8]
        · simp only [k6mHCyc2_3, eC]; simp [V8]
      · rw [eB', eC']
        apply inner_lt
        have : b' - c' = (0:ℝ) • p + (-β1) • q + β1 • r := by rw [hb', hc']; simp only [hp, hq, hr]; module
        rw [this, key]; nlinarith
      · rw [eC', eA']
        exact inner_lt _ _ hneg
    exact ⟨R, hR0, hA⟩
  · -- a' < c' : pentagon
    have hA : HasLexCellAt (V8 a a' b b' c c' d) R := by
      refine k14_hc1_frame (V8 a a' b b' c c' d) q r R d hΔ hκn hσn hα1 (by linarith) hβ6 hγ6 hγ61 hbc hcc haa hE
        ?_ hV ?_ ?_ ?_ ?_ ?_
      · intro i
        rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
        · simp only [k6mHCyc1_0, eA]; simp [V8]
        · simp only [k6mHCyc1_1, eC']; simp [V8]
        · simp only [k6mHCyc1_2, eA']; simp [V8]
        · simp only [k6mHCyc1_3, eC]; simp [V8]
        · simp only [k6mHCyc1_4, eO]; simp [V8]
      · rw [eC, eA']
        have := hlit'
        rw [inner_sub_left] at this
        linarith
      · rw [hm0, eC, eA']
        have e1 : fcomb q r R 1 (-1) 0 = (1:ℝ) • q + (-1:ℝ) • r + (0:ℝ) • R := by simp only [fcomb]
        have e2 : c - a' = (0:ℝ) • p + (-β6) • q + (1 - γ6) • r := by rw [ha', hp, hq, hr]; module
        have e3 : fcomb q r R 1 (-1) 0 = (0:ℝ) • p + (1:ℝ) • q + (-1:ℝ) • r := by
          simp only [fcomb]; module
        rw [e3, e2, k6m_ip]
        nlinarith
      · rw [eA', eC']
        have hp2 : 0 < ⟪c' - a', R⟫ := hpos
        rw [inner_sub_left] at hp2
        linarith
      · rw [eC, eO]
        apply inner_lt
        have : c - d = (0:ℝ) • p + (0:ℝ) • q + (1:ℝ) • r := by rw [hr]; module
        rw [this, key]; nlinarith
      · rw [eC', eA, eO]
        have zA := key 1 0 0
        rcases le_or_gt ((1 - α1) * ⟪p, p⟫ - β1 * ⟪p, r⟫) 0 with hA0 | hA0
        · left
          apply inner_lt
          have : c' - a = (α1 - 1) • p + β1 • q + (0:ℝ) • r := by rw [hc', hp, hq]; module
          rw [this, key]; nlinarith
        · right
          apply inner_lt
          have : d - a = (-1:ℝ) • p + (0:ℝ) • q + (0:ℝ) • r := by rw [hp]; module
          rw [this, key]; nlinarith
    exact ⟨R, hR0, hA⟩

end C2
end Type08Sp
end Minimality
