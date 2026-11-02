module

public import Minimality.Type08S.C2K14F

@[expose] public section


/-!
# K14 / G: M `α1 = 1` (view `c - d = -(a - b')/β1`): closed when `⟪a - d, b - d⟫ < 0` and `β6 > 1`; mirror for `γ6 > 1`
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
theorem k14_A1_hasLexCell {a a' b b' c c' d : ℝ³} {β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + (1:ℝ) • (a - d) + β1 • (b - d)) (hb' : b' = d + (1:ℝ) • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hβ1 : 1 < β1) (hβ6 : 1 < β6) (hγ6 : 0 < γ6) (hσ : β1 < β6 + γ6)
    (hM : K6sM a a' b b' c c' d) (hs : ⟪a - d, b - d⟫ < 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨m1, m2, m3⟩ := hM
  set p := a - d with hp
  set q := b - d with hq
  set r := c - d with hr
  have hr0 : r ≠ 0 := by intro h0; apply hdet; rw [h0]; simp [det3_expand]
  have hrr : 0 < ⟪r, r⟫ := real_inner_self_pos.2 hr0
  have hm1 : ⟪p, q⟫ = ⟪p, r⟫ := by
    have : ⟪p, b - c⟫ = ⟪p, q⟫ - ⟪p, r⟫ := by
      rw [← inner_sub_right]; congr 1; rw [hq, hr]; abel
    linarith
  have hm2 : 0 < ⟪q, q⟫ - ⟪q, r⟫ := by
    have e : ⟪c' - d, b - c⟫ = 1 * (⟪p, q⟫ - ⟪p, r⟫) + β1 * (⟪q, q⟫ - ⟪q, r⟫) := by
      have : c' - d = (1:ℝ) • p + β1 • q + (0:ℝ) • r := by rw [hc']; simp only [hp, hq]; module
      have h2 : b - c = (0:ℝ) • p + (1:ℝ) • q + (-1:ℝ) • r := by rw [hq, hr]; module
      rw [this, h2, k6m_ip]; ring
    rw [hm1] at e
    nlinarith
  have hm3 : ⟪q, r⟫ - ⟪r, r⟫ < 0 := by
    have e : ⟪b' - d, b - c⟫ = 1 * (⟪p, q⟫ - ⟪p, r⟫) + β1 * (⟪q, r⟫ - ⟪r, r⟫) := by
      have : b' - d = (1:ℝ) • p + (0:ℝ) • q + β1 • r := by rw [hb']; simp only [hp, hr]; module
      have h2 : b - c = (0:ℝ) • p + (1:ℝ) • q + (-1:ℝ) • r := by rw [hq, hr]; module
      rw [this, h2, k6m_ip]; ring
    rw [hm1] at e
    nlinarith
  have eO : fpoint p q r d (0, 0, 0) = d := by simp [fpoint, fcomb]
  have eA : fpoint p q r d (1, 0, 0) = a := by simp only [fpoint, fcomb, hp]; module
  have eB : fpoint p q r d (0, 1, 0) = b := by simp only [fpoint, fcomb, hq]; module
  have eC : fpoint p q r d (0, 0, 1) = c := by simp only [fpoint, fcomb, hr]; module
  have eC' : fpoint p q r d (1, β1, 0) = c' := by rw [hc']; simp only [fpoint, fcomb, hp, hq]; module
  have eB' : fpoint p q r d (1, 0, β1) = b' := by rw [hb']; simp only [fpoint, fcomb, hp, hr]; module
  have eA' : fpoint p q r d (0, β6, γ6) = a' := by rw [ha']; simp only [fpoint, fcomb, hq, hr]; module
  have hV : ∀ y ∈ V8 a a' b b' c c' d, y = fpoint p q r d (1, 0, 0) ∨ y = fpoint p q r d (1, β1, 0) ∨
      y = fpoint p q r d (0, β6, γ6) ∨ y = fpoint p q r d (0, 0, 1) ∨ y = fpoint p q r d (0, 0, 0) ∨
      y = fpoint p q r d (0, 1, 0) ∨ y = fpoint p q r d (1, 0, β1) := by
    intro y hy
    rw [eA, eC', eA', eC, eO, eB, eB']
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    tauto
  have inner_lt : ∀ X Y : ℝ³, ⟪X - Y, r⟫ < 0 → ⟪X, r⟫ < ⟪Y, r⟫ := by
    intro X Y h; rw [inner_sub_left] at h; linarith
  have inner_le : ∀ X Y : ℝ³, ⟪X, r⟫ ≤ ⟪Y, r⟫ → ⟪X - Y, r⟫ ≤ 0 := by
    intro X Y h; rw [inner_sub_left]; linarith
  have key : ∀ x y z : ℝ, ⟪x • p + y • q + z • r, r⟫ = x * ⟪p, r⟫ + y * ⟪q, r⟫ + z * ⟪r, r⟫ := by
    intro x y z
    simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real]
  have hA : HasLexCellAt (V8 a a' b b' c c' d) r := by
    refine k14_a1_frame (V8 a a' b b' c c' d) p q r d hdet hβ1 hβ6 hγ6 ?_ hV ?_ ?_ ?_
    · intro i
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · simp only [k14A1Cyc_0, eA]; simp [V8]
      · simp only [k14A1Cyc_1, eC']; simp [V8]
      · simp only [k14A1Cyc_2, eA']; simp [V8]
      · simp only [k14A1Cyc_3, eC]; simp [V8]
      · simp only [k14A1Cyc_4, eO]; simp [V8]
    · rw [eA, eO]
      apply inner_lt
      have : a - d = (1:ℝ) • p + (0:ℝ) • q + (0:ℝ) • r := by rw [hp]; module
      rw [this, key]; linarith
    · rw [eO, eC]
      apply inner_lt
      have : d - c = (0:ℝ) • p + (0:ℝ) • q + (-1:ℝ) • r := by rw [hr]; module
      rw [this, key]; linarith
    · intro h1 h2 h3
      rw [eA', eC] at h1
      rw [eA', eC'] at h2
      rw [eA, eC'] at h3
      have g1 := inner_le _ _ h1
      have g2 := inner_le _ _ h2
      have g3 := inner_le _ _ h3
      have e1 : a' - c = (0:ℝ) • p + β6 • q + (γ6 - 1) • r := by rw [ha', hp, hq, hr]; module
      have e2 : a' - c' = (-1:ℝ) • p + (β6 - β1) • q + γ6 • r := by rw [ha', hc', hp, hq, hr]; module
      have e3 : a - c' = (0:ℝ) • p + (-β1) • q + (0:ℝ) • r := by rw [hc', hp, hq]; module
      rw [e2, key] at g2
      rw [e3, key] at g3
      have hqr : 0 ≤ ⟪q, r⟫ := by nlinarith
      rw [hp, hq] at hm1
      have hs' : ⟪p, r⟫ < 0 := by rw [← hm1]; exact hs
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ β6 - β1 + γ6) hqr, mul_pos hγ6 (by linarith : (0:ℝ) < ⟪r, r⟫ - ⟪q, r⟫)]
  exact ⟨r, hr0, hA⟩

end C2
end Type08Sp
end Minimality
