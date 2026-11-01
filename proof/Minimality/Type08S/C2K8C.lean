module

public import Minimality.Type08S.C2K8B

@[expose] public section

/-! # K8C: cells `Q1⁻` and `Q4⁻` (`β6 < 1`, `C > 0`) with the tie `s₂ = 0` decided by the tilt. -/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

set_option maxHeartbeats 3200000 in
/-- **`Q1⁻` with a caller tilt**: `β6 < 1`, `C > 0`, `s₂ ≥ 0`; a tie `s₂ = 0` is decided by `w(b) > w(c')`. -/
theorem k8q1m_hasLexCellAt (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0)
    {β1 γ4 β6 γ6 u1 u2 t1 t2 : ℝ} (hβ1 : 0 < β1) (hγ4 : 0 < γ4) (hβ6p : 0 < β6) (hβ6 : β6 < 1) (hγ6 : 0 < γ6)
    (hs : 1 < β6 + γ6) (hut : u1 * t2 - u2 * t1 ≠ 0)
    (hcone : ∀ lam : ℝ, 0 < lam → lam < 1 → 0 < u1 + lam * t1 ∧ u2 + lam * t2 < 0)
    (hC : 0 < ⟪q, r⟫) (hs2 : 0 ≤ (1 - β1) * ⟪q, r⟫ - ⟪p, r⟫)
    (hw : (1 - β1) * ⟪q, r⟫ - ⟪p, r⟫ = 0 → ∀ lam : ℝ, 0 < lam → lam < 1 →
      0 < (u1 + lam * t1) * ⟪fpoint p q r d (0, 1, 0) - fpoint p q r d (1, β1, 0), p⟫ +
        (u2 + lam * t2) * ⟪fpoint p q r d (0, 1, 0) - fpoint p q r d (1, β1, 0), q⟫)
    (hmem : ∀ i, fpoint p q r d (k3q1mCyc β1 β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint p q r d (0, 0, 1) ∨ y = fpoint p q r d (0, 0, 0) ∨
      y = fpoint p q r d (1, 0, 0) ∨ y = fpoint p q r d (1, β1, 0) ∨ y = fpoint p q r d (0, β6, γ6) ∨
      y = fpoint p q r d (0, 1, 0) ∨ y = fpoint p q r d (1, 0, γ4)) :
    HasLexCellAt V r := by
  set Y := k3q1mCyc β1 β6 γ6 with hY
  have hr0 : r ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  have hA : 0 < ⟪r, r⟫ := real_inner_self_pos.2 hr0
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint p q r d t, r⟫ = ⟪d, r⟫ + t.1 * ⟪p, r⟫ + t.2.1 * ⟪q, r⟫ + t.2.2 * ⟪r, r⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  refine k8_cell_gen V p q r d hΔ (by norm_num) Y (k3q1mCyc_inj hβ1 hβ6p hβ6 hγ6) hut hmem ?_ ?_ ?_
  · intro lam hl0 hl1 D hD
    obtain ⟨h1, h2⟩ := hcone lam hl0 hl1
    exact k3q1m_cyc hD hβ1 hβ6p hβ6 hγ6 hs h1 h2
  · intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [hY, k3q1mCyc, pc6_0])).elim
    · exact (hyx 1 (by simp only [hY, k3q1mCyc, pc6_1])).elim
    · exact (hyx 2 (by simp only [hY, k3q1mCyc, pc6_2])).elim
    · exact (hyx 3 (by simp only [hY, k3q1mCyc, pc6_3])).elim
    · exact (hyx 5 (by simp only [hY, k3q1mCyc, pc6_5])).elim
    · exact (hyx 4 (by simp only [hY, k3q1mCyc, pc6_4])).elim
    · exact ⟨_, rfl, fun lam hl0 hl1 D hD => by
        obtain ⟨h1, h2⟩ := hcone lam hl0 hl1
        exact k3q1m_rest hD hβ1 hγ4 hβ6p hβ6 hγ6 hs h1 h2⟩
  · intro lam hl0 hl1 w hwd hw'
    refine lexUni6_top2 _ w hw' ?_ ?_ ?_ ?_
    · left; simp only [hY, k3q1mCyc, pc6_0, pc6_1, hz]; nlinarith
    · left; simp only [hY, k3q1mCyc, pc6_2, pc6_3, hz]; nlinarith [mul_pos hβ1 hC]
    · rcases hs2.lt_or_eq with h | h
      · left; simp only [hY, k3q1mCyc, pc6_3, pc6_4, hz]; nlinarith
      · right; refine ⟨?_, ?_⟩
        · simp only [hY, k3q1mCyc, pc6_3, pc6_4, hz]; nlinarith
        · rw [hwd, hwd]
          have := k8_wdiff p q r d (0, 1, 0) (1, β1, 0) (u1 + lam * t1) (u2 + lam * t2)
          simp only [hY, k3q1mCyc, pc6_3, pc6_4]
          linarith [hw h.symm lam hl0 hl1]
    · rcases le_total ⟪q, r⟫ ⟪r, r⟫ with h | h
      · left; left; simp only [hY, k3q1mCyc, pc6_4, pc6_5, hz]
        nlinarith [mul_pos (sub_pos.2 hs) hC, mul_nonneg hγ6.le (sub_nonneg.2 h)]
      · right; left; simp only [hY, k3q1mCyc, pc6_0, pc6_5, hz]
        nlinarith [mul_pos (sub_pos.2 hs) hA, mul_nonneg hβ6p.le (sub_nonneg.2 h)]

set_option maxHeartbeats 3200000 in
/-- **`Q4⁻` with a caller tilt** (`C > 0` only): `β6 < 1`, `s₂ ≤ 0`; a tie `s₂ = 0` is decided by `w(b) < w(c')`. -/
theorem k8q4m_hasLexCellAt (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0)
    {β1 γ4 β6 γ6 u1 u2 t1 t2 : ℝ} (hβ1 : 0 < β1) (hγ4 : 0 < γ4) (hβ6p : 0 < β6) (hβ6 : β6 < 1) (hγ6 : 0 < γ6)
    (hs : 1 < β6 + γ6) (hut : u1 * t2 - u2 * t1 ≠ 0)
    (hcone : ∀ lam : ℝ, 0 < lam → lam < 1 → u1 + lam * t1 < 0 ∧ u2 + lam * t2 < 0)
    (hC : 0 < ⟪q, r⟫) (hs2 : (1 - β1) * ⟪q, r⟫ - ⟪p, r⟫ ≤ 0)
    (hw : (1 - β1) * ⟪q, r⟫ - ⟪p, r⟫ = 0 → ∀ lam : ℝ, 0 < lam → lam < 1 →
      (u1 + lam * t1) * ⟪fpoint p q r d (0, 1, 0) - fpoint p q r d (1, β1, 0), p⟫ +
        (u2 + lam * t2) * ⟪fpoint p q r d (0, 1, 0) - fpoint p q r d (1, β1, 0), q⟫ < 0)
    (hmem : ∀ i, fpoint p q r d (k3q4mCyc γ4 β1 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint p q r d (0, 0, 1) ∨ y = fpoint p q r d (0, 0, 0) ∨
      y = fpoint p q r d (1, 0, 0) ∨ y = fpoint p q r d (1, β1, 0) ∨ y = fpoint p q r d (0, β6, γ6) ∨
      y = fpoint p q r d (0, 1, 0) ∨ y = fpoint p q r d (1, 0, γ4)) :
    HasLexCellAt V r := by
  set Y := k3q4mCyc γ4 β1 with hY
  have hr0 : r ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  have hA : 0 < ⟪r, r⟫ := real_inner_self_pos.2 hr0
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint p q r d t, r⟫ = ⟪d, r⟫ + t.1 * ⟪p, r⟫ + t.2.1 * ⟪q, r⟫ + t.2.2 * ⟪r, r⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  refine k8_cell_gen V p q r d hΔ (by norm_num) Y (k3q4mCyc_inj hγ4 hβ1) hut hmem ?_ ?_ ?_
  · intro lam hl0 hl1 D hD
    obtain ⟨h1, h2⟩ := hcone lam hl0 hl1
    exact k3q4m_cyc hD hγ4 hβ1 h1 h2
  · intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, rfl, fun lam hl0 hl1 D hD => by
        obtain ⟨h1, h2⟩ := hcone lam hl0 hl1
        exact (k3q4m_rest hD hγ4 hβ1 hβ6p hβ6 hγ6 hs h1 h2).1⟩
    · exact (hyx 0 (by simp only [hY, k3q4mCyc, pc5_0])).elim
    · exact (hyx 1 (by simp only [hY, k3q4mCyc, pc5_1])).elim
    · exact (hyx 3 (by simp only [hY, k3q4mCyc, pc5_3])).elim
    · exact ⟨_, rfl, fun lam hl0 hl1 D hD => by
        obtain ⟨h1, h2⟩ := hcone lam hl0 hl1
        exact (k3q4m_rest hD hγ4 hβ1 hβ6p hβ6 hγ6 hs h1 h2).2⟩
    · exact (hyx 4 (by simp only [hY, k3q4mCyc, pc5_4])).elim
    · exact (hyx 2 (by simp only [hY, k3q4mCyc, pc5_2])).elim
  · intro lam hl0 hl1 w hwd hw'
    have m0 : (2 : ZMod 5) - 0 = 2 := by decide
    have m1 : (2 : ZMod 5) - 1 = 1 := by decide
    have m2 : (2 : ZMod 5) - 2 = 0 := by decide
    have m3 : (2 : ZMod 5) - 3 = 4 := by decide
    have m4 : (2 : ZMod 5) - 4 = 3 := by decide
    apply lexUni_rev_shift (2 : ZMod 5)
    refine lexUni5_top _ _ (fun i j h1 h2 => sub_right_injective (hw' _ _ h1 h2)) ?_ ?_ ?_
    · left; simp only [m1, m0, hY, k3q4mCyc, pc5_1, pc5_2, hz]; nlinarith [mul_pos hγ4 hA]
    · left; simp only [m2, m3, hY, k3q4mCyc, pc5_0, pc5_4, hz]; nlinarith
    · rcases hs2.lt_or_eq with h | h
      · left; simp only [m3, m4, hY, k3q4mCyc, pc5_4, pc5_3, hz]; nlinarith
      · right; refine ⟨?_, ?_⟩
        · simp only [m3, m4, hY, k3q4mCyc, pc5_4, pc5_3, hz]; nlinarith
        · rw [hwd, hwd]
          have := k8_wdiff p q r d (0, 1, 0) (1, β1, 0) (u1 + lam * t1) (u2 + lam * t2)
          simp only [m3, m4, hY, k3q4mCyc, pc5_4, pc5_3]
          linarith [hw h lam hl0 hl1]

end C2
end Type08Sp
end Minimality
