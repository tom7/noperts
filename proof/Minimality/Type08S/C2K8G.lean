module

public import Minimality.Type08S.C2K8F

@[expose] public section

/-! # K8G: level-face cells `Q2⁺`, `Q2⁻` (`C = 0`) with the tie `s = 0` decided by a tilt in the cone `v1, v2 > 0`. -/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

set_option maxHeartbeats 3200000 in
/-- **`Q2⁺` with a caller tilt**: `β6 > 1`, `C = 0`, `s₁ ≥ 0`; a tie `s₁ = 0` is decided by `w(a') > w(c')`. -/
theorem k8q2p_hasLexCellAt (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0)
    {β1 γ4 β6 γ6 u1 u2 t1 t2 : ℝ} (hβ1 : 0 < β1) (hγ4 : 0 < γ4) (hβ6 : 1 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hs : 1 < β6 + γ6) (hut : u1 * t2 - u2 * t1 ≠ 0)
    (hcone : ∀ lam : ℝ, 0 < lam → lam < 1 → 0 < u1 + lam * t1 ∧ 0 < u2 + lam * t2)
    (hC : ⟪q, r⟫ = 0) (hs1 : 0 ≤ (β6 - β1) * ⟪q, r⟫ + γ6 * ⟪r, r⟫ - ⟪p, r⟫)
    (hw : (β6 - β1) * ⟪q, r⟫ + γ6 * ⟪r, r⟫ - ⟪p, r⟫ = 0 → ∀ lam : ℝ, 0 < lam → lam < 1 →
      0 < (u1 + lam * t1) * ⟪fpoint p q r d (0, β6, γ6) - fpoint p q r d (1, β1, 0), p⟫ +
        (u2 + lam * t2) * ⟪fpoint p q r d (0, β6, γ6) - fpoint p q r d (1, β1, 0), q⟫)
    (hmem : ∀ i, fpoint p q r d (k3q2pCyc γ4 β1 β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint p q r d (0, 0, 1) ∨ y = fpoint p q r d (0, 0, 0) ∨
      y = fpoint p q r d (1, 0, 0) ∨ y = fpoint p q r d (1, β1, 0) ∨ y = fpoint p q r d (0, β6, γ6) ∨
      y = fpoint p q r d (0, 1, 0) ∨ y = fpoint p q r d (1, 0, γ4)) :
    HasLexCellAt V r := by
  set Y := k3q2pCyc γ4 β1 β6 γ6 with hY
  have hr0 : r ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  have hA : 0 < ⟪r, r⟫ := real_inner_self_pos.2 hr0
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint p q r d t, r⟫ = ⟪d, r⟫ + t.1 * ⟪p, r⟫ + t.2.1 * ⟪q, r⟫ + t.2.2 * ⟪r, r⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  refine k8_cell_gen V p q r d hΔ (by norm_num) Y (k3q2pCyc_inj hγ4 hβ1 hβ6 hγ6 hγ61) hut hmem ?_ ?_ ?_
  · intro lam hl0 hl1 D hD
    obtain ⟨h1, h2⟩ := hcone lam hl0 hl1
    exact k3q2p_cyc hD hγ4 hβ1 hβ6 hγ6 hγ61 hs h1 h2
  · intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 4 (by simp only [hY, k3q2pCyc, pc5_4])).elim
    · exact ⟨_, rfl, fun lam hl0 hl1 D hD => by
        obtain ⟨h1, h2⟩ := hcone lam hl0 hl1
        exact (k3q2p_rest hD hγ4 hβ1 hβ6 hγ6 hγ61 hs h1 h2).1⟩
    · exact (hyx 1 (by simp only [hY, k3q2pCyc, pc5_1])).elim
    · exact (hyx 2 (by simp only [hY, k3q2pCyc, pc5_2])).elim
    · exact (hyx 3 (by simp only [hY, k3q2pCyc, pc5_3])).elim
    · exact ⟨_, rfl, fun lam hl0 hl1 D hD => by
        obtain ⟨h1, h2⟩ := hcone lam hl0 hl1
        exact (k3q2p_rest hD hγ4 hβ1 hβ6 hγ6 hγ61 hs h1 h2).2⟩
    · exact (hyx 0 (by simp only [hY, k3q2pCyc, pc5_0])).elim
  · intro lam hl0 hl1 w hwd hw'
    refine lexUni5_top _ _ hw' ?_ ?_ ?_
    · left; simp only [hY, k3q2pCyc, pc5_1, pc5_0, hz]; nlinarith [mul_pos hγ4 hA]
    · rcases hs1.lt_or_eq with h | h
      · left; simp only [hY, k3q2pCyc, pc5_2, pc5_3, hz]; nlinarith
      · right; refine ⟨?_, ?_⟩
        · simp only [hY, k3q2pCyc, pc5_2, pc5_3, hz]; nlinarith
        · rw [hwd, hwd]
          have := k8_wdiff p q r d (1, β1, 0) (0, β6, γ6) (u1 + lam * t1) (u2 + lam * t2)
          simp only [hY, k3q2pCyc, pc5_2, pc5_3]
          have h5 := hw h.symm lam hl0 hl1
          have h6 : ⟪fpoint p q r d (1, β1, 0) - fpoint p q r d (0, β6, γ6), p⟫ =
              -⟪fpoint p q r d (0, β6, γ6) - fpoint p q r d (1, β1, 0), p⟫ := by
            rw [← inner_neg_left, neg_sub]
          have h7 : ⟪fpoint p q r d (1, β1, 0) - fpoint p q r d (0, β6, γ6), q⟫ =
              -⟪fpoint p q r d (0, β6, γ6) - fpoint p q r d (1, β1, 0), q⟫ := by
            rw [← inner_neg_left, neg_sub]
          rw [h6, h7] at this
          linarith
    · left; simp only [hY, k3q2pCyc, pc5_3, pc5_4, hz]; nlinarith [mul_pos (sub_pos.2 hγ61) hA]

set_option maxHeartbeats 3200000 in
/-- **`Q2⁻` with a caller tilt**: `β6 < 1`, `C = 0`, `s₂ ≥ 0`; a tie `s₂ = 0` is decided by `w(b) > w(c')`. -/
theorem k8q2m_hasLexCellAt (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0)
    {β1 γ4 β6 γ6 u1 u2 t1 t2 : ℝ} (hβ1 : 0 < β1) (hγ4 : 0 < γ4) (hβ6p : 0 < β6) (hβ6 : β6 < 1) (hγ6 : 0 < γ6)
    (hγ61 : γ6 < 1) (hs : 1 < β6 + γ6) (hut : u1 * t2 - u2 * t1 ≠ 0)
    (hcone : ∀ lam : ℝ, 0 < lam → lam < 1 → 0 < u1 + lam * t1 ∧ 0 < u2 + lam * t2)
    (hC : ⟪q, r⟫ = 0) (hs2 : 0 ≤ (1 - β1) * ⟪q, r⟫ - ⟪p, r⟫)
    (hw : (1 - β1) * ⟪q, r⟫ - ⟪p, r⟫ = 0 → ∀ lam : ℝ, 0 < lam → lam < 1 →
      0 < (u1 + lam * t1) * ⟪fpoint p q r d (0, 1, 0) - fpoint p q r d (1, β1, 0), p⟫ +
        (u2 + lam * t2) * ⟪fpoint p q r d (0, 1, 0) - fpoint p q r d (1, β1, 0), q⟫)
    (hmem : ∀ i, fpoint p q r d (k3q2mCyc γ4 β1 β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint p q r d (0, 0, 1) ∨ y = fpoint p q r d (0, 0, 0) ∨
      y = fpoint p q r d (1, 0, 0) ∨ y = fpoint p q r d (1, β1, 0) ∨ y = fpoint p q r d (0, β6, γ6) ∨
      y = fpoint p q r d (0, 1, 0) ∨ y = fpoint p q r d (1, 0, γ4)) :
    HasLexCellAt V r := by
  set Y := k3q2mCyc γ4 β1 β6 γ6 with hY
  have hr0 : r ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  have hA : 0 < ⟪r, r⟫ := real_inner_self_pos.2 hr0
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint p q r d t, r⟫ = ⟪d, r⟫ + t.1 * ⟪p, r⟫ + t.2.1 * ⟪q, r⟫ + t.2.2 * ⟪r, r⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  refine k8_cell_gen V p q r d hΔ (by norm_num) Y (k3q2mCyc_inj hγ4 hβ1 hβ6p hβ6 hγ6 hγ61) hut hmem ?_ ?_ ?_
  · intro lam hl0 hl1 D hD
    obtain ⟨h1, h2⟩ := hcone lam hl0 hl1
    exact k3q2m_cyc hD hγ4 hβ1 hβ6p hβ6 hγ6 hγ61 hs h1 h2
  · intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 5 (by simp only [hY, k3q2mCyc, pc6_5])).elim
    · exact ⟨_, rfl, fun lam hl0 hl1 D hD => by
        obtain ⟨h1, h2⟩ := hcone lam hl0 hl1
        exact k3q2m_rest hD hγ4 hβ1 hβ6p hβ6 hγ6 hγ61 hs h1 h2⟩
    · exact (hyx 1 (by simp only [hY, k3q2mCyc, pc6_1])).elim
    · exact (hyx 2 (by simp only [hY, k3q2mCyc, pc6_2])).elim
    · exact (hyx 4 (by simp only [hY, k3q2mCyc, pc6_4])).elim
    · exact (hyx 3 (by simp only [hY, k3q2mCyc, pc6_3])).elim
    · exact (hyx 0 (by simp only [hY, k3q2mCyc, pc6_0])).elim
  · intro lam hl0 hl1 w hwd hw'
    refine lexUni6_top2 _ w hw' ?_ ?_ ?_ ?_
    · left; simp only [hY, k3q2mCyc, pc6_1, pc6_0, hz]; nlinarith [mul_pos hγ4 hA]
    · rcases hs2.lt_or_eq with h | h
      · left; simp only [hY, k3q2mCyc, pc6_2, pc6_3, hz]; nlinarith
      · right; refine ⟨?_, ?_⟩
        · simp only [hY, k3q2mCyc, pc6_2, pc6_3, hz]; nlinarith
        · rw [hwd, hwd]
          have := k8_wdiff p q r d (1, β1, 0) (0, 1, 0) (u1 + lam * t1) (u2 + lam * t2)
          simp only [hY, k3q2mCyc, pc6_2, pc6_3]
          have h5 := hw h.symm lam hl0 hl1
          have h6 : ⟪fpoint p q r d (1, β1, 0) - fpoint p q r d (0, 1, 0), p⟫ =
              -⟪fpoint p q r d (0, 1, 0) - fpoint p q r d (1, β1, 0), p⟫ := by
            rw [← inner_neg_left, neg_sub]
          have h7 : ⟪fpoint p q r d (1, β1, 0) - fpoint p q r d (0, 1, 0), q⟫ =
              -⟪fpoint p q r d (0, 1, 0) - fpoint p q r d (1, β1, 0), q⟫ := by
            rw [← inner_neg_left, neg_sub]
          rw [h6, h7] at this
          linarith
    · left; simp only [hY, k3q2mCyc, pc6_3, pc6_4, hz]; nlinarith [mul_pos hγ6 hA]
    · left; left; simp only [hY, k3q2mCyc, pc6_4, pc6_5, hz]; nlinarith [mul_pos (sub_pos.2 hγ61) hA]

/-- Tilt segment in the cone `v1, v2 > 0` making `x v1 + y v2 > 0` (needs `0 < x ∨ 0 < y`). -/
theorem k8_tilt2 (x y : ℝ) (h : 0 < x ∨ 0 < y) : ∃ u1 u2 t1 t2 : ℝ, u1 * t2 - u2 * t1 ≠ 0 ∧
    (∀ lam : ℝ, 0 < lam → lam < 1 → 0 < u1 + lam * t1 ∧ 0 < u2 + lam * t2) ∧
    ∀ lam : ℝ, 0 < lam → lam < 1 → 0 < (u1 + lam * t1) * x + (u2 + lam * t2) * y := by
  by_cases hy : 0 < y
  · -- v = (η (1 + lam), 1)
    obtain ⟨η, hη, hηx⟩ := k8_eta (x := x) hy.ne'
    refine ⟨η, 1, η, 0, by simpa using hη.ne', fun lam hl0 hl1 => ⟨by nlinarith, by simp⟩, ?_⟩
    intro lam hl0 hl1
    have hay : |y| = y := abs_of_pos hy
    have h1 : |(η + lam * η) * x| ≤ 2 * η * |x| := by
      rw [abs_mul, abs_of_pos (by nlinarith : 0 < η + lam * η)]
      have := abs_nonneg x
      nlinarith [mul_nonneg (mul_pos hη (sub_pos.2 hl1)).le this]
    have := neg_abs_le ((η + lam * η) * x)
    nlinarith
  · have hx : 0 < x := h.resolve_right hy
    push_neg at hy
    by_cases hy0 : y = 0
    · refine ⟨1, 1, 1, 0, by simp, fun lam hl0 hl1 => ⟨by linarith, by simp⟩, ?_⟩
      intro lam hl0 hl1
      rw [hy0]; nlinarith
    · obtain ⟨η, hη, hηx⟩ := k8_eta (x := y) hy0
      -- v = (|x|-ish, ...): take v = (1, η' (1 + lam)) with η' small relative to x
      have hy1 : y < 0 := lt_of_le_of_ne hy hy0
      obtain ⟨η2, hη2, hη2x⟩ := k8_eta (x := y) (y := x) hx.ne'
      refine ⟨1, η2, 0, η2, by simpa using hη2.ne', fun lam hl0 hl1 => ⟨by simp, by nlinarith⟩, ?_⟩
      intro lam hl0 hl1
      have hay : |x| = x := abs_of_pos hx
      have h1 : |(η2 + lam * η2) * y| ≤ 2 * η2 * |y| := by
        rw [abs_mul, abs_of_pos (by nlinarith : 0 < η2 + lam * η2)]
        have := abs_nonneg y
        nlinarith [mul_nonneg (mul_pos hη2 (sub_pos.2 hl1)).le this]
      have := neg_abs_le ((η2 + lam * η2) * y)
      nlinarith

end C2
end Type08Sp
end Minimality
