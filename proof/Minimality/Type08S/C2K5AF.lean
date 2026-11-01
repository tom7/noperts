module

public import Minimality.Type08S.C2K5AE

@[expose] public section


/-!
# K5a / F: generic frame cell `(a, d, x, a', x')` at `r = a - d` (cell 1 of QCE2; cell 2 by swapping `p, q`).
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem k5a_interval {β6 γ6 : ℝ} (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hs : 1 < β6 + γ6) :
    ∃ lo hi : ℝ, lo < hi ∧ 0 ≤ lo ∧ ∀ lam, lo < lam → lam < hi →
      0 < lam ∧ 1 - β6 < lam * γ6 ∧ (1 - γ6) * lam + β6 * (-1) < 0 := by
  rcases lt_or_ge γ6 1 with h1 | h1
  · have hhi0 : 0 < β6 / (1 - γ6) := div_pos hβ6 (by linarith)
    have hβγ1 : (1 - β6) / γ6 < 1 := by
      rw [div_lt_one hγ6]; linarith
    have hβγ2 : (1 - β6) / γ6 < β6 / (1 - γ6) := by
      rw [div_lt_div_iff₀ hγ6 (by linarith)]; nlinarith
    refine ⟨max 0 ((1 - β6) / γ6), min 1 (β6 / (1 - γ6)),
      max_lt (lt_min one_pos hhi0) (lt_min hβγ1 hβγ2), le_max_left _ _, fun lam hl0 hl1 => ?_⟩
    have hlam0 : 0 < lam := lt_of_le_of_lt (le_max_left _ _) hl0
    have hlam1 : (1 - β6) / γ6 < lam := lt_of_le_of_lt (le_max_right _ _) hl0
    have hlam3 : lam < β6 / (1 - γ6) := lt_of_lt_of_le hl1 (min_le_right _ _)
    refine ⟨hlam0, ?_, ?_⟩
    · have := (div_lt_iff₀ hγ6).1 hlam1; linarith
    · have := (lt_div_iff₀ (by linarith : 0 < 1 - γ6)).1 hlam3; linarith
  · refine ⟨max 0 ((1 - β6) / γ6), 1 + max 0 ((1 - β6) / γ6), by linarith [le_max_left 0 ((1 - β6) / γ6)],
      le_max_left _ _, fun lam hl0 hl1 => ?_⟩
    have hlam0 : 0 < lam := lt_of_le_of_lt (le_max_left _ _) hl0
    have hlam1 : (1 - β6) / γ6 < lam := lt_of_le_of_lt (le_max_right _ _) hl0
    refine ⟨hlam0, ?_, ?_⟩
    · have := (div_lt_iff₀ hγ6).1 hlam1; linarith
    · nlinarith

set_option maxHeartbeats 1600000 in
/-- **Generic cell `(a, d, x, a', x')` at `r = a - d`**, `x = (1,0,0)`, `x' = (0,1,α4)`, rest `y = (0,1,0)`,
`y' = (1,0,α1)`, `a' = (β6, γ6, 0)`.  Inner-product hypotheses: `⟪q,r⟫ = ⟪p,r⟫ + m ⟪r,r⟫`, `m > 0`,
`1 < m + α4`, `hcond : 0 < β6 m + α4 (β6+γ6) - (β6+γ6-1)`. -/
theorem k5a_core_hasLexCellAt (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0)
    {α1 α4 β6 γ6 m : ℝ} (hα1 : 0 < α1) (hα4 : 0 < α4) (hβ6 : 0 < β6)
    (hγ6 : 0 < γ6) (hs : 1 < β6 + γ6)
    (hm : 0 < m) (hmα : 1 < m + α4) (hcond : 0 < β6 * m + α4 * (β6 + γ6) - (β6 + γ6 - 1))
    (hC : ⟪q, r⟫ = ⟪p, r⟫ + m * ⟪r, r⟫)
    (hmem : ∀ i, fpoint p q r d (kCyc β6 γ6 α4 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint p q r d (0, 0, 1) ∨ y = fpoint p q r d (0, 0, 0) ∨
      y = fpoint p q r d (1, 0, 0) ∨ y = fpoint p q r d (β6, γ6, 0) ∨ y = fpoint p q r d (0, 1, α4) ∨
      y = fpoint p q r d (0, 1, 0) ∨ y = fpoint p q r d (1, 0, α1)) :
    HasLexCellAt V r := by
  set Y := kCyc β6 γ6 α4 with hY
  have hr0 : r ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  have hA : 0 < ⟪r, r⟫ := real_inner_self_pos.2 hr0
  obtain ⟨lo, hi, hlh, -, hlam⟩ := k5a_interval hβ6 hγ6 hs
  obtain ⟨lam, hl0, hl1, hsep⟩ := exists_sep_tilt p q r d hΔ Y (kCyc_inj hβ6 hγ6)
    (u1 := 0) (u2 := -1) (t1 := 1) (t2 := 0) (by norm_num) hlh
  obtain ⟨hlam0, hlam1, hlam3⟩ := hlam lam hl0 hl1
  set vv := fcomb p q r (0 + lam * 1) (-1 + lam * 0) 0 with hvv
  have hv1 : 0 < 0 + lam * 1 := by linarith
  have hv2 : -1 + lam * 0 < 0 := by linarith
  have hcone : (1 - γ6) * (0 + lam * 1) + β6 * (-1 + lam * 0) < 0 := by nlinarith
  have hc1 : 0 < γ6 * (0 + lam * 1) + (1 - β6) * (-1 + lam * 0) := by nlinarith
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint p q r d t, r⟫ = ⟪d, r⟫ + t.1 * ⟪p, r⟫ + t.2.1 * ⟪q, r⟫ + t.2.2 * ⟪r, r⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  have hinj := hsep
  have hlexY : LexUni (fun i => ⟪fpoint p q r d (Y i), r⟫) (fun i => ⟪fpoint p q r d (Y i), vv⟫) := by
    set zz : ZMod 5 → ℝ := fun i => ⟪fpoint p q r d (Y i), r⟫ with hzz
    set ww : ZMod 5 → ℝ := fun i => ⟪fpoint p q r d (Y i), vv⟫ with hww
    have z0 : zz 0 = ⟪d, r⟫ + ⟪r, r⟫ := by simp only [hzz, hY, kCyc, pc5_0, hz]; ring
    have z1 : zz 1 = ⟪d, r⟫ := by simp only [hzz, hY, kCyc, pc5_1, hz]; ring
    have z2 : zz 2 = ⟪d, r⟫ + ⟪p, r⟫ := by simp only [hzz, hY, kCyc, pc5_2, hz]; ring
    have z3 : zz 3 = ⟪d, r⟫ + β6 * ⟪p, r⟫ + γ6 * ⟪q, r⟫ := by simp only [hzz, hY, kCyc, pc5_3, hz]; ring
    have z4 : zz 4 = ⟪d, r⟫ + ⟪q, r⟫ + α4 * ⟪r, r⟫ := by simp only [hzz, hY, kCyc, pc5_4, hz]; ring
    rw [hC] at z3 z4
    have h10 : LexLt (zz 1, ww 1) (zz 0, ww 0) := Or.inl (by rw [z0, z1]; linarith)
    rcases lt_or_ge (⟪p, r⟫) 0 with hB | hB
    · -- B < 0: x < d
      have h21 : LexLt (zz 2, ww 2) (zz 1, ww 1) := Or.inl (by rw [z2, z1]; linarith)
      have hne : ∀ i j : ZMod 5, i ≠ j → (zz i, ww i) ≠ (zz j, ww j) := fun i j hij h =>
        hij (hinj i j (congrArg Prod.fst h) (congrArg Prod.snd h))
      rcases lexLt_total (hne 3 2 (by decide)) with h32 | h23
      · exact lexUni5_adj zz ww hinj h10 h21 (Or.inl h32)
      · rcases lexLt_total (hne 3 4 (by decide)) with h34 | h43
        · exact lexUni5_adj zz ww hinj h10 h21 (Or.inr h34)
        · have h04 : LexLt (zz 0, ww 0) (zz 4, ww 4) := by
            left
            by_contra hcon
            have h43' : zz 4 ≤ zz 3 := by
              rcases h43 with h | ⟨h, -⟩
              · exact h.le
              · exact h.le
            rw [z0, z4] at hcon
            rw [z3, z4] at h43'
            push Not at hcon
            have e1 : 0 ≤ -⟪p, r⟫ - (m + α4 - 1) * ⟪r, r⟫ := by nlinarith
            nlinarith [mul_pos hA hcond, mul_nonneg (by linarith : 0 ≤ β6 + γ6 - 1) e1]
          exact k5a_lexUni5_three zz ww hinj h10 h04 h23 h43
    · -- B ≥ 0: L2
      have hs1 : LexLt (zz 1, ww 1) (zz 0, ww 0) := h10
      apply lexUni_shift_k 1
      refine lexUni5_two _ _ (fun i j h1 h2 => add_right_cancel (hinj _ _ h1 h2)) ?_ ?_ ?_
      · left; simp only [f0, f1, f2, f3, f4, z2, z3]
        nlinarith [mul_nonneg (by linarith : 0 ≤ β6 + γ6 - 1) hB, mul_pos hγ6 (mul_pos hm hA)]
      · left; simp only [f0, f1, f2, f3, f4, z0, z4]
        nlinarith [mul_pos (by linarith : 0 < m + α4 - 1) hA]
      · right; simp only [f0, f1, f2, f3, f4]; exact h10
  have n0 : -(0 : ZMod 5) = 0 := by decide
  have n1 : -(1 : ZMod 5) = 4 := by decide
  have n2 : -(2 : ZMod 5) = 3 := by decide
  have n3 : -(3 : ZMod 5) = 2 := by decide
  have n4 : -(4 : ZMod 5) = 1 := by decide
  have hcyc0 := fun D (hD : 0 < D) => k2_cyc (v3 := 0) (α4 := α4) hD hβ6 hγ6 hs hv1 hv2
  have hr0' := fun D (hD : 0 < D) => k5a_rest0 (v3 := 0) (α4 := α4) hD hα4 hβ6 hγ6 hs hv1 hv2 hcone
  have hr1' := fun D (hD : 0 < D) => k5a_rest1 (α4 := α4) (v3 := 0) hD hα1 hβ6 hγ6 hs hv2 hc1
  rcases hΔ.lt_or_gt with hneg | hpos
  · have hD : 0 < -det3 p q r := by linarith
    refine ⟨5, inferInstance, fun i => fpoint p q r d (Y (-i)), vv, ?_⟩
    refine lexCell_coord V p q r d (by norm_num) (fun i => Y (-i)) (0 + lam * 1, -1 + lam * 0, 0)
      (fun i => hmem (-i)) (hcyc_rev (hcyc0 _ hD)) ?_ (lexUni_neg hlexY)
    intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [n0, hY, kCyc, pc5_0])).elim
    · exact (hyx 4 (by simp only [n4, hY, kCyc, pc5_1])).elim
    · exact (hyx 3 (by simp only [n3, hY, kCyc, pc5_2])).elim
    · exact (hyx 2 (by simp only [n2, hY, kCyc, pc5_3])).elim
    · exact (hyx 1 (by simp only [n1, hY, kCyc, pc5_4])).elim
    · exact ⟨_, rfl, hrest_rev (hr0' _ hD)⟩
    · exact ⟨_, rfl, hrest_rev (hr1' _ hD)⟩
  · refine ⟨5, inferInstance, fun i => fpoint p q r d (Y i), vv, ?_⟩
    refine lexCell_coord V p q r d (by norm_num) Y (0 + lam * 1, -1 + lam * 0, 0) hmem
      (hcyc0 _ hpos) ?_ hlexY
    intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [hY, kCyc, pc5_0])).elim
    · exact (hyx 1 (by simp only [hY, kCyc, pc5_1])).elim
    · exact (hyx 2 (by simp only [hY, kCyc, pc5_2])).elim
    · exact (hyx 3 (by simp only [hY, kCyc, pc5_3])).elim
    · exact (hyx 4 (by simp only [hY, kCyc, pc5_4])).elim
    · exact ⟨_, rfl, hr0' _ hpos⟩
    · exact ⟨_, rfl, hr1' _ hpos⟩

