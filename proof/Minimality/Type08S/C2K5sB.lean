module

public import Minimality.Type08S.C2K5sA

@[expose] public section

/-!
# K5s / B: X1 = `(d, b, a', b', c)` at `a - d` with a free tilt segment; `s > 0`, or `s = 0` and the tie `a' ~ b` decided by the tilt
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

set_option maxHeartbeats 3200000 in
theorem k5x1_hasLexCellAt (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0)
    {α1 β1 α4 β6 : ℝ} (hα1 : 0 < α1) (hβ1 : 0 < β1) (hβ11 : β1 < 1) (hα4 : 0 < α4) (hβ6 : 0 < β6)
    (hB : 0 < ⟪p, r⟫)
    {u1 u2 t1 t2 : ℝ} (hu1 : u1 < 0) (hu2 : u2 < 0) (hw1 : u1 + t1 < 0) (hw2 : u2 + t2 < 0)
    (hut : u1 * t2 - u2 * t1 ≠ 0)
    (hs : 0 < (β6 - 1) * ⟪p, r⟫ + ⟪q, r⟫ ∨
      ((β6 - 1) * ⟪p, r⟫ + ⟪q, r⟫ = 0 ∧
        0 < u1 * ⟪(β6 - 1) • p + q, p⟫ + u2 * ⟪(β6 - 1) • p + q, q⟫ ∧
        0 < (u1 + t1) * ⟪(β6 - 1) • p + q, p⟫ + (u2 + t2) * ⟪(β6 - 1) • p + q, q⟫))
    (hmem : ∀ i, fpoint p q r d (k1Cyc β6 α4 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint p q r d (0, 0, 1) ∨ y = fpoint p q r d (0, 0, 0) ∨
      y = fpoint p q r d (1, 0, 0) ∨ y = fpoint p q r d (β6, 1, 0) ∨ y = fpoint p q r d (0, 1, α4) ∨
      y = fpoint p q r d (0, 1, 0) ∨ y = fpoint p q r d (β1, 0, α1)) :
    HasLexCellAt V r := by
  set Y := k1Cyc β6 α4 with hY
  have hr0 : r ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  have hA : 0 < ⟪r, r⟫ := real_inner_self_pos.2 hr0
  obtain ⟨lam, hl0, hl1, hsep⟩ := exists_sep_tilt p q r d hΔ Y (k1Cyc_inj hβ6 hα4)
    (u1 := u1) (u2 := u2) (t1 := t1) (t2 := t2) hut (lo := 0) (hi := 1) (by norm_num)
  set vv := fcomb p q r (u1 + lam * t1) (u2 + lam * t2) 0 with hvv
  have hv1 : u1 + lam * t1 < 0 := by nlinarith [mul_pos (sub_pos.2 hl1) (neg_pos.2 hu1), mul_pos hl0 (neg_pos.2 hw1)]
  have hv2 : u2 + lam * t2 < 0 := by nlinarith [mul_pos (sub_pos.2 hl1) (neg_pos.2 hu2), mul_pos hl0 (neg_pos.2 hw2)]
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint p q r d t, r⟫ = ⟪d, r⟫ + t.1 * ⟪p, r⟫ + t.2.1 * ⟪q, r⟫ + t.2.2 * ⟪r, r⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hlexY : LexUni (fun i => ⟪fpoint p q r d (Y i), r⟫) (fun i => ⟪fpoint p q r d (Y i), vv⟫) := by
    refine lexUni5_two _ _ hsep ?_ ?_ ?_
    · rcases hs with hs | ⟨hs0, hs1, hs2⟩
      · left; simp only [hY, k1Cyc, pc5_1, pc5_2, hz]; nlinarith
      · right
        have hd := k5_wdiff p q r d β6 (u1 + lam * t1) (u2 + lam * t2)
        refine ⟨?_, ?_⟩
        · simp only [hY, k1Cyc, pc5_1, pc5_2, hz]; nlinarith
        · simp only [hY, k1Cyc, pc5_1, pc5_2]
          rw [hvv]
          nlinarith [mul_pos (sub_pos.2 hl1) hs1, mul_pos hl0 hs2]
    · left; simp only [hY, k1Cyc, pc5_4, pc5_3, hz]; nlinarith [mul_pos hα4 hA]
    · left; left; simp only [hY, k1Cyc, pc5_0, pc5_1, hz]; nlinarith
  have n0 : -(0 : ZMod 5) = 0 := by decide
  have n1 : -(1 : ZMod 5) = 4 := by decide
  have n2 : -(2 : ZMod 5) = 3 := by decide
  have n3 : -(3 : ZMod 5) = 2 := by decide
  have n4 : -(4 : ZMod 5) = 1 := by decide
  rcases hΔ.lt_or_gt with hneg | hpos
  · have hD : 0 < -det3 p q r := by linarith
    have hcyc := k1_cyc (v3 := 0) hD hβ6 hα4 hv1 hv2
    have hr := k1_rest (v3 := 0) hD hα1 hβ1 hβ11 hα4 hβ6 hv1 hv2
    refine ⟨5, inferInstance, fun i => fpoint p q r d (Y (-i)), vv, ?_⟩
    refine lexCell_coord V p q r d (by norm_num) (fun i => Y (-i)) (u1 + lam * t1, u2 + lam * t2, 0)
      (fun i => hmem (-i)) (hcyc_rev hcyc) ?_ (lexUni_neg hlexY)
    intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, rfl, hrest_rev hr.1⟩
    · exact (hyx 0 (by simp only [n0, hY, k1Cyc, pc5_0])).elim
    · exact (hyx 4 (by simp only [n4, hY, k1Cyc, pc5_1])).elim
    · exact (hyx 3 (by simp only [n3, hY, k1Cyc, pc5_2])).elim
    · exact (hyx 2 (by simp only [n2, hY, k1Cyc, pc5_3])).elim
    · exact (hyx 1 (by simp only [n1, hY, k1Cyc, pc5_4])).elim
    · exact ⟨_, rfl, hrest_rev hr.2⟩
  · have hcyc := k1_cyc (v3 := 0) hpos hβ6 hα4 hv1 hv2
    have hr := k1_rest (v3 := 0) hpos hα1 hβ1 hβ11 hα4 hβ6 hv1 hv2
    refine ⟨5, inferInstance, fun i => fpoint p q r d (Y i), vv, ?_⟩
    refine lexCell_coord V p q r d (by norm_num) Y (u1 + lam * t1, u2 + lam * t2, 0) hmem hcyc ?_ hlexY
    intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, rfl, hr.1⟩
    · exact (hyx 0 (by simp only [hY, k1Cyc, pc5_0])).elim
    · exact (hyx 1 (by simp only [hY, k1Cyc, pc5_1])).elim
    · exact (hyx 2 (by simp only [hY, k1Cyc, pc5_2])).elim
    · exact (hyx 3 (by simp only [hY, k1Cyc, pc5_3])).elim
    · exact (hyx 4 (by simp only [hY, k1Cyc, pc5_4])).elim
    · exact ⟨_, rfl, hr.2⟩

end C2
end Type08Sp
end Minimality
