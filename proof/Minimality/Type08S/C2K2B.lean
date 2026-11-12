module

public import Minimality.Type08S.C2K2A

@[expose] public section

/-!
# C2 / K2B: the cell `(a, d, b, a', b')` at `a - d` as `HasLexCellAt` (frame form)
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem kCyc_inj {β6 γ6 α4 : ℝ} (hβ6 : 0 < β6) (hγ6 : 0 < γ6) :
    ∀ i j, kCyc β6 γ6 α4 i = kCyc β6 γ6 α4 j → i = j := by
  intro i j h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [kCyc, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h)

set_option maxHeartbeats 1600000 in
/-- **The 5-cycle cell `(a, d, b, a', b')` at the base view `r = a - d`** (frame form), `γ4 = 1`,
`B' = ⟪p, r⟫ = 0`, `D_c = ⟪q, p⟫ > 0`, `β1 < 1`, `γ6 ≤ 1`. -/
theorem k2_hasLexCellAt (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0)
    {α1 β1 α4 β6 γ6 : ℝ} (hα1 : 0 < α1) (hβ1 : 0 < β1) (hβ11 : β1 < 1) (hα4 : 0 < α4) (hβ6 : 0 < β6)
    (hγ6 : 0 < γ6) (hγ61 : γ6 ≤ 1) (hs : 1 < β6 + γ6)
    (hB0 : ⟪p, r⟫ = 0) (hDc : 0 < ⟪q, p⟫)
    (hmem : ∀ i, fpoint p q r d (kCyc β6 γ6 α4 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint p q r d (0, 0, 1) ∨ y = fpoint p q r d (0, 0, 0) ∨
      y = fpoint p q r d (1, 0, 0) ∨ y = fpoint p q r d (β6, γ6, 0) ∨ y = fpoint p q r d (0, 1, α4) ∨
      y = fpoint p q r d (0, 1, 0) ∨ y = fpoint p q r d (β1, 0, α1)) :
    HasLexCellAt V r := by
  set Y := kCyc β6 γ6 α4 with hY
  have hp0 : p ≠ 0 := by
    rintro rfl; simp at hDc
  have hpp : 0 < ⟪p, p⟫ := real_inner_self_pos.2 hp0
  have hr0 : r ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  have hA : 0 < ⟪r, r⟫ := real_inner_self_pos.2 hr0
  have hhi : 0 < min (⟪q, p⟫ / ⟪p, p⟫) β6 := lt_min (div_pos hDc hpp) hβ6
  obtain ⟨lam, hl0, hl1, hsep⟩ := exists_sep_tilt p q r d hΔ Y (kCyc_inj hβ6 hγ6)
    (u1 := 0) (u2 := -1) (t1 := 1) (t2 := 0) (by norm_num) (lo := 0) (hi := min (⟪q, p⟫ / ⟪p, p⟫) β6) hhi
  have hl2 : lam < ⟪q, p⟫ / ⟪p, p⟫ := lt_of_lt_of_le hl1 (min_le_left _ _)
  have hl3 : lam < β6 := lt_of_lt_of_le hl1 (min_le_right _ _)
  set vv := fcomb p q r (0 + lam * 1) (-1 + lam * 0) 0 with hvv
  have hv1 : 0 < 0 + lam * 1 := by linarith
  have hv2 : -1 + lam * 0 < 0 := by linarith
  have hcone : (1 - γ6) * (0 + lam * 1) + β6 * (-1 + lam * 0) < 0 := by nlinarith [mul_pos hγ6 hl0]
  have hpv : ⟪p, vv⟫ = lam * ⟪p, p⟫ - ⟪q, p⟫ := by
    rw [real_inner_comm, hvv, inner_fcomb_left]; ring
  have hbd : lam * ⟪p, p⟫ - ⟪q, p⟫ < 0 := by
    have := (lt_div_iff₀ hpp).1 hl2; linarith
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint p q r d t, r⟫ = ⟪d, r⟫ + t.1 * ⟪p, r⟫ + t.2.1 * ⟪q, r⟫ + t.2.2 * ⟪r, r⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hw : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint p q r d t, vv⟫ = ⟪d, vv⟫ + t.1 * ⟪p, vv⟫ + t.2.1 * ⟪q, vv⟫ + t.2.2 * ⟪r, vv⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hlexY : LexUni (fun i => ⟪fpoint p q r d (Y i), r⟫) (fun i => ⟪fpoint p q r d (Y i), vv⟫) := by
    refine lexUni5_adj _ _ hsep ?_ ?_ ?_
    · left; simp only [hY, kCyc, pc5_0, pc5_1, hz]; nlinarith
    · right
      refine ⟨?_, ?_⟩
      · simp only [hY, kCyc, pc5_2, pc5_1, hz]; nlinarith
      · simp only [hY, kCyc, pc5_2, pc5_1, hw]; nlinarith
    · by_cases hC : 0 ≤ ⟪q, r⟫
      · right; left
        simp only [hY, kCyc, pc5_3, pc5_4, hz]
        nlinarith [mul_nonneg (sub_nonneg.2 hγ61) hC]
      · left; left
        simp only [hY, kCyc, pc5_3, pc5_2, hz]
        nlinarith [mul_pos hγ6 (neg_pos.2 (not_le.1 hC))]
  have n0 : -(0 : ZMod 5) = 0 := by decide
  have n1 : -(1 : ZMod 5) = 4 := by decide
  have n2 : -(2 : ZMod 5) = 3 := by decide
  have n3 : -(3 : ZMod 5) = 2 := by decide
  have n4 : -(4 : ZMod 5) = 1 := by decide
  rcases hΔ.lt_or_gt with hneg | hpos
  · have hD : 0 < -det3 p q r := by linarith
    have hcyc := k2_cyc (v3 := 0) (α4 := α4) hD hβ6 hγ6 hs hv1 hv2
    have hr := k2_rest (v3 := 0) hD hα1 hβ1 hβ11 hα4 hβ6 hγ6 hγ61 hs hv1 hv2 hcone
    refine ⟨5, inferInstance, fun i => fpoint p q r d (Y (-i)), vv, ?_⟩
    refine lexCell_coord V p q r d (by norm_num) (fun i => Y (-i)) (0 + lam * 1, -1 + lam * 0, 0)
      (fun i => hmem (-i)) (hcyc_rev hcyc) ?_ (lexUni_neg hlexY)
    intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [n0, hY, kCyc, pc5_0])).elim
    · exact (hyx 4 (by simp only [n4, hY, kCyc, pc5_1])).elim
    · exact (hyx 3 (by simp only [n3, hY, kCyc, pc5_2])).elim
    · exact (hyx 2 (by simp only [n2, hY, kCyc, pc5_3])).elim
    · exact (hyx 1 (by simp only [n1, hY, kCyc, pc5_4])).elim
    · exact ⟨_, rfl, hrest_rev hr.1⟩
    · exact ⟨_, rfl, hrest_rev hr.2⟩
  · have hcyc := k2_cyc (v3 := 0) (α4 := α4) hpos hβ6 hγ6 hs hv1 hv2
    have hr := k2_rest (v3 := 0) hpos hα1 hβ1 hβ11 hα4 hβ6 hγ6 hγ61 hs hv1 hv2 hcone
    refine ⟨5, inferInstance, fun i => fpoint p q r d (Y i), vv, ?_⟩
    refine lexCell_coord V p q r d (by norm_num) Y (0 + lam * 1, -1 + lam * 0, 0) hmem hcyc ?_ hlexY
    intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [hY, kCyc, pc5_0])).elim
    · exact (hyx 1 (by simp only [hY, kCyc, pc5_1])).elim
    · exact (hyx 2 (by simp only [hY, kCyc, pc5_2])).elim
    · exact (hyx 3 (by simp only [hY, kCyc, pc5_3])).elim
    · exact (hyx 4 (by simp only [hY, kCyc, pc5_4])).elim
    · exact ⟨_, rfl, hr.1⟩
    · exact ⟨_, rfl, hr.2⟩

end C2
end Type08Sp
end Minimality
