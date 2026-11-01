module

public import Minimality.Type08S.C2K5sF

@[expose] public section

/-!
# C2 / K1D: the 6-cycle cell `(a, c', b, a', c, d)` at `a - d` as `HasLexCellAt` (frame form, `s < 0`)
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

theorem k5_wdiff2 (p q r d : ℝ³) (β6 v1 v2 : ℝ) :
    ⟪fpoint p q r d (β6, 1, 0), fcomb p q r v1 v2 0⟫ - ⟪fpoint p q r d (0, 1, 0), fcomb p q r v1 v2 0⟫ =
      β6 * (v1 * ⟪p, p⟫ + v2 * ⟪p, q⟫) := by
  simp only [fpoint, fcomb, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    inner_zero_right, inner_sub_left, inner_zero_left]
  rw [real_inner_comm q p]
  ring

theorem k5_wdiff3 (p q r d : ℝ³) (v1 v2 : ℝ) :
    ⟪fpoint p q r d (0, 1, 0), fcomb p q r v1 v2 0⟫ - ⟪fpoint p q r d (0, 0, 0), fcomb p q r v1 v2 0⟫ =
      v1 * ⟪p, q⟫ + v2 * ⟪q, q⟫ := by
  simp only [fpoint, fcomb, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    inner_zero_right, inner_sub_left, inner_zero_left, zero_smul, add_zero, zero_add]
  rw [real_inner_comm q p]
  ring

set_option maxHeartbeats 3200000 in
/-- **The 6-cycle cell `(a, c', b, a', c, d)` at the base view `r = a - d`** (frame form), `γ4 = γ6 = 1`,
`1 < α1`, `B' = ⟪p, r⟫ ≥ 0`, `s = (β6 - 1) B' + ⟪q, r⟫ < 0`, `β1 < 1`. -/
theorem k5x2z_hasLexCellAt (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0)
    {α1 β1 α4 β6 : ℝ} (hα1 : 1 < α1) (hβ1 : 0 < β1) (hβ11 : β1 < 1) (hα4 : 0 < α4) (hβ6 : 0 < β6)
    (hB : ⟪p, r⟫ = 0) (hC : ⟪q, r⟫ = 0) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ * ⟪q, q⟫ < ⟪p, q⟫)
    (hδ2 : δ * ⟪p, q⟫ < ⟪p, p⟫) (hg : 0 < ⟪p, q⟫)
    (hmem : ∀ i, fpoint p q r d (k1Cyc6 α1 β1 β6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint p q r d (0, 0, 1) ∨ y = fpoint p q r d (0, 0, 0) ∨
      y = fpoint p q r d (1, 0, 0) ∨ y = fpoint p q r d (β6, 1, 0) ∨ y = fpoint p q r d (0, 1, α4) ∨
      y = fpoint p q r d (0, 1, 0) ∨ y = fpoint p q r d (β1, 0, α1)) :
    HasLexCellAt V r := by
  set Y := k1Cyc6 α1 β1 β6 with hY
  have hr0 : r ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  have hA : 0 < ⟪r, r⟫ := real_inner_self_pos.2 hr0
  obtain ⟨lam, hl0, hl1, hsep⟩ := exists_sep_tilt p q r d hΔ Y (k1Cyc6_inj hα1 hβ1 hβ11 hβ6)
    (u1 := -1) (u2 := δ / 2) (t1 := 0) (t2 := δ / 2) (by nlinarith) (lo := 0) (hi := 1) (by norm_num)
  set vv := fcomb p q r (-1 + lam * 0) (δ / 2 + lam * (δ / 2)) 0 with hvv
  have hv1 : -1 + lam * 0 < 0 := by linarith
  have hv2 : 0 < δ / 2 + lam * (δ / 2) := by nlinarith
  have hv2' : δ / 2 + lam * (δ / 2) < δ := by nlinarith
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint p q r d t, r⟫ = ⟪d, r⟫ + t.1 * ⟪p, r⟫ + t.2.1 * ⟪q, r⟫ + t.2.2 * ⟪r, r⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hlexY : LexUni (fun i => ⟪fpoint p q r d (Y i), r⟫) (fun i => ⟪fpoint p q r d (Y i), vv⟫) := by
    have hqq : 0 ≤ ⟪q, q⟫ := real_inner_self_nonneg
    refine lexUni6_gen _ _ hsep ?_ ?_ ?_ ?_ ?_
    · left; simp only [hY, k1Cyc6, six_0, six_1, hz]; nlinarith [mul_pos (sub_pos.2 hα1) hA]
    · left; simp only [hY, k1Cyc6, six_2, six_1, hz]; nlinarith [mul_pos (lt_trans one_pos hα1) hA]
    · left; simp only [hY, k1Cyc6, six_5, six_0, hz]; nlinarith
    · right; right
      have hd := k5_wdiff2 p q r d β6 (-1 + lam * 0) (δ / 2 + lam * (δ / 2))
      refine ⟨?_, ?_⟩
      · simp only [hY, k1Cyc6, six_3, six_4, hz]; nlinarith
      · simp only [hY, k1Cyc6, six_3, six_4]
        rw [hvv]
        have : (δ / 2 + lam * (δ / 2)) * ⟪p, q⟫ < ⟪p, p⟫ := by nlinarith [mul_pos hδ (lt_trans hl0 hl1), hδ2]
        nlinarith [mul_pos hβ6 (sub_pos.2 this)]
    · right; right
      have hd := k5_wdiff3 p q r d (-1 + lam * 0) (δ / 2 + lam * (δ / 2))
      refine ⟨?_, ?_⟩
      · simp only [hY, k1Cyc6, six_4, six_5, hz]; nlinarith
      · simp only [hY, k1Cyc6, six_4, six_5]
        rw [hvv]
        nlinarith [mul_nonneg (sub_nonneg.2 hv2'.le) hqq]
  have n0 : -(0 : ZMod 6) = 0 := by decide
  have n1 : -(1 : ZMod 6) = 5 := by decide
  have n2 : -(2 : ZMod 6) = 4 := by decide
  have n3 : -(3 : ZMod 6) = 3 := by decide
  have n4 : -(4 : ZMod 6) = 2 := by decide
  have n5 : -(5 : ZMod 6) = 1 := by decide
  rcases hΔ.lt_or_gt with hneg | hpos
  · have hD : 0 < -det3 p q r := by linarith
    have hcyc := k1_cyc6 (v3 := 0) hD hα1 hβ1 hβ11 hβ6 hv1 hv2
    have hr := k1_rest6 (v3 := 0) hD hα1 hβ1 hβ11 hα4 hβ6 hv1 hv2
    refine ⟨6, inferInstance, fun i => fpoint p q r d (Y (-i)), vv, ?_⟩
    refine lexCell_coord V p q r d (by norm_num) (fun i => Y (-i)) (-1 + lam * 0, δ / 2 + lam * (δ / 2), 0)
      (fun i => hmem (-i)) (hcyc_rev hcyc) ?_ (lexUni_neg hlexY)
    intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [n0, hY, k1Cyc6, six_0])).elim
    · exact (hyx 1 (by simp only [n1, hY, k1Cyc6, six_5])).elim
    · exact (hyx 4 (by simp only [n4, hY, k1Cyc6, six_2])).elim
    · exact (hyx 3 (by simp only [n3, hY, k1Cyc6, six_3])).elim
    · exact ⟨_, rfl, hrest_rev hr⟩
    · exact (hyx 2 (by simp only [n2, hY, k1Cyc6, six_4])).elim
    · exact (hyx 5 (by simp only [n5, hY, k1Cyc6, six_1])).elim
  · have hcyc := k1_cyc6 (v3 := 0) hpos hα1 hβ1 hβ11 hβ6 hv1 hv2
    have hr := k1_rest6 (v3 := 0) hpos hα1 hβ1 hβ11 hα4 hβ6 hv1 hv2
    refine ⟨6, inferInstance, fun i => fpoint p q r d (Y i), vv, ?_⟩
    refine lexCell_coord V p q r d (by norm_num) Y (-1 + lam * 0, δ / 2 + lam * (δ / 2), 0) hmem hcyc ?_ hlexY
    intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [hY, k1Cyc6, six_0])).elim
    · exact (hyx 5 (by simp only [hY, k1Cyc6, six_5])).elim
    · exact (hyx 2 (by simp only [hY, k1Cyc6, six_2])).elim
    · exact (hyx 3 (by simp only [hY, k1Cyc6, six_3])).elim
    · exact ⟨_, rfl, hr⟩
    · exact (hyx 4 (by simp only [hY, k1Cyc6, six_4])).elim
    · exact (hyx 1 (by simp only [hY, k1Cyc6, six_1])).elim

end C2
end Type08Sp
end Minimality
