module

public import Minimality.Type08S.C2K6PG

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
/-- **Cell 2 `(a, d, c, a', c')` at `r = b - c`** (ccw cycle `(a, c', a', c, d)`, tilt `v1 < 0`). -/
theorem k6p_cell2_D1_hasLexCellAt (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0)
    {α1 β1 β6 γ6 : ℝ} (hα11 : 1 < α1) (hβ1 : 0 < β1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hs : 1 < β6 + γ6)
    (hab : 1 < α1 + β1) (hcond : 0 < (α1 - 1) * (β6 + γ6) + β1)
    (hx : ⟪p, r⟫ = 0) (hy : ⟪q, r⟫ = -⟪r, r⟫)
    (hmem : ∀ i, fpoint p q r d (k5b_cyc2 α1 β1 β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint p q r d (1, 0, 0) ∨ y = fpoint p q r d (α1, β1, β1) ∨
      y = fpoint p q r d (0, β6 + γ6, β6) ∨ y = fpoint p q r d (0, 1, 0) ∨ y = fpoint p q r d (0, 0, 0) ∨
      y = fpoint p q r d (0, 1, 1) ∨ y = fpoint p q r d (α1, β1, 0)) :
    HasLexCellAt V r := by
  set Y := k5b_cyc2 α1 β1 β6 γ6 with hY
  have hα1 : 0 < α1 := by linarith
  have hαm : 0 < α1 - 1 := by linarith
  obtain ⟨hlh0, hlam⟩ := k6p_interval2 hα11 hβ1 (s := β6 + γ6) (by linarith)
  have hr0 : r ≠ 0 := by intro h0; rw [h0] at hΔ; simp [det3_expand] at hΔ
  have hR : 0 < ⟪r, r⟫ := real_inner_self_pos.2 hr0
  have hDne : (α1 - 1) • p + β1 • q + β1 • r ≠ 0 := by
    intro h0
    have h := det3_coord p q r (α1 - 1) β1 β1 0 1 0 0 0 1
    simp only [fcomb, zero_smul, add_zero, one_smul, zero_add] at h
    have h00 : det3 (0 : ℝ³) q r = 0 := by simp [det3_expand]
    rw [h0, h00] at h
    have h2 : det3 p q r * (α1 - 1) = 0 := by
      have : d3 (α1 - 1) β1 β1 0 1 0 0 0 1 = α1 - 1 := by unfold d3; ring
      rw [← this]; exact h.symm
    rcases mul_eq_zero.mp h2 with h | h
    · exact hΔ h
    · linarith
  have hDpos : 0 < ⟪(α1 - 1) • p + β1 • q + β1 • r, (α1 - 1) • p + β1 • q + β1 • r⟫ := real_inner_self_pos.2 hDne
  have hn : 0 < (α1 - 1) ^ 2 * ⟪p, p⟫ + 2 * (α1 - 1) * β1 * ⟪p, q⟫ + β1 ^ 2 * (⟪q, q⟫ - ⟪r, r⟫) := by
    have : ⟪(α1 - 1) • p + β1 • q + β1 • r, (α1 - 1) • p + β1 • q + β1 • r⟫ =
        (α1 - 1) ^ 2 * ⟪p, p⟫ + 2 * (α1 - 1) * β1 * ⟪p, q⟫ + β1 ^ 2 * (⟪q, q⟫ - ⟪r, r⟫) := by
      simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
      rw [real_inner_comm p q, real_inner_comm p r, real_inner_comm q r, hx, hy]; ring
    rw [← this]; exact hDpos
  obtain ⟨δ, hδ, hδf⟩ := k6p_near_hi (A := ⟪p, p⟫) (B := ⟪p, q⟫) (C := ⟪q, q⟫ - ⟪r, r⟫) hαm hn
  obtain ⟨lam, hl0, hl1, hsep⟩ := exists_sep_tilt p q r d hΔ Y (k5b_cycN_inj hα1 hβ1 hs).2
    (u1 := -1) (u2 := 0) (t1 := 0) (t2 := -1) (by norm_num)
    (lo := max ((β1 - (β6 + γ6)) / α1) (β1 / (α1 - 1) - δ)) (hi := β1 / (α1 - 1))
    (max_lt hlh0 (by linarith))
  have hlo' : (β1 - (β6 + γ6)) / α1 < lam := lt_of_le_of_lt (le_max_left _ _) hl0
  have hlo'' : β1 / (α1 - 1) - δ < lam := lt_of_le_of_lt (le_max_right _ _) hl0
  have hflam := hδf lam hlo'' hl1
  obtain ⟨hc1, hc2⟩ := hlam lam hlo' hl1
  set vv := fcomb p q r (-1 + lam * 0) (0 + lam * -1) 0 with hvv
  have hv1 : -1 + lam * 0 < 0 := by linarith
  have hc1' : 0 < -β1 * (-1 + lam * 0) + (α1 - 1) * (0 + lam * -1) := by nlinarith
  have hc2' : 0 < -(β6 + γ6 - β1) * (-1 + lam * 0) - α1 * (0 + lam * -1) := by nlinarith
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint p q r d t, r⟫ = ⟪d, r⟫ + t.1 * ⟪p, r⟫ + t.2.1 * ⟪q, r⟫ + t.2.2 * ⟪r, r⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hlexY : LexUni (fun i => ⟪fpoint p q r d (Y i), r⟫) (fun i => ⟪fpoint p q r d (Y i), vv⟫) := by
    set zz : ZMod 5 → ℝ := fun i => ⟪fpoint p q r d (Y i), r⟫ with hzz
    set ww : ZMod 5 → ℝ := fun i => ⟪fpoint p q r d (Y i), vv⟫ with hww
    have hw : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint p q r d t, vv⟫ = ⟪d, vv⟫ + t.1 * ⟪p, vv⟫ + t.2.1 * ⟪q, vv⟫ + t.2.2 * ⟪r, vv⟫ :=
      fun t => inner_fpoint _ _ _ _ _ _
    have hrv : ⟪r, vv⟫ = lam * ⟪r, r⟫ := by
      simp only [hvv, fcomb, inner_add_right, inner_smul_right]
      rw [real_inner_comm p r, real_inner_comm q r, hx, hy]; ring
    have hpv : ⟪p, vv⟫ = -(⟪p, p⟫ + lam * ⟪p, q⟫) := by
      simp only [hvv, fcomb, inner_add_right, inner_smul_right]
      rw [hx]; ring
    have hqv : ⟪q, vv⟫ = -(⟪p, q⟫ + lam * ⟪q, q⟫) := by
      simp only [hvv, fcomb, inner_add_right, inner_smul_right]
      rw [hy, real_inner_comm p q]; ring
    have z0 : zz 0 = ⟪d, r⟫ := by simp only [hzz, hY, k5b_cyc2, pc5_0, hz, hx]; ring
    have z1 : zz 1 = ⟪d, r⟫ := by simp only [hzz, hY, k5b_cyc2, pc5_1, hz, hx, hy]; ring
    have z2 : zz 2 = ⟪d, r⟫ - γ6 * ⟪r, r⟫ := by simp only [hzz, hY, k5b_cyc2, pc5_2, hz, hx, hy]; ring
    have z3 : zz 3 = ⟪d, r⟫ - ⟪r, r⟫ := by simp only [hzz, hY, k5b_cyc2, pc5_3, hz, hx, hy]; ring
    have z4 : zz 4 = ⟪d, r⟫ := by simp only [hzz, hY, k5b_cyc2, pc5_4, hz, hx, hy]; ring
    have w0 : ww 0 = ⟪d, vv⟫ + ⟪p, vv⟫ := by simp only [hww, hY, k5b_cyc2, pc5_0, hw]; ring
    have w1 : ww 1 = ⟪d, vv⟫ + (α1 * ⟪p, vv⟫ + β1 * ⟪q, vv⟫ + β1 * ⟪r, vv⟫) := by
      simp only [hww, hY, k5b_cyc2, pc5_1, hw]; ring
    have L10 : LexLt (zz 1, ww 1) (zz 0, ww 0) := by
      right
      refine ⟨by rw [z0, z1], ?_⟩
      simp only
      rw [w0, w1, hpv, hqv, hrv]
      nlinarith [hflam]
    have L21 : LexLt (zz 2, ww 2) (zz 1, ww 1) := Or.inl (by simp only; rw [z1, z2]; nlinarith [mul_pos hγ6 hR])
    have L34 : LexLt (zz 3, ww 3) (zz 4, ww 4) := Or.inl (by simp only; rw [z4, z3]; linarith)
    exact k6p_lexUni5_excl _ _ hsep (k6p_lex_ex_of zz ww (Or.inr (Or.inr (Or.inl L21))) (Or.inl L10)
      (Or.inl L21) (Or.inr (Or.inl L34)) (Or.inr (Or.inr (Or.inl L10))))
  have n0 : -(0 : ZMod 5) = 0 := by decide
  have n1 : -(1 : ZMod 5) = 4 := by decide
  have n2 : -(2 : ZMod 5) = 3 := by decide
  have n3 : -(3 : ZMod 5) = 2 := by decide
  have n4 : -(4 : ZMod 5) = 1 := by decide
  have hcyc0 := fun D (hD : 0 < D) => k5b_cyc2_tsc (v2 := 0 + lam * -1) hD hα1 hβ1 hβ6 hγ6 hs hab hcond hv1
  have hr0' := fun D (hD : 0 < D) =>
    (k5b_rest2_tsc (v2 := 0 + lam * -1) hD hα1 hβ1 hβ6 hγ6 hs hab hv1 hc1' hc2').1
  have hr1' := fun D (hD : 0 < D) =>
    (k5b_rest2_tsc (v2 := 0 + lam * -1) hD hα1 hβ1 hβ6 hγ6 hs hab hv1 hc1' hc2').2
  rcases hΔ.lt_or_gt with hneg | hpos
  · have hD : 0 < -det3 p q r := by linarith
    refine ⟨5, inferInstance, fun i => fpoint p q r d (Y (-i)), vv, ?_⟩
    refine lexCell_coord V p q r d (by norm_num) (fun i => Y (-i)) (-1 + lam * 0, 0 + lam * -1, 0)
      (fun i => hmem (-i)) (hcyc_rev (hcyc0 _ hD)) ?_ (lexUni_neg hlexY)
    intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [n0, hY, k5b_cyc2, pc5_0])).elim
    · exact (hyx 4 (by simp only [n4, hY, k5b_cyc2, pc5_1])).elim
    · exact (hyx 3 (by simp only [n3, hY, k5b_cyc2, pc5_2])).elim
    · exact (hyx 2 (by simp only [n2, hY, k5b_cyc2, pc5_3])).elim
    · exact (hyx 1 (by simp only [n1, hY, k5b_cyc2, pc5_4])).elim
    · exact ⟨_, rfl, hrest_rev (hr0' _ hD)⟩
    · exact ⟨_, rfl, hrest_rev (hr1' _ hD)⟩
  · refine ⟨5, inferInstance, fun i => fpoint p q r d (Y i), vv, ?_⟩
    refine lexCell_coord V p q r d (by norm_num) Y (-1 + lam * 0, 0 + lam * -1, 0) hmem
      (hcyc0 _ hpos) ?_ hlexY
    intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [hY, k5b_cyc2, pc5_0])).elim
    · exact (hyx 1 (by simp only [hY, k5b_cyc2, pc5_1])).elim
    · exact (hyx 2 (by simp only [hY, k5b_cyc2, pc5_2])).elim
    · exact (hyx 3 (by simp only [hY, k5b_cyc2, pc5_3])).elim
    · exact (hyx 4 (by simp only [hY, k5b_cyc2, pc5_4])).elim
    · exact ⟨_, rfl, hr0' _ hpos⟩
    · exact ⟨_, rfl, hr1' _ hpos⟩


end C2
end Type08Sp
end Minimality
