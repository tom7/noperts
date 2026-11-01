module

public import Minimality.Type08S.C2K4A

@[expose] public section

/-!
# C2 / K4B: the cell `(a, c', b, a', c, b')` at `a - d` as `HasLexCellAt` (frame form)
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem lexUni_of_shift {k : ℕ} [NeZero k] {z w : ZMod k → ℝ} (s : ZMod k)
    (h : LexUni (fun i => z (i + s)) (fun i => w (i + s))) : LexUni z w := by
  have := lexUni_shift (-s) h
  simpa only [neg_add_cancel_right] using this

theorem k4Cyc_inj {β1 β6 γ6 α4 : ℝ} (hβ1 : 0 < β1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hα4 : 0 < α4) :
    ∀ i j, k4Cyc β1 β6 γ6 α4 i = k4Cyc β1 β6 γ6 α4 j → i = j := by
  intro i j h
  rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [k4Cyc, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith) | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; linarith)

set_option maxHeartbeats 3200000 in
/-- **The 6-cycle cell `(a, c', b, a', c, b')` at the base view `r = a - d`** (frame form): `γ4 = 1`, `T'`
(`α1 = 1`), `B' = ⟪p, r⟫ = 0`, `D_c = ⟪q, p⟫ < 0`, `β1 < 1`, `γ6 ≤ 1`, `α4 < 1`. -/
theorem k4_hasLexCellAt (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0)
    {β1 α4 β6 γ6 : ℝ} (hβ1 : 0 < β1) (hβ11 : β1 < 1) (hα4 : 0 < α4) (hα41 : α4 < 1) (hβ6 : 0 < β6)
    (hγ6 : 0 < γ6) (hγ61 : γ6 ≤ 1) (hs : 1 < β6 + γ6)
    (hB0 : ⟪p, r⟫ = 0) (hDc : ⟪q, p⟫ < 0)
    (hmem : ∀ i, fpoint p q r d (k4Cyc β1 β6 γ6 α4 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint p q r d (0, 0, 1) ∨ y = fpoint p q r d (β1, 0, 1) ∨
      y = fpoint p q r d (1, 0, 0) ∨ y = fpoint p q r d (β6, γ6, 0) ∨ y = fpoint p q r d (0, 1, 0) ∨
      y = fpoint p q r d (0, 1, α4) ∨ y = fpoint p q r d (0, 0, 0)) :
    HasLexCellAt V r := by
  set Y := k4Cyc β1 β6 γ6 α4 with hY
  have hp0 : p ≠ 0 := by
    rintro rfl; simp at hDc
  have hpp : 0 < ⟪p, p⟫ := real_inner_self_pos.2 hp0
  have hr0 : r ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  have hA : 0 < ⟪r, r⟫ := real_inner_self_pos.2 hr0
  have hhi : 0 < -⟪q, p⟫ / ⟪p, p⟫ := div_pos (neg_pos.2 hDc) hpp
  obtain ⟨lam, hl0, hl1, hsep⟩ := exists_sep_tilt p q r d hΔ Y (k4Cyc_inj hβ1 hβ6 hγ6 hα4)
    (u1 := 0) (u2 := 1) (t1 := 1) (t2 := 0) (by norm_num) (lo := 0) (hi := -⟪q, p⟫ / ⟪p, p⟫) hhi
  set vv := fcomb p q r (0 + lam * 1) (1 + lam * 0) 0 with hvv
  have hv1 : 0 < 0 + lam * 1 := by linarith
  have hv2 : 0 < 1 + lam * 0 := by linarith
  have hpv : ⟪p, vv⟫ = lam * ⟪p, p⟫ + ⟪q, p⟫ := by
    rw [real_inner_comm, hvv, inner_fcomb_left]; ring
  have hwp : ⟪p, vv⟫ < 0 := by
    have := (lt_div_iff₀ hpp).1 hl1; rw [hpv]; linarith
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint p q r d t, r⟫ = ⟪d, r⟫ + t.1 * ⟪p, r⟫ + t.2.1 * ⟪q, r⟫ + t.2.2 * ⟪r, r⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hw : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint p q r d t, vv⟫ = ⟪d, vv⟫ + t.1 * ⟪p, vv⟫ + t.2.1 * ⟪q, vv⟫ + t.2.2 * ⟪r, vv⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  set zf : ZMod 6 → ℝ := fun i => ⟪fpoint p q r d (Y i), r⟫ with hzf
  set wf : ZMod 6 → ℝ := fun i => ⟪fpoint p q r d (Y i), vv⟫ with hwf
  set C' := ⟪q, r⟫ with hC'
  set A := ⟪r, r⟫ with hAdef
  set d0 := ⟪d, r⟫ with hd0
  set e0 := ⟪d, vv⟫ with he0
  set wp := ⟪p, vv⟫ with hwpdef
  set wq := ⟪q, vv⟫ with hwq
  set wr := ⟪r, vv⟫ with hwr
  have z0 : zf 0 = d0 + A := by simp only [hzf, hY, k4Cyc, pc6_0, hz, hB0]; ring
  have z1 : zf 1 = d0 + A := by simp only [hzf, hY, k4Cyc, pc6_1, hz, hB0]; ring
  have z2 : zf 2 = d0 := by simp only [hzf, hY, k4Cyc, pc6_2, hz, hB0]; ring
  have z3 : zf 3 = d0 + γ6 * C' := by simp only [hzf, hY, k4Cyc, pc6_3, hz, hB0]; ring
  have z4 : zf 4 = d0 + C' := by simp only [hzf, hY, k4Cyc, pc6_4, hz, hB0]; ring
  have z5 : zf 5 = d0 + C' + α4 * A := by simp only [hzf, hY, k4Cyc, pc6_5, hz, hB0]; ring
  have w0 : wf 0 = e0 + wr := by simp only [hwf, hY, k4Cyc, pc6_0, hw]; ring
  have w1 : wf 1 = e0 + β1 * wp + wr := by simp only [hwf, hY, k4Cyc, pc6_1, hw]; ring
  have w2 : wf 2 = e0 + wp := by simp only [hwf, hY, k4Cyc, pc6_2, hw]; ring
  have w3 : wf 3 = e0 + β6 * wp + γ6 * wq := by simp only [hwf, hY, k4Cyc, pc6_3, hw]; ring
  have w4 : wf 4 = e0 + wq := by simp only [hwf, hY, k4Cyc, pc6_4, hw]; ring
  have w5 : wf 5 = e0 + wq + α4 * wr := by simp only [hwf, hY, k4Cyc, pc6_5, hw]; ring
  have hinj : ∀ i j, zf i = zf j → wf i = wf j → i = j := hsep
  have hnwp : 0 < -wp := neg_pos.2 hwp
  have hlexY : LexUni zf wf := by
    by_cases hC : 0 < C'
    · apply lexUni_of_shift (4 : ZMod 6)
      refine lexUni6_two _ _ (fun i j h1 h2 => add_right_cancel (hinj _ _ h1 h2)) ?_ ?_ ?_ ?_
      · show LexLt (zf 4, wf 4) (zf 5, wf 5)
        left; rw [z4, z5]; nlinarith [mul_pos hα4 hA]
      · show LexLt (zf 1, wf 1) (zf 0, wf 0)
        right; refine ⟨by rw [z0, z1], ?_⟩
        rw [w0, w1]; nlinarith [mul_pos hβ1 hnwp]
      · show LexLt (zf 3, wf 3) (zf 4, wf 4)
        rcases hγ61.lt_or_eq with h | h
        · left; rw [z3, z4]; nlinarith [mul_pos (sub_pos.2 h) hC]
        · right; refine ⟨by rw [z3, z4, h]; ring, ?_⟩
          rw [w3, w4, h]; nlinarith [mul_pos hβ6 hnwp]
      · show LexLt (zf 2, wf 2) (zf 1, wf 1) ∨ LexLt (zf 2, wf 2) (zf 3, wf 3)
        left; left; rw [z1, z2]; linarith
    · have hC0 : C' ≤ 0 := not_lt.1 hC
      apply lexUni_of_shift (5 : ZMod 6)
      refine lexUni6_two _ _ (fun i j h1 h2 => add_right_cancel (hinj _ _ h1 h2)) ?_ ?_ ?_ ?_
      · show LexLt (zf 5, wf 5) (zf 0, wf 0)
        left; rw [z5, z0]; nlinarith [mul_pos (sub_pos.2 hα41) hA]
      · show LexLt (zf 2, wf 2) (zf 1, wf 1)
        left; rw [z1, z2]; linarith
      · show LexLt (zf 4, wf 4) (zf 5, wf 5)
        left; rw [z4, z5]; nlinarith [mul_pos hα4 hA]
      · show LexLt (zf 3, wf 3) (zf 2, wf 2) ∨ LexLt (zf 3, wf 3) (zf 4, wf 4)
        rcases hC0.lt_or_eq with hneg | h0
        · left; left; rw [z3, z2]; nlinarith [mul_pos hγ6 (neg_pos.2 hneg)]
        · have e3 : zf 3 = zf 2 := by rw [z3, z2, h0]; ring
          have e4 : zf 4 = zf 2 := by rw [z4, z2, h0]; ring
          by_cases hq : 0 ≤ wq
          · right; right; refine ⟨by rw [e3, e4], ?_⟩
            rw [w3, w4]; nlinarith [mul_pos hβ6 hnwp, mul_nonneg (sub_nonneg.2 hγ61) hq]
          · have hq' : wq < 0 := not_le.1 hq
            rcases le_or_gt wp wq with hle | hlt
            · right; right; refine ⟨by rw [e3, e4], ?_⟩
              rw [w3, w4]; nlinarith [mul_nonneg hβ6.le (sub_nonneg.2 hle),
                mul_pos (by linarith : 0 < β6 + γ6 - 1) (neg_pos.2 hq')]
            · left; right; refine ⟨e3, ?_⟩
              rw [w3, w2]; nlinarith [mul_pos hγ6 (sub_pos.2 hlt),
                mul_pos (by linarith : 0 < β6 + γ6 - 1) hnwp]
  have n0 : -(0 : ZMod 6) = 0 := by decide
  have n1 : -(1 : ZMod 6) = 5 := by decide
  have n2 : -(2 : ZMod 6) = 4 := by decide
  have n3 : -(3 : ZMod 6) = 3 := by decide
  have n4 : -(4 : ZMod 6) = 2 := by decide
  have n5 : -(5 : ZMod 6) = 1 := by decide
  rcases hΔ.lt_or_gt with hneg | hpos
  · have hD : 0 < -det3 p q r := by linarith
    have hcyc := k4_cyc (v3 := 0) (α4 := α4) hD hβ1 hβ11 hβ6 hγ6 hγ61 hs hα4 hv1 hv2
    have hr := k4_rest (v3 := 0) hD hβ1 hβ11 hβ6 hγ6 hα4 hv1 hv2
    refine ⟨6, inferInstance, fun i => fpoint p q r d (Y (-i)), vv, ?_⟩
    refine lexCell_coord V p q r d (by norm_num) (fun i => Y (-i)) (0 + lam * 1, 1 + lam * 0, 0)
      (fun i => hmem (-i)) (hcyc_rev hcyc) ?_ (lexUni_neg hlexY)
    intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [n0, hY, k4Cyc, pc6_0])).elim
    · exact (hyx 5 (by simp only [n5, hY, k4Cyc, pc6_1])).elim
    · exact (hyx 4 (by simp only [n4, hY, k4Cyc, pc6_2])).elim
    · exact (hyx 3 (by simp only [n3, hY, k4Cyc, pc6_3])).elim
    · exact (hyx 2 (by simp only [n2, hY, k4Cyc, pc6_4])).elim
    · exact (hyx 1 (by simp only [n1, hY, k4Cyc, pc6_5])).elim
    · exact ⟨_, rfl, hrest_rev hr⟩
  · have hcyc := k4_cyc (v3 := 0) (α4 := α4) hpos hβ1 hβ11 hβ6 hγ6 hγ61 hs hα4 hv1 hv2
    have hr := k4_rest (v3 := 0) hpos hβ1 hβ11 hβ6 hγ6 hα4 hv1 hv2
    refine ⟨6, inferInstance, fun i => fpoint p q r d (Y i), vv, ?_⟩
    refine lexCell_coord V p q r d (by norm_num) Y (0 + lam * 1, 1 + lam * 0, 0) hmem hcyc ?_ hlexY
    intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [hY, k4Cyc, pc6_0])).elim
    · exact (hyx 1 (by simp only [hY, k4Cyc, pc6_1])).elim
    · exact (hyx 2 (by simp only [hY, k4Cyc, pc6_2])).elim
    · exact (hyx 3 (by simp only [hY, k4Cyc, pc6_3])).elim
    · exact (hyx 4 (by simp only [hY, k4Cyc, pc6_4])).elim
    · exact (hyx 5 (by simp only [hY, k4Cyc, pc6_5])).elim
    · exact ⟨_, rfl, hr⟩

end C2
end Type08Sp
end Minimality
