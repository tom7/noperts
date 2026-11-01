module

public import Minimality.Type08S.C2FB1
public import Minimality.Type08S.P2RQ1

@[expose] public section

/-!
# C2 / FB2: the 5-cycle `(c', a', b, d, a)` at the edge view `c - d` (frame form, `T'`)

Frame `p = a - d`, `q = b - d`, `r = c - d` (the base view), coordinates over `d`:
`d = 0, a = (1,0,0), b = (0,1,0), c = (0,0,1), c' = (1,β1,0)` (`T'`: `c' - a ∥ b - d`), `b' = (α4,0,γ4)`,
`a' = (0,β6,γ6)`.  Screen: the face `Q_ab = (d, a, c', b)` with `a'` beyond `b` on the ray `d → b` (`β6 > 1`);
`c` sits over `d`, `b'` on the side `[d, a]` (`α4 < 1`).  The tilt `v = (v1, v2, *)`, `v1, v2 < 0` hides `c`, `b'`
and pushes `b` out of the side `[a', d]`: the cycle is `(c', a', b, d, a)` (ccw).  Depths (`B = ⟪q, r⟫ > 0`):
`a < c'` (`β1 B`), `d < b < a'` — lex unimodal by `lexUni5_top`.
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- The ccw cycle `(c', a', b, d, a)` in the `c - d` frame. -/
def fbCyc (β1 β6 γ6 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ := pc5 (1, β1, 0) (0, β6, γ6) (0, 1, 0) (0, 0, 0) (1, 0, 0)

set_option maxHeartbeats 1600000 in
theorem fbC_cyc {D β1 β6 γ6 v1 v2 v3 : ℝ} (hD : 0 < D) (hβ1 : 0 < β1) (hβ6 : 1 < β6) (hγ6 : 0 < γ6)
    (hv1 : v1 < 0) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc D (fbCyc β1 β6 γ6 (i + 1) - fbCyc β1 β6 γ6 i) (fbCyc β1 β6 γ6 j - fbCyc β1 β6 γ6 i) (v1, v2, v3) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have k1 := hD
  have kb1 := mul_pos hD hβ1
  have kb6 := mul_pos hD (lt_trans one_pos hβ6)
  have kb61 := mul_pos hD (sub_pos.2 hβ6)
  have kgv := mul_pos (mul_pos hD hγ6) (neg_pos.2 hv1)
  intro i j h1 h2'
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2' (by decide)).elim
    | (simp only [TSc, d3, fbCyc, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 1600000 in
theorem fbC_rest {D β1 α4 γ4 β6 γ6 v1 v2 v3 : ℝ} (hD : 0 < D) (hβ1 : 0 < β1) (hα4 : 0 < α4) (hα41 : α4 < 1)
    (hγ4 : 0 < γ4) (hβ6 : 1 < β6) (hγ6 : 0 < γ6) (hv1 : v1 < 0) (hv2 : v2 < 0) :
    (∀ i : ZMod 5, TSc D (fbCyc β1 β6 γ6 (i + 1) - fbCyc β1 β6 γ6 i) ((0, 0, 1) - fbCyc β1 β6 γ6 i) (v1, v2, v3)) ∧
    (∀ i : ZMod 5, TSc D (fbCyc β1 β6 γ6 (i + 1) - fbCyc β1 β6 γ6 i) ((α4, 0, γ4) - fbCyc β1 β6 γ6 i)
      (v1, v2, v3)) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have k1 := hD
  have kb1 := mul_pos hD hβ1
  have kb6 := mul_pos hD (lt_trans one_pos hβ6)
  have kb61 := mul_pos hD (sub_pos.2 hβ6)
  have ka4 := mul_pos hD hα4
  have ka41 := mul_pos (mul_pos hD hβ1) (sub_pos.2 hα41)
  have kab := mul_pos (mul_pos hD hα4) hβ1
  have kab6 := mul_pos (mul_pos hD (lt_trans one_pos hβ6)) (sub_pos.2 hα41)
  have kab61 := mul_pos (mul_pos hD hα4) (sub_pos.2 hβ6)
  have kv1 := mul_pos hD (neg_pos.2 hv1)
  have kv2 := mul_pos hD (neg_pos.2 hv2)
  have kgv := mul_pos (mul_pos hD hγ6) (neg_pos.2 hv1)
  have kg4v := mul_pos (mul_pos hD hγ4) (neg_pos.2 hv2)
  have ksv := mul_pos (mul_pos hD (neg_pos.2 hv1)) (by linarith : (0 : ℝ) < β6 + γ6 - 1)
  refine ⟨?_, ?_⟩ <;> intro i <;>
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, fbCyc, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

theorem fbCyc_inj {β1 β6 γ6 : ℝ} (hβ1 : 0 < β1) (hβ6 : 1 < β6) (hγ6 : 0 < γ6) :
    ∀ i j, fbCyc β1 β6 γ6 i = fbCyc β1 β6 γ6 j → i = j := by
  intro i j h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [fbCyc, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; linarith)

set_option maxHeartbeats 1600000 in
/-- **The 5-cycle cell at the base view `r`** (frame form).  `V` consists of the seven frame points over `d`
(header); `β6 > 1`, `α4 < 1`, `⟪q, r⟫ > 0`. -/
theorem fbC_hasLexCellAt (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0)
    {β1 α4 γ4 β6 γ6 : ℝ} (hβ1 : 0 < β1) (hα4 : 0 < α4) (hα41 : α4 < 1) (hγ4 : 0 < γ4) (hβ6 : 1 < β6)
    (hγ6 : 0 < γ6) (hB : 0 < ⟪q, r⟫)
    (hmem : ∀ i, fpoint p q r d (fbCyc β1 β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint p q r d (1, β1, 0) ∨ y = fpoint p q r d (0, β6, γ6) ∨
      y = fpoint p q r d (0, 1, 0) ∨ y = fpoint p q r d (0, 0, 0) ∨ y = fpoint p q r d (1, 0, 0) ∨
      y = fpoint p q r d (0, 0, 1) ∨ y = fpoint p q r d (α4, 0, γ4)) :
    HasLexCellAt V r := by
  set Y := fbCyc β1 β6 γ6 with hY
  obtain ⟨lam, hl0, hl1, hsep⟩ := exists_sep_tilt p q r d hΔ Y (fbCyc_inj hβ1 hβ6 hγ6)
    (u1 := -1) (u2 := -1) (t1 := 1) (t2 := 0) (by norm_num) (lo := 0) (hi := 1) (by norm_num)
  set vv := fcomb p q r (-1 + lam * 1) (-1 + lam * 0) 0 with hvv
  have hv1 : -1 + lam * 1 < 0 := by linarith
  have hv2 : -1 + lam * 0 < 0 := by linarith
  have hr0 : r ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  have hC : 0 < ⟪r, r⟫ := real_inner_self_pos.2 hr0
  have n0 : -(0 : ZMod 5) = 0 := by decide
  have n1 : -(1 : ZMod 5) = 4 := by decide
  have n2 : -(2 : ZMod 5) = 3 := by decide
  have n3 : -(3 : ZMod 5) = 2 := by decide
  have n4 : -(4 : ZMod 5) = 1 := by decide
  -- lex unimodality of the reversed cycle `X = (c', a, d, b, a')`
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint p q r d t, r⟫ = ⟪d, r⟫ + t.1 * ⟪p, r⟫ + t.2.1 * ⟪q, r⟫ + t.2.2 * ⟪r, r⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hlexX : LexUni (fun i => ⟪fpoint p q r d (Y (-i)), r⟫) (fun i => ⟪fpoint p q r d (Y (-i)), vv⟫) := by
    refine lexUni5_top _ _ (fun i j h1 h2 => neg_injective (hsep _ _ h1 h2)) ?_ ?_ ?_
    · left; simp only [n0, n1, hY, fbCyc, pc5_0, pc5_4, hz]; nlinarith
    · left; simp only [n2, n3, hY, fbCyc, pc5_3, pc5_2, hz]; nlinarith
    · left; simp only [n3, n4, hY, fbCyc, pc5_2, pc5_1, hz]; nlinarith [mul_pos (sub_pos.2 hβ6) hB, mul_pos hγ6 hC]
  have hlexY : LexUni (fun i => ⟪fpoint p q r d (Y i), r⟫) (fun i => ⟪fpoint p q r d (Y i), vv⟫) := by
    simpa only [neg_neg] using lexUni_neg hlexX
  rcases hΔ.lt_or_gt with hneg | hpos
  · have hD : 0 < -det3 p q r := by linarith
    have hcyc := fbC_cyc (v2 := -1 + lam * 0) (v3 := 0) hD hβ1 hβ6 hγ6 hv1
    have hr := fbC_rest (v3 := 0) hD hβ1 hα4 hα41 hγ4 hβ6 hγ6 hv1 hv2
    refine ⟨5, inferInstance, fun i => fpoint p q r d (Y (-i)), vv, ?_⟩
    refine lexCell_coord V p q r d (by norm_num) (fun i => Y (-i)) (-1 + lam * 1, -1 + lam * 0, 0)
      (fun i => hmem (-i)) (hcyc_rev hcyc) ?_ hlexX
    intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [n0, hY, fbCyc, pc5_0])).elim
    · exact (hyx 4 (by simp only [n4, hY, fbCyc, pc5_1])).elim
    · exact (hyx 3 (by simp only [n3, hY, fbCyc, pc5_2])).elim
    · exact (hyx 2 (by simp only [n2, hY, fbCyc, pc5_3])).elim
    · exact (hyx 1 (by simp only [n1, hY, fbCyc, pc5_4])).elim
    · exact ⟨_, rfl, hrest_rev hr.1⟩
    · exact ⟨_, rfl, hrest_rev hr.2⟩
  · have hcyc := fbC_cyc (v2 := -1 + lam * 0) (v3 := 0) hpos hβ1 hβ6 hγ6 hv1
    have hr := fbC_rest (v3 := 0) hpos hβ1 hα4 hα41 hγ4 hβ6 hγ6 hv1 hv2
    refine ⟨5, inferInstance, fun i => fpoint p q r d (Y i), vv, ?_⟩
    refine lexCell_coord V p q r d (by norm_num) Y (-1 + lam * 1, -1 + lam * 0, 0) hmem hcyc ?_ hlexY
    intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [hY, fbCyc, pc5_0])).elim
    · exact (hyx 1 (by simp only [hY, fbCyc, pc5_1])).elim
    · exact (hyx 2 (by simp only [hY, fbCyc, pc5_2])).elim
    · exact (hyx 3 (by simp only [hY, fbCyc, pc5_3])).elim
    · exact (hyx 4 (by simp only [hY, fbCyc, pc5_4])).elim
    · exact ⟨_, rfl, hr.1⟩
    · exact ⟨_, rfl, hr.2⟩

end C2
end Type08Sp
end Minimality
