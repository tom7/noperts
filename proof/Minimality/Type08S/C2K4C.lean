module

public import Minimality.Type08S.C2K4B

@[expose] public section

/-!
# C2 / K4C: the 5-cycle `(c', a', b, d, a)` at the edge view `c - d` with `β6 = 1` (`a' = b + γ6 (c - d)`)

Frame `p = a - d`, `q = b - d`, `r = c - d`; `d = 0, a = (1,0,0), b = (0,1,0), c = (0,0,1), c' = (1,β1,0)`,
`b' = (α4,0,γ4)`, `a' = (0,1,γ6)`.  On the screen `a'` coincides with `b`, `c` with `d`, `b'` lies on `[d, a]`;
every degenerate test is decided by the tilt `v = (v1, v2, *)`, `v1 < 0`, `v2 < 0`, `(1 - β1) v1 + v2 < 0`.
Depths (`B = ⟪q, r⟫ > 0`): `a < c'` (`β1 B`), `d < b < a'` (`γ6 |r|²`) — `lexUni5_top`.
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- The ccw cycle `(c', a', b, d, a)` in the `c - d` frame with `β6 = 1`. -/
def k4bCyc (β1 γ6 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ := pc5 (1, β1, 0) (0, 1, γ6) (0, 1, 0) (0, 0, 0) (1, 0, 0)

set_option maxHeartbeats 1600000 in
theorem k4b_cyc {D β1 γ6 v1 v2 v3 : ℝ} (hD : 0 < D) (hβ1 : 0 < β1) (hγ6 : 0 < γ6)
    (hv1 : v1 < 0) (hv2 : v2 < 0) (hcone : (1 - β1) * v1 + v2 < 0) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc D (k4bCyc β1 γ6 (i + 1) - k4bCyc β1 γ6 i) (k4bCyc β1 γ6 j - k4bCyc β1 γ6 i) (v1, v2, v3) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have k1 := hD
  have kb1 := mul_pos hD hβ1
  have kg6 := mul_pos hD hγ6
  have kv1 := mul_pos hD (neg_pos.2 hv1)
  have kv2 := mul_pos hD (neg_pos.2 hv2)
  have kgv1 := mul_pos (mul_pos hD hγ6) (neg_pos.2 hv1)
  have kgc := mul_pos (mul_pos hD hγ6) (neg_pos.2 hcone)
  intro i j h1 h2'
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2' (by decide)).elim
    | (simp only [TSc, d3, k4bCyc, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 1600000 in
theorem k4b_rest {D β1 α4 γ4 γ6 v1 v2 v3 : ℝ} (hD : 0 < D) (hβ1 : 0 < β1) (hα4 : 0 < α4) (hα41 : α4 < 1)
    (hγ4 : 0 < γ4) (hγ6 : 0 < γ6) (hv1 : v1 < 0) (hv2 : v2 < 0) (hcone : (1 - β1) * v1 + v2 < 0) :
    (∀ i : ZMod 5, TSc D (k4bCyc β1 γ6 (i + 1) - k4bCyc β1 γ6 i) ((0, 0, 1) - k4bCyc β1 γ6 i) (v1, v2, v3)) ∧
    (∀ i : ZMod 5, TSc D (k4bCyc β1 γ6 (i + 1) - k4bCyc β1 γ6 i) ((α4, 0, γ4) - k4bCyc β1 γ6 i)
      (v1, v2, v3)) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have k1 := hD
  have kb1 := mul_pos hD hβ1
  have kg6 := mul_pos hD hγ6
  have ka4 := mul_pos hD hα4
  have ka41 := mul_pos hD (sub_pos.2 hα41)
  have kab := mul_pos (mul_pos hD hα4) hβ1
  have kmix := mul_pos hD (show 0 < 1 - α4 + β1 * α4 by nlinarith)
  have kv1 := mul_pos hD (neg_pos.2 hv1)
  have kv2 := mul_pos hD (neg_pos.2 hv2)
  have kgv1 := mul_pos (mul_pos hD hγ6) (neg_pos.2 hv1)
  have kgv2 := mul_pos (mul_pos hD hγ6) (neg_pos.2 hv2)
  have kgc := mul_pos (mul_pos hD hγ6) (neg_pos.2 hcone)
  have kg4v2 := mul_pos (mul_pos hD hγ4) (neg_pos.2 hv2)
  have kg6a4v2 := mul_pos (mul_pos (mul_pos hD hγ6) hα4) (neg_pos.2 hv2)
  have kg4v1 := mul_pos (mul_pos hD hγ4) (neg_pos.2 hv1)
  refine ⟨?_, ?_⟩ <;> intro i <;>
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, k4bCyc, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

theorem k4bCyc_inj {β1 γ6 : ℝ} (hβ1 : 0 < β1) (hγ6 : 0 < γ6) :
    ∀ i j, k4bCyc β1 γ6 i = k4bCyc β1 γ6 j → i = j := by
  intro i j h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [k4bCyc, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith) | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; linarith)

set_option maxHeartbeats 1600000 in
/-- **The 5-cycle cell at the base view `r`** (frame form), `β6 = 1`, `α4 < 1`, `⟪q, r⟫ > 0`. -/
theorem k4b_hasLexCellAt (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0)
    {β1 α4 γ4 γ6 : ℝ} (hβ1 : 0 < β1) (hα4 : 0 < α4) (hα41 : α4 < 1) (hγ4 : 0 < γ4)
    (hγ6 : 0 < γ6) (hB : 0 < ⟪q, r⟫)
    (hmem : ∀ i, fpoint p q r d (k4bCyc β1 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint p q r d (1, β1, 0) ∨ y = fpoint p q r d (0, 1, γ6) ∨
      y = fpoint p q r d (0, 1, 0) ∨ y = fpoint p q r d (0, 0, 0) ∨ y = fpoint p q r d (1, 0, 0) ∨
      y = fpoint p q r d (0, 0, 1) ∨ y = fpoint p q r d (α4, 0, γ4)) :
    HasLexCellAt V r := by
  set Y := k4bCyc β1 γ6 with hY
  obtain ⟨lam, hl0, hl1, hsep⟩ := exists_sep_tilt p q r d hΔ Y (k4bCyc_inj hβ1 hγ6)
    (u1 := -1) (u2 := -(β1 + 1)) (t1 := 1) (t2 := 0) (by nlinarith) (lo := 0) (hi := 1) (by norm_num)
  set vv := fcomb p q r (-1 + lam * 1) (-(β1 + 1) + lam * 0) 0 with hvv
  have hv1 : -1 + lam * 1 < 0 := by linarith
  have hv2 : -(β1 + 1) + lam * 0 < 0 := by linarith
  have hcone : (1 - β1) * (-1 + lam * 1) + (-(β1 + 1) + lam * 0) < 0 := by nlinarith
  have hr0 : r ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  have hC : 0 < ⟪r, r⟫ := real_inner_self_pos.2 hr0
  have n0 : -(0 : ZMod 5) = 0 := by decide
  have n1 : -(1 : ZMod 5) = 4 := by decide
  have n2 : -(2 : ZMod 5) = 3 := by decide
  have n3 : -(3 : ZMod 5) = 2 := by decide
  have n4 : -(4 : ZMod 5) = 1 := by decide
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint p q r d t, r⟫ = ⟪d, r⟫ + t.1 * ⟪p, r⟫ + t.2.1 * ⟪q, r⟫ + t.2.2 * ⟪r, r⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hlexX : LexUni (fun i => ⟪fpoint p q r d (Y (-i)), r⟫) (fun i => ⟪fpoint p q r d (Y (-i)), vv⟫) := by
    refine lexUni5_top _ _ (fun i j h1 h2 => neg_injective (hsep _ _ h1 h2)) ?_ ?_ ?_
    · left; simp only [n0, n1, hY, k4bCyc, pc5_0, pc5_4, hz]; nlinarith
    · left; simp only [n2, n3, hY, k4bCyc, pc5_3, pc5_2, hz]; nlinarith
    · left; simp only [n3, n4, hY, k4bCyc, pc5_2, pc5_1, hz]; nlinarith [mul_pos hγ6 hC]
  have hlexY : LexUni (fun i => ⟪fpoint p q r d (Y i), r⟫) (fun i => ⟪fpoint p q r d (Y i), vv⟫) := by
    simpa only [neg_neg] using lexUni_neg hlexX
  rcases hΔ.lt_or_gt with hneg | hpos
  · have hD : 0 < -det3 p q r := by linarith
    have hcyc := k4b_cyc (v3 := 0) hD hβ1 hγ6 hv1 hv2 hcone
    have hr := k4b_rest (v3 := 0) hD hβ1 hα4 hα41 hγ4 hγ6 hv1 hv2 hcone
    refine ⟨5, inferInstance, fun i => fpoint p q r d (Y (-i)), vv, ?_⟩
    refine lexCell_coord V p q r d (by norm_num) (fun i => Y (-i)) (-1 + lam * 1, -(β1 + 1) + lam * 0, 0)
      (fun i => hmem (-i)) (hcyc_rev hcyc) ?_ hlexX
    intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [n0, hY, k4bCyc, pc5_0])).elim
    · exact (hyx 4 (by simp only [n4, hY, k4bCyc, pc5_1])).elim
    · exact (hyx 3 (by simp only [n3, hY, k4bCyc, pc5_2])).elim
    · exact (hyx 2 (by simp only [n2, hY, k4bCyc, pc5_3])).elim
    · exact (hyx 1 (by simp only [n1, hY, k4bCyc, pc5_4])).elim
    · exact ⟨_, rfl, hrest_rev hr.1⟩
    · exact ⟨_, rfl, hrest_rev hr.2⟩
  · have hcyc := k4b_cyc (v3 := 0) hpos hβ1 hγ6 hv1 hv2 hcone
    have hr := k4b_rest (v3 := 0) hpos hβ1 hα4 hα41 hγ4 hγ6 hv1 hv2 hcone
    refine ⟨5, inferInstance, fun i => fpoint p q r d (Y i), vv, ?_⟩
    refine lexCell_coord V p q r d (by norm_num) Y (-1 + lam * 1, -(β1 + 1) + lam * 0, 0) hmem hcyc ?_ hlexY
    intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [hY, k4bCyc, pc5_0])).elim
    · exact (hyx 1 (by simp only [hY, k4bCyc, pc5_1])).elim
    · exact (hyx 2 (by simp only [hY, k4bCyc, pc5_2])).elim
    · exact (hyx 3 (by simp only [hY, k4bCyc, pc5_3])).elim
    · exact (hyx 4 (by simp only [hY, k4bCyc, pc5_4])).elim
    · exact ⟨_, rfl, hr.1⟩
    · exact ⟨_, rfl, hr.2⟩

end C2
end Type08Sp
end Minimality
