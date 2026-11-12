module

public import Minimality.Type08S.C2K4E

@[expose] public section

/-!
# C2 / K3A: the 5-cycle `Q1⁺ = (c, d, a, c', a')` at the edge view `c - d` (frame form, `T'`, `α4 = 1`, `β6 > 1`)

Frame `p = a - d`, `q = b - d`, `r = c - d` (the base view), coordinates over `d`:
`d = 0, a = (1,0,0), b = (0,1,0), c = (0,0,1), c' = (1,β1,0)` (`T'`), `b' = (1,0,γ4)` (`α4 = 1`: `b'` over `a`),
`a' = (0,β6,γ6)`.  Screen: `{d, c}` at `0`, `{a, b'}` at `(1,0)`, `c'` at `(1,β1)`, `b` at `(0,1)`, `a'` at `(0,β6)`.
The tilt `v = (v1, v2, 0)`, `v1 > 0 > v2` pushes `c` (and `a'`) out to the left and hides `b'` (behind `a`) and `b`
(on the side `[c, a']`): the ccw cycle is `(c, d, a, c', a')`.  Depths over `d` (`A = |r|²`, `B = ⟪p,r⟫`, `C = ⟪q,r⟫`):
`c = A, d = 0, a = B, c' = B + β1 C, a' = β6 C + γ6 A`.  With `C > 0` and `s₁ = ⟪a' - c', r⟫ > 0`:
`d < c`, `a < c' < a'`, so the peaks lie in `{a', c}` (adjacent): `lexUni5_top`.
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- The ccw cycle `(c, d, a, c', a')` in the `c - d` frame. -/
def k3q1pCyc (β1 β6 γ6 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ := pc5 (0, 0, 1) (0, 0, 0) (1, 0, 0) (1, β1, 0) (0, β6, γ6)

set_option maxHeartbeats 1600000 in
theorem k3q1p_cyc {D β1 β6 γ6 v1 v2 v3 : ℝ} (hD : 0 < D) (hβ1 : 0 < β1) (hβ6 : 1 < β6) (hγ6 : 0 < γ6)
    (hv1 : 0 < v1) (hv2 : v2 < 0) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc D (k3q1pCyc β1 β6 γ6 (i + 1) - k3q1pCyc β1 β6 γ6 i) (k3q1pCyc β1 β6 γ6 j - k3q1pCyc β1 β6 γ6 i)
        (v1, v2, v3) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have k1 := hD
  have kb1 := mul_pos hD hβ1
  have kb6 := mul_pos hD (lt_trans one_pos hβ6)
  have kb61 := mul_pos hD (sub_pos.2 hβ6)
  have kg6 := mul_pos hD hγ6
  have kv1 := mul_pos hD hv1
  have kv2 := mul_pos hD (neg_pos.2 hv2)
  have kgv1 := mul_pos (mul_pos hD hγ6) hv1
  have kgv2 := mul_pos (mul_pos hD hγ6) (neg_pos.2 hv2)
  have kbv1 := mul_pos (mul_pos hD hβ1) hv1
  have kb6v1 := mul_pos (mul_pos hD (lt_trans one_pos hβ6)) hv1
  intro i j h1 h2'
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2' (by decide)).elim
    | (simp only [TSc, d3, k3q1pCyc, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 1600000 in
theorem k3q1p_rest {D β1 γ4 β6 γ6 v1 v2 v3 : ℝ} (hD : 0 < D) (hβ1 : 0 < β1) (hγ4 : 0 < γ4) (hβ6 : 1 < β6)
    (hγ6 : 0 < γ6) (hs : 1 < β6 + γ6) (hv1 : 0 < v1) (hv2 : v2 < 0) :
    (∀ i : ZMod 5, TSc D (k3q1pCyc β1 β6 γ6 (i + 1) - k3q1pCyc β1 β6 γ6 i) ((0, 1, 0) - k3q1pCyc β1 β6 γ6 i)
      (v1, v2, v3)) ∧
    (∀ i : ZMod 5, TSc D (k3q1pCyc β1 β6 γ6 (i + 1) - k3q1pCyc β1 β6 γ6 i) ((1, 0, γ4) - k3q1pCyc β1 β6 γ6 i)
      (v1, v2, v3)) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have k1 := hD
  have kb1 := mul_pos hD hβ1
  have kb6 := mul_pos hD (lt_trans one_pos hβ6)
  have kb61 := mul_pos hD (sub_pos.2 hβ6)
  have kg6 := mul_pos hD hγ6
  have kg4 := mul_pos hD hγ4
  have kv1 := mul_pos hD hv1
  have kv2 := mul_pos hD (neg_pos.2 hv2)
  have kgv1 := mul_pos (mul_pos hD hγ6) hv1
  have kgv2 := mul_pos (mul_pos hD hγ6) (neg_pos.2 hv2)
  have kg4v1 := mul_pos (mul_pos hD hγ4) hv1
  have kg4v2 := mul_pos (mul_pos hD hγ4) (neg_pos.2 hv2)
  have ksv1 := mul_pos (mul_pos hD (sub_pos.2 hs)) hv1
  have kbv1 := mul_pos (mul_pos hD hβ1) hv1
  have kb6v1 := mul_pos (mul_pos hD (lt_trans one_pos hβ6)) hv1
  have kb61v1 := mul_pos (mul_pos hD (sub_pos.2 hβ6)) hv1
  refine ⟨?_, ?_⟩ <;> intro i <;>
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, k3q1pCyc, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

theorem k3q1pCyc_inj {β1 β6 γ6 : ℝ} (hβ1 : 0 < β1) (hβ6 : 1 < β6) (hγ6 : 0 < γ6) :
    ∀ i j, k3q1pCyc β1 β6 γ6 i = k3q1pCyc β1 β6 γ6 j → i = j := by
  intro i j h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [k3q1pCyc, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h)

set_option maxHeartbeats 1600000 in
/-- **The cell `Q1⁺` at the base view `r`** (frame form).  `V` consists of the seven frame points over `d`
(header); `β6 > 1`, `C = ⟪q, r⟫ > 0`, `s₁ = (β6 - β1) C + γ6 A - B > 0`. -/
theorem k3q1p_hasLexCellAt (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0)
    {β1 γ4 β6 γ6 : ℝ} (hβ1 : 0 < β1) (hγ4 : 0 < γ4) (hβ6 : 1 < β6) (hγ6 : 0 < γ6) (hs : 1 < β6 + γ6)
    (hC : 0 < ⟪q, r⟫) (hs1 : 0 < (β6 - β1) * ⟪q, r⟫ + γ6 * ⟪r, r⟫ - ⟪p, r⟫)
    (hmem : ∀ i, fpoint p q r d (k3q1pCyc β1 β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint p q r d (0, 0, 1) ∨ y = fpoint p q r d (0, 0, 0) ∨
      y = fpoint p q r d (1, 0, 0) ∨ y = fpoint p q r d (1, β1, 0) ∨ y = fpoint p q r d (0, β6, γ6) ∨
      y = fpoint p q r d (0, 1, 0) ∨ y = fpoint p q r d (1, 0, γ4)) :
    HasLexCellAt V r := by
  set Y := k3q1pCyc β1 β6 γ6 with hY
  obtain ⟨lam, hl0, hl1, hsep⟩ := exists_sep_tilt p q r d hΔ Y (k3q1pCyc_inj hβ1 hβ6 hγ6)
    (u1 := 1) (u2 := -1) (t1 := 1) (t2 := 0) (by norm_num) (lo := 0) (hi := 1) (by norm_num)
  set vv := fcomb p q r (1 + lam * 1) (-1 + lam * 0) 0 with hvv
  have hv1 : 0 < 1 + lam * 1 := by linarith
  have hv2 : -1 + lam * 0 < 0 := by linarith
  have hr0 : r ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  have hA : 0 < ⟪r, r⟫ := real_inner_self_pos.2 hr0
  have n0 : -(0 : ZMod 5) = 0 := by decide
  have n1 : -(1 : ZMod 5) = 4 := by decide
  have n2 : -(2 : ZMod 5) = 3 := by decide
  have n3 : -(3 : ZMod 5) = 2 := by decide
  have n4 : -(4 : ZMod 5) = 1 := by decide
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint p q r d t, r⟫ = ⟪d, r⟫ + t.1 * ⟪p, r⟫ + t.2.1 * ⟪q, r⟫ + t.2.2 * ⟪r, r⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  -- lex unimodality of `Y = (c, d, a, c', a')`: `d < c`, `a < c'`, `c' < a'`
  have hlexY : LexUni (fun i => ⟪fpoint p q r d (Y i), r⟫) (fun i => ⟪fpoint p q r d (Y i), vv⟫) := by
    refine lexUni5_top _ _ (fun i j h1 h2 => hsep _ _ h1 h2) ?_ ?_ ?_
    · left; simp only [hY, k3q1pCyc, pc5_0, pc5_1, hz]; nlinarith
    · left; simp only [hY, k3q1pCyc, pc5_2, pc5_3, hz]; nlinarith [mul_pos hβ1 hC]
    · left; simp only [hY, k3q1pCyc, pc5_3, pc5_4, hz]; nlinarith
  have hlexX : LexUni (fun i => ⟪fpoint p q r d (Y (-i)), r⟫) (fun i => ⟪fpoint p q r d (Y (-i)), vv⟫) :=
    lexUni_neg hlexY
  rcases hΔ.lt_or_gt with hneg | hpos
  · have hD : 0 < -det3 p q r := by linarith
    have hcyc := k3q1p_cyc (v2 := -1 + lam * 0) (v3 := 0) hD hβ1 hβ6 hγ6 hv1 hv2
    have hr := k3q1p_rest (v3 := 0) hD hβ1 hγ4 hβ6 hγ6 hs hv1 hv2
    refine ⟨5, inferInstance, fun i => fpoint p q r d (Y (-i)), vv, ?_⟩
    refine lexCell_coord V p q r d (by norm_num) (fun i => Y (-i)) (1 + lam * 1, -1 + lam * 0, 0)
      (fun i => hmem (-i)) (hcyc_rev hcyc) ?_ hlexX
    intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [n0, hY, k3q1pCyc, pc5_0])).elim
    · exact (hyx 4 (by simp only [n4, hY, k3q1pCyc, pc5_1])).elim
    · exact (hyx 3 (by simp only [n3, hY, k3q1pCyc, pc5_2])).elim
    · exact (hyx 2 (by simp only [n2, hY, k3q1pCyc, pc5_3])).elim
    · exact (hyx 1 (by simp only [n1, hY, k3q1pCyc, pc5_4])).elim
    · exact ⟨_, rfl, hrest_rev hr.1⟩
    · exact ⟨_, rfl, hrest_rev hr.2⟩
  · have hcyc := k3q1p_cyc (v2 := -1 + lam * 0) (v3 := 0) hpos hβ1 hβ6 hγ6 hv1 hv2
    have hr := k3q1p_rest (v3 := 0) hpos hβ1 hγ4 hβ6 hγ6 hs hv1 hv2
    refine ⟨5, inferInstance, fun i => fpoint p q r d (Y i), vv, ?_⟩
    refine lexCell_coord V p q r d (by norm_num) Y (1 + lam * 1, -1 + lam * 0, 0) hmem hcyc ?_ hlexY
    intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [hY, k3q1pCyc, pc5_0])).elim
    · exact (hyx 1 (by simp only [hY, k3q1pCyc, pc5_1])).elim
    · exact (hyx 2 (by simp only [hY, k3q1pCyc, pc5_2])).elim
    · exact (hyx 3 (by simp only [hY, k3q1pCyc, pc5_3])).elim
    · exact (hyx 4 (by simp only [hY, k3q1pCyc, pc5_4])).elim
    · exact ⟨_, rfl, hr.1⟩
    · exact ⟨_, rfl, hr.2⟩

end C2
end Type08Sp
end Minimality

