module

public import Minimality.Type08S.C2FA1

@[expose] public section

/-!
# C2 / FA2: the face cell of `Q_bc` at the edge view `a - d` (frame form)

Frame `p = b - d`, `q = c - d`, `r = a - d` (the base view), coordinates over `d`:
`d = 0, b = (1,0,0), c = (0,1,0), a = (0,0,1), c' = (β1,0,α1), b' = (0,γ4,α4), a' = (β6,γ6,0)`.
The screen (first two coordinates) shows the face `Q_bc = (d, b, a', c)` (convex: `β6, γ6 > 0`, `β6 + γ6 > 1`);
`a` sits over `d`, `c'` on the line of the side `[d, b]` (inside iff `β1 < 1`), `b'` on the line of `[c, d]`
(inside iff `γ4 < 1`).  With a tilt `v = (v1, v2, *)`, `v1, v2 < 0`, every test passes; the depths and the
tilt values are affine on the face, so the cycle is lex unimodal (`lexUni4_conv`) once the tilt separates the
four vertices (`exists_tilt_avoid`).
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- The face cycle `(d, b, a', c)` in frame coordinates. -/
def faCyc (β6 γ6 : ℝ) : ZMod 4 → ℝ × ℝ × ℝ := ![(0, 0, 0), (1, 0, 0), (β6, γ6, 0), (0, 1, 0)]

theorem faCyc_0 : faCyc β6 γ6 0 = (0, 0, 0) := rfl
theorem faCyc_1 : faCyc β6 γ6 1 = (1, 0, 0) := rfl
theorem faCyc_2 : faCyc β6 γ6 2 = (β6, γ6, 0) := rfl
theorem faCyc_3 : faCyc β6 γ6 3 = (0, 1, 0) := rfl

theorem z4_add : (0 : ZMod 4) + 1 = 1 ∧ (1 : ZMod 4) + 1 = 2 ∧ (2 : ZMod 4) + 1 = 3 ∧ (3 : ZMod 4) + 1 = 0 := by
  decide

set_option maxHeartbeats 1600000 in
theorem faA_cyc {D β6 γ6 v1 v2 v3 : ℝ} (hD : 0 < D) (hb : 0 < β6) (hg : 0 < γ6) (hs : 1 < β6 + γ6) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      TSc D (faCyc β6 γ6 (i + 1) - faCyc β6 γ6 i) (faCyc β6 γ6 j - faCyc β6 γ6 i) (v1, v2, v3) := by
  obtain ⟨s0, s1, s2, s3⟩ := z4_add
  have k1 := hD
  have kb := mul_pos hD hb
  have kg := mul_pos hD hg
  have ks := mul_pos hD (sub_pos.2 hs)
  intro i j h1 h2
  rcases z4_cases i with rfl | rfl | rfl | rfl <;>
    rcases z4_cases j with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2 (by decide)).elim
    | (simp only [TSc, d3, faCyc_0, faCyc_1, faCyc_2, faCyc_3, s0, s1, s2, s3, Prod.fst_sub, Prod.snd_sub,
          Prod.mk_sub_mk]
       left; nlinarith)

set_option maxHeartbeats 1600000 in
theorem faA_rest {D β6 γ6 α1 β1 α4 γ4 v1 v2 v3 : ℝ} (hD : 0 < D) (hb : 0 < β6) (hg : 0 < γ6)
    (hs : 1 < β6 + γ6) (hα1 : 0 < α1) (hβ1 : 0 < β1) (hβ11 : β1 < 1) (hα4 : 0 < α4) (hγ4 : 0 < γ4)
    (hγ41 : γ4 < 1) (hv1 : v1 < 0) (hv2 : v2 < 0) :
    (∀ i : ZMod 4, TSc D (faCyc β6 γ6 (i + 1) - faCyc β6 γ6 i) ((0, 0, 1) - faCyc β6 γ6 i) (v1, v2, v3)) ∧
    (∀ i : ZMod 4, TSc D (faCyc β6 γ6 (i + 1) - faCyc β6 γ6 i) ((β1, 0, α1) - faCyc β6 γ6 i) (v1, v2, v3)) ∧
    (∀ i : ZMod 4, TSc D (faCyc β6 γ6 (i + 1) - faCyc β6 γ6 i) ((0, γ4, α4) - faCyc β6 γ6 i) (v1, v2, v3)) := by
  obtain ⟨s0, s1, s2, s3⟩ := z4_add
  have k1 := hD
  have kb := mul_pos hD hb
  have kg := mul_pos hD hg
  have ks := mul_pos hD (sub_pos.2 hs)
  have kv1 := mul_pos hD (neg_pos.2 hv1)
  have kv2 := mul_pos hD (neg_pos.2 hv2)
  have ka1 := mul_pos (mul_pos hD hα1) (neg_pos.2 hv2)
  have ka4 := mul_pos (mul_pos hD hα4) (neg_pos.2 hv1)
  have kb1 := mul_pos hD hβ1
  have kg4 := mul_pos hD hγ4
  have kc1 := mul_pos (mul_pos hD hg) (sub_pos.2 hβ11)
  have kc2 := mul_pos (mul_pos hD hβ1) (sub_pos.2 hs)
  have kc3 := mul_pos (mul_pos hD hb) (sub_pos.2 hβ11)
  have kd1 := mul_pos (mul_pos hD hγ4) (sub_pos.2 hs)
  have kd2 := mul_pos (mul_pos hD hg) (sub_pos.2 hγ41)
  have kd3 := mul_pos (mul_pos hD hb) (sub_pos.2 hγ41)
  refine ⟨?_, ?_, ?_⟩ <;> intro i <;>
  rcases z4_cases i with rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, faCyc_0, faCyc_1, faCyc_2, faCyc_3, s0, s1, s2, s3, Prod.fst_sub, Prod.snd_sub,
        Prod.mk_sub_mk]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 1600000 in
/-- **Face cell of `Q_bc` at the base view `r`** (frame form).  `V` consists of the seven frame points over
`d` listed in the header; `β1 < 1` and `γ4 < 1` put `c'` and `b'` inside the face's screen. -/
theorem faA_hasLexCellAt (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0)
    {α1 β1 α4 γ4 β6 γ6 : ℝ} (hb : 0 < β6) (hg : 0 < γ6) (hs : 1 < β6 + γ6) (hα1 : 0 < α1) (hβ1 : 0 < β1)
    (hβ11 : β1 < 1) (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hγ41 : γ4 < 1)
    (hmem : ∀ i, fpoint p q r d (faCyc β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint p q r d (0, 0, 0) ∨ y = fpoint p q r d (1, 0, 0) ∨
      y = fpoint p q r d (β6, γ6, 0) ∨ y = fpoint p q r d (0, 1, 0) ∨ y = fpoint p q r d (0, 0, 1) ∨
      y = fpoint p q r d (β1, 0, α1) ∨ y = fpoint p q r d (0, γ4, α4)) :
    HasLexCellAt V r := by
  obtain ⟨lam, hl0, hl1, hL⟩ := exists_tilt_avoid p q r hΔ (lo := 0) (hi := 1) (by norm_num)
    [(1, 0), (β6, γ6), (0, 1), (β6 - 1, γ6), (-1, 1), (β6, γ6 - 1)] (by
      intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> intro h <;>
        simp only [Prod.mk.injEq] at h <;> first | (norm_num at h; done) | (linarith [h.1, h.2]))
  set vv := fcomb p q r (-lam) (-1) 0 with hvv
  set Pv := ⟪p, vv⟫
  set Qv := ⟪q, vv⟫
  have hLv : ∀ x y : ℝ, ⟪fcomb p q r x y 0, vv⟫ = x * Pv + y * Qv := by
    intro x y; rw [inner_fcomb_left]; ring
  have hL' : ∀ t ∈ [((1 : ℝ), (0 : ℝ)), (β6, γ6), (0, 1), (β6 - 1, γ6), (-1, 1), (β6, γ6 - 1)],
      t.1 * Pv + t.2 * Qv ≠ 0 := by
    intro t ht; rw [← hLv]; exact hL t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hL'
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hL'
  have hz : ∀ i, ⟪fpoint p q r d (faCyc β6 γ6 i), r⟫ = ⟪d, r⟫ + (faCyc β6 γ6 i).1 * ⟪p, r⟫ +
      (faCyc β6 γ6 i).2.1 * ⟪q, r⟫ + (faCyc β6 γ6 i).2.2 * ⟪r, r⟫ := fun i => inner_fpoint _ _ _ _ _ _
  have hw : ∀ i, ⟪fpoint p q r d (faCyc β6 γ6 i), vv⟫ = ⟪d, vv⟫ + (faCyc β6 γ6 i).1 * Pv +
      (faCyc β6 γ6 i).2.1 * Qv + (faCyc β6 γ6 i).2.2 * ⟪r, vv⟫ := fun i => inner_fpoint _ _ _ _ _ _
  have hlex : LexUni (fun i => ⟪fpoint p q r d (faCyc β6 γ6 i), r⟫)
      (fun i => ⟪fpoint p q r d (faCyc β6 γ6 i), vv⟫) := by
    refine lexUni4_conv _ _ hb hg hs ?_ ?_ ?_
    · simp only [faCyc_0, faCyc_1, faCyc_2, faCyc_3, inner_fpoint]; ring
    · simp only [faCyc_0, faCyc_1, faCyc_2, faCyc_3, inner_fpoint]; ring
    · intro i j _ hwij
      simp only [hw] at hwij
      rcases z4_cases i with rfl | rfl | rfl | rfl <;>
        rcases z4_cases j with rfl | rfl | rfl | rfl <;>
        simp only [faCyc_0, faCyc_1, faCyc_2, faCyc_3] at hwij <;>
        first
        | rfl
        | (exfalso; apply e1; linarith)
        | (exfalso; apply e2; linarith)
        | (exfalso; apply e3; linarith)
        | (exfalso; apply e4; linarith)
        | (exfalso; apply e5; linarith)
        | (exfalso; apply e6; linarith)
  have n0 : -(0 : ZMod 4) = 0 := by decide
  have n1 : -(1 : ZMod 4) = 3 := by decide
  have n2 : -(2 : ZMod 4) = 2 := by decide
  have n3 : -(3 : ZMod 4) = 1 := by decide
  have hv1 : -lam < 0 := by linarith
  have hv2 : (-1 : ℝ) < 0 := by norm_num
  rcases hΔ.lt_or_gt with hneg | hpos
  · have hD : 0 < -det3 p q r := by linarith
    have hcyc := faA_cyc (v1 := -lam) (v2 := -1) (v3 := 0) hD hb hg hs
    have hr := faA_rest (v3 := 0) hD hb hg hs hα1 hβ1 hβ11 hα4 hγ4 hγ41 hv1 hv2
    refine ⟨4, inferInstance, fun i => fpoint p q r d (faCyc β6 γ6 (-i)), vv, ?_⟩
    refine lexCell_coord V p q r d (by norm_num) (fun i => faCyc β6 γ6 (-i)) (-lam, -1, 0) (fun i => hmem (-i))
      (hcyc_rev hcyc) ?_ (lexUni_neg hlex)
    intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [n0, faCyc_0])).elim
    · exact (hyx 3 (by simp only [n3, faCyc_1])).elim
    · exact (hyx 2 (by simp only [n2, faCyc_2])).elim
    · exact (hyx 1 (by simp only [n1, faCyc_3])).elim
    · exact ⟨_, rfl, hrest_rev hr.1⟩
    · exact ⟨_, rfl, hrest_rev hr.2.1⟩
    · exact ⟨_, rfl, hrest_rev hr.2.2⟩
  · have hcyc := faA_cyc (v1 := -lam) (v2 := -1) (v3 := 0) hpos hb hg hs
    have hr := faA_rest (v3 := 0) hpos hb hg hs hα1 hβ1 hβ11 hα4 hγ4 hγ41 hv1 hv2
    refine ⟨4, inferInstance, fun i => fpoint p q r d (faCyc β6 γ6 i), vv, ?_⟩
    refine lexCell_coord V p q r d (by norm_num) (faCyc β6 γ6) (-lam, -1, 0) hmem hcyc ?_ hlex
    intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [faCyc_0])).elim
    · exact (hyx 1 (by simp only [faCyc_1])).elim
    · exact (hyx 2 (by simp only [faCyc_2])).elim
    · exact (hyx 3 (by simp only [faCyc_3])).elim
    · exact ⟨_, rfl, hr.1⟩
    · exact ⟨_, rfl, hr.2.1⟩
    · exact ⟨_, rfl, hr.2.2⟩

end C2
end Type08Sp
end Minimality
