module

public import Minimality.Type08S.C2K5FE

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- ccw cycle `(c', a', b, d, a)` of box C1 in the `c - d` frame, `α1 ≥ 1`, `γ6 = 1`. -/
def k5fC1Cyc (α1 β1 β6 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  pc5 (α1, β1, 0) (0, β6, 1) (0, 1, 0) (0, 0, 0) (1, 0, 0)

set_option maxHeartbeats 1600000 in
theorem k5f_C1_cyc {α1 β1 β6 v1 v2 v3 : ℝ} (hα1 : 1 ≤ α1) (hβ1 : 0 < β1) (hβ6 : 1 < β6)
    (hv1 : v1 < 0) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k5fC1Cyc α1 β1 β6 (i + 1) - k5fC1Cyc α1 β1 β6 i)
        (k5fC1Cyc α1 β1 β6 j - k5fC1Cyc α1 β1 β6 i) (v1, v2, v3) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have a1 : 0 < α1 := by linarith
  have a3 : 0 < α1 * β6 - β6 + β1 := by nlinarith
  have a6 := sub_pos.2 hβ6
  have a7 := mul_pos hβ1 a6
  have a8 := neg_pos.2 hv1
  intro i j h1 h2'
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2' (by decide)).elim
    | (simp only [TSc, d3, k5fC1Cyc, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 1600000 in
theorem k5f_C1_rest {α1 β1 α4 γ4 β6 v1 v2 v3 : ℝ} (hα1 : 1 ≤ α1) (hβ1 : 0 < β1) (hα4 : 0 < α4)
    (hα41 : α4 < 1) (hγ4 : 0 < γ4) (hβ6 : 1 < β6) (hv1 : v1 < 0) (hv2 : v2 < 0) :
    (∀ i : ZMod 5, TSc 1 (k5fC1Cyc α1 β1 β6 (i + 1) - k5fC1Cyc α1 β1 β6 i)
      ((0, 0, 1) - k5fC1Cyc α1 β1 β6 i) (v1, v2, v3)) ∧
    (∀ i : ZMod 5, TSc 1 (k5fC1Cyc α1 β1 β6 (i + 1) - k5fC1Cyc α1 β1 β6 i)
      ((α4, 0, γ4) - k5fC1Cyc α1 β1 β6 i) (v1, v2, v3)) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have a1 : 0 < α1 := by linarith
  have a3 : 0 < α1 * β6 - β6 + β1 := by nlinarith
  have a6 := sub_pos.2 hβ6
  have a7 := mul_pos hβ1 a6
  have a8 := neg_pos.2 hv1
  have a9 := neg_pos.2 hv2
  have a10 := sub_pos.2 hα41
  have a11 := mul_pos hα4 a6
  have a12 := mul_pos hβ1 a10
  have a13 := mul_pos a8 hγ4
  have a14 := mul_pos a9 hγ4
  have a15 := mul_pos hα4 a9
  have a16 := mul_pos a10 a9
  have a17 := mul_pos a8 a9
  refine ⟨?_, ?_⟩ <;> intro i <;>
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, k5fC1Cyc, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

theorem k5f_C1_frame (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0)
    {α1 β1 α4 γ4 β6 : ℝ} (hα1 : 1 ≤ α1) (hβ1 : 0 < β1) (hα4 : 0 < α4) (hα41 : α4 < 1) (hγ4 : 0 < γ4)
    (hβ6 : 1 < β6)
    (hcase : 0 < ⟪q, r⟫ ∨ (⟪q, r⟫ < 0 ∧ 0 < (α1 - 1) * ⟪p, r⟫ + β1 * ⟪q, r⟫))
    (hmem : ∀ i, fpoint p q r d (k5fC1Cyc α1 β1 β6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint p q r d (α1, β1, 0) ∨ y = fpoint p q r d (0, β6, 1) ∨
      y = fpoint p q r d (0, 1, 0) ∨ y = fpoint p q r d (0, 0, 0) ∨ y = fpoint p q r d (1, 0, 0) ∨
      y = fpoint p q r d (0, 0, 1) ∨ y = fpoint p q r d (α4, 0, γ4)) :
    HasLexCellAt V r := by
  have hr0 : r ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  have hA : 0 < ⟪r, r⟫ := real_inner_self_pos.2 hr0
  have hinjX : ∀ i j, k5fC1Cyc α1 β1 β6 i = k5fC1Cyc α1 β1 β6 j → i = j := by
    intro i j h
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      simp only [k5fC1Cyc, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4, Prod.mk.injEq] at h <;>
      first | rfl | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h)
  refine cyc_cell V p q r d hΔ (k := 5) (by norm_num) (k5fC1Cyc α1 β1 β6) hinjX hmem
    [(0, 0, 1), (α4, 0, γ4)] ?_ (u1 := -1) (u2 := -1) (t1 := 1) (t2 := 0) (lo := 0) (hi := 1)
    (by norm_num) (by norm_num) (fun v1 v2 => v1 < 0 ∧ v2 < 0) ?_ ?_ ?_
  · intro y hy
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by simp [k5fC1Cyc, pc5_0]⟩
    · exact Or.inl ⟨1, by simp [k5fC1Cyc, pc5_1]⟩
    · exact Or.inl ⟨2, by simp [k5fC1Cyc, pc5_2]⟩
    · exact Or.inl ⟨3, by simp [k5fC1Cyc, pc5_3]⟩
    · exact Or.inl ⟨4, by simp [k5fC1Cyc, pc5_4]⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
  · intro lam hl0 hl1
    constructor <;> linarith
  · intro v1 v2 hv
    have hr := k5f_C1_rest (v3 := 0) hα1 hβ1 hα4 hα41 hγ4 hβ6 hv.1 hv.2
    refine ⟨k5f_C1_cyc hα1 hβ1 hβ6 hv.1, ?_⟩
    intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact hr.1 i
    · exact hr.2 i
  · intro v1 v2 hv hsep
    have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint p q r d t, r⟫ = ⟪d, r⟫ + t.1 * ⟪p, r⟫ + t.2.1 * ⟪q, r⟫ + t.2.2 * ⟪r, r⟫ :=
      fun t => inner_fpoint _ _ _ _ _ _
    rcases hcase with hD | ⟨hD, hζ⟩
    · rcases lt_or_ge (⟪p, r⟫) 0 with hB | hB
      · refine k5f_lexUni5_C1b _ _ hsep ?_ ?_ ?_
        · left; simp only [k5fC1Cyc, pc5_3, pc5_4, hz]; nlinarith
        · left; simp only [k5fC1Cyc, pc5_2, pc5_3, hz]; nlinarith
        · left; simp only [k5fC1Cyc, pc5_1, pc5_2, hz]; nlinarith [mul_pos (sub_pos.2 hβ6) hD]
      · refine k5f_lexUni5_C1a _ _ hsep ?_ ?_ ?_
        · left; simp only [k5fC1Cyc, pc5_2, pc5_3, hz]; nlinarith
        · left; simp only [k5fC1Cyc, pc5_1, pc5_2, hz]; nlinarith [mul_pos (sub_pos.2 hβ6) hD]
        · left; simp only [k5fC1Cyc, pc5_0, pc5_4, hz]
          nlinarith [mul_nonneg (sub_nonneg.2 hα1) hB, mul_pos hβ1 hD]
    · have hB : 0 < ⟪p, r⟫ := by
        by_contra hh; push Not at hh
        nlinarith [mul_nonneg (sub_nonneg.2 hα1) (neg_nonneg.2 hh), mul_pos hβ1 (neg_pos.2 hD)]
      refine k5f_lexUni5_C1c _ _ hsep ?_ ?_ ?_
      · left; simp only [k5fC1Cyc, pc5_2, pc5_3, hz]; nlinarith
      · left; simp only [k5fC1Cyc, pc5_3, pc5_4, hz]; nlinarith
      · left; simp only [k5fC1Cyc, pc5_0, pc5_4, hz]; nlinarith

end C2
end Type08Sp
end Minimality
