module

public import Minimality.Type08S.C2K5FC

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

set_option maxHeartbeats 800000 in
/-- 5-cycle, `P1 < P0`, `P2 < P3`, and `P4` above `P0` or above `P3`: exactly one lex peak. -/
theorem k5f_lexUni5_C2 (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h10 : LexLt (z 1, w 1) (z 0, w 0)) (h23 : LexLt (z 2, w 2) (z 3, w 3))
    (h4 : LexLt (z 0, w 0) (z 4, w 4) ∨ LexLt (z 3, w 3) (z 4, w 4)) : LexUni z w := by
  classical
  refine ⟨hinj, ?_⟩
  have h04 : (z 0, w 0) ≠ (z 4, w 4) := by
    intro h; have := hinj 0 4 (congrArg Prod.fst h) (congrArg Prod.snd h); exact absurd this (by decide)
  have h34 : (z 3, w 3) ≠ (z 4, w 4) := by
    intro h; have := hinj 3 4 (congrArg Prod.fst h) (congrArg Prod.snd h); exact absurd this (by decide)
  rw [Finset.card_filter]
  have hs : ∀ g : ZMod 5 → ℕ, ∑ i, g i = g 0 + g 1 + g 2 + g 3 + g 4 := fun g => Fin.sum_univ_five (f := g)
  rw [hs]
  have e0 : (0 : ZMod 5) - 1 = 4 := by decide
  have e1 : (1 : ZMod 5) - 1 = 0 := by decide
  have e2 : (2 : ZMod 5) - 1 = 1 := by decide
  have e3 : (3 : ZMod 5) - 1 = 2 := by decide
  have e4 : (4 : ZMod 5) - 1 = 3 := by decide
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  show (if LexLt (z (0 - 1), w (0 - 1)) (z 0, w 0) ∧ LexLt (z (0 + 1), w (0 + 1)) (z 0, w 0) then 1 else 0) +
    (if LexLt (z (1 - 1), w (1 - 1)) (z 1, w 1) ∧ LexLt (z (1 + 1), w (1 + 1)) (z 1, w 1) then 1 else 0) +
    (if LexLt (z (2 - 1), w (2 - 1)) (z 2, w 2) ∧ LexLt (z (2 + 1), w (2 + 1)) (z 2, w 2) then 1 else 0) +
    (if LexLt (z (3 - 1), w (3 - 1)) (z 3, w 3) ∧ LexLt (z (3 + 1), w (3 + 1)) (z 3, w 3) then 1 else 0) +
    (if LexLt (z (4 - 1), w (4 - 1)) (z 4, w 4) ∧ LexLt (z (4 + 1), w (4 + 1)) (z 4, w 4) then 1 else 0) = 1
  rw [e0, e1, e2, e3, e4, f0, f1, f2, f3, f4]
  have a10 := lexLt_asymm h10
  have a23 := lexLt_asymm h23
  rcases lexLt_total h04 with h | h <;> rcases lexLt_total h34 with h' | h' <;>
    have a := lexLt_asymm h <;> have a' := lexLt_asymm h' <;>
    first
    | (exfalso; rcases h4 with h4 | h4 <;> first | exact a h4 | exact a' h4)
    | simp [h, h', h10, h23, a, a', a10, a23]

theorem k5f_C2_frame (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0)
    {α1 β1 β6 α4 γ4 : ℝ} (hα1 : 1 ≤ α1) (hβ1 : 1 < β1) (hβ6 : 1 < β6) (hα4 : 0 < α4) (hα41 : α4 < 1)
    (hγ4 : 1 < γ4) (hD : ⟪q, r⟫ < 0) (hζ : (α1 - 1) * ⟪p, r⟫ + β1 * ⟪q, r⟫ < 0)
    (hmem : ∀ i, fpoint p q r d (k5fC2Cyc α1 β1 β6 α4 γ4 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint p q r d (1, 0, 0) ∨ y = fpoint p q r d (α1, β1, 0) ∨
      y = fpoint p q r d (0, β6, 1) ∨ y = fpoint p q r d (0, 0, 1) ∨ y = fpoint p q r d (α4, 0, γ4) ∨
      y = fpoint p q r d (0, 0, 0) ∨ y = fpoint p q r d (0, 1, 0)) :
    HasLexCellAt V r := by
  have hr0 : r ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  have hA : 0 < ⟪r, r⟫ := real_inner_self_pos.2 hr0
  have hinjX : ∀ i j, k5fC2Cyc α1 β1 β6 α4 γ4 i = k5fC2Cyc α1 β1 β6 α4 γ4 j → i = j := by
    intro i j h
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      simp only [k5fC2Cyc, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4, Prod.mk.injEq] at h <;>
      first | rfl | (exfalso; linarith [h.1, h.2.1, h.2.2])
  refine cyc_cell V p q r d hΔ (k := 5) (by norm_num) (k5fC2Cyc α1 β1 β6 α4 γ4) hinjX hmem
    [(0, 0, 0), (0, 1, 0)] ?_ (u1 := 1) (u2 := 1) (t1 := 1) (t2 := 0) (lo := 0) (hi := 1)
    (by norm_num) (by norm_num) (fun v1 v2 => 0 < v1 ∧ 0 < v2) ?_ ?_ ?_
  · intro y hy
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by simp [k5fC2Cyc, pc5_0]⟩
    · exact Or.inl ⟨1, by simp [k5fC2Cyc, pc5_1]⟩
    · exact Or.inl ⟨2, by simp [k5fC2Cyc, pc5_2]⟩
    · exact Or.inl ⟨3, by simp [k5fC2Cyc, pc5_3]⟩
    · exact Or.inl ⟨4, by simp [k5fC2Cyc, pc5_4]⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
  · intro lam hl0 hl1
    constructor <;> linarith
  · intro v1 v2 hv
    exact ⟨k5f_C2_cyc hα1 (by linarith) hβ6 hα4 hα41 (by linarith) (by linarith) hv.1 hv.2,
      k5f_C2_rest hα1 hβ1 hβ6 hα4 hα41 (by linarith) (by linarith) hv.1 hv.2⟩
  · intro v1 v2 hv hsep
    have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint p q r d t, r⟫ = ⟪d, r⟫ + t.1 * ⟪p, r⟫ + t.2.1 * ⟪q, r⟫ + t.2.2 * ⟪r, r⟫ :=
      fun t => inner_fpoint _ _ _ _ _ _
    refine k5f_lexUni5_C2 _ _ hsep ?_ ?_ ?_
    · left; simp only [k5fC2Cyc, pc5_0, pc5_1, hz]; nlinarith
    · left; simp only [k5fC2Cyc, pc5_2, pc5_3, hz]; nlinarith
    · rcases lt_or_ge (⟪p, r⟫) 0 with hB | hB
      · left; left; simp only [k5fC2Cyc, pc5_0, pc5_4, hz]
        nlinarith [mul_pos (sub_pos.2 hα41) (neg_pos.2 hB), mul_pos (by linarith : (0:ℝ) < γ4) hA]
      · right; left; simp only [k5fC2Cyc, pc5_3, pc5_4, hz]; nlinarith [mul_nonneg hα4.le hB, mul_pos (sub_pos.2 hγ4) hA]

end C2
end Type08Sp
end Minimality
