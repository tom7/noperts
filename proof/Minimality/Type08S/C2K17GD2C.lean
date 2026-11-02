module

public import Minimality.Type08S.C2K17GD2B

@[expose] public section


set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem k17gd_ll {a b c d : ℝ} (h : a < c) : LexLt (a, b) (c, d) := Or.inl h
theorem k17gd_ll' {a b c d : ℝ} (h : a = c) (h2 : b < d) : LexLt (a, b) (c, d) := Or.inr ⟨h, h2⟩

theorem k17gd_ne5 {z w : ZMod 5 → ℝ} (hinj : ∀ i j, z i = z j → w i = w j → i = j) {i j : ZMod 5} (h : i ≠ j) :
    (z i, w i) ≠ (z j, w j) := fun h' =>
  h (hinj i j (congrArg Prod.fst h') (congrArg Prod.snd h'))

/-- Cell A lex (cycle `a, c', a', c, d`): `d < c < a'` and `a` is not a peak. -/
theorem k17gd_lexUni5_A (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h32 : LexLt (z 3, w 3) (z 2, w 2)) (h43 : LexLt (z 4, w 4) (z 3, w 3))
    (h0 : LexLt (z 0, w 0) (z 4, w 4) ∨ LexLt (z 0, w 0) (z 1, w 1)) : LexUni z w := by
  obtain ⟨t0, t1, t2, t3, t4, s0, s1, s2, s3, s4⟩ := k17gd_z5
  rcases lexLt_total (k17gd_ne5 hinj (show (1 : ZMod 5) ≠ 2 by decide)) with h | h
  · refine k17gd_lexUni_nb z w hinj 2 (by rw [t2, s2]; exact ⟨h, h32⟩) (fun i hi => ?_)
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · rw [t0, s0]; exact h0
    · rw [s1]; right; exact h
    · exact absurd rfl hi
    · rw [t3]; left; exact h32
    · rw [t4]; left; exact h43
  · have h01 : LexLt (z 0, w 0) (z 1, w 1) := by
      rcases h0 with h0 | h0
      · exact lexLt_trans_K2 h0 (lexLt_trans_K2 h43 (lexLt_trans_K2 h32 h))
      · exact h0
    refine k17gd_lexUni_nb z w hinj 1 (by rw [t1, s1]; exact ⟨h01, h⟩) (fun i hi => ?_)
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · rw [s0]; right; exact h01
    · exact absurd rfl hi
    · rw [t2]; left; exact h
    · rw [t3]; left; exact h32
    · rw [t4]; left; exact h43

/-- Cell A lex, `a'` below `c` (tie in `z`, decided by `w`): peak at `c`. -/
theorem k17gd_lexUni5_A2 (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h23 : LexLt (z 2, w 2) (z 3, w 3)) (h43 : LexLt (z 4, w 4) (z 3, w 3))
    (h12 : LexLt (z 1, w 1) (z 2, w 2))
    (h0 : LexLt (z 0, w 0) (z 4, w 4) ∨ LexLt (z 0, w 0) (z 1, w 1)) : LexUni z w := by
  obtain ⟨t0, t1, t2, t3, t4, s0, s1, s2, s3, s4⟩ := k17gd_z5
  refine k17gd_lexUni_nb z w hinj 3 (by rw [t3, s3]; exact ⟨h23, h43⟩) (fun i hi => ?_)
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
  · rw [t0, s0]; exact h0
  · rw [s1]; right; exact h12
  · rw [s2]; right; exact h23
  · exact absurd rfl hi
  · rw [t4]; left; exact h43

/-- Cell B lex (cycle `c', b', c, d, b`): `c < d < b` and if `b` is the peak then `b'` is not. -/
theorem k17gd_lexUni5_B (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h23 : LexLt (z 2, w 2) (z 3, w 3)) (h34 : LexLt (z 3, w 3) (z 4, w 4))
    (h : LexLt (z 0, w 0) (z 4, w 4) → (LexLt (z 1, w 1) (z 0, w 0) ∨ LexLt (z 1, w 1) (z 2, w 2))) :
    LexUni z w := by
  obtain ⟨t0, t1, t2, t3, t4, s0, s1, s2, s3, s4⟩ := k17gd_z5
  rcases lexLt_total (k17gd_ne5 hinj (show (0 : ZMod 5) ≠ 4 by decide)) with h04 | h40
  · refine k17gd_lexUni_nb z w hinj 4 (by rw [t4, s4]; exact ⟨h34, h04⟩) (fun i hi => ?_)
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · rw [t0]; left; exact h04
    · rcases h h04 with h1 | h1
      · rw [t1]; left; exact h1
      · rw [s1]; right; exact h1
    · rw [s2]; right; exact h23
    · rw [s3]; right; exact h34
    · exact absurd rfl hi
  · rcases lexLt_total (k17gd_ne5 hinj (show (0 : ZMod 5) ≠ 1 by decide)) with h01 | h10
    · have h21 : LexLt (z 2, w 2) (z 1, w 1) :=
        lexLt_trans_K2 h23 (lexLt_trans_K2 h34 (lexLt_trans_K2 h40 h01))
      refine k17gd_lexUni_nb z w hinj 1 (by rw [t1, s1]; exact ⟨h01, h21⟩) (fun i hi => ?_)
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · rw [s0]; right; exact h01
      · exact absurd rfl hi
      · rw [s2]; right; exact h23
      · rw [s3]; right; exact h34
      · rw [s4]; right; exact h40
    · refine k17gd_lexUni_nb z w hinj 0 (by rw [t0, s0]; exact ⟨h40, h10⟩) (fun i hi => ?_)
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · exact absurd rfl hi
      · rw [t1]; left; exact h10
      · rw [s2]; right; exact h23
      · rw [s3]; right; exact h34
      · rw [s4]; right; exact h40

end C2
end Type08Sp
end Minimality
