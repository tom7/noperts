module

public import Minimality.Type08S.C2K17GD5A

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

theorem k17gd_z4 : (0 : ZMod 4) - 1 = 3 ∧ (1 : ZMod 4) - 1 = 0 ∧ (2 : ZMod 4) - 1 = 1 ∧ (3 : ZMod 4) - 1 = 2 ∧
    (0 : ZMod 4) + 1 = 1 ∧ (1 : ZMod 4) + 1 = 2 ∧ (2 : ZMod 4) + 1 = 3 ∧ (3 : ZMod 4) + 1 = 0 := by decide

/-- Cell E1 `(a, b', a', b, d)`: `b < d`, `a' < b'`, `a` not a valley. -/
theorem k17gd_lexUni5_E1 (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h34 : LexLt (z 3, w 3) (z 4, w 4)) (h21 : LexLt (z 2, w 2) (z 1, w 1))
    (h0 : LexLt (z 4, w 4) (z 0, w 0) ∨ LexLt (z 1, w 1) (z 0, w 0)) : LexUni z w := by
  obtain ⟨t0, t1, t2, t3, t4, s0, s1, s2, s3, s4⟩ := k17gd_z5
  rcases lexLt_total (k17gd_ne5 hinj (show (0 : ZMod 5) ≠ 4 by decide)) with h04 | h40
  · -- 0 < 4: then 1 < 0 by h0, peak at 4
    have h10 : LexLt (z 1, w 1) (z 0, w 0) := by
      rcases h0 with h | h
      · exact absurd h (lexLt_asymm h04)
      · exact h
    refine k17gd_lexUni_nb z w hinj 4 (by rw [t4, s4]; exact ⟨h34, h04⟩) (fun i hi => ?_)
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · rw [t0]; left; exact h04
    · rw [t1]; left; exact h10
    · rw [t2]; left; exact h21
    · rw [s3]; right; exact h34
    · exact absurd rfl hi
  · rcases lexLt_total (k17gd_ne5 hinj (show (0 : ZMod 5) ≠ 1 by decide)) with h01 | h10
    · -- 4 < 0 < 1: peak at 1
      refine k17gd_lexUni_nb z w hinj 1 (by rw [t1, s1]; exact ⟨h01, h21⟩) (fun i hi => ?_)
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · rw [s0]; right; exact h01
      · exact absurd rfl hi
      · rw [t2]; left; exact h21
      · rw [s3]; right; exact h34
      · rw [s4]; right; exact h40
    · -- peak at 0
      refine k17gd_lexUni_nb z w hinj 0 (by rw [t0, s0]; exact ⟨h40, h10⟩) (fun i hi => ?_)
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · exact absurd rfl hi
      · rw [t1]; left; exact h10
      · rw [t2]; left; exact h21
      · rw [s3]; right; exact h34
      · rw [s4]; right; exact h40

/-- Cell E2 `(c', b', a', b)`: `b' < a'`, `c' < b`: the peak is the larger of `a', b`. -/
theorem k17gd_lexUni4_E2 (z w : ZMod 4 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h12 : LexLt (z 1, w 1) (z 2, w 2)) (h03 : LexLt (z 0, w 0) (z 3, w 3)) : LexUni z w := by
  obtain ⟨t0, t1, t2, t3, s0, s1, s2, s3⟩ := k17gd_z4
  have hne : (z 2, w 2) ≠ (z 3, w 3) := fun h' =>
    absurd (hinj 2 3 (congrArg Prod.fst h') (congrArg Prod.snd h')) (by decide)
  rcases lexLt_total hne with h23 | h32
  · refine k17gd_lexUni_nb z w hinj 3 (by rw [t3, s3]; exact ⟨h23, h03⟩) (fun i hi => ?_)
    rcases z4_cases i with rfl | rfl | rfl | rfl
    · rw [t0]; left; exact h03
    · rw [s1]; right; exact h12
    · rw [s2]; right; exact h23
    · exact absurd rfl hi
  · refine k17gd_lexUni_nb z w hinj 2 (by rw [t2, s2]; exact ⟨h12, h32⟩) (fun i hi => ?_)
    rcases z4_cases i with rfl | rfl | rfl | rfl
    · rw [t0]; left; exact h03
    · rw [s1]; right; exact h12
    · exact absurd rfl hi
    · rw [t3]; left; exact h32

end C2
end Type08Sp
end Minimality
