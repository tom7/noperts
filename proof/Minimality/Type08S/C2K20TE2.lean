module

public import Minimality.Type08S.C2K20TE1
public import Minimality.Type08S.C2K19B

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

theorem k20t_ne5 {z w : ZMod 5 → ℝ} (hinj : ∀ i j, z i = z j → w i = w j → i = j) {i j : ZMod 5} (h : i ≠ j) :
    (z i, w i) ≠ (z j, w j) := fun h' => h (hinj i j (congrArg Prod.fst h') (congrArg Prod.snd h'))

/-- Lex unimodality of cell E: depths `z - rr, z - b1 rr, z, z, z - b6 rr`; `b1 < 1 ∨ b6 < 1`. -/
theorem k20tE_lex (zz ww : ZMod 5 → ℝ) (hinj : ∀ i j, zz i = zz j → ww i = ww j → i = j) {z rr b1 b6 : ℝ}
    (hrr : 0 < rr) (hb1 : 0 < b1) (hb6 : 0 < b6) (hlow : b1 < 1 ∨ b6 < 1)
    (h0 : zz 0 = z - rr) (h1 : zz 1 = z - b1 * rr) (h2 : zz 2 = z) (h3 : zz 3 = z) (h4 : zz 4 = z - b6 * rr) :
    LexUni zz ww := by
  obtain ⟨e0, e1, e2, e3, e4, f0, f1, f2, f3, f4⟩ := k19_z5
  have l10 : LexLt (zz 1, ww 1) (zz 2, ww 2) := Or.inl (by rw [h1, h2]; nlinarith)
  have l43 : LexLt (zz 4, ww 4) (zz 3, ww 3) := Or.inl (by rw [h4, h3]; nlinarith)
  have l0 : LexLt (zz 0, ww 0) (zz 4, ww 4) ∨ LexLt (zz 0, ww 0) (zz 1, ww 1) := by
    rcases hlow with h | h
    · right; left; show zz 0 < zz 1; rw [h0, h1]; nlinarith
    · left; left; show zz 0 < zz 4; rw [h0, h4]; nlinarith
  rcases lexLt_total (k20t_ne5 hinj (show (2 : ZMod 5) ≠ 3 by decide)) with h | h
  · refine k19_lexUni_nb zz ww hinj 3 ?_ ?_ ?_
    · rw [e3]; exact h
    · rw [f3]; exact l43
    · intro i hi
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · rw [e0, f0]; exact l0
      · right; rw [f1]; exact l10
      · right; rw [f2]; exact h
      · exact absurd rfl hi
      · left; rw [e4]; exact l43
  · refine k19_lexUni_nb zz ww hinj 2 ?_ ?_ ?_
    · rw [e2]; exact l10
    · rw [f2]; exact h
    · intro i hi
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · rw [e0, f0]; exact l0
      · right; rw [f1]; exact l10
      · exact absurd rfl hi
      · left; rw [e3]; exact h
      · left; rw [e4]; exact l43

end C2
end Type08Sp
end Minimality
