module

public import Minimality.Type08S.C2FB1

@[expose] public section

/-!
# C2 / FC1: two-candidate peak lemmas for 5- and 6-cycles (for package K1 and later cells)

A cyclic lex sequence whose only possible peaks are two adjacent positions is lex unimodal.
* `lexUni5_two`: `P1 < P2`, `P4 < P3`, `P0 < P1 ∨ P0 < P4` (peaks only at 2 or 3).
* `lexUni6_two`: `P0 < P1`, `P3 < P2`, `P5 < P0`, `P4 < P3 ∨ P4 < P5` (peaks only at 1 or 2).
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem lexUni5_two (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h12 : LexLt (z 1, w 1) (z 2, w 2)) (h43 : LexLt (z 4, w 4) (z 3, w 3))
    (h0 : LexLt (z 0, w 0) (z 1, w 1) ∨ LexLt (z 0, w 0) (z 4, w 4)) : LexUni z w := by
  classical
  refine ⟨hinj, ?_⟩
  have h23 : (z 2, w 2) ≠ (z 3, w 3) := by
    intro h; have := hinj 2 3 (congrArg Prod.fst h) (congrArg Prod.snd h); exact absurd this (by decide)
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
  have a12 := lexLt_asymm h12
  have a43 := lexLt_asymm h43
  rcases lexLt_total h23 with h | h <;> have a := lexLt_asymm h <;>
    rcases h0 with h0 | h0 <;> have a0 := lexLt_asymm h0 <;>
    simp [h, a, h12, a12, h43, a43, h0, a0]

theorem lexUni6_two (z w : ZMod 6 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h01 : LexLt (z 0, w 0) (z 1, w 1)) (h32 : LexLt (z 3, w 3) (z 2, w 2))
    (h50 : LexLt (z 5, w 5) (z 0, w 0))
    (h4 : LexLt (z 4, w 4) (z 3, w 3) ∨ LexLt (z 4, w 4) (z 5, w 5)) : LexUni z w := by
  classical
  refine ⟨hinj, ?_⟩
  have h12 : (z 1, w 1) ≠ (z 2, w 2) := by
    intro h; have := hinj 1 2 (congrArg Prod.fst h) (congrArg Prod.snd h); exact absurd this (by decide)
  rw [Finset.card_filter]
  have hs : ∀ g : ZMod 6 → ℕ, ∑ i, g i = g 0 + g 1 + g 2 + g 3 + g 4 + g 5 := fun g => Fin.sum_univ_six (f := g)
  rw [hs]
  have e0 : (0 : ZMod 6) - 1 = 5 := by decide
  have e1 : (1 : ZMod 6) - 1 = 0 := by decide
  have e2 : (2 : ZMod 6) - 1 = 1 := by decide
  have e3 : (3 : ZMod 6) - 1 = 2 := by decide
  have e4 : (4 : ZMod 6) - 1 = 3 := by decide
  have e5 : (5 : ZMod 6) - 1 = 4 := by decide
  have f0 : (0 : ZMod 6) + 1 = 1 := by decide
  have f1 : (1 : ZMod 6) + 1 = 2 := by decide
  have f2 : (2 : ZMod 6) + 1 = 3 := by decide
  have f3 : (3 : ZMod 6) + 1 = 4 := by decide
  have f4 : (4 : ZMod 6) + 1 = 5 := by decide
  have f5 : (5 : ZMod 6) + 1 = 0 := by decide
  show (if LexLt (z (0 - 1), w (0 - 1)) (z 0, w 0) ∧ LexLt (z (0 + 1), w (0 + 1)) (z 0, w 0) then 1 else 0) +
    (if LexLt (z (1 - 1), w (1 - 1)) (z 1, w 1) ∧ LexLt (z (1 + 1), w (1 + 1)) (z 1, w 1) then 1 else 0) +
    (if LexLt (z (2 - 1), w (2 - 1)) (z 2, w 2) ∧ LexLt (z (2 + 1), w (2 + 1)) (z 2, w 2) then 1 else 0) +
    (if LexLt (z (3 - 1), w (3 - 1)) (z 3, w 3) ∧ LexLt (z (3 + 1), w (3 + 1)) (z 3, w 3) then 1 else 0) +
    (if LexLt (z (4 - 1), w (4 - 1)) (z 4, w 4) ∧ LexLt (z (4 + 1), w (4 + 1)) (z 4, w 4) then 1 else 0) +
    (if LexLt (z (5 - 1), w (5 - 1)) (z 5, w 5) ∧ LexLt (z (5 + 1), w (5 + 1)) (z 5, w 5) then 1 else 0) = 1
  rw [e0, e1, e2, e3, e4, e5, f0, f1, f2, f3, f4, f5]
  have a01 := lexLt_asymm h01
  have a32 := lexLt_asymm h32
  have a50 := lexLt_asymm h50
  rcases lexLt_total h12 with h | h <;> have a := lexLt_asymm h <;>
    rcases h4 with h4 | h4 <;> have a4 := lexLt_asymm h4 <;>
    simp [h, a, h01, a01, h32, a32, h50, a50, h4, a4]

end C2
end Type08Sp
end Minimality
