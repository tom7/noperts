module

public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-!
# Cyclic index lemmas for `ZMod 4`, `ZMod 5`, `ZMod 6`

The successor / predecessor tables and the case split of `ZMod k` for k = 4, 5, 6, stated once
(they were re-proved in L8Shapes, Prism, HEnd, CaseC18Step4, CaseC18M, Type02X, Type02V12,
Type16UE and Type16V2Pop).
-/

namespace Minimality

theorem zmod4_add_one : (0 : ZMod 4) + 1 = 1 ∧ (1 : ZMod 4) + 1 = 2 ∧ (2 : ZMod 4) + 1 = 3 ∧
    (3 : ZMod 4) + 1 = 0 := by decide

theorem zmod4_sub_one : (0 : ZMod 4) - 1 = 3 ∧ (1 : ZMod 4) - 1 = 0 ∧ (2 : ZMod 4) - 1 = 1 ∧
    (3 : ZMod 4) - 1 = 2 := by decide

theorem zmod4_cases (i : ZMod 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by revert i; decide

theorem zmod5_add_one :
    (0 : ZMod 5) + 1 = 1 ∧ (1 : ZMod 5) + 1 = 2 ∧ (2 : ZMod 5) + 1 = 3 ∧ (3 : ZMod 5) + 1 = 4 ∧
      (4 : ZMod 5) + 1 = 0 := by decide

theorem zmod5_sub_one :
    (0 : ZMod 5) - 1 = 4 ∧ (1 : ZMod 5) - 1 = 0 ∧ (2 : ZMod 5) - 1 = 1 ∧ (3 : ZMod 5) - 1 = 2 ∧
      (4 : ZMod 5) - 1 = 3 := by decide

theorem zmod5_cases (i : ZMod 5) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by revert i; decide

theorem zmod6_add_one : (0 : ZMod 6) + 1 = 1 ∧ (1 : ZMod 6) + 1 = 2 ∧ (2 : ZMod 6) + 1 = 3 ∧
    (3 : ZMod 6) + 1 = 4 ∧ (4 : ZMod 6) + 1 = 5 ∧ (5 : ZMod 6) + 1 = 0 := by decide

theorem zmod6_sub_one : (0 : ZMod 6) - 1 = 5 ∧ (1 : ZMod 6) - 1 = 0 ∧ (2 : ZMod 6) - 1 = 1 ∧
    (3 : ZMod 6) - 1 = 2 ∧ (4 : ZMod 6) - 1 = 3 ∧ (5 : ZMod 6) - 1 = 4 := by decide

theorem zmod6_cases (i : ZMod 6) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
  revert i; decide

end Minimality

end
