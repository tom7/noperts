module

public import Minimality.Type08S.C2K8J
public import Minimality.Type08S.C2K9A

@[expose] public section

/-!
# K9B: lex peak lemmas for the two 5-cycles at the view `b - d` and their `TSc` tables

Frame `(P, Q, R) = (c - d, a - d, b - d)`; coordinates `b = (0,0,1)`, `d = 0`, `c = (1,0,0)`, `a = (0,1,0)`,
`b' = (γ4, 1, 0)`, `c' = (0, 1, β1)`, `a' = (γ6, 0, β6)`.
* `k9Y1 = (b, d, c, b', c')` with the cone `v1 > 0 > v2`.
* `k9Y2 = (a, d, c, b', c')` with the cone `v1 < 0, v2 < 0`.
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem lexUni5_k9a (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (hdb : LexLt (z 1, w 1) (z 0, w 0)) (hdc : LexLt (z 1, w 1) (z 2, w 2))
    (h : (LexLt (z 0, w 0) (z 4, w 4) ∧ LexLt (z 4, w 4) (z 3, w 3)) ∨
      (LexLt (z 2, w 2) (z 3, w 3) ∧ LexLt (z 3, w 3) (z 4, w 4))) : LexUni z w := by
  classical
  refine ⟨hinj, ?_⟩
  have h23 : (z 2, w 2) ≠ (z 3, w 3) := by
    intro h; have := hinj 2 3 (congrArg Prod.fst h) (congrArg Prod.snd h); exact absurd this (by decide)
  have h04 : (z 0, w 0) ≠ (z 4, w 4) := by
    intro h; have := hinj 0 4 (congrArg Prod.fst h) (congrArg Prod.snd h); exact absurd this (by decide)
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
  have adb := lexLt_asymm hdb
  rcases h with ⟨hP1, hP2⟩ | ⟨hQ1, hQ2⟩
  · have a1 := lexLt_asymm hP1
    have a2 := lexLt_asymm hP2
    rcases lexLt_total h23 with t | t
    · have a3 := lexLt_asymm t
      simp [hdb, adb, hdc, hP1, hP2, a1, a2, t, a3]
    · have a3 := lexLt_asymm t
      simp [hdb, adb, hdc, hP1, hP2, a1, a2, t, a3]
  · have a1 := lexLt_asymm hQ1
    have a2 := lexLt_asymm hQ2
    rcases lexLt_total h04 with t | t
    · have a3 := lexLt_asymm t
      simp [hdb, adb, hdc, hQ1, hQ2, a1, a2, t, a3]
    · have a3 := lexLt_asymm t
      simp [hdb, adb, hdc, hQ1, hQ2, a1, a2, t, a3]

theorem lexUni5_k9b (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (hdc : LexLt (z 1, w 1) (z 2, w 2)) (hcb : LexLt (z 4, w 4) (z 3, w 3))
    (hA : LexLt (z 0, w 0) (z 4, w 4) ∨ LexLt (z 0, w 0) (z 1, w 1)) : LexUni z w := by
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
  have adc := lexLt_asymm hdc
  have acb := lexLt_asymm hcb
  have h0 : ¬ (LexLt (z 4, w 4) (z 0, w 0) ∧ LexLt (z 1, w 1) (z 0, w 0)) := by
    rintro ⟨x, y⟩
    rcases hA with hh | hh
    · exact lexLt_asymm hh x
    · exact lexLt_asymm hh y
  rcases lexLt_total h23 with t | t
  · have a3 := lexLt_asymm t
    simp [h0, hdc, adc, hcb, acb, t, a3]
  · have a3 := lexLt_asymm t
    simp [h0, hdc, adc, hcb, acb, t, a3]

end C2
end Type08Sp
end Minimality
