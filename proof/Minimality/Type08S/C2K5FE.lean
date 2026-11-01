module

public import Minimality.Type08S.C2K5FD

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- Shared reduction: a 5-cycle whose lex peaks are among `0, 1` and exactly one of them. -/
theorem k5f_lexUni5_core (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h2 : ¬ (LexLt (z 1, w 1) (z 2, w 2) ∧ LexLt (z 3, w 3) (z 2, w 2)))
    (h3 : ¬ (LexLt (z 2, w 2) (z 3, w 3) ∧ LexLt (z 4, w 4) (z 3, w 3)))
    (h4 : ¬ (LexLt (z 3, w 3) (z 4, w 4) ∧ LexLt (z 0, w 0) (z 4, w 4)))
    (h0 : LexLt (z 1, w 1) (z 0, w 0) → LexLt (z 4, w 4) (z 0, w 0)) (h1 : LexLt (z 0, w 0) (z 1, w 1) → LexLt (z 2, w 2) (z 1, w 1)) : LexUni z w := by
  classical
  refine ⟨hinj, ?_⟩
  have h01 : (z 0, w 0) ≠ (z 1, w 1) := by
    intro h; have := hinj 0 1 (congrArg Prod.fst h) (congrArg Prod.snd h); exact absurd this (by decide)
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
  rcases lexLt_total h01 with h | h <;> have a := lexLt_asymm h
  · have h1' := h1 h
    simp [h, a, h2, h3, h4, h1', lexLt_asymm h1']
  · have h0' := h0 h
    have : ¬ LexLt (z 2, w 2) (z 1, w 1) ∨ True := Or.inr trivial
    simp [h, a, h2, h3, h4, h0', lexLt_asymm h0', lexLt_asymm h]

/-- `d < b < a'` and `a < c'` (cycle `(c', a', b, d, a)`). -/
theorem k5f_lexUni5_C1a (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h43 : LexLt (z 3, w 3) (z 2, w 2)) (h32 : LexLt (z 2, w 2) (z 1, w 1))
    (h0 : LexLt (z 4, w 4) (z 0, w 0)) : LexUni z w := by
  refine k5f_lexUni5_core z w hinj ?_ ?_ ?_ (fun _ => h0) (fun _ => h32)
  · intro h; exact lexLt_asymm h32 h.1
  · intro h; exact lexLt_asymm h43 h.1
  · intro h; exact lexLt_asymm h0 h.2

/-- `a < d < b < a'` (cycle `(c', a', b, d, a)`), `c'` arbitrary. -/
theorem k5f_lexUni5_C1b (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h34 : LexLt (z 4, w 4) (z 3, w 3)) (h43 : LexLt (z 3, w 3) (z 2, w 2))
    (h32 : LexLt (z 2, w 2) (z 1, w 1)) : LexUni z w := by
  refine k5f_lexUni5_core z w hinj ?_ ?_ ?_ (fun h => ?_) (fun _ => h32)
  · intro h; exact lexLt_asymm h32 h.1
  · intro h; exact lexLt_asymm h43 h.1
  · intro h; exact lexLt_asymm h34 h.1
  · exact lexLt_trans_K2 h34 (lexLt_trans_K2 h43 (lexLt_trans_K2 h32 h))

/-- `b < d < a < c'` (cycle `(c', a', b, d, a)`), `a'` arbitrary. -/
theorem k5f_lexUni5_C1c (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h23 : LexLt (z 2, w 2) (z 3, w 3)) (h34 : LexLt (z 3, w 3) (z 4, w 4))
    (h40 : LexLt (z 4, w 4) (z 0, w 0)) : LexUni z w := by
  have h20 := lexLt_trans_K2 h23 (lexLt_trans_K2 h34 h40)
  refine k5f_lexUni5_core z w hinj ?_ ?_ ?_ (fun _ => h40) (fun h => lexLt_trans_K2 h20 h)
  · intro h; exact lexLt_asymm h23 h.2
  · intro h; exact lexLt_asymm h34 h.2
  · intro h; exact lexLt_asymm h40 h.2

end C2
end Type08Sp
end Minimality
