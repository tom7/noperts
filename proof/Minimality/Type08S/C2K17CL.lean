module

public import Minimality.Type08S.C2K17CK

@[expose] public section


/-!
# K17C / P3L: 4-cycle lex peak lemma, and the cell S3.4 / S3.6b cycles at `d - b`: cycle, injectivity, TSc.
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

/-- 4-cycle with the valley at `0`: `P0 < P1`, `P0 < P3`, `P3 < P2` ⟹ exactly one peak. -/
theorem k17c_lexUni4_valley (z w : ZMod 4 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h01 : LexLt (z 0, w 0) (z 1, w 1)) (h03 : LexLt (z 0, w 0) (z 3, w 3))
    (h32 : LexLt (z 3, w 3) (z 2, w 2)) : LexUni z w := by
  classical
  refine ⟨hinj, ?_⟩
  have h12 : (z 1, w 1) ≠ (z 2, w 2) := by
    intro h; have := hinj 1 2 (congrArg Prod.fst h) (congrArg Prod.snd h); exact absurd this (by decide)
  rw [Finset.card_filter]
  have hs : ∀ g : ZMod 4 → ℕ, ∑ i, g i = g 0 + g 1 + g 2 + g 3 := fun g => Fin.sum_univ_four (f := g)
  rw [hs]
  have e0 : (0 : ZMod 4) - 1 = 3 := by decide
  have e1 : (1 : ZMod 4) - 1 = 0 := by decide
  have e2 : (2 : ZMod 4) - 1 = 1 := by decide
  have e3 : (3 : ZMod 4) - 1 = 2 := by decide
  have f0 : (0 : ZMod 4) + 1 = 1 := by decide
  have f1 : (1 : ZMod 4) + 1 = 2 := by decide
  have f2 : (2 : ZMod 4) + 1 = 3 := by decide
  have f3 : (3 : ZMod 4) + 1 = 0 := by decide
  show (if LexLt (z (0 - 1), w (0 - 1)) (z 0, w 0) ∧ LexLt (z (0 + 1), w (0 + 1)) (z 0, w 0) then 1 else 0) +
    (if LexLt (z (1 - 1), w (1 - 1)) (z 1, w 1) ∧ LexLt (z (1 + 1), w (1 + 1)) (z 1, w 1) then 1 else 0) +
    (if LexLt (z (2 - 1), w (2 - 1)) (z 2, w 2) ∧ LexLt (z (2 + 1), w (2 + 1)) (z 2, w 2) then 1 else 0) +
    (if LexLt (z (3 - 1), w (3 - 1)) (z 3, w 3) ∧ LexLt (z (3 + 1), w (3 + 1)) (z 3, w 3) then 1 else 0) = 1
  rw [e0, e1, e2, e3, f0, f1, f2, f3]
  have a01 := lexLt_asymm h01
  have a03 := lexLt_asymm h03
  have a32 := lexLt_asymm h32
  rcases lexLt_total h12 with h | h <;> have a := lexLt_asymm h <;>
    simp [h, a, h01, a01, h03, a03, h32, a32]

end C2
end Type08Sp
end Minimality
