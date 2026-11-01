module

public import Minimality.Type08S.C2K3A

@[expose] public section

/-!
# C2 / K3B: two 6-cycle peak lemmas for package K3
* `lexUni6_top2`: `P1 < P0`, `P2 < P3 < P4`, and `P4 < P5 ∨ P0 < P5` (`P5` not a valley): one peak
  (cells `Q1⁻`, `Q4⁺` main (reversed), `Q2⁻`).
* `lexUni6_peak0`: `P1 < P0`, `P2 < P1`, `P3 < P2`, `P4 < P5 < P0`: the only peak is `P0` (cell `Q4⁺` on the level face).
-/
set_option autoImplicit true

open Finset

namespace Minimality
namespace Type08Sp
namespace C2

private theorem z6_shifts : (0 : ZMod 6) - 1 = 5 ∧ (1 : ZMod 6) - 1 = 0 ∧ (2 : ZMod 6) - 1 = 1 ∧
    (3 : ZMod 6) - 1 = 2 ∧ (4 : ZMod 6) - 1 = 3 ∧ (5 : ZMod 6) - 1 = 4 ∧
    (0 : ZMod 6) + 1 = 1 ∧ (1 : ZMod 6) + 1 = 2 ∧ (2 : ZMod 6) + 1 = 3 ∧ (3 : ZMod 6) + 1 = 4 ∧
    (4 : ZMod 6) + 1 = 5 ∧ (5 : ZMod 6) + 1 = 0 := by decide

theorem lexUni6_top2 (z w : ZMod 6 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h10 : LexLt (z 1, w 1) (z 0, w 0)) (h23 : LexLt (z 2, w 2) (z 3, w 3))
    (h34 : LexLt (z 3, w 3) (z 4, w 4))
    (h5 : LexLt (z 4, w 4) (z 5, w 5) ∨ LexLt (z 0, w 0) (z 5, w 5)) : LexUni z w := by
  classical
  refine ⟨hinj, ?_⟩
  have h50 : (z 5, w 5) ≠ (z 0, w 0) := by
    intro h; have := hinj 5 0 (congrArg Prod.fst h) (congrArg Prod.snd h); exact absurd this (by decide)
  have h45 : (z 4, w 4) ≠ (z 5, w 5) := by
    intro h; have := hinj 4 5 (congrArg Prod.fst h) (congrArg Prod.snd h); exact absurd this (by decide)
  rw [Finset.card_filter]
  have hs : ∀ g : ZMod 6 → ℕ, ∑ i, g i = g 0 + g 1 + g 2 + g 3 + g 4 + g 5 := fun g => Fin.sum_univ_six (f := g)
  rw [hs]
  obtain ⟨e0, e1, e2, e3, e4, e5, f0, f1, f2, f3, f4, f5⟩ := z6_shifts
  show (if LexLt (z (0 - 1), w (0 - 1)) (z 0, w 0) ∧ LexLt (z (0 + 1), w (0 + 1)) (z 0, w 0) then 1 else 0) +
    (if LexLt (z (1 - 1), w (1 - 1)) (z 1, w 1) ∧ LexLt (z (1 + 1), w (1 + 1)) (z 1, w 1) then 1 else 0) +
    (if LexLt (z (2 - 1), w (2 - 1)) (z 2, w 2) ∧ LexLt (z (2 + 1), w (2 + 1)) (z 2, w 2) then 1 else 0) +
    (if LexLt (z (3 - 1), w (3 - 1)) (z 3, w 3) ∧ LexLt (z (3 + 1), w (3 + 1)) (z 3, w 3) then 1 else 0) +
    (if LexLt (z (4 - 1), w (4 - 1)) (z 4, w 4) ∧ LexLt (z (4 + 1), w (4 + 1)) (z 4, w 4) then 1 else 0) +
    (if LexLt (z (5 - 1), w (5 - 1)) (z 5, w 5) ∧ LexLt (z (5 + 1), w (5 + 1)) (z 5, w 5) then 1 else 0) = 1
  rw [e0, e1, e2, e3, e4, e5, f0, f1, f2, f3, f4, f5]
  have a10 := lexLt_asymm h10
  have a23 := lexLt_asymm h23
  have a34 := lexLt_asymm h34
  rcases h5 with h5 | h5 <;> have a5 := lexLt_asymm h5
  · rcases lexLt_total h50 with h | h <;> have a := lexLt_asymm h <;>
      simp [h, a, h10, a10, h23, a23, h34, a34, h5, a5]
  · rcases lexLt_total h45 with h | h <;> have a := lexLt_asymm h <;>
      simp [h, a, h10, a10, h23, a23, h34, a34, h5, a5]

theorem lexUni6_peak0 (z w : ZMod 6 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h10 : LexLt (z 1, w 1) (z 0, w 0)) (h21 : LexLt (z 2, w 2) (z 1, w 1))
    (h32 : LexLt (z 3, w 3) (z 2, w 2)) (h45 : LexLt (z 4, w 4) (z 5, w 5))
    (h50 : LexLt (z 5, w 5) (z 0, w 0)) : LexUni z w := by
  classical
  refine ⟨hinj, ?_⟩
  rw [Finset.card_filter]
  have hs : ∀ g : ZMod 6 → ℕ, ∑ i, g i = g 0 + g 1 + g 2 + g 3 + g 4 + g 5 := fun g => Fin.sum_univ_six (f := g)
  rw [hs]
  obtain ⟨e0, e1, e2, e3, e4, e5, f0, f1, f2, f3, f4, f5⟩ := z6_shifts
  show (if LexLt (z (0 - 1), w (0 - 1)) (z 0, w 0) ∧ LexLt (z (0 + 1), w (0 + 1)) (z 0, w 0) then 1 else 0) +
    (if LexLt (z (1 - 1), w (1 - 1)) (z 1, w 1) ∧ LexLt (z (1 + 1), w (1 + 1)) (z 1, w 1) then 1 else 0) +
    (if LexLt (z (2 - 1), w (2 - 1)) (z 2, w 2) ∧ LexLt (z (2 + 1), w (2 + 1)) (z 2, w 2) then 1 else 0) +
    (if LexLt (z (3 - 1), w (3 - 1)) (z 3, w 3) ∧ LexLt (z (3 + 1), w (3 + 1)) (z 3, w 3) then 1 else 0) +
    (if LexLt (z (4 - 1), w (4 - 1)) (z 4, w 4) ∧ LexLt (z (4 + 1), w (4 + 1)) (z 4, w 4) then 1 else 0) +
    (if LexLt (z (5 - 1), w (5 - 1)) (z 5, w 5) ∧ LexLt (z (5 + 1), w (5 + 1)) (z 5, w 5) then 1 else 0) = 1
  rw [e0, e1, e2, e3, e4, e5, f0, f1, f2, f3, f4, f5]
  have a10 := lexLt_asymm h10
  have a21 := lexLt_asymm h21
  have a32 := lexLt_asymm h32
  have a45 := lexLt_asymm h45
  have a50 := lexLt_asymm h50
  simp [h10, a10, h21, a21, h32, a32, h45, a45, h50, a50]

end C2
end Type08Sp
end Minimality

