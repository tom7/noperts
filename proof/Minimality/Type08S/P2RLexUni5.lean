module

public import Minimality.Type08S.P2RDefs

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkR / R4a / LexUni5: lex unimodality of 5-cycles (general; R5 may reuse).
* `lexUni5_top`: pairs `u i = (z i, w i)` injective; `u 1 < u 0`, `u 2 < u 3 < u 4` (lex): LexUni.  (Two adjacent
  candidate peaks `4, 0`, the valley is `1` or `2`, whichever.)
* `lexUni_neg`: reversing the cycle `i ↦ -i` preserves LexUni (any `k`).
* `pc5`: the 5-cycle `![p0,…,p4]` on `ZMod 5`; `z5_cases`.
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

def pc5 {α : Type*} (p₀ p₁ p₂ p₃ p₄ : α) : ZMod 5 → α := ![p₀, p₁, p₂, p₃, p₄]

theorem pc5_0 {α : Type*} {w0 w1 w2 w3 w4 : α} : pc5 w0 w1 w2 w3 w4 0 = w0 := rfl
theorem pc5_1 {α : Type*} {w0 w1 w2 w3 w4 : α} : pc5 w0 w1 w2 w3 w4 1 = w1 := rfl
theorem pc5_2 {α : Type*} {w0 w1 w2 w3 w4 : α} : pc5 w0 w1 w2 w3 w4 2 = w2 := rfl
theorem pc5_3 {α : Type*} {w0 w1 w2 w3 w4 : α} : pc5 w0 w1 w2 w3 w4 3 = w3 := rfl
theorem pc5_4 {α : Type*} {w0 w1 w2 w3 w4 : α} : pc5 w0 w1 w2 w3 w4 4 = w4 := rfl


theorem z5_add : (0 : ZMod 5) + 1 = 1 ∧ (1 : ZMod 5) + 1 = 2 ∧ (2 : ZMod 5) + 1 = 3 ∧
    (3 : ZMod 5) + 1 = 4 ∧ (4 : ZMod 5) + 1 = 0 := by decide

theorem lexLt_asymm {p q : ℝ × ℝ} (h : LexLt p q) : ¬ LexLt q p := by
  unfold LexLt at *; rintro (h' | ⟨h1, h2⟩) <;> rcases h with h | ⟨h3, h4⟩ <;> first | linarith | skip

theorem lexLt_total {p q : ℝ × ℝ} (h : p ≠ q) : LexLt p q ∨ LexLt q p := by
  unfold LexLt
  rcases lt_trichotomy p.1 q.1 with h1 | h1 | h1
  · exact Or.inl (Or.inl h1)
  · rcases lt_trichotomy p.2 q.2 with h2 | h2 | h2
    · exact Or.inl (Or.inr ⟨h1, h2⟩)
    · exact absurd (Prod.ext h1 h2) h
    · exact Or.inr (Or.inr ⟨h1.symm, h2⟩)
  · exact Or.inr (Or.inl h1)

set_option maxHeartbeats 800000 in
/-- **5-cycle with two adjacent candidate peaks `4, 0`.** -/
theorem lexUni5_top (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h10 : LexLt (z 1, w 1) (z 0, w 0)) (h23 : LexLt (z 2, w 2) (z 3, w 3))
    (h34 : LexLt (z 3, w 3) (z 4, w 4)) : LexUni z w := by
  classical
  refine ⟨hinj, ?_⟩
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
  have a10 := lexLt_asymm h10
  have a23 := lexLt_asymm h23
  have a34 := lexLt_asymm h34
  rcases lexLt_total h04 with h | h
  · have a := lexLt_asymm h
    simp [h, h10, h23, h34, a, a10, a23, a34]
  · have a := lexLt_asymm h
    simp [h, h10, h23, h34, a, a10, a23, a34]

/-- Reversing the cycle preserves lex unimodality. -/
theorem lexUni_neg {k : ℕ} [NeZero k] {z w : ZMod k → ℝ} (h : LexUni z w) :
    LexUni (fun i => z (-i)) (fun i => w (-i)) := by
  classical
  refine ⟨fun i j h1 h2 => neg_injective (h.1 _ _ h1 h2), ?_⟩
  rw [← h.2]
  have key : ∀ i : ZMod k, (LexLt (z (-(i - 1)), w (-(i - 1))) (z (-i), w (-i)) ∧
      LexLt (z (-(i + 1)), w (-(i + 1))) (z (-i), w (-i))) ↔
      (LexLt (z (-i - 1), w (-i - 1)) (z (-i), w (-i)) ∧ LexLt (z (-i + 1), w (-i + 1)) (z (-i), w (-i))) := by
    intro i
    rw [show -(i - 1) = -i + 1 by ring, show -(i + 1) = -i - 1 by ring, and_comm]
  refine Finset.card_nbij' (fun i => -i) (fun i => -i) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact (key i).1 hi
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact (key (-i)).2 (by simpa using hi)
  · intro i _; simp
  · intro i _; simp
