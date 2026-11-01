module

public import Minimality.Type08S.C2K5AI

@[expose] public section


/-!
# K5b / A: a 5-cycle with no double lex peak is lex unimodal (strict-depth peak exclusions).
For each non-adjacent pair `(i, i+2)` one strict depth inequality kills the double peak.
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem k5b_lexLt_iff (p q : ℝ × ℝ) : LexLt p q ↔ toLex p < toLex q := by
  unfold LexLt; rw [Prod.Lex.lt_iff]; rfl

theorem k5b_lexLt_le {p q : ℝ × ℝ} (h : LexLt p q) : p.1 ≤ q.1 := by
  unfold LexLt at h; rcases h with h | ⟨h, _⟩ <;> linarith

theorem k5b_zmod5_cases : ∀ m j : ZMod 5, j = m ∨ j = m + 1 ∨ j = m - 1 ∨ j = m + 2 ∨ j = m - 2 := by decide

theorem k5b_zmod5_ne : ∀ m : ZMod 5, m - 1 ≠ m ∧ m + 1 ≠ m := by decide

open Classical in
/-- **Five-cycle unimodality from pairwise exclusions.**  `ex i`: for the candidate peaks `i, i+2`, a strict
depth inequality contradicts one of them being a peak. -/
theorem k5b_lexUni5_excl (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (ex : ∀ i : ZMod 5, z i < z (i - 1) ∨ z i < z (i + 1) ∨ z (i + 2) < z (i + 2 - 1) ∨
      z (i + 2) < z (i + 2 + 1)) :
    LexUni z w := by
  refine ⟨hinj, ?_⟩
  set K : ZMod 5 → Lex (ℝ × ℝ) := fun i => toLex (z i, w i) with hK
  have hne : ∀ i j, i ≠ j → K i ≠ K j := fun i j hij h =>
    hij (hinj i j (congrArg (fun x => (ofLex x).1) h) (congrArg (fun x => (ofLex x).2) h))
  set pk : ZMod 5 → Prop := fun i => LexLt (z (i - 1), w (i - 1)) (z i, w i) ∧
    LexLt (z (i + 1), w (i + 1)) (z i, w i) with hpk
  have nopair : ∀ i, pk i → pk (i + 2) → False := by
    intro i ⟨a1, a2⟩ ⟨b1, b2⟩
    have c1 := k5b_lexLt_le a1; have c2 := k5b_lexLt_le a2
    have c3 := k5b_lexLt_le b1; have c4 := k5b_lexLt_le b2
    simp only at c1 c2 c3 c4
    have e : i + 2 - 1 = i + 1 := by ring
    rw [e] at c3
    rcases ex i with h | h | h | h <;> [linarith; linarith; (rw [e] at h; linarith); linarith]
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image (Finset.univ : Finset (ZMod 5)) K ⟨0, Finset.mem_univ _⟩
  have hmax : ∀ j, j ≠ m → K j < K m := fun j hj => lt_of_le_of_ne (hm j (Finset.mem_univ _)) (hne j m hj)
  have hpm : pk m := by
    exact ⟨(k5b_lexLt_iff _ _).2 (hmax _ (k5b_zmod5_ne m).1), (k5b_lexLt_iff _ _).2 (hmax _ (k5b_zmod5_ne m).2)⟩
  rw [Finset.card_eq_one]
  refine ⟨m, ?_⟩
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hj
    by_contra hjm
    obtain ⟨h1, h2⟩ := hj
    rcases k5b_zmod5_cases m j with h | h | h | h | h
    · exact hjm h
    · have := (k5b_lexLt_iff _ _).1 h1
      have e : j - 1 = m := by rw [h]; ring
      rw [e] at this
      exact absurd this (not_lt.2 (hm j (Finset.mem_univ _)))
    · have := (k5b_lexLt_iff _ _).1 h2
      have e : j + 1 = m := by rw [h]; ring
      rw [e] at this
      exact absurd this (not_lt.2 (hm j (Finset.mem_univ _)))
    · rw [h] at h1 h2
      exact nopair m hpm ⟨h1, h2⟩
    · have e : j + 2 = m := by rw [h]; ring
      rw [← e] at hpm
      exact nopair j ⟨h1, h2⟩ hpm
  · rintro rfl; exact hpm

end C2
end Type08Sp
end Minimality
