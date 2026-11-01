module

public import Minimality.Type08S.C2K6PE

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2

theorem k6p_lexLt_asymm {p q : ℝ × ℝ} (h : LexLt p q) (h' : LexLt q p) : False := by
  unfold LexLt at h h'
  rcases h with h | ⟨h1, h2⟩ <;> rcases h' with h' | ⟨h1', h2'⟩ <;> linarith

/-- Lex version of `k5b_lexUni5_excl`: the exclusions are lex inequalities. -/
theorem k6p_lexUni5_excl (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (ex : ∀ i : ZMod 5, LexLt (z i, w i) (z (i - 1), w (i - 1)) ∨ LexLt (z i, w i) (z (i + 1), w (i + 1)) ∨
      LexLt (z (i + 2), w (i + 2)) (z (i + 2 - 1), w (i + 2 - 1)) ∨
      LexLt (z (i + 2), w (i + 2)) (z (i + 2 + 1), w (i + 2 + 1))) :
    LexUni z w := by
  refine ⟨hinj, ?_⟩
  set K : ZMod 5 → Lex (ℝ × ℝ) := fun i => toLex (z i, w i) with hK
  have hne : ∀ i j, i ≠ j → K i ≠ K j := fun i j hij h =>
    hij (hinj i j (congrArg (fun x => (ofLex x).1) h) (congrArg (fun x => (ofLex x).2) h))
  set pk : ZMod 5 → Prop := fun i => LexLt (z (i - 1), w (i - 1)) (z i, w i) ∧
    LexLt (z (i + 1), w (i + 1)) (z i, w i) with hpk
  have nopair : ∀ i, pk i → pk (i + 2) → False := by
    intro i ⟨a1, a2⟩ ⟨b1, b2⟩
    have e : i + 2 - 1 = i + 1 := by ring
    rw [e] at b1
    rcases ex i with h | h | h | h
    · exact k6p_lexLt_asymm a1 h
    · exact k6p_lexLt_asymm a2 h
    · rw [e] at h; exact k6p_lexLt_asymm b1 h
    · exact k6p_lexLt_asymm b2 h
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


/-- The five lex exclusions as explicit disjunctions. -/
theorem k6p_lex_ex_of (z w : ZMod 5 → ℝ)
    (h0 : LexLt (z 0, w 0) (z 4, w 4) ∨ LexLt (z 0, w 0) (z 1, w 1) ∨ LexLt (z 2, w 2) (z 1, w 1) ∨ LexLt (z 2, w 2) (z 3, w 3))
    (h1 : LexLt (z 1, w 1) (z 0, w 0) ∨ LexLt (z 1, w 1) (z 2, w 2) ∨ LexLt (z 3, w 3) (z 2, w 2) ∨ LexLt (z 3, w 3) (z 4, w 4))
    (h2 : LexLt (z 2, w 2) (z 1, w 1) ∨ LexLt (z 2, w 2) (z 3, w 3) ∨ LexLt (z 4, w 4) (z 3, w 3) ∨ LexLt (z 4, w 4) (z 0, w 0))
    (h3 : LexLt (z 3, w 3) (z 2, w 2) ∨ LexLt (z 3, w 3) (z 4, w 4) ∨ LexLt (z 0, w 0) (z 4, w 4) ∨ LexLt (z 0, w 0) (z 1, w 1))
    (h4 : LexLt (z 4, w 4) (z 3, w 3) ∨ LexLt (z 4, w 4) (z 0, w 0) ∨ LexLt (z 1, w 1) (z 0, w 0) ∨ LexLt (z 1, w 1) (z 2, w 2)) :
    ∀ i : ZMod 5, LexLt (z i, w i) (z (i - 1), w (i - 1)) ∨ LexLt (z i, w i) (z (i + 1), w (i + 1)) ∨
      LexLt (z (i + 2), w (i + 2)) (z (i + 2 - 1), w (i + 2 - 1)) ∨
      LexLt (z (i + 2), w (i + 2)) (z (i + 2 + 1), w (i + 2 + 1)) := by
  have e1 : (0 : ZMod 5) - 1 = 4 := by decide
  have e2 : (1 : ZMod 5) - 1 = 0 := by decide
  have e3 : (2 : ZMod 5) - 1 = 1 := by decide
  have e4 : (3 : ZMod 5) - 1 = 2 := by decide
  have e5 : (4 : ZMod 5) - 1 = 3 := by decide
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  have g0 : (0 : ZMod 5) + 2 = 2 := by decide
  have g1 : (1 : ZMod 5) + 2 = 3 := by decide
  have g2 : (2 : ZMod 5) + 2 = 4 := by decide
  have g3 : (3 : ZMod 5) + 2 = 0 := by decide
  have g4 : (4 : ZMod 5) + 2 = 1 := by decide
  intro i
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    simp only [e1, e2, e3, e4, e5, f0, f1, f2, f3, f4, g0, g1, g2, g3, g4] <;>
    first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4

end C2
end Type08Sp
end Minimality
