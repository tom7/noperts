module

public import Minimality.Type08S.C2K6ME

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2

/-- Any three distinct lex pairs on a 3-cycle are lex unimodal. -/
theorem k6m_lexUni3 (z w : ZMod 3 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j) : LexUni z w := by
  obtain ⟨M, hM⟩ := exists_key z w hinj
  refine lexUni_of_key z w (fun i => M * z i + w i) hinj hM ?_
  refine k5d_uni_of_nopair (by decide) _ ?_ ?_
  · intro i j h
    by_contra hij
    have hne : (z i, w i) ≠ (z j, w j) := fun e => hij (hinj i j (congrArg Prod.fst e) (congrArg Prod.snd e))
    have ht : LexLt (z i, w i) (z j, w j) ∨ LexLt (z j, w j) (z i, w i) := by
      simp only [LexLt]
      rcases lt_trichotomy (z i) (z j) with h1 | h1 | h1
      · exact Or.inl (Or.inl h1)
      · rcases lt_trichotomy (w i) (w j) with h2 | h2 | h2
        · exact Or.inl (Or.inr ⟨h1, h2⟩)
        · exact absurd (Prod.ext h1 h2) hne
        · exact Or.inr (Or.inr ⟨h1.symm, h2⟩)
      · exact Or.inr (Or.inl h1)
    rcases ht with ht | ht
    · have := (hM i j).1 ht; linarith
    · have := (hM j i).1 ht; linarith
  · intro i j h1 h2 h3
    exfalso
    have : ∀ i j : ZMod 3, j ≠ i → j ≠ i + 1 → j ≠ i - 1 → False := by decide
    exact this i j h1 h2 h3

end C2
end Type08Sp
end Minimality
