module

public import Minimality.Type08S.C2K17GB8

@[expose] public section


/-!
# K17GB / GB9: S1.9 lex lemma and the Gram facts (N-argument).
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- Cycle `(c',b',c,d,a)` (indices 0..4): `a < c'`, `c` not a peak, `d` not a peak. -/
theorem k17gb_lex5_s19 (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h40 : LexLt (z 4, w 4) (z 0, w 0))
    (H1 : LexLt (z 2, w 2) (z 1, w 1) ∨ LexLt (z 2, w 2) (z 3, w 3))
    (H2 : LexLt (z 3, w 3) (z 2, w 2) ∨ LexLt (z 3, w 3) (z 4, w 4)) : LexUni z w := by
  refine k17gb_uni5 z w hinj (fun key hk => ?_)
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add_one
  obtain ⟨t0, t1, t2, t3, t4⟩ := k17f_zsub
  have k40 : key 4 < key 0 := (hk _ _).1 h40
  have K1 : key 2 < key 1 ∨ key 2 < key 3 := by
    rcases H1 with h | h
    · exact Or.inl ((hk _ _).1 h)
    · exact Or.inr ((hk _ _).1 h)
  have K2 : key 3 < key 2 ∨ key 3 < key 4 := by
    rcases H2 with h | h
    · exact Or.inl ((hk _ _).1 h)
    · exact Or.inr ((hk _ _).1 h)
  have hne : key 0 ≠ key 1 := by
    intro h
    have hn : (z 0, w 0) ≠ (z 1, w 1) := fun h' => by
      have := hinj 0 1 (congrArg Prod.fst h') (congrArg Prod.snd h'); exact absurd this (by decide)
    rcases lexLt_total hn with h' | h'
    · have := (hk _ _).1 h'; linarith
    · have := (hk _ _).1 h'; linarith
  by_cases h10 : key 1 < key 0
  · refine ⟨0, ?_, fun i hi => ?_⟩
    · simp only [t0, s0]; exact ⟨k40, h10⟩
    · rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · exact absurd rfl hi
      · simp only [t1, s1]; rintro ⟨a, b⟩; linarith
      · simp only [t2, s2]; rintro ⟨a, b⟩; rcases K1 with h | h <;> linarith
      · simp only [t3, s3]; rintro ⟨a, b⟩; rcases K2 with h | h <;> linarith
      · simp only [t4, s4]; rintro ⟨a, b⟩; linarith
  · have h01 : key 0 < key 1 := lt_of_le_of_ne (not_lt.1 h10) hne
    have h21 : key 2 < key 1 := by
      rcases K1 with h | h
      · exact h
      · rcases K2 with h' | h' <;> linarith
    refine ⟨1, ?_, fun i hi => ?_⟩
    · simp only [t1, s1]; exact ⟨h01, h21⟩
    · rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · simp only [t0, s0]; rintro ⟨a, b⟩; linarith
      · exact absurd rfl hi
      · simp only [t2, s2]; rintro ⟨a, b⟩; linarith
      · simp only [t3, s3]; rintro ⟨a, b⟩; rcases K2 with h | h <;> linarith
      · simp only [t4, s4]; rintro ⟨a, b⟩; linarith

end C2
end Type08Sp
end Minimality
