module

public import Minimality.Type08S.C2K16R

@[expose] public section


set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
open C2

theorem k17a_zsub : (0 : ZMod 5) - 1 = 4 ∧ (1 : ZMod 5) - 1 = 0 ∧ (2 : ZMod 5) - 1 = 1 ∧
    (3 : ZMod 5) - 1 = 2 ∧ (4 : ZMod 5) - 1 = 3 := by decide

open Classical in
theorem k17a_lexUni5_of_peak (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j) (m : ZMod 5)
    (hm : LexLt (z (m - 1), w (m - 1)) (z m, w m) ∧ LexLt (z (m + 1), w (m + 1)) (z m, w m))
    (ho : ∀ i, i ≠ m → ¬ (LexLt (z (i - 1), w (i - 1)) (z i, w i) ∧ LexLt (z (i + 1), w (i + 1)) (z i, w i))) :
    LexUni z w := by
  refine ⟨hinj, ?_⟩
  rw [Finset.card_eq_one]
  refine ⟨m, ?_⟩
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h; by_contra hne; exact ho i hne h
  · rintro rfl; exact hm

/-- D2: bottom plateau `a, b', d` (indices 0,1,4), `w a < w b'`, top `a', b` (2,3). -/
theorem k17a_lex_D2 (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h01 : z 0 = z 1) (h04 : z 0 = z 4) (h2 : z 0 < z 2) (h3 : z 0 < z 3) (hw : w 0 < w 1) :
    LexUni z w := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add_one
  obtain ⟨t0, t1, t2, t3, t4⟩ := k17a_zsub
  have n23 : z 2 ≠ z 3 ∨ w 2 ≠ w 3 := by
    by_contra h; push Not at h
    have := hinj 2 3 h.1 h.2; revert this; decide
  by_cases hc : LexLt (z 3, w 3) (z 2, w 2)
  · refine k17a_lexUni5_of_peak z w hinj 2 ?_ (fun i hi => ?_)
    · exact ⟨by simp only [t2, LexLt]; left; linarith, by simpa only [s2] using hc⟩
    · rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · simp only [t0, s0, LexLt]
        rintro ⟨h1, h2⟩
        rcases h2 with h2 | ⟨h2, h2'⟩ <;> linarith
      · simp only [t1, s1, LexLt]
        rintro ⟨h1, h2⟩
        rcases h2 with h2 | ⟨h2, h2'⟩ <;> linarith
      · exact absurd rfl hi
      · simp only [t3, s3, LexLt] at *
        rintro ⟨h1, h2⟩
        rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases hc with hc | ⟨hc, hc'⟩ <;> linarith
      · simp only [t4, s4, LexLt]
        rintro ⟨h1, h2⟩
        rcases h1 with h1 | ⟨h1, h1'⟩ <;> linarith
  · have hc' : LexLt (z 2, w 2) (z 3, w 3) := by
      simp only [LexLt] at hc ⊢
      push Not at hc
      rcases lt_trichotomy (z 2) (z 3) with h | h | h
      · exact Or.inl h
      · right; refine ⟨h, ?_⟩
        rcases n23 with n | n
        · exact absurd h n
        · exact lt_of_le_of_ne (hc.2 h.symm) n
      · exact absurd h (not_lt.2 hc.1)
    refine k17a_lexUni5_of_peak z w hinj 3 ?_ (fun i hi => ?_)
    · simp only [t3, s3, LexLt] at *; constructor
      · exact hc'
      · left; linarith
    · rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · simp only [t0, s0, LexLt]
        rintro ⟨h1, h2⟩
        rcases h2 with h2 | ⟨h2, h2'⟩ <;> linarith
      · simp only [t1, s1, LexLt]
        rintro ⟨h1, h2⟩
        rcases h2 with h2 | ⟨h2, h2'⟩ <;> linarith
      · simp only [t2, s2, LexLt] at *
        rintro ⟨h1, h2⟩
        rcases h2 with h2 | ⟨h2, h2'⟩ <;> rcases hc' with hc' | ⟨hc', hc''⟩ <;> linarith
      · exact absurd rfl hi
      · simp only [t4, s4, LexLt]
        rintro ⟨h1, h2⟩
        rcases h1 with h1 | ⟨h1, h1'⟩ <;> linarith

/-- D1: top plateau `a, b, d` (indices 0,3,4) with `w b < w d`, bottom `b', a'` (1,2). -/
theorem k17a_lex_D1 (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h1 : z 1 < z 0) (h2 : z 2 < z 3) (h04 : z 0 = z 4) (h34 : z 3 = z 4) (hw : w 3 < w 4) :
    LexUni z w := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add_one
  obtain ⟨t0, t1, t2, t3, t4⟩ := k17a_zsub
  have n04 : w 0 ≠ w 4 := fun h => by
    have := hinj 0 4 h04 h; revert this; decide
  by_cases hc : w 4 < w 0
  · refine k17a_lexUni5_of_peak z w hinj 0 ?_ (fun i hi => ?_)
    · simp only [t0, s0, LexLt]; exact ⟨Or.inr ⟨h04.symm, hc⟩, Or.inl h1⟩
    · rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · exact absurd rfl hi
      · simp only [t1, s1, LexLt]
        rintro ⟨a1, a2⟩
        rcases a1 with a1 | ⟨a1, a1'⟩ <;> linarith
      · simp only [t2, s2, LexLt]
        rintro ⟨a1, a2⟩
        rcases a2 with a2 | ⟨a2, a2'⟩ <;> linarith
      · simp only [t3, s3, LexLt]
        rintro ⟨a1, a2⟩
        rcases a2 with a2 | ⟨a2, a2'⟩ <;> linarith
      · simp only [t4, s4, LexLt]
        rintro ⟨a1, a2⟩
        rcases a2 with a2 | ⟨a2, a2'⟩ <;> linarith
  · have hc' : w 0 < w 4 := lt_of_le_of_ne (not_lt.1 hc) n04
    refine k17a_lexUni5_of_peak z w hinj 4 ?_ (fun i hi => ?_)
    · simp only [t4, s4, LexLt]; exact ⟨Or.inr ⟨h34, hw⟩, Or.inr ⟨h04, hc'⟩⟩
    · rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · simp only [t0, s0, LexLt]
        rintro ⟨a1, a2⟩
        rcases a1 with a1 | ⟨a1, a1'⟩ <;> linarith
      · simp only [t1, s1, LexLt]
        rintro ⟨a1, a2⟩
        rcases a1 with a1 | ⟨a1, a1'⟩ <;> linarith
      · simp only [t2, s2, LexLt]
        rintro ⟨a1, a2⟩
        rcases a2 with a2 | ⟨a2, a2'⟩ <;> linarith
      · simp only [t3, s3, LexLt]
        rintro ⟨a1, a2⟩
        rcases a2 with a2 | ⟨a2, a2'⟩ <;> linarith
      · exact absurd rfl hi

end Type08Sp
end Minimality
