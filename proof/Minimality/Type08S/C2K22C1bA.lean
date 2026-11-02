module

public import Minimality.Type08S.C2K22C1A
public import Minimality.Type08S.C2K21C
public import Minimality.Type08S.C2K22A1

@[expose] public section


/-!
# K22C1b / A: lex unimodality from two adjacent peak candidates

`k22c1b_uni`: if every index other than `i0, i0 + 1` has a lex-larger neighbour, the cycle is lex unimodal (the lex
maximum is a peak, and `i0, i0 + 1` cannot both be peaks).
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem k22c1b_lexLt_asymm {x y : ℝ × ℝ} (h : LexLt x y) : ¬ LexLt y x := by
  unfold LexLt at *
  rcases h with h | ⟨h1, h2⟩ <;> rintro (h' | ⟨h1', h2'⟩) <;> linarith

theorem k22c1b_lexLt_trich (x y : ℝ × ℝ) : LexLt x y ∨ x = y ∨ LexLt y x := by
  unfold LexLt
  rcases lt_trichotomy x.1 y.1 with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases lt_trichotomy x.2 y.2 with h' | h' | h'
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · exact Or.inr (Or.inl (Prod.ext h h'))
    · exact Or.inr (Or.inr (Or.inr ⟨h.symm, h'⟩))
  · exact Or.inr (Or.inr (Or.inl h))

theorem k22c1b_uni {k : ℕ} [NeZero k] (h1 : (1 : ZMod k) ≠ 0) (z w : ZMod k → ℝ)
    (hinj : ∀ i j, z i = z j → w i = w j → i = j) (i0 : ZMod k)
    (h : ∀ j, j ≠ i0 → j ≠ i0 + 1 →
      LexLt (z j, w j) (z (j - 1), w (j - 1)) ∨ LexLt (z j, w j) (z (j + 1), w (j + 1))) :
    LexUni z w := by
  classical
  refine ⟨hinj, ?_⟩
  set S := Finset.univ.filter (fun i : ZMod k => LexLt (z (i - 1), w (i - 1)) (z i, w i) ∧
    LexLt (z (i + 1), w (i + 1)) (z i, w i)) with hS
  -- a peak exists: the lex maximum
  obtain ⟨M, hM⟩ := exists_key z w hinj
  obtain ⟨j0, -, hj0⟩ := Finset.exists_max_image Finset.univ (fun i => M * z i + w i) ⟨0, Finset.mem_univ _⟩
  have below : ∀ n, n ≠ j0 → LexLt (z n, w n) (z j0, w j0) := by
    intro n hn
    rcases k22c1b_lexLt_trich (z n, w n) (z j0, w j0) with h' | h' | h'
    · exact h'
    · exact (hn (hinj n j0 (congrArg Prod.fst h') (congrArg Prod.snd h'))).elim
    · have := (hM j0 n).1 h'
      have := hj0 n (Finset.mem_univ _)
      linarith
  have hm1 : j0 - 1 ≠ j0 := by
    intro e; apply h1; have := congrArg (fun x => j0 - x) e; simp at this; exact this
  have hp1 : j0 + 1 ≠ j0 := by
    intro e; apply h1; have := congrArg (fun x => x - j0) e; simp at this; exact this
  have hj0S : j0 ∈ S := by
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨below _ hm1, below _ hp1⟩
  -- every peak is j0
  have peak_mem : ∀ j ∈ S, j = i0 ∨ j = i0 + 1 := by
    intro j hj
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    by_contra hc
    push_neg at hc
    rcases h j hc.1 hc.2 with h' | h'
    · exact k22c1b_lexLt_asymm hj.1 h'
    · exact k22c1b_lexLt_asymm hj.2 h'
  have uniq : ∀ j ∈ S, j = j0 := by
    intro j hj
    by_contra hne
    have hj' := hj
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hj'
    have hj0' := hj0S
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hj0'
    have hsub : i0 + 1 - 1 = i0 := by ring
    rcases peak_mem j hj with rfl | rfl <;> rcases peak_mem j0 hj0S with e | e
    · exact hne e.symm
    · subst e; rw [hsub] at hj0'; exact k22c1b_lexLt_asymm hj'.2 hj0'.1
    · subst e; rw [hsub] at hj'; exact k22c1b_lexLt_asymm hj0'.2 hj'.1
    · exact hne e.symm
  rw [Finset.card_eq_one]
  exact ⟨j0, Finset.eq_singleton_iff_unique_mem.2 ⟨hj0S, uniq⟩⟩

end C2
end Type08Sp
end Minimality
