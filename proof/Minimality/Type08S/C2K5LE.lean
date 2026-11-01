module

public import Minimality.Type08S.C2K5LD

@[expose] public section


/-!
# K5L / E: cyclic tools for the K5e pentagon

* `lexUni_unshift1`: `LexUni` is invariant under the cyclic shift `i ↦ i + 1`.
* `pent_lexUni`: the lex-peak argument for the pentagon `(a, d, c, a', c')` of K5e `β1 > 1`.
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

theorem lexUni_unshift1 {k : ℕ} [NeZero k] {z w : ZMod k → ℝ} (h : LexUni (fun i => z (i + 1)) (fun i => w (i + 1))) :
    LexUni z w := by
  classical
  refine ⟨fun i j h1 h2 => ?_, ?_⟩
  · have := h.1 (i - 1) (j - 1) (by simpa using h1) (by simpa using h2)
    exact sub_left_injective this
  · rw [← h.2]
    have key : ∀ j : ZMod k, (LexLt (z (j - 1), w (j - 1)) (z j, w j) ∧
        LexLt (z (j + 1), w (j + 1)) (z j, w j)) ↔
        (LexLt (z (j - 1 - 1 + 1), w (j - 1 - 1 + 1)) (z (j - 1 + 1), w (j - 1 + 1)) ∧
        LexLt (z (j - 1 + 1 + 1), w (j - 1 + 1 + 1)) (z (j - 1 + 1), w (j - 1 + 1))) := by
      intro j; simp only [sub_add_cancel]
    refine Finset.card_nbij' (fun i => i - 1) (fun i => i + 1) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact (key i).1 hi
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact (key (i + 1)).2 (by simpa using hi)
    · intro i _; simp
    · intro i _; simp

/-- **The K5e pentagon `(a, d, c, a', c')` (indices `0..4`).** -/
theorem pent_lexUni (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    {e f A wR m s α1 k1 k2 : ℝ} (hA : 0 < A) (hm : m < 0) (hs : 0 < s) (hα1 : 1 ≤ α1)
    (hk1 : 0 < k1) (hk2 : 0 < k2)
    (hz1 : z 0 - z 1 = e) (hw1 : w 0 - w 1 = f)
    (hz2 : z 2 - z 1 = m * e + s * A) (hw2 : w 2 - w 1 = m * f + s * wR)
    (hz3 : z 3 = z 2) (hw3 : w 3 - w 2 = k1)
    (hz4 : z 4 - z 1 = α1 * e) (hw4 : w 4 - w 1 = α1 * f + k2) : LexUni z w := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  have l23 : LexLt (z 2, w 2) (z 3, w 3) := Or.inr ⟨hz3.symm, by linarith⟩
  have hne : ¬ (e = 0 ∧ f = 0) := by
    rintro ⟨h1, h2⟩
    have := hinj 0 1 (by linarith) (by linarith)
    exact absurd this (by decide)
  have shift_case : LexLt (z 0, w 0) (z 4, w 4) → (LexLt (z 1, w 1) (z 2, w 2) ∨ LexLt (z 1, w 1) (z 0, w 0)) →
      LexUni z w := by
    intro l04 hd
    apply lexUni_unshift1
    refine lexUni5_two _ _ (fun i j h1 h2 => ?_) ?_ ?_ ?_
    · exact add_right_cancel (hinj _ _ h1 h2)
    · simp only [f1, f2]; exact l23
    · simp only [f3, f4]; exact l04
    · simp only [f0, f1, f4]; exact hd
  have hcases : (0 < e ∨ (e = 0 ∧ 0 < f)) ∨ (e < 0 ∨ (e = 0 ∧ f < 0)) := by
    rcases lt_trichotomy e 0 with h | h | h
    · exact Or.inr (Or.inl h)
    · rcases lt_trichotomy f 0 with h' | h' | h'
      · exact Or.inr (Or.inr ⟨h, h'⟩)
      · exact absurd ⟨h, h'⟩ hne
      · exact Or.inl (Or.inr ⟨h, h'⟩)
    · exact Or.inl (Or.inl h)
  rcases hcases with hpos | hneg
  · -- `E > 0`: `c' > a > d`
    have l10 : LexLt (z 1, w 1) (z 0, w 0) := by
      rcases hpos with h | ⟨h1, h2⟩
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by linarith, by linarith⟩
    have l04 : LexLt (z 0, w 0) (z 4, w 4) := by
      rcases hpos with h | ⟨h1, h2⟩
      · rcases eq_or_lt_of_le hα1 with h3 | h3
        · subst h3
          exact Or.inr ⟨by linarith, by linarith⟩
        · exact Or.inl (by nlinarith)
      · exact Or.inr ⟨by subst h1; linarith, by nlinarith⟩
    exact shift_case l04 (Or.inr l10)
  · -- `E < 0`: `a < d < c < a'`
    have l01 : LexLt (z 0, w 0) (z 1, w 1) := by
      rcases hneg with h | ⟨h1, h2⟩
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by linarith, by linarith⟩
    have l12 : LexLt (z 1, w 1) (z 2, w 2) := by
      left
      have he : e ≤ 0 := by rcases hneg with h | ⟨h1, h2⟩ <;> linarith
      nlinarith [mul_nonneg_of_nonpos_of_nonpos hm.le he, mul_pos hs hA]
    have hne2 : (z 4, w 4) ≠ (z 3, w 3) := by
      intro h
      have := hinj 4 3 (congrArg Prod.fst h) (congrArg Prod.snd h)
      exact absurd this (by decide)
    rcases lexLt_total hne2 with l43 | l34
    · refine lexUni5_two z w hinj l12 l43 (Or.inl l01)
    · exact shift_case (lexLt_trans_K2 l01 (lexLt_trans_K2 l12 (lexLt_trans_K2 l23 l34))) (Or.inl l12)

end C2
end Type08Sp
end Minimality
