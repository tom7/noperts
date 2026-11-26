module

public import Minimality.LexCell
public import Minimality.RimOrder

@[expose] public section

/-!
# Adjacent-tie quad lemma (`Task EE`, Carbon A61 Lemma 1.2(a))

On a 4-cycle whose adjacent corners `i`, `i + 1` tie at level 0 while the other two are not both at
that level, one of the two opposite tie-breaks at level 1 is `RobUniLex`.
-/

set_option autoImplicit false

open Finset

namespace Minimality.GenPlus

open Minimality Minimality.LexCell Minimality.GenRev

private lemma toLex3_lt_first {p q : ℝ × ℝ × ℝ} (h : p.1 < q.1) :
    toLex (p.1, toLex (p.2.1, p.2.2)) < toLex (q.1, toLex (q.2.1, q.2.2)) :=
  Prod.Lex.lt_iff.2 (Or.inl h)

private lemma toLex3_lt_second {p q : ℝ × ℝ × ℝ} (h1 : p.1 = q.1) (h2 : p.2.1 < q.2.1) :
    toLex (p.1, toLex (p.2.1, p.2.2)) < toLex (q.1, toLex (q.2.1, q.2.2)) :=
  Prod.Lex.lt_iff.2 (Or.inr ⟨h1, Prod.Lex.lt_iff.2 (Or.inl h2)⟩)

private lemma zmod4_cases (v : ZMod 4) : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by
  fin_cases v
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

private lemma zmod4_noAlt_of_skip {B : ZMod 4} {b c d : ℕ} (hb : 0 < b) (hbc : b < c) (hcd : c < d) (hd : d < 4)
    {s : ZMod 4} (hs : s ≠ B ∧ s ≠ B + b ∧ s ≠ B + c ∧ s ≠ B + d) : False := by
  have hb1 : b = 1 := by omega
  have hc2 : c = 2 := by omega
  have hd3 : d = 3 := by omega
  subst hb1 hc2 hd3
  rcases zmod4_cases B with rfl | rfl | rfl | rfl <;>
  rcases zmod4_cases s with rfl | rfl | rfl | rfl <;>
  simp only [Nat.cast_one, Nat.cast_ofNat, zero_add] at hs <;>
  first | exact hs.1 rfl | exact hs.2.1 rfl | exact hs.2.2.1 rfl | exact hs.2.2.2 rfl

/-- **APPROVED (Task EE).**  On a 4-cycle whose adjacent corners `i`, `i + 1` tie at level 0 while
the other two are not both at that level, one of the two opposite tie-breaks at level 1 is
`RobUniLex`. -/
theorem robUniLex_adjTie {z : ZMod 4 → ℝ} (i : ZMod 4) (h01 : z i = z (i + 1))
    (hn : ¬ (z (i + 2) = z i ∧ z (i + 3) = z i)) :
    RobUniLex (fun j => (z j, (if j = i then 1 else if j = i + 1 then -1 else 0 : ℝ), (0 : ℝ))) ∨
      RobUniLex (fun j => (z j, (if j = i then -1 else if j = i + 1 then 1 else 0 : ℝ), (0 : ℝ))) := by
  have h10 : i + 1 ≠ i := fun h => absurd (show (1 : ZMod 4) = 0 by linear_combination h) (by decide)
  have h_one_skip : ∀ (f : ZMod 4 → ℝ × ℝ × ℝ) (s : ZMod 4),
      ((toLex ((f (s - 1)).1, toLex ((f (s - 1)).2.1, (f (s - 1)).2.2)) <
          toLex ((f s).1, toLex ((f s).2.1, (f s).2.2)) ∧
        toLex ((f s).1, toLex ((f s).2.1, (f s).2.2)) <
          toLex ((f (s + 1)).1, toLex ((f (s + 1)).2.1, (f (s + 1)).2.2))) ∨
       (toLex ((f (s + 1)).1, toLex ((f (s + 1)).2.1, (f (s + 1)).2.2)) <
          toLex ((f s).1, toLex ((f s).2.1, (f s).2.2)) ∧
        toLex ((f s).1, toLex ((f s).2.1, (f s).2.2)) <
          toLex ((f (s - 1)).1, toLex ((f (s - 1)).2.1, (f (s - 1)).2.2)))) →
      RobUniLex f := by
    intro f s hs
    rw [robUniLex_iff_O]
    refine robUniO_of_noAlt (univ \ {s}) (univ \ {s}) ?_ ?_ ?_
    · intro v hv
      have hvs : v = s := by by_contra hne; exact hv (mem_sdiff.2 ⟨mem_univ v, fun h => hne (mem_singleton.1 h)⟩)
      subst hvs; rcases hs with ⟨h1, _⟩ | ⟨h2, _⟩ <;> [exact Or.inl h1; exact Or.inr h2]
    · intro v hv
      have hvs : v = s := by by_contra hne; exact hv (mem_sdiff.2 ⟨mem_univ v, fun h => hne (mem_singleton.1 h)⟩)
      subst hvs; rcases hs with ⟨_, h2⟩ | ⟨_, h1⟩ <;> [exact Or.inr h2; exact Or.inl h1]
    · intro B b c d hb hbc hcd hd ⟨hB, hBb, hBc, hBd⟩
      simp only [mem_sdiff, mem_univ, mem_singleton, true_and] at hB hBb hBc hBd
      exact zmod4_noAlt_of_skip hb hbc hcd hd ⟨Ne.symm hB, Ne.symm hBb, Ne.symm hBc, Ne.symm hBd⟩
  by_cases h2 : z (i + 2) = z i
  · have h3 : z (i + 3) ≠ z i := fun h => hn ⟨h2, h⟩
    have hi_sub : i - 1 = i + 3 := by rw [sub_eq_add_neg, show (-1 : ZMod 4) = 3 by decide]
    rcases lt_or_gt_of_ne h3 with h3lt | h3gt
    · right; refine h_one_skip _ i (Or.inl ⟨?_, ?_⟩)
      · rw [hi_sub]; exact toLex3_lt_first h3lt
      · exact toLex3_lt_second h01 (by simp [h10])
    · left; refine h_one_skip _ i (Or.inr ⟨?_, ?_⟩)
      · exact toLex3_lt_second h01.symm (by simp [h10])
      · rw [hi_sub]; exact toLex3_lt_first h3gt
  · have hi1_add : i + 1 + 1 = i + 2 := by ring
    have hi1_sub : i + 1 - 1 = i := by ring
    rcases lt_or_gt_of_ne h2 with h2lt | h2gt
    · left; refine h_one_skip _ (i + 1) (Or.inr ⟨?_, ?_⟩)
      · rw [hi1_add]; exact toLex3_lt_first (by linarith)
      · rw [hi1_sub]; exact toLex3_lt_second h01.symm (by simp [h10])
    · right; refine h_one_skip _ (i + 1) (Or.inl ⟨?_, ?_⟩)
      · rw [hi1_sub]; exact toLex3_lt_second h01 (by simp [h10])
      · rw [hi1_add]; exact toLex3_lt_first (by linarith)

end Minimality.GenPlus
