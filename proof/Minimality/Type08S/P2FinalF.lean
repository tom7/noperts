module

public import Minimality.Type08S.P2FinalE
public import Minimality.Type08S.P2F8
public import Minimality.Type08S.P2P1a

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true

set_option linter.unusedVariables false

/-!
# Type 08, plan 2 (final integration F): `Resid08FinalF` and `type08_rupert_or_residF`

As `Resid08FinalE`, with two changes.  (1) The weak-far-triple hypothesis `TpFarH` left the residual
(`Tp_far_of_H`, files `P2F0`-`P2F9`).  (2) At `T` the companion set is `CoT2'` (`CoT2` minus the `H2`
item; `close_T2_final'`, `P2P1a`) instead of `CoT2`: `ResNC'` is `ResNC` with that change.
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- `ResNC` with `CoT2'` at `T`. -/
def ResNC' {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) : Prop :=
  (TieN2 a a' b b' c c' ∧ ¬ N2Closable N) ∨
  (TieT4 b b' c c' d ∧ ¬ T4Closable N) ∨
  ¬ TieOK a a' b b' c c' d ∨
  (∃ t ∈ SC08, ¬ NoHDNAt (insert d ({a, a', b, b', c, c'} : Finset ℝ³))
    ((test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d)) ∧ ¬ ClassCt a a' b b' c c' d t) ∨
  (IsT a' b c d ∧ CoT2' a a' b b' c c' d) ∨
  (IsT' a b c' d ∧ CoT'2 a a' b b' c c' d)

theorem norm08_rupert_or_resNC' {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ∨ ResNC' N := by
  classical
  by_cases h2 : TieN2 a a' b b' c c'
  · by_cases hc : N2Closable N
    · exact Or.inl (gt_far_N2'' N hc.1 hc.2.1 h2 hc.2.2.1 hc.2.2.2)
    · exact Or.inr (Or.inl ⟨h2, hc⟩)
  by_cases h4 : TieT4 b b' c c' d
  · by_cases hc : T4Closable N
    · exact Or.inl (gt_far_T4' N hc.1 hc.2.1 h4 hc.2.2.1 hc.2.2.2)
    · exact Or.inr (Or.inr (Or.inl ⟨h4, hc⟩))
  have hnt : ¬ Touch a a' b b' c c' d := by
    rintro (h | h)
    · exact h2 h
    · exact h4 h
  by_cases hties : TieOK a a' b b' c c' d
  swap
  · exact Or.inr (Or.inr (Or.inr (Or.inl hties)))
  obtain ⟨q, hq, ties, ht, hi, hcov⟩ := hties
  have hnR : ¬ RTouch a a' b b' c c' d := by
    rintro (h | h | h)
    · exact h (fun ht => absurd (Or.inl ht) hnt)
    · exact h (fun ht => absurd (Or.inr ht) hnt)
    · exact h (fun ht => absurd (Or.inr ht) hnt)
  by_cases hT : IsT a' b c d
  · by_cases hco : CoT2' a a' b b' c c' d
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hT, hco⟩)))))
    · exact Or.inl (close_T2_final' N hT hco hnR)
  by_cases hT' : IsT' a b c' d ∧ CoT'2 a a' b b' c c' d
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hT')))))
  rcases isRupert_type08_limit_hdnC N hq ties ht hi hcov hnt (fun h => absurd h hT)
      (fun h hc => hT' ⟨h, hc⟩) with h | h
  · exact Or.inl h
  · obtain ⟨t, ht, -, hn, hs⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨t, ht, hn, hs⟩))))

end Type08Sp
end Minimality

