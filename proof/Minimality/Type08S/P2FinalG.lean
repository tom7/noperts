module

public import Minimality.Type08S.P2FinalF
public import Minimality.Type08S.P2S10

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true

set_option linter.unusedVariables false

/-!
# Type 08, plan 2 (final integration G): `Resid08FinalG` and `type08_rupert_or_residG`

As `Resid08FinalF`, with the T' leftover `S4TpG2` (Lemma T'S, `Tp_poked_of_H`, `Tp_caseA`; files
`P2S1`-`P2S10`) in place of `TpResF = S4Tp or TpPokedH`.
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- **The residual in the labelling of `N`** (G). -/
def ResNG {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) : Prop :=
  ResNC' N ∧ (IsT a' b c d ∨ S4TpG2 a a' b b' c c' d)

theorem norm08_rupert_or_resNG {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ∨ ResNG N := by
  classical
  by_cases hT : IsT a' b c d
  · rcases norm08_rupert_or_resNC' N with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, Or.inl hT⟩
  by_cases hT' : IsT' a b c' d
  · rcases close_T'_sig4G2 N hT' with h | h
    · exact Or.inl h
    · rcases norm08_rupert_or_resNC' N with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨h', Or.inr h⟩
  by_cases hQ : RegQ N.F
  · exact Or.inl (region_Q N hQ)
  rcases isRupert_type08_limit_hdnR' N hT hT' hQ with h | ⟨t, ht, hreg, hr⟩
  · exact Or.inl h
  · exact Or.inl (close_hdn N hT hT' ht hreg hr)

end Type08Sp
end Minimality

