module

public import Minimality.Type08S.P2S9

@[expose] public section

set_option relaxedAutoImplicit true
set_option autoImplicit true
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {a a' b b' c c' d : ℝ³}

/-- The Case A configuration: `α4 > 1` and `{d, a}` strictly below `{b', c}` along `ℓ` (the strict tie
`D(c) = D(b') > max(D(d), D(a))` when combined with `QacTop`). -/
def CaseATp (a b b' c d : ℝ³) : Prop :=
  ∃ α4 γ4 : ℝ, b' = d + α4 • (a - d) + γ4 • (c - d) ∧ 1 < α4 ∧
    max ⟪d, b - d⟫ ⟪a, b - d⟫ < min ⟪b', b - d⟫ ⟪c, b - d⟫

/-- `S4TpG` with Case A removed from the `X_2a`-HDN item. -/
def S4TpG2 (a a' b b' c c' d : ℝ³) : Prop :=
  IsT' a b c' d ∧ QacTop a b b' c d ∧
    ((LevelQac a b c d ∧ ¬ NoHDNAt ({b, c', b', c} : Finset ℝ³) (b - d) ∧
        ∃ α4 γ4 : ℝ, b' = d + α4 • (a - d) + γ4 • (c - d) ∧ 1 < α4) ∨
     (¬ NoHDNAt ({d, a, b', c} : Finset ℝ³) (b - d) ∧
       (TpHDN2 a b b' c c' d ∨ det3 (b' - a) (c - d) (b - d) = 0) ∧ ¬ CaseATp a b b' c d))

theorem S4TpG2_imp (h : S4TpG2 a a' b b' c c' d) : S4TpG a a' b b' c c' d := by
  obtain ⟨h1, h2, h3 | ⟨h3, h4, -⟩⟩ := h
  · exact ⟨h1, h2, Or.inl h3⟩
  · exact ⟨h1, h2, Or.inr ⟨h3, h4⟩⟩

theorem close_T'_sig4G2 (N : Norm08 a a' b b' c c' d) (hT' : IsT' a b c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ∨ S4TpG2 a a' b b' c c' d := by
  rcases close_T'_sig4G N hT' with h | ⟨h1, h2, h3 | ⟨h3, h4⟩⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2, Or.inl h3⟩
  · by_cases hA : CaseATp a b b' c d
    · obtain ⟨α4, γ4, hrep, hα, hsep⟩ := hA
      exact Or.inl (Tp_caseA N hT' hrep hα hsep)
    · exact Or.inr ⟨h1, h2, Or.inr ⟨h3, h4, hA⟩⟩

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.close_T'_sig4G2
