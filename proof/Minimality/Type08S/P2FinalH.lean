module

public import Minimality.Type08S.P2FinalG
public import Minimality.Type08S.P2TL2
public import Minimality.Type08S.P2TT2
public import Minimality.Type08S.P2TA1c
public import Minimality.Type08S.P2TA2d
public import Minimality.Type08S.P2TBt3

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true

set_option linter.unusedVariables false

/-!
# Type 08, plan 2 (final integration H): `Resid08FinalH` and `type08_rupert_or_residH`

As `Resid08FinalG`, with the case at `T` (P1, package pkP: `P2T*`) closed down to the codim-4 leftover
`S4T2 = S4T' ∨ S4TB`: the refined limit theorem at `T` (`isRupert_type08_limit_T`), touching
(`close_touchT`), `K_b` with non-persistent / persistent HDN (`close_hdn_np_KbT`, `close_hdn_pers_KbT`), and case B
(`close_caseB_T`: cells (−,−,−) and (+,−,−), 18.3 on `X_ba'`, the slide of `K_2`).
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- The full leftover at `T` (codim 4): `S4T'` (touching L1/L2, case B's L3/L4) or case B's `S4TB`. -/
def S4T2 (a a' b b' c c' d : ℝ³) : Prop := S4T' a a' b b' c c' d ∨ S4TB a a' b b' c c' d

theorem close_T_sig4 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hT : IsT a' b c d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ∨ S4T2 a a' b b' c c' d := by
  rcases isRupert_type08_limit_T N hT with h | h | ⟨hA, s, h⟩ | ⟨hB, s, h⟩
  · exact Or.inl h
  · exact (close_touchT N hT h).imp id Or.inl
  · obtain ⟨k', hk', σ, hrim, hrob, -⟩ := h
    by_cases hnp : NoPersistHDN (fun i => pts08 a a' b b' c c' d ((test08 1 s true).lab (σ i)))
        ((test08 1 s true).view (pts08 a a' b b' c c' d)) (eF a a' b b' c c' d (1, s, true))
    · exact Or.inl (close_hdn_np_KbT N hT hrim hrob hnp)
    · exact Or.inl (close_hdn_pers_KbT N hT hrim hrob hnp)
  · exact (close_caseB_T N hT hB h).imp id Or.inr

/-- **The residual in the labelling of `N`** (H). -/
def ResNH {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) : Prop :=
  ResNC' N ∧ (S4T2 a a' b b' c c' d ∨ S4TpG2 a a' b b' c c' d)

theorem norm08_rupert_or_resNH {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ∨ ResNH N := by
  rcases norm08_rupert_or_resNG N with h | ⟨h1, hT | h2⟩
  · exact Or.inl h
  · rcases close_T_sig4 N hT with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h1, Or.inl h⟩
  · exact Or.inr ⟨h1, Or.inr h2⟩

def ResidNH (a a' b b' c c' d : ℝ³) : Prop := ∃ N : Norm08 a a' b b' c c' d, ResNH N

theorem wrapNH {p p' q q' r r' d : ℝ³} (N : Norm08 p p' q q' r r' d) {V : Finset ℝ³}
    (hset : insert d ({p, p', q, q', r, r'} : Finset ℝ³) = V) :
    IsRupert V ∨ ResidNH p p' q q' r r' d := by
  rcases norm08_rupert_or_resNH N with h | h
  · exact Or.inl (hset ▸ h)
  · exact Or.inr ⟨N, h⟩

end Type08Sp
end Minimality
