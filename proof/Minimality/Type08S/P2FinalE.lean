module

public import Minimality.Type08S.P2I9b
public import Minimality.Type08S.P2E3
public import Minimality.Type08S.P2FIN1
public import Minimality.Type08S.P2CE3

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true

set_option linter.unusedVariables false

/-!
# Type 08, plan 2 (final integration E): `Resid08FinalE` and `type08_rupert_or_residE`

In a Lemma-6 labelling (`Norm08`): at `T` (`P1`, package `close_T_sig4`, unproved) the case is residual;
at `T'` the proved pieces (`close_Tp_X`, `close_T'2'`, R3, R4h, level, dichotomy) are used and the residual
is `S4Tp` or the hypotheses of the two unproved pieces `Tp_poked`, `Tp_far`; otherwise the Q region
(`region_Q`), the refined limit theorem `isRupert_type08_limit_hdnR'` and the HDN closings
(`close_hdn_np`, `close_hdn_pers_full`) are all proved.  The planar items are as in `Resid08FinalC`.
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- Q region is Rupert outright. -/
theorem region_Q {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (h : RegQ N.F) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) :=
  close_caseQ N.F N.hd h.1 h.2

/-- P3 assembled (non-persistent and persistent HDN closings). -/
theorem close_hdn {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (hT : ¬ IsT a' b c d) (hT' : ¬ IsT' a b c' d) {t : Fin 3 × Bool × Bool} (ht : t ∈ SC08)
    (hreg : (t.1 = 0 ∧ RegN2 N.F) ∨ (t.1 = 1 ∧ RegT4 N.F)) (h : RobHDN a a' b b' c c' d t) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  classical
  obtain ⟨k', hk', σ, hrim, hrob, -⟩ := h
  by_cases hnp : NoPersistHDN (fun i => pts08 a a' b b' c c' d ((test08 t.1 t.2.1 t.2.2).lab (σ i)))
      ((test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d)) (eF a a' b b' c c' d t)
  · exact close_hdn_np N hT hT' ht hreg hrim hrob hnp
  · exact close_hdn_pers_full N hT hT' ht hreg hrim hrob hnp

end Type08Sp
end Minimality

