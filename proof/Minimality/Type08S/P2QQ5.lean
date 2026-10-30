module

public import Minimality.Type08S.P2QWP2CE3
public import Minimality.Type08S.P2QDefs

@[expose] public section

set_option relaxedAutoImplicit true
set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- **Q5.** `P2FinalE.close_hdn` on `Norm08w` (statement as in PQ0). -/
theorem close_hdn_w {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d)
    (hT : ¬ IsT a' b c d) (hT' : ¬ IsT' a b c' d) {t : Fin 3 × Bool × Bool} (ht : t ∈ SC08)
    (hreg : (t.1 = 0 ∧ RegN2 N.F) ∨ (t.1 = 1 ∧ RegT4 N.F)) (h : RobHDN a a' b b' c c' d t)
    (hpe : ¬ (det3 (c - b) (b' - b) (c' - b) = 0 ∧ ParEnd a a' b b' c c' d)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  classical
  obtain ⟨k', hk', σ, hrim, hrob, -⟩ := h
  by_cases hnp : NoPersistHDN (fun i => pts08 a a' b b' c c' d ((test08 t.1 t.2.1 t.2.2).lab (σ i)))
      ((test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d)) (eF a a' b b' c c' d t)
  · exact W5.close_hdn_np N hT hT' ht hreg hrim hrob hnp
  · exact W5.close_hdn_pers_full N hpe hT hT' ht hreg hrim hrob hnp

end Type08Sp
end Minimality

