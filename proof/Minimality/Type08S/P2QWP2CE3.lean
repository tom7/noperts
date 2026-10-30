module

public import Minimality.Type08S.P2QQ0c
public import Minimality.Type08S.P2QWSCl
public import Minimality.Type08S.P2QWP2PF0
public import Minimality.Type08S.P2QWP2PF1
public import Minimality.Type08S.P2QWP2PF2
public import Minimality.Type08S.P2QWP2PF3
public import Minimality.Type08S.P2QWP2NP1
public import Minimality.Type08S.P2QWP2NP2
public import Minimality.Type08S.P2QWP2NP3
public import Minimality.Type08S.P2QWP2NP5
public import Minimality.Type08S.P2QWP2NP6
public import Minimality.Type08S.P2QWP2FIN1
public import Minimality.Type08S.P2QWP2H8
public import Minimality.Type08S.P2QWP2H11
public import Minimality.Type08S.P2QWP2H9
public import Minimality.Type08S.P2QWP2H10
public import Minimality.Type08S.P2QWP2H13
public import Minimality.Type08S.P2QWP2H14
public import Minimality.Type08S.P2QWP2CE2

@[expose] public section

set_option relaxedAutoImplicit true
set_option relaxedAutoImplicit true

set_option autoImplicit true

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace W5

/-- `close_hdn_pers` (P2Pkg statement), unconditional on the SC2 package. -/
theorem close_hdn_pers_full {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d)
    (hpe : ¬ (det3 (c - b) (b' - b) (c' - b) = 0 ∧ ParEnd a a' b b' c c' d))
    (hT : ¬ IsT a' b c d) (hT' : ¬ IsT' a b c' d) {t : Fin 3 × Bool × Bool} (ht : t ∈ SC08)
    (hreg : (t.1 = 0 ∧ RegN2 N.F) ∨ (t.1 = 1 ∧ RegT4 N.F))
    {k' : ℕ} [NeZero k'] {σ : ZMod k' → ZMod (test08 t.1 t.2.1 t.2.2).k}
    (hrim : RimCertAt (pts08 a a' b b' c c' d) ((test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d))
      ((test08 t.1 t.2.1 t.2.2).lab ∘ σ))
    (hrob : IsRobustUnimodal (fun i => ⟪pts08 a a' b b' c c' d ((test08 t.1 t.2.1 t.2.2).lab (σ i)),
      (test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d)⟫))
    (hp : ¬ NoPersistHDN (fun i => pts08 a a' b b' c c' d ((test08 t.1 t.2.1 t.2.2).lab (σ i)))
        ((test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d)) (eF a a' b b' c c' d t)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) :=
  close_hdn_pers' N hpe hT hT' ht hreg hrim hrob hp (fun hr => cef_N2 N hpe hr)
    (fun hr => ⟨cef_Kb N hpe hr, cef_K2 N hpe hr⟩)

end W5
end Type08Sp
end Minimality

