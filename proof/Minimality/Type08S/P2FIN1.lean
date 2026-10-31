module

public import Minimality.Type08S.P2FIN0
public import Minimality.Type08S.P2QWP2FIN1

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# P3a: `close_hdn_np` (statement identical to `P2Pkg.close_hdn_np`).
-/

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

theorem close_hdn_np {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (hT : ¬ IsT a' b c d) (hT' : ¬ IsT' a b c' d) {t : Fin 3 × Bool × Bool} (ht : t ∈ SC08)
    (hreg : (t.1 = 0 ∧ RegN2 N.F) ∨ (t.1 = 1 ∧ RegT4 N.F))
    {k' : ℕ} [NeZero k'] {σ : ZMod k' → ZMod (test08 t.1 t.2.1 t.2.2).k}
    (hrim : RimCertAt (pts08 a a' b b' c c' d) ((test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d))
      ((test08 t.1 t.2.1 t.2.2).lab ∘ σ))
    (hrob : IsRobustUnimodal (fun i => ⟪pts08 a a' b b' c c' d ((test08 t.1 t.2.1 t.2.2).lab (σ i)),
      (test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d)⟫))
    (hnp : NoPersistHDN (fun i => pts08 a a' b b' c c' d ((test08 t.1 t.2.1 t.2.2).lab (σ i)))
        ((test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d)) (eF a a' b b' c c' d t)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) :=
  W5.close_hdn_np N.toW hT hT' ht hreg hrim hrob hnp

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.close_hdn_np
