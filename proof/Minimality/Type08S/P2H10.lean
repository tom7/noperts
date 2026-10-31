module

public import Minimality.Type08S.P2H9
public import Minimality.Type08S.P2H11
public import Minimality.Type08S.P2QWP2H10

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# pkH H10: P-K, `close_hdn_pers` (P2Pkg statement + the explicit external hypotheses)

Statement = `P2Pkg.close_hdn_pers` (with `eF` of pkB FIN1, identical to P2Pkg's) plus two hypotheses
`hSN2`, `hST4` (the SC2 package: chord end at `f`, parallel set).  Lemma E (D6) is proved (`lemE_all`, H11).
-/

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

theorem close_hdn_pers {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (hT : ¬ IsT a' b c d) (hT' : ¬ IsT' a b c' d) {t : Fin 3 × Bool × Bool} (ht : t ∈ SC08)
    (hreg : (t.1 = 0 ∧ RegN2 N.F) ∨ (t.1 = 1 ∧ RegT4 N.F))
    {k' : ℕ} [NeZero k'] {σ : ZMod k' → ZMod (test08 t.1 t.2.1 t.2.2).k}
    (hrim : RimCertAt (pts08 a a' b b' c c' d) ((test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d))
      ((test08 t.1 t.2.1 t.2.2).lab ∘ σ))
    (hrob : IsRobustUnimodal (fun i => ⟪pts08 a a' b b' c c' d ((test08 t.1 t.2.1 t.2.2).lab (σ i)),
      (test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d)⟫))
    (hp : ¬ NoPersistHDN (fun i => pts08 a a' b b' c c' d ((test08 t.1 t.2.1 t.2.2).lab (σ i)))
        ((test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d)) (eF a a' b b' c c' d t))
    -- the SC2 package (chord end at f, parallel set)
    (hSN2 : RegN2 N.F → SC2N2 a a' b b' c c' d) (hST4 : RegT4 N.F → SC2Kb a a' b b' c c' d ∧ SC2K2 a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) :=
  W5.close_hdn_pers N.toW hT hT' ht hreg hrim hrob hp hSN2 hST4

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.close_hdn_pers
