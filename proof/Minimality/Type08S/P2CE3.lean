module

public import Minimality.Type08S.P2CE2

@[expose] public section

set_option relaxedAutoImplicit true

set_option autoImplicit true

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- `close_hdn_pers` (P2Pkg statement), unconditional on the SC2 package. -/
theorem close_hdn_pers_full {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
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
  close_hdn_pers' N hT hT' ht hreg hrim hrob hp (fun hr => cef_N2 N hr)
    (fun hr => ⟨cef_Kb N hr, cef_K2 N hr⟩)

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.close_hdn_pers_full
