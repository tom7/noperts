module

public import Minimality.Type29SAT.Nf

@[expose] public section

/-! Type 29: from a normal form with `V = 0` to the core theorem; the bracket `[0245] = D * V` vanishes, and so does its mirror image. -/

set_option autoImplicit false
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H29.SAT

/-- **Class V0 from the core theorem**: if every type 29 facet family with `[0123] > 0` and `[0245] = 0` is Rupert, every
normal form with `V = 0` is Rupert.  There is no hypothesis on `a2`, `b0`. -/
theorem nf29_V0_of_core
    (hcore : ∀ {y : Fin 7 → ℝ³} (_ : S0xFac 9 s0x_S29 y),
      0 < det3 (y 1 - y 0) (y 2 - y 0) (y 3 - y 0) → det3 (y 2 - y 0) (y 4 - y 0) (y 5 - y 0) = 0 →
      IsRupert (univ.image y))
    {x : Fin 7 → ℝ³} (N : NF29 x) (hV : N.V = 0) :
    IsRupert (univ.image x) := by
  obtain ⟨i0, i1, i2, i3⟩ := nf29_brackets N
  have hDD := N.hDD
  let F := s0x_fac29 N.facets
  rcases lt_or_gt_of_ne N.hD with hD | hD
  · refine isRupert_of_mir (hcore (mirFac F) ?_ ?_)
    · show 0 < det3 (mir (x 1) - mir (x 0)) (mir (x 2) - mir (x 0)) (mir (x 3) - mir (x 0))
      rw [mir_br, i0]; have := mul_neg_of_neg_of_pos hD hDD; linarith
    · show det3 (mir (x 2) - mir (x 0)) (mir (x 4) - mir (x 0)) (mir (x 5) - mir (x 0)) = 0
      rw [mir_br, i2, hV]; ring
  · refine hcore F ?_ ?_
    · rw [i0]; exact mul_pos hD hDD
    · rw [i2, hV]; ring

end Minimality.H29.SAT
