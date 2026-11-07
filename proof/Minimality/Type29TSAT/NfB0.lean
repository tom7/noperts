module

public import Minimality.Type29TSAT.LinkB0
public import Minimality.Type29SAT.Nf

@[expose] public section

/-! Type 29 (L29T, T10): from a normal form with `b0 = 0` to core B0; `[0134] = D * b0`, and its mirror image. -/

set_option autoImplicit false
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.H29.SAT

namespace Minimality.H29T.SAT

/-- **Class `b0 = 0` from the core theorem**: if every type 29 facet family with `[0123] > 0` and `[0134] = 0` is Rupert,
every normal form with `b0 = 0` is Rupert (no hypothesis on `a2`, `V`). -/
theorem nf29_B0_of_core
    (hcore : ∀ {y : Fin 7 → ℝ³} (_ : S0xFac 9 s0x_S29 y),
      0 < det3 (y 1 - y 0) (y 2 - y 0) (y 3 - y 0) → det3 (y 1 - y 0) (y 3 - y 0) (y 4 - y 0) = 0 →
      IsRupert (univ.image y))
    {x : Fin 7 → ℝ³} (N : NF29 x) (hb : N.b0 = 0) :
    IsRupert (univ.image x) := by
  obtain ⟨i0, i1, i2, i3⟩ := nf29_brackets N
  have hDD := N.hDD
  let F := s0x_fac29 N.facets
  rcases lt_or_gt_of_ne N.hD with hD | hD
  · refine isRupert_of_mir (hcore (mirFac F) ?_ ?_)
    · show 0 < det3 (mir (x 1) - mir (x 0)) (mir (x 2) - mir (x 0)) (mir (x 3) - mir (x 0))
      rw [mir_br, i0]; have := mul_neg_of_neg_of_pos hD hDD; linarith
    · show det3 (mir (x 1) - mir (x 0)) (mir (x 3) - mir (x 0)) (mir (x 4) - mir (x 0)) = 0
      rw [mir_br, i1, hb]; ring
  · refine hcore F ?_ ?_
    · rw [i0]; exact mul_pos hD hDD
    · rw [i1, hb]; ring

end Minimality.H29T.SAT
