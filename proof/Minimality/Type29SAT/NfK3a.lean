module

public import Minimality.Type29SAT.Nf

@[expose] public section

/-! Type 29: from a normal form of class K3a (`a2 < 0`, `b0 > 0`, `V > 0`) to the core theorem; facet brackets `[0134]+ [0245]+ [1235]-` for `D > 0`, mirrored for `D < 0`. -/

set_option autoImplicit false
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H29.SAT

/-- **Class K3a from the core theorem**: if every type 29 facet family with the brackets `[0123]+ [0134]+ [0245]+ [1235]-` is
Rupert, every normal form with `a2 < 0`, `b0 > 0`, `V > 0` is Rupert. -/
theorem nf29_K3a_of_core
    (hcore : ∀ {y : Fin 7 → ℝ³} (_ : S0xFac 9 s0x_S29 y),
      0 < det3 (y 1 - y 0) (y 2 - y 0) (y 3 - y 0) → 0 < det3 (y 1 - y 0) (y 3 - y 0) (y 4 - y 0) →
      0 < det3 (y 2 - y 0) (y 4 - y 0) (y 5 - y 0) → det3 (y 2 - y 1) (y 3 - y 1) (y 5 - y 1) < 0 →
      IsRupert (univ.image y))
    {x : Fin 7 → ℝ³} (N : NF29 x) (ha2 : N.a2 < 0) (hb0 : 0 < N.b0) (hV : 0 < N.V) :
    IsRupert (univ.image x) := by
  obtain ⟨i0, i1, i2, i3⟩ := nf29_brackets N
  have hDD := N.hDD
  let F := s0x_fac29 N.facets
  rcases lt_or_gt_of_ne N.hD with hD | hD
  · refine isRupert_of_mir (hcore (mirFac F) ?_ ?_ ?_ ?_)
    · show 0 < det3 (mir (x 1) - mir (x 0)) (mir (x 2) - mir (x 0)) (mir (x 3) - mir (x 0))
      rw [mir_br, i0]; have := mul_neg_of_neg_of_pos hD hDD; linarith
    · show 0 < det3 (mir (x 1) - mir (x 0)) (mir (x 3) - mir (x 0)) (mir (x 4) - mir (x 0))
      rw [mir_br, i1]; have := mul_neg_of_neg_of_pos hD hb0; linarith
    · show 0 < det3 (mir (x 2) - mir (x 0)) (mir (x 4) - mir (x 0)) (mir (x 5) - mir (x 0))
      rw [mir_br, i2]; have := mul_neg_of_neg_of_pos hD hV; linarith
    · show det3 (mir (x 2) - mir (x 1)) (mir (x 3) - mir (x 1)) (mir (x 5) - mir (x 1)) < 0
      rw [mir_br, i3]; have := mul_pos_of_neg_of_neg hD ha2; linarith
  · refine hcore F ?_ ?_ ?_ ?_
    · rw [i0]; exact mul_pos hD hDD
    · rw [i1]; exact mul_pos hD hb0
    · rw [i2]; exact mul_pos hD hV
    · rw [i3]; exact mul_neg_of_pos_of_neg hD ha2

end Minimality.H29.SAT
