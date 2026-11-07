module

public import Minimality.Type29SAT.Mir

@[expose] public section

/-!
# Type 29: from a normal form `N : NF29 x` of class K4a to the core theorem

The four brackets `[0123]`, `[0134]`, `[0245]`, `[1235]` of a normal form are `D * (a0 b2 - a2 b0)`, `D * b0`, `D * V`,
`D * a2` (`D = det3 E1 E2 E3`).  For `D > 0` the class `K4a` (`a2 > 0`, `b0 > 0`, `V < 0`) has the brackets of the core
`[0123]+ [0134]+ [0245]- [1235]+`; for `D < 0` the mirror image has them.  So a core theorem for all facet families
of those four bracket signs closes the class.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H29.SAT

/-- The brackets of a normal form in terms of `D`. -/
theorem nf29_brackets {x : Fin 7 → ℝ³} (N : NF29 x) :
    det3 (x 1 - x 0) (x 2 - x 0) (x 3 - x 0) = det3 N.E₁ N.E₂ N.E₃ * (N.a0 * N.b2 - N.a2 * N.b0) ∧
    det3 (x 1 - x 0) (x 3 - x 0) (x 4 - x 0) = det3 N.E₁ N.E₂ N.E₃ * N.b0 ∧
    det3 (x 2 - x 0) (x 4 - x 0) (x 5 - x 0) = det3 N.E₁ N.E₂ N.E₃ * N.V ∧
    det3 (x 2 - x 1) (x 3 - x 1) (x 5 - x 1) = det3 N.E₁ N.E₂ N.E₃ * N.a2 := by
  have e0 := N.x0
  have e1 := N.x1
  have e2 := N.x2
  have e3 := N.x3
  have e4 := N.x4
  have e5 := N.x5
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [e0, e1, e2, e3, e4, e5, nfP, NF29.V, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul]
    ring

/-- The reflection negates the bracket of four points. -/
theorem mir_br (a b c d : ℝ³) : det3 (mir b - mir a) (mir c - mir a) (mir d - mir a) = - det3 (b - a) (c - a) (d - a) := by
  rw [← mir_sub, ← mir_sub, ← mir_sub, mir_det3]

/-- **Class K4a from the core theorem**: if every type 29 facet family with the brackets `[0123]+ [0134]+ [0245]- [1235]+` is
Rupert, every normal form with `a2 > 0`, `b0 > 0`, `V < 0` is Rupert. -/
theorem nf29_K4a_of_core
    (hcore : ∀ {y : Fin 7 → ℝ³} (_ : S0xFac 9 s0x_S29 y),
      0 < det3 (y 1 - y 0) (y 2 - y 0) (y 3 - y 0) → 0 < det3 (y 1 - y 0) (y 3 - y 0) (y 4 - y 0) →
      det3 (y 2 - y 0) (y 4 - y 0) (y 5 - y 0) < 0 → 0 < det3 (y 2 - y 1) (y 3 - y 1) (y 5 - y 1) →
      IsRupert (univ.image y))
    {x : Fin 7 → ℝ³} (N : NF29 x) (ha2 : 0 < N.a2) (hb0 : 0 < N.b0) (hV : N.V < 0) :
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
    · show det3 (mir (x 2) - mir (x 0)) (mir (x 4) - mir (x 0)) (mir (x 5) - mir (x 0)) < 0
      rw [mir_br, i2]; have := mul_pos_of_neg_of_neg hD hV; linarith
    · show 0 < det3 (mir (x 2) - mir (x 1)) (mir (x 3) - mir (x 1)) (mir (x 5) - mir (x 1))
      rw [mir_br, i3]; have := mul_neg_of_neg_of_pos hD ha2; linarith
  · refine hcore F ?_ ?_ ?_ ?_
    · rw [i0]; exact mul_pos hD hDD
    · rw [i1]; exact mul_pos hD hb0
    · rw [i2]; exact mul_neg_of_pos_of_neg hD hV
    · rw [i3]; exact mul_pos hD ha2

end Minimality.H29.SAT
