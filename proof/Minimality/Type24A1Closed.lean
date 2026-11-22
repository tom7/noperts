import Minimality.Type24A1Small
import Minimality.Type24A1Z54

/-!
# Type 24, region A1 inside OB1: the glue

`a1_closed`: on `Hole24R` with `Reg.A1` and `OB1`, the points are Rupert, modulo the named sample-fact bundles
`A1TieSmall` (the tie, via `a1_tie_rupert_small`) and `A1E25Sample`, `A1Z54Sample` (off the tie, via
`a1_offtie_rupert`). The case split is on the tie `⟪x 2 - x 5, x 5 - x 0⟫ = 0`.
-/


open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.A1

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell

/-- **Region A1 inside OB1**, modulo the named sample facts: the tie by `a1_tie_rupert_small`, off the tie by
`a1_offtie_rupert` (a contradiction with `Hole24R`). -/
theorem a1_closed {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hR : Hole24R x F) (hA1 : Reg.A1 x F) (hO : H24K.SAT.OB1 x)
    (hT : if 0 < det24 x then A1TieSmall x F else A1TieSmall (fun i => -x i) (facNeg F))
    (hS25 : A1E25Sample x F) (hS54 : A1Z54Sample x F) :
    IsRupert (univ.image x) := by
  by_cases htie : ⟪x 2 - x 5, x 5 - x 0⟫ = 0
  · exact a1_tie_rupert_small F hR hA1 htie hT
  · exact (a1_offtie_rupert F hR hA1 hO htie hS25 hS54).elim

end Minimality.T24.A1
