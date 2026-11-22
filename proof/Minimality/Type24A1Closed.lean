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
`a1_e25_lt_small` + `z54_A1` + `E05P5U_A1` (a contradiction with `Hole24R`). -/
theorem a1_closed {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hR : Hole24R x F) (hA1 : Reg.A1 x F) (hO : H24K.SAT.OB1 x)
    (hT : if 0 < det24 x then A1TieSmall x F else A1TieSmall (fun i => -x i) (facNeg F))
    (hS25 : if 0 < det24 x then A1E25Small x F else A1E25Small (fun i => -x i) (facNeg F))
    (hS54 : A1Z54Sample x F) :
    IsRupert (univ.image x) := by
  by_cases htie : ⟪x 2 - x 5, x 5 - x 0⟫ = 0
  · exact a1_tie_rupert_small F hR hA1 htie hT
  · exfalso
    have hlt := a1_e25_lt_small F hR hA1 hO hS25 htie
    have hz := z54_A1 F hA1 hR.2.2.1 hR.1 hO hR.2.2.2.2.1 hS54
    have hA4 := a4_le_of_hA1 F hA1 hR.2.2.1
    rcases E05P5U_A1 F hR.1 hA1.1 hA4 hA1.2 ⟨hz, hlt⟩ with h | h
    · exact hR.2.2.2.2.1 h
    · exact hR.2.2.2.2.2 h

end Minimality.T24.A1
