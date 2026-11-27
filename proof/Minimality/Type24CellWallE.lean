module

public import Minimality.Type24CellWall

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.Stmt

/-!
# The cell-form headline with the far-pair special Prop (job OSPEC3)

`Cell.not_hole24_of_cellCoverEmpty_R` (Type24CellWall.lean) with `OSpec.OpenSpecialE` (Type24OffOB1Res.lean, weaker
than `OpenSpecialR`, Rupert form) in place of `OpenSpecialR`: every `Hole24` point is Rupert, so `Open24Rupert`, the
form the main theorem uses (`main_sorry_of_open24Rupert`).
-/

namespace Minimality.T24.Cell

/-- [PROVED] `CellCoverEmpty L` and `OSpec.OpenSpecialE`: every `Hole24` point is Rupert. -/
theorem rupert_of_cellCoverEmpty_E {L : List Cell24} (hN : CellCoverEmpty L) (hS : OSpec.OpenSpecialE) :
    ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), Hole24 x F → IsRupert (univ.image x) := by
  intro x F hH
  by_cases hO : H24K.SAT.OB1 x
  · exact (hN x F hH.1.1 hO (hole24_cellCoverResidue L hH)).elim
  · exact OSpec.hole24_offOB1_E hH hO hS

/-- [PROVED] `CellCoverEmpty L` and `OSpec.OpenSpecialE` give `Stmt.Open24Rupert`. -/
theorem open24Rupert_of_cellCoverEmpty_E {L : List Cell24} (hN : CellCoverEmpty L) (hS : OSpec.OpenSpecialE) :
    Open24Rupert :=
  OSpec.open24Rupert_of_split_E (openOB1_of_cellCoverEmpty hN) hS

/-- [PROVED] Headline chain after OSPEC4: `CellCoverEmpty L` and `OSpec.OpenSpecialT` (weaker than `OpenSpecialE`)
rule out every `Hole24` up to Rupert-ness. -/
theorem rupert_of_cellCoverEmpty_T {L : List Cell24} (hN : CellCoverEmpty L) (hS : OSpec.OpenSpecialT) :
    ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), Hole24 x F → IsRupert (univ.image x) := by
  intro x F hH
  by_cases hO : H24K.SAT.OB1 x
  · exact (hN x F hH.1.1 hO (hole24_cellCoverResidue L hH)).elim
  · exact OSpec.hole24_offOB1_T hH hO hS

/-- [PROVED] `CellCoverEmpty L` and `OSpec.OpenSpecialT` give `Stmt.Open24Rupert`. -/
theorem open24Rupert_of_cellCoverEmpty_T {L : List Cell24} (hN : CellCoverEmpty L) (hS : OSpec.OpenSpecialT) :
    Open24Rupert :=
  OSpec.open24Rupert_of_split_T (openOB1_of_cellCoverEmpty hN) hS

/-- [PROVED] Headline chain after OSPEC5: `CellCoverEmpty L` and `OSpec.OpenSpecialU` (weaker than `OpenSpecialT`)
rule out every `Hole24` up to Rupert-ness. -/
theorem rupert_of_cellCoverEmpty_U {L : List Cell24} (hN : CellCoverEmpty L) (hS : OSpec.OpenSpecialU) :
    ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), Hole24 x F → IsRupert (univ.image x) := by
  intro x F hH
  by_cases hO : H24K.SAT.OB1 x
  · exact (hN x F hH.1.1 hO (hole24_cellCoverResidue L hH)).elim
  · exact OSpec.hole24_offOB1_U hH hO hS

/-- [PROVED] `CellCoverEmpty L` and `OSpec.OpenSpecialU` give `Stmt.Open24Rupert`. -/
theorem open24Rupert_of_cellCoverEmpty_U {L : List Cell24} (hN : CellCoverEmpty L) (hS : OSpec.OpenSpecialU) :
    Open24Rupert :=
  OSpec.open24Rupert_of_split_U (openOB1_of_cellCoverEmpty hN) hS

/-- [PROVED] Headline chain after OSPEC6: `CellCoverEmpty L` and `OSpec.OpenSpecialV` (weaker than `OpenSpecialU`)
rule out every `Hole24` up to Rupert-ness. -/
theorem rupert_of_cellCoverEmpty_V {L : List Cell24} (hN : CellCoverEmpty L) (hS : OSpec.OpenSpecialV) :
    ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), Hole24 x F → IsRupert (univ.image x) := by
  intro x F hH
  by_cases hO : H24K.SAT.OB1 x
  · exact (hN x F hH.1.1 hO (hole24_cellCoverResidue L hH)).elim
  · exact OSpec.hole24_offOB1_V hH hO hS

/-- [PROVED] `CellCoverEmpty L` and `OSpec.OpenSpecialV` give `Stmt.Open24Rupert`. -/
theorem open24Rupert_of_cellCoverEmpty_V {L : List Cell24} (hN : CellCoverEmpty L) (hS : OSpec.OpenSpecialV) :
    Open24Rupert :=
  OSpec.open24Rupert_of_split_V (openOB1_of_cellCoverEmpty hN) hS

/-- [PROVED] Headline chain after OSPEC7: `CellCoverEmpty L` and `OSpec.OpenSpecialX` (weaker than `OpenSpecialV`)
rule out every `Hole24` up to Rupert-ness. -/
theorem rupert_of_cellCoverEmpty_X {L : List Cell24} (hN : CellCoverEmpty L) (hS : OSpec.OpenSpecialX) :
    ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), Hole24 x F → IsRupert (univ.image x) := by
  intro x F hH
  by_cases hO : H24K.SAT.OB1 x
  · exact (hN x F hH.1.1 hO (hole24_cellCoverResidue L hH)).elim
  · exact OSpec.hole24_offOB1_X hH hO hS

/-- [PROVED] `CellCoverEmpty L` and `OSpec.OpenSpecialX` give `Stmt.Open24Rupert`. -/
theorem open24Rupert_of_cellCoverEmpty_X {L : List Cell24} (hN : CellCoverEmpty L) (hS : OSpec.OpenSpecialX) :
    Open24Rupert :=
  OSpec.open24Rupert_of_split_X (openOB1_of_cellCoverEmpty hN) hS

/-- [PROVED] Headline chain after the OSPEC7 wall views: `CellCoverEmpty L` and `OSpec.OpenSpecialY` (weaker than
`OpenSpecialX`) rule out every `Hole24` up to Rupert-ness. -/
theorem rupert_of_cellCoverEmpty_Y {L : List Cell24} (hN : CellCoverEmpty L) (hS : OSpec.OpenSpecialY) :
    ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), Hole24 x F → IsRupert (univ.image x) := by
  intro x F hH
  by_cases hO : H24K.SAT.OB1 x
  · exact (hN x F hH.1.1 hO (hole24_cellCoverResidue L hH)).elim
  · exact OSpec.hole24_offOB1_Y hH hO hS

/-- [PROVED] `CellCoverEmpty L` and `OSpec.OpenSpecialY` give `Stmt.Open24Rupert`. -/
theorem open24Rupert_of_cellCoverEmpty_Y {L : List Cell24} (hN : CellCoverEmpty L) (hS : OSpec.OpenSpecialY) :
    Open24Rupert :=
  OSpec.open24Rupert_of_split_Y (openOB1_of_cellCoverEmpty hN) hS


/-- [PROVED] Headline chain after OSPEC8: `CellCoverEmpty L` and `OSpec.OpenSpecialZ` (the explicit-wall form,
equivalent to `OpenSpecialY`) rule out every `Hole24` up to Rupert-ness. -/
theorem rupert_of_cellCoverEmpty_Z {L : List Cell24} (hN : CellCoverEmpty L) (hS : OSpec.OpenSpecialZ) :
    ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), Hole24 x F → IsRupert (univ.image x) := by
  intro x F hH
  by_cases hO : H24K.SAT.OB1 x
  · exact (hN x F hH.1.1 hO (hole24_cellCoverResidue L hH)).elim
  · exact OSpec.hole24_offOB1_Z hH hO hS

/-- [PROVED] `CellCoverEmpty L` and `OSpec.OpenSpecialZ` give `Stmt.Open24Rupert`. -/
theorem open24Rupert_of_cellCoverEmpty_Z {L : List Cell24} (hN : CellCoverEmpty L) (hS : OSpec.OpenSpecialZ) :
    Open24Rupert :=
  OSpec.open24Rupert_of_split_Z (openOB1_of_cellCoverEmpty hN) hS

/-- [PROVED] Headline chain after OSPEC9: `CellCoverEmpty L` and `OSpec.OpenSpecialK` (the special piece after the K0
views) rule out every `Hole24` up to Rupert-ness. -/
theorem rupert_of_cellCoverEmpty_K {L : List Cell24} (hN : CellCoverEmpty L) (hS : OSpec.OpenSpecialK) :
    ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), Hole24 x F → IsRupert (univ.image x) := by
  intro x F hH
  by_cases hO : H24K.SAT.OB1 x
  · exact (hN x F hH.1.1 hO (hole24_cellCoverResidue L hH)).elim
  · exact OSpec.hole24_offOB1_K hH hO hS

/-- [PROVED] `CellCoverEmpty L` and `OSpec.OpenSpecialK` give `Stmt.Open24Rupert`. -/
theorem open24Rupert_of_cellCoverEmpty_K {L : List Cell24} (hN : CellCoverEmpty L) (hS : OSpec.OpenSpecialK) :
    Open24Rupert :=
  OSpec.open24Rupert_of_split_K (openOB1_of_cellCoverEmpty hN) hS

end Minimality.T24.Cell
