module

public import Minimality.Type24CellWallE
public import Minimality.Type24GapLemmas2

/-!
# Type 24: the extended cell list `cells28`

The pocket point `t1_1e-2_nb548_k0_e1e-02` (nopert229 data/hard/holekit/gapt2oc_resid.lines, GAPT2OC 11-27) has no
Lex / Split certificate in any cell of `cells24` [EXACT], while its certificates sit on walls of the four cells
`cell0164`, `cell01634`, `cell05326`, `cell046125` (Type24GapLemmas2.lean).  Since a longer list gives a weaker open Prop
(`cellCoverEmpty_mono`), the headline open Prop on `OB1` becomes `CellCoverEmpty cells28`.
-/

@[expose] public section

open Finset
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.Stmt

namespace Minimality.T24.Cell

/-- `cells24` plus the four cells of the GAPT2OC pocket. -/
def cells28 : List Cell24 :=
  cells24 ++ [cell0164, cell01634, cell05326, cell046125]

/-- [PROVED] Headline chain with `cells28`: `CellCoverEmpty cells28` and `OSpec.OpenSpecialB` give `Open24Rupert`. -/
theorem open24Rupert_of_cellCoverEmpty28_B (hN : CellCoverEmpty cells28) (hS : OSpec.OpenSpecialB) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmpty_B hN hS

/-- [PROVED] Headline chain with `cells28` after the double-wall K0 views (OSPEC11): `CellCoverEmpty cells28` and
`OSpec.OpenSpecialD` give `Open24Rupert`. -/
theorem open24Rupert_of_cellCoverEmpty28_D (hN : CellCoverEmpty cells28) (hS : OSpec.OpenSpecialD) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmpty_D hN hS

/-- [PROVED] Headline chain with `cells28` after the e26 views on `s = 1` / `t = 1` (OSPEC12): `CellCoverEmpty
cells28` and `OSpec.OpenSpecialS` give `Open24Rupert`. -/
theorem open24Rupert_of_cellCoverEmpty28_S (hN : CellCoverEmpty cells28) (hS : OSpec.OpenSpecialS) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmpty_S hN hS

/-- [PROVED] Headline chain with `cells28` after the diagonal views `x 1 - x 5` / `x 1 - x 4` (OSPEC13): `CellCoverEmpty
cells28` and `OSpec.OpenSpecialG` give `Open24Rupert`. -/
theorem open24Rupert_of_cellCoverEmpty28_G (hN : CellCoverEmpty cells28) (hS : OSpec.OpenSpecialG) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmpty_G hN hS

/-- [PROVED] Headline chain with `cells28` after the T234 views on the B2 valley (OSPEC14): `CellCoverEmpty cells28` and
`OSpec.OpenSpecialH` give `Open24Rupert`. -/
theorem open24Rupert_of_cellCoverEmpty28_H (hN : CellCoverEmpty cells28) (hS : OSpec.OpenSpecialH) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmpty_H hN hS

/-- [PROVED] Headline chain with `cells28` in the reduced T234 form (OSPEC15): `CellCoverEmpty cells28` and
`OSpec.OpenSpecialI` give `Open24Rupert`. -/
theorem open24Rupert_of_cellCoverEmpty28_I (hN : CellCoverEmpty cells28) (hS : OSpec.OpenSpecialI) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmpty_I hN hS

end Minimality.T24.Cell
