module

public import Minimality.Type24Cells28
public import Minimality.Type24A236Cover
public import Minimality.Type24OffOB1DW

/-!
# Type 24: the open Prop `CellCoverEmptyE` (only `A236E` points on both sides)

`CellCoverEmptyE L` is `CellCoverEmpty L` restricted to the points where the letter condition `A236E` of the A2.236
wall holds on `x` and on the `π_24` twin (`a236_cert_or_E`: elsewhere a `Gen.LexAny` / `Gen.SplitAny` certificate
exists).  Hole points satisfy both (`holeLeaf_a236E`, `holeLeaf_a236E_twin`), so the narrower Prop suffices.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.Stmt

namespace Minimality.T24.Cell

/-- **[OPEN] `CellCoverEmptyE L`**: on `CbarIn`, `OB1`, with `A236E` on `x` and on the twin, the point is not in the
cell-cover residue of `L`. -/
def CellCoverEmptyE (L : List Cell24) : Prop :=
  ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), CbarIn x → H24K.SAT.OB1 x → A236E x F →
    A236E (x ∘ Sym.pi24) (Sym.sym24 F) → ¬ CellCoverResidue L x F

/-- The old open Prop implies the narrower one. -/
theorem cellCoverEmptyE_of_cellCoverEmpty {L : List Cell24} (h : CellCoverEmpty L) : CellCoverEmptyE L :=
  fun x F hC hO _ _ => h x F hC hO

/-- `CellCoverEmptyE L` rules out the generic hole `HoleLeaf` on `OB1`. -/
theorem not_holeLeaf_of_cellCoverEmptyE {L : List Cell24} (hN : CellCoverEmptyE L) (x : Fin 7 → ℝ³)
    (F : S0xFac 9 s0x_S24 x) (hO : H24K.SAT.OB1 x) : ¬ HoleLeaf x F := fun h =>
  hN x F h.1 hO (holeLeaf_a236E h hO) (holeLeaf_a236E_twin h hO) (holeLeaf_cellCoverResidue L h)

/-- `CellCoverEmptyE L → Stmt.OpenOB1`. -/
theorem openOB1_of_cellCoverEmptyE {L : List Cell24} (hN : CellCoverEmptyE L) : OpenOB1 := fun x F hO hF =>
  not_holeLeaf_of_cellCoverEmptyE hN x F hO (holeLeaf_of_holeFull hF)

/-- [PROVED] `CellCoverEmptyE L` and `OSpec.OpenSpecialO` give `Open24Rupert`. -/
theorem open24Rupert_of_cellCoverEmptyE_O {L : List Cell24} (hN : CellCoverEmptyE L)
    (hS : OSpec.OpenSpecialO) : Open24Rupert :=
  OSpec.open24Rupert_of_split_O (openOB1_of_cellCoverEmptyE hN) hS

/-- [PROVED] Headline chain: `CellCoverEmptyE cells28` and `OSpec.OpenSpecialO` give `Open24Rupert`. -/
theorem open24Rupert_of_cellCoverEmptyE28_O (hN : CellCoverEmptyE cells28) (hS : OSpec.OpenSpecialO) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmptyE_O hN hS

end Minimality.T24.Cell
