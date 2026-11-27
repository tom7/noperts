module

public import Minimality.Type24CellWall

/-!
# Type 24: the named-cover residue from the cell cover (PRUNE24, 2026-11-27)

`Type24NamedCover` defines `NamedCoverResidue` / `NamedCoverEmpty`; the proof that a `Hole24` point lies in the
residue is the cell route: `hole24_cellCoverResidue cells24` followed by `namedCoverResidue_of_cellCoverResidue`
(`Type24CellWall`).  The old per-certificate Edge-Plane proofs are deleted (nopert229 notes/TOOLBOX-LEAN.md,
"Pruned 11-27").  Public names unchanged: `hole24_namedCoverResidue`, `not_hole24_of_namedCoverEmpty`,
`OSpec.not_hole24_of_namedCoverEmpty_W`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.HC Minimality.T24.SF Minimality.T24.Stmt

namespace Minimality.T24.TwoCone

/-- **FT2:** `Hole24 x F` implies `NamedCoverResidue x F` (cell route). -/
theorem hole24_namedCoverResidue {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : Hole24 x F) :
    NamedCoverResidue x F :=
  Cell.namedCoverResidue_of_cellCoverResidue (Cell.hole24_cellCoverResidue Cell.cells24 hF)

/-- **FU1:** `NamedCoverEmpty` together with `OpenSpecial` (the off-`OB1` walls `a₄ = 1 ∨ a₅ = 1`
and `Q45Special'`) rules out every `Hole24 x F`, via `hole24_namedCoverResidue` and
`hole24_ob1_or_special`. -/
theorem not_hole24_of_namedCoverEmpty (hN : NamedCoverEmpty) (hS : OpenSpecial) :
    ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), ¬ Hole24 x F := by
  intro x F hH
  have hres := hole24_namedCoverResidue hH
  have hC : CbarIn x := hres.1
  have hF : HoleFull x F := holeFull_of_hole24 hH
  rcases hole24_ob1_or_special hH with hO | ⟨hO, hw⟩ | hq
  · exact hN x F hC hO hres
  · exact hS x F hO (Or.inl hw) hF
  · by_cases hO : H24K.SAT.OB1 x
    · exact hN x F hC hO hres
    · exact hS x F hO (Or.inr hq) hF

end Minimality.T24.TwoCone

namespace Minimality.T24.OSpec

/-- [PROVED] `NamedCoverEmpty` and the restricted special piece rule out every `Hole24` point. -/
theorem not_hole24_of_namedCoverEmpty_W (hN : TwoCone.NamedCoverEmpty) (hS : OpenSpecialW) :
    ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), ¬ Hole24 x F := by
  intro x F hH
  by_cases hO : H24K.SAT.OB1 x
  · have hres := TwoCone.hole24_namedCoverResidue hH
    exact hN x F hres.1 hO hres
  · exact hole24_offOB1 hH hO hS

end Minimality.T24.OSpec
