module

public import Minimality.Type16SAT.Cls16W
public import Minimality.Type16SAT.Final
public import Minimality.Type16SAT.LinkPPPZ
public import Minimality.Type16SAT.LinkPPZP
public import Minimality.Type16SAT.LinkPZPP
public import Minimality.Type16SAT.LinkZPPP
public import Minimality.Type16SAT.LinkPMZP
public import Minimality.Type16SAT.LinkZPPM
public import Minimality.Type16SAT.LinkPPZM
public import Minimality.Type16SAT.LinkZPMP
public import Minimality.Type16SAT.LinkZPMM

@[expose] public section

/-!
# Type 16: all closed classes and walls, unconditional (J10)
-/

set_option autoImplicit false
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.H29.SAT

namespace Minimality.H16.SAT

/-- **Type 16, the walls (16 sign vectors with one zero product) are Rupert.** -/
theorem isRupert_cls3w {x : Fin 7 → ℝ³} (T : Type16 x) (h : Cls16ClosedW x) : IsRupert (univ.image x) :=
  isRupert_cls3w_of Minimality.H16K.SAT.rupert_of_corePPPZ Minimality.H16K.SAT.rupert_of_corePPZP Minimality.H16K.SAT.rupert_of_corePZPP Minimality.H16K.SAT.rupert_of_coreZPPP Minimality.H16K.SAT.rupert_of_corePMZP Minimality.H16K.SAT.rupert_of_coreZPPM Minimality.H16K.SAT.rupert_of_corePPZM Minimality.H16K.SAT.rupert_of_coreZPMP Minimality.H16K.SAT.rupert_of_coreZPMM T h

/-- **Type 16, the closed classes and the closed walls are Rupert.** -/
theorem isRupert_closed {x : Fin 7 → ℝ³} (T : Type16 x) (h : Cls16Closed x ∨ Cls16ClosedW x) :
    IsRupert (univ.image x) := by
  rcases h with h | h
  · exact isRupert_cls3 T h
  · exact isRupert_cls3w T h

end Minimality.H16.SAT
