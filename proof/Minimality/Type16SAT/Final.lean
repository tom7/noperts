module

public import Minimality.Type16SAT.Cls16
public import Minimality.Type16SAT.LinkPPMP
public import Minimality.Type16SAT.LinkPPMM
public import Minimality.Type16SAT.LinkPMMP

@[expose] public section

/-!
# Type 16: the closed classes, unconditionally (J8)

`isRupert_cls3`: a type 16 shape whose strict class vector is one of `++-+`, `++--`, `+--+` or their `sigma16` images
`-+-+`, `---+`, `-+--` (`Cls16Closed`, in `Cls16.lean`) is Rupert.  This is `isRupert_cls3_of` (Cls16.lean) applied to the
three kernel-checked class cores `rupert_of_corePPMP`, `rupert_of_corePPMM`, `rupert_of_corePMMP` (Link modules).
-/

set_option autoImplicit false
open Finset
open Minimality

namespace Minimality.H16.SAT

/-- **Type 16, the three closed classes and their sigma images are Rupert.** -/
theorem isRupert_cls3 {x : Fin 7 → ℝ³} (T : Type16 x) (h : Cls16Closed x) : IsRupert (univ.image x) :=
  isRupert_cls3_of Minimality.H16K.SAT.rupert_of_corePPMP Minimality.H16K.SAT.rupert_of_corePPMM
    Minimality.H16K.SAT.rupert_of_corePMMP T h

end Minimality.H16.SAT
