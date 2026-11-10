module

public import Minimality.Type16SAT.PLSlide16
public import Minimality.Type16SAT.FinalA16PM
public import Minimality.Type16SAT.FinalZS16PM

@[expose] public section

/-!
# Type 16: the class `+-+-` (and its `sigma16` image `--+-`) is Rupert, unconditionally

`isRupert_clsPMPM`: `isRupert_clsPMPM_of` (`PLSlide16.lean`) applied to the two kernel-checked class cores
`isRupert_corePMPM_T` (`FinalA16PM`) and `isRupert_corePMPM_Z` (`FinalZS16PM`); the stratum `PL` is the slide leaf.
-/

set_option autoImplicit false
open Finset
open Minimality

namespace Minimality.H16.SAT

/-- **Type 16, the class `+-+-` and its `sigma16` image `--+-` is Rupert.** -/
theorem isRupert_clsPMPM {x : Fin 7 → ℝ³} (T : Type16 x)
    (h : (0 < C16 x * br16 x 0 1 2 6 ∧ C16 x * br16 x 0 1 3 4 < 0 ∧ 0 < C16 x * br16 x 1 2 3 4 ∧
        C16 x * br16 x 2 3 4 6 < 0) ∨
      (C16 x * br16 x 0 1 2 6 < 0 ∧ C16 x * br16 x 0 1 3 4 < 0 ∧ 0 < C16 x * br16 x 1 2 3 4 ∧
        C16 x * br16 x 2 3 4 6 < 0)) :
    IsRupert (univ.image x) :=
  isRupert_clsPMPM_of isRupert_corePMPM_T isRupert_corePMPM_Z T h

end Minimality.H16.SAT
