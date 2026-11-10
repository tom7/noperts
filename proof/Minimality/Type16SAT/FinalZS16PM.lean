module

public import Minimality.Type16SAT.Cls16Z
public import Minimality.Type16SAT.LinkPMPMZ

@[expose] public section

/-!
# Type 16: the class `+-+-` with a nonzero shape entry of `Z` (the Z case of the class `+-+-`)

`isRupert_corePMPM_Z`: `Core16Z 1 (-1) 1 (-1)`, the kernel-checked class core `rupert_of_corePMPMZ` of `LinkPMPMZ.lean`: one SAT
proof from the sign-matrix encoder with the class units `+-+-` and the one class clause "some entry of `Z` is positive or negative"
(the same 18 entries as `ZShape16`, with the extra triple routes `TriDataX` that `FinalZS16` uses).
-/

set_option autoImplicit false
open Finset
open Minimality

namespace Minimality.H16.SAT

/-- **Type 16, the class `+-+-` with `¬ ZShape16`: the case core.** -/
theorem isRupert_corePMPM_Z : Core16Z 1 (-1) 1 (-1) := Minimality.H16K.SAT.rupert_of_corePMPMZ

end Minimality.H16.SAT
