module

public import Minimality.Type16SAT.Cls16C
public import Minimality.Type16SAT.LinkPMPMU

@[expose] public section

/-!
# Type 16: the class `+-+-` with a nonzero inner product (the T case of the class `+-+-`)

`isRupert_corePMPM_T`: the class core `Core16T 1 (-1) 1 (-1)` (strict signs of `C * [0126]`, `C * [0134]`, `C * [1234]`,
`C * [2346]` equal to `+-+-` with `0 < C = [3056]`, and `CaseT16`: one of `T(d03, d16)`, `T(d06, d16)` nonzero), the kernel-checked
class core `rupert_of_corePMPMU` of `LinkPMPMU.lean` (one SAT proof from the sign-matrix encoder with the four class units and the
one class clause "`T(d03, d16) > 0`, `< 0`, or `T(d06, d16) > 0`, `< 0`").  The class `+-+-` and its `sigma16` image `--+-` are
assembled from this core, `Core16Z 1 (-1) 1 (-1)` (`FinalZS16PM`) and the slide leaf on `PL` in `FinalPMPM16`.
-/

set_option autoImplicit false
open Finset
open Minimality

namespace Minimality.H16.SAT

/-- **Type 16, the class `+-+-` with `CaseT16`: the case core.** -/
theorem isRupert_corePMPM_T : Core16T 1 (-1) 1 (-1) := Minimality.H16K.SAT.rupert_of_corePMPMU

end Minimality.H16.SAT
