module

public import Minimality.Type16SAT.Cls16C
public import Minimality.Type16SAT.LinkPMMM

@[expose] public section

/-!
# Type 16: the class `+---` with a nonzero inner product, unconditionally (the fact "PM_U12")

`isRupert_cls16A`: a type 16 shape whose strict class vector (the signs of `C * [0126]`, `C * [0134]`, `C * [1234]`,
`C * [2346]`, with `C = [3056]` the chirality bracket) is `+---` and whose edge `x 1 - x 6` is not orthogonal to both
`x 0 - x 3` and `x 0 - x 6`, or whose `sigma16` image has these properties (class vector `----` on `x`), is Rupert.
This is `isRupert_cls16A_of` (`Cls16C.lean`) applied to the kernel-checked class core `rupert_of_corePMMM`
(`LinkPMMM.lean`): a core of 4,285 clauses, derived by one SAT proof from the sign-matrix encoder with the four class
units and the one class clause "`T(d03, d16) > 0`, `< 0`, or `T(d06, d16) > 0`, `< 0`".
The residual of the class `+---` is the shapes with both inner products zero.
-/

set_option autoImplicit false
open Finset
open Minimality

namespace Minimality.H16.SAT

/-- **Type 16, the class `+---` (and its `sigma16` image `----`) in case A is Rupert.** -/
theorem isRupert_cls16A {x : Fin 7 → ℝ³} (T : Type16 x) (h : Cls16A x) : IsRupert (univ.image x) :=
  isRupert_cls16A_of Minimality.H16K.SAT.rupert_of_corePMMM T h

end Minimality.H16.SAT
