module

public import Minimality.Type16SAT.Cls16Z
public import Minimality.Type16SAT.LinkPMZS

@[expose] public section

/-!
# Type 16: the class `+---` with a nonzero shape entry of `Z`, unconditionally (the fact "PM_ZS")

`isRupert_cls16Z`: a type 16 shape whose strict class vector (the signs of `C * [0126]`, `C * [0134]`, `C * [1234]`,
`C * [2346]`, with `C = [3056]` the chirality bracket) is `+---` and for which one of the 18 shape entries of `Z` is nonzero
(`¬ ZShape16 x F`, `Cls16Z.lean`), or whose `sigma16` image has these properties (class vector `----` on `x`), is Rupert.
This is `isRupert_cls16Z_of` applied to the kernel-checked class core `rupert_of_corePMZS` (`LinkPMZS.lean`): one SAT proof from the
sign-matrix encoder with the class units and the one class clause "some entry of `Z` is positive or negative".
With `isRupert_cls16A` (some inner product `T(d03, d16)`, `T(d06, d16)` nonzero) the residual of the class `+---` lies on the
stratum `Z` with both inner products zero.
-/

set_option autoImplicit false
open Finset
open Minimality

namespace Minimality.H16.SAT

/-- The class `+---` with some entry of `Z` nonzero for the facet family `h16g_fac T` of `x`, or `----` with some entry nonzero
for the facet family `h16g_fac T.sigma` of `x ∘ sigma16`. -/
def Cls16Z (x : Fin 7 → ℝ³) (T : Type16 x) : Prop :=
  let C := C16 x
  let b1 := br16 x 0 1 2 6
  let b2 := br16 x 0 1 3 4
  let b3 := br16 x 1 2 3 4
  let b4 := br16 x 2 3 4 6
  (0 < C * b1 ∧ C * b2 < 0 ∧ C * b3 < 0 ∧ C * b4 < 0 ∧ ¬ ZShape16 x (Minimality.H16A.h16g_fac T)) ∨
  (C * b1 < 0 ∧ C * b2 < 0 ∧ C * b3 < 0 ∧ C * b4 < 0 ∧
    ¬ ZShape16 (x ∘ sigma16) (Minimality.H16A.h16g_fac T.sigma))

/-- **Type 16, the class `+---` (and its `sigma16` image `----`) with a nonzero entry of `Z` is Rupert.** -/
theorem isRupert_cls16Z {x : Fin 7 → ℝ³} (T : Type16 x) (h : Cls16Z x T) : IsRupert (univ.image x) :=
  isRupert_cls16Z_of Minimality.H16K.SAT.rupert_of_corePMZS T (Minimality.H16A.h16g_fac T)
    (Minimality.H16A.h16g_fac T.sigma) h

end Minimality.H16.SAT
