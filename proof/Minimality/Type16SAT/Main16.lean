module

public import Minimality.Type16SAT.FinalW
public import Minimality.Type16SAT.FinalA16
public import Minimality.Type16SAT.FinalZS16
public import Minimality.Type16SAT.PLSlide16
public import Minimality.Type16SAT.FinalPMPM16
public import Minimality.Type16SAT.FinalW16
public import Minimality.Type16SAT.FinalW16X
public import Minimality.Type16SAT.FinalW16Y
public import Minimality.Type16SAT.FinalLast16
public import Minimality.Type16SAT.GPDead16
public import Minimality.Type16SAT.Exh16

@[expose] public section

/-!
# Type 16: every realizing solid is Rupert

The sign-matrix SAT route in one theorem. `isRupert_type16 T` holds for every `T : Type16 x`, at every metric: the
sign vector of the brackets `[0126] [0134] [1234] [2346]` (times `C16 x`) lies in one of the classes closed by a
kernel-checked LRAT core (`isRupert_closed`, `isRupert_cls16A`, `isRupert_cls16Z`, `isRupert_cls16M_resid`,
`isRupert_clsPMPM`, `isRupert_wallR_all`, `isRupert_wallX_all`, `isRupert_pmzm`, `isRupert_z2_all`, `isRupert_last`),
is excluded by one sign relation of the brackets (`not_cls16Dead`), or is covered by none of them, which `cls16_exhaust`
refutes.
-/

namespace Minimality.H16.SAT

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.H29.SAT

theorem isRupert_type16 {x : Fin 7 → ℝ³} (T : Type16 x) : IsRupert (univ.image x) := by
  by_cases hcl : Cls16Closed x ∨ Cls16ClosedW x
  · exact isRupert_closed T hcl
  by_cases hA : Cls16A x
  · exact isRupert_cls16A T hA
  by_cases hZ : Cls16Z x T
  · exact isRupert_cls16Z T hZ
  by_cases hM : Cls16M x
  · exact isRupert_cls16M_resid T hM hA hZ
  by_cases hP : (0 < C16 x * br16 x 0 1 2 6 ∧ C16 x * br16 x 0 1 3 4 < 0 ∧ 0 < C16 x * br16 x 1 2 3 4 ∧
      C16 x * br16 x 2 3 4 6 < 0) ∨
    (C16 x * br16 x 0 1 2 6 < 0 ∧ C16 x * br16 x 0 1 3 4 < 0 ∧ 0 < C16 x * br16 x 1 2 3 4 ∧
      C16 x * br16 x 2 3 4 6 < 0)
  · exact isRupert_clsPMPM T hP
  by_cases hDead : Cls16Dead x
  · exact (not_cls16Dead T hDead).elim
  by_cases hW : Cls16WallR x ∨ Cls16WallX x ∨ (Vec16 1 (-1) 0 (-1) x ∨ Vec16 (-1) (-1) 0 (-1) x)
  · rcases hW with hW | hW | hW
    · exact isRupert_wallR_all T hW
    · exact isRupert_wallX_all T hW
    · exact isRupert_pmzm T hW
  rcases cls16_exhaust x hcl hM hP hDead hW with h | h
  · exact isRupert_z2_all T h
  · exact isRupert_last T h

end Minimality.H16.SAT
