module

public import Minimality.Type16SAT.Cls16W
public import Minimality.Type16SAT.Final
public import Minimality.Type16SAT.GPDead16
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

/-- **Type 16, the walls (16 sign vectors with one zero product) are Rupert.** Thirteen of them have
`C * [1234] ≥ 0` and `C * [0134] ≥ 0` or `C * [2346] ≥ 0` and do not occur (`not_cls16Dead`); the others
(`0+-+`, `0+--` and the `sigma16` image `0--+`) are closed by two kernel-checked cores. -/
theorem isRupert_cls3w {x : Fin 7 → ℝ³} (T : Type16 x) (h : Cls16ClosedW x) : IsRupert (univ.image x) := by
  simp only [Cls16ClosedW] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact (not_cls16Dead T (cls16Dead_of_vec h (by norm_num) (by norm_num))).elim
  · exact (not_cls16Dead T (cls16Dead_of_vec h (by norm_num) (by norm_num))).elim
  · exact (not_cls16Dead T (cls16Dead_of_vec h (by norm_num) (by norm_num))).elim
  · exact (not_cls16Dead T (cls16Dead_of_vec h (by norm_num) (by norm_num))).elim
  · exact (not_cls16Dead T (cls16Dead_of_vec h (by norm_num) (by norm_num))).elim
  · exact (not_cls16Dead T (cls16Dead_of_vec h (by norm_num) (by norm_num))).elim
  · exact (not_cls16Dead T (cls16Dead_of_vec h (by norm_num) (by norm_num))).elim
  · exact (not_cls16Dead T (cls16Dead_of_vec h (by norm_num) (by norm_num))).elim
  · exact (not_cls16Dead T (cls16Dead_of_vec h (by norm_num) (by norm_num))).elim
  · exact (not_cls16Dead T (cls16Dead_of_vec h (by norm_num) (by norm_num))).elim
  · exact (not_cls16Dead T (cls16Dead_of_vec h (by norm_num) (by norm_num))).elim
  · exact (not_cls16Dead T (cls16Dead_of_vec h (by norm_num) (by norm_num))).elim
  · exact (not_cls16Dead T (cls16Dead_of_vec h (by norm_num) (by norm_num))).elim
  · exact rupert_wall Minimality.H16K.SAT.rupert_of_coreZPMP T h
  · exact rupert_wall Minimality.H16K.SAT.rupert_of_coreZPMM T h
  · exact rupert_wall_sigma Minimality.H16K.SAT.rupert_of_coreZPMM T h (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **Type 16, the closed classes and the closed walls are Rupert.** -/
theorem isRupert_closed {x : Fin 7 → ℝ³} (T : Type16 x) (h : Cls16Closed x ∨ Cls16ClosedW x) :
    IsRupert (univ.image x) := by
  rcases h with h | h
  · exact isRupert_cls3 T h
  · exact isRupert_cls3w T h

end Minimality.H16.SAT
