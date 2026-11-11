module

public import Minimality.Type16SAT.Last16
public import Minimality.Type16SAT.LinkZZMPU
public import Minimality.Type16SAT.LinkZZMPZ
public import Minimality.Type16SAT.LinkZZMMU
public import Minimality.Type16SAT.LinkZZMMZ
public import Minimality.Type16SAT.LinkZMPMU
public import Minimality.Type16SAT.LinkZMMMU
public import Minimality.Type16SAT.LinkZZMZU
public import Minimality.Type16SAT.LinkPZMZT
public import Minimality.Type16SAT.LinkMZMZT
public import Minimality.Type16SAT.LinkZMPMZZ
public import Minimality.Type16SAT.LinkZMMMZZ
public import Minimality.Type16SAT.LinkZZMZZZ
public import Minimality.Type16SAT.LinkPZMZZZ
public import Minimality.Type16SAT.LinkZMZMU
public import Minimality.Type16SAT.LinkZMZMZZ

@[expose] public section

/-!
# Type 16: the last sign vectors `0-+-`, `0---`, `0-0-`, `00-0`, `+0-0`, `-0-0`, and `00-+`, `00--`, `0+-0`, `0--0` with their residue

Eleven kernel-checked cores and the hand modules `Last16`, `ResA16`:
* `0-+-`, `0---`, `0-0-`, `00-0` (fixed by `sigma16`): `CaseT16` cores `ZMPMU`, `ZMMMU`, `ZMZMU`, `ZZMZU` (`Core16TW`), cores off
  `Z` and off its `sigma16` image `ZMPMZZ`, `ZMMMZZ`, `ZMZMZZ`, `ZZMZZZ` (`Core16ZZW`), and the leaves on `PL` (`isRupert_fix_of`).
* `+0-0`, `-0-0`: the cores on `Z` with `CaseT16` `PZMZT`, `MZMZT` (`Core16ZTW`), the core `PZMZZZ` (`Core16ZZW`) and the
  leaves on `PL` (`isRupert_pzmz_of`, `isRupert_mzmz_of`).
* `00-+`, `00--` and images (`Cls16Z2`): the cores `ZZMPU`, `ZZMMU`, `ZZMPZ`, `ZZMMZ` and `isRupert_wall0_res` (the residue `a = r = 1`,
  `c = 0` by `NF16.isRupert_PL_res1`).
-/

set_option autoImplicit false
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.H29.SAT

namespace Minimality.H16.SAT

open Minimality.H16K.SAT

/-- The four vectors with two zero brackets `[0126] = [0134] = 0` (`00-+`, `00--`) or `[0126] = [2346] = 0` (`0+-0`,
`0--0`, the `sigma16` images). -/
def Cls16Z2 (x : Fin 7 → ℝ³) : Prop :=
  Vec16 0 0 (-1) 1 x ∨ Vec16 0 0 (-1) (-1) x ∨ Vec16 0 1 (-1) 0 x ∨ Vec16 0 (-1) (-1) 0 x

/-- **Type 16, the vectors `00-+`, `00--`, `0+-0`, `0--0` with their residue.** -/
theorem isRupert_z2_all {x : Fin 7 → ℝ³} (T : Type16 x) (h : Cls16Z2 x) : IsRupert (univ.image x) := by
  rcases h with h | h | h | h
  · exact isRupert_wall0_res rupert_of_coreZZMPU rupert_of_coreZZMPZ T h
  · exact isRupert_wall0_res rupert_of_coreZZMMU rupert_of_coreZZMMZ T h
  · have := isRupert_wall0_res rupert_of_coreZZMPU rupert_of_coreZZMPZ T.sigma
      (vec16_sigma (by rw [neg_zero]; exact h))
    rwa [Minimality.image_sigma16] at this
  · have := isRupert_wall0_res rupert_of_coreZZMMU rupert_of_coreZZMMZ T.sigma
      (vec16_sigma (by rw [neg_zero]; exact h))
    rwa [Minimality.image_sigma16] at this

/-- **Type 16, the vectors `0-+-`, `0---`, `0-0-`, `00-0`, `+0-0`, `-0-0`.** -/
theorem isRupert_last {x : Fin 7 → ℝ³} (T : Type16 x) (h : Cls16Last x) : IsRupert (univ.image x) := by
  rcases h with h | h | h | h | h | h
  · exact isRupert_fix_of rupert_of_coreZMPMU rupert_of_coreZMPMZZ
      (fun T F h hA hz => isRupert_PL_zm T F h hA hz) T h
  · exact isRupert_fix_of rupert_of_coreZMMMU rupert_of_coreZMMMZZ
      (fun T F h hA hz => isRupert_PL_zm T F h hA hz) T h
  · exact isRupert_fix_of rupert_of_coreZMZMU rupert_of_coreZMZMZZ
      (fun T F h hA hz => isRupert_PL_zm T F h hA hz) T h
  · exact isRupert_fix_of rupert_of_coreZZMZU rupert_of_coreZZMZZZ
      (fun T F h hA hz => isRupert_PL_r1 T F h hA hz) T h
  · exact isRupert_pzmz_of rupert_of_corePZMZT rupert_of_coreMZMZT rupert_of_corePZMZZZ T h
  · exact isRupert_mzmz_of rupert_of_corePZMZT rupert_of_coreMZMZT rupert_of_corePZMZZZ T h

end Minimality.H16.SAT
