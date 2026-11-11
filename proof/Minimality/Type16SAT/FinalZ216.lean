module

public import Minimality.Type16SAT.FinalW16
public import Minimality.Type16SAT.LinkZZMPU
public import Minimality.Type16SAT.LinkZZMPZ
public import Minimality.Type16SAT.LinkZZMMU
public import Minimality.Type16SAT.LinkZZMMZ

@[expose] public section

/-!
# Type 16: the vectors `00-+`, `00--` and their `sigma16` images `0+-0`, `0--0` (two zero brackets)

The class vector is the sign vector of `C * ([0126], [0134], [1234], [2346])`.  On `Z` (`g = d = q = 1`) the zero of
`[0126]` is `a = 1`, and the zero of `[0134]` is `r = 1`; then `[1234] = -b p < 0` is automatic, and `[2346] = b p - 1`
has the sign `+` (`00-+`, `b p > 1`) or `-` (`00--`, `b p < 1`).  These are the walls `1 0 (-1) e4` of `FinalW16` with `e1 = 0`:
* `CaseT16 y`: the cores `ZZMPU`, `ZZMMU` (`Core16TW 0 0 (-1) (±1)`);
* some entry of `Z` nonzero: the cores `ZZMPZ`, `ZZMMZ` (`Core16ZW 0 0 (-1) (±1)`);
* else `PL` with `r = 1`: the Slide Lemma (`NF16.isRupert_PL_slide_le`) when `c = ⟪x 0 - x 3, x 6 - x 3⟫ ≠ 0`.
The Slide Lemma does not use `a`.  The residue is `PL`, `a = 1`, `r = 1`, `c = 0`: the box corner of the walls, with the
extra relation `a = 1` (`0 2 ∥ 3 5`).  `0+-0` and `0--0` are the `sigma16` images of `00-+` and `00--`.
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

/-- The residue: `⟪x 0 - x 3, x 6 - x 3⟫ = 0` on `00-+`, `00--`, the same for `x ∘ sigma16` on `0+-0`, `0--0`. -/
def Z2Res16 (x : Fin 7 → ℝ³) : Prop :=
  ((Vec16 0 0 (-1) 1 x ∨ Vec16 0 0 (-1) (-1) x) ∧ ⟪x 0 - x 3, x 6 - x 3⟫ = 0) ∨
  ((Vec16 0 1 (-1) 0 x ∨ Vec16 0 (-1) (-1) 0 x) ∧
    ⟪(x ∘ sigma16) 0 - (x ∘ sigma16) 3, (x ∘ sigma16) 6 - (x ∘ sigma16) 3⟫ = 0)

/-- **Type 16, the vectors `00-+`, `00--`, `0+-0`, `0--0` off the residue `Z2Res16`**: four kernel-checked cores and the
Slide Lemma. -/
theorem isRupert_z2 {x : Fin 7 → ℝ³} (T : Type16 x) (h : Cls16Z2 x) (hr : ¬ Z2Res16 x) :
    IsRupert (univ.image x) := by
  simp only [Z2Res16, not_or, not_and] at hr
  obtain ⟨hr1, hr2⟩ := hr
  rcases h with h | h | h | h
  · exact isRupert_wall0_of rupert_of_coreZZMPU rupert_of_coreZZMPZ T h (hr1 (Or.inl h))
  · exact isRupert_wall0_of rupert_of_coreZZMMU rupert_of_coreZZMMZ T h (hr1 (Or.inr h))
  · exact isRupert_wall0_sigma_of rupert_of_coreZZMPU rupert_of_coreZZMPZ T (by rw [neg_zero]; exact h)
      (hr2 (Or.inl h))
  · exact isRupert_wall0_sigma_of rupert_of_coreZZMMU rupert_of_coreZZMMZ T (by rw [neg_zero]; exact h)
      (hr2 (Or.inr h))

end Minimality.H16.SAT
