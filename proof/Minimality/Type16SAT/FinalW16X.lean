module

public import Minimality.Type16SAT.FinalW16
public import Minimality.Type16SAT.LinkPZPM
public import Minimality.Type16SAT.LinkMZPM
public import Minimality.Type16SAT.LinkPZMMU
public import Minimality.Type16SAT.LinkPZMMZ
public import Minimality.Type16SAT.LinkMZMMU
public import Minimality.Type16SAT.LinkMZMMZ

@[expose] public section

/-!
# Type 16: the one-zero vectors next to the open classes with the zero at `[0134]` or `[2346]`

* `+0+-`, `-0+-` and their `sigma16` images `--+0`, `+-+0`: one plain wall core each (`Core16W`, `PZPM`, `MZPM`).
* `+0--`, `-0--` and their images `---0`, `+--0`: as the walls of `FinalW16` (`r = 1` on `Z`), two case cores each
  (`PZMMU`/`PZMMZ`, `MZMMU`/`MZMMZ`) and the Slide Lemma at `r = 1`, off the residue `⟪x 0 - x 3, x 6 - x 3⟫ = 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.H29.SAT

namespace Minimality.H16.SAT

open Minimality.H16K.SAT

/-- The eight vectors of this module. -/
def Cls16WallX (x : Fin 7 → ℝ³) : Prop :=
  Vec16 1 0 1 (-1) x ∨ Vec16 (-1) (-1) 1 0 x ∨ Vec16 (-1) 0 1 (-1) x ∨ Vec16 1 (-1) 1 0 x ∨
  Vec16 1 0 (-1) (-1) x ∨ Vec16 (-1) (-1) (-1) 0 x ∨ Vec16 (-1) 0 (-1) (-1) x ∨ Vec16 1 (-1) (-1) 0 x

/-- The residue of `+0--`, `-0--` (`⟪x 0 - x 3, x 6 - x 3⟫ = 0`) and of their images (the same for `x ∘ sigma16`). -/
def WallResX16 (x : Fin 7 → ℝ³) : Prop :=
  ((Vec16 1 0 (-1) (-1) x ∨ Vec16 (-1) 0 (-1) (-1) x) ∧ ⟪x 0 - x 3, x 6 - x 3⟫ = 0) ∨
  ((Vec16 (-1) (-1) (-1) 0 x ∨ Vec16 1 (-1) (-1) 0 x) ∧
    ⟪(x ∘ sigma16) 0 - (x ∘ sigma16) 3, (x ∘ sigma16) 6 - (x ∘ sigma16) 3⟫ = 0)

/-- **Type 16, the eight vectors of `Cls16WallX` off the residue `WallResX16`.** -/
theorem isRupert_wallX {x : Fin 7 → ℝ³} (T : Type16 x) (h : Cls16WallX x) (hr : ¬ WallResX16 x) :
    IsRupert (univ.image x) := by
  simp only [WallResX16, not_or, not_and] at hr
  obtain ⟨hr1, hr2⟩ := hr
  rcases h with h | h | h | h | h | h | h | h
  · exact rupert_wall rupert_of_corePZPM T h
  · exact rupert_wall_sigma rupert_of_corePZPM T h (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact rupert_wall rupert_of_coreMZPM T h
  · exact rupert_wall_sigma rupert_of_coreMZPM T h (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact isRupert_wall0_of rupert_of_corePZMMU rupert_of_corePZMMZ T h (hr1 (Or.inl h))
  · exact isRupert_wall0_sigma_of rupert_of_corePZMMU rupert_of_corePZMMZ T h (hr2 (Or.inl h))
  · exact isRupert_wall0_of rupert_of_coreMZMMU rupert_of_coreMZMMZ T h (hr1 (Or.inr h))
  · exact isRupert_wall0_sigma_of rupert_of_coreMZMMU rupert_of_coreMZMMZ T (by rw [neg_neg]; exact h)
      (hr2 (Or.inr h))

end Minimality.H16.SAT
