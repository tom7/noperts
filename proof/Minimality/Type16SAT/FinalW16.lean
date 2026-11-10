module

public import Minimality.Type16SAT.PLSlideW16
public import Minimality.Type16SAT.Cls16WC
public import Minimality.Type16SAT.LinkPZMPU
public import Minimality.Type16SAT.LinkPZMPZ
public import Minimality.Type16SAT.LinkMZMPU
public import Minimality.Type16SAT.LinkMZMPZ

@[expose] public section

/-!
# Type 16: the walls `+0-+`, `-0-+` and their `sigma16` images `-+-0`, `++-0`

On the wall `C [0134] = 0` (`r = 1` on `Z`), with `[0126]` of either sign (`+0-+`: `a < 1`, `-0-+`: `a > 1`):
* `CaseT16 y` (`x 1 - x 6` not orthogonal to both `x 0 - x 3`, `x 0 - x 6`): the cores `PZMPU`, `MZMPU` (`Core16TW`);
* some entry of `Z` nonzero: the cores `PZMPZ`, `MZMPZ` (`Core16ZW`);
* else `PL` with `r = 1`: the Slide Lemma (`NF16.isRupert_PL_slide_le`) when `c = ⟪x 0 - x 3, x 6 - x 3⟫ ≠ 0`.
The residue is `PL`, `r = 1`, `c = 0` (both slab ends touched; `1356` a rectangle perpendicular to `036`, `145`, `0235`, `146`,
with `036 ∥ 145` and `0235 ∥ 146`).  The wall `++-0` is the `sigma16` image of `-0-+`, and `-+-0` that of `+0-+`.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.H29.SAT

namespace Minimality.NF16

variable {x : Fin 7 → ℝ³}

/-- **`r = 1` on the wall.**  On `g = d = q = 1`, `C [0134] = (r - 1) D²`, so a zero `C * [0134]` gives `r = 1`. -/
theorem r_eq_one (N : NF16 x) (hg : N.g = 1) (hd : N.d = 1) (hq : N.q = 1)
    (h : H16.SAT.C16 x * H16.SAT.br16 x 0 1 3 4 = 0) : N.r = 1 := by
  have e : H16.SAT.C16 x * H16.SAT.br16 x 0 1 3 4 = (N.r - 1) * det3 N.E₁ N.E₂ N.E₃ ^ 2 := by
    simp only [H16.SAT.C16, H16.SAT.br16, N.x0, N.x1, N.x3, N.x4, N.x5, N.x6, nfP_sub,
      det3_nfV, det3c, hg, hd, hq]
    ring
  rw [e] at h
  have hD2 : det3 N.E₁ N.E₂ N.E₃ ^ 2 ≠ 0 := pow_ne_zero 2 N.hD
  have := (mul_eq_zero.1 h).resolve_right hD2
  linarith

end Minimality.NF16

namespace Minimality.H16.SAT

open Minimality.H16K.SAT

/-- **A wall `e1 0 e3 e4` from its two case cores and the Slide Lemma**, off the residue `⟪x 0 - x 3, x 6 - x 3⟫ = 0`. -/
theorem isRupert_wall0_of {e1 e3 e4 : ℝ} (hT : Core16TW e1 0 e3 e4) (hZ : Core16ZW e1 0 e3 e4)
    {x : Fin 7 → ℝ³} (T : Type16 x) (h : Vec16 e1 0 e3 e4 x) (hc : ⟪x 0 - x 3, x 6 - x 3⟫ ≠ 0) :
    IsRupert (univ.image x) := by
  have F := Minimality.H16A.h16g_fac T
  have hne : C16 x ≠ 0 := T.det_ne
  by_cases hA : CaseT16 x
  · exact rupert_of_core_bothTW hT F hne h hA
  by_cases hz : ZShape16 x F
  · have N := T.toNF
    obtain ⟨hg, hd, hq⟩ := N.zshape_nf F hz
    simp only [CaseT16, not_or, not_not] at hA
    have h2 : C16 x * br16 x 0 1 3 4 = 0 := by
      have := h.2.1
      simpa [SgnP] using this
    have hr := N.r_eq_one hg hd hq h2
    exact N.isRupert_PL_slide_le hg hd hq hA.1 hA.2 hr.le (Or.inr hc)
  · exact rupert_of_core_bothZW hZ F hne h hz

/-- The `sigma16` image of `isRupert_wall0_of`: the wall `(-e1) e4 e3 0`. -/
theorem isRupert_wall0_sigma_of {e1 e3 e4 : ℝ} (hT : Core16TW e1 0 e3 e4) (hZ : Core16ZW e1 0 e3 e4)
    {x : Fin 7 → ℝ³} (T : Type16 x) (h : Vec16 (-e1) e4 e3 0 x)
    (hc : ⟪(x ∘ sigma16) 0 - (x ∘ sigma16) 3, (x ∘ sigma16) 6 - (x ∘ sigma16) 3⟫ ≠ 0) :
    IsRupert (univ.image x) := by
  have := isRupert_wall0_of hT hZ T.sigma (vec16_sigma h) hc
  rwa [Minimality.image_sigma16] at this

/-- The four wall vectors `+0-+`, `-0-+` (`C [0134] = 0`) and their `sigma16` images `-+-0`, `++-0` (`C [2346] = 0`). -/
def Cls16WallR (x : Fin 7 → ℝ³) : Prop :=
  Vec16 1 0 (-1) 1 x ∨ Vec16 (-1) 0 (-1) 1 x ∨ Vec16 (-1) 1 (-1) 0 x ∨ Vec16 1 1 (-1) 0 x

/-- The residue of the walls: `⟪x 0 - x 3, x 6 - x 3⟫ = 0` on `+0-+`, `-0-+`, the same for `x ∘ sigma16` on `-+-0`, `++-0`. -/
def WallRes16 (x : Fin 7 → ℝ³) : Prop :=
  ((Vec16 1 0 (-1) 1 x ∨ Vec16 (-1) 0 (-1) 1 x) ∧ ⟪x 0 - x 3, x 6 - x 3⟫ = 0) ∨
  ((Vec16 (-1) 1 (-1) 0 x ∨ Vec16 1 1 (-1) 0 x) ∧
    ⟪(x ∘ sigma16) 0 - (x ∘ sigma16) 3, (x ∘ sigma16) 6 - (x ∘ sigma16) 3⟫ = 0)

/-- **Type 16, the walls `+0-+`, `-0-+`, `-+-0`, `++-0` off the residue `WallRes16`**: kernel-checked cores (four) and the
Slide Lemma. -/
theorem isRupert_wallR {x : Fin 7 → ℝ³} (T : Type16 x) (h : Cls16WallR x) (hr : ¬ WallRes16 x) :
    IsRupert (univ.image x) := by
  simp only [WallRes16, not_or, not_and] at hr
  obtain ⟨hr1, hr2⟩ := hr
  rcases h with h | h | h | h
  · exact isRupert_wall0_of rupert_of_corePZMPU rupert_of_corePZMPZ T h (hr1 (Or.inl h))
  · exact isRupert_wall0_of rupert_of_coreMZMPU rupert_of_coreMZMPZ T h (hr1 (Or.inr h))
  · exact isRupert_wall0_sigma_of rupert_of_corePZMPU rupert_of_corePZMPZ T h
      (hr2 (Or.inl h))
  · exact isRupert_wall0_sigma_of rupert_of_coreMZMPU rupert_of_coreMZMPZ T (by rw [neg_neg]; exact h)
      (hr2 (Or.inr h))

end Minimality.H16.SAT
