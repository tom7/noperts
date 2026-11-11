module

public import Minimality.Type16SAT.ResA16
public import Minimality.Type16SAT.Cls16ZZ
public import Minimality.Type16SAT.FinalW16Y

@[expose] public section

/-!
# Type 16: the last sign vectors, from their core theorems

The class vector is the sign vector of `C * ([0126], [0134], [1234], [2346])`.  The vectors here:
* `0-+-`, `0---`, `0-0-`, `00-0`: fixed by `sigma16` (`s ↦ (-s₁, s₄, s₃, s₂)`).  The encoder puts the case "off `Z`" on the
  `sigma16` image of `Z` (its models have all 18 image entries zero), so the split is: `CaseT16 x` (core `Core16TW`);
  on `Z` (`PL` then); the same two for `x ∘ sigma16` (same vector); else off `Z` and off its image (core `Core16ZZW`).
  On `PL`: `0-+-`, `0---`, `0-0-` have `r < 1` (`isRupert_PL16`); `00-0` has `r = 1`, `a = 1`: the Slide Lemma if
  `c = ⟪x 0 - x 3, x 6 - x 3⟫ ≠ 0`, else the residue leaves at `a = 1` (`NF16.isRupert_PL_res1`).
  `isRupert_fix_of`.
* `+0-0` and its image `-0-0`: on `Z` with `CaseT16` (core `Core16ZTW`, for both vectors), on `Z` without it (`PL`,
  `r = 1`, `a ≠ 1`: the Slide Lemma or `NF16.isRupert_PL_res`), the same for `x ∘ sigma16`, else off `Z` and off its
  image (core `Core16ZZW`).  `isRupert_pzmz_of`.
* `00-+`, `00--` and images `0+-0`, `0--0` with the residue: on `PL` with `a = 1`, `r = 1` (`NF16.isRupert_PL_z2`).
-/

set_option autoImplicit false
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.H29.SAT

namespace Minimality.NF16

variable {x : Fin 7 → ℝ³}

/-- `a = 1` from `C [0126] = 0` (`= (1 - a) D²` on `g = d = 1`). -/
theorem a_eq_one (N : NF16 x) (hg : N.g = 1) (hd : N.d = 1)
    (h : H16.SAT.C16 x * H16.SAT.br16 x 0 1 2 6 = 0) : N.a = 1 := by
  have e : H16.SAT.C16 x * H16.SAT.br16 x 0 1 2 6 = (1 - N.a) * det3 N.E₁ N.E₂ N.E₃ ^ 2 := by
    simp only [H16.SAT.C16, H16.SAT.br16, N.x0, N.x1, N.x2, N.x3, N.x5, N.x6, nfP_sub, det3_nfV, det3c, hg, hd]
    ring
  rw [e] at h
  have := (mul_eq_zero.1 h).resolve_right (pow_ne_zero 2 N.hD)
  linarith

/-- **`PL` with `r = 1` and `a = 1`**: the Slide Lemma if `c ≠ 0`, else the residue leaves at `a = 1`. -/
theorem isRupert_PL_z2 (N : NF16 x) (F : H21.S0xFac 8 Minimality.V2.fIdx x)
    (hg : N.g = 1) (hd : N.d = 1) (hq : N.q = 1)
    (h1 : ⟪x 0 - x 3, x 1 - x 6⟫ = 0) (h2 : ⟪x 0 - x 6, x 1 - x 6⟫ = 0) (hr : N.r = 1) (ha : N.a = 1) :
    IsRupert (univ.image x) := by
  by_cases hc : ⟪x 0 - x 3, x 6 - x 3⟫ = 0
  · exact N.isRupert_PL_res1 F hg hd hq h1 h2 hr hc ha
  · exact N.isRupert_PL_slide_le hg hd hq h1 h2 hr.le (Or.inr hc)

end Minimality.NF16

namespace Minimality.H16.SAT

/-- The six vectors `0-+-`, `0---`, `0-0-`, `00-0`, `+0-0`, `-0-0`. -/
def Cls16Last (x : Fin 7 → ℝ³) : Prop :=
  Vec16 0 (-1) 1 (-1) x ∨ Vec16 0 (-1) (-1) (-1) x ∨ Vec16 0 (-1) 0 (-1) x ∨ Vec16 0 0 (-1) 0 x ∨
    Vec16 1 0 (-1) 0 x ∨ Vec16 (-1) 0 (-1) 0 x

/-- On `Z` without `CaseT16`, for a vector with `C [0134] = 0`: `PL` with `r = 1`; the Slide Lemma or the residue
leaves (`a ≠ 1` if `C [0126] ≠ 0`, `a = 1` otherwise). -/
theorem isRupert_PL_r1 {e1 e3 e4 : ℝ} {x : Fin 7 → ℝ³} (T : Type16 x) (F : S0xFac 8 Minimality.V2.fIdx x)
    (h : Vec16 e1 0 e3 e4 x) (hA : ¬ CaseT16 x) (hz : ZShape16 x F) : IsRupert (univ.image x) := by
  have N := T.toNF
  obtain ⟨hg, hd, hq⟩ := N.zshape_nf F hz
  simp only [CaseT16, not_or, not_not] at hA
  have h2 : C16 x * br16 x 0 1 3 4 = 0 := by
    have := h.2.1
    simpa [SgnP] using this
  have hr := N.r_eq_one hg hd hq h2
  by_cases h0 : C16 x * br16 x 0 1 2 6 = 0
  · exact N.isRupert_PL_z2 F hg hd hq hA.1 hA.2 hr (N.a_eq_one hg hd h0)
  · by_cases hc : ⟪x 0 - x 3, x 6 - x 3⟫ = 0
    · exact N.isRupert_PL_res F hg hd hq hA.1 hA.2 hr hc (N.a_ne_one hg hd h0)
    · exact N.isRupert_PL_slide_le hg hd hq hA.1 hA.2 hr.le (Or.inr hc)

/-- **A wall `e1 0 e3 e4` from a `CaseT16` core and a `¬ ZShape16` core, with no residue** (any `e1`; at `e1 = 0` the
residue `a = 1` is closed by `isRupert_PL_res1`). -/
theorem isRupert_wall0_res {e1 e3 e4 : ℝ} (hT : Core16TW e1 0 e3 e4) (hZ : Core16ZW e1 0 e3 e4)
    {x : Fin 7 → ℝ³} (T : Type16 x) (h : Vec16 e1 0 e3 e4 x) : IsRupert (univ.image x) := by
  have F := Minimality.H16A.h16g_fac T
  have hne : C16 x ≠ 0 := T.det_ne
  by_cases hA : CaseT16 x
  · exact rupert_of_core_bothTW hT F hne h hA
  by_cases hz : ZShape16 x F
  · exact isRupert_PL_r1 T F h hA hz
  · exact rupert_of_core_bothZW hZ F hne h hz

/-- **A `sigma16`-fixed vector `0 e2 e3 e2`** from a `CaseT16` core, a core off `Z` and off its `sigma16` image, and a
leaf on `Z` without `CaseT16`. -/
theorem isRupert_fix_of {e2 e3 : ℝ} (hT : Core16TW 0 e2 e3 e2) (hZZ : Core16ZZW 0 e2 e3 e2)
    (hPL : ∀ {y : Fin 7 → ℝ³} (_ : Type16 y) (F : S0xFac 8 Minimality.V2.fIdx y), Vec16 0 e2 e3 e2 y →
      ¬ CaseT16 y → ZShape16 y F → IsRupert (univ.image y))
    {x : Fin 7 → ℝ³} (T : Type16 x) (h : Vec16 0 e2 e3 e2 x) : IsRupert (univ.image x) := by
  have F := Minimality.H16A.h16g_fac T
  have hne : C16 x ≠ 0 := T.det_ne
  by_cases hA : CaseT16 x
  · exact rupert_of_core_bothTW hT F hne h hA
  by_cases hz : ZShape16 x F
  · exact hPL T F h hA hz
  have hs : Vec16 0 e2 e3 e2 (x ∘ sigma16) := vec16_sigma (by rw [neg_zero]; exact h)
  have hne' : C16 (x ∘ sigma16) ≠ 0 := T.sigma.det_ne
  by_cases hA' : CaseT16 (x ∘ sigma16)
  · have := rupert_of_core_bothTW hT (sigFac F) hne' hs hA'
    rwa [Minimality.image_sigma16] at this
  by_cases hz' : ZShape16 (x ∘ sigma16) (sigFac F)
  · have := hPL T.sigma (sigFac F) hs hA' hz'
    rwa [Minimality.image_sigma16] at this
  · exact rupert_of_core_bothZZW hZZ F hne h hz hz'

/-- **The vector `+0-0`** from the cores on `Z` with `CaseT16` (for `+0-0` and for its image `-0-0`) and the core off
`Z` and off its image. -/
theorem isRupert_pzmz_of (hZT : Core16ZTW 1 0 (-1) 0) (hZTm : Core16ZTW (-1) 0 (-1) 0) (hZZ : Core16ZZW 1 0 (-1) 0)
    {x : Fin 7 → ℝ³} (T : Type16 x) (h : Vec16 1 0 (-1) 0 x) : IsRupert (univ.image x) := by
  have F := Minimality.H16A.h16g_fac T
  have hne : C16 x ≠ 0 := T.det_ne
  by_cases hz : ZShape16 x F
  · by_cases hA : CaseT16 x
    · exact rupert_of_core_bothZTW hZT F hne h hz hA
    · exact isRupert_PL_r1 T F h hA hz
  have hs : Vec16 (-1) 0 (-1) 0 (x ∘ sigma16) := vec16_sigma (by rw [neg_neg]; exact h)
  have hne' : C16 (x ∘ sigma16) ≠ 0 := T.sigma.det_ne
  by_cases hz' : ZShape16 (x ∘ sigma16) (sigFac F)
  · by_cases hA' : CaseT16 (x ∘ sigma16)
    · have := rupert_of_core_bothZTW hZTm (sigFac F) hne' hs hz' hA'
      rwa [Minimality.image_sigma16] at this
    · have := isRupert_PL_r1 T.sigma (sigFac F) hs hA' hz'
      rwa [Minimality.image_sigma16] at this
  · exact rupert_of_core_bothZZW hZZ F hne h hz hz'

/-- `-0-0`, the `sigma16` image of `+0-0`. -/
theorem isRupert_mzmz_of (hZT : Core16ZTW 1 0 (-1) 0) (hZTm : Core16ZTW (-1) 0 (-1) 0) (hZZ : Core16ZZW 1 0 (-1) 0)
    {x : Fin 7 → ℝ³} (T : Type16 x) (h : Vec16 (-1) 0 (-1) 0 x) : IsRupert (univ.image x) := by
  have := isRupert_pzmz_of hZT hZTm hZZ T.sigma (vec16_sigma h)
  rwa [Minimality.image_sigma16] at this

/-- The leaf on `Z` without `CaseT16` for `0-+-`, `0---` and `0-0-` (`C [0134] < 0`: `isRupert_PL16`). -/
theorem isRupert_PL_zm {e3 : ℝ} {y : Fin 7 → ℝ³} (T : Type16 y) (F : S0xFac 8 Minimality.V2.fIdx y)
    (h : Vec16 0 (-1) e3 (-1) y) (hA : ¬ CaseT16 y) (hz : ZShape16 y F) : IsRupert (univ.image y) := by
  have h2 := h.2.1
  simp only [SgnP] at h2
  norm_num at h2
  exact isRupert_PL16 T F (by linarith) hA hz

end Minimality.H16.SAT
