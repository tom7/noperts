module

public import Minimality.Type16SAT.PLSlide16
public import Minimality.Type16SAT.Cls16WC
public import Minimality.Type16SAT.LinkPMZMU
public import Minimality.Type16SAT.LinkPMZMZ

@[expose] public section

/-!
# Type 16: the boundary `+-0-` (between `+-+-` and `+---`) and its `sigma16` image `--0-`

Off `PL` two case cores (`PMZMU`: `CaseT16`, `PMZMZ`: a shape entry of `Z` nonzero); on `PL` the existing Slide leaf
`isRupert_PL16` (it needs only `C [0134] < 0`).  No residue.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.H29.SAT

namespace Minimality.H16.SAT

open Minimality.H16K.SAT

/-- A wall vector with `C [0134] < 0` from its two case cores and `isRupert_PL16`. -/
theorem isRupert_vecPL_of {e1 e2 e3 e4 : ℝ} (hT : Core16TW e1 e2 e3 e4) (hZ : Core16ZW e1 e2 e3 e4)
    {x : Fin 7 → ℝ³} (T : Type16 x) (h : Vec16 e1 e2 e3 e4 x) (h2 : C16 x * br16 x 0 1 3 4 < 0) :
    IsRupert (univ.image x) := by
  have F := Minimality.H16A.h16g_fac T
  have hne : C16 x ≠ 0 := T.det_ne
  by_cases hA : CaseT16 x
  · exact rupert_of_core_bothTW hT F hne h hA
  by_cases hz : ZShape16 x F
  · exact isRupert_PL16 T F h2 hA hz
  · exact rupert_of_core_bothZW hZ F hne h hz

/-- **Type 16, the boundary `+-0-` and its `sigma16` image `--0-`.** -/
theorem isRupert_pmzm {x : Fin 7 → ℝ³} (T : Type16 x)
    (h : Vec16 1 (-1) 0 (-1) x ∨ Vec16 (-1) (-1) 0 (-1) x) : IsRupert (univ.image x) := by
  rcases h with h | h
  · refine isRupert_vecPL_of rupert_of_corePMZMU rupert_of_corePMZMZ T h ?_
    have := h.2.1
    simp only [SgnP] at this
    norm_num at this
    linarith
  · have hs : Vec16 1 (-1) 0 (-1) (x ∘ sigma16) := vec16_sigma h
    have h4 := h.2.2.2
    simp only [SgnP] at h4
    norm_num at h4
    have := isRupert_vecPL_of rupert_of_corePMZMU rupert_of_corePMZMZ T.sigma hs
      (by rw [C16_sigma, b2_sigma, neg_mul_neg]; linarith)
    rwa [Minimality.image_sigma16] at this

end Minimality.H16.SAT
