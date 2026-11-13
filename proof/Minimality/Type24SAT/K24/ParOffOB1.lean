module

public import Minimality.Type24SAT.K24.ParR2
public import Minimality.Type24SAT.K24.ParBox
public import Minimality.Type24SAT.K24.FinalPppppNotP
public import Minimality.Type24SAT.K24.FinalPppppPq
public import Minimality.Type24SAT.K24.FinalPmpppNotP
public import Minimality.Type24SAT.K24.FinalPmpppPq
public import Minimality.Type24SAT.K24.FinalMpmpmNotP
public import Minimality.Type24SAT.K24.FinalMpmpmPq
public import Minimality.Type24SAT.K24.FinalMpmmmNotP
public import Minimality.Type24SAT.K24.FinalMpmmmPq

@[expose] public section

/-!
# Type 24 off the obtuse corner, the four split classes with the parallel-pair stratum

The SAT closures `isRupert_offOB1_<cls>_notP` (`D` not a parallelogram) and `isRupert_offOB1_<cls>_Pq`
(`D` a parallelogram, neither `E ∥ G` nor `C ∥ I`) leave the stratum `D` a parallelogram with `E ∥ G` or `C ∥ I`.
That stratum is `Minimality.T24.Par.isRupert_par` (class- and `OB1`-free), including the box corner `ParBox`
(`isRupert_parBox`): `D` a rectangle with `E, G, C, I` all perpendicular to it (`X 2 = 0`, `X 6 = |e|²` in the
notation of `ParR2`).  No hypothesis remains.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.Par
open Minimality Minimality.H21 Minimality.T24.SAT

variable {x : Fin 7 → ℝ³}

open Minimality.H24K.SAT in
/-- The `σ`-image of the box corner (the exclusion of `isRupert_parCI`) has `E ∥ G`: `E:23 = 0`
(`box_ci` in the `σ` frame). -/
theorem eg_of_ciBox (F : S0xFac 9 s0x_S24 x) (hP : x 3 = x 4 + x 5 - x 0)
    (hC : ⟪F.N 2, x 3 - x 6⟫ = 0)
    (hB : ⟪x 4 - x 0, x 6 - x 3⟫ = 0 ∧ ⟪x 4 - x 0, x 2 - x 0⟫ = 0 ∧ 0 ≤ ⟪x 2 - x 0, x 6 - x 3⟫ ∧
      ⟪x 6 - x 0, x 5 - x 0⟫ = 0 ∧ ⟪x 2 - x 0, x 5 - x 0⟫ = ⟪x 5 - x 0, x 5 - x 0⟫ ∧
      ⟪x 3 - x 2, x 6 - x 0⟫ ≤ 0) :
    ⟪F.N 4, x 2 - x 3⟫ = 0 := by
  obtain ⟨hw, hs, -, h2, h6, -⟩ := hB
  exact box_ci (facSig F) (x := x ∘ wallSig) (by show x 3 = x 5 + x 4 - x 0; rw [hP]; abel)
    (by show ⟪F.N 2, x 6 - x 3⟫ = 0; rw [show x 6 - x 3 = -(x 3 - x 6) by abel, inner_neg_right, hC, neg_zero])
    hw hs h2 h6

/-- **The parallel-pair stratum of type 24**: `D` a parallelogram (`KD0435 = KD0534 = 0`) and `E ∥ G` (`E:23 = 0`)
or `C ∥ I` (`C:36 = 0`), outside the box corner: Rupert.  No class, `OB1` or acuteness hypothesis. -/
theorem isRupert_par (F : S0xFac 9 s0x_S24 x)
    (hD : det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0)
    (hPar : ⟪F.N 4, x 2 - x 3⟫ = 0 ∨ ⟪F.N 2, x 3 - x 6⟫ = 0) :
    IsRupert (univ.image x) := by
  by_cases hEG : ⟪F.N 4, x 2 - x 3⟫ = 0
  · by_cases hB : ParBox x
    · exact isRupert_parBox F (par_of_KD F hD) hEG hB
    · exact isRupert_parEG F hD hEG hB
  have hCI : ⟪F.N 2, x 3 - x 6⟫ = 0 := hPar.resolve_left hEG
  exact isRupert_parCI F hD hCI fun hR => hEG (eg_of_ciBox F (par_of_KD F hD) hCI hR)

end Minimality.T24.Par

open Minimality Minimality.H21

/-- **Type 24, class ppppp off the obtuse corner `OB1`**, all cases (`D` not a parallelogram; a parallelogram without,
and with, a parallel facet pair) -/
theorem Minimality.T24.isRupert_offOB1_ppppp {x : Fin 7 → EuclideanSpace ℝ (Fin 3)}
    (F : S0xFac 9 Minimality.T24.SAT.s0x_S24 x)
    (hcls : (det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0 ∧ 0 < det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) ∧ 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1) ∧ 0 < det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) ∧ 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1) ∧ 0 < det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2)) ∨
      (0 < det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) ∧ det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) < 0 ∧ det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1) < 0 ∧ det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) < 0 ∧ det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1) < 0 ∧ det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2) < 0))
    (hO : ¬ Minimality.H24K.SAT.OB1 x) :
    IsRupert (Finset.univ.image x) := by
  by_cases hD : Minimality.det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ Minimality.det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0
  · by_cases hEG : inner ℝ (F.N 4) (x 2 - x 3) = 0 ∧ inner ℝ (F.N 4) (x 2 - x 5) = 0
    · exact Minimality.T24.Par.isRupert_par F hD (Or.inl hEG.1)
    by_cases hCI : inner ℝ (F.N 2) (x 3 - x 6) = 0 ∧ inner ℝ (F.N 2) (x 4 - x 6) = 0
    · exact Minimality.T24.Par.isRupert_par F hD (Or.inr hCI.1)
    exact Minimality.T24.isRupert_offOB1_ppppp_Pq F hcls hO hD hEG hCI
  · exact Minimality.T24.isRupert_offOB1_ppppp_notP F hcls hO hD

/-- **Type 24, class pmppp off the obtuse corner `OB1`**, all cases (`D` not a parallelogram; a parallelogram without,
and with, a parallel facet pair) -/
theorem Minimality.T24.isRupert_offOB1_pmppp {x : Fin 7 → EuclideanSpace ℝ (Fin 3)}
    (F : S0xFac 9 Minimality.T24.SAT.s0x_S24 x)
    (hcls : (det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0 ∧ 0 < det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) ∧ det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1) < 0 ∧ 0 < det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) ∧ 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1) ∧ 0 < det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2)) ∨
      (0 < det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) ∧ det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) < 0 ∧ 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1) ∧ det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) < 0 ∧ det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1) < 0 ∧ det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2) < 0))
    (hO : ¬ Minimality.H24K.SAT.OB1 x) :
    IsRupert (Finset.univ.image x) := by
  by_cases hD : Minimality.det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ Minimality.det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0
  · by_cases hEG : inner ℝ (F.N 4) (x 2 - x 3) = 0 ∧ inner ℝ (F.N 4) (x 2 - x 5) = 0
    · exact Minimality.T24.Par.isRupert_par F hD (Or.inl hEG.1)
    by_cases hCI : inner ℝ (F.N 2) (x 3 - x 6) = 0 ∧ inner ℝ (F.N 2) (x 4 - x 6) = 0
    · exact Minimality.T24.Par.isRupert_par F hD (Or.inr hCI.1)
    exact Minimality.T24.isRupert_offOB1_pmppp_Pq F hcls hO hD hEG hCI
  · exact Minimality.T24.isRupert_offOB1_pmppp_notP F hcls hO hD

/-- **Type 24, class mpmpm off the obtuse corner `OB1`**, all cases (`D` not a parallelogram; a parallelogram without,
and with, a parallel facet pair) -/
theorem Minimality.T24.isRupert_offOB1_mpmpm {x : Fin 7 → EuclideanSpace ℝ (Fin 3)}
    (F : S0xFac 9 Minimality.T24.SAT.s0x_S24 x)
    (hcls : (det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0 ∧ det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) < 0 ∧ 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1) ∧ det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) < 0 ∧ 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1) ∧ det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2) < 0) ∨
      (0 < det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) ∧ 0 < det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) ∧ det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1) < 0 ∧ 0 < det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) ∧ det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1) < 0 ∧ 0 < det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2)))
    (hO : ¬ Minimality.H24K.SAT.OB1 x) :
    IsRupert (Finset.univ.image x) := by
  by_cases hD : Minimality.det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ Minimality.det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0
  · by_cases hEG : inner ℝ (F.N 4) (x 2 - x 3) = 0 ∧ inner ℝ (F.N 4) (x 2 - x 5) = 0
    · exact Minimality.T24.Par.isRupert_par F hD (Or.inl hEG.1)
    by_cases hCI : inner ℝ (F.N 2) (x 3 - x 6) = 0 ∧ inner ℝ (F.N 2) (x 4 - x 6) = 0
    · exact Minimality.T24.Par.isRupert_par F hD (Or.inr hCI.1)
    exact Minimality.T24.isRupert_offOB1_mpmpm_Pq F hcls hO hD hEG hCI
  · exact Minimality.T24.isRupert_offOB1_mpmpm_notP F hcls hO hD

/-- **Type 24, class mpmmm off the obtuse corner `OB1`**, all cases (`D` not a parallelogram; a parallelogram without,
and with, a parallel facet pair) -/
theorem Minimality.T24.isRupert_offOB1_mpmmm {x : Fin 7 → EuclideanSpace ℝ (Fin 3)}
    (F : S0xFac 9 Minimality.T24.SAT.s0x_S24 x)
    (hcls : (det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0 ∧ det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) < 0 ∧ 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1) ∧ det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) < 0 ∧ det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1) < 0 ∧ det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2) < 0) ∨
      (0 < det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) ∧ 0 < det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) ∧ det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1) < 0 ∧ 0 < det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) ∧ 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1) ∧ 0 < det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2)))
    (hO : ¬ Minimality.H24K.SAT.OB1 x) :
    IsRupert (Finset.univ.image x) := by
  by_cases hD : Minimality.det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ Minimality.det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0
  · by_cases hEG : inner ℝ (F.N 4) (x 2 - x 3) = 0 ∧ inner ℝ (F.N 4) (x 2 - x 5) = 0
    · exact Minimality.T24.Par.isRupert_par F hD (Or.inl hEG.1)
    by_cases hCI : inner ℝ (F.N 2) (x 3 - x 6) = 0 ∧ inner ℝ (F.N 2) (x 4 - x 6) = 0
    · exact Minimality.T24.Par.isRupert_par F hD (Or.inr hCI.1)
    exact Minimality.T24.isRupert_offOB1_mpmmm_Pq F hcls hO hD hEG hCI
  · exact Minimality.T24.isRupert_offOB1_mpmmm_notP F hcls hO hD
