module

public import Minimality.Type24Face
public import Minimality.Type24SAT.K24.Wire24Res
public import Minimality.Type24
public import Minimality.Q45

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.NC Minimality.T24.Z0
  Minimality.T24.Adj

namespace Minimality.T24

/-!
# Type 24: Single Named Open Hole (`Hole24`)

Refines the Type-24 branch of `Minimality.lean` by combining:
1. `Minimality.T24.Face.rupert_or_resid24_noFacetCell_noNC_noAdj_noFace` (SAT + no facet cell,
   no Root T0, no Lemma NC, no Adjacency Lemma, no Lemma E2 face pair),
2. `Minimality.isRupert_type24_outside_Cbar` (closes outside `C̄ ∪ Σ_B`, `Type24.lean` / `NOTES` §15), and
3. `Q45.isRupert_q45_half` (closes `Q45-Half` off `Q45Special`, `Q45.lean` / `Q45THEOREM24.md`).

Every remaining open sub-region is exposed as a named disjunct of `Hole24`.
-/

/-- Inside the closed `C̄` region: `ω3, ω4, ω5 > 0` and `Δ24 ≥ 0`
(complement of `not_type24_outside_Cbar_of_isNopert` / `isRupert_type24_outside_Cbar`, `Type24.lean`). -/
def CbarIn (x : Fin 7 → ℝ³) : Prop :=
  0 < Minimality.omega3 x ∧ 0 < Minimality.omega4 x ∧ 0 < Minimality.omega5 x ∧
    0 ≤ Minimality.Delta24 x

/-- Outside `C̄`, the residual `Σ_B` locus: `RegionB24` with no free side crossing
(attacked in `Type24.lean` / `FEWER-FACES-PROOFS.md` §15). -/
def Hole24SigmaB (x : Fin 7 → ℝ³) : Prop :=
  Minimality.RegionB24 x ∧ ¬ (Minimality.S6Free x ∨ Minimality.S2Free x ∨ Minimality.S0Free x)

/-- The `Q45-Half` sign hypothesis (`hsign` of `q45_half_geom` / `isRupert_q45_half` in `Q45.lean`). -/
def Q45HalfPred {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∀ s t : ℝ, 0 < s → 0 < t → 1 < s + t →
    x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0) → Q45.Q45HalfHyp F s t

/-- Special loci of Theorem Q45 inside `C̄ ∩ Resid24` (no `OB1` restriction, since `isRupert_q45_half`
requires only `F` and `Q45HalfPred F`; attacked in `Q45.lean` / `Q45THEOREM24.md`). -/
def Hole24Q45Special (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  CbarIn x ∧ Resid24 x ∧ Q45HalfPred F ∧ Q45.Q45Special F

/-- Region `R`: `C̄ ∩ OB1` outside `Q45-Half` (attacked in `R012.lean`, `R046.lean`,
`CARBON-RESPONSES.md`). Lean leaves already proved for `Hole24R` (not yet wired; the `R`
dispatcher is future work): `R012.q012_LC_plus`, `R012.q012_LC_minus`, `R046.q046_cross`. -/
def Hole24R (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  CbarIn x ∧ H24K.SAT.OB1 x ∧ ¬ Q45HalfPred F

/-- Off-`OB1` open classes inside `C̄` outside `Q45-Half`: `mpppz` (`ZRes24`), `mpppp`, `mpppm`
(attacked in `Wire24Zero.lean` / `Type24SAT/K24`). -/
def Hole24OffOB1 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  CbarIn x ∧ ¬ H24K.SAT.OB1 x ∧
    (ZRes24 x ∨ cls24 x false true true true true ∨ cls24 x false true true true false) ∧
    ¬ Q45HalfPred F

/-- Existing non-closure flags from `rupert_or_resid24_noFacetCell_noNC_noAdj_noFace`. -/
def Hole24Flags (x : Fin 7 → ℝ³) (fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ) : Prop :=
  ¬ FacetCell24 fs ∧ ¬ T024 x ∧ ¬ NC24 x ∧ ¬ Adj24 x ∧ ¬ Face.Face24 x

/-- The single named Type-24 open hole proposition for `Minimality.lean`. -/
def Hole24 (x : Fin 7 → ℝ³) (fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ) (F : S0xFac 9 s0x_S24 x) : Prop :=
  Hole24Flags x fs ∧
    (Hole24SigmaB x ∨ Hole24Q45Special x F ∨ Hole24R x F ∨ Hole24OffOB1 x F)

/-- Main Type-24 reduction using `rupert_or_resid24_noFacetCell_noNC_noAdj_noFace`,
`isRupert_type24_outside_Cbar`, and `isRupert_q45_half` (`mkFac24` constructs `F`). -/
theorem type24_rupert_or_hole {x : Fin 7 → ℝ³}
    (fA fB fC fD fE fF fG fH fI : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 1, 2} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 1, 2} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({0, 1, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({0, 1, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hC : ∀ i, (i ∈ ({1, 2, 6} : Finset (Fin 7)) → fC (x i) = 0) ∧
      (i ∉ ({1, 2, 6} : Finset (Fin 7)) → fC (x i) < 0))
    (hD : ∀ i, (i ∈ ({2, 3, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({2, 3, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({0, 4, 6} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({0, 4, 6} : Finset (Fin 7)) → fE (x i) < 0))
    (hF : ∀ i, (i ∈ ({0, 2, 5} : Finset (Fin 7)) → fF (x i) = 0) ∧
      (i ∉ ({0, 2, 5} : Finset (Fin 7)) → fF (x i) < 0))
    (hG : ∀ i, (i ∈ ({0, 3, 4, 5} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({0, 3, 4, 5} : Finset (Fin 7)) → fG (x i) < 0))
    (hH : ∀ i, (i ∈ ({2, 3, 5} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({2, 3, 5} : Finset (Fin 7)) → fH (x i) < 0))
    (hI : ∀ i, (i ∈ ({3, 4, 6} : Finset (Fin 7)) → fI (x i) = 0) ∧
      (i ∉ ({3, 4, 6} : Finset (Fin 7)) → fI (x i) < 0)) :
    IsRupert (univ.image x) ∨
      ∃ hh : ∀ t i, (i ∈ s0x_S24 t → ![fA, fB, fF, fG, fE, fC, fH, fD, fI] t (x i) = 0) ∧
        (i ∉ s0x_S24 t → ![fA, fB, fF, fG, fE, fC, fH, fD, fI] t (x i) < 0),
        Hole24 x ![fA, fB, fF, fG, fE, fC, fH, fD, fI]
          (mkFac24 ![fA, fB, fF, fG, fE, fC, fH, fD, fI] hh) := by
  rcases Face.rupert_or_resid24_noFacetCell_noNC_noAdj_noFace
      fA fB fC fD fE fF fG fH fI hA hB hC hD hE hF hG hH hI with
    hRup | ⟨hres, hz, hT0, hNC, hAdj, hFace⟩
  · exact Or.inl hRup
  · have hflags : Hole24Flags x ![fA, fB, fF, fG, fE, fC, fH, fD, fI] :=
      ⟨hz, hT0, hNC, hAdj, hFace⟩
    have hh : ∀ t i, (i ∈ s0x_S24 t → ![fA, fB, fF, fG, fE, fC, fH, fD, fI] t (x i) = 0) ∧
        (i ∉ s0x_S24 t → ![fA, fB, fF, fG, fE, fC, fH, fD, fI] t (x i) < 0) := by
      intro t i
      fin_cases t
      exacts [hA i, hB i, hF i, hG i, hE i, hC i, hH i, hD i, hI i]
    set F := mkFac24 ![fA, fB, fF, fG, fE, fC, fH, fD, fI] hh
    by_cases hCbar : CbarIn x
    · by_cases hHalf : Q45HalfPred F
      · rcases Q45.isRupert_q45_half F hHalf with hRup | hSp
        · exact Or.inl hRup
        · exact Or.inr ⟨hh, hflags, Or.inr (Or.inl ⟨hCbar, hres, hHalf, hSp⟩)⟩
      · by_cases hOB1 : H24K.SAT.OB1 x
        · exact Or.inr ⟨hh, hflags, Or.inr (Or.inr (Or.inl ⟨hCbar, hOB1, hHalf⟩))⟩
        · have hOff : ZRes24 x ∨ cls24 x false true true true true ∨
              cls24 x false true true true false := by
            rcases hres with hO | hZ | hP | hM
            · exact False.elim (hOB1 hO)
            · exact Or.inl hZ
            · exact Or.inr (Or.inl hP)
            · exact Or.inr (Or.inr hM)
          exact Or.inr ⟨hh, hflags, Or.inr (Or.inr (Or.inr ⟨hCbar, hOB1, hOff, hHalf⟩))⟩
    · by_cases hSig : Minimality.RegionB24 x →
          Minimality.S6Free x ∨ Minimality.S2Free x ∨ Minimality.S0Free x
      · exact Or.inl (Minimality.isRupert_type24_outside_Cbar
          (Minimality.Type24.ofAffine x fA fB fC fD fE fF hA hB hC hD hE hF) hCbar hSig)
      · have hnotB : Minimality.RegionB24 x ∧
            ¬ (Minimality.S6Free x ∨ Minimality.S2Free x ∨ Minimality.S0Free x) := by
          by_contra hc
          apply hSig
          intro hr
          by_contra hf
          exact hc ⟨hr, hf⟩
        exact Or.inr ⟨hh, hflags, Or.inl hnotB⟩

end Minimality.T24
