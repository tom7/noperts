module

public import Minimality.Type24Face
public import Minimality.Type24SAT.K24.Wire24Res
public import Minimality.Type24
public import Minimality.Q45
public import Minimality.RCell24
public import Minimality.RDispatch24

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
2. `Minimality.isRupert_type24_outside_Cbar'` (closes all of `¬ CbarIn`, `Type24.lean` / Lemma CV),
3. `Q45.q45_half_cell` (closes `Q45-Half` off `Q45Special'`, `Q45.lean`),
4. Generic closed-cell / face-chord leaves `RCell.AnyFaceChord` and `RCell.LexAny` (`RCell24.lean`).

The single named open hole `Hole24` consists of `Hole24Flags` together with two pieces stated in
terms of the generic negations:
- `Hole24Q45Special` (inside `C̄ ∩ Resid24 ∩ Q45HalfPred`, `Q45Special'`, off `AnyFaceChord` and `LexAny`),
- `Hole24R` (inside `C̄ ∩ Resid24 \ Q45HalfPred`, off `AnyFaceChord` and `LexAny`).
-/

/-- Special loci of Theorem Q45 inside `C̄ ∩ Resid24`, off `AnyFaceChord` and `LexAny`. -/
def Hole24Q45Special (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  CbarIn x ∧ Resid24 x ∧ Q45HalfPred F ∧ Q45.Q45Special' F ∧
    ¬ RCell.AnyFaceChord F ∧ ¬ RCell.LexAny F

/-- Region `R` residual inside `C̄ ∩ Resid24 \ Q45HalfPred`, off `AnyFaceChord` and `LexAny`. -/
def Hole24R (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  CbarIn x ∧ Resid24 x ∧ ¬ Q45HalfPred F ∧
    ¬ RCell.AnyFaceChord F ∧ ¬ RCell.LexAny F

/-- Existing non-closure flags from `rupert_or_resid24_noFacetCell_noNC_noAdj_noFace`. -/
def Hole24Flags (x : Fin 7 → ℝ³) (fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ) : Prop :=
  ¬ FacetCell24 fs ∧ ¬ T024 x ∧ ¬ NC24 x ∧ ¬ Adj24 x ∧ ¬ Face.Face24 x

/-- The single named Type-24 open hole proposition for `Minimality.lean`. -/
def Hole24 (x : Fin 7 → ℝ³) (fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ) (F : S0xFac 9 s0x_S24 x) : Prop :=
  Hole24Flags x fs ∧ (Hole24Q45Special x F ∨ Hole24R x F)

/-- Main Type-24 reduction using `rupert_or_resid24_noFacetCell_noNC_noAdj_noFace`,
`isRupert_type24_outside_Cbar'`, `Q45.q45_half_cell`, `RCell.anyFaceChord_isRupert`, and
`RCell.lexAny_isRupert` (`mkFac24` constructs `F`). -/
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
    · by_cases hAfc : RCell.AnyFaceChord F
      · exact Or.inl (RCell.anyFaceChord_isRupert F hAfc)
      · by_cases hLex : RCell.LexAny F
        · exact Or.inl (RCell.lexAny_isRupert F hLex)
        · by_cases hHalf : Q45HalfPred F
          · rcases Q45.q45_half_cell F hHalf with hRup | hSp
            · exact Or.inl hRup
            · exact Or.inr ⟨hh, hflags, Or.inl ⟨hCbar, hres, hHalf, hSp, hAfc, hLex⟩⟩
          · exact Or.inr ⟨hh, hflags, Or.inr ⟨hCbar, hres, hHalf, hAfc, hLex⟩⟩
    · exact Or.inl (Minimality.isRupert_type24_outside_Cbar'
        (Minimality.Type24.ofAffine x fA fB fC fD fE fF hA hB hC hD hE hF) hCbar)

end Minimality.T24
