module

public import Minimality.Type24Face
public import Minimality.Type24SAT.K24.Wire24Res
public import Minimality.Type24
public import Minimality.Q45
public import Minimality.RDispatch24
public import Minimality.RSpec24

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

/-- Outside `C̄`, the residual `Σ_B` locus: `RegionB24` with no free side crossing
(attacked in `Type24.lean` / `FEWER-FACES-PROOFS.md` §15). -/
def Hole24SigmaB (x : Fin 7 → ℝ³) : Prop :=
  Minimality.RegionB24 x ∧ ¬ (Minimality.S6Free x ∨ Minimality.S2Free x ∨ Minimality.S0Free x)

/-- Special loci of Theorem Q45 inside `C̄ ∩ Resid24` (no `OB1` restriction, since `q45_half_cell`
requires only `F` and `Q45HalfPred F`; refined to `Q45Special' F` after trying `q45_B1_cell`..`q45_C2_cell`). -/
def Hole24Q45Special (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  CbarIn x ∧ Resid24 x ∧ Q45HalfPred F ∧ Q45.Q45Special' F

/-- Region `R` + off-`OB1` residual inside `C̄ ∩ Resid24 \ Q45HalfPred` after applying
`RDispatch.r_dispatch` (`R24Spec ∨ R24Wall ∨ R24Open`) and excluding the `RSpec` closed-cell leaves. -/
def Hole24RRes {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  Resid24 x ∧ RDispatch.RResidual' F ∧ ¬ RSpec.HSpecAny F

/-- Existing non-closure flags from `rupert_or_resid24_noFacetCell_noNC_noAdj_noFace`. -/
def Hole24Flags (x : Fin 7 → ℝ³) (fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ) : Prop :=
  ¬ FacetCell24 fs ∧ ¬ T024 x ∧ ¬ NC24 x ∧ ¬ Adj24 x ∧ ¬ Face.Face24 x

/-- The single named Type-24 open hole proposition for `Minimality.lean`. -/
def Hole24 (x : Fin 7 → ℝ³) (fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ) (F : S0xFac 9 s0x_S24 x) : Prop :=
  Hole24Flags x fs ∧
    (Hole24SigmaB x ∨ Hole24Q45Special x F ∨ Hole24RRes F)

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
      · rcases Q45.q45_half_cell F hHalf with hRup | hSp
        · exact Or.inl hRup
        · exact Or.inr ⟨hh, hflags, Or.inr (Or.inl ⟨hCbar, hres, hHalf, hSp⟩)⟩
      · rcases RDispatch.r_dispatch F hCbar hHalf with
          h0 | h1 | h2 | h3 | h4 | hRes
        · exact Or.inl (FaceChord.isRupert_cover24_S5 F (Or.inl h0))
        · exact Or.inl (FaceChord.isRupert_cover24_S5 F (Or.inr (Or.inl h1)))
        · exact Or.inl (FaceChord.isRupert_cover24_S5 F (Or.inr (Or.inr (Or.inl h2))))
        · exact Or.inl (FaceChord.isRupert_cover24_S5 F (Or.inr (Or.inr (Or.inr (Or.inl h3)))))
        · exact Or.inl (FaceChord.isRupert_cover24_S5 F (Or.inr (Or.inr (Or.inr (Or.inr h4)))))
        · by_cases hSpec : RSpec.HSpecAny F
          · exact Or.inl (RSpec.rspec_closes F hSpec)
          · exact Or.inr ⟨hh, hflags, Or.inr (Or.inr ⟨hres, hRes, hSpec⟩)⟩
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
