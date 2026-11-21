module

public import Mathlib
public import Minimality.DiagCross
public import Minimality.RimCell
public import Minimality.Slide
public import Minimality.UnimodalCert
public import Minimality.FaceChordFac
public import Minimality.Q45Signs
public import Minimality.Q45Orient
public import Minimality.CornerU
public import Minimality.Q45Leaf
public import Minimality.Q45J0
public import Minimality.Q45Cell
public import Minimality.RimFromSigns

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped RealInnerProductSpace Topology
open Filter Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.T24.RimFromSigns

namespace Minimality.T24.Q45

/-!
# Task AH: Local Q45 Dispatcher

This module formalizes:
1. `Q45Special`: The disjunction of the negations of all special-position locus
   exclusions used across the twelve leaves:
   - `Q45TieLocus`: 6 corner base tie loci (T-B1 through T-C2).
   - `Q45S3Locus`: Farther vertex tie between exterior vertices 2 and 6 on facet 3.
   - `Q45S4Locus`: 7 chord offset failure loci (chords [4,0], [3,0], [3,5], [0,5], [0,3], [4,3], [4,5]).
   - `Q45S2Locus`: 9 quad projection depth collision loci.
2. `q45_half`: The refined dispatcher with the weakest branch-specific sign hypotheses.
3. `q45_half_geom`: Global version obtaining `s, t` from `lemmaM_quad_decomp`.
4. `q45`: The primary local dispatcher theorem with hypotheses `ha4, ha5`.
-/


/-- Special locus S3 (farther vertex tie on face 3 between exterior vertices 2 and 6).
Serves all twelve leaves. -/
def Q45S3Locus {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  -- Serves all twelve leaves: exterior vertices 2 and 6 have equal distance to facet plane 3
  F.f 3 (x 2) = F.f 3 (x 6)

/-- Weakest a-hypothesis predicate for the Q45 branches:
Each branch receives only the normal sign at the specific view(s) it inspects.
Matches Carbon's Q45-Half predicate (CARBON-RESPONSES.md A19 Rank 4) on K+ and K-,
and specifies both signs at the flat ridge kJ = 0 for interior ray perturbation. -/
def Q45HalfHyp {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (s t : ℝ) : Prop :=
  (det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) < 0 →
    ((s ≤ 1 → ⟪F.N 5, x 5 - x 0⟫ < 0) ∧ (1 < s → ⟪F.N 5, x 3 - x 4⟫ < 0))) ∧
  (0 < det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) →
    ((t ≤ 1 → ⟪F.N 5, x 4 - x 0⟫ < 0) ∧ (1 < t → ⟪F.N 5, x 3 - x 5⟫ < 0))) ∧
  (det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) = 0 →
    (⟪F.N 5, x 4 - x 0⟫ < 0 ∧ ⟪F.N 5, x 5 - x 0⟫ < 0))

/-! ### Cell-first Q45 dispatcher (`q45_half_cell` and `Q45Special'`) -/

/-- `hlex` cell condition for `q45_B1_cell` (`s < 1`). -/
def HlexB1 (x : Fin 7 → ℝ³) : Prop :=
  ∃ i ∈ ({4, 2} : Finset (Fin 7)), ∃ j ∈ ({6, 0} : Finset (Fin 7)),
    ⟪x i - x j, x 5 - x 0⟫ < 0 ∨ (⟪x i - x j, x 5 - x 0⟫ = 0 ∧ 0 < ⟪x i - x j, x 4 - x 0⟫)

/-- `hlex` cell condition for `q45_B2_cell` (`1 < s`). -/
def HlexB2 (x : Fin 7 → ℝ³) : Prop :=
  ∃ i ∈ ({3, 2} : Finset (Fin 7)), ∃ j ∈ ({6, 5} : Finset (Fin 7)),
    ⟪x i - x j, x 3 - x 4⟫ < 0 ∨ (⟪x i - x j, x 3 - x 4⟫ = 0 ∧ ⟪x i - x j, x 5 - x 0⟫ < 0)

/-- `hlex` cell condition for `q45_C1_cell` (`t < 1`). -/
def HlexC1 (x : Fin 7 → ℝ³) : Prop :=
  ∃ i ∈ ({6, 5} : Finset (Fin 7)), ∃ j ∈ ({0, 2} : Finset (Fin 7)),
    ⟪x i - x j, x 4 - x 0⟫ < 0 ∨ (⟪x i - x j, x 4 - x 0⟫ = 0 ∧ 0 < ⟪x i - x j, x 5 - x 0⟫)

/-- `hlex` cell condition for `q45_C2_cell` (`1 < t`). -/
def HlexC2 (x : Fin 7 → ℝ³) : Prop :=
  ∃ i ∈ ({6, 3} : Finset (Fin 7)), ∃ j ∈ ({4, 2} : Finset (Fin 7)),
    ⟪x i - x j, x 3 - x 5⟫ < 0 ∨ (⟪x i - x j, x 3 - x 5⟫ = 0 ∧ ⟪x i - x j, x 4 - x 0⟫ < 0)

def Q45TieLocusB1 (x : Fin 7 → ℝ³) : Prop :=
  ⟪x 2, x 5 - x 0⟫ = ⟪x 4, x 5 - x 0⟫ ∧ ⟪x 4, x 5 - x 0⟫ = ⟪x 6, x 5 - x 0⟫
def Q45TieLocusBs1 (x : Fin 7 → ℝ³) : Prop := ⟪x 2, x 5 - x 0⟫ = ⟪x 6, x 5 - x 0⟫
def Q45TieLocusB2 (x : Fin 7 → ℝ³) : Prop :=
  ⟪x 2, x 3 - x 4⟫ = ⟪x 5, x 3 - x 4⟫ ∧ ⟪x 5, x 3 - x 4⟫ = ⟪x 6, x 3 - x 4⟫
def Q45TieLocusC1 (x : Fin 7 → ℝ³) : Prop :=
  ⟪x 2, x 4 - x 0⟫ = ⟪x 5, x 4 - x 0⟫ ∧ ⟪x 5, x 4 - x 0⟫ = ⟪x 6, x 4 - x 0⟫
def Q45TieLocusCt1 (x : Fin 7 → ℝ³) : Prop := ⟪x 2, x 4 - x 0⟫ = ⟪x 6, x 4 - x 0⟫
def Q45TieLocusC2 (x : Fin 7 → ℝ³) : Prop :=
  ⟪x 2, x 3 - x 5⟫ = ⟪x 4, x 3 - x 5⟫ ∧ ⟪x 4, x 3 - x 5⟫ = ⟪x 6, x 3 - x 5⟫

def Q45S4LocusB1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ¬ (⟪F.N 3, cross (x 0 - x 4) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4)⟫ ≠ 0 ∨
     ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 0 - x 4⟫ < 0 ∨
     ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 0, x 4 - x 0⟫ < 0)
def Q45S4LocusBs1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ¬ (⟪F.N 3, cross (x 0 - x 3) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 3)⟫ ≠ 0 ∨
     ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 3, x 0 - x 3⟫ < 0 ∨
     ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 0, x 3 - x 0⟫ < 0)
def Q45S4LocusB2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ¬ (⟪F.N 3, cross (x 5 - x 3) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 3)⟫ ≠ 0 ∨
     ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 3, x 5 - x 3⟫ < 0 ∨
     ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 3 - x 5⟫ < 0)
def Q45S4LocusC1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ¬ (⟪F.N 3, cross (x 5 - x 0) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 0)⟫ ≠ 0 ∨
     ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 0, x 5 - x 0⟫ < 0 ∨
     ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 0 - x 5⟫ < 0)
def Q45S4LocusCt1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ¬ (⟪F.N 3, cross (x 3 - x 0) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 0)⟫ ≠ 0 ∨
     ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 0, x 3 - x 0⟫ < 0 ∨
     ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 3, x 0 - x 3⟫ < 0)
def Q45S4LocusC2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ¬ (⟪F.N 3, cross (x 3 - x 4) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4)⟫ ≠ 0 ∨
     ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 3 - x 4⟫ < 0 ∨
     ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 3, x 4 - x 3⟫ < 0)
def Q45S4LocusJ0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ¬ (⟪F.N 3, cross (x 5 - x 4) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4)⟫ ≠ 0 ∨
     ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 5 - x 4⟫ < 0 ∨
     ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 4 - x 5⟫ < 0)

def Q45S2LocusB1 (x : Fin 7 → ℝ³) : Prop :=
  ¬ (∀ i j : ZMod 4, i ≠ j →
    ⟪quad (x 6) (x 4) (x 0) (x 2) i - quad (x 6) (x 4) (x 0) (x 2) j, x 5 - x 0⟫ ≠ 0 ∨
    ⟪quad (x 6) (x 4) (x 0) (x 2) i - quad (x 6) (x 4) (x 0) (x 2) j, x 4 - x 0⟫ ≠ 0)
def Q45S2LocusBs1 (x : Fin 7 → ℝ³) : Prop :=
  ¬ (∀ i j : ZMod 4, i ≠ j →
    ⟪quad (x 6) (x 3) (x 0) (x 2) i - quad (x 6) (x 3) (x 0) (x 2) j, x 5 - x 0⟫ ≠ 0 ∨
    ⟪quad (x 6) (x 3) (x 0) (x 2) i - quad (x 6) (x 3) (x 0) (x 2) j, x 4 - x 0⟫ ≠ 0)
def Q45S2LocusB2 (x : Fin 7 → ℝ³) : Prop :=
  ¬ (∀ i j : ZMod 4, i ≠ j →
    ⟪quad (x 6) (x 3) (x 5) (x 2) i - quad (x 6) (x 3) (x 5) (x 2) j, x 3 - x 4⟫ ≠ 0 ∨
    ⟪quad (x 6) (x 3) (x 5) (x 2) i - quad (x 6) (x 3) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0)
def Q45S2LocusC1 (x : Fin 7 → ℝ³) : Prop :=
  ¬ (∀ i j : ZMod 4, i ≠ j →
    ⟪quad (x 6) (x 0) (x 5) (x 2) i - quad (x 6) (x 0) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0 ∨
    ⟪quad (x 6) (x 0) (x 5) (x 2) i - quad (x 6) (x 0) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0)
def Q45S2LocusCt1 (x : Fin 7 → ℝ³) : Prop :=
  ¬ (∀ i j : ZMod 4, i ≠ j →
    ⟪quad (x 6) (x 0) (x 3) (x 2) i - quad (x 6) (x 0) (x 3) (x 2) j, x 4 - x 0⟫ ≠ 0 ∨
    ⟪quad (x 6) (x 0) (x 3) (x 2) i - quad (x 6) (x 0) (x 3) (x 2) j, x 5 - x 0⟫ ≠ 0)
def Q45S2LocusC2 (x : Fin 7 → ℝ³) : Prop :=
  ¬ (∀ i j : ZMod 4, i ≠ j →
    ⟪quad (x 6) (x 4) (x 3) (x 2) i - quad (x 6) (x 4) (x 3) (x 2) j, x 3 - x 5⟫ ≠ 0 ∨
    ⟪quad (x 6) (x 4) (x 3) (x 2) i - quad (x 6) (x 4) (x 3) (x 2) j, x 4 - x 0⟫ ≠ 0)
def Q45S2LocusJ0_e5 (x : Fin 7 → ℝ³) : Prop :=
  ¬ (∀ i j : ZMod 4, i ≠ j →
    ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0 ∨
    ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0)
def Q45S2LocusJ0_e34 (x : Fin 7 → ℝ³) : Prop :=
  ¬ (∀ i j : ZMod 4, i ≠ j →
    ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 3 - x 4⟫ ≠ 0 ∨
    ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0)
def Q45S2LocusJ0_e35 (x : Fin 7 → ℝ³) : Prop :=
  ¬ (∀ i j : ZMod 4, i ≠ j →
    ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 3 - x 5⟫ ≠ 0 ∨
    ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0)

def Q45SpecialT_B1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ¬ HlexB1 x ∧ (Q45TieLocusB1 x ∨ Q45S3Locus F ∨ Q45S4LocusB1 F ∨ Q45S2LocusB1 x)
def Q45SpecialT_B2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ¬ HlexB2 x ∧ (Q45TieLocusB2 x ∨ Q45S3Locus F ∨ Q45S4LocusB2 F ∨ Q45S2LocusB2 x)
def Q45SpecialT_C1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ¬ HlexC1 x ∧ (Q45TieLocusC1 x ∨ Q45S3Locus F ∨ Q45S4LocusC1 F ∨ Q45S2LocusC1 x)
def Q45SpecialT_C2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ¬ HlexC2 x ∧ (Q45TieLocusC2 x ∨ Q45S3Locus F ∨ Q45S4LocusC2 F ∨ Q45S2LocusC2 x)
def Q45SpecialBs1Ct1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  Q45TieLocusBs1 x ∨ Q45TieLocusCt1 x ∨ Q45S3Locus F ∨
  Q45S4LocusBs1 F ∨ Q45S4LocusCt1 F ∨ Q45S2LocusBs1 x ∨ Q45S2LocusCt1 x
def Q45SpecialJ0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  Q45S3Locus F ∨ Q45S4LocusJ0 F ∨
  Q45S2LocusJ0_e5 x ∨ Q45S2LocusJ0_e34 x ∨ Q45S2LocusJ0_e35 x

/-- Refined Q45 special-position residual after trying `q45_B1_cell`..`q45_C2_cell` first. -/
def Q45Special' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  Q45SpecialT_B1 F ∨ Q45SpecialT_B2 F ∨ Q45SpecialT_C1 F ∨ Q45SpecialT_C2 F ∨
  Q45SpecialBs1Ct1 F ∨ Q45SpecialJ0 F


/-- Local cell-first Q45-Half dispatcher: tries `q45_B1_cell`..`q45_C2_cell` first in the four
interior corner branches before falling back to the face-chord leaves and `Q45Special'`. -/
theorem q45_half_cell_local {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (s t : ℝ) (hs0 : 0 < s) (ht : 0 < t) (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hsign : Q45HalfHyp F s t) :
    IsRupert (univ.image x) ∨ Q45Special' F := by
  set kJ := det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6)
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
  have h_om := omega_ne_zero F
  rcases lt_trichotomy (kJ * Ω) 0 with hk_neg | hk_zero | hk_pos
  · have h_Kplus_signs := hsign.1 hk_neg
    rcases le_or_gt s 1 with hs | hs
    · have ha5 := h_Kplus_signs.1 hs
      by_cases h6hi : max ⟪x 4, x 5 - x 0⟫ ⟪x 2, x 5 - x 0⟫ ≤ ⟪x 6, x 5 - x 0⟫
      · rcases lt_or_eq_of_le hs with hs_lt | hs_eq
        · by_cases hlex : HlexB1 x
          · exact Or.inl (q45_B1_cell F ha5 s t hs0 ht hst hdecomp hs_lt hlex)
          · by_cases htie : ¬ Q45TieLocusB1 x
            · by_cases hs3 : F.f 3 (x 2) ≠ F.f 3 (x 6)
              · by_cases hs4 : ¬ Q45S4LocusB1 F
                · by_cases hs2 : ¬ Q45S2LocusB1 x
                  · exact Or.inl (isRupert_of_faceChordView F (q45_B1 F ha5 s t hs0 ht hst hdecomp hs_lt h6hi htie (not_not.mp hs2) hs3 (not_not.mp hs4)))
                  · exact Or.inr (Or.inl ⟨hlex, Or.inr (Or.inr (Or.inr (not_not.mp hs2)))⟩)
                · exact Or.inr (Or.inl ⟨hlex, Or.inr (Or.inr (Or.inl (not_not.mp hs4)))⟩)
              · exact Or.inr (Or.inl ⟨hlex, Or.inr (Or.inl (not_not.mp hs3))⟩)
            · exact Or.inr (Or.inl ⟨hlex, Or.inl (not_not.mp htie)⟩)
        · by_cases htie : ¬ Q45TieLocusBs1 x
          · by_cases hs3 : F.f 3 (x 2) ≠ F.f 3 (x 6)
            · by_cases hs4 : ¬ Q45S4LocusBs1 F
              · by_cases hs2 : ¬ Q45S2LocusBs1 x
                · exact Or.inl (isRupert_of_faceChordView F (q45_Bs1 F ha5 s t ht hdecomp hs_eq h6hi htie (not_not.mp hs2) hs3 (not_not.mp hs4)))
                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (not_not.mp hs2))))))))))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (not_not.mp hs4))))))))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (not_not.mp hs3)))))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (not_not.mp htie)))))))
      · have h6lo : min ⟪x 6, x 5 - x 0⟫ ⟪x 5, x 5 - x 0⟫ < max ⟪x 4, x 5 - x 0⟫ ⟪x 2, x 5 - x 0⟫ :=
          lt_of_le_of_lt (min_le_left _ _) (not_le.mp h6hi)
        by_cases hs3 : F.f 3 (x 2) ≠ F.f 3 (x 6)
        · by_cases hs4 : ¬ Q45S4LocusJ0 F
          · by_cases hs2 : ¬ Q45S2LocusJ0_e5 x
            · exact Or.inl (isRupert_of_faceChordView F (q45_Kplus_s_le_one F ha5 s t hs0 ht hst hdecomp hk_neg hs h6lo (not_not.mp hs2) hs3 (not_not.mp hs4)))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (not_not.mp hs2)))))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (not_not.mp hs4))))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (not_not.mp hs3)))))))
    · have ha34 := h_Kplus_signs.2 hs
      by_cases h6hi : max ⟪x 4, x 3 - x 4⟫ ⟪x 2, x 3 - x 4⟫ ≤ min ⟪x 6, x 3 - x 4⟫ ⟪x 5, x 3 - x 4⟫
      · by_cases hlex : HlexB2 x
        · exact Or.inl (q45_B2_cell F ha34 s t ht hdecomp hs hlex)
        · by_cases htie : ¬ Q45TieLocusB2 x
          · by_cases hs3 : F.f 3 (x 2) ≠ F.f 3 (x 6)
            · by_cases hs4 : ¬ Q45S4LocusB2 F
              · by_cases hs2 : ¬ Q45S2LocusB2 x
                · exact Or.inl (isRupert_of_faceChordView F (q45_B2 F ha34 s t ht hdecomp hs h6hi htie (not_not.mp hs2) hs3 (not_not.mp hs4)))
                · exact Or.inr (Or.inr (Or.inl ⟨hlex, Or.inr (Or.inr (Or.inr (not_not.mp hs2)))⟩))
              · exact Or.inr (Or.inr (Or.inl ⟨hlex, Or.inr (Or.inr (Or.inl (not_not.mp hs4)))⟩))
            · exact Or.inr (Or.inr (Or.inl ⟨hlex, Or.inr (Or.inl (not_not.mp hs3))⟩))
          · exact Or.inr (Or.inr (Or.inl ⟨hlex, Or.inl (not_not.mp htie)⟩))
      · have h6lo : min ⟪x 6, x 3 - x 4⟫ ⟪x 5, x 3 - x 4⟫ < max ⟪x 4, x 3 - x 4⟫ ⟪x 2, x 3 - x 4⟫ := not_le.mp h6hi
        by_cases hs3 : F.f 3 (x 2) ≠ F.f 3 (x 6)
        · by_cases hs4 : ¬ Q45S4LocusJ0 F
          · by_cases hs2 : ¬ Q45S2LocusJ0_e34 x
            · exact Or.inl (isRupert_of_faceChordView F (q45_Kplus_s_gt_one F ha34 s t hs0 ht hst hdecomp hk_neg hs h6lo (not_not.mp hs2) hs3 (not_not.mp hs4)))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (not_not.mp hs2))))))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (not_not.mp hs4))))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (not_not.mp hs3)))))))
  · have hk0 : kJ = 0 := (mul_eq_zero.mp hk_zero).resolve_right h_om
    have hK0_signs := hsign.2.2 hk0
    by_cases hs3 : F.f 3 (x 2) ≠ F.f 3 (x 6)
    · by_cases hs4 : ¬ Q45S4LocusJ0 F
      · by_cases hs2 : ¬ Q45S2LocusJ0_e5 x
        · exact Or.inl (isRupert_of_faceChordView F (q45_K0 F hK0_signs.1 hK0_signs.2 s t hs0 ht hst hdecomp hk0 (not_not.mp hs2) hs3 (not_not.mp hs4)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (not_not.mp hs2)))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (not_not.mp hs4))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (not_not.mp hs3)))))))
  · have h_Kminus_signs := hsign.2.1 hk_pos
    rcases le_or_gt t 1 with ht1_le | ht1_gt
    · have ha4 := h_Kminus_signs.1 ht1_le
      by_cases h2hi : max ⟪x 6, x 4 - x 0⟫ ⟪x 5, x 4 - x 0⟫ ≤ ⟪x 2, x 4 - x 0⟫
      · rcases lt_or_eq_of_le ht1_le with ht_lt | ht_eq
        · by_cases hlex : HlexC1 x
          · exact Or.inl (q45_C1_cell F ha4 s t hs0 ht hst hdecomp ht_lt hlex)
          · by_cases htie : ¬ Q45TieLocusC1 x
            · by_cases hs3 : F.f 3 (x 2) ≠ F.f 3 (x 6)
              · by_cases hs4 : ¬ Q45S4LocusC1 F
                · by_cases hs2 : ¬ Q45S2LocusC1 x
                  · exact Or.inl (isRupert_of_faceChordView F (q45_C1 F ha4 s t hs0 ht hst hdecomp ht_lt h2hi htie (not_not.mp hs2) hs3 (not_not.mp hs4)))
                  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hlex, Or.inr (Or.inr (Or.inr (not_not.mp hs2)))⟩)))
                · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hlex, Or.inr (Or.inr (Or.inl (not_not.mp hs4)))⟩)))
              · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hlex, Or.inr (Or.inl (not_not.mp hs3))⟩)))
            · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hlex, Or.inl (not_not.mp htie)⟩)))
        · by_cases htie : ¬ Q45TieLocusCt1 x
          · by_cases hs3 : F.f 3 (x 2) ≠ F.f 3 (x 6)
            · by_cases hs4 : ¬ Q45S4LocusCt1 F
              · by_cases hs2 : ¬ Q45S2LocusCt1 x
                · exact Or.inl (isRupert_of_faceChordView F (q45_Ct1 F ha4 s t hs0 hdecomp ht_eq h2hi htie (not_not.mp hs2) hs3 (not_not.mp hs4)))
                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (not_not.mp hs2))))))))))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (not_not.mp hs4)))))))))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (not_not.mp hs3)))))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (not_not.mp htie))))))))
      · have h2lo : min ⟪x 4, x 4 - x 0⟫ ⟪x 2, x 4 - x 0⟫ < max ⟪x 6, x 4 - x 0⟫ ⟪x 5, x 4 - x 0⟫ :=
          lt_of_le_of_lt (min_le_right _ _) (not_le.mp h2hi)
        by_cases hs3 : F.f 3 (x 2) ≠ F.f 3 (x 6)
        · by_cases hs4 : ¬ Q45S4LocusJ0 F
          · by_cases hs2 : ¬ Q45S2LocusJ0_e5 x
            · have hs2' : ∀ i j : ZMod 4, i ≠ j →
                ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0 ∨
                ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0 := by
                intro i j hij; exact ((not_not.mp hs2) i j hij).symm
              exact Or.inl (isRupert_of_faceChordView F (q45_Kminus_t_le_one F ha4 s t hs0 ht hst hdecomp hk_pos ht1_le h2lo hs2' hs3 (not_not.mp hs4)))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (not_not.mp hs2)))))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (not_not.mp hs4))))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (not_not.mp hs3)))))))
    · have ha35 := h_Kminus_signs.2 ht1_gt
      by_cases h2hi : max ⟪x 6, x 3 - x 5⟫ ⟪x 5, x 3 - x 5⟫ ≤ min ⟪x 2, x 3 - x 5⟫ ⟪x 4, x 3 - x 5⟫
      · by_cases hlex : HlexC2 x
        · exact Or.inl (q45_C2_cell F ha35 s t hs0 hdecomp ht1_gt hlex)
        · by_cases htie : ¬ Q45TieLocusC2 x
          · by_cases hs3 : F.f 3 (x 2) ≠ F.f 3 (x 6)
            · by_cases hs4 : ¬ Q45S4LocusC2 F
              · by_cases hs2 : ¬ Q45S2LocusC2 x
                · exact Or.inl (isRupert_of_faceChordView F (q45_C2 F ha35 s t hs0 hdecomp ht1_gt h2hi htie (not_not.mp hs2) hs3 (not_not.mp hs4)))
                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hlex, Or.inr (Or.inr (Or.inr (not_not.mp hs2)))⟩))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hlex, Or.inr (Or.inr (Or.inl (not_not.mp hs4)))⟩))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hlex, Or.inr (Or.inl (not_not.mp hs3))⟩))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hlex, Or.inl (not_not.mp htie)⟩))))
      · have h2lo : min ⟪x 4, x 3 - x 5⟫ ⟪x 2, x 3 - x 5⟫ < max ⟪x 6, x 3 - x 5⟫ ⟪x 5, x 3 - x 5⟫ := by
          rw [min_comm]; exact not_le.mp h2hi
        by_cases hs3 : F.f 3 (x 2) ≠ F.f 3 (x 6)
        · by_cases hs4 : ¬ Q45S4LocusJ0 F
          · by_cases hs2 : ¬ Q45S2LocusJ0_e35 x
            · exact Or.inl (isRupert_of_faceChordView F (q45_Kminus_t_gt_one F ha35 s t hs0 ht hst hdecomp hk_pos ht1_gt h2lo (not_not.mp hs2) hs3 (not_not.mp hs4)))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (not_not.mp hs2))))))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (not_not.mp hs4))))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (not_not.mp hs3)))))))

/-- Global cell-first Q45-Half dispatcher (`IsRupert ∨ Q45Special' F`), obtaining `s, t` from
`lemmaM_quad_decomp F`. -/
theorem q45_half_cell {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hsign : ∀ s t : ℝ, 0 < s → 0 < t → 1 < s + t →
      x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0) → Q45HalfHyp F s t) :
    IsRupert (univ.image x) ∨ Q45Special' F := by
  obtain ⟨s, t, hs0, ht, hst, hdecomp⟩ := lemmaM_quad_decomp F
  exact q45_half_cell_local F s t hs0 ht hst hdecomp (hsign s t hs0 ht hst hdecomp)

end Minimality.T24.Q45
