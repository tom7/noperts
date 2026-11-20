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

/-- Six corner tie loci (T-B1 through T-C2). Each represents an exact depth collision
at the base direction, negating that corner leaf's tie-breaking hypothesis. -/
def Q45TieLocus (x : Fin 7 → ℝ³) : Prop :=
  -- Serves `q45_B1`: triple tie z2 = z4 = z6 at e5
  (⟪x 2, x 5 - x 0⟫ = ⟪x 4, x 5 - x 0⟫ ∧ ⟪x 4, x 5 - x 0⟫ = ⟪x 6, x 5 - x 0⟫) ∨
  -- Serves `q45_Bs1`: pair tie z2 = z6 at e5
  (⟪x 2, x 5 - x 0⟫ = ⟪x 6, x 5 - x 0⟫) ∨
  -- Serves `q45_B2`: triple tie z2 = z5 = z6 at e34
  (⟪x 2, x 3 - x 4⟫ = ⟪x 5, x 3 - x 4⟫ ∧ ⟪x 5, x 3 - x 4⟫ = ⟪x 6, x 3 - x 4⟫) ∨
  -- Serves `q45_C1`: triple tie z2 = z5 = z6 at e4
  (⟪x 2, x 4 - x 0⟫ = ⟪x 5, x 4 - x 0⟫ ∧ ⟪x 5, x 4 - x 0⟫ = ⟪x 6, x 4 - x 0⟫) ∨
  -- Serves `q45_Ct1`: pair tie z2 = z6 at e4
  (⟪x 2, x 4 - x 0⟫ = ⟪x 6, x 4 - x 0⟫) ∨
  -- Serves `q45_C2`: triple tie z2 = z4 = z6 at e35
  (⟪x 2, x 3 - x 5⟫ = ⟪x 4, x 3 - x 5⟫ ∧ ⟪x 4, x 3 - x 5⟫ = ⟪x 6, x 3 - x 5⟫)

/-- Special locus S3 (farther vertex tie on face 3 between exterior vertices 2 and 6).
Serves all twelve leaves. -/
def Q45S3Locus {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  -- Serves all twelve leaves: exterior vertices 2 and 6 have equal distance to facet plane 3
  F.f 3 (x 2) = F.f 3 (x 6)

/-- Special locus S4 (chord offset failure on the relevant chord).
Each disjunct is the negation of the chord general-position exclusion used in that leaf:
the orthogonal foot of the farther exterior vertex lies on the closed chord segment. -/
def Q45S4Locus {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  -- Serves `q45_B1`: chord [4, 0] offset failure
  ¬ (⟪F.N 3, cross (x 0 - x 4) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4)⟫ ≠ 0 ∨
     ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 0 - x 4⟫ < 0 ∨
     ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 0, x 4 - x 0⟫ < 0) ∨
  -- Serves `q45_Bs1`: chord [3, 0] offset failure
  ¬ (⟪F.N 3, cross (x 0 - x 3) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 3)⟫ ≠ 0 ∨
     ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 3, x 0 - x 3⟫ < 0 ∨
     ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 0, x 3 - x 0⟫ < 0) ∨
  -- Serves `q45_B2`: chord [3, 5] offset failure
  ¬ (⟪F.N 3, cross (x 5 - x 3) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 3)⟫ ≠ 0 ∨
     ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 3, x 5 - x 3⟫ < 0 ∨
     ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 3 - x 5⟫ < 0) ∨
  -- Serves `q45_C1`: chord [0, 5] offset failure
  ¬ (⟪F.N 3, cross (x 5 - x 0) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 0)⟫ ≠ 0 ∨
     ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 0, x 5 - x 0⟫ < 0 ∨
     ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 0 - x 5⟫ < 0) ∨
  -- Serves `q45_Ct1`: chord [0, 3] offset failure
  ¬ (⟪F.N 3, cross (x 3 - x 0) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 0)⟫ ≠ 0 ∨
     ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 0, x 3 - x 0⟫ < 0 ∨
     ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 3, x 0 - x 3⟫ < 0) ∨
  -- Serves `q45_C2`: chord [4, 3] offset failure
  ¬ (⟪F.N 3, cross (x 3 - x 4) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4)⟫ ≠ 0 ∨
     ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 3 - x 4⟫ < 0 ∨
     ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 3, x 4 - x 3⟫ < 0) ∨
  -- Serves `q45_K0`, `q45_Kplus`, `q45_Kminus` (all J0 leaves): chord [4, 5] offset failure
  ¬ (⟪F.N 3, cross (x 5 - x 4) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4)⟫ ≠ 0 ∨
     ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 5 - x 4⟫ < 0 ∨
     ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 4 - x 5⟫ < 0)

/-- Special locus S2 (persistent depth collision across the affine ray of views).
Each disjunct is the negation of the quad depth-injectivity condition used in that leaf. -/
def Q45S2Locus (x : Fin 7 → ℝ³) : Prop :=
  -- Serves `q45_B1`: quad (6, 4, 0, 2) depth collision along directions e5, e4
  ¬ (∀ i j : ZMod 4, i ≠ j →
    ⟪quad (x 6) (x 4) (x 0) (x 2) i - quad (x 6) (x 4) (x 0) (x 2) j, x 5 - x 0⟫ ≠ 0 ∨
    ⟪quad (x 6) (x 4) (x 0) (x 2) i - quad (x 6) (x 4) (x 0) (x 2) j, x 4 - x 0⟫ ≠ 0) ∨
  -- Serves `q45_Bs1`: quad (6, 3, 0, 2) depth collision along directions e5, e4
  ¬ (∀ i j : ZMod 4, i ≠ j →
    ⟪quad (x 6) (x 3) (x 0) (x 2) i - quad (x 6) (x 3) (x 0) (x 2) j, x 5 - x 0⟫ ≠ 0 ∨
    ⟪quad (x 6) (x 3) (x 0) (x 2) i - quad (x 6) (x 3) (x 0) (x 2) j, x 4 - x 0⟫ ≠ 0) ∨
  -- Serves `q45_B2`: quad (6, 3, 5, 2) depth collision along directions e34, e5
  ¬ (∀ i j : ZMod 4, i ≠ j →
    ⟪quad (x 6) (x 3) (x 5) (x 2) i - quad (x 6) (x 3) (x 5) (x 2) j, x 3 - x 4⟫ ≠ 0 ∨
    ⟪quad (x 6) (x 3) (x 5) (x 2) i - quad (x 6) (x 3) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0) ∨
  -- Serves `q45_C1`: quad (6, 0, 5, 2) depth collision along directions e4, e5
  ¬ (∀ i j : ZMod 4, i ≠ j →
    ⟪quad (x 6) (x 0) (x 5) (x 2) i - quad (x 6) (x 0) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0 ∨
    ⟪quad (x 6) (x 0) (x 5) (x 2) i - quad (x 6) (x 0) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0) ∨
  -- Serves `q45_Ct1`: quad (6, 0, 3, 2) depth collision along directions e4, e5
  ¬ (∀ i j : ZMod 4, i ≠ j →
    ⟪quad (x 6) (x 0) (x 3) (x 2) i - quad (x 6) (x 0) (x 3) (x 2) j, x 4 - x 0⟫ ≠ 0 ∨
    ⟪quad (x 6) (x 0) (x 3) (x 2) i - quad (x 6) (x 0) (x 3) (x 2) j, x 5 - x 0⟫ ≠ 0) ∨
  -- Serves `q45_C2`: quad (6, 4, 3, 2) depth collision along directions e35, e4
  ¬ (∀ i j : ZMod 4, i ≠ j →
    ⟪quad (x 6) (x 4) (x 3) (x 2) i - quad (x 6) (x 4) (x 3) (x 2) j, x 3 - x 5⟫ ≠ 0 ∨
    ⟪quad (x 6) (x 4) (x 3) (x 2) i - quad (x 6) (x 4) (x 3) (x 2) j, x 4 - x 0⟫ ≠ 0) ∨
  -- Serves `q45_K0`, `q45_Kplus` (s ≤ 1), `q45_Kminus` (t ≤ 1): quad (6, 4, 5, 2) along e5, e4
  ¬ (∀ i j : ZMod 4, i ≠ j →
    ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0 ∨
    ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0) ∨
  -- Serves `q45_Kplus` (1 < s): quad (6, 4, 5, 2) along e34, e4
  ¬ (∀ i j : ZMod 4, i ≠ j →
    ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 3 - x 4⟫ ≠ 0 ∨
    ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0) ∨
  -- Serves `q45_Kminus` (1 < t): quad (6, 4, 5, 2) along e35, e5
  ¬ (∀ i j : ZMod 4, i ≠ j →
    ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 3 - x 5⟫ ≠ 0 ∨
    ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0)

/-- **Definition AH1: Full Q45Special Locus**.
Disjunction of the negations of all special-position exclusions across the twelve leaves:
1. `Q45TieLocus`: 6 corner base tie loci (T-B1 .. T-C2).
2. `Q45S3Locus`: farther vertex tie between exterior vertices 2 and 6 on facet 3.
3. `Q45S4Locus`: 7 chord offset failure loci for chords [4,0], [3,0], [3,5], [0,5], [0,3], [4,3], [4,5].
4. `Q45S2Locus`: 9 quad projection depth collision loci. -/
def Q45Special {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  Q45TieLocus x ∨ Q45S3Locus F ∨ Q45S4Locus F ∨ Q45S2Locus x

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

/-- **Theorem AH3: Local Q45-Half Dispatcher (Weakest a-Hypothesis Form)**.
Dispatches among the six corner leaves and five J0 leaves using the exact case split
of Q45THEOREM24: trichotomy on frame-free kJ * Ω, weak X-high test at the end,
and trichotomy on s (resp. t). Every branch either closes with FaceChordView F 3
or witnesses a failing non-degeneracy condition in Q45Special F. -/
theorem q45_half {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (s t : ℝ)
    (hs0 : 0 < s)
    (ht : 0 < t)
    (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hsign : Q45HalfHyp F s t) :
    FaceChordView F 3 ∨ Q45Special F := by
  have sp_tie : Q45TieLocus x → Q45Special F := fun h => Or.inl h
  have sp_s3  : Q45S3Locus F → Q45Special F := fun h => Or.inr (Or.inl h)
  have sp_s4  : Q45S4Locus F → Q45Special F := fun h => Or.inr (Or.inr (Or.inl h))
  have sp_s2  : Q45S2Locus x → Q45Special F := fun h => Or.inr (Or.inr (Or.inr h))

  set kJ := det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6)
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
  have h_om := omega_ne_zero F
  have h_trich := lt_trichotomy (kJ * Ω) 0

  rcases h_trich with hk_neg | hk_zero | hk_pos

  · -- =========================================================================
    -- Branch K+: kJ * Ω < 0 (doc ρ0 kJ > 0)
    -- =========================================================================
    have h_Kplus_signs := hsign.1 hk_neg
    rcases le_or_gt s 1 with hs | hs

    · -- Subcase s ≤ 1: base ray E5 = e5 = x 5 - x 0
      have ha5 := h_Kplus_signs.1 hs
      by_cases h6hi : max ⟪x 4, x 5 - x 0⟫ ⟪x 2, x 5 - x 0⟫ ≤ ⟪x 6, x 5 - x 0⟫

      · -- Weak 6-high holds at e5: split s < 1 (B1) vs s = 1 (Bs1)
        rcases lt_or_eq_of_le hs with hs_lt | hs_eq

        · -- Leaf B1: s < 1
          by_cases htie : ¬ (⟪x 2, x 5 - x 0⟫ = ⟪x 4, x 5 - x 0⟫ ∧ ⟪x 4, x 5 - x 0⟫ = ⟪x 6, x 5 - x 0⟫)
          · by_cases hs3 : F.f 3 (x 2) ≠ F.f 3 (x 6)
            · by_cases hs4 : ⟪F.N 3, cross (x 0 - x 4) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4)⟫ ≠ 0 ∨
                ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 0 - x 4⟫ < 0 ∨
                ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 0, x 4 - x 0⟫ < 0
              · by_cases hs2 : ∀ i j : ZMod 4, i ≠ j →
                  ⟪quad (x 6) (x 4) (x 0) (x 2) i - quad (x 6) (x 4) (x 0) (x 2) j, x 5 - x 0⟫ ≠ 0 ∨
                  ⟪quad (x 6) (x 4) (x 0) (x 2) i - quad (x 6) (x 4) (x 0) (x 2) j, x 4 - x 0⟫ ≠ 0
                · exact Or.inl (q45_B1 F ha5 s t hs0 ht hst hdecomp hs_lt h6hi htie hs2 hs3 hs4)
                · exact Or.inr (sp_s2 (Or.inl hs2))
              · exact Or.inr (sp_s4 (Or.inl hs4))
            · have hs3_eq : F.f 3 (x 2) = F.f 3 (x 6) := by
                by_contra hc; exact hs3 hc
              exact Or.inr (sp_s3 hs3_eq)
          · have htie_eq : ⟪x 2, x 5 - x 0⟫ = ⟪x 4, x 5 - x 0⟫ ∧ ⟪x 4, x 5 - x 0⟫ = ⟪x 6, x 5 - x 0⟫ := by
              by_contra hc; exact htie hc
            exact Or.inr (sp_tie (Or.inl htie_eq))

        · -- Leaf Bs1: s = 1
          by_cases htie : ⟪x 2, x 5 - x 0⟫ ≠ ⟪x 6, x 5 - x 0⟫
          · by_cases hs3 : F.f 3 (x 2) ≠ F.f 3 (x 6)
            · by_cases hs4 : ⟪F.N 3, cross (x 0 - x 3) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 3)⟫ ≠ 0 ∨
                ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 3, x 0 - x 3⟫ < 0 ∨
                ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 0, x 3 - x 0⟫ < 0
              · by_cases hs2 : ∀ i j : ZMod 4, i ≠ j →
                  ⟪quad (x 6) (x 3) (x 0) (x 2) i - quad (x 6) (x 3) (x 0) (x 2) j, x 5 - x 0⟫ ≠ 0 ∨
                  ⟪quad (x 6) (x 3) (x 0) (x 2) i - quad (x 6) (x 3) (x 0) (x 2) j, x 4 - x 0⟫ ≠ 0
                · exact Or.inl (q45_Bs1 F ha5 s t ht hdecomp hs_eq h6hi htie hs2 hs3 hs4)
                · exact Or.inr (sp_s2 (Or.inr (Or.inl hs2)))
              · exact Or.inr (sp_s4 (Or.inr (Or.inl hs4)))
            · have hs3_eq : F.f 3 (x 2) = F.f 3 (x 6) := by
                by_contra hc; exact hs3 hc
              exact Or.inr (sp_s3 hs3_eq)
          · have htie_eq : ⟪x 2, x 5 - x 0⟫ = ⟪x 6, x 5 - x 0⟫ := by
              by_contra hc; exact htie hc
            exact Or.inr (sp_tie (Or.inr (Or.inl htie_eq)))

      · -- Weak 6-high fails at e5: Leaf K+ (s ≤ 1)
        have h6lo : min ⟪x 6, x 5 - x 0⟫ ⟪x 5, x 5 - x 0⟫ < max ⟪x 4, x 5 - x 0⟫ ⟪x 2, x 5 - x 0⟫ := by
          have h_not : ⟪x 6, x 5 - x 0⟫ < max ⟪x 4, x 5 - x 0⟫ ⟪x 2, x 5 - x 0⟫ := not_le.mp h6hi
          exact lt_of_le_of_lt (min_le_left _ _) h_not
        by_cases hs3 : F.f 3 (x 2) ≠ F.f 3 (x 6)
        · by_cases hs4 : ⟪F.N 3, cross (x 5 - x 4) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4)⟫ ≠ 0 ∨
            ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 5 - x 4⟫ < 0 ∨
            ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 4 - x 5⟫ < 0
          · by_cases hs2 : ∀ i j : ZMod 4, i ≠ j →
              ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0 ∨
              ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0
            · exact Or.inl (q45_Kplus_s_le_one F ha5 s t hs0 ht hst hdecomp hk_neg hs h6lo hs2 hs3 hs4)
            · exact Or.inr (sp_s2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hs2))))))))
          · exact Or.inr (sp_s4 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hs4)))))))
        · have hs3_eq : F.f 3 (x 2) = F.f 3 (x 6) := by
            by_contra hc; exact hs3 hc
          exact Or.inr (sp_s3 hs3_eq)

    · -- Subcase 1 < s: base ray E5 = e34 = x 3 - x 4
      have ha34 := h_Kplus_signs.2 hs
      by_cases h6hi : max ⟪x 4, x 3 - x 4⟫ ⟪x 2, x 3 - x 4⟫ ≤ min ⟪x 6, x 3 - x 4⟫ ⟪x 5, x 3 - x 4⟫

      · -- Weak 6-high holds at e34: Leaf B2
        by_cases htie : ¬ (⟪x 2, x 3 - x 4⟫ = ⟪x 5, x 3 - x 4⟫ ∧ ⟪x 5, x 3 - x 4⟫ = ⟪x 6, x 3 - x 4⟫)
        · by_cases hs3 : F.f 3 (x 2) ≠ F.f 3 (x 6)
          · by_cases hs4 : ⟪F.N 3, cross (x 5 - x 3) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 3)⟫ ≠ 0 ∨
              ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 3, x 5 - x 3⟫ < 0 ∨
              ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 3 - x 5⟫ < 0
            · by_cases hs2 : ∀ i j : ZMod 4, i ≠ j →
                ⟪quad (x 6) (x 3) (x 5) (x 2) i - quad (x 6) (x 3) (x 5) (x 2) j, x 3 - x 4⟫ ≠ 0 ∨
                ⟪quad (x 6) (x 3) (x 5) (x 2) i - quad (x 6) (x 3) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0
              · exact Or.inl (q45_B2 F ha34 s t ht hdecomp hs h6hi htie hs2 hs3 hs4)
              · exact Or.inr (sp_s2 (Or.inr (Or.inr (Or.inl hs2))))
            · exact Or.inr (sp_s4 (Or.inr (Or.inr (Or.inl hs4))))
          · have hs3_eq : F.f 3 (x 2) = F.f 3 (x 6) := by
              by_contra hc; exact hs3 hc
            exact Or.inr (sp_s3 hs3_eq)
        · have htie_eq : ⟪x 2, x 3 - x 4⟫ = ⟪x 5, x 3 - x 4⟫ ∧ ⟪x 5, x 3 - x 4⟫ = ⟪x 6, x 3 - x 4⟫ := by
            by_contra hc; exact htie hc
          exact Or.inr (sp_tie (Or.inr (Or.inr (Or.inl htie_eq))))

      · -- Weak 6-high fails at e34: Leaf K+ (1 < s)
        have h6lo : min ⟪x 6, x 3 - x 4⟫ ⟪x 5, x 3 - x 4⟫ < max ⟪x 4, x 3 - x 4⟫ ⟪x 2, x 3 - x 4⟫ := not_le.mp h6hi
        by_cases hs3 : F.f 3 (x 2) ≠ F.f 3 (x 6)
        · by_cases hs4 : ⟪F.N 3, cross (x 5 - x 4) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4)⟫ ≠ 0 ∨
            ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 5 - x 4⟫ < 0 ∨
            ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 4 - x 5⟫ < 0
          · by_cases hs2 : ∀ i j : ZMod 4, i ≠ j →
              ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 3 - x 4⟫ ≠ 0 ∨
              ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0
            · exact Or.inl (q45_Kplus_s_gt_one F ha34 s t hs0 ht hst hdecomp hk_neg hs h6lo hs2 hs3 hs4)
            · exact Or.inr (sp_s2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hs2)))))))))
          · exact Or.inr (sp_s4 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hs4)))))))
        · have hs3_eq : F.f 3 (x 2) = F.f 3 (x 6) := by
            by_contra hc; exact hs3 hc
          exact Or.inr (sp_s3 hs3_eq)

  · -- =========================================================================
    -- Branch K0: kJ * Ω = 0 (doc kJ = 0)
    -- =========================================================================
    have hk0 : kJ = 0 := by
      rcases mul_eq_zero.mp hk_zero with h1 | h2
      · exact h1
      · exact False.elim (h_om h2)
    have hK0_signs := hsign.2.2 hk0
    have ha4 := hK0_signs.1
    have ha5 := hK0_signs.2

    by_cases hs3 : F.f 3 (x 2) ≠ F.f 3 (x 6)
    · by_cases hs4 : ⟪F.N 3, cross (x 5 - x 4) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4)⟫ ≠ 0 ∨
        ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 5 - x 4⟫ < 0 ∨
        ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 4 - x 5⟫ < 0
      · by_cases hs2 : ∀ i j : ZMod 4, i ≠ j →
          ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0 ∨
          ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0
        · exact Or.inl (q45_K0 F ha4 ha5 s t hs0 ht hst hdecomp hk0 hs2 hs3 hs4)
        · exact Or.inr (sp_s2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hs2))))))))
      · exact Or.inr (sp_s4 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hs4)))))))
    · have hs3_eq : F.f 3 (x 2) = F.f 3 (x 6) := by
        by_contra hc; exact hs3 hc
      exact Or.inr (sp_s3 hs3_eq)

  · -- =========================================================================
    -- Branch K-: 0 < kJ * Ω (doc ρ0 kJ < 0)
    -- =========================================================================
    have h_Kminus_signs := hsign.2.1 hk_pos
    rcases le_or_gt t 1 with ht1_le | ht1_gt

    · -- Subcase t ≤ 1: base ray E4 = e4 = x 4 - x 0
      have ha4 := h_Kminus_signs.1 ht1_le
      by_cases h2hi : max ⟪x 6, x 4 - x 0⟫ ⟪x 5, x 4 - x 0⟫ ≤ ⟪x 2, x 4 - x 0⟫

      · -- Weak 2-high holds at e4: split t < 1 (C1) vs t = 1 (Ct1)
        rcases lt_or_eq_of_le ht1_le with ht_lt | ht_eq

        · -- Leaf C1: t < 1
          by_cases htie : ¬ (⟪x 2, x 4 - x 0⟫ = ⟪x 5, x 4 - x 0⟫ ∧ ⟪x 5, x 4 - x 0⟫ = ⟪x 6, x 4 - x 0⟫)
          · by_cases hs3 : F.f 3 (x 2) ≠ F.f 3 (x 6)
            · by_cases hs4 : ⟪F.N 3, cross (x 5 - x 0) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 0)⟫ ≠ 0 ∨
                ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 0, x 5 - x 0⟫ < 0 ∨
                ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 0 - x 5⟫ < 0
              · by_cases hs2 : ∀ i j : ZMod 4, i ≠ j →
                  ⟪quad (x 6) (x 0) (x 5) (x 2) i - quad (x 6) (x 0) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0 ∨
                  ⟪quad (x 6) (x 0) (x 5) (x 2) i - quad (x 6) (x 0) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0
                · exact Or.inl (q45_C1 F ha4 s t hs0 ht hst hdecomp ht_lt h2hi htie hs2 hs3 hs4)
                · exact Or.inr (sp_s2 (Or.inr (Or.inr (Or.inr (Or.inl hs2)))))
              · exact Or.inr (sp_s4 (Or.inr (Or.inr (Or.inr (Or.inl hs4)))))
            · have hs3_eq : F.f 3 (x 2) = F.f 3 (x 6) := by
                by_contra hc; exact hs3 hc
              exact Or.inr (sp_s3 hs3_eq)
          · have htie_eq : ⟪x 2, x 4 - x 0⟫ = ⟪x 5, x 4 - x 0⟫ ∧ ⟪x 5, x 4 - x 0⟫ = ⟪x 6, x 4 - x 0⟫ := by
              by_contra hc; exact htie hc
            exact Or.inr (sp_tie (Or.inr (Or.inr (Or.inr (Or.inl htie_eq)))))

        · -- Leaf Ct1: t = 1
          by_cases htie : ⟪x 2, x 4 - x 0⟫ ≠ ⟪x 6, x 4 - x 0⟫
          · by_cases hs3 : F.f 3 (x 2) ≠ F.f 3 (x 6)
            · by_cases hs4 : ⟪F.N 3, cross (x 3 - x 0) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 0)⟫ ≠ 0 ∨
                ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 0, x 3 - x 0⟫ < 0 ∨
                ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 3, x 0 - x 3⟫ < 0
              · by_cases hs2 : ∀ i j : ZMod 4, i ≠ j →
                  ⟪quad (x 6) (x 0) (x 3) (x 2) i - quad (x 6) (x 0) (x 3) (x 2) j, x 4 - x 0⟫ ≠ 0 ∨
                  ⟪quad (x 6) (x 0) (x 3) (x 2) i - quad (x 6) (x 0) (x 3) (x 2) j, x 5 - x 0⟫ ≠ 0
                · exact Or.inl (q45_Ct1 F ha4 s t hs0 hdecomp ht_eq h2hi htie hs2 hs3 hs4)
                · exact Or.inr (sp_s2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hs2))))))
              · exact Or.inr (sp_s4 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hs4))))))
            · have hs3_eq : F.f 3 (x 2) = F.f 3 (x 6) := by
                by_contra hc; exact hs3 hc
              exact Or.inr (sp_s3 hs3_eq)
          · have htie_eq : ⟪x 2, x 4 - x 0⟫ = ⟪x 6, x 4 - x 0⟫ := by
              by_contra hc; exact htie hc
            exact Or.inr (sp_tie (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl htie_eq))))))

      · -- Weak 2-high fails at e4: Leaf K- (t ≤ 1)
        have h2lo : min ⟪x 4, x 4 - x 0⟫ ⟪x 2, x 4 - x 0⟫ < max ⟪x 6, x 4 - x 0⟫ ⟪x 5, x 4 - x 0⟫ := by
          have h_not : ⟪x 2, x 4 - x 0⟫ < max ⟪x 6, x 4 - x 0⟫ ⟪x 5, x 4 - x 0⟫ := not_le.mp h2hi
          exact lt_of_le_of_lt (min_le_right _ _) h_not
        by_cases hs3 : F.f 3 (x 2) ≠ F.f 3 (x 6)
        · by_cases hs4 : ⟪F.N 3, cross (x 5 - x 4) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4)⟫ ≠ 0 ∨
            ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 5 - x 4⟫ < 0 ∨
            ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 4 - x 5⟫ < 0
          · by_cases hs2 : ∀ i j : ZMod 4, i ≠ j →
              ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0 ∨
              ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0
            · have hs2' : ∀ i j : ZMod 4, i ≠ j →
                ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0 ∨
                ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0 := by
                intro i j hij; exact (hs2 i j hij).symm
              exact Or.inl (q45_Kminus_t_le_one F ha4 s t hs0 ht hst hdecomp hk_pos ht1_le h2lo hs2' hs3 hs4)
            · exact Or.inr (sp_s2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hs2))))))))
          · exact Or.inr (sp_s4 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hs4)))))))
        · have hs3_eq : F.f 3 (x 2) = F.f 3 (x 6) := by
            by_contra hc; exact hs3 hc
          exact Or.inr (sp_s3 hs3_eq)

    · -- Subcase 1 < t: base ray E4 = e35 = x 3 - x 5
      have ha35 := h_Kminus_signs.2 ht1_gt
      by_cases h2hi : max ⟪x 6, x 3 - x 5⟫ ⟪x 5, x 3 - x 5⟫ ≤ min ⟪x 2, x 3 - x 5⟫ ⟪x 4, x 3 - x 5⟫

      · -- Weak 2-high holds at e35: Leaf C2
        by_cases htie : ¬ (⟪x 2, x 3 - x 5⟫ = ⟪x 4, x 3 - x 5⟫ ∧ ⟪x 4, x 3 - x 5⟫ = ⟪x 6, x 3 - x 5⟫)
        · by_cases hs3 : F.f 3 (x 2) ≠ F.f 3 (x 6)
          · by_cases hs4 : ⟪F.N 3, cross (x 3 - x 4) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4)⟫ ≠ 0 ∨
              ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 3 - x 4⟫ < 0 ∨
              ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 3, x 4 - x 3⟫ < 0
            · by_cases hs2 : ∀ i j : ZMod 4, i ≠ j →
                ⟪quad (x 6) (x 4) (x 3) (x 2) i - quad (x 6) (x 4) (x 3) (x 2) j, x 3 - x 5⟫ ≠ 0 ∨
                ⟪quad (x 6) (x 4) (x 3) (x 2) i - quad (x 6) (x 4) (x 3) (x 2) j, x 4 - x 0⟫ ≠ 0
              · exact Or.inl (q45_C2 F ha35 s t hs0 hdecomp ht1_gt h2hi htie hs2 hs3 hs4)
              · exact Or.inr (sp_s2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hs2)))))))
            · exact Or.inr (sp_s4 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hs4)))))))
          · have hs3_eq : F.f 3 (x 2) = F.f 3 (x 6) := by
              by_contra hc; exact hs3 hc
            exact Or.inr (sp_s3 hs3_eq)
        · have htie_eq : ⟪x 2, x 3 - x 5⟫ = ⟪x 4, x 3 - x 5⟫ ∧ ⟪x 4, x 3 - x 5⟫ = ⟪x 6, x 3 - x 5⟫ := by
            by_contra hc; exact htie hc
          exact Or.inr (sp_tie (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr htie_eq))))))

      · -- Weak 2-high fails at e35: Leaf K- (1 < t)
        have h2lo : min ⟪x 4, x 3 - x 5⟫ ⟪x 2, x 3 - x 5⟫ < max ⟪x 6, x 3 - x 5⟫ ⟪x 5, x 3 - x 5⟫ := by
          have h_not := not_le.mp h2hi
          rw [min_comm]
          exact h_not
        by_cases hs3 : F.f 3 (x 2) ≠ F.f 3 (x 6)
        · by_cases hs4 : ⟪F.N 3, cross (x 5 - x 4) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4)⟫ ≠ 0 ∨
            ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 5 - x 4⟫ < 0 ∨
            ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 4 - x 5⟫ < 0
          · by_cases hs2 : ∀ i j : ZMod 4, i ≠ j →
              ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 3 - x 5⟫ ≠ 0 ∨
              ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0
            · exact Or.inl (q45_Kminus_t_gt_one F ha35 s t hs0 ht hst hdecomp hk_pos ht1_gt h2lo hs2 hs3 hs4)
            · exact Or.inr (sp_s2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hs2)))))))))
          · exact Or.inr (sp_s4 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hs4)))))))
        · have hs3_eq : F.f 3 (x 2) = F.f 3 (x 6) := by
            by_contra hc; exact hs3 hc
          exact Or.inr (sp_s3 hs3_eq)

/-- Global geometric version of `q45_half` where `s, t` are obtained internally via `lemmaM_quad_decomp F`. -/
theorem q45_half_geom {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hsign : ∀ s t : ℝ, 0 < s → 0 < t → 1 < s + t →
      x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0) → Q45HalfHyp F s t) :
    FaceChordView F 3 ∨ Q45Special F := by
  obtain ⟨s, t, hs0, ht, hst, hdecomp⟩ := lemmaM_quad_decomp F
  have hs := hsign s t hs0 ht hst hdecomp
  exact q45_half F s t hs0 ht hst hdecomp hs

/-- **Theorem AH2: Local Q45 Dispatcher (Full a4, a5 > 1 form)**.
For every Type-24 solid with `⟪F.N 5, x 4 - x 0⟫ < 0` and `⟪F.N 5, x 5 - x 0⟫ < 0`,
face 3 admits a FaceChordView, unless the solid lies on the Q45Special locus. -/
theorem q45 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha4 : ⟪F.N 5, x 4 - x 0⟫ < 0)
    (ha5 : ⟪F.N 5, x 5 - x 0⟫ < 0) :
    FaceChordView F 3 ∨ Q45Special F := by
  obtain ⟨s, t, hs0, ht, hst, hdecomp⟩ := lemmaM_quad_decomp F
  have hsign : Q45HalfHyp F s t := by
    refine ⟨fun _ => ⟨fun _ => ha5, fun hs1 => ?_⟩, fun _ => ⟨fun _ => ha4, fun ht1 => ?_⟩, fun _ => ⟨ha4, ha5⟩⟩
    · have hd : x 3 - x 4 = (s - 1) • (x 4 - x 0) + t • (x 5 - x 0) := by
        calc
          x 3 - x 4 = (x 3 - x 0) - (x 4 - x 0) := by abel
          _ = (s • (x 4 - x 0) + t • (x 5 - x 0)) - (x 4 - x 0) := by rw [hdecomp]
          _ = (s - 1) • (x 4 - x 0) + t • (x 5 - x 0) := by
            ext j; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
      rw [hd, inner_add_right, real_inner_smul_right, real_inner_smul_right]
      have h1 : (s - 1) * ⟪F.N 5, x 4 - x 0⟫ < 0 := mul_neg_of_pos_of_neg (by linarith) ha4
      have h2 : t * ⟪F.N 5, x 5 - x 0⟫ < 0 := mul_neg_of_pos_of_neg ht ha5
      linarith
    · have hd : x 3 - x 5 = s • (x 4 - x 0) + (t - 1) • (x 5 - x 0) := by
        calc
          x 3 - x 5 = (x 3 - x 0) - (x 5 - x 0) := by abel
          _ = (s • (x 4 - x 0) + t • (x 5 - x 0)) - (x 5 - x 0) := by rw [hdecomp]
          _ = s • (x 4 - x 0) + (t - 1) • (x 5 - x 0) := by
            ext j; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
      rw [hd, inner_add_right, real_inner_smul_right, real_inner_smul_right]
      have h1 : s * ⟪F.N 5, x 4 - x 0⟫ < 0 := mul_neg_of_pos_of_neg hs0 ha4
      have h2 : (t - 1) * ⟪F.N 5, x 5 - x 0⟫ < 0 := mul_neg_of_pos_of_neg (by linarith) ha5
      linarith
  exact q45_half F s t hs0 ht hst hdecomp hsign

/-- **Theorem AI1: Rupert Wiring from Q45-Half (Plan Item 10)**.
Wires the local Q45-Half dispatcher into the three-circle cover `isRupert_cover24`
on facet 3 (`0345`), establishing that every Type-24 solid satisfying the Q45-Half
hypothesis is Rupert unless it lies on the special locus `Q45Special F`. -/
theorem isRupert_q45_half {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hsign : ∀ s t : ℝ, 0 < s → 0 < t → 1 < s + t →
      x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0) → Q45HalfHyp F s t) :
    IsRupert (univ.image x) ∨ Q45Special F := by
  rcases q45_half_geom F hsign with hfc | hsp
  · exact Or.inl (isRupert_of_faceChordView F hfc)
  · exact Or.inr hsp

/-- **Corollary AI1: Rupert Wiring from Q45 ($a_4, a_5 > 1$ form)**.
For every Type-24 solid with `a_4 > 1` and `a_5 > 1` (`ha4, ha5`),
the solid is Rupert unless it lies on `Q45Special F`. -/
theorem isRupert_q45 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha4 : ⟪F.N 5, x 4 - x 0⟫ < 0)
    (ha5 : ⟪F.N 5, x 5 - x 0⟫ < 0) :
    IsRupert (univ.image x) ∨ Q45Special F := by
  rcases q45 F ha4 ha5 with hfc | hsp
  · exact Or.inl (isRupert_of_faceChordView F hfc)
  · exact Or.inr hsp

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

theorem q45Special'_imp_q45Special {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x}
    (h : Q45Special' F) : Q45Special F := by
  rcases h with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | h | h
  · rcases h with h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases h with h | h | h | h
    · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · rcases h with h | h | h | h
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · rcases h with h | h | h | h
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
  · rcases h with h | h | h | h | h | h | h
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · rcases h with h | h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))

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
