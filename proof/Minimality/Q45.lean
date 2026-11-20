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
2. `q45`: The primary local dispatcher theorem with hypotheses `ha4, ha5`.
3. `q45_half`: The refined dispatcher with the weakest branch-specific sign hypotheses.
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

/-- **Theorem AH2: Local Q45 Dispatcher (Full a4, a5 > 1 form)**.
For every Type-24 solid with `⟪F.N 5, x 4 - x 0⟫ < 0` and `⟪F.N 5, x 5 - x 0⟫ < 0`,
face 3 admits a FaceChordView, unless the solid lies on the Q45Special locus. -/
theorem q45 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha4 : ⟪F.N 5, x 4 - x 0⟫ < 0)
    (ha5 : ⟪F.N 5, x 5 - x 0⟫ < 0) :
    FaceChordView F 3 ∨ Q45Special F := sorry

/-- Weakest a-hypothesis predicate for the Q45 branches:
Each branch receives only the normal sign at the specific view(s) it inspects. -/
def Q45HalfHyp {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (s t : ℝ) : Prop :=
  (det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) < 0 →
    ((s ≤ 1 → ⟪F.N 5, x 5 - x 0⟫ < 0) ∧ (1 < s → ⟪F.N 5, x 3 - x 4⟫ < 0))) ∧
  (0 < det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) →
    ((t ≤ 1 → ⟪F.N 5, x 4 - x 0⟫ < 0) ∧ (1 < t → ⟪F.N 5, x 3 - x 5⟫ < 0))) ∧
  (det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) = 0 →
    (⟪F.N 5, x 4 - x 0⟫ < 0 ∧ ⟪F.N 5, x 5 - x 0⟫ < 0))

/-- **Theorem AH3: Local Q45-Half Dispatcher (Weakest a-Hypothesis Form)**.
Same conclusion as `q45`, but requiring only `Q45HalfHyp F s t` rather than both `ha4` and `ha5`. -/
theorem q45_half {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (s t : ℝ)
    (hs0 : 0 < s)
    (ht : 0 < t)
    (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hsign : Q45HalfHyp F s t) :
    FaceChordView F 3 ∨ Q45Special F := sorry

/-- Global geometric version of `q45_half` where `s, t` are obtained internally via `lemmaM_quad_decomp F`. -/
theorem q45_half_geom {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hsign : ∀ s t : ℝ, 0 < s → 0 < t → 1 < s + t →
      x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0) → Q45HalfHyp F s t) :
    FaceChordView F 3 ∨ Q45Special F := sorry

end Minimality.T24.Q45
