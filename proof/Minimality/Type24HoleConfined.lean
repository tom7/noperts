module

public import Minimality.Type24HoleReduce
public import Minimality.Type24QuadNormal
public import Minimality.Type24MerC6C10

/-!
# Type 24: confinement of `Hole24` by the proved region lemmas

`Hole24` (Type24HoleReduce.lean) carries the negated generic leaves `¬ AnyFaceChord F` and `¬ LexAny F` (inside
`Hole24R` / `Hole24Q45Special`, Type24Hole.lean).  Every proved region lemma whose conclusion is one of these
leaves therefore confines the hole to the complement of its hypotheses.  This file states each lemma's hypotheses
as one named Prop and proves `hole24_confined`: on `Hole24` every one of them fails.

* `QNHyp`: `QN.lexAny_quadNormal` (Type24QuadNormal.lean; conclusion `LexAny F`), without its `CbarIn x`
  hypothesis, which `Hole24` supplies (`hole24_leaves`).
* `MerC*Hyp`: the 25 meridian / tie-view lemmas `Mer.faceChordView_C*` (Type24MerC1.lean, Type24MerC2C5.lean,
  Type24MerC6C10.lean; conclusion `FaceChordView F t`, hence `AnyFaceChord F`).  The view of C9, C9', C10, C10'
  is a parameter `u` (any view on the facet circle), so the confinement is `∀ u, ¬ MerC9Hyp F u`.

No new mathematics: each conjunct is the contrapositive of a proved lemma.  The point is that the hole statement
now lists, in one place, every region the proved lemmas remove.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset Filter Topology
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.RimFromSigns
  Minimality.T24.Mer

namespace Minimality.T24

/-! ### Quad-normal LexAny region (Type24QuadNormal.lean) -/

/-- Hypotheses of `QN.lexAny_quadNormal` (Type24QuadNormal.lean; conclusion `RCell.LexAny F`) other than
`CbarIn x`: `hob` (the corner-edge Gram entries at vertex 1 are `≤ 0`), `hnB`, `hnC`, `hTE` (not two-ear). -/
def QNHyp {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  (⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0 ∧ ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0 ∧ ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0) ∧
  F.f 3 (x 1) ≤ F.f 3 (x 2) ∧ F.f 3 (x 1) ≤ F.f 3 (x 6) ∧ ¬ QN.TwoEar F

/-! ### Meridian case C1 (Type24MerC1.lean): 5-rim at `mer F 1 7`, and its `sym24` mirror -/

/-- Hypotheses of `Mer.faceChordView_C1` (Type24MerC1.lean; conclusion `FaceChordView F 7`):
`hM1`, `hM2`, `hinj`, `hz`, `hM4`. -/
def MerC1Hyp {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  (⟪F.N 0, mer F 1 7⟫ < 0 ∧ 0 < ⟪F.N 5, mer F 1 7⟫ ∧ ⟪F.N 6, mer F 1 7⟫ < 0 ∧
      ⟪F.N 3, mer F 1 7⟫ < 0 ∧ 0 < ⟪F.N 8, mer F 1 7⟫ ∧ 0 < ⟪F.N 4, mer F 1 7⟫) ∧
  (0 < ⟪x 6 - x 2, cross (F.N 7) (F.N 1)⟫ * ⟪x 3 - x 6, cross (F.N 7) (F.N 1)⟫) ∧
  (Function.Injective fun i : ZMod 5 => ⟪x (rimC1 i), mer F 1 7⟫) ∧
  (UniOrSep (fun i : ZMod 5 => x (rimC1 i)) (mer F 1 7)) ∧
  ((F.f 7 (x 0) < F.f 7 (x 1) ∧ F.f 7 (x 0) < F.f 7 (x 4) ∧
        (⟪F.N 7, cross (x 3 - x 2) (x 0 - x 2)⟫ ≠ 0 ∨ ⟪x 0 - x 2, x 3 - x 2⟫ < 0 ∨
          ⟪x 0 - x 3, x 2 - x 3⟫ < 0)) ∨
      (F.f 7 (x 4) < F.f 7 (x 0) ∧ F.f 7 (x 4) < F.f 7 (x 1) ∧
        (⟪F.N 7, cross (x 3 - x 2) (x 4 - x 2)⟫ ≠ 0 ∨ ⟪x 4 - x 2, x 3 - x 2⟫ < 0 ∨
          ⟪x 4 - x 3, x 2 - x 3⟫ < 0)) ∨
      (F.f 7 (x 1) < F.f 7 (x 0) ∧ F.f 7 (x 1) < F.f 7 (x 4) ∧
        (⟪F.N 7, cross (x 3 - x 2) (x 1 - x 2)⟫ ≠ 0 ∨ ⟪x 1 - x 2, x 3 - x 2⟫ < 0 ∨
          ⟪x 1 - x 3, x 2 - x 3⟫ < 0)))

/-- Hypotheses of `Mer.faceChordView_C1'` (Type24MerC1.lean; conclusion `FaceChordView F 7`):
`hM1`, `hM2`, `hinj`, `hz`, `hM4`. -/
def MerC1Hyp' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  (⟪F.N 1, mer F 0 7⟫ < 0 ∧ 0 < ⟪F.N 5, mer F 0 7⟫ ∧ ⟪F.N 8, mer F 0 7⟫ < 0 ∧
      ⟪F.N 3, mer F 0 7⟫ < 0 ∧ 0 < ⟪F.N 6, mer F 0 7⟫ ∧ 0 < ⟪F.N 2, mer F 0 7⟫) ∧
  (0 < ⟪x 2 - x 6, cross (F.N 7) (F.N 0)⟫ * ⟪x 3 - x 2, cross (F.N 7) (F.N 0)⟫) ∧
  (Function.Injective fun i : ZMod 5 => ⟪x (rimC1' i), mer F 0 7⟫) ∧
  (UniOrSep (fun i : ZMod 5 => x (rimC1' i)) (mer F 0 7)) ∧
  ((F.f 7 (x 0) < F.f 7 (x 1) ∧ F.f 7 (x 0) < F.f 7 (x 5) ∧
        (⟪F.N 7, cross (x 3 - x 6) (x 0 - x 6)⟫ ≠ 0 ∨ ⟪x 0 - x 6, x 3 - x 6⟫ < 0 ∨
          ⟪x 0 - x 3, x 6 - x 3⟫ < 0)) ∨
      (F.f 7 (x 5) < F.f 7 (x 0) ∧ F.f 7 (x 5) < F.f 7 (x 1) ∧
        (⟪F.N 7, cross (x 3 - x 6) (x 5 - x 6)⟫ ≠ 0 ∨ ⟪x 5 - x 6, x 3 - x 6⟫ < 0 ∨
          ⟪x 5 - x 3, x 6 - x 3⟫ < 0)) ∨
      (F.f 7 (x 1) < F.f 7 (x 0) ∧ F.f 7 (x 1) < F.f 7 (x 5) ∧
        (⟪F.N 7, cross (x 3 - x 6) (x 1 - x 6)⟫ ≠ 0 ∨ ⟪x 1 - x 6, x 3 - x 6⟫ < 0 ∨
          ⟪x 1 - x 3, x 6 - x 3⟫ < 0)))

/-! ### Meridian cases C2-C5 and mirrors (Type24MerC2C5.lean) -/

/-- Hypotheses of `Mer.faceChordView_C2` (Type24MerC2C5.lean; conclusion `FaceChordView F 3`):
`hM1`, `hM2`, `hguard`, `hlev`, `hM4`. -/
def MerC2Hyp {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  (0 < ⟪F.N 0, mer F 2 3⟫ ∧ ⟪F.N 1, mer F 2 3⟫ < 0 ∧ ⟪F.N 5, mer F 2 3⟫ < 0) ∧
  (0 < ⟪x 3 - x 5, x 0 - x 5⟫ ∧ 0 < ⟪x 3 - x 0, x 5 - x 0⟫ ∧
      0 < ⟪x 4 - x 5, x 0 - x 5⟫ ∧ 0 < ⟪x 4 - x 0, x 5 - x 0⟫) ∧
  (⟪x 2 - x 1, mer F 2 3⟫ ≠ 0 ∨ ⟪x 2 - x 1, x 0 - x 5⟫ ≠ 0) ∧
  ((⟪x 2 - x 5, mer F 2 3⟫ ≠ 0 ∨ ⟪x 1 - x 5, mer F 2 3⟫ ≠ 0) ∧
      (⟪x 2 - x 5, mer F 2 3⟫ ≠ 0 ∨
        ⟪x 2 - x 5, x 0 - x 5⟫ ≠ 0 ∧ ⟪x 2 - x 0, x 0 - x 5⟫ ≠ 0) ∧
      (⟪x 1 - x 5, mer F 2 3⟫ ≠ 0 ∨
        ⟪x 1 - x 5, x 0 - x 5⟫ ≠ 0 ∧ ⟪x 1 - x 0, x 0 - x 5⟫ ≠ 0)) ∧
  ((F.f 3 (x 1) < F.f 3 (x 2) ∧
        (⟪F.N 3, cross (x 0 - x 5) (x 1 - x 5)⟫ ≠ 0 ∨ ⟪x 1 - x 5, x 0 - x 5⟫ < 0 ∨
          ⟪x 1 - x 0, x 5 - x 0⟫ < 0)) ∨
      (F.f 3 (x 2) < F.f 3 (x 1) ∧
        (⟪F.N 3, cross (x 0 - x 5) (x 2 - x 5)⟫ ≠ 0 ∨ ⟪x 2 - x 5, x 0 - x 5⟫ < 0 ∨
          ⟪x 2 - x 0, x 5 - x 0⟫ < 0)))

/-- Hypotheses of `Mer.faceChordView_C2'` (Type24MerC2C5.lean; conclusion `FaceChordView F 3`):
`hM1`, `hM2`, `hguard`, `hlev`, `hM4`. -/
def MerC2Hyp' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  (0 < ⟪F.N 1, mer F 4 3⟫ ∧ ⟪F.N 0, mer F 4 3⟫ < 0 ∧ ⟪F.N 5, mer F 4 3⟫ < 0) ∧
  (0 < ⟪x 3 - x 4, x 0 - x 4⟫ ∧ 0 < ⟪x 3 - x 0, x 4 - x 0⟫ ∧
      0 < ⟪x 5 - x 4, x 0 - x 4⟫ ∧ 0 < ⟪x 5 - x 0, x 4 - x 0⟫) ∧
  (⟪x 6 - x 1, mer F 4 3⟫ ≠ 0 ∨ ⟪x 6 - x 1, x 0 - x 4⟫ ≠ 0) ∧
  ((⟪x 6 - x 4, mer F 4 3⟫ ≠ 0 ∨ ⟪x 1 - x 4, mer F 4 3⟫ ≠ 0) ∧
      (⟪x 6 - x 4, mer F 4 3⟫ ≠ 0 ∨
        ⟪x 6 - x 4, x 0 - x 4⟫ ≠ 0 ∧ ⟪x 6 - x 0, x 0 - x 4⟫ ≠ 0) ∧
      (⟪x 1 - x 4, mer F 4 3⟫ ≠ 0 ∨
        ⟪x 1 - x 4, x 0 - x 4⟫ ≠ 0 ∧ ⟪x 1 - x 0, x 0 - x 4⟫ ≠ 0)) ∧
  ((F.f 3 (x 1) < F.f 3 (x 6) ∧
        (⟪F.N 3, cross (x 0 - x 4) (x 1 - x 4)⟫ ≠ 0 ∨ ⟪x 1 - x 4, x 0 - x 4⟫ < 0 ∨
          ⟪x 1 - x 0, x 4 - x 0⟫ < 0)) ∨
      (F.f 3 (x 6) < F.f 3 (x 1) ∧
        (⟪F.N 3, cross (x 0 - x 4) (x 6 - x 4)⟫ ≠ 0 ∨ ⟪x 6 - x 4, x 0 - x 4⟫ < 0 ∨
          ⟪x 6 - x 0, x 4 - x 0⟫ < 0)))

/-- Hypotheses of `Mer.faceChordView_C3` (Type24MerC2C5.lean; conclusion `FaceChordView F 1`):
`hM1`, `hM2`, `hguard`, `hlev`, `hM4`. -/
def MerC3Hyp {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  (0 < ⟪F.N 3, mer F 4 1⟫ ∧ 0 < ⟪F.N 8, mer F 4 1⟫ ∧
      ⟪F.N 2, mer F 4 1⟫ < 0 ∧ ⟪F.N 6, mer F 4 1⟫ < 0 ∧ ⟪F.N 7, mer F 4 1⟫ < 0) ∧
  (0 < ⟪x 1 - x 6, x 0 - x 6⟫ ∧ 0 < ⟪x 1 - x 0, x 6 - x 0⟫) ∧
  (⟪x 3 - x 5, mer F 4 1⟫ ≠ 0 ∨ ⟪x 3 - x 5, x 0 - x 6⟫ ≠ 0) ∧
  ((⟪x 3 - x 6, mer F 4 1⟫ ≠ 0 ∨ ⟪x 5 - x 6, mer F 4 1⟫ ≠ 0) ∧
      (⟪x 3 - x 6, mer F 4 1⟫ ≠ 0 ∨
        ⟪x 3 - x 6, x 0 - x 6⟫ ≠ 0 ∧ ⟪x 3 - x 0, x 0 - x 6⟫ ≠ 0) ∧
      (⟪x 5 - x 6, mer F 4 1⟫ ≠ 0 ∨
        ⟪x 5 - x 6, x 0 - x 6⟫ ≠ 0 ∧ ⟪x 5 - x 0, x 0 - x 6⟫ ≠ 0)) ∧
  ((F.f 1 (x 3) < F.f 1 (x 5) ∧
        (⟪F.N 1, cross (x 0 - x 6) (x 3 - x 6)⟫ ≠ 0 ∨ ⟪x 3 - x 6, x 0 - x 6⟫ < 0 ∨
          ⟪x 3 - x 0, x 6 - x 0⟫ < 0)) ∨
      (F.f 1 (x 5) < F.f 1 (x 3) ∧
        (⟪F.N 1, cross (x 0 - x 6) (x 5 - x 6)⟫ ≠ 0 ∨ ⟪x 5 - x 6, x 0 - x 6⟫ < 0 ∨
          ⟪x 5 - x 0, x 6 - x 0⟫ < 0)))

/-- Hypotheses of `Mer.faceChordView_C3'` (Type24MerC2C5.lean; conclusion `FaceChordView F 0`):
`hM1`, `hM2`, `hguard`, `hlev`, `hM4`. -/
def MerC3Hyp' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  (0 < ⟪F.N 3, mer F 2 0⟫ ∧ 0 < ⟪F.N 6, mer F 2 0⟫ ∧
      ⟪F.N 4, mer F 2 0⟫ < 0 ∧ ⟪F.N 8, mer F 2 0⟫ < 0 ∧ ⟪F.N 7, mer F 2 0⟫ < 0) ∧
  (0 < ⟪x 1 - x 2, x 0 - x 2⟫ ∧ 0 < ⟪x 1 - x 0, x 2 - x 0⟫) ∧
  (⟪x 3 - x 4, mer F 2 0⟫ ≠ 0 ∨ ⟪x 3 - x 4, x 0 - x 2⟫ ≠ 0) ∧
  ((⟪x 3 - x 2, mer F 2 0⟫ ≠ 0 ∨ ⟪x 4 - x 2, mer F 2 0⟫ ≠ 0) ∧
      (⟪x 3 - x 2, mer F 2 0⟫ ≠ 0 ∨
        ⟪x 3 - x 2, x 0 - x 2⟫ ≠ 0 ∧ ⟪x 3 - x 0, x 0 - x 2⟫ ≠ 0) ∧
      (⟪x 4 - x 2, mer F 2 0⟫ ≠ 0 ∨
        ⟪x 4 - x 2, x 0 - x 2⟫ ≠ 0 ∧ ⟪x 4 - x 0, x 0 - x 2⟫ ≠ 0)) ∧
  ((F.f 0 (x 3) < F.f 0 (x 4) ∧
        (⟪F.N 0, cross (x 0 - x 2) (x 3 - x 2)⟫ ≠ 0 ∨ ⟪x 3 - x 2, x 0 - x 2⟫ < 0 ∨
          ⟪x 3 - x 0, x 2 - x 0⟫ < 0)) ∨
      (F.f 0 (x 4) < F.f 0 (x 3) ∧
        (⟪F.N 0, cross (x 0 - x 2) (x 4 - x 2)⟫ ≠ 0 ∨ ⟪x 4 - x 2, x 0 - x 2⟫ < 0 ∨
          ⟪x 4 - x 0, x 2 - x 0⟫ < 0)))

/-- Hypotheses of `Mer.faceChordView_C4` (Type24MerC2C5.lean; conclusion `FaceChordView F 2`):
`hM1`, `hM2`, `hguard`, `hlev`, `hM4`. -/
def MerC4Hyp {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  (⟪F.N 7, mer F 0 2⟫ < 0 ∧ ⟪F.N 8, mer F 0 2⟫ < 0 ∧
      0 < ⟪F.N 5, mer F 0 2⟫ ∧ 0 < ⟪F.N 4, mer F 0 2⟫) ∧
  (0 < ⟪x 5 - x 0, x 2 - x 0⟫ ∧ 0 < ⟪x 5 - x 2, x 0 - x 2⟫) ∧
  (⟪x 4 - x 6, mer F 0 2⟫ ≠ 0 ∨ ⟪x 4 - x 6, x 2 - x 0⟫ ≠ 0) ∧
  ((⟪x 4 - x 0, mer F 0 2⟫ ≠ 0 ∨ ⟪x 6 - x 0, mer F 0 2⟫ ≠ 0) ∧
      (⟪x 4 - x 0, mer F 0 2⟫ ≠ 0 ∨
        ⟪x 4 - x 0, x 2 - x 0⟫ ≠ 0 ∧ ⟪x 4 - x 2, x 2 - x 0⟫ ≠ 0) ∧
      (⟪x 6 - x 0, mer F 0 2⟫ ≠ 0 ∨
        ⟪x 6 - x 0, x 2 - x 0⟫ ≠ 0 ∧ ⟪x 6 - x 2, x 2 - x 0⟫ ≠ 0)) ∧
  ((F.f 2 (x 6) < F.f 2 (x 4) ∧
        (⟪F.N 2, cross (x 2 - x 0) (x 6 - x 0)⟫ ≠ 0 ∨ ⟪x 6 - x 0, x 2 - x 0⟫ < 0 ∨
          ⟪x 6 - x 2, x 0 - x 2⟫ < 0)) ∨
      (F.f 2 (x 4) < F.f 2 (x 6) ∧
        (⟪F.N 2, cross (x 2 - x 0) (x 4 - x 0)⟫ ≠ 0 ∨ ⟪x 4 - x 0, x 2 - x 0⟫ < 0 ∨
          ⟪x 4 - x 2, x 0 - x 2⟫ < 0)))

/-- Hypotheses of `Mer.faceChordView_C4'` (Type24MerC2C5.lean; conclusion `FaceChordView F 4`):
`hM1`, `hM2`, `hguard`, `hlev`, `hM4`. -/
def MerC4Hyp' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  (⟪F.N 7, mer F 1 4⟫ < 0 ∧ ⟪F.N 6, mer F 1 4⟫ < 0 ∧
      0 < ⟪F.N 5, mer F 1 4⟫ ∧ 0 < ⟪F.N 2, mer F 1 4⟫) ∧
  (0 < ⟪x 4 - x 0, x 6 - x 0⟫ ∧ 0 < ⟪x 4 - x 6, x 0 - x 6⟫) ∧
  (⟪x 5 - x 2, mer F 1 4⟫ ≠ 0 ∨ ⟪x 5 - x 2, x 6 - x 0⟫ ≠ 0) ∧
  ((⟪x 5 - x 0, mer F 1 4⟫ ≠ 0 ∨ ⟪x 2 - x 0, mer F 1 4⟫ ≠ 0) ∧
      (⟪x 5 - x 0, mer F 1 4⟫ ≠ 0 ∨
        ⟪x 5 - x 0, x 6 - x 0⟫ ≠ 0 ∧ ⟪x 5 - x 6, x 6 - x 0⟫ ≠ 0) ∧
      (⟪x 2 - x 0, mer F 1 4⟫ ≠ 0 ∨
        ⟪x 2 - x 0, x 6 - x 0⟫ ≠ 0 ∧ ⟪x 2 - x 6, x 6 - x 0⟫ ≠ 0)) ∧
  ((F.f 4 (x 2) < F.f 4 (x 5) ∧
        (⟪F.N 4, cross (x 6 - x 0) (x 2 - x 0)⟫ ≠ 0 ∨ ⟪x 2 - x 0, x 6 - x 0⟫ < 0 ∨
          ⟪x 2 - x 6, x 0 - x 6⟫ < 0)) ∨
      (F.f 4 (x 5) < F.f 4 (x 2) ∧
        (⟪F.N 4, cross (x 6 - x 0) (x 5 - x 0)⟫ ≠ 0 ∨ ⟪x 5 - x 0, x 6 - x 0⟫ < 0 ∨
          ⟪x 5 - x 6, x 0 - x 6⟫ < 0)))

/-- Hypotheses of `Mer.faceChordView_C5` (Type24MerC2C5.lean; conclusion `FaceChordView F 2`):
`hM1`, `hM2`, `hinj`, `hz`, `hM4`. -/
def MerC5Hyp {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  (⟪F.N 5, mer F 4 2⟫ < 0 ∧ ⟪F.N 6, mer F 4 2⟫ < 0 ∧
      ⟪F.N 7, mer F 4 2⟫ < 0 ∧ 0 < ⟪F.N 1, mer F 4 2⟫ ∧ 0 < ⟪F.N 8, mer F 4 2⟫) ∧
  (0 < ⟪x 0 - x 2, cross (F.N 2) (F.N 4)⟫ * ⟪x 5 - x 0, cross (F.N 2) (F.N 4)⟫) ∧
  (Function.Injective fun i : ZMod 5 => ⟪x (rimC5 i), mer F 4 2⟫) ∧
  (UniOrSep (fun i : ZMod 5 => x (rimC5 i)) (mer F 4 2)) ∧
  ((F.f 2 (x 6) < F.f 2 (x 1) ∧ F.f 2 (x 6) < F.f 2 (x 3) ∧
        (⟪F.N 2, cross (x 5 - x 2) (x 6 - x 2)⟫ ≠ 0 ∨ ⟪x 6 - x 2, x 5 - x 2⟫ < 0 ∨
          ⟪x 6 - x 5, x 2 - x 5⟫ < 0)) ∨
      (F.f 2 (x 3) < F.f 2 (x 1) ∧ F.f 2 (x 3) < F.f 2 (x 6) ∧
        (⟪F.N 2, cross (x 5 - x 2) (x 3 - x 2)⟫ ≠ 0 ∨ ⟪x 3 - x 2, x 5 - x 2⟫ < 0 ∨
          ⟪x 3 - x 5, x 2 - x 5⟫ < 0)) ∨
      (F.f 2 (x 1) < F.f 2 (x 3) ∧ F.f 2 (x 1) < F.f 2 (x 6) ∧
        (⟪F.N 2, cross (x 5 - x 2) (x 1 - x 2)⟫ ≠ 0 ∨ ⟪x 1 - x 2, x 5 - x 2⟫ < 0 ∨
          ⟪x 1 - x 5, x 2 - x 5⟫ < 0)))

/-- Hypotheses of `Mer.faceChordView_C5'` (Type24MerC2C5.lean; conclusion `FaceChordView F 4`):
`hM1`, `hM2`, `hinj`, `hz`, `hM4`. -/
def MerC5Hyp' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  (⟪F.N 5, mer F 2 4⟫ < 0 ∧ ⟪F.N 8, mer F 2 4⟫ < 0 ∧
      ⟪F.N 7, mer F 2 4⟫ < 0 ∧ 0 < ⟪F.N 0, mer F 2 4⟫ ∧ 0 < ⟪F.N 6, mer F 2 4⟫) ∧
  (0 < ⟪x 0 - x 6, cross (F.N 4) (F.N 2)⟫ * ⟪x 4 - x 0, cross (F.N 4) (F.N 2)⟫) ∧
  (Function.Injective fun i : ZMod 5 => ⟪x (rimC5' i), mer F 2 4⟫) ∧
  (UniOrSep (fun i : ZMod 5 => x (rimC5' i)) (mer F 2 4)) ∧
  ((F.f 4 (x 2) < F.f 4 (x 1) ∧ F.f 4 (x 2) < F.f 4 (x 3) ∧
        (⟪F.N 4, cross (x 4 - x 6) (x 2 - x 6)⟫ ≠ 0 ∨ ⟪x 2 - x 6, x 4 - x 6⟫ < 0 ∨
          ⟪x 2 - x 4, x 6 - x 4⟫ < 0)) ∨
      (F.f 4 (x 3) < F.f 4 (x 1) ∧ F.f 4 (x 3) < F.f 4 (x 2) ∧
        (⟪F.N 4, cross (x 4 - x 6) (x 3 - x 6)⟫ ≠ 0 ∨ ⟪x 3 - x 6, x 4 - x 6⟫ < 0 ∨
          ⟪x 3 - x 4, x 6 - x 4⟫ < 0)) ∨
      (F.f 4 (x 1) < F.f 4 (x 3) ∧ F.f 4 (x 1) < F.f 4 (x 2) ∧
        (⟪F.N 4, cross (x 4 - x 6) (x 1 - x 6)⟫ ≠ 0 ∨ ⟪x 1 - x 6, x 4 - x 6⟫ < 0 ∨
          ⟪x 1 - x 4, x 6 - x 4⟫ < 0)))

/-! ### Level-chord 4-rims C6a, C6b, C7a, C7a', C8, C8' (Type24MerC6C10.lean, via `faceChordView_mer4`) -/

/-- Hypotheses of `Mer.faceChordView_C6a` (Type24MerC6C10.lean; conclusion `FaceChordView F 7`):
`hM1`, `hM2`, `hguard`, `hlev`, `hM4`. -/
def MerC6aHyp {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  (0 < ⟪F.N 2, mer F 5 7⟫ ∧ ⟪F.N 4, mer F 5 7⟫ < 0 ∧ 0 < ⟪F.N 1, mer F 5 7⟫) ∧
  (0 < ⟪x 3 - x 2, x 6 - x 2⟫ ∧ 0 < ⟪x 3 - x 6, x 2 - x 6⟫) ∧
  (⟪x 5 - x 0, mer F 5 7⟫ ≠ 0 ∨ ⟪x 5 - x 0, x 6 - x 2⟫ ≠ 0) ∧
  ((⟪x 5 - x 2, mer F 5 7⟫ ≠ 0 ∨ ⟪x 0 - x 2, mer F 5 7⟫ ≠ 0) ∧
      (⟪x 5 - x 2, mer F 5 7⟫ ≠ 0 ∨
        ⟪x 5 - x 2, x 6 - x 2⟫ ≠ 0 ∧ ⟪x 5 - x 6, x 6 - x 2⟫ ≠ 0) ∧
      (⟪x 0 - x 2, mer F 5 7⟫ ≠ 0 ∨
        ⟪x 0 - x 2, x 6 - x 2⟫ ≠ 0 ∧ ⟪x 0 - x 6, x 6 - x 2⟫ ≠ 0)) ∧
  ((F.f 7 (x 0) < F.f 7 (x 5) ∧
        (⟪F.N 7, cross (x 6 - x 2) (x 0 - x 2)⟫ ≠ 0 ∨ ⟪x 0 - x 2, x 6 - x 2⟫ < 0 ∨
          ⟪x 0 - x 6, x 2 - x 6⟫ < 0)) ∨
      (F.f 7 (x 5) < F.f 7 (x 0) ∧
        (⟪F.N 7, cross (x 6 - x 2) (x 5 - x 2)⟫ ≠ 0 ∨ ⟪x 5 - x 2, x 6 - x 2⟫ < 0 ∨
          ⟪x 5 - x 6, x 2 - x 6⟫ < 0)))

/-- Hypotheses of `Mer.faceChordView_C6b` (Type24MerC6C10.lean; conclusion `FaceChordView F 7`):
`hM1`, `hM2`, `hguard`, `hlev`, `hM4`. -/
def MerC6bHyp {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  (⟪F.N 2, mer F 5 7⟫ < 0 ∧ 0 < ⟪F.N 0, mer F 5 7⟫ ∧ 0 < ⟪F.N 4, mer F 5 7⟫) ∧
  (0 < ⟪x 3 - x 2, x 6 - x 2⟫ ∧ 0 < ⟪x 3 - x 6, x 2 - x 6⟫) ∧
  (⟪x 0 - x 4, mer F 5 7⟫ ≠ 0 ∨ ⟪x 0 - x 4, x 6 - x 2⟫ ≠ 0) ∧
  ((⟪x 0 - x 2, mer F 5 7⟫ ≠ 0 ∨ ⟪x 4 - x 2, mer F 5 7⟫ ≠ 0) ∧
      (⟪x 0 - x 2, mer F 5 7⟫ ≠ 0 ∨
        ⟪x 0 - x 2, x 6 - x 2⟫ ≠ 0 ∧ ⟪x 0 - x 6, x 6 - x 2⟫ ≠ 0) ∧
      (⟪x 4 - x 2, mer F 5 7⟫ ≠ 0 ∨
        ⟪x 4 - x 2, x 6 - x 2⟫ ≠ 0 ∧ ⟪x 4 - x 6, x 6 - x 2⟫ ≠ 0)) ∧
  ((F.f 7 (x 0) < F.f 7 (x 4) ∧
        (⟪F.N 7, cross (x 6 - x 2) (x 0 - x 2)⟫ ≠ 0 ∨ ⟪x 0 - x 2, x 6 - x 2⟫ < 0 ∨
          ⟪x 0 - x 6, x 2 - x 6⟫ < 0)) ∨
      (F.f 7 (x 4) < F.f 7 (x 0) ∧
        (⟪F.N 7, cross (x 6 - x 2) (x 4 - x 2)⟫ ≠ 0 ∨ ⟪x 4 - x 2, x 6 - x 2⟫ < 0 ∨
          ⟪x 4 - x 6, x 2 - x 6⟫ < 0)))

/-- Hypotheses of `Mer.faceChordView_C7a` (Type24MerC6C10.lean; conclusion `FaceChordView F 7`):
`hM1`, `hM2`, `hguard`, `hlev`, `hM4`. -/
def MerC7aHyp {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  (0 < ⟪F.N 2, mer F 6 7⟫ ∧ 0 < ⟪F.N 3, mer F 6 7⟫ ∧
      ⟪F.N 0, mer F 6 7⟫ < 0 ∧ ⟪F.N 4, mer F 6 7⟫ < 0) ∧
  (0 < ⟪x 6 - x 2, x 3 - x 2⟫ ∧ 0 < ⟪x 6 - x 3, x 2 - x 3⟫) ∧
  (⟪x 0 - x 4, mer F 6 7⟫ ≠ 0 ∨ ⟪x 0 - x 4, x 3 - x 2⟫ ≠ 0) ∧
  ((⟪x 0 - x 2, mer F 6 7⟫ ≠ 0 ∨ ⟪x 4 - x 2, mer F 6 7⟫ ≠ 0) ∧
      (⟪x 0 - x 2, mer F 6 7⟫ ≠ 0 ∨
        ⟪x 0 - x 2, x 3 - x 2⟫ ≠ 0 ∧ ⟪x 0 - x 3, x 3 - x 2⟫ ≠ 0) ∧
      (⟪x 4 - x 2, mer F 6 7⟫ ≠ 0 ∨
        ⟪x 4 - x 2, x 3 - x 2⟫ ≠ 0 ∧ ⟪x 4 - x 3, x 3 - x 2⟫ ≠ 0)) ∧
  ((F.f 7 (x 0) < F.f 7 (x 4) ∧
        (⟪F.N 7, cross (x 3 - x 2) (x 0 - x 2)⟫ ≠ 0 ∨ ⟪x 0 - x 2, x 3 - x 2⟫ < 0 ∨
          ⟪x 0 - x 3, x 2 - x 3⟫ < 0)) ∨
      (F.f 7 (x 4) < F.f 7 (x 0) ∧
        (⟪F.N 7, cross (x 3 - x 2) (x 4 - x 2)⟫ ≠ 0 ∨ ⟪x 4 - x 2, x 3 - x 2⟫ < 0 ∨
          ⟪x 4 - x 3, x 2 - x 3⟫ < 0)))

/-- Hypotheses of `Mer.faceChordView_C7a'` (Type24MerC6C10.lean; conclusion `FaceChordView F 7`):
`hM1`, `hM2`, `hguard`, `hlev`, `hM4`. -/
def MerC7aHyp' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  (0 < ⟪F.N 4, mer F 8 7⟫ ∧ 0 < ⟪F.N 3, mer F 8 7⟫ ∧
      ⟪F.N 1, mer F 8 7⟫ < 0 ∧ ⟪F.N 2, mer F 8 7⟫ < 0) ∧
  (0 < ⟪x 2 - x 6, x 3 - x 6⟫ ∧ 0 < ⟪x 2 - x 3, x 6 - x 3⟫) ∧
  (⟪x 0 - x 5, mer F 8 7⟫ ≠ 0 ∨ ⟪x 0 - x 5, x 3 - x 6⟫ ≠ 0) ∧
  ((⟪x 0 - x 6, mer F 8 7⟫ ≠ 0 ∨ ⟪x 5 - x 6, mer F 8 7⟫ ≠ 0) ∧
      (⟪x 0 - x 6, mer F 8 7⟫ ≠ 0 ∨
        ⟪x 0 - x 6, x 3 - x 6⟫ ≠ 0 ∧ ⟪x 0 - x 3, x 3 - x 6⟫ ≠ 0) ∧
      (⟪x 5 - x 6, mer F 8 7⟫ ≠ 0 ∨
        ⟪x 5 - x 6, x 3 - x 6⟫ ≠ 0 ∧ ⟪x 5 - x 3, x 3 - x 6⟫ ≠ 0)) ∧
  ((F.f 7 (x 0) < F.f 7 (x 5) ∧
        (⟪F.N 7, cross (x 3 - x 6) (x 0 - x 6)⟫ ≠ 0 ∨ ⟪x 0 - x 6, x 3 - x 6⟫ < 0 ∨
          ⟪x 0 - x 3, x 6 - x 3⟫ < 0)) ∨
      (F.f 7 (x 5) < F.f 7 (x 0) ∧
        (⟪F.N 7, cross (x 3 - x 6) (x 5 - x 6)⟫ ≠ 0 ∨ ⟪x 5 - x 6, x 3 - x 6⟫ < 0 ∨
          ⟪x 5 - x 3, x 6 - x 3⟫ < 0)))

/-- Hypotheses of `Mer.faceChordView_C8` (Type24MerC6C10.lean; conclusion `FaceChordView F 3`):
`hM1`, `hM2`, `hguard`, `hlev`, `hM4`. -/
def MerC8Hyp {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  (0 < ⟪F.N 7, mer F 6 3⟫ ∧ ⟪F.N 5, mer F 6 3⟫ < 0) ∧
  (0 < ⟪x 0 - x 3, x 5 - x 3⟫ ∧ 0 < ⟪x 0 - x 5, x 3 - x 5⟫ ∧
      0 < ⟪x 4 - x 3, x 5 - x 3⟫ ∧ 0 < ⟪x 4 - x 5, x 3 - x 5⟫) ∧
  (⟪x 6 - x 2, mer F 6 3⟫ ≠ 0 ∨ ⟪x 6 - x 2, x 5 - x 3⟫ ≠ 0) ∧
  ((⟪x 6 - x 3, mer F 6 3⟫ ≠ 0 ∨ ⟪x 2 - x 3, mer F 6 3⟫ ≠ 0) ∧
      (⟪x 6 - x 3, mer F 6 3⟫ ≠ 0 ∨
        ⟪x 6 - x 3, x 5 - x 3⟫ ≠ 0 ∧ ⟪x 6 - x 5, x 5 - x 3⟫ ≠ 0) ∧
      (⟪x 2 - x 3, mer F 6 3⟫ ≠ 0 ∨
        ⟪x 2 - x 3, x 5 - x 3⟫ ≠ 0 ∧ ⟪x 2 - x 5, x 5 - x 3⟫ ≠ 0)) ∧
  ((F.f 3 (x 2) < F.f 3 (x 6) ∧
        (⟪F.N 3, cross (x 5 - x 3) (x 2 - x 3)⟫ ≠ 0 ∨ ⟪x 2 - x 3, x 5 - x 3⟫ < 0 ∨
          ⟪x 2 - x 5, x 3 - x 5⟫ < 0)) ∨
      (F.f 3 (x 6) < F.f 3 (x 2) ∧
        (⟪F.N 3, cross (x 5 - x 3) (x 6 - x 3)⟫ ≠ 0 ∨ ⟪x 6 - x 3, x 5 - x 3⟫ < 0 ∨
          ⟪x 6 - x 5, x 3 - x 5⟫ < 0)))

/-- Hypotheses of `Mer.faceChordView_C8'` (Type24MerC6C10.lean; conclusion `FaceChordView F 3`):
`hM1`, `hM2`, `hguard`, `hlev`, `hM4`. -/
def MerC8Hyp' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  (0 < ⟪F.N 7, mer F 8 3⟫ ∧ ⟪F.N 5, mer F 8 3⟫ < 0) ∧
  (0 < ⟪x 0 - x 3, x 4 - x 3⟫ ∧ 0 < ⟪x 0 - x 4, x 3 - x 4⟫ ∧
      0 < ⟪x 5 - x 3, x 4 - x 3⟫ ∧ 0 < ⟪x 5 - x 4, x 3 - x 4⟫) ∧
  (⟪x 2 - x 6, mer F 8 3⟫ ≠ 0 ∨ ⟪x 2 - x 6, x 4 - x 3⟫ ≠ 0) ∧
  ((⟪x 2 - x 3, mer F 8 3⟫ ≠ 0 ∨ ⟪x 6 - x 3, mer F 8 3⟫ ≠ 0) ∧
      (⟪x 2 - x 3, mer F 8 3⟫ ≠ 0 ∨
        ⟪x 2 - x 3, x 4 - x 3⟫ ≠ 0 ∧ ⟪x 2 - x 4, x 4 - x 3⟫ ≠ 0) ∧
      (⟪x 6 - x 3, mer F 8 3⟫ ≠ 0 ∨
        ⟪x 6 - x 3, x 4 - x 3⟫ ≠ 0 ∧ ⟪x 6 - x 4, x 4 - x 3⟫ ≠ 0)) ∧
  ((F.f 3 (x 6) < F.f 3 (x 2) ∧
        (⟪F.N 3, cross (x 4 - x 3) (x 6 - x 3)⟫ ≠ 0 ∨ ⟪x 6 - x 3, x 4 - x 3⟫ < 0 ∨
          ⟪x 6 - x 4, x 3 - x 4⟫ < 0)) ∨
      (F.f 3 (x 2) < F.f 3 (x 6) ∧
        (⟪F.N 3, cross (x 4 - x 3) (x 2 - x 3)⟫ ≠ 0 ∨ ⟪x 2 - x 3, x 4 - x 3⟫ < 0 ∨
          ⟪x 2 - x 4, x 3 - x 4⟫ < 0)))

/-! ### Slide cases C6c, C6d, C6d', C7b, C7b' (Type24MerC6C10.lean, via `faceChordView_of_rimCert_slide`) -/

/-- Hypotheses of `Mer.faceChordView_C6c` (Type24MerC6C10.lean; conclusion `FaceChordView F 7`):
`hM1`, `hM2`, `hinj`, `hz`, `hM4`. -/
def MerC6cHyp {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  (0 < ⟪F.N 4, mer F 5 7⟫ ∧ 0 < ⟪F.N 2, mer F 5 7⟫) ∧
  (0 < ⟪x 3 - x 6, x 2 - x 6⟫ ∧ 0 < ⟪x 3 - x 2, x 6 - x 2⟫) ∧
  (∀ i j : ZMod 5, i ≠ j → ({i, j} : Finset (ZMod 5)) ≠ {2, 3} →
      ⟪x (rimC6c i), mer F 5 7⟫ ≠ ⟪x (rimC6c j), mer F 5 7⟫) ∧
  (∃ σ : ℝ, σ ≠ 0 ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ),
      UniOrSep (fun i : ZMod 5 => x (rimC6c i)) (mer F 5 7 + t • (σ • (x 2 - x 6)))) ∧
  ((F.f 7 (x 0) < F.f 7 (x 4) ∧ F.f 7 (x 0) < F.f 7 (x 5) ∧
        (⟪F.N 7, cross (x 2 - x 6) (x 0 - x 6)⟫ ≠ 0 ∨ ⟪x 0 - x 6, x 2 - x 6⟫ < 0 ∨
          ⟪x 0 - x 2, x 6 - x 2⟫ < 0)) ∨
      (F.f 7 (x 4) < F.f 7 (x 0) ∧ F.f 7 (x 4) < F.f 7 (x 5) ∧
        (⟪F.N 7, cross (x 2 - x 6) (x 4 - x 6)⟫ ≠ 0 ∨ ⟪x 4 - x 6, x 2 - x 6⟫ < 0 ∨
          ⟪x 4 - x 2, x 6 - x 2⟫ < 0)) ∨
      (F.f 7 (x 5) < F.f 7 (x 0) ∧ F.f 7 (x 5) < F.f 7 (x 4) ∧
        (⟪F.N 7, cross (x 2 - x 6) (x 5 - x 6)⟫ ≠ 0 ∨ ⟪x 5 - x 6, x 2 - x 6⟫ < 0 ∨
          ⟪x 5 - x 2, x 6 - x 2⟫ < 0)))

/-- Hypotheses of `Mer.faceChordView_C6d` (Type24MerC6C10.lean; conclusion `FaceChordView F 7`):
`hM1`, `hM2`, `hinj`, `hz`, `hM4`. -/
def MerC6dHyp {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  (⟪F.N 0, mer F 5 7⟫ < 0 ∧ 0 < ⟪F.N 1, mer F 5 7⟫ ∧ 0 < ⟪F.N 4, mer F 5 7⟫) ∧
  (0 < ⟪x 3 - x 2, x 6 - x 2⟫ ∧ 0 < ⟪x 3 - x 6, x 2 - x 6⟫) ∧
  (∀ i j : ZMod 5, i ≠ j → ({i, j} : Finset (ZMod 5)) ≠ {2, 3} →
      ⟪x (rimC6d i), mer F 5 7⟫ ≠ ⟪x (rimC6d j), mer F 5 7⟫) ∧
  (∃ σ : ℝ, σ ≠ 0 ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ),
      UniOrSep (fun i : ZMod 5 => x (rimC6d i)) (mer F 5 7 + t • (σ • (x 6 - x 2)))) ∧
  ((F.f 7 (x 0) < F.f 7 (x 1) ∧ F.f 7 (x 0) < F.f 7 (x 4) ∧
        (⟪F.N 7, cross (x 6 - x 2) (x 0 - x 2)⟫ ≠ 0 ∨ ⟪x 0 - x 2, x 6 - x 2⟫ < 0 ∨
          ⟪x 0 - x 6, x 2 - x 6⟫ < 0)) ∨
      (F.f 7 (x 1) < F.f 7 (x 0) ∧ F.f 7 (x 1) < F.f 7 (x 4) ∧
        (⟪F.N 7, cross (x 6 - x 2) (x 1 - x 2)⟫ ≠ 0 ∨ ⟪x 1 - x 2, x 6 - x 2⟫ < 0 ∨
          ⟪x 1 - x 6, x 2 - x 6⟫ < 0)) ∨
      (F.f 7 (x 4) < F.f 7 (x 0) ∧ F.f 7 (x 4) < F.f 7 (x 1) ∧
        (⟪F.N 7, cross (x 6 - x 2) (x 4 - x 2)⟫ ≠ 0 ∨ ⟪x 4 - x 2, x 6 - x 2⟫ < 0 ∨
          ⟪x 4 - x 6, x 2 - x 6⟫ < 0)))

/-- Hypotheses of `Mer.faceChordView_C6d'` (Type24MerC6C10.lean; conclusion `FaceChordView F 7`):
`hM1`, `hM2`, `hinj`, `hz`, `hM4`. -/
def MerC6dHyp' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  (⟪F.N 1, mer F 5 7⟫ < 0 ∧ 0 < ⟪F.N 0, mer F 5 7⟫ ∧ 0 < ⟪F.N 2, mer F 5 7⟫) ∧
  (0 < ⟪x 3 - x 6, x 2 - x 6⟫ ∧ 0 < ⟪x 3 - x 2, x 6 - x 2⟫) ∧
  (∀ i j : ZMod 5, i ≠ j → ({i, j} : Finset (ZMod 5)) ≠ {2, 3} →
      ⟪x (rimC6d' i), mer F 5 7⟫ ≠ ⟪x (rimC6d' j), mer F 5 7⟫) ∧
  (∃ σ : ℝ, σ ≠ 0 ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ),
      UniOrSep (fun i : ZMod 5 => x (rimC6d' i)) (mer F 5 7 + t • (σ • (x 2 - x 6)))) ∧
  ((F.f 7 (x 0) < F.f 7 (x 1) ∧ F.f 7 (x 0) < F.f 7 (x 5) ∧
        (⟪F.N 7, cross (x 2 - x 6) (x 0 - x 6)⟫ ≠ 0 ∨ ⟪x 0 - x 6, x 2 - x 6⟫ < 0 ∨
          ⟪x 0 - x 2, x 6 - x 2⟫ < 0)) ∨
      (F.f 7 (x 1) < F.f 7 (x 0) ∧ F.f 7 (x 1) < F.f 7 (x 5) ∧
        (⟪F.N 7, cross (x 2 - x 6) (x 1 - x 6)⟫ ≠ 0 ∨ ⟪x 1 - x 6, x 2 - x 6⟫ < 0 ∨
          ⟪x 1 - x 2, x 6 - x 2⟫ < 0)) ∨
      (F.f 7 (x 5) < F.f 7 (x 0) ∧ F.f 7 (x 5) < F.f 7 (x 1) ∧
        (⟪F.N 7, cross (x 2 - x 6) (x 5 - x 6)⟫ ≠ 0 ∨ ⟪x 5 - x 6, x 2 - x 6⟫ < 0 ∨
          ⟪x 5 - x 2, x 6 - x 2⟫ < 0)))

/-- Hypotheses of `Mer.faceChordView_C7b` (Type24MerC6C10.lean; conclusion `FaceChordView F 7`):
`hM1`, `hM2`, `hinj`, `hz`, `hM4`. -/
def MerC7bHyp {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  (0 < ⟪F.N 0, mer F 6 7⟫ ∧ 0 < ⟪F.N 3, mer F 6 7⟫) ∧
  (0 < ⟪x 6 - x 2, x 3 - x 2⟫ ∧ 0 < ⟪x 6 - x 3, x 2 - x 3⟫) ∧
  (∀ i j : ZMod 5, i ≠ j → ({i, j} : Finset (ZMod 5)) ≠ {2, 3} →
      ⟪x (rimC1 i), mer F 6 7⟫ ≠ ⟪x (rimC1 j), mer F 6 7⟫) ∧
  (∃ σ : ℝ, σ ≠ 0 ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ),
      UniOrSep (fun i : ZMod 5 => x (rimC1 i)) (mer F 6 7 + t • (σ • (x 3 - x 2)))) ∧
  ((F.f 7 (x 0) < F.f 7 (x 1) ∧ F.f 7 (x 0) < F.f 7 (x 4) ∧
        (⟪F.N 7, cross (x 3 - x 2) (x 0 - x 2)⟫ ≠ 0 ∨ ⟪x 0 - x 2, x 3 - x 2⟫ < 0 ∨
          ⟪x 0 - x 3, x 2 - x 3⟫ < 0)) ∨
      (F.f 7 (x 1) < F.f 7 (x 0) ∧ F.f 7 (x 1) < F.f 7 (x 4) ∧
        (⟪F.N 7, cross (x 3 - x 2) (x 1 - x 2)⟫ ≠ 0 ∨ ⟪x 1 - x 2, x 3 - x 2⟫ < 0 ∨
          ⟪x 1 - x 3, x 2 - x 3⟫ < 0)) ∨
      (F.f 7 (x 4) < F.f 7 (x 0) ∧ F.f 7 (x 4) < F.f 7 (x 1) ∧
        (⟪F.N 7, cross (x 3 - x 2) (x 4 - x 2)⟫ ≠ 0 ∨ ⟪x 4 - x 2, x 3 - x 2⟫ < 0 ∨
          ⟪x 4 - x 3, x 2 - x 3⟫ < 0)))

/-- Hypotheses of `Mer.faceChordView_C7b'` (Type24MerC6C10.lean; conclusion `FaceChordView F 7`):
`hM1`, `hM2`, `hinj`, `hz`, `hM4`. -/
def MerC7bHyp' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  (0 < ⟪F.N 1, mer F 8 7⟫ ∧ 0 < ⟪F.N 3, mer F 8 7⟫) ∧
  (0 < ⟪x 2 - x 6, x 3 - x 6⟫ ∧ 0 < ⟪x 2 - x 3, x 6 - x 3⟫) ∧
  (∀ i j : ZMod 5, i ≠ j → ({i, j} : Finset (ZMod 5)) ≠ {2, 3} →
      ⟪x (rimC1' i), mer F 8 7⟫ ≠ ⟪x (rimC1' j), mer F 8 7⟫) ∧
  (∃ σ : ℝ, σ ≠ 0 ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ),
      UniOrSep (fun i : ZMod 5 => x (rimC1' i)) (mer F 8 7 + t • (σ • (x 3 - x 6)))) ∧
  ((F.f 7 (x 0) < F.f 7 (x 1) ∧ F.f 7 (x 0) < F.f 7 (x 5) ∧
        (⟪F.N 7, cross (x 3 - x 6) (x 0 - x 6)⟫ ≠ 0 ∨ ⟪x 0 - x 6, x 3 - x 6⟫ < 0 ∨
          ⟪x 0 - x 3, x 6 - x 3⟫ < 0)) ∨
      (F.f 7 (x 1) < F.f 7 (x 0) ∧ F.f 7 (x 1) < F.f 7 (x 5) ∧
        (⟪F.N 7, cross (x 3 - x 6) (x 1 - x 6)⟫ ≠ 0 ∨ ⟪x 1 - x 6, x 3 - x 6⟫ < 0 ∨
          ⟪x 1 - x 3, x 6 - x 3⟫ < 0)) ∨
      (F.f 7 (x 5) < F.f 7 (x 0) ∧ F.f 7 (x 5) < F.f 7 (x 1) ∧
        (⟪F.N 7, cross (x 3 - x 6) (x 5 - x 6)⟫ ≠ 0 ∨ ⟪x 5 - x 6, x 3 - x 6⟫ < 0 ∨
          ⟪x 5 - x 3, x 6 - x 3⟫ < 0)))

/-! ### Views on a facet circle, any `u`: C9, C9' (circle of facet 2 / 4) and C10, C10' (circle of facet 3)
(Type24MerC6C10.lean) -/

/-- Hypotheses of `Mer.faceChordView_C9` (Type24MerC6C10.lean; conclusion `FaceChordView F 2`):
`hnu`, `hM1`, `hinj`, `hz`, `hM4`, for the view `u`. -/
def MerC9Hyp {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (u : ℝ³) : Prop :=
  (⟪F.N 2, u⟫ = 0) ∧
  (0 < ⟪F.N 5, u⟫ ∧ 0 < ⟪F.N 6, u⟫ ∧ 0 < ⟪F.N 7, u⟫ ∧
      ⟪F.N 0, u⟫ < 0 ∧ ⟪F.N 1, u⟫ < 0 ∧ ⟪F.N 3, u⟫ < 0 ∧ ⟪F.N 8, u⟫ < 0) ∧
  (Function.Injective fun i : ZMod 5 => ⟪x (rimC5 i), u⟫) ∧
  (UniOrSep (fun i : ZMod 5 => x (rimC5 i)) u) ∧
  ((F.f 2 (x 6) < F.f 2 (x 1) ∧ F.f 2 (x 6) < F.f 2 (x 3) ∧
        (⟪F.N 2, cross (x 5 - x 2) (x 6 - x 2)⟫ ≠ 0 ∨ ⟪x 6 - x 2, x 5 - x 2⟫ < 0 ∨
          ⟪x 6 - x 5, x 2 - x 5⟫ < 0)) ∨
      (F.f 2 (x 3) < F.f 2 (x 1) ∧ F.f 2 (x 3) < F.f 2 (x 6) ∧
        (⟪F.N 2, cross (x 5 - x 2) (x 3 - x 2)⟫ ≠ 0 ∨ ⟪x 3 - x 2, x 5 - x 2⟫ < 0 ∨
          ⟪x 3 - x 5, x 2 - x 5⟫ < 0)) ∨
      (F.f 2 (x 1) < F.f 2 (x 3) ∧ F.f 2 (x 1) < F.f 2 (x 6) ∧
        (⟪F.N 2, cross (x 5 - x 2) (x 1 - x 2)⟫ ≠ 0 ∨ ⟪x 1 - x 2, x 5 - x 2⟫ < 0 ∨
          ⟪x 1 - x 5, x 2 - x 5⟫ < 0)))

/-- Hypotheses of `Mer.faceChordView_C9'` (Type24MerC6C10.lean; conclusion `FaceChordView F 4`):
`hnu`, `hM1`, `hinj`, `hz`, `hM4`, for the view `u`. -/
def MerC9Hyp' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (u : ℝ³) : Prop :=
  (⟪F.N 4, u⟫ = 0) ∧
  (0 < ⟪F.N 5, u⟫ ∧ 0 < ⟪F.N 8, u⟫ ∧ 0 < ⟪F.N 7, u⟫ ∧
      ⟪F.N 1, u⟫ < 0 ∧ ⟪F.N 0, u⟫ < 0 ∧ ⟪F.N 3, u⟫ < 0 ∧ ⟪F.N 6, u⟫ < 0) ∧
  (Function.Injective fun i : ZMod 5 => ⟪x (rimC5' i), u⟫) ∧
  (UniOrSep (fun i : ZMod 5 => x (rimC5' i)) u) ∧
  ((F.f 4 (x 2) < F.f 4 (x 1) ∧ F.f 4 (x 2) < F.f 4 (x 3) ∧
        (⟪F.N 4, cross (x 4 - x 6) (x 2 - x 6)⟫ ≠ 0 ∨ ⟪x 2 - x 6, x 4 - x 6⟫ < 0 ∨
          ⟪x 2 - x 4, x 6 - x 4⟫ < 0)) ∨
      (F.f 4 (x 3) < F.f 4 (x 1) ∧ F.f 4 (x 3) < F.f 4 (x 2) ∧
        (⟪F.N 4, cross (x 4 - x 6) (x 3 - x 6)⟫ ≠ 0 ∨ ⟪x 3 - x 6, x 4 - x 6⟫ < 0 ∨
          ⟪x 3 - x 4, x 6 - x 4⟫ < 0)) ∨
      (F.f 4 (x 1) < F.f 4 (x 3) ∧ F.f 4 (x 1) < F.f 4 (x 2) ∧
        (⟪F.N 4, cross (x 4 - x 6) (x 1 - x 6)⟫ ≠ 0 ∨ ⟪x 1 - x 6, x 4 - x 6⟫ < 0 ∨
          ⟪x 1 - x 4, x 6 - x 4⟫ < 0)))

/-- Hypotheses of `Mer.faceChordView_C10` (Type24MerC6C10.lean; conclusion `FaceChordView F 3`):
`hnu`, `hM1`, `hinj`, `hz`, `hM4`, for the view `u`. -/
def MerC10Hyp {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (u : ℝ³) : Prop :=
  (⟪F.N 3, u⟫ = 0) ∧
  (0 < ⟪F.N 5, u⟫ ∧ 0 < ⟪F.N 6, u⟫ ∧ 0 < ⟪F.N 8, u⟫ ∧
      ⟪F.N 0, u⟫ < 0 ∧ ⟪F.N 1, u⟫ < 0 ∧ ⟪F.N 2, u⟫ < 0 ∧ ⟪F.N 4, u⟫ < 0) ∧
  (Function.Injective fun i : ZMod 5 => ⟪x (rimC10 i), u⟫) ∧
  (UniOrSep (fun i : ZMod 5 => x (rimC10 i)) u) ∧
  ((F.f 3 (x 6) < F.f 3 (x 1) ∧ F.f 3 (x 6) < F.f 3 (x 2) ∧
        (⟪F.N 3, cross (x 4 - x 5) (x 6 - x 5)⟫ ≠ 0 ∨ ⟪x 6 - x 5, x 4 - x 5⟫ < 0 ∨
          ⟪x 6 - x 4, x 5 - x 4⟫ < 0)) ∨
      (F.f 3 (x 1) < F.f 3 (x 6) ∧ F.f 3 (x 1) < F.f 3 (x 2) ∧
        (⟪F.N 3, cross (x 4 - x 5) (x 1 - x 5)⟫ ≠ 0 ∨ ⟪x 1 - x 5, x 4 - x 5⟫ < 0 ∨
          ⟪x 1 - x 4, x 5 - x 4⟫ < 0)) ∨
      (F.f 3 (x 2) < F.f 3 (x 6) ∧ F.f 3 (x 2) < F.f 3 (x 1) ∧
        (⟪F.N 3, cross (x 4 - x 5) (x 2 - x 5)⟫ ≠ 0 ∨ ⟪x 2 - x 5, x 4 - x 5⟫ < 0 ∨
          ⟪x 2 - x 4, x 5 - x 4⟫ < 0)))

/-- Hypotheses of `Mer.faceChordView_C10'` (Type24MerC6C10.lean; conclusion `FaceChordView F 3`):
`hnu`, `hM1`, `hinj`, `hz`, `hM4`, for the view `u`. -/
def MerC10Hyp' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (u : ℝ³) : Prop :=
  (⟪F.N 3, u⟫ = 0) ∧
  (0 < ⟪F.N 5, u⟫ ∧ 0 < ⟪F.N 8, u⟫ ∧ 0 < ⟪F.N 6, u⟫ ∧
      ⟪F.N 1, u⟫ < 0 ∧ ⟪F.N 0, u⟫ < 0 ∧ ⟪F.N 4, u⟫ < 0 ∧ ⟪F.N 2, u⟫ < 0) ∧
  (Function.Injective fun i : ZMod 5 => ⟪x (rimC10' i), u⟫) ∧
  (UniOrSep (fun i : ZMod 5 => x (rimC10' i)) u) ∧
  ((F.f 3 (x 2) < F.f 3 (x 1) ∧ F.f 3 (x 2) < F.f 3 (x 6) ∧
        (⟪F.N 3, cross (x 5 - x 4) (x 2 - x 4)⟫ ≠ 0 ∨ ⟪x 2 - x 4, x 5 - x 4⟫ < 0 ∨
          ⟪x 2 - x 5, x 4 - x 5⟫ < 0)) ∨
      (F.f 3 (x 1) < F.f 3 (x 2) ∧ F.f 3 (x 1) < F.f 3 (x 6) ∧
        (⟪F.N 3, cross (x 5 - x 4) (x 1 - x 4)⟫ ≠ 0 ∨ ⟪x 1 - x 4, x 5 - x 4⟫ < 0 ∨
          ⟪x 1 - x 5, x 4 - x 5⟫ < 0)) ∨
      (F.f 3 (x 6) < F.f 3 (x 2) ∧ F.f 3 (x 6) < F.f 3 (x 1) ∧
        (⟪F.N 3, cross (x 5 - x 4) (x 6 - x 4)⟫ ≠ 0 ∨ ⟪x 6 - x 4, x 5 - x 4⟫ < 0 ∨
          ⟪x 6 - x 5, x 4 - x 5⟫ < 0)))

/-! ### The confinement -/

/-- The generic negated leaves carried by `Hole24`: `C̄`, no face-chord view, no lex cell, no split cell (from
`Hole24R` or `Hole24Q45Special` at the bottom of the reduction chains), no box lemma, no Q4 cell and no edge-cone
cell. -/
theorem hole24_leaves {x : Fin 7 → ℝ³} {fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ} {F : S0xFac 9 s0x_S24 x}
    (h : Hole24 x fs F) :
    CbarIn x ∧ ¬ RCell.AnyFaceChord F ∧ ¬ RCell.LexAny F ∧ ¬ RCell.SplitAny24 F ∧
      ¬ BoxApplies (univ.image x) ∧ ¬ GenPlus.Q4Any F ∧ ¬ GenPlus.EdgeAny F := by
  obtain ⟨_, hQR, _, _, hbox, hq4, hedge⟩ := h
  rcases hQR with hQ | hR
  · obtain ⟨hC, -, -, -, hA, hL, hS⟩ := hQ.1.1.1.1.1
    exact ⟨hC, hA, hL, hS, hbox, hq4, hedge⟩
  · obtain ⟨hC, -, -, hA, hL, hS⟩ := hole24R_of_hole24R1 hR.1.1.1.1.1.1.1.1
    exact ⟨hC, hA, hL, hS, hbox, hq4, hedge⟩

/-- Off `AnyFaceChord` (any `S0xFac` of type 24, no region hypotheses), the hypotheses of every meridian /
tie-view lemma `Mer.faceChordView_C*` fail. -/
theorem merHyps_off {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hA : ¬ RCell.AnyFaceChord F) :
    ¬ MerC1Hyp F ∧
    ¬ MerC1Hyp' F ∧
    ¬ MerC2Hyp F ∧
    ¬ MerC2Hyp' F ∧
    ¬ MerC3Hyp F ∧
    ¬ MerC3Hyp' F ∧
    ¬ MerC4Hyp F ∧
    ¬ MerC4Hyp' F ∧
    ¬ MerC5Hyp F ∧
    ¬ MerC5Hyp' F ∧
    ¬ MerC6aHyp F ∧
    ¬ MerC6bHyp F ∧
    ¬ MerC7aHyp F ∧
    ¬ MerC7aHyp' F ∧
    ¬ MerC8Hyp F ∧
    ¬ MerC8Hyp' F ∧
    ¬ MerC6cHyp F ∧
    ¬ MerC6dHyp F ∧
    ¬ MerC6dHyp' F ∧
    ¬ MerC7bHyp F ∧
    ¬ MerC7bHyp' F ∧
    (∀ u, ¬ MerC9Hyp F u) ∧
    (∀ u, ¬ MerC9Hyp' F u) ∧
    (∀ u, ¬ MerC10Hyp F u) ∧
    (∀ u, ¬ MerC10Hyp' F u) :=
  ⟨fun ⟨h0, h1, h2, h3, h4⟩ => hA ⟨_, Mer.faceChordView_C1 F h0 h1 h2 h3 h4⟩,
    fun ⟨h0, h1, h2, h3, h4⟩ => hA ⟨_, Mer.faceChordView_C1' F h0 h1 h2 h3 h4⟩,
    fun ⟨h0, h1, h2, h3, h4⟩ => hA ⟨_, Mer.faceChordView_C2 F h0 h1 h2 h3 h4⟩,
    fun ⟨h0, h1, h2, h3, h4⟩ => hA ⟨_, Mer.faceChordView_C2' F h0 h1 h2 h3 h4⟩,
    fun ⟨h0, h1, h2, h3, h4⟩ => hA ⟨_, Mer.faceChordView_C3 F h0 h1 h2 h3 h4⟩,
    fun ⟨h0, h1, h2, h3, h4⟩ => hA ⟨_, Mer.faceChordView_C3' F h0 h1 h2 h3 h4⟩,
    fun ⟨h0, h1, h2, h3, h4⟩ => hA ⟨_, Mer.faceChordView_C4 F h0 h1 h2 h3 h4⟩,
    fun ⟨h0, h1, h2, h3, h4⟩ => hA ⟨_, Mer.faceChordView_C4' F h0 h1 h2 h3 h4⟩,
    fun ⟨h0, h1, h2, h3, h4⟩ => hA ⟨_, Mer.faceChordView_C5 F h0 h1 h2 h3 h4⟩,
    fun ⟨h0, h1, h2, h3, h4⟩ => hA ⟨_, Mer.faceChordView_C5' F h0 h1 h2 h3 h4⟩,
    fun ⟨h0, h1, h2, h3, h4⟩ => hA ⟨_, Mer.faceChordView_C6a F h0 h1 h2 h3 h4⟩,
    fun ⟨h0, h1, h2, h3, h4⟩ => hA ⟨_, Mer.faceChordView_C6b F h0 h1 h2 h3 h4⟩,
    fun ⟨h0, h1, h2, h3, h4⟩ => hA ⟨_, Mer.faceChordView_C7a F h0 h1 h2 h3 h4⟩,
    fun ⟨h0, h1, h2, h3, h4⟩ => hA ⟨_, Mer.faceChordView_C7a' F h0 h1 h2 h3 h4⟩,
    fun ⟨h0, h1, h2, h3, h4⟩ => hA ⟨_, Mer.faceChordView_C8 F h0 h1 h2 h3 h4⟩,
    fun ⟨h0, h1, h2, h3, h4⟩ => hA ⟨_, Mer.faceChordView_C8' F h0 h1 h2 h3 h4⟩,
    fun ⟨h0, h1, h2, h3, h4⟩ => hA ⟨_, Mer.faceChordView_C6c F h0 h1 h2 h3 h4⟩,
    fun ⟨h0, h1, h2, h3, h4⟩ => hA ⟨_, Mer.faceChordView_C6d F h0 h1 h2 h3 h4⟩,
    fun ⟨h0, h1, h2, h3, h4⟩ => hA ⟨_, Mer.faceChordView_C6d' F h0 h1 h2 h3 h4⟩,
    fun ⟨h0, h1, h2, h3, h4⟩ => hA ⟨_, Mer.faceChordView_C7b F h0 h1 h2 h3 h4⟩,
    fun ⟨h0, h1, h2, h3, h4⟩ => hA ⟨_, Mer.faceChordView_C7b' F h0 h1 h2 h3 h4⟩,
    fun u ⟨h0, h1, h2, h3, h4⟩ => hA ⟨_, Mer.faceChordView_C9 F u h0 h1 h2 h3 h4⟩,
    fun u ⟨h0, h1, h2, h3, h4⟩ => hA ⟨_, Mer.faceChordView_C9' F u h0 h1 h2 h3 h4⟩,
    fun u ⟨h0, h1, h2, h3, h4⟩ => hA ⟨_, Mer.faceChordView_C10 F u h0 h1 h2 h3 h4⟩,
    fun u ⟨h0, h1, h2, h3, h4⟩ => hA ⟨_, Mer.faceChordView_C10' F u h0 h1 h2 h3 h4⟩⟩

/-- **Confinement of `Hole24`.**  On `Hole24` (inside `C̄`), the hypotheses of `QN.lexAny_quadNormal` and of
every meridian / tie-view lemma `Mer.faceChordView_C*` fail (for C9, C9', C10, C10' at every view `u`). -/
theorem hole24_confined {x : Fin 7 → ℝ³} {fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ} {F : S0xFac 9 s0x_S24 x}
    (h : Hole24 x fs F) :
    CbarIn x ∧ ¬ QNHyp F ∧
    ¬ MerC1Hyp F ∧
    ¬ MerC1Hyp' F ∧
    ¬ MerC2Hyp F ∧
    ¬ MerC2Hyp' F ∧
    ¬ MerC3Hyp F ∧
    ¬ MerC3Hyp' F ∧
    ¬ MerC4Hyp F ∧
    ¬ MerC4Hyp' F ∧
    ¬ MerC5Hyp F ∧
    ¬ MerC5Hyp' F ∧
    ¬ MerC6aHyp F ∧
    ¬ MerC6bHyp F ∧
    ¬ MerC7aHyp F ∧
    ¬ MerC7aHyp' F ∧
    ¬ MerC8Hyp F ∧
    ¬ MerC8Hyp' F ∧
    ¬ MerC6cHyp F ∧
    ¬ MerC6dHyp F ∧
    ¬ MerC6dHyp' F ∧
    ¬ MerC7bHyp F ∧
    ¬ MerC7bHyp' F ∧
    (∀ u, ¬ MerC9Hyp F u) ∧
    (∀ u, ¬ MerC9Hyp' F u) ∧
    (∀ u, ¬ MerC10Hyp F u) ∧
    (∀ u, ¬ MerC10Hyp' F u) := by
  obtain ⟨hC, hA, hL, -⟩ := hole24_leaves h
  exact ⟨hC, fun ⟨hob, hnB, hnC, hTE⟩ => hL (QN.lexAny_quadNormal F hC hob hnB hnC hTE), merHyps_off hA⟩

end Minimality.T24
