module

public import Minimality.Generic.PV.SK
public import Minimality.Generic.PV.PVReal
public import Minimality.Generic.PV.PVChain
public import Minimality.Generic.PV.FaceCircle
public import Minimality.Tilt
public import Minimality.Oct9Weak
public import Minimality.FaceChain
public import Minimality.Type29NF

@[expose] public section


/-! Definitions for Lemma PV (pair view of a prismatoid). -/

namespace Minimality
open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ## Data -/

/-- Planar chart of the plane `{⟪n,·⟫ = h}` seen along its direction `d` (`⟪n,d⟫ = 0`):
(coordinate along the screen line, depth). -/
noncomputable def planeChart (n d : ℝ³) (p : ℝ³) : ℝ² := !₂[⟪cross n d, p⟫, ⟪d, p⟫]

/-- `V = F₁ ∪ F₂ ∪ H`: `F₁`, `F₂` the vertex sets of two disjoint faces in the planes
`⟪nᵢ,·⟫ = hᵢ` (all of `V` on the closed negative side, `F₃₋ᵢ` strictly), strictly convex in the
chart along `d = n₁ × n₂`; `H` are extra vertices (e.g. a hidden cap). -/
structure IsPrismPair (V F₁ F₂ H : Finset ℝ³) (n₁ n₂ : ℝ³) (h₁ h₂ : ℝ) : Prop where
  union : V = F₁ ∪ F₂ ∪ H
  disj : Disjoint F₁ F₂
  card₁ : 3 ≤ F₁.card
  card₂ : 3 ≤ F₂.card
  on₁ : ∀ p ∈ F₁, ⟪n₁, p⟫ = h₁
  on₂ : ∀ p ∈ F₂, ⟪n₂, p⟫ = h₂
  le₁ : ∀ p ∈ V, ⟪n₁, p⟫ ≤ h₁
  le₂ : ∀ p ∈ V, ⟪n₂, p⟫ ≤ h₂
  strict₁ : ∀ p ∈ F₂, ⟪n₁, p⟫ < h₁
  strict₂ : ∀ p ∈ F₁, ⟪n₂, p⟫ < h₂
  d_ne : cross n₁ n₂ ≠ 0
  conv₁ : ConvPos (F₁.image (planeChart n₁ (cross n₁ n₂)))
  conv₂ : ConvPos (F₂.image (planeChart n₂ (cross n₁ n₂)))

/-- The depth `ℓ = ⟪d,·⟫` of the pair view `d = n₁ × n₂`. -/
noncomputable def pvDepth (n₁ n₂ : ℝ³) (p : ℝ³) : ℝ := ⟪cross n₁ n₂, p⟫

/-- Near ends `A₁, A₂` (closest to the other plane) and far ends `B₁, B₂` (farthest);
affine notions, unique (genericity). -/
structure PVEnds (F₁ F₂ : Finset ℝ³) (n₁ n₂ : ℝ³) (h₁ h₂ : ℝ) where
  A₁ : ℝ³
  B₁ : ℝ³
  A₂ : ℝ³
  B₂ : ℝ³
  A₁_mem : A₁ ∈ F₁
  B₁_mem : B₁ ∈ F₁
  A₂_mem : A₂ ∈ F₂
  B₂_mem : B₂ ∈ F₂
  A₁_near : ∀ y ∈ F₁, y ≠ A₁ → ⟪n₂, y⟫ < ⟪n₂, A₁⟫
  B₁_far : ∀ y ∈ F₁, y ≠ B₁ → ⟪n₂, B₁⟫ < ⟪n₂, y⟫
  A₂_near : ∀ y ∈ F₂, y ≠ A₂ → ⟪n₁, y⟫ < ⟪n₁, A₂⟫
  B₂_far : ∀ y ∈ F₂, y ≠ B₂ → ⟪n₁, B₂⟫ < ⟪n₁, y⟫

/-- `a` is the lowest (resp. highest) vertex of `F` in depth `ℓ`. -/
def IsLoIn (ℓ : ℝ³ → ℝ) (F : Finset ℝ³) (a : ℝ³) : Prop := a ∈ F ∧ ∀ y ∈ F, ℓ a ≤ ℓ y
def IsHiIn (ℓ : ℝ³ → ℝ) (F : Finset ℝ³) (a : ℝ³) : Prop := a ∈ F ∧ ∀ y ∈ F, ℓ y ≤ ℓ a

/-- (M−) of the paper: mixed depths at the bridges and no escape equality. -/
def PVMixedMinus {F₁ F₂ n₁ n₂ h₁ h₂} (E : PVEnds F₁ F₂ n₁ n₂ h₁ h₂) : Prop :=
  pvDepth n₁ n₂ E.B₁ < pvDepth n₁ n₂ E.B₂ ∧ pvDepth n₁ n₂ E.A₂ < pvDepth n₁ n₂ E.A₁ ∧
  ¬ IsLoIn (pvDepth n₁ n₂) F₁ E.A₁ ∧ ¬ IsHiIn (pvDepth n₁ n₂) F₁ E.B₁ ∧
  ¬ IsHiIn (pvDepth n₁ n₂) F₂ E.A₂ ∧ ¬ IsLoIn (pvDepth n₁ n₂) F₂ E.B₂

/-- (M+) of the paper. -/
def PVMixedPlus {F₁ F₂ n₁ n₂ h₁ h₂} (E : PVEnds F₁ F₂ n₁ n₂ h₁ h₂) : Prop :=
  pvDepth n₁ n₂ E.B₂ < pvDepth n₁ n₂ E.B₁ ∧ pvDepth n₁ n₂ E.A₁ < pvDepth n₁ n₂ E.A₂ ∧
  ¬ IsHiIn (pvDepth n₁ n₂) F₁ E.A₁ ∧ ¬ IsLoIn (pvDepth n₁ n₂) F₁ E.B₁ ∧
  ¬ IsLoIn (pvDepth n₁ n₂) F₂ E.A₂ ∧ ¬ IsHiIn (pvDepth n₁ n₂) F₂ E.B₂

/-- `p` projects strictly inside the shadow quadrilateral `A₁B₁B₂A₂` along `d`.  The cycle
`A₁B₁B₂A₂` is CLOCKWISE (PVOrient.lean), so interior means all four determinants are NEGATIVE
(phase 2a had `0 <`, which forces `H = ∅`: it contradicts `le₁`). -/
def PVHidden {F₁ F₂ n₁ n₂ h₁ h₂} (E : PVEnds F₁ F₂ n₁ n₂ h₁ h₂) (p : ℝ³) : Prop :=
  det3 (E.B₁ - E.A₁) (p - E.A₁) (cross n₁ n₂) < 0 ∧ det3 (E.B₂ - E.B₁) (p - E.B₁) (cross n₁ n₂) < 0 ∧
  det3 (E.A₂ - E.B₂) (p - E.B₂) (cross n₁ n₂) < 0 ∧ det3 (E.A₁ - E.A₂) (p - E.A₂) (cross n₁ n₂) < 0

end Minimality
