module

public import Noperthedron.Nopert7.Cell
public import Noperthedron.BalancedSupport.ViewAntipode

@[expose] public section

/-!
# Reducing the outer view of a C3v solid

Let S be invariant under the cyclic coordinate permutations c_k and under
the mirrors σ_i = −Q_i (coordinate transpositions). Three operations on
poses keep both shadows (so Rupert iff Rupert) and act on the view u (the
third row of the outer rotation):

- `bothRightC3 p k`: both rotations times c_k on the right; u ↦ c_kᵀ u.
- `mirrorScene p i`: both rotations become H_z · rot · Q_i (= D · rot · σ_i
  with D = diag(1,1,−1)); u ↦ Q_iᵀ u = −σ_i u. The relative rotation becomes
  σ_i R σ_i.
- `viewAntipode` (generic): u ↦ −u.

Together they reach every ±P u with P a coordinate permutation, so every
pose is equivalent to one whose view lies in the domain
u₀ ≥ u₁ ≥ u₂, u₀ + u₁ + u₂ ≥ 0 (`InC3vViewDomain`): the image maximizing
f(v) = 3 v₀ + 2 v₁ + v₂ is sorted (a transposition of an unsorted pair would
increase f) and has a nonnegative sum (negating and reversing would
increase f by 4 times the sum's absolute value).
-/

namespace Noperthedron.Nopert7

open scoped Matrix
open Noperthedron.PentagonalHexecontahedron

/-- The view domain: sorted, with a nonnegative sum. -/
def InC3vViewDomain (u : Fin 3 → ℝ) : Prop := u 1 ≤ u 0 ∧ u 2 ≤ u 1 ∧ 0 ≤ u 0 + u 1 + u 2

noncomputable def _root_.MatrixPose.bothRightC3 (p : MatrixPose) (k : Fin 3) : MatrixPose where
  innerRot := p.innerRot * c3SO3 k
  outerRot := p.outerRot * c3SO3 k
  innerOffset := p.innerOffset

noncomputable def _root_.MatrixPose.mirrorScene (p : MatrixPose) (i : Fin 3) : MatrixPose where
  innerRot := halfTurnZ * p.innerRot * mirrorQ i
  outerRot := halfTurnZ * p.outerRot * mirrorQ i
  innerOffset := p.innerOffset

section Shadows

variable (S : Set ℝ³)

theorem innerShadow_bothRightC3 (p : MatrixPose) (k : Fin 3)
    (hS : (c3Mat k).toEuclideanLin '' S = S) :
    innerShadow (p.bothRightC3 k) S = innerShadow p S := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨(c3Mat k).toEuclideanLin v, by rw [← hS]; exact ⟨v, hv, rfl⟩, ?_⟩
    simp [MatrixPose.inner_apply, MatrixPose.bothRightC3, c3SO3, Matrix.toLpLin_apply,
      Matrix.mulVec_mulVec]
  · rintro ⟨v, hv, rfl⟩
    have hv' : v ∈ (c3Mat k).toEuclideanLin '' S := by rwa [hS]
    obtain ⟨u, hu, rfl⟩ := hv'
    refine ⟨u, hu, ?_⟩
    simp [MatrixPose.inner_apply, MatrixPose.bothRightC3, c3SO3, Matrix.toLpLin_apply,
      Matrix.mulVec_mulVec]

theorem outerShadow_bothRightC3 (p : MatrixPose) (k : Fin 3)
    (hS : (c3Mat k).toEuclideanLin '' S = S) :
    outerShadow (p.bothRightC3 k) S = outerShadow p S := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨(c3Mat k).toEuclideanLin v, by rw [← hS]; exact ⟨v, hv, rfl⟩, ?_⟩
    simp [MatrixPose.bothRightC3, c3SO3, PoseLike.outer, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  · rintro ⟨v, hv, rfl⟩
    have hv' : v ∈ (c3Mat k).toEuclideanLin '' S := by rwa [hS]
    obtain ⟨u, hu, rfl⟩ := hv'
    refine ⟨u, hu, ?_⟩
    simp [MatrixPose.bothRightC3, c3SO3, PoseLike.outer, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

theorem RupertPose_bothRightC3_iff (p : MatrixPose) (k : Fin 3)
    (hS : (c3Mat k).toEuclideanLin '' S = S) :
    RupertPose (p.bothRightC3 k) S ↔ RupertPose p S := by
  unfold RupertPose
  rw [innerShadow_bothRightC3 S p k hS, outerShadow_bothRightC3 S p k hS]

theorem proj_outer_mirrorScene (p : MatrixPose) (i : Fin 3) (v : ℝ³) :
    proj_xyL (PoseLike.outer (p.mirrorScene i) v) =
      proj_xyL (PoseLike.outer p (-((mirrorQMat i).toEuclideanLin v))) := by
  have h : (p.mirrorScene i).outerRot.val.toEuclideanLin v =
      halfTurnZMat.toEuclideanLin (p.outerRot.val.toEuclideanLin ((mirrorQMat i).toEuclideanLin v)) := by
    simp [MatrixPose.mirrorScene, halfTurnZ, mirrorQ, Matrix.toLpLin_apply, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
  simp only [PoseLike.outer, AffineMap.coe_comp, LinearMap.coe_toAffineMap, Function.comp_apply] at h ⊢
  rw [h, proj_halfTurnZ, map_neg, map_neg]

theorem proj_inner_mirrorScene (p : MatrixPose) (i : Fin 3) (v : ℝ³) :
    proj_xyL (PoseLike.inner (p.mirrorScene i) v) =
      proj_xyL (PoseLike.inner p (-((mirrorQMat i).toEuclideanLin v))) := by
  -- The inner copy of mirrorScene is that of mirrorTie (same inner rotation and offset).
  have : PoseLike.inner (p.mirrorScene i) v = PoseLike.inner (p.mirrorTie (mirrorQ i)) v := rfl
  rw [this, proj_inner_mirrorTie]
  rfl

theorem innerShadow_mirrorScene (p : MatrixPose) (i : Fin 3)
    (hS : (fun v => -((mirrorQMat i).toEuclideanLin v)) '' S = S) :
    innerShadow (p.mirrorScene i) S = innerShadow p S := by
  have : innerShadow (p.mirrorScene i) S = innerShadow (p.mirrorTie (mirrorQ i)) S := rfl
  rw [this, innerShadow_mirrorTie p (mirrorQ i) S hS]

theorem outerShadow_mirrorScene (p : MatrixPose) (i : Fin 3)
    (hS : (fun v => -((mirrorQMat i).toEuclideanLin v)) '' S = S) :
    outerShadow (p.mirrorScene i) S = outerShadow p S := by
  ext w
  simp only [outerShadow, Set.mem_setOf_eq]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨_, by rw [← hS]; exact ⟨v, hv, rfl⟩, (proj_outer_mirrorScene p i v).symm⟩
  · rintro ⟨v, hv, rfl⟩
    have hv' : v ∈ (fun v => -((mirrorQMat i).toEuclideanLin v)) '' S := by rwa [hS]
    obtain ⟨u, hu, rfl⟩ := hv'
    exact ⟨u, hu, proj_outer_mirrorScene p i u⟩

theorem RupertPose_mirrorScene_iff (p : MatrixPose) (i : Fin 3)
    (hS : (fun v => -((mirrorQMat i).toEuclideanLin v)) '' S = S) :
    RupertPose (p.mirrorScene i) S ↔ RupertPose p S := by
  unfold RupertPose
  rw [innerShadow_mirrorScene S p i hS, outerShadow_mirrorScene S p i hS]

end Shadows

theorem view_bothRightC3 (p : MatrixPose) (k : Fin 3) :
    (p.bothRightC3 k).view = fun j => ∑ l, p.view l * c3Mat k l j := by
  funext j
  simp [MatrixPose.view, MatrixPose.bothRightC3, c3SO3, Matrix.mul_apply]

theorem view_mirrorScene (p : MatrixPose) (i : Fin 3) :
    (p.mirrorScene i).view = fun j => ∑ l, p.view l * mirrorQMat i l j := by
  funext j
  simp [MatrixPose.view, MatrixPose.mirrorScene, halfTurnZ, mirrorQ, halfTurnZMat, Matrix.mul_apply,
    Fin.sum_univ_three, Matrix.vecMul, dotProduct]

end Noperthedron.Nopert7
