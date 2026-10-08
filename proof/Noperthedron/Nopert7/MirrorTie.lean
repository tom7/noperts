module

public import Noperthedron.PentagonalHexecontahedron.HalfTurnReduce

@[expose] public section

/-!
# The mirror-tie reduction (solids with a mirror symmetry)

Let σ = −Q be an improper symmetry of the solid S (Q a rotation with
−Q S = S, e.g. a reflection σ in a mirror of S, Q = −σ the half-turn about
the mirror's normal). Projecting along z ignores the reflection
D = diag(1, 1, −1), and D = −H_z with H_z the half-turn about z. So turning
the inner copy into D · innerRot · σ = H_z · innerRot · Q leaves the inner
shadow unchanged (no central symmetry needed, offset kept), and the pose stays
Rupert iff it was (`RupertPose_mirrorTie_iff`). In terms of the outer view u
the relative rotation becomes H_u R Q (`relativeRotation_mirrorTie`): the same
form as the deltoidal hexecontahedron's half-turn reduction, with Q ranging
over the solid's improper symmetries instead of (H_u-composed) rotations. The
cell condition has the same shape as `InHalfTurnCell` (`Cell.lean`); the DH
prune boxes (`AtlasHalfTurnPrune.Box`, indexed by `IcoIndex`) need
generalizing to an indexed table of Q's.

For a 3-fold axis along (1,1,1), the mirrors of a C3v solid are the
coordinate transpositions; Q = −σ is then rational.
-/

namespace Noperthedron.Nopert7

open scoped Matrix
open Noperthedron.PentagonalHexecontahedron

/-- Turn the inner copy into H_z · innerRot · Q (= D · innerRot · (−Q)), keeping
the offset. -/
noncomputable def _root_.MatrixPose.mirrorTie (p : MatrixPose) (Q : SO3) : MatrixPose where
  innerRot := halfTurnZ * p.innerRot * Q
  outerRot := p.outerRot
  innerOffset := p.innerOffset

theorem proj_inner_mirrorTie (p : MatrixPose) (Q : SO3) (v : ℝ³) :
    proj_xyL (PoseLike.inner (p.mirrorTie Q) v) =
      proj_xyL (PoseLike.inner p (-(Q.val.toEuclideanLin v))) := by
  rw [MatrixPose.inner_apply, MatrixPose.inner_apply, map_add, map_add, proj_inject_xy,
    proj_inject_xy]
  have h : (p.mirrorTie Q).innerRot.val.toEuclideanLin v =
      halfTurnZMat.toEuclideanLin (p.innerRot.val.toEuclideanLin (Q.val.toEuclideanLin v)) := by
    simp [MatrixPose.mirrorTie, halfTurnZ, Matrix.toLpLin_apply, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
  rw [h, proj_halfTurnZ, map_neg, map_neg]
  simp [MatrixPose.mirrorTie]

/-- The inner shadow is unchanged when −Q maps the solid onto itself. -/
theorem innerShadow_mirrorTie (p : MatrixPose) (Q : SO3) (S : Set ℝ³)
    (hQ : (fun v => -(Q.val.toEuclideanLin v)) '' S = S) :
    innerShadow (p.mirrorTie Q) S = innerShadow p S := by
  ext w
  simp only [innerShadow, Set.mem_setOf_eq]
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨-(Q.val.toEuclideanLin v), ?_, (proj_inner_mirrorTie p Q v).symm⟩
    rw [← hQ]
    exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    have hv' : v ∈ (fun v => -(Q.val.toEuclideanLin v)) '' S := by rwa [hQ]
    obtain ⟨u, hu, rfl⟩ := hv'
    exact ⟨u, hu, proj_inner_mirrorTie p Q u⟩

theorem outerShadow_mirrorTie (p : MatrixPose) (Q : SO3) (S : Set ℝ³) :
    outerShadow (p.mirrorTie Q) S = outerShadow p S := rfl

/-- The mirror-tie reduction preserves Rupert poses of a solid with the
improper symmetry −Q. -/
theorem RupertPose_mirrorTie_iff (p : MatrixPose) (Q : SO3) (S : Set ℝ³)
    (hQ : (fun v => -(Q.val.toEuclideanLin v)) '' S = S) :
    RupertPose (p.mirrorTie Q) S ↔ RupertPose p S := by
  unfold RupertPose
  rw [innerShadow_mirrorTie p Q S hQ, outerShadow_mirrorTie]

/-- With the outer view u, the relative rotation becomes H_u R Q. -/
theorem relativeRotation_mirrorTie (p : MatrixPose) (Q : SO3) :
    (p.mirrorTie Q).relativeRotation = halfTurnMat p.view * p.relativeRotation * Q.val := by
  have horth := (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp p.outerRot.property.1
  rw [halfTurnMat_view]
  simp only [MatrixPose.relativeRotation, MatrixPose.mirrorTie, halfTurnZ]
  show p.outerRot.valᵀ * (halfTurnZMat * p.innerRot.val * Q.val) = _
  rw [show p.outerRot.valᵀ * halfTurnZMat * p.outerRot.val * (p.outerRot.valᵀ * p.innerRot.val) * Q.val =
      p.outerRot.valᵀ * halfTurnZMat * (p.outerRot.val * p.outerRot.valᵀ) * p.innerRot.val * Q.val by
    simp only [Matrix.mul_assoc]]
  rw [horth, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

end Noperthedron.Nopert7
