module

public import Pipeline.HalfTurnBasic

@[expose] public section

/-!
# Scaling a solid

`rupertPose_of_smul`: if a pose is Rupert for `s • S` (s > 0), the same
rotations with the offset divided by `s` are Rupert for `S` (both shadows
scale by `s`). So a claim that no pose of a family (determined by the
rotations) is Rupert for `S` carries over to `s • S`.
-/

namespace Noperts.Pipeline

open scoped Pointwise

theorem proj_inner_smul (p : MatrixPose) (s : ℝ) (hs : s ≠ 0) (v : ℝ³) :
    proj_xyL (PoseLike.inner p (s • v)) =
      s • proj_xyL (PoseLike.inner ({ p with innerOffset := s⁻¹ • p.innerOffset } : MatrixPose) v) := by
  rw [MatrixPose.inner_apply, MatrixPose.inner_apply, map_add, map_add, proj_inject_xy, proj_inject_xy,
    map_smul, map_smul]
  simp only [smul_add, smul_smul, mul_inv_cancel₀ hs, one_smul]

theorem innerShadow_smul (p : MatrixPose) (S : Set ℝ³) (s : ℝ) (hs : s ≠ 0) :
    innerShadow p (s • S) = s • innerShadow ({ p with innerOffset := s⁻¹ • p.innerOffset } : MatrixPose) S := by
  ext y
  simp only [innerShadow, Set.mem_setOf_eq, Set.mem_smul_set]
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨_, ⟨v, hv, rfl⟩, (proj_inner_smul p s hs v).symm⟩
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨s • v, ⟨v, hv, rfl⟩, proj_inner_smul p s hs v⟩

theorem outerShadow_smul (p : MatrixPose) (S : Set ℝ³) (s : ℝ) :
    outerShadow p (s • S) = s • outerShadow ({ p with innerOffset := s⁻¹ • p.innerOffset } : MatrixPose) S := by
  ext y
  simp only [outerShadow, Set.mem_setOf_eq, Set.mem_smul_set]
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨_, ⟨v, hv, rfl⟩, by simp [PoseLike.outer, map_smul]⟩
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨s • v, ⟨v, hv, rfl⟩, by simp [PoseLike.outer, map_smul]⟩

theorem rupertPose_of_smul (p : MatrixPose) (S : Set ℝ³) (s : ℝ) (hs : 0 < s)
    (h : RupertPose p (s • S)) :
    RupertPose ({ p with innerOffset := s⁻¹ • p.innerOffset } : MatrixPose) S := by
  unfold RupertPose at h ⊢
  rw [innerShadow_smul p S s hs.ne', outerShadow_smul p S s, closure_smul₀' hs.ne', interior_smul₀ hs.ne'] at h
  exact (Set.smul_set_subset_smul_set_iff₀ hs.ne').mp h

end Noperts.Pipeline

end
