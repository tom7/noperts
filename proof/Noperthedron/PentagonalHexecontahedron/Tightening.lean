module

public import Noperthedron.PentagonalHexecontahedron.Symmetry
public import Noperthedron.BalancedSupport.UniversalDomain
public import Noperthedron.BalancedSupport.ViewAntipode

@[expose] public section

/-!
# The pose domain

`tightPoseInterval` is the rational Euler box of the atlas root, and
`InViewWedge` the outer-view azimuth wedge `[0, 2π/5]` of the atlas cover
(for the C3v solid the view domain has azimuth in `[0, π/4]`, inside the
wedge). `translated_rupert_iff_of_images` transfers Rupert poses between
Euler poses with equal shadows.

(The fivefold pipeline reduced both azimuths modulo `2π/5` here,
`tighten_theta`; with the C3 axis along (1,1,1) that reduction does not
apply and was removed.)
-/

namespace Noperthedron.PentagonalHexecontahedron

variable {P : C5Model}

open Real
open Noperthedron.BalancedSupport

noncomputable def tightPoseInterval : PoseInterval ℝ :=
  PoseInterval.mk
    { θ₁ := -4 / 5, θ₂ := 0, φ₁ := 0, φ₂ := 0, α := -4 }
    { θ₁ := 12 / 5, θ₂ := 8 / 5, φ₁ := 4, φ₂ := 4, α := 4 }
    (by rw [Pose.le_iff]; norm_num)

/-- The exact angular wedge of outer views covered by the atlas.
Unlike the rational root box, these sharp bounds preserve the signs of the
first two outer viewing coordinates. -/
def InViewWedge (q : Pose ℝ) : Prop :=
  q.θ₂ ∈ Set.Icc 0 (2 * π / 5) ∧ q.φ₂ ∈ Set.Icc 0 π

private theorem translated_innerShadow_eq (p : Pose ℝ) (offset : ℝ²)
    (S : Set ℝ³) :
    innerShadow (p.matrixPoseWithOffset offset) S =
      (fun x : ℝ² => x + offset) '' (p.inner '' S) := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨p.inner v, ⟨v, hv, rfl⟩, ?_⟩
    rw [Noperthedron.BalancedSupport.project_inner_apply,
      matrixPoseWithOffset_inner_rotation_project]
    rfl
  · rintro ⟨y, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨v, hv, ?_⟩
    rw [Noperthedron.BalancedSupport.project_inner_apply,
      matrixPoseWithOffset_inner_rotation_project]
    rfl

private theorem translated_outerShadow_eq (p : Pose ℝ) (offset : ℝ²)
    (S : Set ℝ³) :
    outerShadow (p.matrixPoseWithOffset offset) S = p.outer '' S := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, (matrixPoseWithOffset_outer_project p offset v).symm⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, matrixPoseWithOffset_outer_project p offset v⟩

theorem translated_rupert_iff_of_images {p q : Pose ℝ}
    (offset : ℝ²)
    (hinner : p.inner '' P.polyhedron.hull =
      q.inner '' P.polyhedron.hull)
    (houter : p.outer '' P.polyhedron.hull =
      q.outer '' P.polyhedron.hull) :
    RupertPose (p.matrixPoseWithOffset offset) P.polyhedron.hull ↔
      RupertPose (q.matrixPoseWithOffset offset) P.polyhedron.hull := by
  unfold RupertPose
  rw [translated_innerShadow_eq, translated_innerShadow_eq,
    translated_outerShadow_eq, translated_outerShadow_eq,
    hinner, houter]

end Noperthedron.PentagonalHexecontahedron

end
