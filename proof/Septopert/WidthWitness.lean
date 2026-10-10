module

public import Noperthedron.Pipeline.HalfTurnBasic

@[expose] public section

/-!
# Width witnesses (no central symmetry)

The deltoidal hexecontahedron's cap and tie witnesses are one-sided,
h_{RK}(d) ≥ h_K(d), and use K = −K for the other side. For a solid without
central symmetry the translation-free form is the width comparison: if two
points v_k, v_k' of S have
  ⟪n, proj(R v_k)⟫ − ⟪n, proj(R v_k')⟫ ≥ M₊ + M₋
where M₊, M₋ bound ⟪n, ·⟫ and ⟪−n, ·⟫ on the outer shadow, then no pose with
these rotations is Rupert, whatever the offset (it cancels in the
difference). That is, the inner shadow is at least as wide as the outer one
in the direction n.
-/

namespace Septopert
open Noperthedron

open scoped RealInnerProductSpace
open Noperthedron.Pipeline

theorem not_rupertPose_of_width_witness (p : MatrixPose) (S : Set ℝ³)
    (n : ℝ²) (hn : n ≠ 0) (Mp Mm : ℝ)
    (hMp : ∀ v ∈ S, ⟪n, proj_xyL (PoseLike.outer p v)⟫ ≤ Mp)
    (hMm : ∀ v ∈ S, -⟪n, proj_xyL (PoseLike.outer p v)⟫ ≤ Mm)
    (vk vk' : ℝ³) (hvk : vk ∈ S) (hvk' : vk' ∈ S)
    (hw : Mp + Mm ≤ ⟪n, proj_xyL (p.innerRot.val.toEuclideanLin vk)⟫ -
      ⟪n, proj_xyL (p.innerRot.val.toEuclideanLin vk')⟫) :
    ¬ RupertPose p S := by
  intro h
  have hup : ∀ y ∈ outerShadow p S, ⟪n, y⟫ ≤ Mp := by
    rintro _ ⟨v, hv, rfl⟩
    exact hMp v hv
  have hdown : ∀ y ∈ outerShadow p S, ⟪-n, y⟫ ≤ Mm := by
    rintro _ ⟨v, hv, rfl⟩
    rw [inner_neg_left]
    exact hMm v hv
  have hin : ∀ v ∈ S, proj_xyL (PoseLike.inner p v) ∈ interior (outerShadow p S) := by
    intro v hv
    exact h (subset_closure ⟨v, hv, rfl⟩)
  have h1 := inner_lt_of_mem_interior hn hup (hin vk hvk)
  have h2 := inner_lt_of_mem_interior (neg_ne_zero.mpr hn) hdown (hin vk' hvk')
  rw [MatrixPose.inner_apply, map_add, proj_inject_xy, inner_add_right] at h1
  rw [MatrixPose.inner_apply, map_add, proj_inject_xy, inner_add_right, inner_neg_left,
    inner_neg_left] at h2
  linarith

end Septopert
