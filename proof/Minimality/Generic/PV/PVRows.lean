module

public import Minimality.Generic.PV.PVFaceChain
public import Minimality.Generic.PV.FaceCircle

@[expose] public section


/-! Row families of the PV rim: chain edges (via `tiltSignS_edge`), the two bridges, and the
hidden-points / off-plane lemmas. -/

namespace Minimality
open scoped RealInnerProductSpace
open Finset

theorem det3_pair (n₁ n₂ a b : ℝ³) :
    det3 a b (cross n₁ n₂) = ⟪a, n₁⟫ * ⟪b, n₂⟫ - ⟪a, n₂⟫ * ⟪b, n₁⟫ := by
  simp only [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]
  simp; ring

theorem det3_nea (n d e : ℝ³) : det3 n e d = - ⟪cross n d, e⟫ := by
  simp only [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]
  simp; ring

theorem inner_v1 (n₁ n₂ : ℝ³) :
    ⟪n₁, cross n₂ (cross n₁ n₂)⟫ = ⟪cross n₁ n₂, cross n₁ n₂⟫ := by
  simp only [cross, PiLp.inner_apply, Fin.sum_univ_three]
  simp; ring

theorem inner_v2 (n₁ n₂ : ℝ³) :
    ⟪n₂, cross (cross n₁ n₂) n₁⟫ = ⟪cross n₁ n₂, cross n₁ n₂⟫ := by
  simp only [cross, PiLp.inner_apply, Fin.sum_univ_three]
  simp; ring

theorem inner_v1' (n₁ n₂ : ℝ³) : ⟪n₂, cross n₂ (cross n₁ n₂)⟫ = 0 := by
  simp only [cross, PiLp.inner_apply, Fin.sum_univ_three]
  simp; ring

theorem inner_v2' (n₁ n₂ : ℝ³) : ⟪n₁, cross (cross n₁ n₂) n₁⟫ = 0 := by
  simp only [cross, PiLp.inner_apply, Fin.sum_univ_three]
  simp; ring

theorem inner_d1 (n₁ n₂ : ℝ³) : ⟪n₁, cross n₁ n₂⟫ = 0 := by
  rw [real_inner_comm]; exact inner_cross_left _ _

theorem inner_d2 (n₁ n₂ : ℝ³) : ⟪n₂, cross n₁ n₂⟫ = 0 := by
  rw [real_inner_comm]; exact inner_cross_right _ _

/-- `⟪n₂, ·⟫` on the plane of `F₁` is `-t₁ / |n₁|²`. -/
theorem t1_rel (n₁ n₂ u : ℝ³) (hu : ⟪n₁, u⟫ = 0) :
    ⟪n₁, n₁⟫ * ⟪n₂, u⟫ = - ⟪cross n₁ (cross n₁ n₂), u⟫ := by
  simp only [cross, PiLp.inner_apply, Fin.sum_univ_three] at hu ⊢
  simp at hu ⊢
  linear_combination (n₁ 0 * n₂ 0 + n₁ 1 * n₂ 1 + n₁ 2 * n₂ 2) * hu

theorem t2_rel (n₁ n₂ u : ℝ³) (hu : ⟪n₂, u⟫ = 0) :
    ⟪n₂, n₂⟫ * ⟪n₁, u⟫ = ⟪cross n₂ (cross n₁ n₂), u⟫ := by
  simp only [cross, PiLp.inner_apply, Fin.sum_univ_three] at hu ⊢
  simp at hu ⊢
  linear_combination (n₁ 0 * n₂ 0 + n₁ 1 * n₂ 1 + n₁ 2 * n₂ 2) * hu

end Minimality
