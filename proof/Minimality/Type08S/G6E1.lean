module

public import Minimality.Type08S.G6B7
public import Minimality.RobustCert
public import Minimality.RobustAxis

@[expose] public section

set_option autoImplicit true

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- 4-cycle robust unimodality from non-separation of the diagonal depth pairs. -/
theorem robust4 {z0 z1 z2 z3 : ℝ} (h : ¬ Sep z0 z2 z1 z3) :
    IsRobustUnimodal (quad z0 z1 z2 z3) := by
  have h' := h
  simp only [Sep, not_or, max_le_iff, le_min_iff, not_and_or, not_le] at h'
  obtain ⟨h1, h2⟩ := h'
  refine isRobustUnimodal_quad ?_ (fun hh => h ?_) (fun hh => h ?_)
  · unfold QuadTie
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro hh <;>
      rcases h1 with (h1 | h1) | (h1 | h1) <;> rcases h2 with (h2 | h2) | (h2 | h2) <;>
      first | (obtain ⟨e1, e2, e3⟩ := hh; linarith) | (obtain ⟨e1, e2⟩ := hh; linarith)
  · exact Or.inl (by simp only [max_le_iff, le_min_iff]; simp only [max_lt_iff, lt_min_iff] at hh; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith)
  · exact Or.inr (by simp only [max_le_iff, le_min_iff]; simp only [max_lt_iff, lt_min_iff] at hh; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith)


theorem frameMat_mem {e1 e2 e3 : ℝ³} (hF : Fr e1 e2 e3) : orthoFrameMat e1 e2 e3 ∈ SO3 := by
  have hI : IsFrame e1 e2 e3 := ⟨hF.n11, hF.n22, hF.n33, hF.n12, hF.n13, hF.n23⟩
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_unitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · have := hI.mul_transpose
    simpa [Matrix.star_eq_conjTranspose] using this
  · have h1 : (orthoFrameMat e1 e2 e3).det = det3 e1 e2 e3 := by
      simp [Matrix.det_fin_three, orthoFrameMat, det3_expand]; ring
    rw [h1, det3_eq_inner, hF.c23, hF.n11]

theorem frameMat_apply {e1 e2 e3 : ℝ³} (x : ℝ³) :
    proj_xy ((orthoFrameMat e1 e2 e3).toEuclideanLin x) = !₂[⟪x, e1⟫, ⟪x, e2⟫] ∧
    ((orthoFrameMat e1 e2 e3).toEuclideanLin x) 2 = ⟪x, e3⟫ := by
  rw [orthoFrameMat_apply]
  simp [proj_xy, Minimality.pt]


/-- **Theorem 18.1 (robust unimodal form) in an orthonormal frame with `e3 ∥ u₀`**, for a
quadrilateral rim `x`. -/
theorem frame_uniform {e1 e2 e3 : ℝ³} (hF : Fr e1 e2 e3) (V M D : Finset ℝ³) {ν : ℝ} (hν : 0 < ν)
    (x : ZMod 4 → ℝ³) (hxV : ∀ i, x i ∈ V) (hxM : ∀ i, x i ∉ M)
    (hcover : ∀ v ∈ V, v ∈ M ∨ v ∈ D ∨ ∃ i, v = x i)
    (hccw : IsCcwPolygon fun i => (!₂[⟪x i, e1⟫, ⟪x i, e2⟫] : ℝ²))
    (hz : IsRobustUnimodal fun i => ⟪x i, e3⟫)
    (hno : NoHDNAt (Finset.univ.image x) (ν • e3))
    (hM : ∀ m ∈ M, ∃ i : ZMod 4, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = x i + s • (x (i + 1) - x i) + δ • (ν • e3))
    (hD : ∀ y ∈ D, ∃ i : ZMod 4, ∃ h : ℝ, h ≠ 0 ∧ y = x i - h • (ν • e3)) : IsRupert V := by
  have hR := frameMat_mem hF
  have hRu : (orthoFrameMat e1 e2 e3).toEuclideanLin (ν • e3) = ν • ez := by
    have hn : ‖e3‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact hF.n33
    rw [orthoFrameMat_apply]
    ext i; fin_cases i <;>
      simp [Minimality.pt, ez, real_inner_smul_left, hF.n13, hF.n23, hn, real_inner_comm e1 e3, real_inner_comm e2 e3]
  have hpr : ∀ i, proj_xy ((orthoFrameMat e1 e2 e3).toEuclideanLin (x i)) =
      (!₂[⟪x i, e1⟫, ⟪x i, e2⟫] : ℝ²) := fun i => (frameMat_apply (x i)).1
  have hzz : ∀ i, ((orthoFrameMat e1 e2 e3).toEuclideanLin (x i)) 2 = ⟪x i, e3⟫ :=
    fun i => (frameMat_apply (x i)).2
  have hno' := hno _ hR ν hν.ne' hRu 4 x (fun i => mem_image.mpr ⟨i, mem_univ _, rfl⟩)
    (by simpa only [hpr] using hccw)
  refine isRupert_of_uniform_doubles_robustUnimodal V M D _ hR hν hRu x hxV hxM
    (by simpa only [hpr] using hccw) ?_ (by simpa only [hzz] using hz)
    (by simpa only [hpr, hzz] using hno') hM hD
  intro v hv hvM hvD hvx
  rcases hcover v hv with h | h | ⟨i, hi⟩
  · exact absurd h hvM
  · exact absurd h hvD
  · exact absurd hi (hvx i)

end Type08Sp
end Minimality
