module

public import Pipeline.HalfTurnBasic
public import Pipeline.CapBridge

@[expose] public section

/-!
# Balanced witnesses

The general form of the width witness (`Pipeline.WidthWitness`): contacts
`k` with directions `n_k` of the projection plane, nonnegative weights `λ_k`
that balance them (`Σ λ_k n_k = 0`), bounds `M_k` of `⟪n_k, ·⟫` on the outer
shadow, and points `v_k` of the solid with
  Σ λ_k M_k ≤ Σ λ_k ⟪n_k, proj(R v_k)⟫
(R the inner rotation). If some contact has `λ_k > 0` and `n_k ≠ 0`, no pose
with these rotations is Rupert, whatever the offset: the offset cancels in
the weighted sum, and each inner point is strictly inside the outer shadow.
The width witness is the case of two opposite directions with weights 1;
the snub cube's caps use three contacts (Cramer weights).
-/

namespace Noperts.Pipeline

open scoped Matrix RealInnerProductSpace

theorem not_rupertPose_of_balanced_witness (p : MatrixPose) (S : Set ℝ³)
    {ι : Type} [Fintype ι]
    (n : ι → ℝ²) (lam : ι → ℝ) (M : ι → ℝ) (vk : ι → ℝ³)
    (hlam : ∀ k, 0 ≤ lam k) (hbal : ∑ k, lam k • n k = 0)
    (hpos : ∃ k, 0 < lam k ∧ n k ≠ 0)
    (hM : ∀ k, ∀ v ∈ S, ⟪n k, proj_xyL (PoseLike.outer p v)⟫ ≤ M k)
    (hvk : ∀ k, vk k ∈ S)
    (hw : ∑ k, lam k * M k ≤
      ∑ k, lam k * ⟪n k, proj_xyL (p.innerRot.val.toEuclideanLin (vk k))⟫) :
    ¬ RupertPose p S := by
  intro h
  have hin : ∀ v ∈ S, proj_xyL (PoseLike.inner p v) ∈ interior (outerShadow p S) := by
    intro v hv
    exact h (subset_closure ⟨v, hv, rfl⟩)
  have hup : ∀ k, ∀ y ∈ outerShadow p S, ⟪n k, y⟫ ≤ M k := by
    rintro k _ ⟨v, hv, rfl⟩
    exact hM k v hv
  -- Each inner contact point is below its bound, strictly where n_k ≠ 0.
  have hle : ∀ k, ⟪n k, proj_xyL (PoseLike.inner p (vk k))⟫ ≤ M k := by
    intro k
    by_cases hn : n k = 0
    · rw [hn, inner_zero_left]
      have := hM k (vk k) (hvk k)
      rw [hn, inner_zero_left] at this
      exact this
    · exact (inner_lt_of_mem_interior hn (hup k) (hin (vk k) (hvk k))).le
  obtain ⟨k0, hlam0, hn0⟩ := hpos
  have hlt0 : ⟪n k0, proj_xyL (PoseLike.inner p (vk k0))⟫ < M k0 :=
    inner_lt_of_mem_interior hn0 (hup k0) (hin (vk k0) (hvk k0))
  -- The weighted sum of the inner contacts: the offset cancels.
  have hsplit : ∀ k, ⟪n k, proj_xyL (PoseLike.inner p (vk k))⟫ =
      ⟪n k, proj_xyL (p.innerRot.val.toEuclideanLin (vk k))⟫ + ⟪n k, p.innerOffset⟫ := by
    intro k
    rw [MatrixPose.inner_apply, map_add, proj_inject_xy, inner_add_right]
  have hcancel : ∑ k, lam k * ⟪n k, p.innerOffset⟫ = 0 := by
    have : ∑ k, lam k * ⟪n k, p.innerOffset⟫ = ⟪∑ k, lam k • n k, p.innerOffset⟫ := by
      rw [sum_inner]
      apply Finset.sum_congr rfl
      intro k _
      rw [inner_smul_left]
      simp
    rw [this, hbal, inner_zero_left]
  have hstrict : ∑ k, lam k * ⟪n k, proj_xyL (PoseLike.inner p (vk k))⟫ < ∑ k, lam k * M k := by
    apply Finset.sum_lt_sum
    · intro k _
      exact mul_le_mul_of_nonneg_left (hle k) (hlam k)
    · exact ⟨k0, Finset.mem_univ _, mul_lt_mul_of_pos_left hlt0 hlam0⟩
  have hsum : ∑ k, lam k * ⟪n k, proj_xyL (PoseLike.inner p (vk k))⟫ =
      ∑ k, lam k * ⟪n k, proj_xyL (p.innerRot.val.toEuclideanLin (vk k))⟫ := by
    simp only [hsplit, mul_add, Finset.sum_add_distrib, hcancel, add_zero]
  linarith

/-- The body-frame form: directions `d_k` perpendicular to the view (the
outer rotation maps them into the projection plane), balanced with
nonnegative weights, bounds `M_k` of `⟪d_k, ·⟫` on `S`, and points `v_k` of
`S` with `Σ λ_k M_k ≤ Σ λ_k ⟪d_k, R v_k⟫` for the relative rotation R. -/
theorem not_rupert_of_balanced_support (p : MatrixPose) (S : Set ℝ³)
    {ι : Type} [Fintype ι]
    (d : ι → ℝ³) (lam : ι → ℝ) (M : ι → ℝ) (vk : ι → ℝ³)
    (hview : ∀ k, (p.outerRot.val.toEuclideanLin (d k)) 2 = 0)
    (hlam : ∀ k, 0 ≤ lam k) (hbal : ∑ k, lam k • d k = 0)
    (hpos : ∃ k, 0 < lam k ∧ d k ≠ 0)
    (hM : ∀ k, ∀ v ∈ S, ⟪d k, v⟫ ≤ M k) (hvk : ∀ k, vk k ∈ S)
    (hw : ∑ k, lam k * M k ≤ ∑ k, lam k * ⟪d k, p.relativeRotation.toEuclideanLin (vk k)⟫) :
    ¬ RupertPose p S := by
  set O := p.outerRot.val
  have hO : Oᵀ * O = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp p.outerRot.property.1
  set n : ι → ℝ² := fun k => proj_xyL (O.toEuclideanLin (d k))
  have hproj : ∀ k (v : ℝ³), ⟪n k, proj_xyL (O.toEuclideanLin v)⟫ = ⟪d k, v⟫ := by
    intro k v
    simp only [n]
    rw [inner_proj_xyL, inner_orth O hO, hview k, zero_mul, sub_zero]
  have hinner : ∀ v : ℝ³, p.innerRot.val.toEuclideanLin v = O.toEuclideanLin (p.relativeRotation.toEuclideanLin v) := by
    intro v
    rw [← Noperts.Atlas.MatrixPose.outer_mul_relativeRotation p]
    simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec, O]
  have hbal' : ∑ k, lam k • n k = 0 := by
    have h : ∑ k, lam k • n k = proj_xyL (O.toEuclideanLin (∑ k, lam k • d k)) := by
      simp only [n, map_sum, map_smul]
    rw [h, hbal, map_zero, map_zero]
  obtain ⟨k0, hlam0, hd0⟩ := hpos
  have hn0 : n k0 ≠ 0 := by
    intro h0
    have h1 : ⟪n k0, n k0⟫ = 0 := by rw [h0]; simp
    simp only [n] at h1
    rw [inner_proj_xyL, inner_orth O hO, hview k0, mul_zero, sub_zero] at h1
    exact hd0 (inner_self_eq_zero.mp h1)
  apply not_rupertPose_of_balanced_witness p S n lam M vk hlam hbal' ⟨k0, hlam0, hn0⟩ _ hvk
  · simp only [hinner, hproj]
    exact hw
  · intro k v hv
    show ⟪n k, proj_xyL (p.outerRot.val.toEuclideanLin.toAffineMap v)⟫ ≤ M k
    simp only [LinearMap.coe_toAffineMap]
    rw [hproj]
    exact hM k v hv

end Noperts.Pipeline

end
