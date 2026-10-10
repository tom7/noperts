module

public import MatrixPose

@[expose] public section

/-!
# Half-turns (shape-independent)

The half-turn H_z about the projection axis (it negates the projection), the
half-turn `halfTurnMat u` about the line through a view u, and their basic
facts: H_u = outerRotᵀ H_z outerRot for the view of a pose
(`halfTurnMat_view`) and H_u² = 1. Also `inner_lt_of_mem_interior`. Split
out of `HalfTurn`, `AtlasHalfTurnPrune`, `HalfTurnReduce` and `CapWitness`
(which import this) so that solids without the icosahedral layer can use
them.
-/

namespace Noperts.Pipeline

open scoped Matrix RealInnerProductSpace

/-- The view of a pose: the third row of its outer rotation. -/
noncomputable def _root_.MatrixPose.view (p : MatrixPose) : Fin 3 → ℝ :=
  fun k => p.outerRot.val 2 k

/-- The half-turn about the projection axis z. -/
def halfTurnZMat : Matrix (Fin 3) (Fin 3) ℝ := !![-1, 0, 0; 0, -1, 0; 0, 0, 1]

theorem halfTurnZMat_mem : halfTurnZMat ∈ SO3 := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [halfTurnZMat, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [halfTurnZMat, Matrix.det_fin_three]

noncomputable def halfTurnZ : SO3 := ⟨halfTurnZMat, halfTurnZMat_mem⟩

theorem proj_halfTurnZ (v : ℝ³) :
    proj_xyL (halfTurnZMat.toEuclideanLin v) = -proj_xyL v := by
  ext i
  fin_cases i <;>
    simp [proj_xyL, proj_xy_mat, halfTurnZMat, Matrix.toLpLin_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three]

theorem proj_inject_xy (w : ℝ²) : proj_xyL (inject_xy w) = w := by
  ext i
  fin_cases i <;> simp [proj_xyL, proj_xy_mat, inject_xy, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_three]

/-- The half-turn about the line through `u` (for u ≠ 0). -/
noncomputable def halfTurnMat (u : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => 2 * u i * u j / (∑ k, u k ^ 2) - if i = j then 1 else 0

theorem view_sq_sum (p : MatrixPose) : ∑ k, p.view k ^ 2 = 1 := by
  have h := (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp p.outerRot.property.1
  have h22 := congrFun (congrFun h 2) 2
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h22
  simpa [MatrixPose.view, sq] using h22

theorem halfTurnMat_view (p : MatrixPose) :
    halfTurnMat p.view = p.outerRot.valᵀ * halfTurnZMat * p.outerRot.val := by
  have horth := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp p.outerRot.property.1
  have hs : p.outerRot.val 2 0 ^ 2 + p.outerRot.val 2 1 ^ 2 + p.outerRot.val 2 2 ^ 2 = 1 := by
    have := view_sq_sum p
    simpa [MatrixPose.view, Fin.sum_univ_three] using this
  ext i j
  have hij := congrFun (congrFun horth i) j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three] at hij
  simp only [halfTurnMat, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, halfTurnZMat,
    MatrixPose.view, hs, div_one]
  simp [Matrix.of_apply, Matrix.one_apply] at hij ⊢
  split_ifs at hij ⊢ <;> linarith

theorem halfTurnMat_mul_self (u : Fin 3 → ℝ) (hu : ∑ k, u k ^ 2 ≠ 0) :
    halfTurnMat u * halfTurnMat u = 1 := by
  ext i j
  simp only [halfTurnMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] at hu ⊢
  field_simp
  fin_cases i <;> fin_cases j <;> simp <;> ring_nf <;> nlinarith [hu]

/-- H_u depends only on the line through u. -/
theorem halfTurnMat_smul (κ : ℝ) (hκ : κ ≠ 0) (u : Fin 3 → ℝ) : halfTurnMat (κ • u) = halfTurnMat u := by
  ext i j
  simp only [halfTurnMat, Pi.smul_apply, smul_eq_mul]
  congr 1
  rw [show ∑ k, (κ * u k) ^ 2 = κ ^ 2 * ∑ k, u k ^ 2 by rw [Finset.mul_sum]; congr 1; ext k; ring]
  by_cases hs : ∑ k, u k ^ 2 = 0
  · rw [hs]; simp
  · field_simp

/-- A linear functional bounded by M on A is < M on the interior of A (n ≠ 0). -/
theorem inner_lt_of_mem_interior {A : Set ℝ²} {n : ℝ²} (hn : n ≠ 0) {M : ℝ}
    (hA : ∀ y ∈ A, ⟪n, y⟫ ≤ M) {y : ℝ²} (hy : y ∈ interior A) : ⟪n, y⟫ < M := by
  have hnhds : A ∈ nhds y := mem_interior_iff_mem_nhds.mp hy
  have hcont : Filter.Tendsto (fun t : ℝ => y + t • n) (nhds 0) (nhds y) := by
    have : Continuous (fun t : ℝ => y + t • n) := by fun_prop
    simpa using this.tendsto 0
  have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), y + t • n ∈ A :=
    (hcont.eventually hnhds).filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ht, ht0⟩ := (hev.and self_mem_nhdsWithin).exists
  have h := hA _ ht
  rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq] at h
  have hpos : 0 < t * ‖n‖ ^ 2 := mul_pos ht0 (by positivity)
  linarith

end Noperts.Pipeline
