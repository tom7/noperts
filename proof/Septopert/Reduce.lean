module

public import Septopert.ViewReduce
public import Septopert.Model
public import Pipeline.AtlasPose
public import Pipeline.TightApproximation
public import Atlas.Tightening

@[expose] public section

/-!
# Atlas representatives for a C3v solid

`exists_c3v_atlas_translated_pose`: the C3v analogue of
`IModel.exists_halfTurn_atlas_translated_pose`. For a solid S invariant under
the cyclic coordinate permutations c_k and the improper symmetries
−Q_i = σ_i, every matrix pose is Rupert-equivalent to a bounded atlas pose
(rational root box, Cayley radius² ≤ 3) whose outer view lies in the C3v view
domain (`InC3vViewDomain`, inside the atlas wedge) and whose relative
rotation lies in the C3v cell at that view (`InC3vCell`).

Steps:
1. `exists_viewDomain_pose`: move the view into the domain u₀ ≥ u₁ ≥ 0, u₁ ≥ u₂.
2. `exists_euler_outer`: a screen rotation (`rotateBy`, keeps the view) makes
   the outer rotation `rotRM_mat θ φ 0` with φ ∈ [0, π] and θ ∈ [0, π/4]. Off
   the poles the domain forces the azimuth into [0, π/4]
   (`theta_mem_of_viewDomain`); at the poles u = (0,0,±1) (both in the domain's
   closure; (0,0,−1) is in the domain) a further screen rotation resets θ to 0
   (`Rz_mul_rotRM_mat_pole`). The domain contains views with u₂ < 0, so the
   upper-view condition φ ≤ π/2 is not available (and not claimed); the root
   box allows φ ∈ [0, 4].
3. `exists_c3v_reduced`: the trace-maximal candidate of `exists_c3v_reduction`,
   realized by `rightC3` (innerRot · c_j) or `mirrorTie` (H_z · innerRot · Q_j);
   both keep the outer rotation.
4. `exists_bounded_chart_cayley` for the relative rotation.

`exists_c3v_atlas_translated_pose_solid` instantiates S = `solid`, and
`exactModel_hull_eq_solid` identifies `solid` with the hull of the exact
9-slot model of `Vertices`.
-/

namespace Septopert
open Noperts

open scoped Matrix
open Noperts.Pipeline CayleyAtlas Real

/-! ### Right C3 on the inner copy -/

/-- Replace the inner rotation by innerRot · c_k (outer rotation and offset kept). -/
noncomputable def _root_.MatrixPose.rightC3 (p : MatrixPose) (k : Fin 3) : MatrixPose where
  innerRot := p.innerRot * c3SO3 k
  outerRot := p.outerRot
  innerOffset := p.innerOffset

theorem innerShadow_rightC3 (S : Set ℝ³) (p : MatrixPose) (k : Fin 3)
    (hS : (c3Mat k).toEuclideanLin '' S = S) :
    innerShadow (p.rightC3 k) S = innerShadow p S := by
  have : innerShadow (p.rightC3 k) S = innerShadow (p.bothRightC3 k) S := rfl
  rw [this, innerShadow_bothRightC3 S p k hS]

theorem RupertPose_rightC3_iff (S : Set ℝ³) (p : MatrixPose) (k : Fin 3)
    (hS : (c3Mat k).toEuclideanLin '' S = S) :
    RupertPose (p.rightC3 k) S ↔ RupertPose p S := by
  unfold RupertPose
  rw [innerShadow_rightC3 S p k hS]
  rfl

theorem relativeRotation_rightC3 (p : MatrixPose) (k : Fin 3) :
    (p.rightC3 k).relativeRotation = p.relativeRotation * c3Mat k := by
  show p.outerRot.valᵀ * (p.innerRot.val * c3Mat k) = p.outerRot.valᵀ * p.innerRot.val * c3Mat k
  rw [Matrix.mul_assoc]

/-! ### The cell reduction on poses -/

/-- The reduction of one pose: same outer rotation, relative rotation in the
C3v cell of its view, same Rupert-ness. -/
theorem exists_c3v_reduced (S : Set ℝ³) (hc : ∀ k, (c3Mat k).toEuclideanLin '' S = S)
    (hm : ∀ i, (fun v => -((mirrorQMat i).toEuclideanLin v)) '' S = S) (pose : MatrixPose) :
    ∃ reduced : MatrixPose, reduced.outerRot = pose.outerRot ∧
      InC3vCell pose.view reduced.relativeRotation ∧
      (RupertPose reduced S ↔ RupertPose pose S) := by
  have hu : ∑ k, pose.view k ^ 2 ≠ 0 := by rw [view_sq_sum]; norm_num
  obtain ⟨b, j, hcell⟩ := exists_c3v_reduction pose.view hu pose.relativeRotation
  cases b
  · refine ⟨pose.rightC3 j, rfl, ?_, RupertPose_rightC3_iff S pose j (hc j)⟩
    rw [relativeRotation_rightC3]
    simpa only [c3vCandidate, Bool.false_eq_true, ite_false] using hcell
  · refine ⟨pose.mirrorTie (mirrorQ j), rfl, ?_,
      RupertPose_mirrorTie_iff pose (mirrorQ j) S (hm j)⟩
    rw [relativeRotation_mirrorTie]
    simp only [c3vCandidate, ite_true] at hcell
    exact hcell

/-! ### Euler angles of the outer rotation -/

theorem Rz_mul_rotRM_mat (δ θ φ α : ℝ) :
    Rz_mat δ * rotRM_mat θ φ α = rotRM_mat θ φ (δ + α) := by
  simp only [rotRM_mat, ← Matrix.mul_assoc, Bounding.Rz_mat_mul_Rz_mat]
  congr 3
  ring

theorem Rz_mul_row2 (δ : ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (k : Fin 3) :
    (Rz_mat δ * M) 2 k = M 2 k := by
  simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem view_rotateBy (p : MatrixPose) (δ : ℝ) : (p.rotateBy δ).view = p.view := by
  funext k
  exact Rz_mul_row2 δ p.outerRot.val k

/-- The third row of `rotRM_mat θ φ 0`: (cos θ sin φ, sin θ sin φ, cos φ). -/
theorem rotRM_mat_row2_zero (θ φ : ℝ) :
    rotRM_mat θ φ 0 2 0 = cos θ * sin φ ∧ rotRM_mat θ φ 0 2 1 = sin θ * sin φ ∧
      rotRM_mat θ φ 0 2 2 = cos φ := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [rotRM_mat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/-- At a pole (sin φ = 0) the azimuth θ is a screen rotation. -/
theorem Rz_mul_rotRM_mat_pole {θ φ : ℝ} (h : sin φ = 0) :
    Rz_mat (θ * cos φ) * rotRM_mat θ φ 0 = rotRM_mat 0 φ 0 := by
  have hc : cos φ = 1 ∨ cos φ = -1 := by
    have hsq := sin_sq_add_cos_sq φ
    rw [h] at hsq
    have : (cos φ - 1) * (cos φ + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h1 | h1
    · left; linarith
    · right; linarith
  rcases hc with hc | hc
  · have hRy : Ry_mat φ = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Ry_mat, h, hc]
    simp only [rotRM_mat, hRy, Matrix.mul_one, Bounding.Rz_mat_mul_Rz_mat, hc]
    congr 1
    ring
  · have hRy : Ry_mat φ * Rz_mat (-θ) = Rz_mat θ * Ry_mat φ := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Ry_mat, Rz_mat, h, hc, Matrix.mul_apply, Fin.sum_univ_three]
    have h0 : Rz_mat (-0) = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Rz_mat]
    simp only [rotRM_mat, Matrix.mul_assoc, hRy, h0, Matrix.mul_one]
    simp only [← Matrix.mul_assoc, Bounding.Rz_mat_mul_Rz_mat, hc]
    congr 2
    ring

/-- Off the poles, a view in the domain has azimuth in [0, π/4]. -/
theorem theta_mem_of_viewDomain {θ φ : ℝ} (hθ : θ ∈ Set.Ioc (-π) π) (hsin : 0 < sin φ)
    (h0 : sin θ * sin φ ≤ cos θ * sin φ) (h1 : 0 ≤ sin θ * sin φ) :
    θ ∈ Set.Icc 0 (π / 4) := by
  have hs : 0 ≤ sin θ := nonneg_of_mul_nonneg_left h1 hsin
  have hcs : sin θ ≤ cos θ := le_of_mul_le_mul_right h0 hsin
  have hθ0 : 0 ≤ θ := by
    by_contra hneg
    push Not at hneg
    have := sin_neg_of_neg_of_neg_pi_lt hneg hθ.1
    linarith
  refine ⟨hθ0, ?_⟩
  by_contra hgt
  push Not at hgt
  have hpos : 0 < sin (θ - π / 4) :=
    sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθ.2, pi_pos])
  rw [sin_sub, cos_pi_div_four, sin_pi_div_four] at hpos
  have hsq : 0 < √2 / 2 := by positivity
  nlinarith

/-- A screen rotation puts the outer rotation of a pose with view in the
domain into the form `rotRM_mat θ φ 0` with θ ∈ [0, π/4], φ ∈ [0, π]. -/
theorem exists_euler_outer (p : MatrixPose) (hdom : InC3vViewDomain p.view) :
    ∃ δ θ φ : ℝ, θ ∈ Set.Icc 0 (π / 4) ∧ φ ∈ Set.Icc 0 π ∧
      (p.rotateBy δ).outerRot.val = rotRM_mat θ φ 0 := by
  obtain ⟨θo, φo, αo, hθo, hφo, -, hM⟩ :=
    Noperts.Atlas.SO3_to_bounded_rotRM_params p.outerRot.val p.outerRot.property
  have hout : Rz_mat (-αo) * p.outerRot.val = rotRM_mat θo φo 0 := by
    rw [hM, Rz_mul_rotRM_mat, neg_add_cancel]
  have hview : ∀ k, p.view k = rotRM_mat θo φo 0 2 k := by
    intro k
    rw [← hout, Rz_mul_row2]
    rfl
  by_cases hs : sin φo = 0
  · refine ⟨θo * cos φo + -αo, 0, φo, ⟨le_rfl, by positivity⟩, hφo, ?_⟩
    show Rz_mat (θo * cos φo + -αo) * p.outerRot.val = _
    rw [← Bounding.Rz_mat_mul_Rz_mat, Matrix.mul_assoc, hout, Rz_mul_rotRM_mat_pole hs]
  · have hspos : 0 < sin φo := lt_of_le_of_ne (sin_nonneg_of_mem_Icc hφo) (Ne.symm hs)
    obtain ⟨hd0, hd1, -⟩ := hdom
    obtain ⟨r0, r1, -⟩ := rotRM_mat_row2_zero θo φo
    rw [hview, hview, r0, r1] at hd0
    rw [hview, r1] at hd1
    exact ⟨-αo, θo, φo, theta_mem_of_viewDomain hθo hspos hd0 hd1, hφo, hout⟩

/-! ### The atlas representative -/

/-- An atlas pose equals any matrix pose with outer rotation `rotRM_mat θ φ 0`,
relative rotation chart · cayley(x, y, z), and the same offset. -/
theorem matrixPoseWithOffset_eq_of (q : AtlasPose ℝ) (reduced : MatrixPose)
    (houter : reduced.outerRot.val = rotRM_mat q.θ q.φ 0) (chart : ChartIndex)
    (hrelative : reduced.relativeRotation = chartMatrix chart * cayleyMatrix q.x q.y q.z) :
    q.matrixPoseWithOffset chart reduced.innerOffset = reduced := by
  apply matrixPose_ext_val
  · calc
      (q.matrixPoseWithOffset chart reduced.innerOffset).innerRot.val =
          rotRM_mat q.θ q.φ 0 * (chartMatrix chart * cayleyMatrix q.x q.y q.z) := by
            change (rotRM_mat q.θ q.φ 0 * chartMatrix chart) * cayleyMatrix q.x q.y q.z =
              rotRM_mat q.θ q.φ 0 * (chartMatrix chart * cayleyMatrix q.x q.y q.z)
            rw [Matrix.mul_assoc]
      _ = reduced.outerRot.val * reduced.relativeRotation := by rw [hrelative, houter]
      _ = reduced.innerRot.val := Noperts.Atlas.MatrixPose.outer_mul_relativeRotation reduced
  · exact houter.symm
  · rfl

/-- Every matrix pose of a C3v solid has an equivalent bounded atlas
representative whose view lies in the C3v view domain (and the atlas wedge)
and whose relative rotation lies in the C3v cell at that view. -/
theorem exists_c3v_atlas_translated_pose (S : Set ℝ³)
    (hc : ∀ k, (c3Mat k).toEuclideanLin '' S = S)
    (hm : ∀ i, (fun v => -((mirrorQMat i).toEuclideanLin v)) '' S = S) (p : MatrixPose) :
    ∃ chart : ChartIndex, ∃ q : AtlasPose ℝ, ∃ offset : ℝ²,
      q ∈ AtlasPose.rootInterval ℝ ∧ q.CayleyBounded ∧ q.InViewWedge ∧
      InC3vViewDomain (fun k => rotRM_mat q.θ q.φ 0 2 k) ∧
      InC3vCell (fun k => rotRM_mat q.θ q.φ 0 2 k) (chartMatrix chart * cayleyMatrix q.x q.y q.z) ∧
      (RupertPose (q.matrixPoseWithOffset chart offset) S ↔ RupertPose p S) := by
  obtain ⟨p1, hdom1, heq1⟩ := exists_viewDomain_pose S hc hm p
  obtain ⟨δ, θ, φ, hθ, hφ, hout⟩ := exists_euler_outer p1 hdom1
  have heq2 : RupertPose (p1.rotateBy δ) S ↔ RupertPose p1 S :=
    MatrixPose.RupertPose_rotateBy_iff p1 δ S
  obtain ⟨reduced, houter, hcell, hiff⟩ := exists_c3v_reduced S hc hm (p1.rotateBy δ)
  obtain ⟨chart, x, hx, y, hy, z, hz, hradius, hrelative⟩ :=
    exists_bounded_chart_cayley reduced.relativeRotation
      (Noperts.Atlas.MatrixPose.relativeRotation_mem_SO3 reduced)
  let q : AtlasPose ℝ := ⟨θ, φ, x, y, z⟩
  have houter' : reduced.outerRot.val = rotRM_mat q.θ q.φ 0 := by rw [houter]; exact hout
  have hview : (fun k => rotRM_mat q.θ q.φ 0 2 k) = (p1.rotateBy δ).view := by
    funext k
    show rotRM_mat θ φ 0 2 k = (p1.rotateBy δ).outerRot.val 2 k
    rw [hout]
  have hmatrix : q.matrixPoseWithOffset chart reduced.innerOffset = reduced :=
    matrixPoseWithOffset_eq_of q reduced houter' chart hrelative
  have hpi4 : π / 4 ≤ 1 := by linarith [pi_le_four]
  refine ⟨chart, q, reduced.innerOffset, ?_, hradius, ⟨⟨hθ.1, ?_⟩, hφ⟩, ?_, ?_, ?_⟩
  · rw [NonemptyInterval.mem_def, AtlasPose.le_iff, AtlasPose.le_iff]
    dsimp only [AtlasPose.rootInterval, q]
    exact ⟨⟨hθ.1, hφ.1, hx.1, hy.1, hz.1⟩,
      ⟨by linarith [hθ.2], hφ.2.trans pi_le_four, hx.2, hy.2, hz.2⟩⟩
  · show θ ≤ 2 * π / 5
    linarith [hθ.2, pi_pos]
  · rw [hview, view_rotateBy]
    exact hdom1
  · show InC3vCell (fun k => rotRM_mat q.θ q.φ 0 2 k) (chartMatrix chart * cayleyMatrix x y z)
    rw [← hrelative, hview]
    exact hcell
  · rw [hmatrix, hiff, heq2, heq1]

/-! ### The solid -/

theorem solid_c3 (k : Fin 3) : (c3Mat k).toEuclideanLin '' solid = solid := c3Mat_image_solid k

theorem solid_mirror (i : Fin 3) :
    (fun v => -((mirrorQMat i).toEuclideanLin v)) '' solid = solid := mirrorQ_neg_image_solid i

theorem exists_c3v_atlas_translated_pose_solid (p : MatrixPose) :
    ∃ chart : ChartIndex, ∃ q : AtlasPose ℝ, ∃ offset : ℝ²,
      q ∈ AtlasPose.rootInterval ℝ ∧ q.CayleyBounded ∧ q.InViewWedge ∧
      InC3vViewDomain (fun k => rotRM_mat q.θ q.φ 0 2 k) ∧
      InC3vCell (fun k => rotRM_mat q.θ q.φ 0 2 k) (chartMatrix chart * cayleyMatrix q.x q.y q.z) ∧
      (RupertPose (q.matrixPoseWithOffset chart offset) solid ↔ RupertPose p solid) :=
  exists_c3v_atlas_translated_pose solid solid_c3 solid_mirror p

/-- The exact 9-slot model of `Vertices` has hull `solid`. -/
theorem exactModel_hull_eq_solid : exactModel.polyhedron.hull = solid := by
  unfold solid Polyhedron.hull
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, CyclicModel.polyhedron_vertex, exactModel_vertex, exactVertex_eq,
    rationalVertex_eq_vertexQ, poly]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨i, rfl⟩ := vertexQIndex_surjective a
    exact ⟨i, rfl⟩

end Septopert
