module

public import Noperthedron.Septopert.Cell
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
u₀ ≥ u₁ ≥ 0, u₁ ≥ u₂ (`InC3vViewDomain`, the cone over (1,1,1), (1,0,0) and
(0,0,−1), 1/12 of the sphere): sort u, and if the middle coordinate is
negative apply u ↦ −(u₂, u₁, u₀). The domain lies in the projective roots 0
and 1, its Euler azimuth is in [0, π/4], and it contains one mirror normal,
(1,0,−1)/√2, on its boundary.
-/

namespace Noperthedron.Septopert

open scoped Matrix
open Noperthedron.PentagonalHexecontahedron

/-- The view domain: u₀ ≥ u₁ ≥ 0 and u₁ ≥ u₂. -/
def InC3vViewDomain (u : Fin 3 → ℝ) : Prop := u 1 ≤ u 0 ∧ 0 ≤ u 1 ∧ u 2 ≤ u 1

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

/-- The candidate views: ±(c_jᵀ u) (not b) or ±(Q_jᵀ u) (b), negated if s. -/
noncomputable def candView (u : Fin 3 → ℝ) (s b : Bool) (j : Fin 3) : Fin 3 → ℝ :=
  fun l => (if s then -1 else 1) * ∑ m, u m * (if b then mirrorQMat j else c3Mat j) m l

/-- Some candidate view lies in the domain. -/
theorem exists_candView_domain (u : Fin 3 → ℝ) : ∃ s b j, InC3vViewDomain (candView u s b j) := by
  rcases le_total (u 0) (u 1) with h01 | h01
  · rcases le_total (u 1) (u 2) with h12 | h12
    · rcases le_total (u 0) (u 2) with h02 | h02
      · rcases le_total 0 (u 1) with hm | hm
        · exact ⟨true, true, 1, by
            simp only [InC3vViewDomain, candView, c3Mat, mirrorQMat, mirrorMat, Fin.sum_univ_three]
            simp
            all_goals (try constructorm* _ ∧ _)
            all_goals linarith⟩
        · exact ⟨true, false, 0, by
            simp only [InC3vViewDomain, candView, c3Mat, mirrorQMat, mirrorMat, Fin.sum_univ_three]
            simp
            all_goals (try constructorm* _ ∧ _)
            all_goals linarith⟩
      · rcases le_total 0 (u 1) with hm | hm
        · exact ⟨false, false, 0, by
            simp only [InC3vViewDomain, candView, c3Mat, mirrorQMat, mirrorMat, Fin.sum_univ_three]
            simp
            all_goals (try constructorm* _ ∧ _)
            all_goals linarith⟩
        · exact ⟨false, true, 1, by
            simp only [InC3vViewDomain, candView, c3Mat, mirrorQMat, mirrorMat, Fin.sum_univ_three]
            simp
            all_goals (try constructorm* _ ∧ _)
            all_goals linarith⟩
    · rcases le_total (u 0) (u 2) with h02 | h02
      · rcases le_total 0 (u 2) with hm | hm
        · exact ⟨false, false, 2, by
            simp only [InC3vViewDomain, candView, c3Mat, mirrorQMat, mirrorMat, Fin.sum_univ_three]
            simp
            all_goals (try constructorm* _ ∧ _)
            all_goals linarith⟩
        · exact ⟨false, true, 0, by
            simp only [InC3vViewDomain, candView, c3Mat, mirrorQMat, mirrorMat, Fin.sum_univ_three]
            simp
            all_goals (try constructorm* _ ∧ _)
            all_goals linarith⟩
      · rcases le_total 0 (u 0) with hm | hm
        · exact ⟨true, true, 2, by
            simp only [InC3vViewDomain, candView, c3Mat, mirrorQMat, mirrorMat, Fin.sum_univ_three]
            simp
            all_goals (try constructorm* _ ∧ _)
            all_goals linarith⟩
        · exact ⟨true, false, 1, by
            simp only [InC3vViewDomain, candView, c3Mat, mirrorQMat, mirrorMat, Fin.sum_univ_three]
            simp
            all_goals (try constructorm* _ ∧ _)
            all_goals linarith⟩
  · rcases le_total (u 1) (u 2) with h12 | h12
    · rcases le_total (u 0) (u 2) with h02 | h02
      · rcases le_total 0 (u 0) with hm | hm
        · exact ⟨false, false, 1, by
            simp only [InC3vViewDomain, candView, c3Mat, mirrorQMat, mirrorMat, Fin.sum_univ_three]
            simp
            all_goals (try constructorm* _ ∧ _)
            all_goals linarith⟩
        · exact ⟨false, true, 2, by
            simp only [InC3vViewDomain, candView, c3Mat, mirrorQMat, mirrorMat, Fin.sum_univ_three]
            simp
            all_goals (try constructorm* _ ∧ _)
            all_goals linarith⟩
      · rcases le_total 0 (u 2) with hm | hm
        · exact ⟨true, true, 0, by
            simp only [InC3vViewDomain, candView, c3Mat, mirrorQMat, mirrorMat, Fin.sum_univ_three]
            simp
            all_goals (try constructorm* _ ∧ _)
            all_goals linarith⟩
        · exact ⟨true, false, 2, by
            simp only [InC3vViewDomain, candView, c3Mat, mirrorQMat, mirrorMat, Fin.sum_univ_three]
            simp
            all_goals (try constructorm* _ ∧ _)
            all_goals linarith⟩
    · rcases le_total (u 0) (u 2) with h02 | h02
      · rcases le_total 0 (u 1) with hm | hm
        · exact ⟨false, false, 0, by
            simp only [InC3vViewDomain, candView, c3Mat, mirrorQMat, mirrorMat, Fin.sum_univ_three]
            simp
            all_goals (try constructorm* _ ∧ _)
            all_goals linarith⟩
        · exact ⟨false, true, 1, by
            simp only [InC3vViewDomain, candView, c3Mat, mirrorQMat, mirrorMat, Fin.sum_univ_three]
            simp
            all_goals (try constructorm* _ ∧ _)
            all_goals linarith⟩
      · rcases le_total 0 (u 1) with hm | hm
        · exact ⟨false, false, 0, by
            simp only [InC3vViewDomain, candView, c3Mat, mirrorQMat, mirrorMat, Fin.sum_univ_three]
            simp
            all_goals (try constructorm* _ ∧ _)
            all_goals linarith⟩
        · exact ⟨false, true, 1, by
            simp only [InC3vViewDomain, candView, c3Mat, mirrorQMat, mirrorMat, Fin.sum_univ_three]
            simp
            all_goals (try constructorm* _ ∧ _)
            all_goals linarith⟩

theorem view_viewAntipode (p : MatrixPose) : p.viewAntipode.view = -p.view := by
  funext k
  simp [MatrixPose.view, MatrixPose.viewAntipode, MatrixPose.viewAntipodeRotation,
    Matrix.mul_apply, Rx_mat, Fin.sum_univ_three]

/-- The candidate poses, realizing `candView`. -/
noncomputable def candPose (p : MatrixPose) (s b : Bool) (j : Fin 3) : MatrixPose :=
  let q := if b then p.mirrorScene j else p.bothRightC3 j
  if s then q.viewAntipode else q

theorem view_candPose (p : MatrixPose) (s b : Bool) (j : Fin 3) :
    (candPose p s b j).view = candView p.view s b j := by
  funext l
  cases s <;> cases b <;>
    simp [candPose, candView, view_viewAntipode, view_mirrorScene, view_bothRightC3]

theorem RupertPose_candPose_iff (S : Set ℝ³) (hc : ∀ k, (c3Mat k).toEuclideanLin '' S = S)
    (hm : ∀ i, (fun v => -((mirrorQMat i).toEuclideanLin v)) '' S = S)
    (p : MatrixPose) (s b : Bool) (j : Fin 3) :
    RupertPose (candPose p s b j) S ↔ RupertPose p S := by
  cases s <;> cases b <;>
    simp only [candPose, Bool.false_eq_true, if_false, if_true, MatrixPose.RupertPose_viewAntipode_iff,
      RupertPose_mirrorScene_iff S _ _ (hm j), RupertPose_bothRightC3_iff S _ _ (hc j)]

/-- Every pose of a C3v solid is equivalent to one whose view lies in the
domain. -/
theorem exists_viewDomain_pose (S : Set ℝ³) (hc : ∀ k, (c3Mat k).toEuclideanLin '' S = S)
    (hm : ∀ i, (fun v => -((mirrorQMat i).toEuclideanLin v)) '' S = S) (p : MatrixPose) :
    ∃ p' : MatrixPose, InC3vViewDomain p'.view ∧ (RupertPose p' S ↔ RupertPose p S) := by
  obtain ⟨s, b, j, h⟩ := exists_candView_domain p.view
  exact ⟨candPose p s b j, by rwa [view_candPose], RupertPose_candPose_iff S hc hm p s b j⟩

end Noperthedron.Septopert
