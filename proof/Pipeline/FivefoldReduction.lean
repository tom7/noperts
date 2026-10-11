module

public import Pipeline.AtlasFundamentalPrune
public import BalancedSupport.UniversalDomain
public import BalancedSupport.ViewAntipode

@[expose] public section

/-!
# Reducing every pose to the fivefold atlas domain

For a fivefold solid (`FivefoldSolid`) whose only symmetry used is C5 about
z, every matrix pose is equivalent, as far as being Rupert goes, to a
translated pose of the atlas:

* both Euler azimuths are reduced modulo `2π/5` (`tighten_theta`) and the
  viewing normal is put in the upper hemisphere, which gives a pose in the
  rational root box `InTightPoseRegion` with outer view in the wedge
  (`exists_upper_tight_translated_pose`);
* the inner rotation is composed with the symmetry rotation that puts the
  relative rotation in the max-trace (Dirichlet) cell of the symmetry
  (`MatrixPose.exists_rightSymmetry_inFundamentalDomain`);
* the relative rotation is written in one of the four bounded Cayley charts
  (`exists_fundamental_atlas_translated_pose`).

This is the reduction of candidate #231's top layer. The icosahedral solids
reduce further, by the whole icosahedral group (`IModel` in `IcoView`), and
the Septopert's C3 axis is not an Euler axis (`Septopert.Reduce`).
-/

namespace Noperts.Pipeline

variable [FivefoldSolid] {P : CyclicModel}

open Real
open scoped Matrix
open Noperts.BalancedSupport
open CayleyAtlas

/-! ### The symmetry-reduced Euler box -/

omit [FivefoldSolid] in
private theorem period_lt_root_upper : 2 * π / 5 < (8 / 5 : ℝ) := by
  nlinarith [Real.pi_lt_four]

/-- Every full matrix pose has an equivalent translated representative in
the symmetry-reduced rational root box. -/
theorem exists_tight_translated_pose (p : MatrixPose) :
    ∃ δ : ℝ, ∃ q : Pose ℝ, ∃ offset : ℝ²,
      InTightPoseRegion q ∧
      InViewWedge q ∧
      (RupertPose (q.matrixPoseWithOffset offset) P.polyhedron.hull ↔
        RupertPose (p.rotateBy δ) P.polyhedron.hull) := by
  obtain ⟨δ, p0, offset, hp0, _hθ0, hφ0, heq⟩ :=
    Noperts.BalancedSupport.exists_universal_translated_pose p
  obtain ⟨q, hθ₂, hdiff, hφ₁, hφ₂, hα, hinner, houter, -⟩ := tighten_theta (P := P) p0
  have hq : q ∈ tightPoseInterval := by
    rw [NonemptyInterval.mem_def, Pose.le_iff, Pose.le_iff]
    rw [NonemptyInterval.mem_def, Pose.le_iff, Pose.le_iff] at hp0
    dsimp [tightPoseInterval, universalPoseInterval] at hp0 ⊢
    rcases hp0 with ⟨hlo, hhi⟩
    exact ⟨
      ⟨by nlinarith [hθ₂.1, hdiff.1, Real.pi_lt_four],
        hθ₂.1, hφ₁.symm ▸ hlo.2.2.1,
        hφ₂.symm ▸ hlo.2.2.2.1, hα.symm ▸ hlo.2.2.2.2⟩,
      ⟨by nlinarith [hθ₂.2, hdiff.2, Real.pi_lt_four],
        hθ₂.2.le.trans period_lt_root_upper.le,
        hφ₁.symm ▸ hhi.2.2.1, hφ₂.symm ▸ hhi.2.2.2.1,
        hα.symm ▸ hhi.2.2.2.2⟩⟩
  have hrelative : q.θ₁ - q.θ₂ ∈ Set.Icc (-(2 / 3)) (2 / 3) := by
    constructor <;> nlinarith [hdiff.1, hdiff.2, Real.pi_lt_d20]
  have hview : InViewWedge q := by
    constructor
    · exact ⟨hθ₂.1, hθ₂.2.le⟩
    · rw [hφ₂]
      exact hφ0
  refine ⟨δ, q, offset, ⟨hq, hrelative⟩, hview, ?_⟩
  rw [← heq]
  exact (translated_rupert_iff_of_images offset hinner houter).symm

/-- The oriented viewing normal may be chosen in the upper hemisphere.  The
extra choice is shape-independent: reversing the normal reflects both planar
shadows and hence preserves Rupert containment. -/
theorem exists_upper_tight_translated_pose (p : MatrixPose) :
    ∃ q : Pose ℝ, ∃ offset : ℝ²,
      InTightPoseRegion q ∧
      InViewWedge q ∧ q.φ₂ ≤ Real.pi / 2 ∧
      (RupertPose (q.matrixPoseWithOffset offset) P.polyhedron.hull ↔
        RupertPose p P.polyhedron.hull) := by
  let p' := p.upperViewRepresentative
  have hp' : 0 ≤ p'.outerRot.val 2 2 :=
    MatrixPose.upperViewRepresentative_outer_22_nonneg p
  obtain ⟨δ, p0, offset, hp0, _hθ0, hφ0, heq⟩ :=
    Noperts.BalancedSupport.exists_universal_translated_pose p'
  have hcos : 0 ≤ Real.cos p0.φ₂ := by
    have hout22 := congrArg
      (fun pose : MatrixPose ↦ pose.outerRot.val 2 2) heq
    simp only [Pose.matrixPoseWithOffset, Pose.matrixPoseOfPose,
      MatrixPose.rotateBy] at hout22
    simp [rotRM_mat, Matrix.mul_apply, Rz_mat, Ry_mat,
      Fin.sum_univ_three] at hout22
    linarith
  have hφ0Upper : p0.φ₂ ≤ Real.pi / 2 := by
    by_contra h
    have hneg := Real.cos_neg_of_pi_div_two_lt_of_lt
      (lt_of_not_ge h) (hφ0.2.trans_lt (by linarith [Real.pi_pos]))
    linarith
  obtain ⟨q, hθ₂, hdiff, hφ₁, hφ₂, hα, hinner, houter, -⟩ := tighten_theta (P := P) p0
  have hq : q ∈ tightPoseInterval := by
    rw [NonemptyInterval.mem_def, Pose.le_iff, Pose.le_iff]
    rw [NonemptyInterval.mem_def, Pose.le_iff, Pose.le_iff] at hp0
    dsimp [tightPoseInterval, universalPoseInterval] at hp0 ⊢
    rcases hp0 with ⟨hlo, hhi⟩
    exact ⟨
      ⟨by nlinarith [hθ₂.1, hdiff.1, Real.pi_lt_four],
        hθ₂.1, hφ₁.symm ▸ hlo.2.2.1,
        hφ₂.symm ▸ hlo.2.2.2.1, hα.symm ▸ hlo.2.2.2.2⟩,
      ⟨by nlinarith [hθ₂.2, hdiff.2, Real.pi_lt_four],
        hθ₂.2.le.trans period_lt_root_upper.le,
        hφ₁.symm ▸ hhi.2.2.1, hφ₂.symm ▸ hhi.2.2.2.1,
        hα.symm ▸ hhi.2.2.2.2⟩⟩
  have hrelative : q.θ₁ - q.θ₂ ∈ Set.Icc (-(2 / 3)) (2 / 3) := by
    constructor <;> nlinarith [hdiff.1, hdiff.2, Real.pi_lt_d20]
  have hview : InViewWedge q := by
    constructor
    · exact ⟨hθ₂.1, hθ₂.2.le⟩
    · rw [hφ₂]
      exact hφ0
  have hrupert :
      RupertPose (q.matrixPoseWithOffset offset) P.polyhedron.hull ↔
        RupertPose p P.polyhedron.hull := by
    calc
      _ ↔ RupertPose (p0.matrixPoseWithOffset offset)
          P.polyhedron.hull :=
        (translated_rupert_iff_of_images offset hinner houter).symm
      _ ↔ RupertPose (p'.rotateBy δ) P.polyhedron.hull := by rw [heq]
      _ ↔ RupertPose p' P.polyhedron.hull :=
        MatrixPose.RupertPose_rotateBy_iff p' δ _
      _ ↔ RupertPose p P.polyhedron.hull :=
        MatrixPose.RupertPose_upperViewRepresentative_iff p _
  refine ⟨q, offset, ⟨hq, hrelative⟩, hview, ?_, hrupert⟩
  simpa [hφ₂] using hφ0Upper

/-! ### The max-trace cell of the symmetry -/

/-- The `k`th symmetry rotation as an element of `SO(3)`. -/
noncomputable def symmetrySO3 (k : OrbitIndex) : SO3 :=
  ⟨symmetryMatrix k, symmetryMatrix_mem k⟩

/-- Compose only the inner rotation by an exact symmetry. -/
noncomputable def MatrixPose.rightSymmetry
    (p : MatrixPose) (k : OrbitIndex) : MatrixPose where
  innerRot := p.innerRot * symmetrySO3 k
  outerRot := p.outerRot
  innerOffset := p.innerOffset

theorem innerShadow_rightSymmetry
    (p : MatrixPose) (k : OrbitIndex) :
    innerShadow (MatrixPose.rightSymmetry p k) P.polyhedron.hull =
      innerShadow p P.polyhedron.hull := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hgv : (symmetryMatrix k).toEuclideanLin v ∈
        P.polyhedron.hull := by
      rw [← rotate_hull k]
      exact ⟨v, hv, rfl⟩
    refine ⟨(symmetryMatrix k).toEuclideanLin v, hgv, ?_⟩
    simp [MatrixPose.inner_apply, MatrixPose.rightSymmetry,
      symmetrySO3, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  · rintro ⟨v, hv, rfl⟩
    have hv' : v ∈ (symmetryMatrix k).toEuclideanLin ''
        P.polyhedron.hull := by
      rwa [rotate_hull k]
    obtain ⟨u, hu, rfl⟩ := hv'
    refine ⟨u, hu, ?_⟩
    simp [MatrixPose.inner_apply, MatrixPose.rightSymmetry,
      symmetrySO3, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

@[simp] theorem outerShadow_rightSymmetry
    (p : MatrixPose) (k : OrbitIndex) :
    outerShadow (MatrixPose.rightSymmetry p k) P.polyhedron.hull =
      outerShadow p P.polyhedron.hull := by
  rfl

theorem RupertPose_rightSymmetry_iff
    (p : MatrixPose) (k : OrbitIndex) :
    RupertPose (MatrixPose.rightSymmetry p k) P.polyhedron.hull ↔
      RupertPose p P.polyhedron.hull := by
  simp only [RupertPose, innerShadow_rightSymmetry,
    outerShadow_rightSymmetry]

theorem exists_mul_symmetry_inFundamentalDomain
    (R : Matrix (Fin 3) (Fin 3) ℝ) :
    ∃ k : OrbitIndex,
      InSymmetryFundamentalDomain (R * symmetryMatrix k) := by
  obtain ⟨k, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun j : OrbitIndex => Matrix.trace (R * symmetryMatrix j))
    Finset.univ_nonempty
  refine ⟨k, fun j => ?_⟩
  rw [Matrix.mul_assoc, symmetryMatrix_mul_composeSymmetry]
  exact hmax (composeSymmetry k j) (Finset.mem_univ _)

@[simp] theorem MatrixPose.relativeRotation_rightSymmetry
    (p : MatrixPose) (k : OrbitIndex) :
    (MatrixPose.rightSymmetry p k).relativeRotation =
      p.relativeRotation * symmetryMatrix k := by
  simp [MatrixPose.relativeRotation,
    MatrixPose.rightSymmetry, symmetrySO3, Matrix.mul_assoc]

theorem MatrixPose.exists_rightSymmetry_inFundamentalDomain
    (p : MatrixPose) :
    ∃ k : OrbitIndex,
      InSymmetryFundamentalDomain (MatrixPose.rightSymmetry p k).relativeRotation := by
  obtain ⟨k, hk⟩ := exists_mul_symmetry_inFundamentalDomain p.relativeRotation
  exact ⟨k, by simpa using hk⟩

/-! ### Into the atlas -/

@[simp] theorem AtlasPose.matrixPoseWithOffset_inFundamentalDomain_iff
    (p : AtlasPose ℝ) (chart : ChartIndex) (offset : ℝ²) :
    InSymmetryFundamentalDomain (p.matrixPoseWithOffset chart offset).relativeRotation ↔
      p.InFivefoldFundamentalDomain chart := by
  rw [AtlasPose.InFivefoldFundamentalDomain,
    AtlasPose.matrixPoseWithOffset_relativeRotation]

theorem matrixPoseWithOffset_ofPose_eq_rightSymmetry
    (euler : Pose ℝ) (offset : ℝ²) (k : OrbitIndex)
    (chart : ChartIndex) (x y z : ℝ)
    (hrelative :
      (euler.matrixPoseWithOffset offset).relativeRotation *
          symmetryMatrix k =
        chartMatrix chart * cayleyMatrix x y z) :
    (AtlasPose.ofPose euler x y z).matrixPoseWithOffset chart offset =
      MatrixPose.rightSymmetry (euler.matrixPoseWithOffset offset) k := by
  let oldPose := euler.matrixPoseWithOffset offset
  let reduced := MatrixPose.rightSymmetry oldPose k
  have hrelative' : reduced.relativeRotation =
      chartMatrix chart * cayleyMatrix x y z := by
    rw [MatrixPose.relativeRotation_rightSymmetry]
    exact hrelative
  apply matrixPose_ext_val
  · calc
      ((AtlasPose.ofPose euler x y z).matrixPoseWithOffset chart offset).innerRot.val =
          oldPose.outerRot.val *
            (chartMatrix chart * cayleyMatrix x y z) := by
              change (rotRM_mat euler.θ₂ euler.φ₂ 0 *
                  chartMatrix chart) * cayleyMatrix x y z =
                rotRM_mat euler.θ₂ euler.φ₂ 0 *
                  (chartMatrix chart * cayleyMatrix x y z)
              rw [Matrix.mul_assoc]
      _ = reduced.outerRot.val * reduced.relativeRotation := by
            rw [hrelative']
            rfl
      _ = reduced.innerRot.val :=
            Atlas.MatrixPose.outer_mul_relativeRotation
              reduced
  · rfl
  · rfl

/-- Every matrix pose is equivalent (for being Rupert) to a translated
atlas pose in the root box, Cayley-bounded, in the fundamental domain of the
symmetry, with outer view in the upper wedge. -/
theorem exists_fundamental_atlas_translated_pose (p : MatrixPose) :
    ∃ chart : ChartIndex, ∃ q : AtlasPose ℝ, ∃ offset : ℝ²,
      q ∈ AtlasPose.rootInterval ℝ ∧ q.CayleyBounded ∧ q.InViewWedge ∧
      q.InUpperView ∧ q.InFivefoldFundamentalDomain chart ∧
      (RupertPose (q.matrixPoseWithOffset chart offset)
          P.polyhedron.hull ↔
        RupertPose p P.polyhedron.hull) := by
  obtain ⟨euler, offset, heuler, hview, hupper, heq⟩ :=
    exists_upper_tight_translated_pose (P := P) p
  let oldPose := euler.matrixPoseWithOffset offset
  obtain ⟨k, hkfund⟩ :=
    MatrixPose.exists_rightSymmetry_inFundamentalDomain oldPose
  let reduced := MatrixPose.rightSymmetry oldPose k
  obtain ⟨chart, x, hx, y, hy, z, hz, hradius, hrelative⟩ :=
    exists_bounded_chart_cayley reduced.relativeRotation
      (Atlas.MatrixPose.relativeRotation_mem_SO3 reduced)
  let q := AtlasPose.ofPose euler x y z
  have hq : q ∈ AtlasPose.rootInterval ℝ :=
    AtlasPose.ofPose_mem_root euler x y z heuler.1 hx hy hz
  have hmatrix : q.matrixPoseWithOffset chart offset = reduced := by
    apply matrixPoseWithOffset_ofPose_eq_rightSymmetry
    rw [← MatrixPose.relativeRotation_rightSymmetry]
    exact hrelative
  have hqfund : q.InFivefoldFundamentalDomain chart := by
    rw [← AtlasPose.matrixPoseWithOffset_inFundamentalDomain_iff
      q chart offset, hmatrix]
    exact hkfund
  refine ⟨chart, q, offset, hq, hradius, ?_, ?_, hqfund, ?_⟩
  · simpa [q, AtlasPose.InViewWedge, AtlasPose.ofPose, InViewWedge]
      using hview
  · simpa [q, AtlasPose.InUpperView, AtlasPose.ofPose] using hupper
  · rw [hmatrix, RupertPose_rightSymmetry_iff]
    exact heq

end Noperts.Pipeline

end
