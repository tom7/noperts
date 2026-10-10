module

public import Pipeline.FivefoldModel
public import Pipeline.Tightening
public import Pipeline.FundamentalDomain

@[expose] public section

/-!
# The fivefold symmetry about the Euler z axis

For the fivefold solids (`FivefoldSolid`) the model's symmetry is the
rotation by `2π/5` about z, which is also the axis of both Euler azimuths.
So each azimuth can be reduced modulo `2π/5` without changing the shadows
(`rotM_add_fifth_iterated`), and every pose has a representative with outer
azimuth in `[0, 2π/5)` and inner azimuth within `π/5` of it
(`tighten_theta`): the pose domain the certificate tree must cover is
`InTightPoseRegion`. (For the Septopert the 3-fold axis is (1,1,1), not an
Euler axis, and its reduction is different; see `Septopert.Reduce`.)
-/

namespace Noperts.Pipeline

variable [FivefoldSolid] {P : C5Model}

open Real
open Noperts.BalancedSupport

private lemma RzL_apply_add (α β : ℝ) (v : ℝ³) :
    RzL (α + β) v = RzL α (RzL β v) := by
  have h := RzC.map_add_eq_mul α β
  simp only [RzC_coe] at h
  rw [h]
  rfl

theorem fivefoldMatrix_eq (k : OrbitIndex) :
    fivefoldMatrix k = Rz_mat ((k : ℝ) * (2 * π / 5)) := by
  rw [fivefoldMatrix, symmetryMatrix_eq_fivefoldRotation, fivefoldRotation_eq_mul]

theorem fivefoldMatrix_one : fivefoldMatrix 1 = Rz_mat (2 * π / 5) := by
  rw [fivefoldMatrix_eq, show ((1 : OrbitIndex) : ℕ) = 1 from rfl]
  simp

/-- The rotation by `2π/5` about z preserves the hull. -/
theorem rotate_hull_fifth :
    RzL (2 * π / 5) '' P.polyhedron.hull = P.polyhedron.hull := by
  have h := Pipeline.rotate_hull (P := P) (1 : OrbitIndex)
  rw [symmetryMatrix_eq_fivefoldRotation] at h
  have hmat : fivefoldRotation (1 : OrbitIndex) = Rz_mat (2 * π / 5) := by
    unfold fivefoldRotation
    congr 1
    norm_num
  rw [hmat] at h
  exact h

/-- Every nonnegative power of the generating fivefold rotation preserves
the exact hull. -/
theorem rotate_hull_iterated_nat (n : ℕ) :
    RzL ((n : ℝ) * (2 * π / 5)) '' P.polyhedron.hull =
      P.polyhedron.hull := by
  induction n with
  | zero =>
      have hzero : RzL 0 = ContinuousLinearMap.id ℝ ℝ³ := by
        apply ContinuousLinearMap.ext
        intro v
        ext i
        fin_cases i <;>
          simp [RzL, Rz_mat, Matrix.toLpLin_apply,
            dotProduct, Fin.sum_univ_three]
      rw [Nat.cast_zero, zero_mul, hzero]
      exact Set.image_id _
  | succ n ih =>
      have hangle : ((n + 1 : ℕ) : ℝ) * (2 * π / 5) =
          2 * π / 5 + (n : ℝ) * (2 * π / 5) := by
        push_cast
        ring
      have hmap : RzL (((n + 1 : ℕ) : ℝ) * (2 * π / 5)) =
          RzL (2 * π / 5) ∘L RzL ((n : ℝ) * (2 * π / 5)) := by
        rw [hangle]
        apply ContinuousLinearMap.ext
        intro v
        exact RzL_apply_add _ _ v
      rw [hmap]
      push_cast
      rw [Set.image_comp, ih, rotate_hull_fifth]

/-- A single symmetry step does not change the shadow at fixed inclination. -/
theorem rotM_add_fifth (θ φ : ℝ) :
    rotM (θ + 2 * π / 5) φ '' P.polyhedron.hull =
      rotM θ φ '' P.polyhedron.hull := by
  repeat rw [rotM_identity]
  push_cast
  have hmap : RzL (-(θ + 2 * π / 5)) =
      RzL (-θ) ∘L RzL (-(2 * π / 5)) := by
    ext v
    rw [show -(θ + 2 * π / 5) = -θ + -(2 * π / 5) by ring,
      RzL_apply_add]
    rfl
  have hneg : RzL (-(2 * π / 5)) '' P.polyhedron.hull =
      P.polyhedron.hull := by
    have hinv (v : ℝ³) :
        RzL (-(2 * π / 5)) (RzL (2 * π / 5) v) = v := by
      rw [← RzL_apply_add,
        show -(2 * π / 5) + 2 * π / 5 = 0 by ring]
      ext i
      fin_cases i <;> simp [RzL, Rz_mat, Matrix.vecHead, Matrix.vecTail]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyimg : y ∈ RzL (2 * π / 5) '' P.polyhedron.hull := by
        rw [rotate_hull_fifth]
        exact hy
      obtain ⟨z, hz, rfl⟩ := hyimg
      rw [hinv]
      exact hz
    · intro hx
      refine ⟨RzL (2 * π / 5) x, ?_, hinv x⟩
      have hmem : RzL (2 * π / 5) x ∈
          RzL (2 * π / 5) '' P.polyhedron.hull := ⟨x, hx, rfl⟩
      rwa [rotate_hull_fifth] at hmem
  rw [hmap]
  push_cast
  repeat rw [Set.image_comp]
  rw [hneg]

theorem rotM_add_fifth_iterated {θ φ : ℝ} (n : ℤ) :
    rotM (θ + n * (2 * π / 5)) φ '' P.polyhedron.hull =
      rotM θ φ '' P.polyhedron.hull := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n hn =>
      rw [← hn]
      push_cast
      have h := rotM_add_fifth (P := P) (θ + n * (2 * π / 5)) φ
      ring_nf at h ⊢
      exact h
  | pred n hn =>
      rw [← hn]
      push_cast
      have h := rotM_add_fifth (P := P) (θ + (-1 - n) * (2 * π / 5)) φ
      ring_nf at h ⊢
      exact h.symm

/-- The rational superset of the closest-representative condition.  Its
width is strictly smaller than one fivefold period, so no symmetry seam is
present inside the domain that the certificate tree must cover. -/
def InTightPoseRegion (q : Pose ℝ) : Prop :=
  q ∈ tightPoseInterval ∧ q.θ₁ - q.θ₂ ∈ Set.Icc (-(2 / 3)) (2 / 3)

/-- Reduce the outer azimuth modulo the exact fivefold symmetry, then choose
the inner representative closest to it.  Thus the only coincident-rotation
stratum in the reduced domain is `θ₁ = θ₂` (rather than an additional seam
at opposite ends of a fundamental interval). -/
theorem tighten_theta (p : Pose ℝ) :
    ∃ q : Pose ℝ,
      q.θ₂ ∈ Set.Ico 0 (2 * π / 5) ∧
      q.θ₁ - q.θ₂ ∈ Set.Ico (-(π / 5)) (π / 5) ∧
      q.φ₁ = p.φ₁ ∧ q.φ₂ = p.φ₂ ∧ q.α = p.α ∧
      p.inner '' P.polyhedron.hull = q.inner '' P.polyhedron.hull ∧
      p.outer '' P.polyhedron.hull = q.outer '' P.polyhedron.hull ∧
      ∃ k : ℤ, q.θ₂ = p.θ₂ + k * (2 * π / 5) := by
  have hperiod : 0 < 2 * π / 5 := div_pos two_pi_pos (by norm_num)
  let θ₂ := Real.emod p.θ₂ (2 * π / 5)
  obtain ⟨k₂, hk₂⟩ :=
    Real.emod_exists_multiple p.θ₂ (2 * π / 5) hperiod
  let d := Real.emod (p.θ₁ - p.θ₂ + π / 5) (2 * π / 5) - π / 5
  let θ₁ := θ₂ + d
  obtain ⟨kd, hkd⟩ := Real.emod_exists_multiple
    (p.θ₁ - p.θ₂ + π / 5) (2 * π / 5) hperiod
  have hd : d ∈ Set.Ico (-(π / 5)) (π / 5) := by
    have h := Real.emod_in_interval
      (a := p.θ₁ - p.θ₂ + π / 5) hperiod
    dsimp [d]
    rcases h with ⟨hl, hu⟩
    constructor <;> linarith
  have hθ₁ : θ₁ = p.θ₁ + (k₂ + kd) * (2 * π / 5) := by
    dsimp [θ₁, θ₂, d]
    rw [hk₂, hkd]
    ring
  let q : Pose ℝ := {p with θ₁ := θ₁, θ₂ := θ₂}
  refine ⟨q, Real.emod_in_interval hperiod, ?_, rfl, rfl, rfl, ?_, ?_, k₂, hk₂⟩
  · simpa [q, θ₁] using hd
  · calc
      p.inner '' P.polyhedron.hull =
          (p.rotR ∘ p.rotM₁) '' P.polyhedron.hull := by
            rw [Pose.inner_eq_RM]
      _ = p.rotR '' (p.rotM₁ '' P.polyhedron.hull) := by
            rw [Set.image_comp]
      _ = p.rotR '' (rotM p.θ₁ p.φ₁ '' P.polyhedron.hull) := rfl
      _ = p.rotR '' (rotM (p.θ₁ + (k₂ + kd) * (2 * π / 5)) p.φ₁ ''
          P.polyhedron.hull) := by
            have hs := rotM_add_fifth_iterated (P := P)
              (θ := p.θ₁) (φ := p.φ₁) (k₂ + kd)
            push_cast at hs
            rw [hs]
      _ = p.rotR '' (rotM θ₁ p.φ₁ '' P.polyhedron.hull) := by rw [hθ₁]
      _ = (q.rotR ∘ q.rotM₁) '' P.polyhedron.hull := by
            rw [Set.image_comp]
            rfl
      _ = q.inner '' P.polyhedron.hull := by rw [Pose.inner_eq_RM]
  · calc
      p.outer '' P.polyhedron.hull =
          p.rotM₂ '' P.polyhedron.hull := by rw [Pose.outer_eq_M]
      _ = rotM p.θ₂ p.φ₂ '' P.polyhedron.hull := rfl
      _ = rotM (p.θ₂ + k₂ * (2 * π / 5)) p.φ₂ ''
          P.polyhedron.hull := by rw [rotM_add_fifth_iterated k₂]
      _ = rotM θ₂ p.φ₂ '' P.polyhedron.hull := by rw [← hk₂]
      _ = q.rotM₂ '' P.polyhedron.hull := rfl
      _ = q.outer '' P.polyhedron.hull := by rw [Pose.outer_eq_M]

end Noperts.Pipeline

end
