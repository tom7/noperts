module

public import Pipeline.OctaModel
public import Pipeline.HalfTurnBasic
public import Pipeline.AtlasProjectiveView
public import Pipeline.AtlasEdgeCertificate
public import Atlas.Tightening

@[expose] public section

/-!
# The octahedral reduction of poses

Every pose of an octahedral model (`OModel`) is equivalent to a bounded atlas
representative whose view lies in the Oh chamber and whose relative rotation
lies in the max-trace cell of O (`OModel.exists_octa_full_atlas_translated_pose`).

* **The view**, modulo Oh = O × {±1}, into the chamber `0 ≤ u₁ ≤ u₀ ≤ u₂`
  (1/48 of the sphere). Composing both rotations on the right with g ∈ O, or
  reflecting the view (`viewAntipode`), preserves Rupert-ness and changes the
  view v to `±G_gᵀ v`. With c = (3, 1, 6) inside the chamber, choose the sign
  and g maximizing ⟨±G_gᵀ v, c⟩ (`exists_octa_view_dirichlet`). The chamber's
  walls are the mirrors −H of three half-turns H ∈ O (about the y axis, about
  (1, −1, 0) and about (1, 0, −1)); comparing with the reflected candidates
  gives ⟨w, c + H c⟩ ≥ 0, i.e. `2 u₁`, `2 (u₀ − u₁)` and `3 (u₂ − u₀)`
  are nonnegative: no Farkas step is needed, everything is integer.
* **The outer angles**: a screen rotation puts the outer rotation into the form
  `rotRM_mat θ φ 0` with θ ∈ [0, π/4] (`exists_octa_euler_outer`; the C3v
  argument of the Septopert, which uses only the walls u₁ ≤ u₀ and 0 ≤ u₁).
* **The relative rotation**, modulo O on the right, into the cell where no
  rotation of O increases the trace (`InOctaCell`), and then into a bounded
  Cayley chart.
-/

namespace Noperts.Pipeline

open scoped Matrix
open CayleyAtlas Real

/-! ### The chamber -/

/-- The Oh chamber `0 ≤ u₁ ≤ u₀ ≤ u₂`. -/
def InOctaViewCone (w : Fin 3 → ℝ) : Prop := 0 ≤ w 1 ∧ w 1 ≤ w 0 ∧ w 0 ≤ w 2

/-- The three wall half-turns of O (as signed permutation matrices). -/
def octaWallEntries : Fin 3 → List Int := ![
  [-1, 0, 0, 0, 1, 0, 0, 0, -1],
  [0, -1, 0, -1, 0, 0, 0, 0, -1],
  [0, 0, -1, 0, -1, 0, -1, 0, 0]]

def octaWallIdx (i : Fin 3) : Nat :=
  ((List.range 24).find? fun c => octaEntries.getD c [] == octaWallEntries i).getD 0

/-- The wall half-turns are in the list, and are symmetric. -/
def octaWallCheck : Bool :=
  (List.finRange 3).all fun i =>
    decide (octaWallIdx i < 24) && octaEntries.getD (octaWallIdx i) [] == octaWallEntries i

theorem octaWallCheck_eq : octaWallCheck = true := by decide +kernel

def octaWall (i : Fin 3) : OctaIndex :=
  ⟨octaWallIdx i, by
    have h := octaWallCheck_eq
    simp only [octaWallCheck, List.all_eq_true, List.mem_finRange, forall_true_left,
      Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact (h i).1⟩

theorem octaWall_entries (i : Fin 3) : octaEntries.getD (octaWall i).val [] = octaWallEntries i := by
  have h := octaWallCheck_eq
  simp only [octaWallCheck, List.all_eq_true, List.mem_finRange, forall_true_left,
    Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact (h i).2

/-- The wall half-turns as explicit matrices. -/
def octaWallMatrix : Fin 3 → Matrix (Fin 3) (Fin 3) ℝ := ![
  !![-1, 0, 0; 0, 1, 0; 0, 0, -1],
  !![0, -1, 0; -1, 0, 0; 0, 0, -1],
  !![0, 0, -1; 0, -1, 0; -1, 0, 0]]

theorem octaMatrix_octaWall (i : Fin 3) : octaMatrix (octaWall i) = octaWallMatrix i := by
  ext r c
  simp only [octaMatrix, Matrix.of_apply, octaEntry]
  rw [octaWall_entries]
  fin_cases i <;> fin_cases r <;> fin_cases c <;> simp [octaWallEntries, octaWallMatrix]

theorem octaWall_symm (i : Fin 3) : (octaMatrix (octaWall i))ᵀ = octaMatrix (octaWall i) := by
  rw [octaMatrix_octaWall]
  ext r c
  fin_cases i <;> fin_cases r <;> fin_cases c <;> simp [octaWallMatrix]

/-- The interior point c = (3, 1, 6) of the chamber. -/
def octaViewCenter : Fin 3 → ℝ := ![3, 1, 6]

/-- `⟨w, c + H_i c⟩` for the wall half-turns: `2 w₁`, `2 (w₀ − w₁)`, `3 (w₂ − w₀)`. -/
theorem wall_dot (i : Fin 3) (w : Fin 3 → ℝ) :
    w ⬝ᵥ (octaViewCenter + octaMatrix (octaWall i) *ᵥ octaViewCenter) =
      ![2 * w 1, 2 * (w 0 - w 1), 3 * (w 2 - w 0)] i := by
  rw [octaMatrix_octaWall]
  fin_cases i <;>
    simp [octaWallMatrix, octaViewCenter, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

/-! ### The Dirichlet choice over Oh -/

/-- The candidate views `s · G_gᵀ v`. -/
noncomputable def octaViewCandidate (v : Fin 3 → ℝ) (s : Bool) (g : OctaIndex) : Fin 3 → ℝ :=
  (if s then (1 : ℝ) else -1) • ((octaMatrix g)ᵀ *ᵥ v)

theorem exists_octa_view_dirichlet (v : Fin 3 → ℝ) :
    ∃ s : Bool, ∃ g : OctaIndex, InOctaViewCone (octaViewCandidate v s g) := by
  obtain ⟨⟨s, g⟩, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun sg : Bool × OctaIndex => octaViewCandidate v sg.1 sg.2 ⬝ᵥ octaViewCenter)
    Finset.univ_nonempty
  refine ⟨s, g, ?_⟩
  -- For each wall: ⟨w, c + H_i c⟩ ≥ 0.
  have hwall : ∀ i : Fin 3, 0 ≤ octaViewCandidate v s g ⬝ᵥ
      (octaViewCenter + octaMatrix (octaWall i) *ᵥ octaViewCenter) := by
    intro i
    obtain ⟨k, hk⟩ := exists_octaMatrix_mul g (octaWall i)
    have hle := hmax (!s, k) (Finset.mem_univ _)
    have hkT : (octaMatrix k)ᵀ = octaMatrix (octaWall i) * (octaMatrix g)ᵀ := by
      rw [← hk, Matrix.transpose_mul, octaWall_symm]
    set H := octaMatrix (octaWall i)
    set x := (octaMatrix g)ᵀ *ᵥ v
    have hsymdot : (H *ᵥ x) ⬝ᵥ octaViewCenter = x ⬝ᵥ (H *ᵥ octaViewCenter) := by
      have hs : Hᵀ = H := octaWall_symm i
      conv_rhs => rw [← hs]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.transpose_apply]
      ring
    have hcand : octaViewCandidate v (!s) k = (if (!s) then (1 : ℝ) else -1) • (H *ᵥ x) := by
      simp only [octaViewCandidate, hkT, ← Matrix.mulVec_mulVec, H, x]
    have hle' : octaViewCandidate v (!s) k ⬝ᵥ octaViewCenter ≤
        octaViewCandidate v s g ⬝ᵥ octaViewCenter := hle
    rw [hcand, smul_dotProduct, hsymdot] at hle'
    simp only [octaViewCandidate, smul_dotProduct, dotProduct_add] at hle' ⊢
    cases s <;> simp at hle' ⊢ <;> linarith
  have h0 := wall_dot 0 (octaViewCandidate v s g)
  have h1 := wall_dot 1 (octaViewCandidate v s g)
  have h2 := wall_dot 2 (octaViewCandidate v s g)
  have hw0 := hwall 0
  have hw1 := hwall 1
  have hw2 := hwall 2
  rw [h0] at hw0
  rw [h1] at hw1
  rw [h2] at hw2
  simp at hw0 hw1 hw2
  exact ⟨by linarith, by linarith, by linarith⟩

/-! ### Realizing the reduced view by a pose -/

noncomputable def octaSO3 (g : OctaIndex) : SO3 := ⟨octaMatrix g, octaMatrix_mem_SO3 g⟩

/-- Compose both rotations on the right with a rotation of O. -/
noncomputable def MatrixPose.bothRightOcta (p : MatrixPose) (g : OctaIndex) : MatrixPose where
  innerRot := p.innerRot * octaSO3 g
  outerRot := p.outerRot * octaSO3 g
  innerOffset := p.innerOffset

theorem view_bothRightOcta (p : MatrixPose) (g : OctaIndex) :
    (MatrixPose.bothRightOcta p g).view = octaViewCandidate p.view true g := by
  funext k
  simp [MatrixPose.view, MatrixPose.bothRightOcta, octaSO3, octaViewCandidate, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.transpose_apply]
  ring

theorem view_octaViewAntipode (p : MatrixPose) : p.viewAntipode.view = -p.view := by
  funext k
  simp [MatrixPose.view, MatrixPose.viewAntipode, MatrixPose.viewAntipodeRotation,
    Matrix.mul_apply, Rx_mat, Fin.sum_univ_three]

/-- Compose only the inner rotation with a rotation of O. -/
noncomputable def MatrixPose.rightOctaSymmetry (p : MatrixPose) (g : OctaIndex) : MatrixPose where
  innerRot := p.innerRot * octaSO3 g
  outerRot := p.outerRot
  innerOffset := p.innerOffset

@[simp] theorem MatrixPose.relativeRotation_rightOctaSymmetry (p : MatrixPose) (g : OctaIndex) :
    (MatrixPose.rightOctaSymmetry p g).relativeRotation = p.relativeRotation * octaMatrix g := by
  simp [MatrixPose.relativeRotation, MatrixPose.rightOctaSymmetry, octaSO3, Matrix.mul_assoc]

/-! ### The cell -/

/-- No right rotation of O increases the trace. -/
def InOctaCell (R : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ g : OctaIndex, Matrix.trace (R * octaMatrix g) ≤ Matrix.trace R

theorem exists_mul_octa_inCell (R : Matrix (Fin 3) (Fin 3) ℝ) :
    ∃ h : OctaIndex, InOctaCell (R * octaMatrix h) := by
  obtain ⟨h, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun g : OctaIndex => Matrix.trace (R * octaMatrix g)) Finset.univ_nonempty
  refine ⟨h, fun g => ?_⟩
  obtain ⟨k, hk⟩ := exists_octaMatrix_mul h g
  rw [Matrix.mul_assoc, hk]
  exact hmax k (Finset.mem_univ _)

/-- The cell condition carried by an atlas representative. -/
def AtlasPose.InOctaFundamentalDomain (p : AtlasPose ℝ) (chart : ChartIndex) : Prop :=
  InOctaCell (chartMatrix chart * cayleyMatrix p.x p.y p.z)

open AtlasEdgeCertificate in
/-- The view of an atlas pose lies in the Oh chamber. -/
def AtlasPose.InOctaView (p : AtlasPose ℝ) : Prop := InOctaViewCone fun c => viewVector p c

/-! ### Rupert-ness is invariant -/

namespace OModel

variable [OctahedralSolid] (P : OModel)

theorem innerShadow_rightOcta (p : MatrixPose) (g : OctaIndex) (inner : SO3 → SO3)
    (hinner : inner p.innerRot = p.innerRot * octaSO3 g) :
    {w | ∃ v ∈ P.toC4.polyhedron.hull, w = proj_xyL ((inner p.innerRot).val.toEuclideanLin v) +
        p.innerOffset} =
      {w | ∃ v ∈ P.toC4.polyhedron.hull, w = proj_xyL (p.innerRot.val.toEuclideanLin v) +
        p.innerOffset} := by
  rw [hinner]
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hgv : (octaMatrix g).toEuclideanLin v ∈ P.toC4.polyhedron.hull := by
      rw [← P.octaMatrix_image_hull g]
      exact ⟨v, hv, rfl⟩
    refine ⟨(octaMatrix g).toEuclideanLin v, hgv, ?_⟩
    simp [octaSO3, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  · rintro ⟨v, hv, rfl⟩
    have hv' : v ∈ (octaMatrix g).toEuclideanLin '' P.toC4.polyhedron.hull := by
      rwa [P.octaMatrix_image_hull g]
    obtain ⟨u, hu, rfl⟩ := hv'
    refine ⟨u, hu, ?_⟩
    simp [octaSO3, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

theorem innerShadow_bothRightOcta (p : MatrixPose) (g : OctaIndex) :
    innerShadow (MatrixPose.bothRightOcta p g) P.toC4.polyhedron.hull =
      innerShadow p P.toC4.polyhedron.hull := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hgv : (octaMatrix g).toEuclideanLin v ∈ P.toC4.polyhedron.hull := by
      rw [← P.octaMatrix_image_hull g]
      exact ⟨v, hv, rfl⟩
    refine ⟨(octaMatrix g).toEuclideanLin v, hgv, ?_⟩
    simp [MatrixPose.inner_apply, MatrixPose.bothRightOcta, octaSO3,
      Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  · rintro ⟨v, hv, rfl⟩
    have hv' : v ∈ (octaMatrix g).toEuclideanLin '' P.toC4.polyhedron.hull := by
      rwa [P.octaMatrix_image_hull g]
    obtain ⟨u, hu, rfl⟩ := hv'
    refine ⟨u, hu, ?_⟩
    simp [MatrixPose.inner_apply, MatrixPose.bothRightOcta, octaSO3,
      Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

theorem outerShadow_bothRightOcta (p : MatrixPose) (g : OctaIndex) :
    outerShadow (MatrixPose.bothRightOcta p g) P.toC4.polyhedron.hull =
      outerShadow p P.toC4.polyhedron.hull := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hgv : (octaMatrix g).toEuclideanLin v ∈ P.toC4.polyhedron.hull := by
      rw [← P.octaMatrix_image_hull g]
      exact ⟨v, hv, rfl⟩
    refine ⟨(octaMatrix g).toEuclideanLin v, hgv, ?_⟩
    simp [MatrixPose.bothRightOcta, octaSO3, PoseLike.outer, Matrix.toLpLin_apply,
      Matrix.mulVec_mulVec]
  · rintro ⟨v, hv, rfl⟩
    have hv' : v ∈ (octaMatrix g).toEuclideanLin '' P.toC4.polyhedron.hull := by
      rwa [P.octaMatrix_image_hull g]
    obtain ⟨u, hu, rfl⟩ := hv'
    refine ⟨u, hu, ?_⟩
    simp [MatrixPose.bothRightOcta, octaSO3, PoseLike.outer, Matrix.toLpLin_apply,
      Matrix.mulVec_mulVec]

theorem RupertPose_bothRightOcta_iff (p : MatrixPose) (g : OctaIndex) :
    RupertPose (MatrixPose.bothRightOcta p g) P.toC4.polyhedron.hull ↔
      RupertPose p P.toC4.polyhedron.hull := by
  simp only [RupertPose, P.innerShadow_bothRightOcta, P.outerShadow_bothRightOcta]

theorem innerShadow_rightOctaSymmetry (p : MatrixPose) (g : OctaIndex) :
    innerShadow (MatrixPose.rightOctaSymmetry p g) P.toC4.polyhedron.hull =
      innerShadow p P.toC4.polyhedron.hull := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hgv : (octaMatrix g).toEuclideanLin v ∈ P.toC4.polyhedron.hull := by
      rw [← P.octaMatrix_image_hull g]
      exact ⟨v, hv, rfl⟩
    refine ⟨(octaMatrix g).toEuclideanLin v, hgv, ?_⟩
    simp [MatrixPose.inner_apply, MatrixPose.rightOctaSymmetry, octaSO3,
      Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  · rintro ⟨v, hv, rfl⟩
    have hv' : v ∈ (octaMatrix g).toEuclideanLin '' P.toC4.polyhedron.hull := by
      rwa [P.octaMatrix_image_hull g]
    obtain ⟨u, hu, rfl⟩ := hv'
    refine ⟨u, hu, ?_⟩
    simp [MatrixPose.inner_apply, MatrixPose.rightOctaSymmetry, octaSO3,
      Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

theorem RupertPose_rightOctaSymmetry_iff (p : MatrixPose) (g : OctaIndex) :
    RupertPose (MatrixPose.rightOctaSymmetry p g) P.toC4.polyhedron.hull ↔
      RupertPose p P.toC4.polyhedron.hull := by
  have houter : outerShadow (MatrixPose.rightOctaSymmetry p g) P.toC4.polyhedron.hull =
      outerShadow p P.toC4.polyhedron.hull := rfl
  simp only [RupertPose, P.innerShadow_rightOctaSymmetry, houter]

/-- Every pose is equivalent to one whose view lies in the Oh chamber. -/
theorem exists_octaViewCone_pose (p : MatrixPose) :
    ∃ p' : MatrixPose, InOctaViewCone p'.view ∧
      (RupertPose p' P.toC4.polyhedron.hull ↔ RupertPose p P.toC4.polyhedron.hull) := by
  obtain ⟨s, g, hcone⟩ := exists_octa_view_dirichlet p.view
  cases s
  · refine ⟨(MatrixPose.bothRightOcta p g).viewAntipode, ?_, ?_⟩
    · rw [view_octaViewAntipode, view_bothRightOcta]
      convert hcone using 1
      funext k
      simp [octaViewCandidate]
    · rw [MatrixPose.RupertPose_viewAntipode_iff, P.RupertPose_bothRightOcta_iff]
  · exact ⟨MatrixPose.bothRightOcta p g, by rwa [view_bothRightOcta],
      P.RupertPose_bothRightOcta_iff p g⟩

end OModel

/-! ### The chamber as a view triangle -/

open AtlasProjectiveView AtlasEdgeCertificate Noperts.Atlas.ProjectiveView in
/-- The Oh chamber as a rational triangle in the root-0 face:
(0, 0, 1), (1/2, 0, 1/2), (1/3, 1/3, 1/3). -/
def octaViewTriangle : AtlasProjectiveView.Triangle ℚ :=
  ![![0, 0, 1], ![1 / 2, 0, 1 / 2], ![1 / 3, 1 / 3, 1 / 3]]

open AtlasProjectiveView AtlasEdgeCertificate Noperts.Atlas.ProjectiveView in
theorem octaView_mem_triangle (p : AtlasPose ℝ) (h : p.InOctaView) :
    1 ≤ viewScale 0 p ∧ InTriangle (toReal octaViewTriangle) (normalizedView 0 p) := by
  obtain ⟨h1, h10, h02⟩ := h
  have hsign : ∀ c, 0 ≤ (rootSign 0 c : ℝ) * viewVector p c := by
    intro c
    fin_cases c <;> simp [rootSign] <;> linarith
  have hscale := one_le_viewScale_of_sign hsign
  have hscale0 : 0 < viewScale 0 p := lt_of_lt_of_le (by norm_num) hscale
  refine ⟨hscale, ?_⟩
  have hscaleEq : viewScale 0 p = viewVector p 0 + viewVector p 1 + viewVector p 2 := by
    simp [viewScale, rootSign, Fin.sum_univ_three]
  set x := viewVector p 0
  set y := viewVector p 1
  set z := viewVector p 2
  -- Barycentric weights (α, β, γ) = (z - x, 2 (x - y), 3 y) / (x + y + z).
  let weight : Fin 3 → ℝ := ![(z - x) / viewScale 0 p, 2 * (x - y) / viewScale 0 p,
    3 * y / viewScale 0 p]
  refine ⟨weight, ?_, ?_, ?_⟩
  · intro k
    fin_cases k <;> simp [weight] <;> apply div_nonneg <;> linarith
  · have hne : x + y + z ≠ 0 := hscaleEq ▸ hscale0.ne'
    simp only [weight, Fin.sum_univ_three]
    simp
    rw [hscaleEq]
    field_simp
    ring
  · funext c
    have hne : x + y + z ≠ 0 := hscaleEq ▸ hscale0.ne'
    fin_cases c <;>
      simp [normalizedView, affinePoint, octaViewTriangle,
        Noperts.Atlas.ProjectiveView.toReal, weight, Fin.sum_univ_three, hscaleEq] <;>
      field_simp <;> ring

/-! ### The outer angles -/

theorem octa_Rz_mul_rotRM_mat (δ θ φ α : ℝ) :
    Rz_mat δ * rotRM_mat θ φ α = rotRM_mat θ φ (δ + α) := by
  simp only [rotRM_mat, ← Matrix.mul_assoc, Bounding.Rz_mat_mul_Rz_mat]
  congr 3
  ring

theorem octa_Rz_mul_row2 (δ : ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (k : Fin 3) :
    (Rz_mat δ * M) 2 k = M 2 k := by
  simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem octa_view_rotateBy (p : MatrixPose) (δ : ℝ) : (p.rotateBy δ).view = p.view := by
  funext k
  exact octa_Rz_mul_row2 δ p.outerRot.val k

theorem octa_rotRM_mat_row2_zero (θ φ : ℝ) :
    rotRM_mat θ φ 0 2 0 = cos θ * sin φ ∧ rotRM_mat θ φ 0 2 1 = sin θ * sin φ ∧
      rotRM_mat θ φ 0 2 2 = cos φ := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [rotRM_mat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/-- At a pole (sin φ = 0) the azimuth θ is a screen rotation. -/
theorem octa_Rz_mul_rotRM_mat_pole {θ φ : ℝ} (h : sin φ = 0) :
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

/-- Off the poles, a view with 0 ≤ u₁ ≤ u₀ has azimuth in [0, π/4]. -/
theorem octa_theta_mem {θ φ : ℝ} (hθ : θ ∈ Set.Ioc (-π) π) (hsin : 0 < sin φ)
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
chamber into the form `rotRM_mat θ φ 0` with θ ∈ [0, π/4], φ ∈ [0, π]. -/
theorem exists_octa_euler_outer (p : MatrixPose) (hdom : InOctaViewCone p.view) :
    ∃ δ θ φ : ℝ, θ ∈ Set.Icc 0 (π / 4) ∧ φ ∈ Set.Icc 0 π ∧
      (p.rotateBy δ).outerRot.val = rotRM_mat θ φ 0 := by
  obtain ⟨θo, φo, αo, hθo, hφo, -, hM⟩ :=
    Noperts.Atlas.SO3_to_bounded_rotRM_params p.outerRot.val p.outerRot.property
  have hout : Rz_mat (-αo) * p.outerRot.val = rotRM_mat θo φo 0 := by
    rw [hM, octa_Rz_mul_rotRM_mat, neg_add_cancel]
  have hview : ∀ k, p.view k = rotRM_mat θo φo 0 2 k := by
    intro k
    rw [← hout, octa_Rz_mul_row2]
    rfl
  by_cases hs : sin φo = 0
  · refine ⟨θo * cos φo + -αo, 0, φo, ⟨le_rfl, by positivity⟩, hφo, ?_⟩
    show Rz_mat (θo * cos φo + -αo) * p.outerRot.val = _
    rw [← Bounding.Rz_mat_mul_Rz_mat, Matrix.mul_assoc, hout, octa_Rz_mul_rotRM_mat_pole hs]
  · have hspos : 0 < sin φo := lt_of_le_of_ne (sin_nonneg_of_mem_Icc hφo) (Ne.symm hs)
    obtain ⟨hd1, hd0, -⟩ := hdom
    obtain ⟨r0, r1, -⟩ := octa_rotRM_mat_row2_zero θo φo
    rw [hview, hview, r0, r1] at hd0
    rw [hview, r1] at hd1
    exact ⟨-αo, θo, φo, octa_theta_mem hθo hspos hd0 hd1, hφo, hout⟩

/-- An atlas pose equals any matrix pose with outer rotation `rotRM_mat θ φ 0`,
relative rotation chart · cayley(x, y, z), and the same offset. -/
theorem octa_matrixPoseWithOffset_eq_of (q : AtlasPose ℝ) (reduced : MatrixPose)
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

/-! ### The full octahedral reduction -/

open AtlasEdgeCertificate in
/-- Every matrix pose of an `OModel` has an equivalent bounded atlas
representative whose view lies in the Oh chamber and whose relative rotation
lies in the O cell. -/
theorem OModel.exists_octa_full_atlas_translated_pose [OctahedralSolid] (P : OModel)
    (p : MatrixPose) :
    ∃ chart : ChartIndex, ∃ q : AtlasPose ℝ, ∃ offset : ℝ²,
      q ∈ AtlasPose.rootInterval ℝ ∧ q.CayleyBounded ∧ q.InOctaView ∧
      q.InOctaFundamentalDomain chart ∧
      (RupertPose (q.matrixPoseWithOffset chart offset) P.toC4.polyhedron.hull ↔
        RupertPose p P.toC4.polyhedron.hull) := by
  obtain ⟨p1, hcone1, heq1⟩ := P.exists_octaViewCone_pose p
  obtain ⟨δ, θ, φ, hθ, hφ, hout⟩ := exists_octa_euler_outer p1 hcone1
  have heq2 : RupertPose (p1.rotateBy δ) P.toC4.polyhedron.hull ↔
      RupertPose p1 P.toC4.polyhedron.hull :=
    MatrixPose.RupertPose_rotateBy_iff p1 δ _
  obtain ⟨g, hgcell⟩ := exists_mul_octa_inCell (p1.rotateBy δ).relativeRotation
  let reduced := MatrixPose.rightOctaSymmetry (p1.rotateBy δ) g
  obtain ⟨chart, x, hx, y, hy, z, hz, hradius, hrelative⟩ :=
    exists_bounded_chart_cayley reduced.relativeRotation
      (Noperts.Atlas.MatrixPose.relativeRotation_mem_SO3 reduced)
  let q : AtlasPose ℝ := ⟨θ, φ, x, y, z⟩
  have houter' : reduced.outerRot.val = rotRM_mat q.θ q.φ 0 := hout
  have hmatrix : q.matrixPoseWithOffset chart reduced.innerOffset = reduced :=
    octa_matrixPoseWithOffset_eq_of q reduced houter' chart hrelative
  have hpi4 : π / 4 ≤ 8 / 5 := by linarith [pi_lt_d2]
  refine ⟨chart, q, reduced.innerOffset, ?_, hradius, ?_, ?_, ?_⟩
  · rw [NonemptyInterval.mem_def, AtlasPose.le_iff, AtlasPose.le_iff]
    dsimp only [AtlasPose.rootInterval, q]
    exact ⟨⟨hθ.1, hφ.1, hx.1, hy.1, hz.1⟩,
      ⟨hθ.2.trans hpi4, hφ.2.trans pi_le_four, hx.2, hy.2, hz.2⟩⟩
  · -- The view of q is the view of p1.
    have hv : (fun c => viewVector q c) = p1.view := by
      rw [← octa_view_rotateBy p1 δ]
      funext k
      obtain ⟨r0, r1, r2⟩ := octa_rotRM_mat_row2_zero θ φ
      have hk : (p1.rotateBy δ).view k = rotRM_mat θ φ 0 2 k := by
        simp only [MatrixPose.view]
        rw [hout]
      rw [hk]
      fin_cases k <;> simp [viewVector, q, r0, r1, r2]
    unfold AtlasPose.InOctaView
    rw [hv]
    exact hcone1
  · show InOctaCell (chartMatrix chart * cayleyMatrix x y z)
    rw [← hrelative, MatrixPose.relativeRotation_rightOctaSymmetry]
    exact hgcell
  · rw [hmatrix, P.RupertPose_rightOctaSymmetry_iff, heq2, heq1]

end Noperts.Pipeline

end
