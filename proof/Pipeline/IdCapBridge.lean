module

public import Pipeline.IdCap
public import Pipeline.CayleyNear
public import Pipeline.AtlasLocalCertificate
public import Pipeline.AtlasProjectiveView
public import Pipeline.HalfTurnBasic

@[expose] public section

/-!
# Identity blow-up certificates as identity-tube claims

An identity-tube table row claims: for every atlas pose whose normalized view
lies in the row's triangle and whose relative rotation is within the tube
radius of the identity (`AtlasLocalCertificate.Box.mismatchRadius ≤ r`), the
pose is not Rupert. For an exact model (`modelErrorQ = 0`) an identity
blow-up certificate (`KCap.IdCert`) over the row's triangle with radius ρ
proves it for r ≤ ρ ≤ 1 (`idCert_not_rupert`): the relative rotation is a
Cayley rotation of a vector of length at most ρ (`exists_cayleyMatrix_of_opNorm_le`),
the view is `viewScale` times a point of the triangle, and the hull is the
hull of the rational vertices.
-/

namespace Noperts.Pipeline

open scoped Matrix RealInnerProductSpace
open Noperts.Pipeline.CayleyAtlas
open Noperts.Atlas.ProjectiveView

variable [SolidModel]

/-- The certificate of an identity-tube row: its vertices, the row's triangle. -/
def rowIdCert (V : Array (KCap.KVec ℚ)) (triangle : Triangle ℚ) (rho : ℚ)
    (faces : List ((ℕ × Bool) × KCap.ATree)) : KCap.IdCert ℚ :=
  ⟨V, fun k c => triangle k c, rho, faces⟩

/-- The row's vertices are the model's (as sets: the model may repeat a vertex in several
slots). -/
def vertsMatchModel (V : Array (KCap.KVec ℚ)) : Bool :=
  V.all (fun v => (List.finRange _).any fun i : VertexIndex => decide (rationalVertex i = v)) &&
    (List.finRange _).all fun i : VertexIndex => V.any fun v => decide (v = rationalVertex i)

omit [SolidModel] in
theorem kval_rat (v : KCap.KVec ℚ) : KCap.PVec.kval v = fun i => (v i : ℝ) := rfl

/-- With an exact model and the model's vertices, the hull of any model is the certificate's. -/
theorem polyhedron_hull_eq_idCert_hull (P : CyclicModel) (hmodel : SolidModel.modelErrorQ = 0)
    (V : Array (KCap.KVec ℚ)) (hV : vertsMatchModel V = true)
    (triangle : Triangle ℚ) (rho : ℚ) (faces : List ((ℕ × Bool) × KCap.ATree)) :
    P.polyhedron.hull = (rowIdCert V triangle rho faces).hull := by
  have hv : ∀ i, P.vertex i = toR3 (rationalVertex i) := by
    intro i
    have h := P.close i
    rw [show modelErrorQ = 0 from hmodel] at h
    push_cast at h
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
  simp only [vertsMatchModel, Bool.and_eq_true, Array.all_eq_true, List.all_eq_true, List.any_eq_true,
    Array.any_eq_true, decide_eq_true_eq, List.mem_finRange, true_and] at hV
  obtain ⟨hV1, hV2⟩ := hV
  rw [P.polyhedron_hull, KCap.IdCert.hull]
  congr 1
  ext v
  simp only [CyclicModel.verts, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range,
    Set.mem_ofPred_eq, rowIdCert, List.mem_map, Array.mem_toList_iff]
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨j, hj, hji⟩ := hV2 i trivial
    exact ⟨_, ⟨V[j], Array.getElem_mem hj, rfl⟩, by rw [hv i, hji]; rfl⟩
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    obtain ⟨j, hj⟩ := Array.getElem_of_mem hw
    obtain ⟨i, hi⟩ := hV1 j hj.1
    exact ⟨i, by rw [hv i, hi, hj.2]; rfl⟩

omit [SolidModel] in
/-- The view of an atlas pose is its view vector. -/
theorem matrixPoseWithOffset_view (chart : ChartIndex) (p : AtlasPose ℝ) (offset : ℝ²) :
    (p.matrixPoseWithOffset chart offset).view = fun k => AtlasEdgeCertificate.viewVector p k := by
  funext k
  simp only [MatrixPose.view, AtlasPose.matrixPoseWithOffset_outerRot_val]
  fin_cases k <;>
    simp [AtlasEdgeCertificate.viewVector, rotRM_mat, Matrix.mul_apply, Rz_mat, Ry_mat,
      Fin.sum_univ_three] <;> ring

/-- **The bridge**: an identity blow-up certificate over a row's triangle with radius ρ ≤ 1
rules out every tube of the identity (symmetry 0) up to mismatch radius ρ whose normalized
view lies in the triangle. -/
theorem idCert_not_rupert (P : CyclicModel) (hmodel : SolidModel.modelErrorQ = 0)
    (V : Array (KCap.KVec ℚ)) (hV : vertsMatchModel V = true)
    (triangle : Triangle ℚ) (rho : ℚ) (faces : List ((ℕ × Bool) × KCap.ATree))
    (hcheck : (rowIdCert V triangle rho faces).check = true) (hρ1 : rho ≤ 1)
    (box : AtlasLocalCertificate.Box) (hsym : box.symmetryIndex = 0)
    (hmis : box.mismatchRadius ≤ rho)
    {p : AtlasPose ℝ} (hp : p ∈ box.interval.toReal) (offset : ℝ²) (root : Fin 8)
    (hscale : 1 ≤ AtlasProjectiveView.viewScale root p)
    (hmem : InTriangle (Noperts.Atlas.ProjectiveView.toReal triangle) (AtlasProjectiveView.normalizedView root p)) :
    ¬ RupertPose (p.matrixPoseWithOffset box.chart offset) P.polyhedron.hull := by
  rw [polyhedron_hull_eq_idCert_hull P hmodel V hV triangle rho faces]
  set cert := rowIdCert V triangle rho faces with hcert
  have hrho0 : (0 : ℚ) ≤ rho := by
    simp only [KCap.IdCert.check, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    exact hcheck.1
  -- The relative rotation is a Cayley rotation of a short vector.
  set R := chartMatrix box.chart * cayleyMatrix p.x p.y p.z with hRdef
  have hRmem : R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
    Submonoid.mul_mem _ (chartMatrix_mem_SO3 box.chart) (cayleyMatrix_mem_SO3 p.x p.y p.z)
  have hnorm : ‖R.toEuclideanLin.toContinuousLinearMap - 1‖ ≤ (box.mismatchRadius : ℝ) := by
    have h := box.exactRelativeMismatchCLM_norm_le hp
    unfold AtlasLocalCertificate.Box.exactRelativeMismatchCLM AtlasLocalCertificate.Box.relativeCLM at h
    rw [hsym, so3CLM_symmetry_zero] at h
    exact h
  obtain ⟨x, y, z, hxyz, hRxyz⟩ := exists_cayleyMatrix_of_opNorm_le R hRmem (box.mismatchRadius : ℝ)
    (rho : ℝ) (by exact_mod_cast hmis) (by exact_mod_cast hρ1) hnorm
  have hbound : ∀ t : ℝ, t ^ 2 ≤ (rho : ℝ) ^ 2 → |t| ≤ (cert.rho : ℝ) := by
    intro t ht
    have : (0 : ℝ) ≤ rho := by exact_mod_cast hrho0
    exact abs_le_of_sq_le_sq' ht this |> fun h => abs_le.mpr h
  have hw : ∀ i, |(![x, y, z] : Fin 3 → ℝ) i| ≤ cert.rho := by
    intro i
    fin_cases i <;> simp <;> apply hbound <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  -- The view.
  obtain ⟨wt, hwt0, hwt1, hpt⟩ := hmem
  have hvs : AtlasProjectiveView.viewScale root p ≠ 0 := by linarith
  have hview : (p.matrixPoseWithOffset box.chart offset).view =
      AtlasProjectiveView.viewScale root p • (KCap.PVec.kval (cert.c 0) +
        (wt 1 • (KCap.PVec.kval (cert.c 1) - KCap.PVec.kval (cert.c 0)) +
          wt 2 • (KCap.PVec.kval (cert.c 2) - KCap.PVec.kval (cert.c 0)))) := by
    rw [matrixPoseWithOffset_view]
    funext k
    have hk := congrFun hpt k
    simp only [AtlasProjectiveView.normalizedView, affinePoint, Fin.sum_univ_three,
      Noperts.Atlas.ProjectiveView.toReal] at hk
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul, hcert, rowIdCert, kval_rat]
    rw [div_eq_iff hvs] at hk
    have h0 : wt 0 = 1 - wt 1 - wt 2 := by simp [Fin.sum_univ_three] at hwt1; linarith
    rw [hk, h0]
    ring
  have hα : 0 ≤ wt 1 ∧ wt 1 ≤ 1 := ⟨hwt0 1, by simp [Fin.sum_univ_three] at hwt1; linarith [hwt0 0, hwt0 2]⟩
  have hβ : 0 ≤ wt 2 ∧ wt 2 ≤ 1 := ⟨hwt0 2, by simp [Fin.sum_univ_three] at hwt1; linarith [hwt0 0, hwt0 1]⟩
  have hαβ : wt 1 + wt 2 ≤ 1 := by simp [Fin.sum_univ_three] at hwt1; linarith [hwt0 0]
  apply cert.claim hcheck _ _ (wt 1) (wt 2) hα.1 hβ.1 hαβ hview ![x, y, z] hw
  rw [AtlasPose.matrixPoseWithOffset_relativeRotation]
  simpa using hRxyz

end Noperts.Pipeline

end
