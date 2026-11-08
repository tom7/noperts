module

public import Septopert.IsNopert
public import Pipeline.Similarity

@[expose] public section

/-!
# Septopert with integer coordinates

(The certificates are built in a congruent frame (`verts`); similarity invariance transfers the result to `intVerts`, which is just a detail.)

`intVerts` are the vertices (-7, 7, 7), (7, -7, 7), (7, 7, -7), (3, -4, -4), (-4, 3, -4),
(-4, -4, 3), (7, 7, 7) (Septopert's integer coordinates). They are the image of `Septopert.verts` under the
similarity `similarity` (a scaling, an orthogonal map and a translation), so the Rupertness of
the two sets is equivalent.
-/

namespace Septopert

open Noperts Noperts.Pipeline

/-- The seven vertices of Septopert with integer coordinates. -/
def intVertexQ : Fin 7 → Fin 3 → ℚ := ![
  ![-7, 7, 7], ![7, -7, 7], ![7, 7, -7], ![3, -4, -4], ![-4, 3, -4], ![-4, -4, 3], ![7, 7, 7]]

/-- The vertex set of Septopert with integer coordinates. -/
noncomputable def intVerts : Finset ℝ³ := Finset.univ.image fun i : Fin 7 => toR3 (intVertexQ i)

/-- The Septopert as used in the main theorem: its integer-coordinate vertex set. -/
noncomputable abbrev septopert : Finset ℝ³ := intVerts

/-- The orthogonal part of the similarity: diagonal 1/3, off-diagonal -2/3. -/
noncomputable def simM : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1/3, -2/3, -2/3; -2/3, 1/3, -2/3; -2/3, -2/3, 1/3]

/-- The similarity `x ↦ (1/8, 1/8, 1/8) + (3/64) • simM x` taking `intVerts` to `verts`. -/
noncomputable def simMap (x : ℝ³) : ℝ³ :=
  toR3 ![1/8, 1/8, 1/8] + (3/64 : ℝ) • simM.toEuclideanLin x

theorem simM_mem : simM ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [simM, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

theorem simMap_intVertex (i : Fin 7) : simMap (toR3 (intVertexQ i)) = toR3 (vertexQ i) := by
  ext k
  fin_cases i <;> fin_cases k <;>
    simp [simMap, simM, toR3, intVertexQ, vertexQ, Matrix.toEuclideanLin, dotProduct, Fin.sum_univ_three] <;> norm_num

theorem intVerts_image_eq : intVerts.image simMap = verts := by
  unfold intVerts verts
  rw [Finset.image_image]
  congr 1
  funext i
  exact simMap_intVertex i

theorem not_coplanar_intVerts : ¬ Coplanar ℝ (intVerts : Set ℝ³) := by
  refine not_coplanar_of_det3_ne_zero
    (a := toR3 (intVertexQ 0)) (b := toR3 (intVertexQ 1)) (c := toR3 (intVertexQ 2))
    (d := toR3 (intVertexQ 6))
    (by simp [intVerts]) (by simp [intVerts]) (by simp [intVerts]) (by simp [intVerts]) ?_
  simp [det3, Matrix.det_fin_three, toR3, intVertexQ]
  norm_num

/-- If Septopert is not Rupert, neither is the integer copy. -/
theorem isNopert_intVerts_of_not_isRupert_verts (h : ¬ IsRupert verts) : IsNopert intVerts := by
  refine ⟨not_coplanar_intVerts, fun hr => h ?_⟩
  have := isRupert_image_similarity (toR3 ![1/8, 1/8, 1/8]) (3/64) (by norm_num) simM
    simM_mem intVerts hr
  rw [← intVerts_image_eq]
  exact this

/-- **Septopert with integer coordinates is a nopert**, given valid certificate data. These are Septopert's
integer coordinates (-7, 7, 7), (3, -4, -4), (7, 7, 7) and permutations. The certificates are
built in the congruent frame `verts` (scaled by 3/64, reflected through the (1, 1, 1) axis plane
composed with the 180 degree rotation, and translated), and similarities preserve Rupertness. -/
theorem isNopert_intVerts (h : CertificatesValid) : IsNopert intVerts :=
  isNopert_intVerts_of_not_isRupert_verts (not_isRupert_of_certificatesValid h)

end Septopert

end
