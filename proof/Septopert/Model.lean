module

public import Septopert.ModelData
public import Septopert.Cell
public import Septopert.SolidModel

@[expose] public section

/-!
# The 7-vertex solid and its C3v symmetry

`solid` is the convex hull of the rational vertices (`ModelData`). Each
coordinate permutation maps the vertex set onto itself (`c3Perm`,
`mirrorPerm`, checked vertex by vertex), so the hull is invariant under C3
(`c3Mat_image_solid`) and under the improper symmetries −Q_i = σ_i
(`mirrorQ_neg_image_solid`), in the forms the reductions use
(`RupertPose_mirrorTie_iff`, `exists_viewDomain_pose`).
-/

namespace Septopert
open Noperts

open scoped Matrix

noncomputable def poly : Polyhedron (Fin 7) ℝ³ := ⟨fun i => toR3 (vertexQ i)⟩

/-- The solid. -/
def solid : Set ℝ³ := poly.hull

theorem c3Mat_vertex (k : Fin 3) (i : Fin 7) :
    (c3Mat k).toEuclideanLin (toR3 (vertexQ i)) = toR3 (vertexQ (c3Perm k i)) := by
  fin_cases k <;> fin_cases i <;> ext j <;> fin_cases j <;>
    simp [c3Mat, vertexQ, c3Perm, toR3, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]

theorem mirrorMat_vertex (i : Fin 3) (a : Fin 7) :
    (mirrorMat i).toEuclideanLin (toR3 (vertexQ a)) = toR3 (vertexQ (mirrorPerm i a)) := by
  fin_cases i <;> fin_cases a <;> ext j <;> fin_cases j <;>
    simp [mirrorMat, vertexQ, mirrorPerm, toR3, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]

/-- A matrix permuting the vertices maps the solid into itself. -/
theorem image_solid_subset (A : Matrix (Fin 3) (Fin 3) ℝ) (π : Fin 7 → Fin 7)
    (h : ∀ i, A.toEuclideanLin (toR3 (vertexQ i)) = toR3 (vertexQ (π i))) :
    A.toEuclideanLin '' solid ⊆ solid := by
  unfold solid Polyhedron.hull
  rw [LinearMap.image_convexHull]
  apply convexHull_mono
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  exact ⟨π i, (h i).symm⟩

/-- If A and B both map the solid into itself and A B = 1, A maps it onto itself. -/
theorem image_solid_eq (A B : Matrix (Fin 3) (Fin 3) ℝ) (hAB : A * B = 1)
    (hA : A.toEuclideanLin '' solid ⊆ solid) (hB : B.toEuclideanLin '' solid ⊆ solid) :
    A.toEuclideanLin '' solid = solid := by
  refine le_antisymm hA (fun v hv => ⟨B.toEuclideanLin v, hB ⟨v, hv, rfl⟩, ?_⟩)
  simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec, hAB]

theorem c3Mat_image_solid (k : Fin 3) : (c3Mat k).toEuclideanLin '' solid = solid := by
  refine image_solid_eq (c3Mat k) (c3Mat (negIdx k)) ?_
    (image_solid_subset _ _ (c3Mat_vertex k)) (image_solid_subset _ _ (c3Mat_vertex _))
  rw [c3_mul_c3]
  fin_cases k <;> rfl

theorem mirrorMat_mul_self (i : Fin 3) : mirrorMat i * mirrorMat i = 1 := by
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [mirrorMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem mirrorMat_image_solid (i : Fin 3) : (mirrorMat i).toEuclideanLin '' solid = solid :=
  image_solid_eq _ _ (mirrorMat_mul_self i)
    (image_solid_subset _ _ (mirrorMat_vertex i)) (image_solid_subset _ _ (mirrorMat_vertex i))

/-- The improper symmetries −Q_i = σ_i, in the form of `RupertPose_mirrorTie_iff`. -/
theorem mirrorQ_neg_image_solid (i : Fin 3) :
    (fun v => -((mirrorQMat i).toEuclideanLin v)) '' solid = solid := by
  have h : (fun v => -((mirrorQMat i).toEuclideanLin v)) = (mirrorMat i).toEuclideanLin := by
    funext v
    simp [mirrorQMat, map_neg]
  rw [h]
  exact mirrorMat_image_solid i

end Septopert
