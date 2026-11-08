module

public import ChippedM18.ModelData
public import ChippedM18.Cell
public import ChippedM18.SolidModel

@[expose] public section

/-!
# The 19-vertex solid (ChippedM18) and its C3v symmetry

`solid` is the convex hull of the rational vertices (`ModelData`). Each
coordinate permutation maps the vertex set onto itself (`c3Perm`,
`mirrorPerm`, checked vertex by vertex), so the hull is invariant under C3
(`c3Mat_image_solid`) and under the improper symmetries −Q_i = σ_i
(`mirrorQ_neg_image_solid`), in the forms the reductions use
(`RupertPose_mirrorTie_iff`, `exists_viewDomain_pose`).
-/

namespace ChippedM18
open Noperts

open scoped Matrix

noncomputable def poly : Polyhedron (Fin 19) ℝ³ := ⟨fun i => toR3 (vertexQ i)⟩

/-- The solid. -/
def solid : Set ℝ³ := poly.hull

/-- A rational matrix acts on `toR3` of a rational vector by the rational product. -/
theorem toEuclideanLin_toR3 (M : Matrix (Fin 3) (Fin 3) ℚ) (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : M.map (fun x => (x : ℝ)) = A) (q : Fin 3 → ℚ) :
    A.toEuclideanLin (toR3 q) = toR3 (fun j => ∑ l, M j l * q l) := by
  subst hA
  ext j
  simp [toR3, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- The mirror matrices over ℚ. -/
def mirrorMatQ : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ
  | 0 => !![1, 0, 0; 0, 0, 1; 0, 1, 0]
  | 1 => !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  | 2 => !![0, 1, 0; 1, 0, 0; 0, 0, 1]

theorem mirrorMatQ_map (g : Fin 3) : (mirrorMatQ g).map (fun x => (x : ℝ)) = mirrorMat g := by
  fin_cases g <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [mirrorMatQ, mirrorMat]

/-- The rational action of the C3 rotations permutes the vertices (kernel-checked). -/
theorem c3MatQ_vertex_rat : ∀ (k : Fin 3) (i : Fin 19),
    (fun j => ∑ l, c3MatQ k j l * vertexQ i l) = vertexQ (c3Perm k i) := by
  decide +kernel

theorem mirrorMatQ_vertex_rat : ∀ (g : Fin 3) (i : Fin 19),
    (fun j => ∑ l, mirrorMatQ g j l * vertexQ i l) = vertexQ (mirrorPerm g i) := by
  decide +kernel

theorem c3Mat_vertex (k : Fin 3) (i : Fin 19) :
    (c3Mat k).toEuclideanLin (toR3 (vertexQ i)) = toR3 (vertexQ (c3Perm k i)) := by
  rw [toEuclideanLin_toR3 (c3MatQ k) _ (c3MatQ_map k), c3MatQ_vertex_rat]

theorem mirrorMat_vertex (i : Fin 3) (a : Fin 19) :
    (mirrorMat i).toEuclideanLin (toR3 (vertexQ a)) = toR3 (vertexQ (mirrorPerm i a)) := by
  rw [toEuclideanLin_toR3 (mirrorMatQ i) _ (mirrorMatQ_map i), mirrorMatQ_vertex_rat]

/-- A matrix permuting the vertices maps the solid into itself. -/
theorem image_solid_subset (A : Matrix (Fin 3) (Fin 3) ℝ) (π : Fin 19 → Fin 19)
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

end ChippedM18
