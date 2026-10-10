module

public import Pipeline.Approximation
public import Pose
public import RealMod

@[expose] public section

/-!
# The cyclic symmetry of the model

Every `C5Model` is invariant under the solid's exact cyclic symmetry:
`symmetryMatrix g` maps vertex `(k, s)` to vertex `(g + k, s)`
(`rotate_vertex`), hence permutes the vertices and fixes the hull
(`rotate_hull`). This is all the certificate pipeline uses of the symmetry.

(For the icosahedral solids, whose symmetry is C5 about the Euler z axis,
`FivefoldSymmetry` also reduces the Euler azimuths modulo `2π/5`.)
-/

namespace Noperts.Pipeline

variable [SolidModel] {P : C5Model}

omit [SolidModel] in
theorem toEuclideanLin_mul_apply (A B : Matrix (Fin 3) (Fin 3) ℝ) (v : ℝ³) :
    A.toEuclideanLin (B.toEuclideanLin v) = (A * B).toEuclideanLin v := by
  simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

theorem rotate_vertex (g k : OrbitIndex) (s : SeedIndex) :
    (symmetryMatrix g).toEuclideanLin (P.vertex (vertexIndex k s)) =
      P.vertex (vertexIndex (g + k) s) := by
  simp only [C5Model.vertex, orbitIndex_vertexIndex, seedIndex_vertexIndex]
  rw [toEuclideanLin_mul_apply, symmetryMatrix_mul]

theorem rotate_vertex' (g : OrbitIndex) (i : VertexIndex) :
    (symmetryMatrix g).toEuclideanLin (P.vertex i) =
      P.vertex (vertexIndex (g + orbitIndex i) (seedIndex i)) := by
  have hi : vertexIndex (orbitIndex i) (seedIndex i) = i := indexEquiv.symm_apply_apply i
  conv_lhs => rw [← hi]
  exact rotate_vertex g _ _

theorem rotate_vertices (g : OrbitIndex) :
    (symmetryMatrix g).toEuclideanLin '' (P.verts : Set ℝ³) = P.verts := by
  ext x
  simp only [C5Model.verts, Finset.coe_image, Finset.coe_univ, Set.image_univ,
    Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    exact ⟨_, (rotate_vertex' g i).symm⟩
  · rintro ⟨i, rfl⟩
    refine ⟨P.vertex (vertexIndex (orbitIndex i - g) (seedIndex i)), ⟨_, rfl⟩, ?_⟩
    rw [rotate_vertex, add_sub_cancel]
    exact congrArg P.vertex (indexEquiv.symm_apply_apply i)

/-- The symmetry rotations preserve the hull. -/
theorem rotate_hull (g : OrbitIndex) :
    (symmetryMatrix g).toEuclideanLin '' P.polyhedron.hull = P.polyhedron.hull := by
  rw [P.polyhedron_hull, LinearMap.image_convexHull]
  congr 1
  exact rotate_vertices g

end Noperts.Pipeline

end
