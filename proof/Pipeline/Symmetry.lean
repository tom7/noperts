module

public import Pipeline.Approximation
public import Pose
public import RealMod

@[expose] public section

/-!
# Threefold symmetry of the model

Every `C5Model` is invariant under the exact C3 rotations `c3Mat g` about
(1,1,1): `c3Mat g` maps vertex `(k, s)` to vertex `(g + k, s)`
(`rotate_vertex`), hence permutes the vertices and fixes the hull
(`rotate_hull`).

(The fivefold pipeline also reduced the Euler azimuths modulo `2π/5` here;
the C3 axis is not the Euler z axis, so that reduction has no analogue and
was removed.)
-/

namespace Noperts.Pipeline

variable {P : C5Model}

open Septopert (c3Mat c3_mul_c3)

theorem toEuclideanLin_mul_apply (A B : Matrix (Fin 3) (Fin 3) ℝ) (v : ℝ³) :
    A.toEuclideanLin (B.toEuclideanLin v) = (A * B).toEuclideanLin v := by
  simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

theorem rotate_vertex (g k : OrbitIndex) (s : SeedIndex) :
    (c3Mat g).toEuclideanLin (P.vertex (vertexIndex k s)) =
      P.vertex (vertexIndex (g + k) s) := by
  simp only [C5Model.vertex, orbitIndex_vertexIndex, seedIndex_vertexIndex]
  rw [toEuclideanLin_mul_apply, c3_mul_c3]

theorem rotate_vertex' (g : OrbitIndex) (i : VertexIndex) :
    (c3Mat g).toEuclideanLin (P.vertex i) =
      P.vertex (vertexIndex (g + orbitIndex i) (seedIndex i)) := by
  have hi : vertexIndex (orbitIndex i) (seedIndex i) = i := indexEquiv.symm_apply_apply i
  conv_lhs => rw [← hi]
  exact rotate_vertex g _ _

theorem rotate_vertices (g : OrbitIndex) :
    (c3Mat g).toEuclideanLin '' (P.verts : Set ℝ³) = P.verts := by
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

/-- The C3 rotations preserve the hull. -/
theorem rotate_hull (g : OrbitIndex) :
    (c3Mat g).toEuclideanLin '' P.polyhedron.hull = P.polyhedron.hull := by
  rw [P.polyhedron_hull, LinearMap.image_convexHull]
  congr 1
  exact rotate_vertices g

end Noperts.Pipeline

end
