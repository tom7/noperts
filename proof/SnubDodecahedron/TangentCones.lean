module

public import SnubDodecahedron.RationalVertices

@[expose] public section

/-!
# Tangent cones of the rational snub dodecahedron

For a linear functional to be maximized at a vertex `v` of a polytope, it is
enough that it does not increase along the edges at `v`, i.e. towards the
generators of `v`'s tangent cone. In the rational model each vertex has at
most seven such generators (`supportGenerator`; padded with the vertex
itself). A `TangentCombination` certifies that another vertex `w` lies in
the tangent cone at `v`: `w - v` is a nonnegative combination, with
coefficients summing to at least 1, of three generator directions. A
`TangentTableValid` table (one combination for every ordered pair of
distinct vertices; `GeneratedTangentCones.table_valid_kernel`, checked by
the kernel) then lets `SparseSupport` replace a support check against all
60 vertices by one against seven generators.

This module depends only on the vertex data, not on the certificate
pipeline, so that the generated 75k-line table is not rebuilt when the
pipeline changes.
-/

namespace SnubDodecahedron.SparseSupport

/-- Tangent-cone generators for each rational checker vertex.  Entries beyond
the actual degree are padded by the vertex itself. -/
def supportGenerator : VertexIndex → Fin 7 → VertexIndex := ![
  ![1, 2, 12, 48, 49, 0, 0],
  ![0, 2, 3, 12, 14, 1, 1],
  ![0, 1, 3, 4, 49, 2, 2],
  ![1, 2, 4, 5, 6, 3, 3],
  ![2, 3, 6, 53, 55, 4, 4],
  ![3, 6, 7, 8, 16, 5, 5],
  ![3, 4, 5, 8, 55, 6, 6],
  ![5, 8, 9, 16, 18, 7, 7],
  ![5, 6, 7, 9, 10, 8, 8],
  ![7, 8, 10, 11, 22, 9, 9],
  ![8, 9, 11, 57, 59, 10, 10],
  ![9, 10, 22, 23, 59, 11, 11],
  ![0, 1, 13, 14, 24, 12, 12],
  ![12, 14, 15, 24, 26, 13, 13],
  ![1, 12, 13, 15, 16, 14, 14],
  ![13, 14, 16, 17, 18, 15, 15],
  ![5, 7, 14, 15, 18, 16, 16],
  ![15, 18, 19, 20, 28, 17, 17],
  ![7, 15, 16, 17, 20, 18, 18],
  ![17, 20, 21, 28, 30, 19, 19],
  ![17, 18, 19, 21, 22, 20, 20],
  ![19, 20, 22, 23, 34, 21, 21],
  ![9, 11, 20, 21, 23, 22, 22],
  ![11, 21, 22, 34, 35, 23, 23],
  ![12, 13, 25, 26, 36, 24, 24],
  ![24, 26, 27, 36, 38, 25, 25],
  ![13, 24, 25, 27, 28, 26, 26],
  ![25, 26, 28, 29, 30, 27, 27],
  ![17, 19, 26, 27, 30, 28, 28],
  ![27, 30, 31, 32, 40, 29, 29],
  ![19, 27, 28, 29, 32, 30, 30],
  ![29, 32, 33, 40, 42, 31, 31],
  ![29, 30, 31, 33, 34, 32, 32],
  ![31, 32, 34, 35, 46, 33, 33],
  ![21, 23, 32, 33, 35, 34, 34],
  ![23, 33, 34, 46, 47, 35, 35],
  ![24, 25, 37, 38, 48, 36, 36],
  ![36, 38, 39, 48, 50, 37, 37],
  ![25, 36, 37, 39, 40, 38, 38],
  ![37, 38, 40, 41, 42, 39, 39],
  ![29, 31, 38, 39, 42, 40, 40],
  ![39, 42, 43, 44, 52, 41, 41],
  ![31, 39, 40, 41, 44, 42, 42],
  ![41, 44, 45, 52, 54, 43, 43],
  ![41, 42, 43, 45, 46, 44, 44],
  ![43, 44, 46, 47, 58, 45, 45],
  ![33, 35, 44, 45, 47, 46, 46],
  ![35, 45, 46, 58, 59, 47, 47],
  ![0, 36, 37, 49, 50, 48, 48],
  ![0, 2, 48, 50, 51, 49, 49],
  ![37, 48, 49, 51, 52, 50, 50],
  ![49, 50, 52, 53, 54, 51, 51],
  ![41, 43, 50, 51, 54, 52, 52],
  ![4, 51, 54, 55, 56, 53, 53],
  ![43, 51, 52, 53, 56, 54, 54],
  ![4, 6, 53, 56, 57, 55, 55],
  ![53, 54, 55, 57, 58, 56, 56],
  ![10, 55, 56, 58, 59, 57, 57],
  ![45, 47, 56, 57, 59, 58, 58],
  ![10, 11, 47, 57, 58, 59, 59]
]

structure TangentCombination where
  generator : Fin 3 → Fin 7
  coefficient : Fin 3 → ℚ
deriving DecidableEq

def TangentCombination.Valid (combination : TangentCombination)
    (base target : VertexIndex) : Prop :=
  (∀ l, 0 ≤ combination.coefficient l) ∧
  1 ≤ ∑ l, combination.coefficient l ∧
  (∀ l, combination.coefficient l ≠ 0 →
    supportGenerator base (combination.generator l) ≠ base) ∧
  rationalVertex target - rationalVertex base =
    ∑ l, combination.coefficient l •
      (rationalVertex (supportGenerator base (combination.generator l)) -
        rationalVertex base)

instance (combination : TangentCombination) (base target : VertexIndex) :
    Decidable (combination.Valid base target) := by
  unfold TangentCombination.Valid
  infer_instance

def TangentTableValid
    (combination : VertexIndex → VertexIndex → TangentCombination) : Prop :=
  ∀ base target, target ≠ base → (combination base target).Valid base target

instance (combination : VertexIndex → VertexIndex → TangentCombination) :
    Decidable (TangentTableValid combination) := by
  unfold TangentTableValid
  infer_instance

end SnubDodecahedron.SparseSupport

end
