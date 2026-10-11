module

public import Nopert231.SolidModel

@[expose] public section

/-!
# Tangent cones of Nopert #231's rational model

For a linear functional to be maximized at a vertex `v` of a polytope, it is
enough that it does not increase along the edges at `v`, i.e. towards the
generators of `v`'s tangent cone. In the rational model each vertex has at
most seven such generators (`supportGenerator`; padded with the vertex
itself). A `TangentCombination` certifies that another vertex `w` lies in
the tangent cone at `v`: `w - v` is a nonnegative combination, with
coefficients summing to at least 1, of three generator directions. A
`TangentTableValid` table (one combination for every ordered pair of
distinct vertices; `GeneratedTangentCones.table_valid_kernel`, checked by
the kernel) then lets `SparseViewCheck` replace a support check against all
twenty vertices by one against seven generators.

This module depends only on the vertex data and the solid model (it is
stated about `Nopert231.rationalVertex`, the data itself), not on the
certificate pipeline above the model layer, so that the generated table is
not rebuilt when the pipeline changes.
-/

namespace Nopert231.SparseSupport

/-- Tangent-cone generators for each rational checker vertex.  Entries beyond
the actual degree are padded by the vertex itself. -/
def supportGenerator : VertexIndex → Fin 7 → VertexIndex := ![
  ![1, 4, 8, 12, 16, 17, 0],
  ![0, 2, 4, 5, 17, 18, 1],
  ![1, 3, 5, 6, 7, 18, 2],
  ![2, 7, 11, 15, 18, 19, 3],
  ![0, 1, 5, 8, 12, 16, 4],
  ![1, 2, 4, 6, 8, 9, 5],
  ![2, 5, 7, 9, 10, 11, 6],
  ![2, 3, 6, 11, 15, 19, 7],
  ![0, 4, 5, 9, 12, 16, 8],
  ![5, 6, 8, 10, 12, 13, 9],
  ![6, 9, 11, 13, 15, 10, 10],
  ![3, 6, 7, 10, 15, 19, 11],
  ![0, 4, 8, 9, 13, 16, 12],
  ![9, 10, 12, 14, 15, 16, 17],
  ![13, 15, 17, 19, 14, 14, 14],
  ![3, 7, 10, 11, 13, 14, 19],
  ![0, 4, 8, 12, 13, 17, 16],
  ![0, 1, 13, 14, 16, 18, 19],
  ![1, 2, 3, 17, 19, 18, 18],
  ![3, 7, 11, 14, 15, 17, 18]
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

end Nopert231.SparseSupport

end
