module

public import Mathlib.Data.Finset.Max
public import Pipeline.CayleyAtlas

@[expose] public section

/-!
# The relative-rotation cell of the cyclic symmetry

The rotations `symmetryMatrix k` of the model's cyclic symmetry are
symmetries of the model. A relative rotation is in the max-trace (Dirichlet)
cell when none of them increases its trace on the right
(`InSymmetryFundamentalDomain`). For the icosahedral solids the symmetry is
C5 about z; for the Septopert it is C3 about (1,1,1).
-/

namespace Noperts.Pipeline

variable [SolidModel] {P : CyclicModel}

open scoped Matrix

def composeSymmetry (a b : OrbitIndex) : OrbitIndex :=
  ⟨(a.val + b.val) % SolidModel.orbitCount, Nat.mod_lt _ SolidModel.orbitCount_pos⟩

theorem composeSymmetry_eq_add (a b : OrbitIndex) : composeSymmetry a b = a + b := by
  apply Fin.ext
  simp [composeSymmetry, Fin.val_add]

theorem symmetryMatrix_mul_composeSymmetry (a b : OrbitIndex) :
    symmetryMatrix a * symmetryMatrix b =
      symmetryMatrix (composeSymmetry a b) := by
  rw [composeSymmetry_eq_add]
  exact symmetryMatrix_mul a b

/-- A relative rotation is in the identity Dirichlet cell when no
right symmetry increases its trace. -/
def InSymmetryFundamentalDomain
    (R : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ k : OrbitIndex,
    Matrix.trace (R * symmetryMatrix k) ≤ Matrix.trace R

end Noperts.Pipeline

end
