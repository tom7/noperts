module

public import Mathlib.Data.Finset.Max
public import Pipeline.CayleyAtlas

@[expose] public section

/-!
# The threefold relative-rotation cell

The C3 rotations `c3Mat k` about (1,1,1) are symmetries of the model. A
relative rotation is in the C3 max-trace (Dirichlet) cell when none of them
increases its trace on the right. (The names `fivefoldMatrix` and
`InFivefoldFundamentalDomain` are kept from the fivefold pipeline;
`fivefoldMatrix k` is now `Septopert.c3Mat k`.)
-/

namespace Noperts.Pipeline

variable {P : C5Model}

open scoped Matrix

/-- The `k`th exact rotation around the symmetry axis (1,1,1). -/
noncomputable def fivefoldMatrix (k : OrbitIndex) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Septopert.c3Mat k

def composeSymmetry (a b : OrbitIndex) : OrbitIndex :=
  ⟨(a.val + b.val) % 3, Nat.mod_lt _ (by omega)⟩

@[simp] theorem fivefoldMatrix_zero : fivefoldMatrix 0 = 1 := rfl

theorem composeSymmetry_eq_add (a b : OrbitIndex) : composeSymmetry a b = a + b := by
  apply Fin.ext
  simp [composeSymmetry, Fin.val_add]

theorem fivefoldMatrix_mul (a b : OrbitIndex) :
    fivefoldMatrix a * fivefoldMatrix b =
      fivefoldMatrix (composeSymmetry a b) := by
  rw [composeSymmetry_eq_add]
  exact Septopert.c3_mul_c3 a b

/-- A relative rotation is in the identity C3 Dirichlet cell when no
right symmetry increases its trace. -/
def InFivefoldFundamentalDomain
    (R : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ k : OrbitIndex,
    Matrix.trace (R * fivefoldMatrix k) ≤ Matrix.trace R

end Noperts.Pipeline

end
