module

public import Basic

@[expose] public section

/-!
# The C3 rotations about (1,1,1)

The cyclic coordinate permutations, as exact matrices. They live in their own
file (importing only `Noperts.Basic`) so that the model layer
(`Septopert.SolidModel`) can use them without importing the
mirror-tie and cell layers (`Group`, `Cell`), which import the certificate
pipeline.
-/

namespace Septopert

open scoped Matrix

/-- (x,y,z) ↦ (y,z,x), k times. -/
def c3Mat : Fin 3 → Matrix (Fin 3) (Fin 3) ℝ
  | 0 => 1
  | 1 => !![0, 1, 0; 0, 0, 1; 1, 0, 0]
  | 2 => !![0, 0, 1; 1, 0, 0; 0, 1, 0]

theorem c3Mat_mem (k : Fin 3) : c3Mat k ∈ SO3 := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · fin_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [c3Mat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]
  · fin_cases k <;> simp [c3Mat, Matrix.det_fin_three]

noncomputable def c3SO3 (k : Fin 3) : SO3 := ⟨c3Mat k, c3Mat_mem k⟩

theorem c3_mul_c3 (k k' : Fin 3) : c3Mat k * c3Mat k' = c3Mat (k + k') := by
  fin_cases k <;> fin_cases k' <;> simp only [Fin.reduceAdd, Fin.isValue] <;> ext a b <;>
    fin_cases a <;> fin_cases b <;> simp [c3Mat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]

end Septopert
