module

public import Septopert.MirrorTie
public import Septopert.C3

@[expose] public section

/-!
# The symmetry group C3v of the 7-vertex candidate

With the 3-fold axis along (1,1,1), C3v ≅ S3 acts on ℝ³ by permuting
coordinates: the rotations (C3) are the cyclic permutations, the mirrors
the transpositions. All entries are 0 or ±1.

- `c3Mat k` (defined in `C3.lean`): the cyclic permutation (x,y,z) ↦ (y,z,x)
  applied k times.
- `mirrorMat i`: the transposition of the two coordinates other than i
  (the mirror whose plane contains the axis and e_i).
- `mirrorQMat i = −mirrorMat i`: the rotation Q with σ = −Q, as used by
  the mirror-tie reduction (`MirrorTie.lean`): the half-turn about the
  mirror's normal.

`c3_mul_mirrorQ`: the C3 rotations permute the Q's (c3Mat k · mirrorQMat i =
mirrorQMat (i + k)), which makes the set of mirror-tie candidates closed
under both operations of the reduction.
-/

namespace Septopert
open Noperts

open scoped Matrix

/-- The transposition of the two coordinates other than i. -/
def mirrorMat : Fin 3 → Matrix (Fin 3) (Fin 3) ℝ
  | 0 => !![1, 0, 0; 0, 0, 1; 0, 1, 0]
  | 1 => !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  | 2 => !![0, 1, 0; 1, 0, 0; 0, 0, 1]

/-- Q = −σ for the mirror σ = `mirrorMat i`. -/
def mirrorQMat (i : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ := -mirrorMat i

theorem mirrorQMat_mem (i : Fin 3) : mirrorQMat i ∈ SO3 := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [mirrorQMat, mirrorMat, Matrix.mul_apply, Fin.sum_univ_three]
  · fin_cases i <;> simp [mirrorQMat, mirrorMat, Matrix.det_fin_three]

noncomputable def mirrorQ (i : Fin 3) : SO3 := ⟨mirrorQMat i, mirrorQMat_mem i⟩

/-- The C3 rotations permute the Q's: c3Mat k · mirrorQMat i = mirrorQMat (i + k). -/
theorem c3_mul_mirrorQ (k i : Fin 3) : c3Mat k * mirrorQMat i = mirrorQMat (i + k) := by
  fin_cases k <;> fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [c3Mat, mirrorQMat, mirrorMat, Matrix.mul_apply, Fin.sum_univ_three]

end Septopert
