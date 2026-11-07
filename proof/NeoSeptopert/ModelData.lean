module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Rat.Defs

@[expose] public section

/-!
# The rational model of the NeoSeptopert (committed data)

Axis (1,1,1): vertices (a,a,b) up to coordinate permutation and (t,t,t),
denominator 32. `c3Perm k` and `mirrorPerm i` are the vertex permutations
induced by `c3Mat k` and `mirrorMat i` (coordinate permutations).
-/

namespace NeoSeptopert

def vertexQ : Fin 7 → Fin 3 → ℚ := ![
  ![(-9 / 16 : ℚ), (9 / 32 : ℚ), (9 / 32 : ℚ)],
  ![(9 / 32 : ℚ), (-9 / 16 : ℚ), (9 / 32 : ℚ)],
  ![(9 / 32 : ℚ), (9 / 32 : ℚ), (-9 / 16 : ℚ)],
  ![(17 / 32 : ℚ), (3 / 32 : ℚ), (3 / 32 : ℚ)],
  ![(3 / 32 : ℚ), (17 / 32 : ℚ), (3 / 32 : ℚ)],
  ![(3 / 32 : ℚ), (3 / 32 : ℚ), (17 / 32 : ℚ)],
  ![(-9 / 32 : ℚ), (-9 / 32 : ℚ), (-9 / 32 : ℚ)]]

def c3Perm : Fin 3 → Fin 7 → Fin 7 := ![![0, 1, 2, 3, 4, 5, 6], ![2, 0, 1, 5, 3, 4, 6], ![1, 2, 0, 4, 5, 3, 6]]

def mirrorPerm : Fin 3 → Fin 7 → Fin 7 := ![![0, 2, 1, 3, 5, 4, 6], ![2, 1, 0, 5, 4, 3, 6], ![1, 0, 2, 4, 3, 5, 6]]

end NeoSeptopert
