module

public import M7.Model

@[expose] public section

/-!
# The vertex permutations of M7's symmetries

M7 (`M7.Model`: vertices (a,a,b) up to coordinate permutation and (t,t,t), denominator 64) has
the 3-fold axis (1,1,1). `c3Perm k` and `mirrorPerm i` are the vertex permutations induced by
`c3Mat k` and `mirrorMat i` (coordinate permutations); the vertex order is that of `vertexQ`, so
they are those of the SeptopertM18.
-/

namespace M7

def c3Perm : Fin 3 → Fin 7 → Fin 7 := ![![0, 1, 2, 3, 4, 5, 6], ![2, 0, 1, 5, 3, 4, 6], ![1, 2, 0, 4, 5, 3, 6]]

def mirrorPerm : Fin 3 → Fin 7 → Fin 7 := ![![0, 2, 1, 3, 5, 4, 6], ![2, 1, 0, 5, 4, 3, 6], ![1, 0, 2, 4, 3, 5, 6]]

end M7
