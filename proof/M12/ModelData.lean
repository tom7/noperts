module

public import M12.Model

@[expose] public section

/-!
# The vertex permutations of M12's symmetries

M12 (`M12.Model`: vertices (a,a,b) up to coordinate permutation and (t,t,t), denominator 16) has
the 3-fold axis (1,1,1). `c3Perm k` and `mirrorPerm i` are the vertex permutations induced by
`c3Mat k` and `mirrorMat i` (coordinate permutations); the vertex order is that of `vertexQ`, so
they are those of the Septopert.
-/

namespace M12

def c3Perm : Fin 3 → Fin 7 → Fin 7 := ![![0, 1, 2, 3, 4, 5, 6], ![2, 0, 1, 5, 3, 4, 6], ![1, 2, 0, 4, 5, 3, 6]]

def mirrorPerm : Fin 3 → Fin 7 → Fin 7 := ![![0, 2, 1, 3, 5, 4, 6], ![2, 1, 0, 5, 4, 3, 6], ![1, 0, 2, 4, 3, 5, 6]]

end M12
