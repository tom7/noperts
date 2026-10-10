module

public import Pipeline.SolidModel
public import Septopert.C3
public import Septopert.ModelData

@[expose] public section

/-!
# The Septopert as a solid model for the certificate pipeline

The Septopert (data in `Septopert.ModelData`) is symmetric under C3v with the
3-fold axis along (1,1,1), so the C3 rotations are the cyclic coordinate
permutations `c3Mat k`, exact rational matrices. The model layout
(`Pipeline.SolidModel`) is rotation-major: three seeds v0, v3, v6
(`vertexQ` indices), and slot `3k + s` is seed `s` rotated by `c3Mat k`.
The axis vertex v6 is fixed by C3, so it fills three slots (2, 5, 8); the
other six vertices of the Septopert fill one slot each
(`rationalVertex_eq_vertexQ`).

The model is exact: the rational slots are the rotated seeds
(`exactVertex_eq`), the rational symmetry matrices are the exact ones, and
both error terms are 0 (the C++ checker's `MODEL_EXACT`: zero support error,
so exact support ties are allowed).

`solidModel` is a scoped instance: it is in effect inside `namespace
Septopert` (and wherever `Septopert` is opened), and nowhere else.
-/

namespace Septopert

open Noperts Noperts.Pipeline
open scoped Matrix

/-- The nine model slots (rotation-major: slot `3k + s` is seed `s` rotated by
`c3Mat k`). -/
def slotVertices : Fin 9 → Fin 3 → ℚ := ![
  ![-470319/524288, 327651/1048576, 327651/1048576],
  ![21999/32768, 11947/262144, 11947/262144],
  ![-514207/1048576, -514207/1048576, -514207/1048576],
  ![327651/1048576, 327651/1048576, -470319/524288],
  ![11947/262144, 11947/262144, 21999/32768],
  ![-514207/1048576, -514207/1048576, -514207/1048576],
  ![327651/1048576, -470319/524288, 327651/1048576],
  ![11947/262144, 21999/32768, 11947/262144],
  ![-514207/1048576, -514207/1048576, -514207/1048576]
]

/-! ### Fast evaluation in compiled code

`slotVertices` is a `![…]` literal of rationals. In compiled code each access
walks the `Fin.cons` chain and re-normalizes the rational literal, and the
native certificate checkers access vertices tens of thousands of times per
row. The `@[csimp]` lemma below makes compiled code read a table of rationals
computed once at initialization instead. It is a proved equality, so it
changes speed only, not what is checked. (The table must hold data, not
functions: the compiler eta-expands function-valued definitions, so a table
of closures would still recompute on every access.) -/

/-- The coordinates of `slotVertices`, computed once. -/
def slotVerticesTable : Array (Array ℚ) :=
  Array.ofFn fun i : Fin 9 => Array.ofFn fun c : Fin 3 => slotVertices i c

def slotVerticesImpl (i : Fin 9) (c : Fin 3) : ℚ :=
  (slotVerticesTable[i.val]'(by simp [slotVerticesTable]))[c.val]'(by
    simp [slotVerticesTable])

@[csimp] theorem slotVertices_eq_impl : @slotVertices = @slotVerticesImpl := by
  funext i c
  simp [slotVerticesImpl, slotVerticesTable]

/-- The three seeds: v0, v3, v6. -/
def seedVertices : Fin 3 → Fin 3 → ℚ := ![
  ![-470319/524288, 327651/1048576, 327651/1048576],
  ![21999/32768, 11947/262144, 11947/262144],
  ![-514207/1048576, -514207/1048576, -514207/1048576]
]

/-- The exact C3 rotations `c3Mat g`, over ℚ (`c3MatQ_map`). -/
def c3MatQ : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ
  | 0 => 1
  | 1 => !![0, 1, 0; 0, 0, 1; 1, 0, 0]
  | 2 => !![0, 0, 1; 1, 0, 0; 0, 1, 0]

theorem c3MatQ_map (g : Fin 3) : ((c3MatQ g).map fun x => (x : ℝ)) = c3Mat g := by
  fin_cases g <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [c3MatQ, c3Mat]

/-- The `vertexQ` index of each seed: v0, v3, v6. -/
def seedVertexQIndex : Fin 3 → Fin 7 := ![0, 3, 6]

/-- The `vertexQ` index of slot `i`: its seed moved by `c3Perm`. -/
def slotVertexQIndex (i : Fin 9) : Fin 7 :=
  c3Perm ⟨i.val / 3, by omega⟩ (seedVertexQIndex ⟨i.val % 3, by omega⟩)

/-- The C++ pipeline numbers the Septopert's 7 vertices in `vertexQ` order
(codebdd/exact5d); the model has 9 rotation-major slots. C++ vertex `n` is
read as the first slot holding it. -/
def vertexSlotTable : Array (Fin 9) :=
  ((List.range 7).map fun n =>
    ((List.finRange 9).find? fun s => (slotVertexQIndex s).val = n).getD 0).toArray

def cppVertexSlot (n : Nat) : Fin 9 := vertexSlotTable[n]?.getD 0

theorem slotVertices_sq_norm_bounds : ∀ i : Fin 9,
    (1 / 100 : ℚ) ≤ slotVertices i 0 ^ 2 + slotVertices i 1 ^ 2 + slotVertices i 2 ^ 2 ∧
      slotVertices i 0 ^ 2 + slotVertices i 1 ^ 2 + slotVertices i 2 ^ 2 ≤
        (1 - 1 / 10^12) ^ 2 := by
  decide +kernel

/-- The exact C3 action maps each seed to its slot. -/
theorem c3Mat_seedVertices (i : Fin 9) :
    (c3Mat ⟨i.val / 3, by omega⟩).toEuclideanLin (toR3 (seedVertices ⟨i.val % 3, by omega⟩)) =
      toR3 (slotVertices i) := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [c3Mat, seedVertices, slotVertices, toR3,
      Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_three]

/-- The Septopert's model for the certificate pipeline (see the module
documentation). -/
scoped instance solidModel : SolidModel where
  orbitCount := 3
  seedCount := 3
  orbitCount_pos := by norm_num
  seedCount_pos := by norm_num
  rationalVertices := slotVertices
  seedVertex := seedVertices
  symmetryMatrixErased := Erased.mk c3Mat
  symmetryMatrixQ := c3MatQ
  symmetryErrorQ := 0
  modelErrorQ := 0
  vertexSlot := cppVertexSlot
  symmetry_mem k := by rw [Erased.out_mk]; exact c3Mat_mem k
  symmetry_mul a b := by rw [Erased.out_mk]; exact c3_mul_c3 a b
  symmetry_zero := by rw [Erased.out_mk]; rfl
  symmetryQ_close k := by
    rw [Erased.out_mk, c3MatQ_map, sub_self]
    simp
  seed_close i := by
    rw [Erased.out_mk, c3Mat_seedVertices i, sub_self, norm_zero]
    norm_num
  modelErrorQ_nonneg := le_refl 0
  modelErrorQ_le := by norm_num
  rationalVertex_sq_norm_bounds := slotVertices_sq_norm_bounds

theorem symmetryMatrix_eq_c3Mat (k : OrbitIndex) : symmetryMatrix k = c3Mat k :=
  Erased.out_mk c3Mat ▸ rfl

/-- The `vertexQ` index of vertex `i`: its seed moved by `c3Perm`. -/
def vertexQIndex (i : VertexIndex) : Fin 7 := slotVertexQIndex i

theorem seedVertex_eq_vertexQ (s : SeedIndex) :
    seedVertex s = vertexQ (seedVertexQIndex s) := by
  revert s; decide +kernel

/-- The rational vertices are the Septopert's vertices (v6 three times). -/
theorem rationalVertex_eq_vertexQ (i : VertexIndex) :
    rationalVertex i = vertexQ (vertexQIndex i) := by
  revert i; decide +kernel

/-- Every vertex of the Septopert is a model vertex. -/
theorem vertexQIndex_surjective : Function.Surjective vertexQIndex := by
  intro a
  fin_cases a
  exacts [⟨0, rfl⟩, ⟨6, rfl⟩, ⟨3, rfl⟩, ⟨1, rfl⟩, ⟨7, rfl⟩, ⟨4, rfl⟩, ⟨2, rfl⟩]

/-- The rational model is exact. -/
theorem exactVertex_eq (i : VertexIndex) : exactVertex i = toR3 (rationalVertex i) := by
  simp only [exactVertex, symmetryMatrix_eq_c3Mat]
  exact c3Mat_seedVertices i

end Septopert

end
