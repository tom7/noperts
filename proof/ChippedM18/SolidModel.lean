module

public import Pipeline.SolidModel
public import ChippedM18.C3
public import ChippedM18.ModelData

@[expose] public section

/-!
# The ChippedM18 as a solid model for the certificate pipeline

The ChippedM18 (data in `ChippedM18.ModelData`) is the SeptopertM18 with its three
vertices (-18,9,9)/32 (and C3 images) cut off by the planes (-1,5,5).x = 209/64
(and C3 images): 19 vertices, C3v, with six acute dihedral edges of 81.95 degrees.
It is symmetric under C3v with the 3-fold axis along (1,1,1), so the C3
rotations are the cyclic coordinate permutations `c3Mat k`, exact rational
matrices. The model layout (`Pipeline.SolidModel`) is rotation-major: seven
seeds, the `vertexQ` indices 0 to 6, and slot `7k + s` is seed `s` rotated by
`c3Mat k`. The axis vertex v5 is fixed by C3, so it fills three slots (5, 12,
19); the other 18 vertices of the ChippedM18 fill one slot each
(`rationalVertex_eq_vertexQ`).

The model is exact: the rational slots are the rotated seeds
(`exactVertex_eq`), the rational symmetry matrices are the exact ones, and
both error terms are 0 (the C++ checker's `MODEL_EXACT`: zero support error,
so exact support ties are allowed).

`solidModel` is a scoped instance: it is in effect inside `namespace
ChippedM18` (and wherever `ChippedM18` is opened), and nowhere else.
-/

namespace ChippedM18

open Noperts Noperts.Pipeline
open scoped Matrix

/-- The 21 model slots (rotation-major: slot `7k + s` is seed `s` rotated by
`c3Mat k`). -/
def slotVertices : Fin 21 → Fin 3 → ℚ := ![
  ![-107/192, 13/48, 13/48],
  ![-209/384, 101/384, 9/32],
  ![-209/384, 9/32, 101/384],
  ![-249/704, 39/176, 127/352],
  ![-249/704, 127/352, 39/176],
  ![-9/32, -9/32, -9/32],
  ![3/32, 3/32, 17/32],
  ![13/48, 13/48, -107/192],
  ![101/384, 9/32, -209/384],
  ![9/32, 101/384, -209/384],
  ![39/176, 127/352, -249/704],
  ![127/352, 39/176, -249/704],
  ![-9/32, -9/32, -9/32],
  ![3/32, 17/32, 3/32],
  ![13/48, -107/192, 13/48],
  ![9/32, -209/384, 101/384],
  ![101/384, -209/384, 9/32],
  ![127/352, -249/704, 39/176],
  ![39/176, -249/704, 127/352],
  ![-9/32, -9/32, -9/32],
  ![17/32, 3/32, 3/32]
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
  Array.ofFn fun i : Fin 21 => Array.ofFn fun c : Fin 3 => slotVertices i c

def slotVerticesImpl (i : Fin 21) (c : Fin 3) : ℚ :=
  (slotVerticesTable[i.val]'(by simp [slotVerticesTable]))[c.val]'(by
    simp [slotVerticesTable])

@[csimp] theorem slotVertices_eq_impl : @slotVertices = @slotVerticesImpl := by
  funext i c
  simp [slotVerticesImpl, slotVerticesTable]

/-- The seven seeds: the `vertexQ` vertices 0 to 6. -/
def seedVertices : Fin 7 → Fin 3 → ℚ := ![
  ![-107/192, 13/48, 13/48],
  ![-209/384, 101/384, 9/32],
  ![-209/384, 9/32, 101/384],
  ![-249/704, 39/176, 127/352],
  ![-249/704, 127/352, 39/176],
  ![-9/32, -9/32, -9/32],
  ![3/32, 3/32, 17/32]
]

/-- The exact C3 rotations `c3Mat g`, over ℚ (`c3MatQ_map`). -/
def c3MatQ : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ
  | 0 => 1
  | 1 => !![0, 1, 0; 0, 0, 1; 1, 0, 0]
  | 2 => !![0, 0, 1; 1, 0, 0; 0, 1, 0]

theorem c3MatQ_map (g : Fin 3) : ((c3MatQ g).map fun x => (x : ℝ)) = c3Mat g := by
  fin_cases g <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [c3MatQ, c3Mat]

/-- The `vertexQ` index of each seed. -/
def seedVertexQIndex : Fin 7 → Fin 19 := ![0, 1, 2, 3, 4, 5, 6]

/-- The `vertexQ` index of slot `i`: its seed moved by `c3Perm`. -/
def slotVertexQIndex (i : Fin 21) : Fin 19 :=
  c3Perm ⟨i.val / 7, by omega⟩ (seedVertexQIndex ⟨i.val % 7, by omega⟩)

/-- The C++ pipeline numbers the ChippedM18's 19 vertices in `vertexQ` order
(codebdd/exact5d); the model has 21 rotation-major slots. C++ vertex `n` is
read as the first slot holding it. -/
def vertexSlotTable : Array (Fin 21) :=
  ((List.range 19).map fun n =>
    ((List.finRange 21).find? fun s => (slotVertexQIndex s).val = n).getD 0).toArray

def cppVertexSlot (n : Nat) : Fin 21 := vertexSlotTable[n]?.getD 0

theorem slotVertices_sq_norm_bounds : ∀ i : Fin 21,
    (1 / 100 : ℚ) ≤ slotVertices i 0 ^ 2 + slotVertices i 1 ^ 2 + slotVertices i 2 ^ 2 ∧
      slotVertices i 0 ^ 2 + slotVertices i 1 ^ 2 + slotVertices i 2 ^ 2 ≤
        (1 - 1 / 10^12) ^ 2 := by
  decide +kernel

/-- The exact C3 action maps each seed to its slot. -/
theorem c3Mat_seedVertices (i : Fin 21) :
    (c3Mat ⟨i.val / 7, by omega⟩).toEuclideanLin (toR3 (seedVertices ⟨i.val % 7, by omega⟩)) =
      toR3 (slotVertices i) := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [c3Mat, seedVertices, slotVertices, toR3,
      Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_three]

/-- The ChippedM18's model for the certificate pipeline (see the module
documentation). -/
scoped instance solidModel : SolidModel where
  orbitCount := 3
  seedCount := 7
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
def vertexQIndex (i : VertexIndex) : Fin 19 := slotVertexQIndex i

theorem seedVertex_eq_vertexQ (s : SeedIndex) :
    seedVertex s = vertexQ (seedVertexQIndex s) := by
  revert s; decide +kernel

/-- The rational vertices are the ChippedM18's vertices (v5 three times). -/
theorem rationalVertex_eq_vertexQ (i : VertexIndex) :
    rationalVertex i = vertexQ (vertexQIndex i) := by
  revert i; decide +kernel

/-- Every vertex of the ChippedM18 is a model vertex. -/
theorem vertexQIndex_surjective : Function.Surjective vertexQIndex := by
  intro a
  revert a; decide +kernel

/-- The rational model is exact. -/
theorem exactVertex_eq (i : VertexIndex) : exactVertex i = toR3 (rationalVertex i) := by
  simp only [exactVertex, symmetryMatrix_eq_c3Mat]
  exact c3Mat_seedVertices i

end ChippedM18

end
