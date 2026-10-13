module

public import Pipeline.OctaGroup
public import Pipeline.SolidModel

@[expose] public section

/-!
# Octahedral models

An octahedral solid (`OctahedralSolid`) is a solid whose 24 vertices are one
free orbit of the octahedral rotation group O (`OctaGroup`): slot `i` is
`g_i · v0` for one base point `v0`, with `g_i = slotElem[i]`, a permutation of
the 24 elements. The layout is rotation-major for C4 about z: slot `6k + s`
is `Rz(π/2)^k` applied to slot `s` (`g_{6k+s} = r^k g_s`, `r` the quarter turn
`octaRz`), so the solid is a `SolidModel` with `orbitCount = 4` and
`seedCount = 6`, whose cyclic symmetry is exact (integer matrices: no
symmetry error). The rational model is itself an exact orbit (its slots are
`g_i` applied to the rational base point; `rational_check`), so the rotated
seeds are the rational vertices exactly; `modelErrorQ = 6 · 10⁻¹⁶` is room
for the solids the certificates cover.

An `OModel` is any base point whose orbit slots lie within `modelErrorQ` of
the rational model. It is a `CyclicModel` (`OModel.toC4`), and its hull is
invariant under all 24 rotations (`OModel.octaMatrix_image_hull`). The
certificates cover every `OModel`; the true solid is one.
-/

namespace Noperts.Pipeline

open scoped Matrix

/-! ### The quarter turn about z -/

/-- The index of `Rz(π/2)` (`(x, y, z) ↦ (-y, x, z)`) in O. -/
def octaRzIdx : Nat :=
  ((List.range 24).find? fun c => octaEntries.getD c [] == [0, -1, 0, 1, 0, 0, 0, 0, 1]).getD 0

theorem octaRzIdx_lt : octaRzIdx < 24 := by decide +kernel

def octaRz : OctaIndex := ⟨octaRzIdx, octaRzIdx_lt⟩

/-- `Rz(π/2)^k`, as an element of O. -/
def octaRzPow : Nat → OctaIndex
  | 0 => 0
  | k + 1 => octaMul octaRz (octaRzPow k)

/-- The decided facts of the C4 layout and of a slot table: `slotElem` lists
the 24 elements of O, each once, rotation-major (`g_{i+6} = r g_i`), and
`Rz(π/2)^4 = 1`. -/
def octaSlotsCheck (slotElem : List Nat) : Bool :=
  slotElem.length == 24 &&
  slotElem.Nodup &&
  slotElem.all (fun g => decide (g < 24)) &&
  ((List.range 18).all fun i =>
    octaMulIdx octaRzIdx (slotElem.getD i 0) == slotElem.getD (i + 6) 0) &&
  (octaRzPow 4).val == 0

/-- A solid whose vertices are one free O-orbit, in the C4 rotation-major
layout (see the module documentation). The kernel checks `slots_check` and
`rational_check` on the solid's data. -/
class OctahedralSolid where
  /-- The rational base point (the model's slot of the identity is not
  needed: slot `i` is `g_i · base`). -/
  base : Fin 3 → ℚ
  /-- `slotElem[i]`: the element of O moving the base point to slot `i`. -/
  slotElem : List Nat
  slots_check : octaSlotsCheck slotElem = true
  /-- The rational vertex table (slot `i` = `g_i · base`, `rational_check`). -/
  rationalVertices : Fin (4 * 6) → Fin 3 → ℚ
  rational_check : ∀ i : Fin (4 * 6),
    rationalVertices i = (octaMatrixQ ⟨slotElem.getD i.val 0 % 24, Nat.mod_lt _ (by norm_num)⟩) *ᵥ base
  rationalVertex_sq_norm_bounds : ∀ i,
    (1 / 100 : ℚ) ≤ rationalVertices i 0 ^ 2 + rationalVertices i 1 ^ 2 +
        rationalVertices i 2 ^ 2 ∧
      rationalVertices i 0 ^ 2 + rationalVertices i 1 ^ 2 + rationalVertices i 2 ^ 2 ≤
        (1 - 1 / 10^12) ^ 2

section Slots

variable [O : OctahedralSolid]

/-- The element index of slot `i` (as a natural number). -/
def slotIdx (i : Nat) : Nat := O.slotElem.getD i 0

theorem octaSlots_facts :
    O.slotElem.length = 24 ∧ O.slotElem.Nodup ∧ (∀ g ∈ O.slotElem, g < 24) ∧
      (∀ i < 18, octaMulIdx octaRzIdx (slotIdx i) = slotIdx (i + 6)) ∧
      (octaRzPow 4).val = 0 := by
  have h := O.slots_check
  simp only [octaSlotsCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq, List.mem_range] at h
  obtain ⟨⟨⟨⟨hlen, hnd⟩, hlt⟩, hrot⟩, hpow⟩ := h
  exact ⟨hlen, hnd, hlt, hrot, hpow⟩

theorem slotIdx_eq_getElem {i : Nat} (hi : i < O.slotElem.length) :
    slotIdx i = O.slotElem[i] := by
  rw [slotIdx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rfl

theorem slotIdx_mem {i : Nat} (hi : i < 24) : slotIdx i ∈ O.slotElem := by
  obtain ⟨hlen, -⟩ := octaSlots_facts
  rw [slotIdx_eq_getElem (by rw [hlen]; exact hi)]
  exact List.getElem_mem _

theorem slotIdx_lt {i : Nat} (hi : i < 24) : slotIdx i < 24 :=
  octaSlots_facts.2.2.1 _ (slotIdx_mem hi)

/-- The element of O moving the base point to slot `i`. -/
def slotOcta (i : Fin (4 * 6)) : OctaIndex := ⟨slotIdx i.val, slotIdx_lt i.isLt⟩

theorem slotOcta_mod (i : Fin (4 * 6)) :
    (⟨O.slotElem.getD i.val 0 % 24, Nat.mod_lt _ (by norm_num)⟩ : OctaIndex) = slotOcta i := by
  apply Fin.ext
  show slotIdx i.val % 24 = slotIdx i.val
  exact Nat.mod_eq_of_lt (slotIdx_lt i.isLt)

theorem slotOcta_congr {a b : Fin (4 * 6)} (h : a.val = b.val) : slotOcta a = slotOcta b := by
  rw [Fin.ext h]

/-- Slot `i + 6` is the quarter turn applied to slot `i`. -/
theorem octaMatrix_slot_add_six (i : Nat) (hi : i < 18) :
    octaMatrix (slotOcta ⟨i + 6, by omega⟩) =
      octaMatrix octaRz * octaMatrix (slotOcta ⟨i, by omega⟩) := by
  rw [octaMatrix_mul]
  congr 1
  apply Fin.ext
  show slotIdx (i + 6) = octaMulIdx octaRzIdx (slotIdx i)
  exact (octaSlots_facts.2.2.2.1 i hi).symm

/-- The quarter-turn powers over ℝ. -/
noncomputable def c4Rotation (k : Fin 4) : Matrix (Fin 3) (Fin 3) ℝ := octaMatrix (octaRzPow k.val)

omit O in
theorem c4Rotation_succ (k : Nat) (hk : k + 1 < 4) :
    c4Rotation ⟨k + 1, hk⟩ = octaMatrix octaRz * c4Rotation ⟨k, by omega⟩ := by
  simp only [c4Rotation, octaRzPow, octaMatrix_mul]

/-- Slot `6k + s` is `Rz(π/2)^k` applied to slot `s`. -/
theorem c4Rotation_mul_slot (k : Fin 4) (s : Fin 6) :
    c4Rotation k * octaMatrix (slotOcta ⟨s.val, by omega⟩) =
      octaMatrix (slotOcta ⟨6 * k.val + s.val, by omega⟩) := by
  rcases k with ⟨k, hk⟩
  induction k with
  | zero =>
      simp [c4Rotation, octaRzPow, octaMatrix_zero]
  | succ k ih =>
      rw [c4Rotation_succ k hk, Matrix.mul_assoc, ih (by omega)]
      have h := octaMatrix_slot_add_six (6 * k + s.val) (by omega)
      rw [slotOcta_congr (b := ⟨6 * (k + 1) + s.val, by omega⟩) (by simp only; ring)] at h
      exact h.symm

/-- Every element of O is the element of some slot. -/
theorem exists_slotOcta (g : OctaIndex) : ∃ i : Fin (4 * 6), slotOcta i = g := by
  obtain ⟨hlen, hnd, hlt, -, -⟩ := octaSlots_facts
  have hsub' : O.slotElem.toFinset ⊆ Finset.range 24 := by
    intro x hx
    simpa using hlt x (List.mem_toFinset.mp hx)
  have hcard : O.slotElem.toFinset.card = 24 := by
    rw [List.toFinset_card_of_nodup hnd, hlen]
  have heq := Finset.eq_of_subset_of_card_le hsub' (by simp [hcard])
  have hg : g.val ∈ O.slotElem := by
    rw [← List.mem_toFinset, heq]
    exact Finset.mem_range.mpr g.isLt
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hg
  refine ⟨⟨i, by rw [hlen] at hi; exact hi⟩, Fin.ext ?_⟩
  show slotIdx i = g.val
  rw [slotIdx_eq_getElem hi, hget]

end Slots

/-! ### The solid model -/

theorem octaRzPow_add (a b : Fin 4) :
    octaMul (octaRzPow a.val) (octaRzPow b.val) = octaRzPow (a + b).val := by
  revert a b
  decide +kernel

theorem c4Rotation_mul (a b : Fin 4) : c4Rotation a * c4Rotation b = c4Rotation (a + b) := by
  rw [c4Rotation, c4Rotation, octaMatrix_mul, octaRzPow_add, c4Rotation]

theorem toR3_mulVec_map (M : Matrix (Fin 3) (Fin 3) ℚ) (v : Fin 3 → ℚ) :
    toR3 (M *ᵥ v) = (M.map fun x => (x : ℝ)).toEuclideanLin (toR3 v) := by
  ext i
  simp [toR3, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

section Model

variable [O : OctahedralSolid]

/-- Rational slot `i` is the exact element of slot `i` applied to the base. -/
theorem toR3_rationalVertices (i : Fin (4 * 6)) :
    toR3 (O.rationalVertices i) = (octaMatrix (slotOcta i)).toEuclideanLin (toR3 O.base) := by
  rw [O.rational_check i, slotOcta_mod, toR3_mulVec_map, octaMatrixQ_map]

omit O in
theorem toEuclideanLin_mul' (A B : Matrix (Fin 3) (Fin 3) ℝ) (v : ℝ³) :
    (A * B).toEuclideanLin v = A.toEuclideanLin (B.toEuclideanLin v) := by
  simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

/-- The rotated rational seeds are the rational vertices. -/
theorem c4_seed_eq (i : Fin (4 * 6)) :
    (c4Rotation ⟨i.val / 6, by omega⟩).toEuclideanLin (toR3 (O.rationalVertices ⟨i.val % 6, by omega⟩)) =
      toR3 (O.rationalVertices i) := by
  rw [toR3_rationalVertices, toR3_rationalVertices, ← toEuclideanLin_mul']
  have h := c4Rotation_mul_slot ⟨i.val / 6, by omega⟩ ⟨i.val % 6, by omega⟩
  have hi : (⟨6 * (i.val / 6) + i.val % 6, by omega⟩ : Fin (4 * 6)) = i := by
    apply Fin.ext; simp only; omega
  simp only at h
  rw [h, hi]

end Model

/-- The solid model of an octahedral solid: C4 about z (exact), model error
`6 · 10⁻¹⁶`; C++ vertex `n` is slot `n`. (Reducible, so that compiled code
specializes it to the solid's data.) -/
@[reducible] instance OctahedralSolid.toSolidModel [O : OctahedralSolid] : SolidModel where
  orbitCount := 4
  seedCount := 6
  orbitCount_pos := by norm_num
  seedCount_pos := by norm_num
  rationalVertices := O.rationalVertices
  seedVertex s := O.rationalVertices ⟨s.val, by omega⟩
  symmetryMatrixErased := Erased.mk c4Rotation
  symmetryMatrixQ k := octaMatrixQ (octaRzPow k.val)
  symmetryErrorQ := 0
  modelErrorQ := 6 / 10^16
  vertexSlot n := ⟨n % 24, Nat.mod_lt _ (by norm_num)⟩
  symmetry_mem k := by rw [Erased.out_mk]; exact octaMatrix_mem_SO3 _
  symmetry_mul a b := by rw [Erased.out_mk]; exact c4Rotation_mul a b
  symmetry_zero := by rw [Erased.out_mk]; exact octaMatrix_zero
  symmetryQ_close k := by
    rw [Erased.out_mk, c4Rotation, octaMatrixQ_map, sub_self]
    simp
  seed_close i := by
    rw [Erased.out_mk]
    have h := c4_seed_eq i
    simp only at h ⊢
    rw [h, sub_self, norm_zero]
    norm_num
  modelErrorQ_nonneg := by norm_num
  modelErrorQ_le := by norm_num
  rationalVertex_sq_norm_bounds := O.rationalVertex_sq_norm_bounds

variable [OctahedralSolid]

@[simp] theorem orbitCount_eq_four : SolidModel.orbitCount = 4 := rfl
@[simp] theorem seedCount_eq_six : SolidModel.seedCount = 6 := rfl

theorem symmetryMatrix_eq_c4Rotation (k : OrbitIndex) : symmetryMatrix k = c4Rotation k :=
  congrFun (Erased.out_mk c4Rotation) k

/-! ### Models -/

/-- A base point whose orbit slots are within `modelErrorQ` of the rational
model. -/
structure OModel where
  v0 : ℝ³
  close : ∀ i : VertexIndex,
    ‖(octaMatrix (slotOcta i)).toEuclideanLin v0 - toR3 (rationalVertex i)‖ ≤ (modelErrorQ : ℝ)

namespace OModel

variable (P : OModel)

/-- Slot `i`: `g_i · v0`. -/
noncomputable def orbit (i : VertexIndex) : ℝ³ := (octaMatrix (slotOcta i)).toEuclideanLin P.v0

omit [OctahedralSolid] in
/-- Vertex `i` of the C4 layout: `Rz(π/2)^(orbitIndex i)` times the element of
its seed slot is the element of slot `i`. -/
theorem _root_.Noperts.Pipeline.c4Rotation_mul_seedSlot [OctahedralSolid] (i : VertexIndex) :
    c4Rotation (orbitIndex i) * octaMatrix (slotOcta ⟨(seedIndex i).val, by
      have := (seedIndex i).isLt; simp at this ⊢; omega⟩) = octaMatrix (slotOcta i) := by
  rw [c4Rotation_mul_slot (orbitIndex i) (seedIndex i)]
  congr 2
  apply Fin.ext
  simp only [orbitIndex, seedIndex, seedCount_eq_six]
  omega

/-- The C4 model with seeds `orbit s`. -/
noncomputable def toC4 : CyclicModel where
  seed s := P.orbit ⟨s.val, by have := s.isLt; simp at this ⊢; omega⟩
  close i := by
    rw [symmetryMatrix_eq_c4Rotation, orbit, ← toEuclideanLin_mul', c4Rotation_mul_seedSlot]
    exact P.close i

theorem toC4_vertex (i : VertexIndex) : P.toC4.vertex i = P.orbit i := by
  simp only [CyclicModel.vertex, toC4, symmetryMatrix_eq_c4Rotation, orbit, ← toEuclideanLin_mul',
    c4Rotation_mul_seedSlot]

/-- A rotation of O moves each vertex to a vertex. -/
theorem exists_octa_vertex (g : OctaIndex) (i : VertexIndex) :
    ∃ j : VertexIndex, (octaMatrix g).toEuclideanLin (P.toC4.vertex i) = P.toC4.vertex j := by
  obtain ⟨j, hj⟩ := exists_slotOcta (octaMul g (slotOcta i))
  refine ⟨j, ?_⟩
  rw [toC4_vertex, toC4_vertex, orbit, orbit, ← toEuclideanLin_mul', octaMatrix_mul]
  have hj' : slotOcta j = octaMul g (slotOcta i) := hj
  rw [hj']

/-- Every rotation of O maps the vertex set onto itself. -/
theorem octaMatrix_image_verts (g : OctaIndex) :
    (octaMatrix g).toEuclideanLin '' (P.toC4.verts : Set ℝ³) = P.toC4.verts := by
  ext x
  simp only [CyclicModel.verts, Finset.coe_image, Finset.coe_univ, Set.image_univ,
    Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    obtain ⟨j, hj⟩ := P.exists_octa_vertex g i
    exact ⟨j, hj.symm⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨i, hi⟩ := P.exists_octa_vertex (octaInv g) j
    refine ⟨P.toC4.vertex i, ⟨i, rfl⟩, ?_⟩
    rw [← hi, ← toEuclideanLin_mul', ← octaMatrix_transpose]
    have horth : octaMatrix g * (octaMatrix g)ᵀ = 1 :=
      mul_eq_one_comm.mp (octaMatrix_transpose_mul g)
    rw [horth]
    simp

theorem octaMatrix_image_hull (g : OctaIndex) :
    (octaMatrix g).toEuclideanLin '' P.toC4.polyhedron.hull = P.toC4.polyhedron.hull := by
  rw [P.toC4.polyhedron_hull, LinearMap.image_convexHull, P.octaMatrix_image_verts g]

end OModel

end Noperts.Pipeline

end
