module

public import Basic

@[expose] public section

/-!
# The octahedral rotation group O

The 24 rotations of the cube: the signed permutation matrices with
determinant 1. `octaEntries` lists them (row-major integer entries) in the
order of the C++ search's table (`search/sc/sc_model.cc`): permutations in
lexicographic order of their images of (0, 1, 2), and for each the sign
patterns `s = 0, …, 7` (bit `r`: row `r` negated) with determinant 1. Element
0 is the identity.

The group facts are decided by kernel computation on the integer entries
(`octaCheck`): the products (`octaMul`) and inverses (`octaInv`) stay in the
list, every element is orthogonal with determinant 1, and the list has no
repetitions. `octaMatrix g` is the real matrix.
-/

namespace Noperts.Pipeline

open scoped Matrix

abbrev OctaIndex := Fin 24

/-- The six permutations of three coordinates (the images of 0, 1, 2) and
their signs. -/
def octaPerms : List (List Nat) :=
  [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]]

def octaPermSigns : List Int := [1, -1, -1, 1, 1, -1]

/-- The sign of row `r` in sign pattern `s`. -/
def octaSignOf (s r : Nat) : Int := if (s / 2 ^ r) % 2 = 1 then -1 else 1

/-- Row-major entries of the signed permutation matrix whose row `r` has
`octaSignOf s r` in column `perm r`. -/
def signedPermEntries (p s : Nat) : List Int :=
  (List.range 9).map fun n =>
    if (octaPerms.getD p []).getD (n / 3) 0 = n % 3 then octaSignOf s (n / 3) else 0

/-- The 24 rotations, row-major. -/
def octaEntries : List (List Int) :=
  (List.range 6).flatMap fun p => (List.range 8).filterMap fun s =>
    if octaPermSigns.getD p 0 * octaSignOf s 0 * octaSignOf s 1 * octaSignOf s 2 = 1 then
      some (signedPermEntries p s)
    else none

/-- Entry `n` (row-major) of element `g`. -/
def octaEntry (g n : Nat) : Int := (octaEntries.getD g []).getD n 0

/-- The entries of the product of elements `a` and `b`. -/
def octaMulEntries (a b : Nat) : List Int :=
  (List.range 9).map fun n =>
    octaEntry a (3 * (n / 3)) * octaEntry b (n % 3) +
      octaEntry a (3 * (n / 3) + 1) * octaEntry b (3 + n % 3) +
      octaEntry a (3 * (n / 3) + 2) * octaEntry b (6 + n % 3)

/-- The entries of the transpose of element `g`. -/
def octaTransposeEntries (g : Nat) : List Int :=
  (List.range 9).map fun n => octaEntry g (3 * (n % 3) + n / 3)

/-- The index of the product (found in the list). -/
def octaMulIdx (a b : Nat) : Nat :=
  ((List.range 24).find? fun c => octaMulEntries a b == octaEntries.getD c []).getD 0

/-- The index of the inverse (the transpose, found in the list). -/
def octaInvIdx (g : Nat) : Nat :=
  ((List.range 24).find? fun c => octaTransposeEntries g == octaEntries.getD c []).getD 0

/-- The determinant of element `g`. -/
def octaDet (g : Nat) : Int :=
  let e := octaEntry g
  e 0 * (e 4 * e 8 - e 5 * e 7) - e 1 * (e 3 * e 8 - e 5 * e 6) + e 2 * (e 3 * e 7 - e 4 * e 6)

/-- The decided group facts. -/
def octaCheck : Bool :=
  octaEntries.length == 24 &&
  octaEntries.Nodup &&
  octaEntries.getD 0 [] == [1, 0, 0, 0, 1, 0, 0, 0, 1] &&
  (List.range 24).all fun g =>
    (octaEntries.getD g []).length == 9 &&
    octaDet g == 1 &&
    octaMulEntries (octaInvIdx g) g == [1, 0, 0, 0, 1, 0, 0, 0, 1] &&
    decide (octaInvIdx g < 24) && octaTransposeEntries g == octaEntries.getD (octaInvIdx g) [] &&
    (List.range 24).all fun h =>
      decide (octaMulIdx g h < 24) && octaMulEntries g h == octaEntries.getD (octaMulIdx g h) []

theorem octaCheck_eq : octaCheck = true := by decide +kernel

/-- The rotation `g` of O over ℝ. -/
noncomputable def octaMatrix (g : OctaIndex) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => (octaEntry g.val (3 * i.val + j.val) : ℝ)

/-- The rotation `g` of O over ℚ (computable). -/
def octaMatrixQ (g : OctaIndex) : Matrix (Fin 3) (Fin 3) ℚ :=
  Matrix.of fun i j => (octaEntry g.val (3 * i.val + j.val) : ℚ)

theorem octaMatrixQ_map (g : OctaIndex) :
    (octaMatrixQ g).map (fun x => (x : ℝ)) = octaMatrix g := by
  ext i j
  simp [octaMatrixQ, octaMatrix]

def octaMul (a b : OctaIndex) : OctaIndex :=
  ⟨octaMulIdx a.val b.val, by
    have h := octaCheck_eq
    simp only [octaCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range,
      decide_eq_true_eq, beq_iff_eq] at h
    exact (h.2 a.val a.isLt).2 b.val b.isLt |>.1⟩

def octaInv (g : OctaIndex) : OctaIndex :=
  ⟨octaInvIdx g.val, by
    have h := octaCheck_eq
    simp only [octaCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range,
      decide_eq_true_eq, beq_iff_eq] at h
    exact (h.2 g.val g.isLt).1.1.2⟩

/-- The facts of `octaCheck` for one element. -/
private theorem octaCheck_at (g : OctaIndex) :
    (octaEntries.getD g.val []).length = 9 ∧ octaDet g.val = 1 ∧
    octaMulEntries (octaInvIdx g.val) g.val = [1, 0, 0, 0, 1, 0, 0, 0, 1] ∧
    octaTransposeEntries g.val = octaEntries.getD (octaInvIdx g.val) [] ∧
    ∀ h : OctaIndex, octaMulEntries g.val h.val = octaEntries.getD (octaMulIdx g.val h.val) [] := by
  have h := octaCheck_eq
  simp only [octaCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hlen, hdet⟩, hinv⟩, -⟩, htr⟩, hmul⟩ := h.2 g.val g.isLt
  exact ⟨hlen, hdet, hinv, htr, fun k => (hmul k.val k.isLt).2⟩

/-- Entry `3 i + j` of a list of nine entries, read through `List.getD`. -/
private theorem entry_of_list_eq {l m : List Int} (h : l = m) (n : Nat) :
    l.getD n 0 = m.getD n 0 := by rw [h]

theorem octaMatrix_mul (a b : OctaIndex) :
    octaMatrix a * octaMatrix b = octaMatrix (octaMul a b) := by
  have hm := (octaCheck_at a).2.2.2.2 b
  ext i j
  have he := entry_of_list_eq hm (3 * i.val + j.val)
  simp only [octaMulEntries] at he
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)] at he
  simp only [Option.map_some, Option.getD_some] at he
  have h3 : (3 * i.val + j.val) / 3 = i.val := by omega
  have h3' : (3 * i.val + j.val) % 3 = j.val := by omega
  rw [h3, h3'] at he
  simp only [Matrix.mul_apply, Fin.sum_univ_three, octaMatrix, Matrix.of_apply, octaMul,
    octaEntry]
  simp only [octaEntry] at he
  have hcast := congrArg (fun z : ℤ => (z : ℝ)) he
  push_cast at hcast
  fin_cases i <;> fin_cases j <;> simp at hcast ⊢ <;> linarith

theorem octaMatrix_transpose (g : OctaIndex) :
    (octaMatrix g)ᵀ = octaMatrix (octaInv g) := by
  have ht := (octaCheck_at g).2.2.2.1
  ext i j
  have he := entry_of_list_eq ht (3 * i.val + j.val)
  simp only [octaTransposeEntries] at he
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)] at he
  simp only [Option.map_some, Option.getD_some] at he
  have h3 : (3 * i.val + j.val) / 3 = i.val := by omega
  have h3' : (3 * i.val + j.val) % 3 = j.val := by omega
  rw [h3, h3'] at he
  simp only [Matrix.transpose_apply, octaMatrix, Matrix.of_apply, octaInv, octaEntry]
  simp only [octaEntry] at he
  rw [← he]

theorem octaMatrix_zero : octaMatrix 0 = 1 := by
  have h := octaCheck_eq
  simp only [octaCheck, Bool.and_eq_true, beq_iff_eq] at h
  have h0 := h.1.2
  ext i j
  have he := entry_of_list_eq h0 (3 * i.val + j.val)
  simp only [octaMatrix, Matrix.of_apply, octaEntry, Fin.val_zero]
  rw [he]
  fin_cases i <;> fin_cases j <;> simp

theorem octaMatrix_inv_mul (g : OctaIndex) : octaMatrix (octaInv g) * octaMatrix g = 1 := by
  rw [octaMatrix_mul]
  have hi := (octaCheck_at g).2.2.1
  have hm := (octaCheck_at (octaInv g)).2.2.2.2 g
  have hid : octaEntries.getD (octaMul (octaInv g) g).val [] = [1, 0, 0, 0, 1, 0, 0, 0, 1] := by
    simp only [octaMul, octaInv] at hm ⊢
    rw [← hm]
    exact hi
  ext i j
  have he := entry_of_list_eq hid (3 * i.val + j.val)
  simp only [octaMatrix, Matrix.of_apply, octaEntry]
  rw [he]
  fin_cases i <;> fin_cases j <;> simp

theorem octaMatrix_transpose_mul (g : OctaIndex) : (octaMatrix g)ᵀ * octaMatrix g = 1 := by
  rw [octaMatrix_transpose, octaMatrix_inv_mul]

theorem octaMatrix_det (g : OctaIndex) : (octaMatrix g).det = 1 := by
  have hd := (octaCheck_at g).2.1
  rw [Matrix.det_fin_three]
  simp only [octaMatrix, Matrix.of_apply, octaDet, octaEntry] at hd ⊢
  have hcast := congrArg (fun z : ℤ => (z : ℝ)) hd
  push_cast at hcast
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Fin.isValue] at hcast ⊢
  norm_num at hcast ⊢
  linarith

theorem octaMatrix_mem_SO3 (g : OctaIndex) :
    octaMatrix g ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff']
  exact ⟨octaMatrix_transpose_mul g, octaMatrix_det g⟩

theorem exists_octaMatrix_mul (g h : OctaIndex) :
    ∃ k : OctaIndex, octaMatrix g * octaMatrix h = octaMatrix k :=
  ⟨octaMul g h, octaMatrix_mul g h⟩

end Noperts.Pipeline

end
