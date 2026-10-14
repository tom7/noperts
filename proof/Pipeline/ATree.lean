module

public import Pipeline.KCapTree

@[expose] public section

/-!
# Split trees with affine changes of coordinates

A `KTree` splits its root box along the coordinate axes. Where a feature of
the certified function (a line where the best witness changes) is slanted,
axis-aligned splits approximate it by a staircase of many small boxes; a
change of coordinates aligned with the feature needs a few. An `ATree` adds
such nodes: `affine m box t` re-parametrizes the region by y = A z + c
(`AffMap`; y the original chart variables) over a new box in z, and its
subtree is checked over that box with the chart polynomials composed with
the map.

Every map is to the original variables (never relative to the parent's), so
the numbers stay as short as the maps' entries however deep the tree goes.
A node only has to cover its parent's region: `coverOk` checks, by exact
interval arithmetic of the affine map z ↦ B'(A z + c − c') on the parent's
box, that the parent's region lies in the image of the new box (with
A' B' = 1). The maps fix variable 0 (the blow-up variable μ), so the
leaves' division by it stays valid.

`ATree.check_sound` is generic in the leaf test and in how a map's chart is
built: if every checked leaf is good at the image of its box, every point
of the root box is good.
-/

namespace Noperts.Pipeline

namespace KCap

open scoped BigOperators

/-- An affine change of the chart variables y = A z + c, with B = A⁻¹ (checked by `ok`); it
fixes variable 0. -/
structure AffMap where
  A : Fin 5 → Fin 5 → ℚ
  c : Fin 5 → ℚ
  B : Fin 5 → Fin 5 → ℚ
deriving DecidableEq

def AffMap.idm : AffMap := ⟨fun i j => if i = j then 1 else 0, fun _ => 0, fun i j => if i = j then 1 else 0⟩

/-- A B = 1, and the map fixes variable 0 (A's row and column 0 are e₀, c 0 = 0). -/
def AffMap.ok (m : AffMap) : Bool :=
  decide ((∀ i j, (∑ k, m.A i k * m.B k j) = if i = j then 1 else 0) ∧
    (∀ j, m.A 0 j = if j = 0 then 1 else 0) ∧ (∀ i, m.A i 0 = if i = 0 then 1 else 0) ∧ m.c 0 = 0)

noncomputable def AffMap.apply (m : AffMap) (z : Fin 5 → ℝ) : Fin 5 → ℝ :=
  fun i => (∑ j, (m.A i j : ℝ) * z j) + m.c i

noncomputable def AffMap.inv (m : AffMap) (y : Fin 5 → ℝ) : Fin 5 → ℝ :=
  fun i => ∑ j, (m.B i j : ℝ) * (y j - m.c j)

theorem AffMap.ok_spec {m : AffMap} (h : m.ok = true) :
    (∀ i j, (∑ k, m.A i k * m.B k j) = if i = j then 1 else 0) ∧
      (∀ j, m.A 0 j = if j = 0 then 1 else 0) ∧ (∀ i, m.A i 0 = if i = 0 then 1 else 0) ∧ m.c 0 = 0 := by
  simpa [AffMap.ok] using h

theorem AffMap.apply_inv {m : AffMap} (h : m.ok = true) (y : Fin 5 → ℝ) : m.apply (m.inv y) = y := by
  obtain ⟨hAB, -, -, -⟩ := AffMap.ok_spec h
  funext i
  have hAB' : ∀ k, (∑ j, (m.A i j : ℝ) * m.B j k) = if i = k then 1 else 0 := by
    intro k
    have := hAB i k
    have h2 : ((∑ j, m.A i j * m.B j k : ℚ) : ℝ) = ((if i = k then 1 else 0 : ℚ) : ℝ) := by rw [this]
    simp only [Rat.cast_sum, Rat.cast_mul, apply_ite (fun q : ℚ => (q : ℝ)), Rat.cast_one, Rat.cast_zero] at h2
    exact h2
  simp only [AffMap.apply, AffMap.inv]
  calc (∑ j, (m.A i j : ℝ) * ∑ k, (m.B j k : ℝ) * (y k - m.c k)) + m.c i
      = (∑ k, (∑ j, (m.A i j : ℝ) * m.B j k) * (y k - m.c k)) + m.c i := by
        congr 1
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro j _; ring
    _ = y i := by
        simp only [hAB', ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        ring

theorem AffMap.apply_zero {m : AffMap} (h : m.ok = true) (z : Fin 5 → ℝ) : m.apply z 0 = z 0 := by
  obtain ⟨-, hA0, -, hc0⟩ := AffMap.ok_spec h
  simp only [AffMap.apply, hA0, hc0]
  simp [apply_ite (fun q : ℚ => (q : ℝ)), Finset.sum_ite_eq']

theorem AffMap.idm_apply (z : Fin 5 → ℝ) : AffMap.idm.apply z = z := by
  funext i
  simp [AffMap.apply, AffMap.idm, apply_ite (fun q : ℚ => (q : ℝ)), Finset.sum_ite_eq]

/-! ### Covering -/

/-- The image of the box (lower end, width) under z ↦ m'.inv (m.apply z), coordinate i, as exact
lower and upper bounds: the affine map is z ↦ M z + d with M = B' A, d = B' (c − c'). -/
def coverM (m m' : AffMap) (i j : Fin 5) : ℚ := ∑ k, m'.B i k * m.A k j
def coverD (m m' : AffMap) (i : Fin 5) : ℚ := ∑ k, m'.B i k * (m.c k - m'.c k)

def coverLo (m m' : AffMap) (box : Box) (i : Fin 5) : ℚ :=
  coverD m m' i + ∑ j, (if 0 ≤ coverM m m' i j then coverM m m' i j * (box j).1
    else coverM m m' i j * ((box j).1 + (box j).2))

def coverHi (m m' : AffMap) (box : Box) (i : Fin 5) : ℚ :=
  coverD m m' i + ∑ j, (if 0 ≤ coverM m m' i j then coverM m m' i j * ((box j).1 + (box j).2)
    else coverM m m' i j * (box j).1)

/-- The parent's region (box under m) lies in the image of box' under m'. -/
def coverOk (m m' : AffMap) (box box' : Box) : Bool :=
  decide (∀ i, (box' i).1 ≤ coverLo m m' box i ∧ coverHi m m' box i ≤ (box' i).1 + (box' i).2)

theorem inv_apply_eq (m m' : AffMap) (z : Fin 5 → ℝ) (i : Fin 5) :
    m'.inv (m.apply z) i = (∑ j, (coverM m m' i j : ℝ) * z j) + coverD m m' i := by
  simp only [AffMap.inv, AffMap.apply, coverM, coverD]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]
  have : ∀ k, (m'.B i k : ℝ) * ((∑ j, (m.A k j : ℝ) * z j) + m.c k - m'.c k) =
      (∑ j, (m'.B i k : ℝ) * m.A k j * z j) + m'.B i k * (m.c k - m'.c k) := by
    intro k
    rw [show (∑ j, (m.A k j : ℝ) * z j) + m.c k - m'.c k = (∑ j, (m.A k j : ℝ) * z j) + (m.c k - m'.c k) by ring,
      mul_add, Finset.mul_sum]
    simp only [mul_assoc]
  simp only [this, Finset.sum_add_distrib]
  rw [Finset.sum_comm]

theorem term_lower (M lo w z : ℝ) (hz : lo ≤ z ∧ z ≤ lo + w) :
    (if 0 ≤ M then M * lo else M * (lo + w)) ≤ M * z := by
  split_ifs with h
  · exact mul_le_mul_of_nonneg_left hz.1 h
  · exact mul_le_mul_of_nonpos_left hz.2 (le_of_lt (not_le.mp h))

theorem term_upper (M lo w z : ℝ) (hz : lo ≤ z ∧ z ≤ lo + w) :
    M * z ≤ (if 0 ≤ M then M * (lo + w) else M * lo) := by
  split_ifs with h
  · exact mul_le_mul_of_nonneg_left hz.2 h
  · exact mul_le_mul_of_nonpos_left hz.1 (le_of_lt (not_le.mp h))

theorem coverOk_sound {m m' : AffMap} {box box' : Box} (h : coverOk m m' box box' = true)
    {z : Fin 5 → ℝ} (hz : KPoly.InBox box z) : KPoly.InBox box' (m'.inv (m.apply z)) := by
  simp only [coverOk, decide_eq_true_eq] at h
  intro i
  obtain ⟨hlo, hhi⟩ := h i
  rw [inv_apply_eq]
  have hL : ((coverLo m m' box i : ℚ) : ℝ) ≤ (∑ j, (coverM m m' i j : ℝ) * z j) + coverD m m' i := by
    simp only [coverLo, Rat.cast_add, Rat.cast_sum]
    rw [add_comm]
    apply add_le_add (Finset.sum_le_sum ?_) le_rfl
    intro j _
    by_cases hM : 0 ≤ coverM m m' i j
    · rw [if_pos hM, Rat.cast_mul]
      exact mul_le_mul_of_nonneg_left (hz j).1 (by exact_mod_cast hM)
    · rw [if_neg hM, Rat.cast_mul]
      have : ((coverM m m' i j : ℚ) : ℝ) ≤ 0 := by exact_mod_cast le_of_lt (not_le.mp hM)
      push_cast
      exact mul_le_mul_of_nonpos_left (hz j).2 this
  have hH : (∑ j, (coverM m m' i j : ℝ) * z j) + coverD m m' i ≤ ((coverHi m m' box i : ℚ) : ℝ) := by
    simp only [coverHi, Rat.cast_add, Rat.cast_sum]
    rw [add_comm (((coverD m m' i : ℚ)) : ℝ)]
    apply add_le_add (Finset.sum_le_sum ?_) le_rfl
    intro j _
    by_cases hM : 0 ≤ coverM m m' i j
    · rw [if_pos hM, Rat.cast_mul]
      push_cast
      exact mul_le_mul_of_nonneg_left (hz j).2 (by exact_mod_cast hM)
    · rw [if_neg hM, Rat.cast_mul]
      have : ((coverM m m' i j : ℚ) : ℝ) ≤ 0 := by exact_mod_cast le_of_lt (not_le.mp hM)
      exact mul_le_mul_of_nonpos_left (hz j).1 this
  constructor
  · exact le_trans (by exact_mod_cast hlo) hL
  · exact le_trans hH (by exact_mod_cast hhi)

/-! ### Trees -/

inductive ATree where
  | split (axis : Fin 5) (l r : ATree)
  | leaf (w : Leaf)
  | affine (m : AffMap) (box : Box) (t : ATree)
  | fail
deriving Inhabited, DecidableEq

variable {K : Type} [ExactScalarOps K]

def boxWidthsOk (box : Box) : Bool := decide (∀ i, 0 ≤ (box i).2)

/-- The tree check: `leafOk cd l box` tests a leaf with the current chart data, and an affine
node switches to `chartOf m'`. -/
def ATree.check (leafOk : ChartData K → Leaf → Box → Bool) (chartOf : AffMap → ChartData K) :
    ChartData K → AffMap → ATree → Box → Bool
  | cd, m, .split a l r, box => l.check leafOk chartOf cd m (half box a false) &&
      r.check leafOk chartOf cd m (half box a true)
  | cd, _, .leaf w, box => leafOk cd w box
  | _, m, .affine m' box' t, box => m'.ok && boxWidthsOk box' && coverOk m m' box box' &&
      t.check leafOk chartOf (chartOf m') m' box'
  | _, _, .fail, _ => false

theorem ATree.check_sound (leafOk : ChartData K → Leaf → Box → Bool) (chartOf : AffMap → ChartData K)
    (Good : (Fin 5 → ℝ) → Prop) (Inv : ChartData K → AffMap → Prop)
    (hleaf : ∀ cd m l box, Inv cd m → (∀ z, m.apply z 0 = z 0) → (∀ i, 0 ≤ (box i).2) →
      leafOk cd l box = true → ∀ z, KPoly.InBox box z → Good (m.apply z))
    (hchart : ∀ m, m.ok = true → Inv (chartOf m) m) :
    ∀ (t : ATree) (cd : ChartData K) (m : AffMap) (box : Box), Inv cd m → (∀ z, m.apply z 0 = z 0) →
      (∀ i, 0 ≤ (box i).2) → t.check leafOk chartOf cd m box = true →
      ∀ z, KPoly.InBox box z → Good (m.apply z)
  | .split a l r, cd, m, box, hinv, hm, hb, h, z, hz => by
    simp only [ATree.check, Bool.and_eq_true] at h
    rcases inBox_half hz a with h1 | h1
    · exact ATree.check_sound leafOk chartOf Good Inv hleaf hchart l cd m _ hinv hm
        (half_width_nonneg hb a false) h.1 z h1
    · exact ATree.check_sound leafOk chartOf Good Inv hleaf hchart r cd m _ hinv hm
        (half_width_nonneg hb a true) h.2 z h1
  | .leaf w, cd, m, box, hinv, hm, hb, h, z, hz => hleaf cd m w box hinv hm hb h z hz
  | .affine m' box' t, _, m, box, _, _, _, h, z, hz => by
    simp only [ATree.check, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hm', hw'⟩, hcov⟩, ht⟩ := h
    have hw'' : ∀ i, 0 ≤ (box' i).2 := by simpa [boxWidthsOk] using hw'
    have hz' := coverOk_sound hcov hz
    have := ATree.check_sound leafOk chartOf Good Inv hleaf hchart t (chartOf m') m' box' (hchart m' hm')
      (AffMap.apply_zero hm') hw'' ht _ hz'
    rwa [AffMap.apply_inv hm'] at this
  | .fail, _, _, _, _, _, _, h, _, _ => by simp [ATree.check] at h

end KCap

end Noperts.Pipeline

end
