module

public import Minimality.RimCellClosed

@[expose] public section

open scoped RealInnerProductSpace

namespace Minimality.H21

/-- `Dominates y i j`: coordinatewise `y j ≤ y i` and `y i ≠ y j`. -/
def Dominates {ι : Type*} {k : ℕ} (y : ι → Fin k → ℝ) (i j : ι) : Prop :=
  (∀ a, y j a ≤ y i a) ∧ y i ≠ y j

/-- Dominance lemma: for points `x i = p + ∑ a, y i a • v a` and a view `u` with every
covector entry `⟪v a, u⟫ > 0`, a dominating `y i` gives `⟪x i - x j, u⟫ > 0`.  Any metric. -/
theorem dominance_pos {ι : Type*} {k : ℕ} (x : ι → ℝ³) (p : ℝ³) (v : Fin k → ℝ³)
    (y : ι → Fin k → ℝ) (hx : ∀ i, x i = p + ∑ a, y i a • v a) (u : ℝ³)
    (hw : ∀ a, 0 < ⟪v a, u⟫) {i j : ι} (h : Dominates y i j) : 0 < ⟪x i - x j, u⟫ := by
  have e : ⟪x i - x j, u⟫ = ∑ a, (y i a - y j a) * ⟪v a, u⟫ := by
    rw [hx i, hx j, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, sum_inner]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← sub_smul, inner_smul_left]; simp
  rw [e]
  obtain ⟨hle, hne⟩ := h
  obtain ⟨a, ha⟩ : ∃ a, y j a ≠ y i a := by
    by_contra H; push Not at H; exact hne (funext fun a => (H a).symm)
  have hlt : y j a < y i a := lt_of_le_of_ne (hle a) ha
  refine lt_of_lt_of_le (mul_pos (sub_pos.2 hlt) (hw a)) ?_
  exact Finset.single_le_sum (f := fun a => (y i a - y j a) * ⟪v a, u⟫)
    (fun b _ => mul_nonneg (sub_nonneg.2 (hle b)) (hw b).le) (Finset.mem_univ a)

/-- Weak version: all entries `≥ 0` give `⟪x i - x j, u⟫ ≥ 0`. -/
theorem dominance_nonneg {ι : Type*} {k : ℕ} (x : ι → ℝ³) (p : ℝ³) (v : Fin k → ℝ³)
    (y : ι → Fin k → ℝ) (hx : ∀ i, x i = p + ∑ a, y i a • v a) (u : ℝ³)
    (hw : ∀ a, 0 ≤ ⟪v a, u⟫) {i j : ι} (h : ∀ a, y j a ≤ y i a) : 0 ≤ ⟪x i - x j, u⟫ := by
  have e : ⟪x i - x j, u⟫ = ∑ a, (y i a - y j a) * ⟪v a, u⟫ := by
    rw [hx i, hx j, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, sum_inner]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← sub_smul, inner_smul_left]; simp
  rw [e]
  exact Finset.sum_nonneg fun a _ => mul_nonneg (sub_nonneg.2 (h a)) (hw a)

/-- Corner corollary: pairwise orthogonal nonzero `v a` and `u = ∑ c a • v a` with `c > 0`
give `⟪v a, u⟫ > 0`. -/
theorem corner_covector_pos {k : ℕ} (v : Fin k → ℝ³) (hv : ∀ a, v a ≠ 0)
    (horth : ∀ a b, a ≠ b → ⟪v a, v b⟫ = 0) (c : Fin k → ℝ) (hc : ∀ a, 0 < c a) (a : Fin k) :
    0 < ⟪v a, ∑ b, c b • v b⟫ := by
  rw [inner_sum, Finset.sum_eq_single a]
  · rw [inner_smul_right]; exact mul_pos (hc a) (real_inner_self_pos.2 (hv a))
  · intro b _ hb; rw [inner_smul_right, horth a b (Ne.symm hb), mul_zero]
  · simp

/-- **Lemma CC (dominance cell).**  Rim `c : ZMod 4 → Fin n` of cell `(U, Dn)`, a point `a` of the open
cell whose covector `⟪v e, a⟫` is entrywise positive, `x i = p + ∑ y i e • v e`.  If some diagonal pair
`(i, j)` has `y (c i)` dominating `y (c j)` and some `(i', j')` has `y (c j')` dominating `y (c i')`,
then Rupert.  No metric, orthogonality, rim non-coplanarity or HDN hypothesis. -/
theorem isRupert_of_dominanceCell {m n k : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (hx : Function.Injective x) {c : ZMod 4 → Fin n}
    (hc : Function.Injective c) {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn)
    {a : ℝ³} (ha : CellAt F U Dn a) (p : ℝ³) (v : Fin k → ℝ³) (y : Fin n → Fin k → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hw : ∀ e, 0 < ⟪v e, a⟫)
    (hD : ∃ q ∈ RimCell.diagPairs, Dominates y (c q.1) (c q.2))
    (hD' : ∃ q ∈ RimCell.diagPairs, Dominates y (c q.2) (c q.1)) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨q, hq, hqd⟩ := hD
  obtain ⟨q', hq', hqd'⟩ := hD'
  refine isRupert_of_closedCell_q4 F hx hc hcyc ha ha.cellLe ha.cellLe ⟨q', hq', ?_⟩ ⟨q, hq, ?_⟩
  · have := dominance_pos x p v y hxy a hw hqd'
    rw [← neg_sub, inner_neg_left]; linarith
  · exact dominance_pos x p v y hxy a hw hqd

/-- Corner form: `v` pairwise orthogonal and nonzero (a cube corner), cell point `a = ∑ c e • v e`
with `c > 0`. -/
theorem isRupert_of_dominanceCell_corner {m n k : ℕ} {S : Fin m → Finset (Fin n)}
    {x : Fin n → ℝ³} (F : S0xFac m S x) (hx : Function.Injective x) {c : ZMod 4 → Fin n}
    (hc : Function.Injective c) {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn)
    (p : ℝ³) (v : Fin k → ℝ³) (hv : ∀ e, v e ≠ 0) (horth : ∀ e f, e ≠ f → ⟪v e, v f⟫ = 0)
    (y : Fin n → Fin k → ℝ) (hxy : ∀ i, x i = p + ∑ e, y i e • v e)
    (cf : Fin k → ℝ) (hcf : ∀ e, 0 < cf e) (ha : CellAt F U Dn (∑ e, cf e • v e))
    (hD : ∃ q ∈ RimCell.diagPairs, Dominates y (c q.1) (c q.2))
    (hD' : ∃ q ∈ RimCell.diagPairs, Dominates y (c q.2) (c q.1)) :
    IsRupert (Finset.univ.image x) :=
  isRupert_of_dominanceCell F hx hc hcyc ha p v y hxy (corner_covector_pos v hv horth cf hcf) hD hD'

end Minimality.H21
