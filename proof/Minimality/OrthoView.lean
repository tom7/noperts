module

public import Minimality.DominanceCell

@[expose] public section

open scoped RealInnerProductSpace

namespace Minimality.H21

/-- **Lemma S, real core.** An affine function with `f0 < f4, f5` and a crossing of the
segments `[0,3]` and `[4,5]` (`(1-s) f0 + s f3 = (1-t) f4 + t f5`, `0 < s ≤ 1`, `0 ≤ t ≤ 1`)
has `min f4 f5 ≤ f3`. -/
theorem lemmaS_real {f0 f3 f4 f5 s t : ℝ} (h4 : f0 < f4) (h5 : f0 < f5)
    (hs : 0 < s) (hs1 : s ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hc : (1 - s) * f0 + s * f3 = (1 - t) * f4 + t * f5) : min f4 f5 ≤ f3 := by
  by_contra H
  push Not at H
  have l4 : min f4 f5 ≤ f4 := min_le_left _ _
  have l5 : min f4 f5 ≤ f5 := min_le_right _ _
  have h0 : f0 < min f4 f5 := lt_min h4 h5
  nlinarith [mul_nonneg (sub_nonneg.2 l4) (sub_nonneg.2 ht1), mul_nonneg (sub_nonneg.2 l5) ht,
    mul_pos hs (sub_pos.2 H), mul_nonneg (sub_nonneg.2 hs1) (sub_pos.2 h0).le]

/-- **Lemma S (geometric).** Points `x0 x3 x4 x5` of `ℝ³` with the diagonals `[x0,x3]` and
`[x4,x5]` meeting (a common point, `s ∈ (0,1]`, `t ∈ [0,1]`), and an affine function
`f = ⟪w,·⟫ + d` with `f x0 < f x4, f x5`: `min (f x4) (f x5) ≤ f x3`. -/
theorem lemmaS (x0 x3 x4 x5 w : ℝ³) (d s t : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) (ht : 0 ≤ t)
    (ht1 : t ≤ 1) (hX : (1 - s) • x0 + s • x3 = (1 - t) • x4 + t • x5)
    (h4 : ⟪w, x0⟫ + d < ⟪w, x4⟫ + d) (h5 : ⟪w, x0⟫ + d < ⟪w, x5⟫ + d) :
    min (⟪w, x4⟫ + d) (⟪w, x5⟫ + d) ≤ ⟪w, x3⟫ + d := by
  have e := congrArg (fun z => ⟪w, z⟫) hX
  simp only [inner_add_right, inner_smul_right] at e
  exact lemmaS_real (f0 := ⟪w, x0⟫ + d) (f3 := ⟪w, x3⟫ + d) (f4 := ⟪w, x4⟫ + d)
    (f5 := ⟪w, x5⟫ + d) (s := s) (t := t) h4 h5 hs hs1 ht ht1 (by linarith)

/-- **Depth identity at the orthocentre view.** For `x i = p + ∑ e, y i e • v e` and a view `u`
with `⟪v e, u⟫ = 1` for all `e`: `⟪x i - x j, u⟫ = σ i - σ j`, `σ i = ∑ e, y i e`.
Metric-free; the cone condition `u = ∑ c e • v e` is not used. -/
theorem depth_orthocentre {ι : Type*} {k : ℕ} (x : ι → ℝ³) (p : ℝ³) (v : Fin k → ℝ³)
    (y : ι → Fin k → ℝ) (hx : ∀ i, x i = p + ∑ a, y i a • v a) (u : ℝ³)
    (hu : ∀ a, ⟪v a, u⟫ = 1) (i j : ι) :
    ⟪x i - x j, u⟫ = (∑ a, y i a) - ∑ a, y j a := by
  rw [hx i, hx j, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, sum_inner,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← sub_smul, inner_smul_left]; simp [hu a]

/-- **Theorem P, 4-rim case (EEVV and its generalisation).**  A 4-rim cell `(U, Dn)` containing
the orthocentre view `u` (`⟪v e, u⟫ = 1`), with `σ (c 0) < σ (c 3)` and `σ (c 1) < σ (c 2)`
(`σ = ∑ e, y · e`): Rupert.  For EEVV with rim `E1 E2 V1 V2` (`σ E = 1 < σ V`) both hold.
Opposite diagonal parities: pair `(0,3)` negative, pair `(2,1)` positive; Q4 at `g = g' = u`. -/
theorem isRupert_of_orthocentre_q4 {m n k : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (hx : Function.Injective x) {c : ZMod 4 → Fin n}
    (hc : Function.Injective c) {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn)
    {u : ℝ³} (hu : CellAt F U Dn u) (p : ℝ³) (v : Fin k → ℝ³) (y : Fin n → Fin k → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (h03 : (∑ e, y (c 0) e) < ∑ e, y (c 3) e) (h12 : (∑ e, y (c 1) e) < ∑ e, y (c 2) e) :
    IsRupert (Finset.univ.image x) := by
  refine isRupert_of_closedCell_q4 F hx hc hcyc hu hu.cellLe hu.cellLe
    ⟨(0, 3), by decide, ?_⟩ ⟨(2, 1), by decide, ?_⟩
  · rw [depth_orthocentre x p v y hxy u hv]; exact sub_neg.2 h03
  · rw [depth_orthocentre x p v y hxy u hv]; exact sub_pos.2 h12

/-- EEVV form: ends `c 0, c 1` with `σ = 1`, others with `σ > 1`. -/
theorem isRupert_of_orthocentre_eevv {m n k : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (hx : Function.Injective x) {c : ZMod 4 → Fin n}
    (hc : Function.Injective c) {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn)
    {u : ℝ³} (hu : CellAt F U Dn u) (p : ℝ³) (v : Fin k → ℝ³) (y : Fin n → Fin k → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE0 : (∑ e, y (c 0) e) = 1) (hE1 : (∑ e, y (c 1) e) = 1)
    (hV2 : 1 < ∑ e, y (c 2) e) (hV3 : 1 < ∑ e, y (c 3) e) :
    IsRupert (Finset.univ.image x) :=
  isRupert_of_orthocentre_q4 F hx hc hcyc hu p v y hxy hv (by linarith) (by linarith)

end Minimality.H21
