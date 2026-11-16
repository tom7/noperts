module

public import Minimality.CornerSnap
public import Minimality.RimCellClosed

/-!
# Obtuse Farkas lemma (OBF) and the corner closed-cell leaf

For a corner frame `e_a, e_b, e_c` with non-positive pairwise inner products (the obtuse cone `OB`
of Gram matrices), a family of depth-difference rows `⟨G, sym(W_i D_iᵀ)⟩ ≥ 0` is infeasible as soon
as a nonnegative combination plus a finite sum `Σ_j u_j u_jᵀ` of rank-1 terms with some
`view u_j ≠ 0` has non-positive diagonal and non-negative off-diagonal (`obtuse_farkas`).  Only
`view u_j ≠ 0` for one `j` is used, not positive definiteness of the whole Gram matrix.  `isRupert_corner_cell` composes it with `isRupert_of_closedCell`.
-/

@[expose] public section

open Finset
open scoped RealInnerProductSpace

namespace Minimality
namespace CornerSnap

/-- The frame form of a depth difference: `⟨G, sym(W Dᵀ)⟩` for the Gram matrix `G` of the frame
(`Corner.Rep.depth_sub` with `W = X v − X w`, `D = d`). -/
noncomputable def Corner.formRow {ι : Type*} (C : Corner ι) (W D : Fin 3 → ℝ) : ℝ :=
  ‖C.ea‖ ^ 2 * (W 0 * D 0) + ‖C.eb‖ ^ 2 * (W 1 * D 1) + ‖C.ec‖ ^ 2 * (W 2 * D 2) +
    ⟪C.ea, C.eb⟫ * (W 0 * D 1 + W 1 * D 0) + ⟪C.ea, C.ec⟫ * (W 0 * D 2 + W 2 * D 0) +
    ⟪C.eb, C.ec⟫ * (W 1 * D 2 + W 2 * D 1)

theorem Corner.Rep.depth_sub_formRow {ι : Type*} {C : Corner ι} {x : ι → ℝ³} (hC : C.Rep x)
    (d : Fin 3 → ℝ) (v w : ι) :
    ⟪x v, C.view d⟫ - ⟪x w, C.view d⟫ =
      C.formRow ![C.Xa v - C.Xa w, C.Xb v - C.Xb w, C.Xc v - C.Xc w] d := by
  rw [hC.depth_sub d v w]
  simp only [Corner.formRow, Corner.snapDepth, Corner.cosCoefAB, Corner.cosCoefAC,
    Corner.cosCoefBC, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- `‖Σ u_a e_a‖²` as a quadratic form in the Gram entries. -/
theorem Corner.norm_view_sq {ι : Type*} (C : Corner ι) (u : Fin 3 → ℝ) :
    ‖C.view u‖ ^ 2 = ‖C.ea‖ ^ 2 * (u 0 * u 0) + ‖C.eb‖ ^ 2 * (u 1 * u 1) +
      ‖C.ec‖ ^ 2 * (u 2 * u 2) + ⟪C.ea, C.eb⟫ * (2 * (u 0 * u 1)) +
      ⟪C.ea, C.ec⟫ * (2 * (u 0 * u 2)) + ⟪C.eb, C.ec⟫ * (2 * (u 1 * u 2)) := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [Corner.view, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm C.ea C.eb, real_inner_comm C.ea C.ec,
    real_inner_comm C.eb C.ec, conj_trivial]
  ring

/-- **Lemma OBF (obtuse Farkas).**  Frame with `⟨e_a,e_b⟩, ⟨e_a,e_c⟩, ⟨e_b,e_c⟩ ≤ 0`, rows
`(W i, D i)`, multipliers `lam i ≥ 0` and a finite family `U j` with some `Σ_a U_j,a e_a ≠ 0`.  If
`S = Σ lam_i sym(W_i D_iᵀ) + Σ_j U_j U_jᵀ` (a positive semidefinite term of any rank) has
non-positive diagonal and non-negative off-diagonal (the latter stated for twice the entry), some
row `⟨G, sym(W_i D_iᵀ)⟩` is negative.  Only the sign pattern of `S` and
`Σ_j ‖Σ_a U_j,a e_a‖² > 0` enter. -/
theorem obtuse_farkas {ι : Type*} (C : Corner ι) {κ : Type*} [Fintype κ] {r : ℕ}
    (hab : ⟪C.ea, C.eb⟫ ≤ 0) (hac : ⟪C.ea, C.ec⟫ ≤ 0) (hbc : ⟪C.eb, C.ec⟫ ≤ 0)
    (W D : κ → Fin 3 → ℝ) (lam : κ → ℝ) (U : Fin r → Fin 3 → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hU : ∃ j, C.view (U j) ≠ 0)
    (h0 : ∑ i, lam i * (W i 0 * D i 0) + ∑ j, U j 0 * U j 0 ≤ 0)
    (h1 : ∑ i, lam i * (W i 1 * D i 1) + ∑ j, U j 1 * U j 1 ≤ 0)
    (h2 : ∑ i, lam i * (W i 2 * D i 2) + ∑ j, U j 2 * U j 2 ≤ 0)
    (h01 : 0 ≤ ∑ i, lam i * (W i 0 * D i 1 + W i 1 * D i 0) + 2 * ∑ j, U j 0 * U j 1)
    (h02 : 0 ≤ ∑ i, lam i * (W i 0 * D i 2 + W i 2 * D i 0) + 2 * ∑ j, U j 0 * U j 2)
    (h12 : 0 ≤ ∑ i, lam i * (W i 1 * D i 2 + W i 2 * D i 1) + 2 * ∑ j, U j 1 * U j 2) :
    ∃ i, C.formRow (W i) (D i) < 0 := by
  by_contra hcon
  push Not at hcon
  have hsum : 0 ≤ ∑ i, lam i * C.formRow (W i) (D i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hlam i) (hcon i)
  have hid : ∑ i, lam i * C.formRow (W i) (D i) =
      ‖C.ea‖ ^ 2 * ∑ i, lam i * (W i 0 * D i 0) + ‖C.eb‖ ^ 2 * ∑ i, lam i * (W i 1 * D i 1) +
      ‖C.ec‖ ^ 2 * ∑ i, lam i * (W i 2 * D i 2) +
      ⟪C.ea, C.eb⟫ * ∑ i, lam i * (W i 0 * D i 1 + W i 1 * D i 0) +
      ⟪C.ea, C.ec⟫ * ∑ i, lam i * (W i 0 * D i 2 + W i 2 * D i 0) +
      ⟪C.eb, C.ec⟫ * ∑ i, lam i * (W i 1 * D i 2 + W i 2 * D i 1) := by
    simp only [Corner.formRow, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hq : ∑ j, ‖C.view (U j)‖ ^ 2 =
      ‖C.ea‖ ^ 2 * ∑ j, U j 0 * U j 0 + ‖C.eb‖ ^ 2 * ∑ j, U j 1 * U j 1 +
      ‖C.ec‖ ^ 2 * ∑ j, U j 2 * U j 2 + ⟪C.ea, C.eb⟫ * (2 * ∑ j, U j 0 * U j 1) +
      ⟪C.ea, C.ec⟫ * (2 * ∑ j, U j 0 * U j 2) + ⟪C.eb, C.ec⟫ * (2 * ∑ j, U j 1 * U j 2) := by
    simp only [C.norm_view_sq, Finset.mul_sum, ← Finset.sum_add_distrib]
  have hpos : 0 < ∑ j, ‖C.view (U j)‖ ^ 2 := by
    obtain ⟨j, hj⟩ := hU
    exact lt_of_lt_of_le (by positivity)
      (Finset.single_le_sum (f := fun j => ‖C.view (U j)‖ ^ 2) (fun _ _ => by positivity)
        (Finset.mem_univ j))
  nlinarith [mul_nonneg (sq_nonneg ‖C.ea‖) (neg_nonneg.2 h0),
    mul_nonneg (sq_nonneg ‖C.eb‖) (neg_nonneg.2 h1),
    mul_nonneg (sq_nonneg ‖C.ec‖) (neg_nonneg.2 h2),
    mul_nonneg (neg_nonneg.2 hab) h01, mul_nonneg (neg_nonneg.2 hac) h02,
    mul_nonneg (neg_nonneg.2 hbc) h12]

/-- Frame coordinate difference of two vertices (the `W` of a depth row). -/
def Corner.xdiff {ι : Type*} (C : Corner ι) (v w : ι) : Fin 3 → ℝ :=
  ![C.Xa v - C.Xa w, C.Xb v - C.Xb w, C.Xc v - C.Xc w]

/-- Shape-only side of an OBF certificate: multipliers `lam ≥ 0`, a finite family `U` of vectors
with some `U j ≠ 0`, and the six sign conditions on `S = Σ lam_i sym(W_i D_iᵀ) + Σ_j U_j U_jᵀ`.
(The single rank-1 term of the first version is `ObfCert.of_rank1`.) -/
def ObfCert {κ : Type*} [Fintype κ] {r : ℕ} (W D : κ → Fin 3 → ℝ) (lam : κ → ℝ)
    (U : Fin r → Fin 3 → ℝ) : Prop :=
  (∀ i, 0 ≤ lam i) ∧ (∃ j, U j ≠ 0) ∧
  ∑ i, lam i * (W i 0 * D i 0) + ∑ j, U j 0 * U j 0 ≤ 0 ∧
  ∑ i, lam i * (W i 1 * D i 1) + ∑ j, U j 1 * U j 1 ≤ 0 ∧
  ∑ i, lam i * (W i 2 * D i 2) + ∑ j, U j 2 * U j 2 ≤ 0 ∧
  0 ≤ ∑ i, lam i * (W i 0 * D i 1 + W i 1 * D i 0) + 2 * ∑ j, U j 0 * U j 1 ∧
  0 ≤ ∑ i, lam i * (W i 0 * D i 2 + W i 2 * D i 0) + 2 * ∑ j, U j 0 * U j 2 ∧
  0 ≤ ∑ i, lam i * (W i 1 * D i 2 + W i 2 * D i 1) + 2 * ∑ j, U j 1 * U j 2

/-- The rank-1 certificate `U Uᵀ` (the first form of `ObfCert`) is the one-term family. -/
theorem ObfCert.of_rank1 {κ : Type*} [Fintype κ] {W D : κ → Fin 3 → ℝ} {lam : κ → ℝ}
    {U : Fin 3 → ℝ} (hl : ∀ i, 0 ≤ lam i) (hU : U ≠ 0)
    (h0 : ∑ i, lam i * (W i 0 * D i 0) + U 0 * U 0 ≤ 0)
    (h1 : ∑ i, lam i * (W i 1 * D i 1) + U 1 * U 1 ≤ 0)
    (h2 : ∑ i, lam i * (W i 2 * D i 2) + U 2 * U 2 ≤ 0)
    (h01 : 0 ≤ ∑ i, lam i * (W i 0 * D i 1 + W i 1 * D i 0) + 2 * (U 0 * U 1))
    (h02 : 0 ≤ ∑ i, lam i * (W i 0 * D i 2 + W i 2 * D i 0) + 2 * (U 0 * U 2))
    (h12 : 0 ≤ ∑ i, lam i * (W i 1 * D i 2 + W i 2 * D i 1) + 2 * (U 1 * U 2)) :
    ObfCert W D lam (fun _ : Fin 1 => U) := by
  refine ⟨hl, ⟨0, hU⟩, ?_⟩
  simpa [Fin.sum_univ_one] using And.intro h0 (And.intro h1 (And.intro h2 (And.intro h01
    (And.intro h02 h12))))

/-- A linearly independent frame has `view U ≠ 0` for `U ≠ 0`. -/
theorem Corner.view_ne_zero {ι : Type*} {C : Corner ι} (hli : LinearIndependent ℝ ![C.ea, C.eb, C.ec])
    {U : Fin 3 → ℝ} (hU : U ≠ 0) : C.view U ≠ 0 := by
  intro h
  apply hU
  have := Fintype.linearIndependent_iff.1 hli U (by
    simpa [Fin.sum_univ_three, Corner.view] using h)
  ext i; exact this i

/-- OBF for a certificate and a linearly independent frame. -/
theorem obtuse_farkas_cert {ι : Type*} {C : Corner ι} (hli : LinearIndependent ℝ ![C.ea, C.eb, C.ec])
    {κ : Type*} [Fintype κ] {r : ℕ}
    (hab : ⟪C.ea, C.eb⟫ ≤ 0) (hac : ⟪C.ea, C.ec⟫ ≤ 0) (hbc : ⟪C.eb, C.ec⟫ ≤ 0)
    {W D : κ → Fin 3 → ℝ} {lam : κ → ℝ} {U : Fin r → Fin 3 → ℝ} (h : ObfCert W D lam U) :
    ∃ i, C.formRow (W i) (D i) < 0 := by
  obtain ⟨hl, hU, h0, h1, h2, h01, h02, h12⟩ := h
  obtain ⟨j, hj⟩ := hU
  exact obtuse_farkas C hab hac hbc W D lam U hl ⟨j, C.view_ne_zero hli hj⟩ h0 h1 h2 h01 h02 h12

end CornerSnap

namespace CornerSnap
open Minimality.H21

variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}

/-- The four rows `z p − z q ≥ 0` of a `RobUni` failure pattern `(B; b₁ < b₂ < b₃)`
(`z (B+b₁), z (B+b₃) ≤ z B, z (B+b₂)`), as pairs of cycle positions. -/
def patternPairs {k : ℕ} (B : ZMod k) (b₁ b₂ b₃ : ℕ) : Fin 4 → ZMod k × ZMod k :=
  ![(B, B + b₁), (B + b₂, B + b₁), (B, B + b₃), (B + b₂, B + b₃)]

/-- **Corner closed-cell leaf.**  A cell `(U, Dn)` of the facet arrangement of `x` with a strict
point `a`, a weak point `C.view d₀` (shape-only data when `d₀` is), a rim cycle `c` of `k ≥ 4`
vertices, an obtuse linearly independent frame representing `x`, and for every `RobUni` failure
pattern an OBF certificate for its four depth rows at `d₀`: `x` is Rupert.  Nothing else of the
metric enters. -/
theorem isRupert_corner_cell {k : ℕ} [NeZero k] (hk : 4 ≤ k) (F : S0xFac m S x)
    (hx : Function.Injective x) {c : ZMod k → Fin n} (hc : Function.Injective c)
    {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn) {a : ℝ³} (ha : CellAt F U Dn a)
    {C : Corner (Fin n)} (hC : C.Rep x) (hli : LinearIndependent ℝ ![C.ea, C.eb, C.ec])
    (hab : ⟪C.ea, C.eb⟫ ≤ 0) (hac : ⟪C.ea, C.ec⟫ ≤ 0) (hbc : ⟪C.eb, C.ec⟫ ≤ 0)
    (d₀ : Fin 3 → ℝ) (hu : CellLe F U Dn (C.view d₀))
    (hcert : ∀ (B : ZMod k) (b₁ b₂ b₃ : ℕ), 0 < b₁ → b₁ < b₂ → b₂ < b₃ → b₃ < k →
      ∃ (lam : Fin 4 → ℝ) (r : ℕ) (V : Fin r → Fin 3 → ℝ),
        ObfCert (fun j => C.xdiff (c (patternPairs B b₁ b₂ b₃ j).1) (c (patternPairs B b₁ b₂ b₃ j).2))
          (fun _ => d₀) lam V) :
    IsRupert (univ.image x) := by
  refine isRupert_of_closedCell hk F hx hc hcyc ha hu ?_
  intro B b₁ b₂ b₃ h1 h2 h3 h4 ⟨e1, e2, e3, e4⟩
  obtain ⟨lam, r, V, hcv⟩ := hcert B b₁ b₂ b₃ h1 h2 h3 h4
  obtain ⟨j, hj⟩ := obtuse_farkas_cert hli hab hac hbc hcv
  have key : ∀ p q : ZMod k, C.formRow (C.xdiff (c p) (c q)) d₀ =
      ⟪x (c p), C.view d₀⟫ - ⟪x (c q), C.view d₀⟫ := fun p q =>
    (hC.depth_sub_formRow d₀ (c p) (c q)).symm
  fin_cases j <;> simp only [patternPairs, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk, Matrix.cons_val_three, key] at hj <;> linarith

end CornerSnap
end Minimality
