module

public import Mathlib
public import Minimality.RimCellConv
public import Minimality.RimCellVertex

@[expose] public section

/-!
# The star certificate (Lemma S)

Fix a direction `ρ` (shape coordinates) and finitely many "row vectors" `a i`.  A row is
*pairing* `((Eᵀ E) a) ⬝ᵥ ρ`, which is linear in `a`.  If `-ρ` is a nonnegative combination of
the `a i`, then for every metric `Eᵀ E` some row is negative (otherwise `-ρᵀ G ρ ≥ 0`).

* `exists_row_neg_of_neg_mem_cone`: the metric-free linear core.
* `PPRow`: the data of one row of Lemma N (`isRupert_of_conv_pair_closure`), with `ρ` a point of
  the closure of a cell and `a` a point of the closure of the cone `convSet` of its rim, or the
  other way round.
* `isRupert_of_star`: if every row is a `PPRow`, `E Y` is Rupert.
* `isRupert_of_star_three`: the three-vector form.
* `isRupert_of_star_leaf`: the leaf form, where further vectors are depth differences
  `y p - y q` of a robust vertex leaf at `ρ` (`isRupert_of_rimCell_vertex_robust`).
-/

set_option autoImplicit false

namespace Minimality.RimCell

open Finset Matrix Filter Topology
open scoped RealInnerProductSpace

/-- A row of Lemma N through `ρ` with vector `a`, for the point set `Y`. -/
def PPRow (Y : Finset (Fin 3 → ℝ)) (ρ a : Fin 3 → ℝ) : Prop :=
  ∃ (k : ℕ) (_ : NeZero k) (_ : 3 ≤ k) (y : ZMod k → Fin 3 → ℝ), Function.Injective y ∧
    (∀ i, y i ∈ Y) ∧
    ((ρ ∈ closure (cellSet Y y) ∧ a ∈ closure (convSet y)) ∨
     (a ∈ closure (cellSet Y y) ∧ ρ ∈ closure (convSet y)))

theorem pairing_symm (G : Matrix (Fin 3) (Fin 3) ℝ) (hG : Gᵀ = G) (a b : Fin 3 → ℝ) :
    (G *ᵥ a) ⬝ᵥ b = (G *ᵥ b) ⬝ᵥ a := by
  have : b ᵥ* G = G *ᵥ b := by rw [← Matrix.vecMul_transpose, hG]
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, this]

theorem pairing_pos (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det) {ρ : Fin 3 → ℝ}
    (hρ : ρ ≠ 0) : 0 < ((Eᵀ * E) *ᵥ ρ) ⬝ᵥ ρ := by
  have h : ((Eᵀ * E) *ᵥ ρ) ⬝ᵥ ρ = (E *ᵥ ρ) ⬝ᵥ (E *ᵥ ρ) := by
    rw [← Matrix.mulVec_mulVec, dotProduct_comm, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose]
  rw [h]
  have : E *ᵥ ρ ≠ 0 := fun h0 => hρ (Matrix.eq_zero_of_mulVec_eq_zero hE.ne' h0)
  exact lt_of_le_of_ne (by simpa using dotProduct_self_star_nonneg (E *ᵥ ρ)) (by
    intro h0; exact this (dotProduct_self_eq_zero.mp h0.symm))

theorem row_sum {ι : Type*} (G : Matrix (Fin 3) (Fin 3) ℝ) (s : Finset ι)
    (a : ι → Fin 3 → ℝ) (lam : ι → ℝ) (ρ : Fin 3 → ℝ) :
    (G *ᵥ (∑ i ∈ s, lam i • a i)) ⬝ᵥ ρ = ∑ i ∈ s, lam i * ((G *ᵥ a i) ⬝ᵥ ρ) := by
  rw [Matrix.mulVec_sum, sum_dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_smul, smul_dotProduct, smul_eq_mul]

/-- **Metric-free core.**  If `-ρ` is a nonnegative combination of the `a i`, some row
`((Eᵀ E) a i) ⬝ᵥ ρ` is negative, for every `E` with `0 < det E`. -/
theorem exists_row_neg_of_neg_mem_cone {ι : Type*} (s : Finset ι) (a : ι → Fin 3 → ℝ)
    (lam : ι → ℝ) (hlam : ∀ i ∈ s, 0 ≤ lam i) {ρ : Fin 3 → ℝ} (hρ : ρ ≠ 0)
    (hsum : -ρ = ∑ i ∈ s, lam i • a i) (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det) :
    ∃ i ∈ s, ((Eᵀ * E) *ᵥ a i) ⬝ᵥ ρ < 0 := by
  by_contra hcon
  push Not at hcon
  have h1 : 0 ≤ ∑ i ∈ s, lam i * (((Eᵀ * E) *ᵥ a i) ⬝ᵥ ρ) :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hlam i hi) (hcon i hi)
  have h2 : ∑ i ∈ s, lam i * (((Eᵀ * E) *ᵥ a i) ⬝ᵥ ρ) = ((Eᵀ * E) *ᵥ (-ρ)) ⬝ᵥ ρ := by
    rw [hsum, row_sum]
  rw [h2, Matrix.mulVec_neg, neg_dotProduct] at h1
  have := pairing_pos E hE hρ
  linarith

/-- A `PPRow` with negative pairing gives a Rupert pair. -/
theorem isRupert_of_PPRow (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det)
    (Y : Finset (Fin 3 → ℝ)) {ρ a : Fin 3 → ℝ} (h : PPRow Y ρ a)
    (hneg : ((Eᵀ * E) *ᵥ a) ⬝ᵥ ρ < 0) : IsRupert (Y.image (emb E)) := by
  obtain ⟨k, hne, hk, y, hy, hyY, h | h⟩ := h
  · exact isRupert_of_conv_pair_closure hk E hE y hy Y hyY h.1 h.2 hneg
  · refine isRupert_of_conv_pair_closure hk E hE y hy Y hyY h.1 h.2 ?_
    rw [pairing_symm _ (by simp [Matrix.transpose_mul]) ] ; exact hneg

/-- **Lemma S (star certificate).**  If every row `a i` through `ρ` is a `PPRow` and
`-ρ = ∑ lam i • a i` with `lam ≥ 0`, then `E Y` is Rupert for every `E` with `0 < det E`. -/
theorem isRupert_of_star {ι : Type*} (s : Finset ι) (a : ι → Fin 3 → ℝ) (lam : ι → ℝ)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det) (Y : Finset (Fin 3 → ℝ))
    {ρ : Fin 3 → ℝ} (hρ : ρ ≠ 0) (hrow : ∀ i ∈ s, PPRow Y ρ (a i))
    (hlam : ∀ i ∈ s, 0 ≤ lam i) (hsum : -ρ = ∑ i ∈ s, lam i • a i) :
    IsRupert (Y.image (emb E)) := by
  obtain ⟨i, hi, hneg⟩ := exists_row_neg_of_neg_mem_cone s a lam hlam hρ hsum E hE
  exact isRupert_of_PPRow E hE Y (hrow i hi) hneg

/-- The three-vector form of Lemma S. -/
theorem isRupert_of_star_three (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det)
    (Y : Finset (Fin 3 → ℝ)) {ρ a₁ a₂ a₃ : Fin 3 → ℝ} {l₁ l₂ l₃ : ℝ} (hρ : ρ ≠ 0)
    (h₁ : PPRow Y ρ a₁) (h₂ : PPRow Y ρ a₂) (h₃ : PPRow Y ρ a₃)
    (hl₁ : 0 ≤ l₁) (hl₂ : 0 ≤ l₂) (hl₃ : 0 ≤ l₃)
    (hsum : -ρ = l₁ • a₁ + l₂ • a₂ + l₃ • a₃) : IsRupert (Y.image (emb E)) := by
  refine isRupert_of_star (Finset.univ : Finset (Fin 3)) ![a₁, a₂, a₃] ![l₁, l₂, l₃] E hE Y hρ
    ?_ ?_ ?_
  · intro i _; fin_cases i <;> assumption
  · intro i _; fin_cases i <;> assumption
  · simpa [Fin.sum_univ_succ, add_assoc] using hsum

/-- **Leaf form.**  The rows are `PPRow`s (indexed by `s`) and depth differences `y p - y q`
(indexed by `t`, pairs `(p, q)` of rim indices of the cell `y`; the row of `y p - y q` is
`z q - z p` negated, i.e. it is `< 0` exactly when the depth `z p < z q`).  `-ρ` is a
nonnegative combination of all of them.  If a failing depth difference at `ρ` (some
`z p < z q`) forces robust unimodality of the depths at `ρ`, and `ρ` is in the closure of the
interior of the cell `A`, then `E Y` is Rupert: either all listed differences hold and then
some `PPRow` is negative, or the robust leaf applies. -/
theorem isRupert_of_star_leaf {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det)
    (y : ZMod k → Fin 3 → ℝ) (hy : Function.Injective y) (Y : Finset (Fin 3 → ℝ))
    (hyY : ∀ i, y i ∈ Y) {A : Set (Fin 3 → ℝ)}
    (hcell : ∀ c ∈ A, ∀ i : ZMod k, ∀ v ∈ Y, v ≠ y i → v ≠ y (i + 1) →
      0 < (Matrix.of ![y (i + 1) - y i, v - y i, c]).det)
    {ρ : Fin 3 → ℝ} (hρ : ρ ≠ 0) (hg : ρ ∈ closure (interior A))
    {ι κ : Type*} (s : Finset ι) (a : ι → Fin 3 → ℝ) (t : Finset κ) (p q : κ → ZMod k)
    (lam : ι → ℝ) (mu : κ → ℝ) (hrow : ∀ i ∈ s, PPRow Y ρ (a i))
    (hlam : ∀ i ∈ s, 0 ≤ lam i) (hmu : ∀ j ∈ t, 0 ≤ mu j)
    (hsum : -ρ = ∑ i ∈ s, lam i • a i + ∑ j ∈ t, mu j • (y (p j) - y (q j)))
    (hleaf : (∃ j ∈ t, ((Eᵀ * E) *ᵥ ρ) ⬝ᵥ y (p j) < ((Eᵀ * E) *ᵥ ρ) ⬝ᵥ y (q j)) →
      IsRobustUnimodal (fun i => ((Eᵀ * E) *ᵥ ρ) ⬝ᵥ y i)) :
    IsRupert (Y.image (emb E)) := by
  classical
  by_cases hall : ∀ j ∈ t, ((Eᵀ * E) *ᵥ ρ) ⬝ᵥ y (q j) ≤ ((Eᵀ * E) *ᵥ ρ) ⬝ᵥ y (p j)
  · by_cases hpp : ∃ i ∈ s, ((Eᵀ * E) *ᵥ a i) ⬝ᵥ ρ < 0
    · obtain ⟨i, hi, hneg⟩ := hpp
      exact isRupert_of_PPRow E hE Y (hrow i hi) hneg
    · exfalso
      push Not at hpp
      have h1 : 0 ≤ ∑ i ∈ s, lam i * (((Eᵀ * E) *ᵥ a i) ⬝ᵥ ρ) :=
        Finset.sum_nonneg fun i hi => mul_nonneg (hlam i hi) (hpp i hi)
      have h2 : 0 ≤ ∑ j ∈ t, mu j * (((Eᵀ * E) *ᵥ (y (p j) - y (q j))) ⬝ᵥ ρ) := by
        refine Finset.sum_nonneg fun j hj => mul_nonneg (hmu j hj) ?_
        rw [pairing_symm _ (by simp [Matrix.transpose_mul]), dotProduct_sub]
        linarith [hall j hj]
      have h3 : ((Eᵀ * E) *ᵥ (-ρ)) ⬝ᵥ ρ
          = ∑ i ∈ s, lam i * (((Eᵀ * E) *ᵥ a i) ⬝ᵥ ρ)
            + ∑ j ∈ t, mu j * (((Eᵀ * E) *ᵥ (y (p j) - y (q j))) ⬝ᵥ ρ) := by
        rw [hsum, Matrix.mulVec_add, add_dotProduct, row_sum, row_sum]
      rw [Matrix.mulVec_neg, neg_dotProduct] at h3
      have := pairing_pos E hE hρ
      linarith
  · push Not at hall
    obtain ⟨j, hj, hlt⟩ := hall
    exact isRupert_of_rimCell_vertex_robust hk E hE y hy Y hyY hcell hg (hleaf ⟨j, hj, hlt⟩)

end Minimality.RimCell
