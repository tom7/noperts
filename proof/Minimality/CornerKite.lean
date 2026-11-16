module

public import Mathlib
public import Minimality.CornerEQCert

/-!
# The foot view: Lemmas FC, PIV and KITE

* `inv_nonneg_fin3` / `inv_diag_pos_fin3` / `inv_mulVec_pos_fin3` (**Lemma FC**): for a positive
  definite `3 × 3` matrix with nonpositive off-diagonal entries (an obtuse Gram matrix) the inverse is
  entrywise nonnegative with positive diagonal, so `G⁻¹ q > 0` for `q > 0`.  Only `Fin 3` is done
  (explicit adjugate); the general M-matrix statement is not in Mathlib.
* `isRupert_of_pivot` (**Lemma PIV**): `ρ₀` in the open cell, `σ` in the closed cone `Conv`,
  `σ ≠ 0`, `((Eᵀ E) σ) ⬝ᵥ ρ₀ ≤ 0`: `E Y` is Rupert.  Move `ρ₀` to `ρ₀ - ε σ`.
* `isRupert_of_kite` (**Lemma KITE**): with `n = G⁻¹ 1` in the cell and `σ ≠ 0` in the closed cone
  with `∑ σ_i ≤ 0`, `E Y` is Rupert.  The proof only uses `G n = 1` (so `G` invertible), not
  obtuseness; obtuseness (via FC) is only needed to know `n` lies in the corner cone, which is a
  statement about `n`, not part of this implication.  So the obtuseness hypothesis is dropped.
-/

set_option autoImplicit false

namespace Minimality.CornerEQ

open Finset Matrix Filter Topology
open Minimality.RimCell

@[expose] public section

section FC

variable {G : Matrix (Fin 3) (Fin 3) ℝ}

private theorem minor_pos (hG : G.PosDef) {i j : Fin 3} (hij : i ≠ j) :
    0 < G i i * G j j - G i j * G j i := by
  have h := (hG.submatrix (e := ![i, j]) (he := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm])).det_pos
  rw [Matrix.det_fin_two] at h
  simpa using h

private theorem sym_of (hG : G.PosDef) (i j : Fin 3) : G j i = G i j := by
  have := hG.isHermitian
  have h2 := congrFun (congrFun this i) j
  simpa [Matrix.conjTranspose_apply] using h2

/-- Entries of the adjugate of an obtuse positive definite `3 × 3` matrix are nonnegative, the
diagonal ones positive. -/
theorem adjugate_nonneg_fin3 (hG : G.PosDef) (hGo : ∀ a b, a ≠ b → G a b ≤ 0) (i j : Fin 3) :
    0 ≤ adjugate G i j := by
  have s01 := sym_of hG 0 1
  have s02 := sym_of hG 0 2
  have s12 := sym_of hG 1 2
  have m01 := minor_pos hG (show (0 : Fin 3) ≠ 1 by decide)
  have m02 := minor_pos hG (show (0 : Fin 3) ≠ 2 by decide)
  have m12 := minor_pos hG (show (1 : Fin 3) ≠ 2 by decide)
  have d0 : 0 < G 0 0 := hG.diag_pos
  have d1 : 0 < G 1 1 := hG.diag_pos
  have d2 : 0 < G 2 2 := hG.diag_pos
  have o01 := hGo 0 1 (by decide)
  have o02 := hGo 0 2 (by decide)
  have o12 := hGo 1 2 (by decide)
  rw [s01] at m01; rw [s02] at m02; rw [s12] at m12
  fin_cases i <;> fin_cases j <;>
    simp [adjugate_fin_three, s01, s02, s12] <;>
    nlinarith [mul_nonneg_of_nonpos_of_nonpos o01 o02, mul_nonneg_of_nonpos_of_nonpos o01 o12,
      mul_nonneg_of_nonpos_of_nonpos o02 o12, mul_nonneg d0.le (neg_nonneg.2 o12),
      mul_nonneg d1.le (neg_nonneg.2 o02), mul_nonneg d2.le (neg_nonneg.2 o01)]

theorem adjugate_diag_pos_fin3 (hG : G.PosDef) (i : Fin 3) : 0 < adjugate G i i := by
  have s01 := sym_of hG 0 1
  have s02 := sym_of hG 0 2
  have s12 := sym_of hG 1 2
  have m01 := minor_pos hG (show (0 : Fin 3) ≠ 1 by decide)
  have m02 := minor_pos hG (show (0 : Fin 3) ≠ 2 by decide)
  have m12 := minor_pos hG (show (1 : Fin 3) ≠ 2 by decide)
  rw [s01] at m01; rw [s02] at m02; rw [s12] at m12
  fin_cases i <;> simp [adjugate_fin_three, s01, s02, s12] <;> nlinarith

private theorem inv_eq : G⁻¹ = (G.det)⁻¹ • adjugate G := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv']

/-- **Lemma FC (entries).**  `G⁻¹ ≥ 0` entrywise for positive definite `G` with nonpositive
off-diagonal entries (`Fin 3` only). -/
theorem inv_nonneg_fin3 (hG : G.PosDef) (hGo : ∀ a b, a ≠ b → G a b ≤ 0) (i j : Fin 3) :
    0 ≤ G⁻¹ i j := by
  rw [inv_eq]
  exact mul_nonneg (inv_nonneg.2 hG.det_pos.le) (adjugate_nonneg_fin3 hG hGo i j)

theorem inv_diag_pos_fin3 (hG : G.PosDef) (i : Fin 3) : 0 < G⁻¹ i i := by
  rw [inv_eq]
  exact mul_pos (inv_pos.2 hG.det_pos) (adjugate_diag_pos_fin3 hG i)

/-- **Lemma FC.**  For positive definite `G` with nonpositive off-diagonal entries and `q > 0`
entrywise, `G⁻¹ q > 0` entrywise.  (`Fin 3` only.) -/
theorem inv_mulVec_pos_fin3 (hG : G.PosDef) (hGo : ∀ a b, a ≠ b → G a b ≤ 0) {q : Fin 3 → ℝ}
    (hq : ∀ i, 0 < q i) (i : Fin 3) : 0 < (G⁻¹ *ᵥ q) i := by
  simp only [mulVec, dotProduct]
  have h0 : ∀ j, 0 ≤ G⁻¹ i j * q j := fun j => mul_nonneg (inv_nonneg_fin3 hG hGo i j) (hq j).le
  exact lt_of_lt_of_le (mul_pos (inv_diag_pos_fin3 hG i) (hq i))
    (single_le_sum (f := fun j => G⁻¹ i j * q j) (fun j _ => h0 j) (mem_univ i))

end FC

section Pivot

/-- **Lemma PIV.**  `ρ₀` in the open cell `cellSet Y y`, `σ ≠ 0` in the closed cone of
`convSet y`, `G = Eᵀ E`, `det E > 0` and `(G σ) ⬝ᵥ ρ₀ ≤ 0`: `E Y` is Rupert. -/
theorem isRupert_of_pivot {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det)
    (y : ZMod k → Fin 3 → ℝ) (hy : Function.Injective y) (Y : Finset (Fin 3 → ℝ))
    (hyY : ∀ i, y i ∈ Y) {ρ₀ σ : Fin 3 → ℝ} (hρ : ρ₀ ∈ cellSet Y y)
    (hσ : σ ∈ closure (convSet y)) (hσ0 : σ ≠ 0) (hle : ((Eᵀ * E) *ᵥ σ) ⬝ᵥ ρ₀ ≤ 0) :
    IsRupert (Y.image (emb E)) := by
  set G := Eᵀ * E with hG
  have hpos : 0 < (G *ᵥ σ) ⬝ᵥ σ := gram_pos E hE hσ0
  have hcont : Continuous fun ε : ℝ => ρ₀ - ε • σ := by fun_prop
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), ρ₀ - ε • σ ∈ cellSet Y y :=
    hcont.continuousAt.eventually_mem (by simpa using (isOpen_cellSet Y y).mem_nhds hρ)
  obtain ⟨ε, hεpos, hε⟩ : ∃ ε : ℝ, 0 < ε ∧ ρ₀ - ε • σ ∈ cellSet Y y := by
    obtain ⟨U, hU, hUo, h0U⟩ := mem_nhds_iff.mp hev
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hUo 0 h0U
    refine ⟨δ / 2, by positivity, hU (hball ?_)⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith
  refine isRupert_of_conv_pair_closure hk E hE y hy Y hyY (subset_closure hε) hσ ?_
  have : (G *ᵥ σ) ⬝ᵥ (ρ₀ - ε • σ) = (G *ᵥ σ) ⬝ᵥ ρ₀ - ε * ((G *ᵥ σ) ⬝ᵥ σ) := by
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
  rw [this]
  nlinarith

/-- **Lemma KITE.**  `G = Eᵀ E`, `det E > 0`, `n = G⁻¹ 1` in the open cell, `σ ≠ 0` in the closed
cone of `convSet y` with `∑ σ_i ≤ 0`: `E Y` is Rupert.  Obtuseness of `G` is not used (it only
places `n` in the corner cone, by Lemma FC); only `G n = 1`. -/
theorem isRupert_of_kite {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det)
    (y : ZMod k → Fin 3 → ℝ) (hy : Function.Injective y) (Y : Finset (Fin 3 → ℝ))
    (hyY : ∀ i, y i ∈ Y) {σ : Fin 3 → ℝ}
    (hn : ((Eᵀ * E)⁻¹ *ᵥ (fun _ => (1 : ℝ))) ∈ cellSet Y y)
    (hσ : σ ∈ closure (convSet y)) (hσ0 : σ ≠ 0) (hs : ∑ i, σ i ≤ 0) :
    IsRupert (Y.image (emb E)) := by
  set G := Eᵀ * E with hG
  have hdet : IsUnit G.det := by
    rw [hG, det_mul, det_transpose]
    exact (IsUnit.mk0 _ (by positivity))
  have h1 : G *ᵥ (G⁻¹ *ᵥ (fun _ => (1 : ℝ))) = fun _ => 1 := by
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, one_mulVec]
  refine isRupert_of_pivot hk E hE y hy Y hyY hn hσ hσ0 ?_
  have hsymm : Gᵀ = G := by simp [hG, transpose_mul]
  have : (G *ᵥ σ) ⬝ᵥ (G⁻¹ *ᵥ (fun _ => (1 : ℝ))) = ∑ i, σ i := by
    rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hsymm, h1, dotProduct_comm]
    simp [dotProduct]
  rw [this]; exact hs

end Pivot

end

end Minimality.CornerEQ
