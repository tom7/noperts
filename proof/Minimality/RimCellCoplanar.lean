module

public import Mathlib
public import Minimality.RimCellView

/-!
# The spanning hypothesis of the rim-cell test from non-coplanarity

`Minimality.RimCell.rimCell_exists_unimodal` and `isRupert_of_rimCell_coords` assume that the
diagonal differences `y i - y j` (`i ∈ {0, 2}`, `j ∈ {1, 3}`) span the space.  For `n = 3`
this follows from the four rim corners `y 0, y 1, y 2, y 3` not being coplanar.

* `diag_span_of_det_ne_zero`: `det (y 1 - y 0, y 2 - y 0, y 3 - y 0) ≠ 0` gives the spanning
  hypothesis `hspan`.
* `isRupert_of_rimCell_coords_of_det`: `isRupert_of_rimCell_coords` with `hspan` replaced by
  that determinant condition.
-/

@[expose] public section

set_option autoImplicit false

namespace Minimality.RimCell

open Finset Matrix

/-- Non-coplanar rim corners: the diagonal differences span `ℝ³`. -/
theorem diag_span_of_det_ne_zero (y : ZMod 4 → Fin 3 → ℝ)
    (hnc : (Matrix.of ![y 1 - y 0, y 2 - y 0, y 3 - y 0]).det ≠ 0) :
    ∀ w : Fin 3 → ℝ, (∀ p ∈ diagPairs, w ⬝ᵥ (y p.1 - y p.2) = 0) → w = 0 := by
  intro w hw
  have h : ∀ i j : ZMod 4, (i, j) ∈ diagPairs → w ⬝ᵥ (y i - y j) = 0 := fun i j h => hw _ h
  have h01 := h 0 1 (by decide)
  have h03 := h 0 3 (by decide)
  have h21 := h 2 1 (by decide)
  have h23 := h 2 3 (by decide)
  have e1 : w ⬝ᵥ (y 1 - y 0) = 0 := by
    rw [show y 1 - y 0 = -(y 0 - y 1) by abel, dotProduct_neg, h01, neg_zero]
  have e3 : w ⬝ᵥ (y 3 - y 0) = 0 := by
    rw [show y 3 - y 0 = -(y 0 - y 3) by abel, dotProduct_neg, h03, neg_zero]
  have e2 : w ⬝ᵥ (y 2 - y 0) = 0 := by
    rw [show y 2 - y 0 = (y 2 - y 1) + (y 1 - y 0) by abel, dotProduct_add, h21, e1, add_zero]
  have hm : (Matrix.of ![y 1 - y 0, y 2 - y 0, y 3 - y 0]) *ᵥ w = 0 := by
    ext i
    fin_cases i
    · change _ ⬝ᵥ w = 0
      rw [dotProduct_comm]; exact e1
    · change _ ⬝ᵥ w = 0
      rw [dotProduct_comm]; exact e2
    · change _ ⬝ᵥ w = 0
      rw [dotProduct_comm]; exact e3
  exact Matrix.eq_zero_of_mulVec_eq_zero hnc hm

/-- `isRupert_of_rimCell_coords` with the spanning hypothesis replaced by non-coplanarity of
the four rim corners. -/
theorem isRupert_of_rimCell_coords_of_det (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det)
    (y : ZMod 4 → Fin 3 → ℝ) (hy : Function.Injective y) (Y : Finset (Fin 3 → ℝ))
    (hyY : ∀ i, y i ∈ Y)
    (hnc : (Matrix.of ![y 1 - y 0, y 2 - y 0, y 3 - y 0]).det ≠ 0)
    {A : Set (Fin 3 → ℝ)} (hAo : IsOpen A) (hAc : Convex ℝ A) (hA0 : (0 : Fin 3 → ℝ) ∉ A)
    (hcell : ∀ c ∈ A, ∀ i : ZMod 4, ∀ v ∈ Y, v ≠ y i → v ≠ y (i + 1) →
      0 < (Matrix.of ![y (i + 1) - y i, v - y i, c]).det)
    {g g' : Fin 3 → ℝ} (hg : g ∈ closure A) (hg' : g' ∈ closure A)
    (hneg : ∃ p ∈ diagPairs, ((Eᵀ * E) *ᵥ g) ⬝ᵥ (y p.1 - y p.2) < 0)
    (hpos : ∃ p ∈ diagPairs, 0 < ((Eᵀ * E) *ᵥ g') ⬝ᵥ (y p.1 - y p.2)) :
    IsRupert (Y.image (emb E)) :=
  isRupert_of_rimCell_coords E hE y hy Y hyY (diag_span_of_det_ne_zero y hnc) hAo hAc hA0 hcell
    hg hg' hneg hpos

end Minimality.RimCell
