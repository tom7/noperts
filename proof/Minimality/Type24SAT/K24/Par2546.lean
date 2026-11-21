module

public import Minimality.Type24SAT.K24.ParEdge

@[expose] public section

/-!
# Type 24, `25 ∥ 46` (facet `H`): the view along the parallel edges

Facets `A … I` = indices `0 … 8` of `s0x_S24`.  Hypothesis `hl : x 6 - x 4 = l • (x 5 - x 2)`
(the edges `46` and `25` are parallel; `l < 0` follows from facet `H`).  At the view `d = x 2 - x 5`
(depths `w i = ⟪x i, d⟫`) one of the Q4 leaves `P0234`, `P0536` has mixed diagonal signs, unless
`w 0 = w 4 = w 5` (the "double wall": `D` perpendicular to the parallel edges).
* `par2546_real`: the pure real case analysis (identity
  `be (w3 - w4) + al (w3 - w5) = (1 - al - be)(be X + al Y)`, `X = w0 - w4`, `Y = w0 - w5`).
* `par2546_quad`: `D` is a quadrilateral `0 4 3 5`: `x 3 - x 0 = al (x 5 - x 0) + be (x 4 - x 0)`,
  `al, be > 0`, `al + be > 1`.
* `isRupert_par2546`: the theorem.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.Par
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.RimCell


/-- `D` is the quadrilateral `0 4 3 5`: `x 3 - x 0 = al (x 5 - x 0) + be (x 4 - x 0)` with
`al, be > 0` and `al + be > 1` (facets `E`, `C`, `G`). -/
theorem par2546_quad {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    ∃ al be : ℝ, 0 < al ∧ 0 < be ∧ 1 < al + be ∧
      x 3 - x 0 = al • (x 5 - x 0) + be • (x 4 - x 0) := by
  have IS := F.inner_sub
  have zD0 := F.zero 3 0 (by decide); have zD3 := F.zero 3 3 (by decide)
  have zD4 := F.zero 3 4 (by decide); have zD5 := F.zero 3 5 (by decide)
  have hD6 := F.neg 3 6 (by decide)
  have zE0 := F.zero 4 0 (by decide); have zE4 := F.zero 4 4 (by decide)
  have zE6 := F.zero 4 6 (by decide)
  have hE3 := F.neg 4 3 (by decide); have hE5 := F.neg 4 5 (by decide)
  have zC0 := F.zero 2 0 (by decide); have zC5 := F.zero 2 5 (by decide)
  have hC3 := F.neg 2 3 (by decide); have hC4 := F.neg 2 4 (by decide)
  have zG3 := F.zero 6 3 (by decide); have zG5 := F.zero 6 5 (by decide)
  have hG0 := F.neg 6 0 (by decide); have hG4 := F.neg 6 4 (by decide)
  obtain ⟨al, hal'⟩ : ∃ al : ℝ, al * F.f 4 (x 5) = F.f 4 (x 3) :=
    ⟨_, div_mul_cancel₀ _ hE5.ne⟩
  obtain ⟨be, hbe'⟩ : ∃ be : ℝ, be * F.f 2 (x 4) = F.f 2 (x 3) :=
    ⟨_, div_mul_cancel₀ _ hC4.ne⟩
  have hal : 0 < al := by
    by_contra h; push Not at h
    linarith [mul_nonneg_of_nonpos_of_nonpos h hE5.le]
  have hbe : 0 < be := by
    by_contra h; push Not at h
    linarith [mul_nonneg_of_nonpos_of_nonpos h hC4.le]
  have hcr : cross (F.N 3) (F.N 4) ≠ 0 := by
    intro h
    have hb := h21_binet (F.N 3) (F.N 4) (x 5 - x 0) (x 6 - x 0)
    rw [h, inner_zero_left, IS 3 5 0, IS 4 6 0, IS 3 6 0, IS 4 5 0, zD5, zD0, zE6, zE0] at hb
    linarith only [hb, mul_pos_of_neg_of_neg hD6 hE5]
  obtain ⟨lam, hlam⟩ := h21_mul_cross hcr
    (by rw [IS, zD4, zD0]; ring : ⟪F.N 3, x 4 - x 0⟫ = 0)
    (by rw [IS, zE4, zE0]; ring : ⟪F.N 4, x 4 - x 0⟫ = 0)
  have hCc : ⟪F.N 2, cross (F.N 3) (F.N 4)⟫ ≠ 0 := by
    intro h0
    have : ⟪F.N 2, x 4 - x 0⟫ = 0 := by rw [hlam, inner_smul_right, h0, mul_zero]
    rw [IS, zC0] at this; linarith
  set v : ℝ³ := (x 3 - x 0) - al • (x 5 - x 0) - be • (x 4 - x 0) with hv
  have ev : ∀ t, ⟪F.N t, v⟫ =
      ⟪F.N t, x 3 - x 0⟫ - al * ⟪F.N t, x 5 - x 0⟫ - be * ⟪F.N t, x 4 - x 0⟫ := by
    intro t; rw [hv, inner_sub_right, inner_sub_right, inner_smul_right, inner_smul_right]
  have vD : ⟪F.N 3, v⟫ = 0 := by rw [ev, IS, IS, IS, zD3, zD0, zD5, zD4]; ring
  have vE : ⟪F.N 4, v⟫ = 0 := by
    rw [ev, IS, IS, IS, zE0, zE4]; linarith
  have vC : ⟪F.N 2, v⟫ = 0 := by
    rw [ev, IS, IS, IS, zC0, zC5]; linarith
  obtain ⟨μ, hμ⟩ := h21_mul_cross hcr vD vE
  have hμ0 : μ = 0 := by
    have : μ * ⟪F.N 2, cross (F.N 3) (F.N 4)⟫ = 0 := by
      rw [← inner_smul_right, ← hμ, vC]
    exact (mul_eq_zero.1 this).resolve_right hCc
  have hv0 : v = 0 := by rw [hμ, hμ0, zero_smul]
  have hdec : x 3 - x 0 = al • (x 5 - x 0) + be • (x 4 - x 0) := by
    have := hv0; rw [hv] at this
    linear_combination (norm := module) this
  have ed : ⟪F.N 6, x 3 - x 0⟫ =
      al * ⟪F.N 6, x 5 - x 0⟫ + be * ⟪F.N 6, x 4 - x 0⟫ := by
    rw [hdec, inner_add_right, inner_smul_right, inner_smul_right]
  rw [IS, IS, IS, zG3, zG5] at ed
  refine ⟨al, be, hal, hbe, ?_, hdec⟩
  by_contra h; push Not at h
  linarith [mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 h) hG0.le,
    mul_neg_of_pos_of_neg hbe hG4]


end Minimality.T24.Par
