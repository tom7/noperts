module

public import Minimality.Type24BCertW26

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset Filter
open scoped Topology

namespace Minimality.T24.A10

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell
  Minimality.LexCell Minimality.Split Minimality.T24.M4 Minimality.T24.A7
  Minimality.T24.Sym Minimality.T24.A8

theorem ustar_sharp {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hU : UStarArgs x F)
    (h63 : ⟪x 6 - x 1, ustar x⟫ < ⟪x 3 - x 1, ustar x⟫) (h30 : ⟪x 3 - x 1, ustar x⟫ ≤ 0)
    (hz5 : 0 < ⟪x 5 - x 1, ustar x⟫) :
    Minimality.Gen.LexAny F := by
  have T := type24OfFac F
  have ha5p : 0 < oblX0 x 5 := T.X0_pos (v := 5) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hz0 := ustar_z0_nonpos F hU.hD hU.hc3 hU.hab hU.hac
  have hrep : ∀ v : Fin 7, x v - x 1 =
      oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1) := by
    intro v; rw [T.rep v]; abel
  have hz5e : ⟪x 5 - x 1, ustar x⟫ = oblX0 x 5 * ⟪x 0 - x 1, ustar x⟫ +
      oblX2 x 5 * ⟪x 2 - x 1, ustar x⟫ + oblX6 x 5 * ⟪x 6 - x 1, ustar x⟫ := by
    rw [hrep 5, inner_add_left, inner_add_left, inner_smul_left, inner_smul_left, inner_smul_left]
    simp
  have hz5' := hz5
  have hz6 : ⟪x 6 - x 1, ustar x⟫ < 0 := by linarith
  have hz2 : 0 < ⟪x 2 - x 1, ustar x⟫ := by
    by_contra hn
    push Not at hn
    nlinarith [mul_nonpos_of_nonneg_of_nonpos ha5p.le hz0,
      mul_nonpos_of_nonneg_of_nonpos hb5.le hn, mul_neg_of_pos_of_neg hc5 hz6]
  have w6 : ⟪x 6, ustar x⟫ = ⟪x 1, ustar x⟫ + ⟪x 6 - x 1, ustar x⟫ := by rw [inner_sub_left]; ring
  have w3 : ⟪x 3, ustar x⟫ = ⟪x 1, ustar x⟫ + ⟪x 3 - x 1, ustar x⟫ := by rw [inner_sub_left]; ring
  have w5 : ⟪x 5, ustar x⟫ = ⟪x 1, ustar x⟫ + ⟪x 5 - x 1, ustar x⟫ := by rw [inner_sub_left]; ring
  have w2 : ⟪x 2, ustar x⟫ = ⟪x 1, ustar x⟫ + ⟪x 2 - x 1, ustar x⟫ := by rw [inner_sub_left]; ring
  refine ustar_lexAny_of_clauses F hU ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    exact clause_of_gt (by first | (left; linarith) | (right; left; linarith))


/-- `ustar_closed_W26` without any `z3` hypothesis. -/
theorem ustar_closed_W26_full {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hU : UStarArgs x F)
    (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0) (hn : nB x < nC x)
    (hz5 : max 0 ⟪x 6 - x 1, ustar x⟫ < ⟪x 5 - x 1, ustar x⟫) :
    Minimality.Gen.LexAny F ∨ SplitAny24 F := by
  by_cases hL : Minimality.Gen.LexAny F
  · exact Or.inl hL
  by_cases h3 : 0 < ⟪x 3 - x 1, ustar x⟫
  · exact ustar_closed_W26 F hU hbc hn h3 hz5
  have h63 : ⟪x 6 - x 1, ustar x⟫ < ⟪x 3 - x 1, ustar x⟫ := by
    by_contra h
    exact cert_w26_geom F hU.hC hU.ha5 hU.hc3 hbc hn hL (not_lt.mp h)
  exact absurd (ustar_sharp F hU h63 (not_lt.mp h3)
    (lt_of_le_of_lt (le_max_left _ _) hz5)) hL

/-- On the wall `a5 = 1`, `Dl < 0` holds unconditionally. -/
theorem dl_neg_of_wallA5 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (ha5 : oblX0 x 5 = 1) :
    Dl x < 0 := by
  have T := type24OfFac F
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  unfold Dl
  rw [ha5, sub_self, mul_zero, zero_sub]
  exact neg_lt_zero.mpr (mul_pos ha3 hc5)

/-- On the wall `a5 = 1`, `Dl4 < 0` holds unconditionally. -/
theorem dl4_neg_of_wallA5 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (ha5 : oblX0 x 5 = 1) :
    Dl4 x < 0 := by
  have T := type24OfFac F
  have ha4 : 0 < oblX0 x 4 := T.X0_pos (v := 4) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  unfold Dl4
  rw [ha5, sub_self, mul_zero, zero_sub]
  exact neg_lt_zero.mpr (mul_pos ha4 hc5)

/-- On the wall `a5 = 1` with `a4 < 1`, `nB < 0 < nC` holds unconditionally. -/
theorem nB_lt_nC_of_wallA5_a4lt {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha5 : oblX0 x 5 = 1) (ha4 : oblX0 x 4 < 1) :
    nB x < nC x := by
  have T := type24OfFac F
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  unfold nB nC
  rw [ha5, sub_self, mul_zero, mul_zero, zero_sub, sub_zero]
  have h14 : 0 < 1 - oblX0 x 4 := sub_pos.mpr ha4
  linarith [mul_pos hc5 h14, mul_pos hb5 h14]

end Minimality.T24.A10
