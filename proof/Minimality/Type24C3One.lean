module

public import Minimality.Type24W63Radon

@[expose] public section

/-!
# Type 24: the stratum `c3 = 1` (`P236`)

Formalizes the `P236` pencil normal form, syzygies, `leaf_O2`, and the `c3 = 1` stratum theorem
`c3eq1_closed` in `Minimality.T24.A20`:
1. `h236`, `pencil236_decomp`, `pencil236_depth`, `syz_E23`, `syz_u27`, `syz_u27_coef_pos`,
   `sign_u07_of_w63_u27`, `sign_u07_of_E23_w63`, `sign_u27_of_u07_E23`, `leaf_O2`,
   `strat_A`..`strat_C` (from `P236.lean`).
2. `w63_eq_smul_u07` and `w63_facings_c3eq1`: at `c3 = 1`, `w63` and `u07` are positive scalar
   multiples of each other, with facets `0, 7, 8` edge-on (`= 0`).
3. `c3eq1_closed`: on `{CbarIn x, oblX6 x 3 = 1}` with non-tie genericity `hgen` on
   `{0, 1, 2, 3, 4, 6}` at `w63`, the single view `w63 = x 3 - x 6` gives `Minimality.Gen.LexAny F`.
   No sample facts (C3FACTS): `hh4_of_cbar` and `hsB_of_facets` derive two former sample facts, cones A and
   B split at `c4 = 1` (`strat_A2`, `strat_B2` for `c4 >= 1`), and cone D dies by `strat_C` (it lies inside cone C's `z1 > z2 > z0`; no `h1234`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.A20

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell
  Minimality.LexCell Minimality.Split Minimality.T24.M4 Minimality.T24.A7 Minimality.T24.A10
  Minimality.T24.A8 Minimality.T24.Q24 Minimality.T24 Minimality.T24.A15

/-! ### Pencil normal form, syzygies, and `leaf_O2` (`P236`) -/

/-- Height over the plane of facet 236 in units of `x 1` (`h = 1 - f236`, `f236 = b + c - om3 a`). -/
noncomputable def h236 (x : Fin 7 → ℝ³) (v : Fin 7) : ℝ :=
  1 - (oblX2 x v + oblX6 x v - omega3 x * oblX0 x v)

/-- **Pencil decomposition** (oblique projection onto plane 236 along edge 12). -/
theorem pencil236_decomp {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (v : Fin 7) :
    x v - x 2 = oblX0 x v • u07 x + oblX6 x v • (x 6 - x 2) + h236 x v • (x 1 - x 2) := by
  have T := type24OfFac F
  have h1 : x v - x 1 = oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) +
      oblX6 x v • (x 6 - x 1) := by rw [T.rep v]; abel
  have e : x v - x 2 = (x v - x 1) - (x 2 - x 1) := by abel
  have e6 : x 6 - x 2 = (x 6 - x 1) - (x 2 - x 1) := by abel
  have e1 : x 1 - x 2 = -(x 2 - x 1) := by abel
  rw [e, h1, e6, e1]
  dsimp only [u07, h236]
  module

/-- **Pencil normal form of a depth**: every depth difference against `x 2` is the in-plane part
(`⟪u07, u⟫`, `⟪x 6 - x 2, u⟫`) plus `h236 v` times the coupling `⟪x 1 - x 2, u⟫`. -/
theorem pencil236_depth {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (v : Fin 7) (u : ℝ³) :
    ⟪x v - x 2, u⟫ = oblX0 x v * ⟪u07 x, u⟫ + oblX6 x v * ⟪x 6 - x 2, u⟫ +
      h236 x v * ⟪x 1 - x 2, u⟫ := by
  rw [pencil236_decomp F v, inner_add_left, inner_add_left, real_inner_smul_left,
    real_inner_smul_left, real_inner_smul_left]

/-- **E23 syzygy**: `a3 u07 = t3 E23 + c3 w63`. -/
theorem syz_E23 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    oblX0 x 3 • u07 x = (1 - oblX6 x 3) • (x 3 - x 2) + oblX6 x 3 • (x 3 - x 6) := by
  have T := type24OfFac F
  have h3 : x 3 - x 1 = oblX0 x 3 • (x 0 - x 1) + oblX2 x 3 • (x 2 - x 1) +
      oblX6 x 3 • (x 6 - x 1) := by rw [T.rep 3]; abel
  have hb3 : oblX2 x 3 = oblX0 x 3 * omega3 x + (1 - oblX6 x 3) := by linarith [eq3 F]
  have e2 : x 3 - x 2 = (x 3 - x 1) - (x 2 - x 1) := by abel
  have e6 : x 3 - x 6 = (x 3 - x 1) - (x 6 - x 1) := by abel
  rw [e2, e6, h3, hb3]
  dsimp only [u07]
  module

/-- **u27 syzygy**: `c3 u27 = (c3 (1 + om5) - a3 (1 + om3)) u07 + (1 + om3) E23`. -/
theorem syz_u27 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    oblX6 x 3 • u27 x = (oblX6 x 3 * (1 + omega5 x) - oblX0 x 3 * (1 + omega3 x)) • u07 x +
      (1 + omega3 x) • (x 3 - x 2) := by
  have T := type24OfFac F
  have h3 : x 3 - x 1 = oblX0 x 3 • (x 0 - x 1) + oblX2 x 3 • (x 2 - x 1) +
      oblX6 x 3 • (x 6 - x 1) := by rw [T.rep 3]; abel
  have hb3 : oblX2 x 3 = oblX0 x 3 * omega3 x + (1 - oblX6 x 3) := by linarith [eq3 F]
  have e2 : x 3 - x 2 = (x 3 - x 1) - (x 2 - x 1) := by abel
  rw [e2, h3, hb3]
  dsimp only [u07, u27]
  module

/-- The `u07` coefficient of `syz_u27` is positive: it is `-f025(x 3) / (-f025(x 1))`, so this is the
strictness of facet 025 at `x 3` (region fact). -/
theorem syz_u27_coef_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    0 < oblX6 x 3 * (1 + omega5 x) - oblX0 x 3 * (1 + omega3 x) := by
  have T := type24OfFac F
  have hf2_6 : F.f 2 (x 6) = (1 + omega5 x) * F.f 2 (x 1) := by
    have ev2_5 := fac_eval F 2 5
    rw [F.zero 2 0 (by decide), F.zero 2 2 (by decide), F.zero 2 5 (by decide)] at ev2_5
    have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
    have hom5_eq : oblX6 x 5 * omega5 x = oblX0 x 5 + oblX2 x 5 - 1 := by
      simp only [omega5]; field_simp
    have h2_id : oblX6 x 5 * (F.f 2 (x 6) - (1 + omega5 x) * F.f 2 (x 1)) = 0 := by
      linear_combination -ev2_5 - F.f 2 (x 1) * hom5_eq
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2_id).resolve_left hc5.ne')
  have ev2_3 := fac_eval F 2 3
  rw [F.zero 2 0 (by decide), F.zero 2 2 (by decide), hf2_6] at ev2_3
  have hb3 : oblX2 x 3 = oblX0 x 3 * omega3 x + (1 - oblX6 x 3) := by linarith [eq3 F]
  have h3 : F.f 2 (x 3) < 0 := F.neg 2 3 (by decide)
  have h1 : F.f 2 (x 1) < 0 := F.neg 2 1 (by decide)
  have hid : F.f 2 (x 3) = F.f 2 (x 1) *
      (oblX6 x 3 * (1 + omega5 x) - oblX0 x 3 * (1 + omega3 x)) := by
    rw [ev2_3, hb3]; ring
  rw [hid] at h3
  by_contra hn
  push Not at hn
  nlinarith [mul_nonneg_of_nonpos_of_nonpos h1.le hn]

/-- **Monotone signs along the pencil, part 1** (from `w63_syzygy`): on `c3 < 1`, a vertex-pair
difference that is positive at `w63` and at `u27` is positive at `u07`. -/
theorem sign_u07_of_w63_u27 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (hc3 : oblX6 x 3 < 1) (b : ℝ³) (hw : 0 < ⟪b, x 3 - x 6⟫) (h27 : 0 < ⟪b, u27 x⟫) :
    0 < ⟪b, u07 x⟫ := by
  have hom3 : 0 < omega3 x := hC.1
  have hom5 : 0 < omega5 x := hC.2.2.1
  have s := congrArg (fun w => ⟪b, w⟫) (w63_syzygy F)
  simp only [inner_add_right, real_inner_smul_right] at s
  have hmu : 0 < (omega3 x + 1) * oblX0 x 3 + (omega5 x + 1) * (1 - oblX6 x 3) := by
    have ha3 : 0 < oblX0 x 3 := (type24OfFac F).X0_pos (v := 3) (by decide)
    have : 0 < 1 - oblX6 x 3 := sub_pos.mpr hc3
    positivity
  have ht : 0 < 1 - oblX6 x 3 := sub_pos.mpr hc3
  by_contra hn
  push Not at hn
  nlinarith [mul_pos (by linarith : (0:ℝ) < omega3 x + 1) hw, mul_pos ht h27,
    mul_nonpos_of_nonneg_of_nonpos hmu.le hn]

/-- **Monotone signs, part 2** (from `syz_E23`): on `0 < c3 < 1`, positive at `E23` and at `w63` gives
positive at `u07`. -/
theorem sign_u07_of_E23_w63 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hc3 : oblX6 x 3 < 1) (hc3p : 0 < oblX6 x 3) (b : ℝ³)
    (hE : 0 < ⟪b, x 3 - x 2⟫) (hw : 0 < ⟪b, x 3 - x 6⟫) : 0 < ⟪b, u07 x⟫ := by
  have ha3 : 0 < oblX0 x 3 := (type24OfFac F).X0_pos (v := 3) (by decide)
  have s := congrArg (fun w => ⟪b, w⟫) (syz_E23 F)
  simp only [inner_add_right, real_inner_smul_right] at s
  have ht : 0 < 1 - oblX6 x 3 := sub_pos.mpr hc3
  by_contra hn
  push Not at hn
  nlinarith [mul_pos ht hE, mul_pos hc3p hw, mul_nonpos_of_nonneg_of_nonpos ha3.le hn]

/-- **Monotone signs, part 3** (from `syz_u27`): on `0 < c3`, positive at `u07` and at `E23` gives
positive at `u27`. -/
theorem sign_u27_of_u07_E23 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (hc3p : 0 < oblX6 x 3) (b : ℝ³)
    (h07 : 0 < ⟪b, u07 x⟫) (hE : 0 < ⟪b, x 3 - x 2⟫) : 0 < ⟪b, u27 x⟫ := by
  have hom3 : 0 < omega3 x := hC.1
  have hk := syz_u27_coef_pos F
  have s := congrArg (fun w => ⟪b, w⟫) (syz_u27 F)
  simp only [inner_add_right, real_inner_smul_right] at s
  by_contra hn
  push Not at hn
  nlinarith [mul_pos hk h07, mul_pos (by linarith : (0:ℝ) < 1 + omega3 x) hE,
    mul_nonpos_of_nonneg_of_nonpos hc3p.le hn]

/-- **Leaf O2** (OB1-free, `{u07:06 -, u27:06 +, w63:03 +, pdx36}`, 27 of 39 pairs): degree 1. -/
theorem leaf_O2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (hc3 : oblX6 x 3 < 1)
    (h07 : ⟪x 0 - x 6, u07 x⟫ < 0) (hw : 0 < ⟪x 0 - x 3, x 3 - x 6⟫)
    (h27 : 0 < ⟪x 0 - x 6, u27 x⟫) : False := by
  have T := type24OfFac F
  have hne : x 3 - x 6 ≠ 0 := sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide)
  have hsq := real_inner_self_pos.mpr hne
  have e : x 0 - x 6 = (x 0 - x 3) + (x 3 - x 6) := by abel
  have hw' : 0 < ⟪x 0 - x 6, x 3 - x 6⟫ := by rw [e, inner_add_left]; linarith
  linarith [sign_u07_of_w63_u27 F hC hc3 (x 0 - x 6) hw' h27]

/-! ### Stratum `c3 = 1` case lemmas (`strat_A`..`strat_C`, `strat_A2`, `strat_B2`) -/

/-- Stratum case A (`min(z0, z6) > max(z2, z4)` part used: `z0 > z2, z0 > z4, z6 > z4`). -/
theorem strat_A (a3 om3 a4 c4 h4 W D k : ℝ) (ha3 : 0 < a3) (hom : 0 < om3 + 1)
    (hc4 : c4 ≤ 1) (hc4p : 0 < c4) (hh : 0 ≤ (c4 - 1) * (om3 + 1) + h4)
    (hs : 0 ≤ a4 * (om3 + 1) - h4) (hW : 0 < W)
    (h02 : 0 < W + a3 * (1 + om3) * k)
    (h04 : a4 * W + a3 * c4 * D + a3 * h4 * k < W + a3 * (1 + om3) * k)
    (h64 : a4 * W + a3 * c4 * D + a3 * h4 * k < a3 * D) : False := by
  nlinarith [mul_nonneg (mul_nonneg ha3.le hh) h02.le, mul_nonneg (mul_nonneg ha3.le
    (mul_nonneg (sub_nonneg.mpr hc4) hom.le)) (sub_pos.mpr h04).le,
    mul_pos (mul_pos (mul_pos ha3 hc4p) hom) (sub_pos.mpr h64), mul_nonneg hs hW.le]

/-- Stratum case B (`z2 > z0, z4 > z0, z4 > z3`). -/
theorem strat_B (a3 om3 a4 c4 h4 W D k : ℝ) (ha3 : 0 < a3) (hom : 0 < om3 + 1)
    (hc4 : c4 ≤ 1) (hc4p : 0 < c4) (hh : 0 ≤ (c4 - 1) * (om3 + 1) + h4)
    (hs : 0 ≤ (om3 + 1) * (a3 * c4 - a4) + h4) (hW : 0 < W)
    (h20 : W + a3 * (1 + om3) * k < 0)
    (h40 : W + a3 * (1 + om3) * k < a4 * W + a3 * c4 * D + a3 * h4 * k)
    (h43 : a3 * (D + W) < a4 * W + a3 * c4 * D + a3 * h4 * k) : False := by
  nlinarith [mul_nonneg (mul_nonneg ha3.le hh) (neg_pos.mpr h20).le, mul_nonneg (mul_nonneg ha3.le
    (mul_nonneg (sub_nonneg.mpr hc4) hom.le)) (sub_pos.mpr h40).le,
    mul_pos (mul_pos (mul_pos ha3 hc4p) hom) (sub_pos.mpr h43), mul_nonneg hs hW.le]

/-- Stratum case C (`z1 > z2 > z0`): multipliers `(a3 (1 + om3), a3, 1)` on `(z1 - z2, z2 - z0, W)`. -/
theorem strat_C (a3 om3 W k : ℝ) (ha3 : 0 < a3) (hom : 0 < om3 + 1) (hW : 0 < W)
    (h12 : 0 < k) (h20 : W + a3 * (1 + om3) * k < 0) : False := by
  nlinarith [mul_pos (mul_pos ha3 hom) h12]

/-! ### Rim / fail-set bridge at `c3 = 1` -/

/-- At `c3 = 1`, `w63` is a positive scalar multiple of `u07`. -/
theorem w63_eq_smul_u07 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (hc3 : oblX6 x 3 = 1) : x 3 - x 6 = oblX0 x 3 • u07 x := by
  have hsyz := w63_syzygy F
  rw [hc3, sub_self] at hsyz
  simp only [zero_smul, add_zero, mul_zero] at hsyz
  have hom3 : 0 < omega3 x + 1 := by linarith [hC.1]
  have hmul : (omega3 x + 1) • ((x 3 - x 6) - oblX0 x 3 • u07 x) = 0 := by
    rw [smul_sub, ← smul_assoc, smul_eq_mul, hsyz, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hmul).resolve_left hom3.ne')

/-- Facet inner products at `w63 = x 3 - x 6` on `c3 = 1`:
facets `0` (`012`), `7` (`236`), `8` (`346`) are edge-on (`= 0`);
facets `1, 4, 5` are `< 0` and facets `2, 3, 6` are `> 0`. -/
theorem w63_facings_c3eq1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (hc3 : oblX6 x 3 = 1) :
    ⟪F.N 0, x 3 - x 6⟫ = 0 ∧ ⟪F.N 1, x 3 - x 6⟫ < 0 ∧ 0 < ⟪F.N 2, x 3 - x 6⟫ ∧
    0 < ⟪F.N 3, x 3 - x 6⟫ ∧ ⟪F.N 4, x 3 - x 6⟫ < 0 ∧ ⟪F.N 5, x 3 - x 6⟫ < 0 ∧
    0 < ⟪F.N 6, x 3 - x 6⟫ ∧ ⟪F.N 7, x 3 - x 6⟫ = 0 ∧ ⟪F.N 8, x 3 - x 6⟫ = 0 := by
  have T := type24OfFac F
  have hN : ∀ t, ⟪F.N t, x 3 - x 6⟫ = F.f t (x 3) - F.f t (x 6) :=
    fun t => (F.hN t (x 3) (x 6)).symm
  have hf0 : ⟪F.N 0, x 3 - x 6⟫ = 0 := by
    have ev0_3 := fac_eval F 0 3
    rw [F.zero 0 0 (by decide), F.zero 0 1 (by decide), F.zero 0 2 (by decide), hc3] at ev0_3
    rw [hN 0]; linarith
  have hf2 : 0 < ⟪F.N 2, x 3 - x 6⟫ := by
    have hf2_6 : F.f 2 (x 6) = (1 + omega5 x) * F.f 2 (x 1) := by
      have ev2_5 := fac_eval F 2 5
      rw [F.zero 2 0 (by decide), F.zero 2 2 (by decide), F.zero 2 5 (by decide)] at ev2_5
      have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
      have hom5_eq : oblX6 x 5 * omega5 x = oblX0 x 5 + oblX2 x 5 - 1 := by
        simp only [omega5]; field_simp
      have h2_id : oblX6 x 5 * (F.f 2 (x 6) - (1 + omega5 x) * F.f 2 (x 1)) = 0 := by
        linear_combination -ev2_5 - F.f 2 (x 1) * hom5_eq
      exact sub_eq_zero.mp ((mul_eq_zero.mp h2_id).resolve_left hc5.ne')
    have ev2_3 := fac_eval F 2 3
    rw [F.zero 2 0 (by decide), F.zero 2 2 (by decide), hf2_6] at ev2_3
    have hb3 : oblX2 x 3 = oblX0 x 3 * omega3 x + (1 - oblX6 x 3) := by linarith [eq3 F]
    have hdiff : F.f 2 (x 3) - F.f 2 (x 6) =
        (-F.f 2 (x 1)) * (oblX0 x 3 * (1 + omega3 x)) := by
      rw [ev2_3, hf2_6, hb3, hc3]; ring
    rw [hN 2, hdiff]
    have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
    have hom3 : 0 < 1 + omega3 x := by linarith [hC.1]
    exact mul_pos (neg_pos.mpr (F.neg 2 1 (by decide))) (mul_pos ha3 hom3)
  refine ⟨hf0, ?_, hf2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hN 1, F.zero 1 6 (by decide), sub_zero]; exact F.neg 1 3 (by decide)
  · rw [hN 3, F.zero 3 3 (by decide), zero_sub]; exact neg_pos.mpr (F.neg 3 6 (by decide))
  · rw [hN 4, F.zero 4 6 (by decide), sub_zero]; exact F.neg 4 3 (by decide)
  · rw [hN 5, F.zero 5 6 (by decide), sub_zero]; exact F.neg 5 3 (by decide)
  · rw [hN 6, F.zero 6 3 (by decide), zero_sub]; exact neg_pos.mpr (F.neg 6 6 (by decide))
  · rw [hN 7, F.zero 7 3 (by decide), F.zero 7 6 (by decide), sub_self]
  · rw [hN 8, F.zero 8 3 (by decide), F.zero 8 6 (by decide), sub_self]

/-! ### Finite combinatorics for the 4 cycles on `{0, 1, 2, 3, 4, 6}` -/

private def c3eq1_ok4 (a b c d : Fin 6) : Bool :=
  !(Nat.blt a.1 b.1 && Nat.blt a.1 d.1 && Nat.blt c.1 b.1 && Nat.blt c.1 d.1) &&
  !(Nat.blt b.1 a.1 && Nat.blt b.1 c.1 && Nat.blt d.1 a.1 && Nat.blt d.1 c.1)

private def c3eq1_ok5 (a b c d e : Fin 6) : Bool :=
  c3eq1_ok4 a b c d && c3eq1_ok4 a b c e && c3eq1_ok4 a b d e &&
  c3eq1_ok4 a c d e && c3eq1_ok4 b c d e

private def c3eq1_ok6 (a b c d e f : Fin 6) : Bool :=
  c3eq1_ok4 a b c d && c3eq1_ok4 a b c e && c3eq1_ok4 a b c f &&
  c3eq1_ok4 a b d e && c3eq1_ok4 a b d f && c3eq1_ok4 a b e f &&
  c3eq1_ok4 a c d e && c3eq1_ok4 a c d f && c3eq1_ok4 a c e f &&
  c3eq1_ok4 a d e f && c3eq1_ok4 b c d e && c3eq1_ok4 b c d f &&
  c3eq1_ok4 b c e f && c3eq1_ok4 b d e f && c3eq1_ok4 c d e f

private def c3eq1_row (r0 r1 r2 r3 r4 r5 : Fin 6) : Bool :=
  let lt53 := Nat.blt r5.1 r3.1
  let coneA := Nat.blt r2.1 r0.1 && Nat.blt r4.1 r0.1 && Nat.blt r2.1 r5.1 && Nat.blt r4.1 r5.1
  let coneB := Nat.blt r0.1 r2.1 && Nat.blt r3.1 r2.1 && Nat.blt r0.1 r4.1 && Nat.blt r3.1 r4.1
  let coneC := Nat.blt r2.1 r1.1 && Nat.blt r0.1 r2.1 && Nat.blt r5.1 r2.1 && Nat.blt r2.1 r4.1
  let coneD := Nat.blt r2.1 r1.1 && Nat.blt r4.1 r2.1 && Nat.blt r0.1 r4.1 &&
    Nat.blt r5.1 r4.1 && Nat.blt r2.1 r3.1
  !(lt53 && !(coneA || coneB || coneC || coneD)) ||
    c3eq1_ok4 r0 r2 r5 r4 || c3eq1_ok5 r0 r2 r3 r5 r4 ||
    c3eq1_ok5 r0 r1 r2 r3 r4 || c3eq1_ok6 r0 r1 r2 r5 r3 r4

private def all6 (f : Fin 6 → Bool) : Bool :=
  f 0 && f 1 && f 2 && f 3 && f 4 && f 5

private theorem all6_eq_true {f : Fin 6 → Bool} (h : all6 f = true) (i : Fin 6) : f i = true := by
  dsimp only [all6] at h
  simp only [Bool.and_eq_true] at h
  fin_cases i <;> tauto

private def c3eq1_for1 (r0 r1 : Fin 6) : Bool :=
  if r1 == r0 then true else
  all6 fun r2 => if r2 == r0 || r2 == r1 then true else
  all6 fun r3 => if r3 == r0 || r3 == r1 || r3 == r2 then true else
  all6 fun r4 => if r4 == r0 || r4 == r1 || r4 == r2 || r4 == r3 then true else
  all6 fun r5 => if r5 == r0 || r5 == r1 || r5 == r2 || r5 == r3 || r5 == r4 then true else
    c3eq1_row r0 r1 r2 r3 r4 r5

private def c3eq1_lo (r0 : Fin 6) : Bool :=
  c3eq1_for1 r0 0 && c3eq1_for1 r0 1 && c3eq1_for1 r0 2

private def c3eq1_hi (r0 : Fin 6) : Bool :=
  c3eq1_for1 r0 3 && c3eq1_for1 r0 4 && c3eq1_for1 r0 5

private theorem c3eq1_lo0 : c3eq1_lo 0 = true := rfl
private theorem c3eq1_lo1 : c3eq1_lo 1 = true := rfl
private theorem c3eq1_lo2 : c3eq1_lo 2 = true := rfl
private theorem c3eq1_lo3 : c3eq1_lo 3 = true := rfl
private theorem c3eq1_lo4 : c3eq1_lo 4 = true := rfl
private theorem c3eq1_lo5 : c3eq1_lo 5 = true := rfl
private theorem c3eq1_hi0 : c3eq1_hi 0 = true := rfl
private theorem c3eq1_hi1 : c3eq1_hi 1 = true := rfl
private theorem c3eq1_hi2 : c3eq1_hi 2 = true := rfl
private theorem c3eq1_hi3 : c3eq1_hi 3 = true := rfl
private theorem c3eq1_hi4 : c3eq1_hi 4 = true := rfl
private theorem c3eq1_hi5 : c3eq1_hi 5 = true := rfl

attribute [irreducible] c3eq1_for1

private theorem bool_and3 {a b c : Bool} (h : (a && b && c) = true) :
    a = true ∧ b = true ∧ c = true := by
  cases a <;> cases b <;> cases c <;> simp_all

private theorem c3eq1_for1_eq_true (r0 r1 : Fin 6) : c3eq1_for1 r0 r1 = true := by
  have hlo : c3eq1_lo r0 = true := by
    fin_cases r0
    · exact c3eq1_lo0
    · exact c3eq1_lo1
    · exact c3eq1_lo2
    · exact c3eq1_lo3
    · exact c3eq1_lo4
    · exact c3eq1_lo5
  have hhi : c3eq1_hi r0 = true := by
    fin_cases r0
    · exact c3eq1_hi0
    · exact c3eq1_hi1
    · exact c3eq1_hi2
    · exact c3eq1_hi3
    · exact c3eq1_hi4
    · exact c3eq1_hi5
  obtain ⟨h0, h1, h2⟩ := bool_and3 hlo
  obtain ⟨h3, h4, h5⟩ := bool_and3 hhi
  fin_cases r1
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

private theorem if_eq_true {b p : Bool} (h : (if b = true then true else p) = true)
    (hb : b = false) : p = true := by
  simp [hb] at h; exact h

private theorem c3eq1_finite :
    ∀ r0 r1 r2 r3 r4 r5 : Fin 6,
      r0 ≠ r1 → r0 ≠ r2 → r0 ≠ r3 → r0 ≠ r4 → r0 ≠ r5 →
      r1 ≠ r2 → r1 ≠ r3 → r1 ≠ r4 → r1 ≠ r5 →
      r2 ≠ r3 → r2 ≠ r4 → r2 ≠ r5 →
      r3 ≠ r4 → r3 ≠ r5 → r4 ≠ r5 →
      r5.1 < r3.1 →
      ¬ ((r2.1 < r0.1 ∧ r4.1 < r0.1 ∧ r2.1 < r5.1 ∧ r4.1 < r5.1) ∨
         (r0.1 < r2.1 ∧ r3.1 < r2.1 ∧ r0.1 < r4.1 ∧ r3.1 < r4.1) ∨
         (r2.1 < r1.1 ∧ r0.1 < r2.1 ∧ r5.1 < r2.1 ∧ r2.1 < r4.1) ∨
         (r2.1 < r1.1 ∧ r4.1 < r2.1 ∧ r0.1 < r4.1 ∧ r5.1 < r4.1 ∧ r2.1 < r3.1)) →
      c3eq1_ok4 r0 r2 r5 r4 = true ∨
      c3eq1_ok5 r0 r2 r3 r5 r4 = true ∨
      c3eq1_ok5 r0 r1 r2 r3 r4 = true ∨
      c3eq1_ok6 r0 r1 r2 r5 r3 r4 = true := by
  intro r0 r1 r2 r3 r4 r5 h01 h02 h03 h04 h05 h12 h13 h14 h15 h23 h24 h25 h34 h35 h45 h53 hnc
  have h1 := c3eq1_for1_eq_true r0 r1
  unfold c3eq1_for1 at h1
  have hb1 : (r1 == r0) = false := beq_false_of_ne h01.symm
  have h1' := all6_eq_true (if_eq_true h1 hb1) r2
  have hb2 : (r2 == r0 || r2 == r1) = false := by simp [h02.symm, h12.symm]
  have h2' := all6_eq_true (if_eq_true h1' hb2) r3
  have hb3 : (r3 == r0 || r3 == r1 || r3 == r2) = false := by simp [h03.symm, h13.symm, h23.symm]
  have h3' := all6_eq_true (if_eq_true h2' hb3) r4
  have hb4 : (r4 == r0 || r4 == r1 || r4 == r2 || r4 == r3) = false := by
    simp [h04.symm, h14.symm, h24.symm, h34.symm]
  have h4' := all6_eq_true (if_eq_true h3' hb4) r5
  have hb5 : (r5 == r0 || r5 == r1 || r5 == r2 || r5 == r3 || r5 == r4) = false := by
    simp [h05.symm, h15.symm, h25.symm, h35.symm, h45.symm]
  have h := if_eq_true h4' hb5
  dsimp only [c3eq1_row] at h
  simp only [Bool.or_eq_true] at h
  rcases h with (((h | h) | h) | h) | h
  · simp only [Bool.not_eq_true', Bool.and_eq_false_iff, Bool.not_eq_false',
      Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | h
    · exact absurd (Nat.blt_eq.mpr h53) (Bool.eq_false_iff.mp h)
    · simp only [Nat.blt_eq, and_assoc, or_assoc] at h hnc
      exact absurd h hnc
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

/-! ### Cycles, rank clauses, tilts, and `c3eq1_closed` -/

private def v012346 : Fin 6 → Fin 7 := ![0, 1, 2, 3, 4, 6]

private def c_0264 : ZMod 4 → Fin 7 := ![0, 2, 6, 4]
private def c_02364 : ZMod 5 → Fin 7 := ![0, 2, 3, 6, 4]
private def c_01234 : ZMod 5 → Fin 7 := ![0, 1, 2, 3, 4]
private def c_012634 : ZMod 6 → Fin 7 := ![0, 1, 2, 6, 3, 4]

private theorem c_0264_inj : Function.Injective c_0264 := by decide
private theorem c_02364_inj : Function.Injective c_02364 := by decide
private theorem c_01234_inj : Function.Injective c_01234 := by decide
private theorem c_012634_inj : Function.Injective c_012634 := by decide

private theorem cyc_0264 : S0xCycUD s0x_S24 c_0264 {2, 3, 6, 7, 8} {0, 1, 4, 5} := by decide
private theorem cyc_02364 : S0xCycUD s0x_S24 c_02364 {2, 3, 6, 8} {0, 1, 4, 5, 7} := by decide
private theorem cyc_01234 : S0xCycUD s0x_S24 c_01234 {0, 2, 3, 6} {1, 4, 5, 7, 8} := by decide
private theorem cyc_012634 : S0xCycUD s0x_S24 c_012634 {0, 2, 3, 6, 7} {1, 4, 5, 8} := by decide

private theorem lexClause_of_rank6 {x : Fin 7 → ℝ³} {w d1 : ℝ³} (r : Fin 6 → Fin 6)
    (hinj : ∀ i j : Fin 6, i ≠ j → r i ≠ r j)
    (hmono : ∀ i j : Fin 6, r i < r j → ⟪x (v012346 i), w⟫ < ⟪x (v012346 j), w⟫)
    {va vb vc vd : Fin 7} {a b c d : Fin 6}
    (hva : va = v012346 a) (hvb : vb = v012346 b) (hvc : vc = v012346 c) (hvd : vd = v012346 d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (h : !(Nat.blt (r a).1 (r c).1 && Nat.blt (r a).1 (r d).1 &&
      Nat.blt (r b).1 (r c).1 && Nat.blt (r b).1 (r d).1) = true) :
    Minimality.GenQuad.LexClause (x va) (x vb) (x vc) (x vd) w d1 0 := by
  subst hva hvb hvc hvd
  apply Minimality.GenQuad.lexClause_of_notM
  rintro ⟨hwac, hwad, hwbc, hwbd⟩
  have h'' : (((r c).1 ≤ (r a).1 ∨ (r d).1 ≤ (r a).1) ∨ (r c).1 ≤ (r b).1) ∨ (r d).1 ≤ (r b).1 := by
    simpa [Nat.blt_eq] using h
  rcases h'' with ((h1 | h2) | h3) | h4
  · exact absurd (hmono c a (lt_of_le_of_ne h1 (hinj c a hac.symm))) (not_lt.mpr hwac)
  · exact absurd (hmono d a (lt_of_le_of_ne h2 (hinj d a had.symm))) (not_lt.mpr hwad)
  · exact absurd (hmono c b (lt_of_le_of_ne h3 (hinj c b hbc.symm))) (not_lt.mpr hwbc)
  · exact absurd (hmono d b (lt_of_le_of_ne h4 (hinj d b hbd.symm))) (not_lt.mpr hwbd)

private theorem tilt_0264_signs {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    let d1 : ℝ³ := (-F.f 0 (x 6)) • (-(x 4 - x 6)) +
      (|F.f 0 (x 4) - F.f 0 (x 6)| + 1) • (-(x 2 - x 6))
    ⟪F.N 0, d1⟫ < 0 ∧ 0 < ⟪F.N 7, d1⟫ ∧ 0 < ⟪F.N 8, d1⟫ := by
  intro d1
  have hf06 : 0 < -F.f 0 (x 6) := neg_pos.mpr (F.neg 0 6 (by decide))
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [d1]
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
      inner_neg_right, inner_neg_right, ← F.hN 0 (x 4) (x 6), ← F.hN 0 (x 2) (x 6),
      F.zero 0 2 (by decide), zero_sub]
    have hle : -(F.f 0 (x 4) - F.f 0 (x 6)) ≤ |F.f 0 (x 4) - F.f 0 (x 6)| :=
      neg_le_abs _
    nlinarith
  · dsimp only [d1]
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
      inner_neg_right, inner_neg_right, ← F.hN 7 (x 4) (x 6), ← F.hN 7 (x 2) (x 6),
      F.zero 7 6 (by decide), F.zero 7 2 (by decide), sub_zero, sub_self, neg_zero,
      mul_zero, add_zero]
    exact mul_pos hf06 (neg_pos.mpr (F.neg 7 4 (by decide)))
  · dsimp only [d1]
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
      inner_neg_right, inner_neg_right, ← F.hN 8 (x 4) (x 6), ← F.hN 8 (x 2) (x 6),
      F.zero 8 6 (by decide), F.zero 8 4 (by decide), sub_self, sub_zero, neg_zero,
      mul_zero, zero_add]
    exact mul_pos (by positivity) (neg_pos.mpr (F.neg 8 2 (by decide)))

private theorem close_k4 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    {c : ZMod 4 → Fin 7} {U Dn : Finset (Fin 9)}
    (hc : Function.Injective c) (hcyc : S0xCycUD s0x_S24 c U Dn)
    (w d1 : ℝ³)
    (hU : ∀ t ∈ U, LexPos3 ⟪F.N t, w⟫ ⟪F.N t, d1⟫ ⟪F.N t, (0 : ℝ³)⟫)
    (hD : ∀ t ∈ Dn, LexPos3 (-⟪F.N t, w⟫) (-⟪F.N t, d1⟫) (-⟪F.N t, (0 : ℝ³)⟫))
    (hA : Minimality.GenQuad.LexClause (x (c 1)) (x (c 3)) (x (c 0)) (x (c 2)) w d1 0)
    (hB : Minimality.GenQuad.LexClause (x (c 0)) (x (c 2)) (x (c 1)) (x (c 3)) w d1 0) :
    Minimality.Gen.LexAny F :=
  Minimality.GenQuad.lexAny_of_clauses F (k := 4) (by norm_num) hc hcyc w d1 0
    hU hD (Minimality.GenQuad.clauses_four (p := fun i => x (c i)) hA hB)

private theorem close_k5 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    {c : ZMod 5 → Fin 7} {U Dn : Finset (Fin 9)}
    (hc : Function.Injective c) (hcyc : S0xCycUD s0x_S24 c U Dn)
    (w d1 : ℝ³)
    (hU : ∀ t ∈ U, LexPos3 ⟪F.N t, w⟫ ⟪F.N t, d1⟫ ⟪F.N t, (0 : ℝ³)⟫)
    (hD : ∀ t ∈ Dn, LexPos3 (-⟪F.N t, w⟫) (-⟪F.N t, d1⟫) (-⟪F.N t, (0 : ℝ³)⟫))
    (hA0123 : Minimality.GenQuad.LexClause (x (c 1)) (x (c 3)) (x (c 0)) (x (c 2)) w d1 0)
    (hB0123 : Minimality.GenQuad.LexClause (x (c 0)) (x (c 2)) (x (c 1)) (x (c 3)) w d1 0)
    (hA0124 : Minimality.GenQuad.LexClause (x (c 1)) (x (c 4)) (x (c 0)) (x (c 2)) w d1 0)
    (hB0124 : Minimality.GenQuad.LexClause (x (c 0)) (x (c 2)) (x (c 1)) (x (c 4)) w d1 0)
    (hA0134 : Minimality.GenQuad.LexClause (x (c 1)) (x (c 4)) (x (c 0)) (x (c 3)) w d1 0)
    (hB0134 : Minimality.GenQuad.LexClause (x (c 0)) (x (c 3)) (x (c 1)) (x (c 4)) w d1 0)
    (hA0234 : Minimality.GenQuad.LexClause (x (c 2)) (x (c 4)) (x (c 0)) (x (c 3)) w d1 0)
    (hB0234 : Minimality.GenQuad.LexClause (x (c 0)) (x (c 3)) (x (c 2)) (x (c 4)) w d1 0)
    (hA1234 : Minimality.GenQuad.LexClause (x (c 2)) (x (c 4)) (x (c 1)) (x (c 3)) w d1 0)
    (hB1234 : Minimality.GenQuad.LexClause (x (c 1)) (x (c 3)) (x (c 2)) (x (c 4)) w d1 0) :
    Minimality.Gen.LexAny F :=
  Minimality.GenQuad.lexAny_of_clauses F (k := 5) (by norm_num) hc hcyc w d1 0
    hU hD (Minimality.GenQuad.clauses_five (p := fun i => x (c i))
      hA0123 hB0123 hA0124 hB0124 hA0134 hB0134 hA0234 hB0234 hA1234 hB1234)

private theorem close_k6 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    {c : ZMod 6 → Fin 7} {U Dn : Finset (Fin 9)}
    (hc : Function.Injective c) (hcyc : S0xCycUD s0x_S24 c U Dn)
    (w d1 : ℝ³)
    (hU : ∀ t ∈ U, LexPos3 ⟪F.N t, w⟫ ⟪F.N t, d1⟫ ⟪F.N t, (0 : ℝ³)⟫)
    (hD : ∀ t ∈ Dn, LexPos3 (-⟪F.N t, w⟫) (-⟪F.N t, d1⟫) (-⟪F.N t, (0 : ℝ³)⟫))
    (hA0123 : Minimality.GenQuad.LexClause (x (c 1)) (x (c 3)) (x (c 0)) (x (c 2)) w d1 0)
    (hB0123 : Minimality.GenQuad.LexClause (x (c 0)) (x (c 2)) (x (c 1)) (x (c 3)) w d1 0)
    (hA0124 : Minimality.GenQuad.LexClause (x (c 1)) (x (c 4)) (x (c 0)) (x (c 2)) w d1 0)
    (hB0124 : Minimality.GenQuad.LexClause (x (c 0)) (x (c 2)) (x (c 1)) (x (c 4)) w d1 0)
    (hA0125 : Minimality.GenQuad.LexClause (x (c 1)) (x (c 5)) (x (c 0)) (x (c 2)) w d1 0)
    (hB0125 : Minimality.GenQuad.LexClause (x (c 0)) (x (c 2)) (x (c 1)) (x (c 5)) w d1 0)
    (hA0134 : Minimality.GenQuad.LexClause (x (c 1)) (x (c 4)) (x (c 0)) (x (c 3)) w d1 0)
    (hB0134 : Minimality.GenQuad.LexClause (x (c 0)) (x (c 3)) (x (c 1)) (x (c 4)) w d1 0)
    (hA0135 : Minimality.GenQuad.LexClause (x (c 1)) (x (c 5)) (x (c 0)) (x (c 3)) w d1 0)
    (hB0135 : Minimality.GenQuad.LexClause (x (c 0)) (x (c 3)) (x (c 1)) (x (c 5)) w d1 0)
    (hA0145 : Minimality.GenQuad.LexClause (x (c 1)) (x (c 5)) (x (c 0)) (x (c 4)) w d1 0)
    (hB0145 : Minimality.GenQuad.LexClause (x (c 0)) (x (c 4)) (x (c 1)) (x (c 5)) w d1 0)
    (hA0234 : Minimality.GenQuad.LexClause (x (c 2)) (x (c 4)) (x (c 0)) (x (c 3)) w d1 0)
    (hB0234 : Minimality.GenQuad.LexClause (x (c 0)) (x (c 3)) (x (c 2)) (x (c 4)) w d1 0)
    (hA0235 : Minimality.GenQuad.LexClause (x (c 2)) (x (c 5)) (x (c 0)) (x (c 3)) w d1 0)
    (hB0235 : Minimality.GenQuad.LexClause (x (c 0)) (x (c 3)) (x (c 2)) (x (c 5)) w d1 0)
    (hA0245 : Minimality.GenQuad.LexClause (x (c 2)) (x (c 5)) (x (c 0)) (x (c 4)) w d1 0)
    (hB0245 : Minimality.GenQuad.LexClause (x (c 0)) (x (c 4)) (x (c 2)) (x (c 5)) w d1 0)
    (hA0345 : Minimality.GenQuad.LexClause (x (c 3)) (x (c 5)) (x (c 0)) (x (c 4)) w d1 0)
    (hB0345 : Minimality.GenQuad.LexClause (x (c 0)) (x (c 4)) (x (c 3)) (x (c 5)) w d1 0)
    (hA1234 : Minimality.GenQuad.LexClause (x (c 2)) (x (c 4)) (x (c 1)) (x (c 3)) w d1 0)
    (hB1234 : Minimality.GenQuad.LexClause (x (c 1)) (x (c 3)) (x (c 2)) (x (c 4)) w d1 0)
    (hA1235 : Minimality.GenQuad.LexClause (x (c 2)) (x (c 5)) (x (c 1)) (x (c 3)) w d1 0)
    (hB1235 : Minimality.GenQuad.LexClause (x (c 1)) (x (c 3)) (x (c 2)) (x (c 5)) w d1 0)
    (hA1245 : Minimality.GenQuad.LexClause (x (c 2)) (x (c 5)) (x (c 1)) (x (c 4)) w d1 0)
    (hB1245 : Minimality.GenQuad.LexClause (x (c 1)) (x (c 4)) (x (c 2)) (x (c 5)) w d1 0)
    (hA1345 : Minimality.GenQuad.LexClause (x (c 3)) (x (c 5)) (x (c 1)) (x (c 4)) w d1 0)
    (hB1345 : Minimality.GenQuad.LexClause (x (c 1)) (x (c 4)) (x (c 3)) (x (c 5)) w d1 0)
    (hA2345 : Minimality.GenQuad.LexClause (x (c 3)) (x (c 5)) (x (c 2)) (x (c 4)) w d1 0)
    (hB2345 : Minimality.GenQuad.LexClause (x (c 2)) (x (c 4)) (x (c 3)) (x (c 5)) w d1 0) :
    Minimality.Gen.LexAny F :=
  Minimality.GenQuad.lexAny_of_clauses F (k := 6) (by norm_num) hc hcyc w d1 0
    hU hD (Minimality.GenQuad.clauses_six (p := fun i => x (c i))
      hA0123 hB0123 hA0124 hB0124 hA0125 hB0125 hA0134 hB0134 hA0135 hB0135 hA0145 hB0145
      hA0234 hB0234 hA0235 hB0235 hA0245 hB0245 hA0345 hB0345 hA1234 hB1234 hA1235 hB1235
      hA1245 hB1245 hA1345 hB1345 hA2345 hB2345)


/-- strat A for c4 >= 1 (replaces the case c4 <= 1 of the old sample fact `hc4`). -/
theorem strat_A2 (a3 om3 a4 c4 h4 W D k : ℝ) (ha3 : 0 < a3) (hom : 0 < om3 + 1)
    (hc4 : 1 ≤ c4) (hh4 : 0 < h4) (hs : 0 ≤ a4 * (om3 + 1) - h4) (hW : 0 < W) (hD : 0 < D)
    (h02 : 0 < W + a3 * (1 + om3) * k)
    (h64 : a4 * W + a3 * c4 * D + a3 * h4 * k < a3 * D) : False := by
  nlinarith [mul_pos hh4 h02, mul_nonneg (mul_nonneg ha3.le (sub_nonneg.mpr hc4)) (mul_nonneg hom.le hD.le),
    mul_pos hom (sub_pos.mpr h64), mul_nonneg hs hW.le]

/-- strat B for c4 >= 1: rows z2>z0, z2>z3, z4>z3. -/
theorem strat_B2 (a3 om3 a4 c4 h4 W D k : ℝ) (ha3 : 0 < a3) (hom : 0 < om3 + 1)
    (hc4 : 1 ≤ c4) (hh4 : 0 < h4) (hs : 0 ≤ (om3 + 1) * (a3 * c4 - a4) + h4) (hW : 0 < W)
    (h20 : W + a3 * (1 + om3) * k < 0) (h32 : D + W < 0)
    (h43 : a3 * (D + W) < a4 * W + a3 * c4 * D + a3 * h4 * k) : False := by
  nlinarith [mul_pos hh4 (neg_pos.mpr h20), mul_nonneg (mul_nonneg ha3.le (sub_nonneg.mpr hc4)) (mul_nonneg hom.le (neg_pos.mpr h32).le),
    mul_pos hom (sub_pos.mpr h43), mul_nonneg hs hW.le]

/-- hh4_bd from CbarIn: (c4-1)(om3+1)+h4 = b4 (om3 om4 - 1) > 0. -/
theorem hh4_of_cbar {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) :
    0 < (oblX6 x 4 - 1) * (omega3 x + 1) + h236 x 4 := by
  have T := Minimality.T24.M4.type24OfFac F
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have e4 := Minimality.T24.M4.eq4 F
  obtain ⟨h3, h4, h5, hD⟩ := hC
  have hD' : 0 ≤ omega3 x * omega4 x * omega5 x - omega3 x - omega4 x - omega5 x - 2 := by
    unfold Delta24 at hD; linarith
  have hprod : 1 < omega3 x * omega4 x := by
    by_contra hcon; push Not at hcon
    nlinarith [mul_nonneg h5.le (sub_nonneg.mpr hcon), mul_pos h3 h4]
  have : (oblX6 x 4 - 1) * (omega3 x + 1) + h236 x 4 = oblX2 x 4 * (omega3 x * omega4 x - 1) := by
    unfold h236; nlinarith [e4]
  rw [this]; exact mul_pos hb4 (by linarith)


/-- Facet 025 at vertex 4 (extracted from the proof of `cross35_pos`): `a4 + b4 - om5 c4 < 1`. -/
theorem f025_x4_lt {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    oblX0 x 4 + oblX2 x 4 - omega5 x * oblX6 x 4 < 1 := by
  have T := Minimality.T24.M4.type24OfFac F
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hneg : F.f 2 (x 4) < 0 := F.neg 2 4 (by decide)
  have h1 : F.f 2 (x 1) < 0 := F.neg 2 1 (by decide)
  have h0 : F.f 2 (x 0) = 0 := F.zero 2 0 (by decide)
  have h2 : F.f 2 (x 2) = 0 := F.zero 2 2 (by decide)
  have h5' : F.f 2 (x 5) = 0 := F.zero 2 5 (by decide)
  have ev24 := Minimality.T24.M4.fac_eval F 2 4
  have ev25 := Minimality.T24.M4.fac_eval F 2 5
  rw [h0, h2] at ev24
  rw [h5', h0, h2] at ev25
  have h6_eq : F.f 2 (x 6) - F.f 2 (x 1) = F.f 2 (x 1) * omega5 x := by
    have := Minimality.T24.M4.eq5 F
    have hc5' : oblX6 x 5 ≠ 0 := hc5.ne'
    have h1' : F.f 2 (x 1) * (1 - oblX0 x 5 - oblX2 x 5) +
        oblX6 x 5 * (F.f 2 (x 6) - F.f 2 (x 1)) = 0 := by
      linear_combination -ev25
    have h2' : oblX6 x 5 * ((F.f 2 (x 6) - F.f 2 (x 1)) - F.f 2 (x 1) * omega5 x) = 0 := by
      linear_combination h1' + F.f 2 (x 1) * this
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2').resolve_left hc5')
  have e24 : (-F.f 2 (x 1)) * (oblX0 x 4 + oblX2 x 4 - omega5 x * oblX6 x 4 - 1) = F.f 2 (x 4) := by
    rw [ev24, h6_eq]; ring
  have hpos1 : 0 < -F.f 2 (x 1) := by linarith
  nlinarith

/-- `hs_B` is a region fact on `c3 = 1`: `(om3+1)(a3 c4 - a4) + h4 = t c5 (om5 c4 - a4 - b4 + 1) > 0`
(`t` the weight of `x5 - x0` in `x3 - x0 = s (x4 - x0) + t (x5 - x0)`, facet 025 at vertex 4). -/
theorem hsB_of_facets {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hc3 : oblX6 x 3 = 1) :
    0 < (omega3 x + 1) * (oblX0 x 3 * oblX6 x 4 - oblX0 x 4) + h236 x 4 := by
  have T := Minimality.T24.M4.type24OfFac F
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hd : det24 x ≠ 0 := T.det_ne
  obtain ⟨s, t, hs, ht, -, hdec⟩ := Minimality.T24.RimFromSigns.lemmaM_quad_decomp F
  have hdec1 : x 3 - x 1 = (1 - s - t) • (x 0 - x 1) + s • (x 4 - x 1) + t • (x 5 - x 1) := by
    calc x 3 - x 1 = (x 0 - x 1) + (x 3 - x 0) := by abel
      _ = (x 0 - x 1) + (s • (x 4 - x 0) + t • (x 5 - x 0)) := by rw [hdec]
      _ = (1 - s - t) • (x 0 - x 1) + s • (x 4 - x 1) + t • (x 5 - x 1) := by
          rw [show x 4 - x 0 = (x 4 - x 1) - (x 0 - x 1) from by abel,
              show x 5 - x 0 = (x 5 - x 1) - (x 0 - x 1) from by abel]
          module
  have hb3 : oblX2 x 3 = s * oblX2 x 4 + t * oblX2 x 5 := by
    simp only [oblX2]
    have hv : vol3 (x 0 - x 1) (x 3 - x 1) (x 6 - x 1) =
        s * vol3 (x 0 - x 1) (x 4 - x 1) (x 6 - x 1) +
        t * vol3 (x 0 - x 1) (x 5 - x 1) (x 6 - x 1) := by
      rw [hdec1]; simp only [vol3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [hv]; ring
  have hc3' : oblX6 x 3 = s * oblX6 x 4 + t * oblX6 x 5 := by
    simp only [oblX6]
    have hv : vol3 (x 0 - x 1) (x 2 - x 1) (x 3 - x 1) =
        s * vol3 (x 0 - x 1) (x 2 - x 1) (x 4 - x 1) +
        t * vol3 (x 0 - x 1) (x 2 - x 1) (x 5 - x 1) := by
      rw [hdec1]; simp only [vol3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [hv]; ring
  have ha3' : oblX0 x 3 = (1 - s - t) + s * oblX0 x 4 + t * oblX0 x 5 := by
    simp only [oblX0]
    have hv : vol3 (x 3 - x 1) (x 2 - x 1) (x 6 - x 1) =
        (1 - s - t) * det24 x + s * vol3 (x 4 - x 1) (x 2 - x 1) (x 6 - x 1) +
        t * vol3 (x 5 - x 1) (x 2 - x 1) (x 6 - x 1) := by
      rw [hdec1]; simp only [det24, vol3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [hv]; field_simp
  have hY := f025_x4_lt F
  have e5 := Minimality.T24.M4.eq5 F
  have hom3 : omega3 x * oblX0 x 3 = oblX2 x 3 + oblX6 x 3 - 1 := by
    simp only [omega3]; field_simp
  have hY' : 0 < omega5 x * oblX6 x 4 - (oblX0 x 4 + oblX2 x 4 - 1) := by linarith
  have key : ((omega3 x + 1) * (oblX0 x 3 * oblX6 x 4 - oblX0 x 4) + h236 x 4) =
      t * oblX6 x 5 * (omega5 x * oblX6 x 4 - (oblX0 x 4 + oblX2 x 4 - 1)) := by
    unfold h236
    rw [hc3] at hc3' hom3
    have h1 : s * oblX6 x 4 = 1 - t * oblX6 x 5 := by linarith
    linear_combination oblX6 x 4 * hom3 + oblX6 x 4 * hb3 + oblX6 x 4 * ha3' +
      (oblX0 x 4 + oblX2 x 4 - 1) * h1 + t * oblX6 x 4 * e5
  rw [key]; exact mul_pos (mul_pos ht hc5) hY'



/-- **Stratum `c3 = 1` closure** via `{w63}` (coinciding with `u07`).
Hypotheses `hc4`, `hh4_bd`, `hs_B`, `h1234` are sample facts on the `A2 band > 1 ∩ {c3 = 1}`
stratum (not provable from `F`, `CbarIn`, `hc3` alone; `h1234` is the `c3 = 1` specialization of
the `Resid24` bracket `[1234]`). `hgen` is the non-tie hypothesis on `{0, 1, 2, 3, 4, 6}` at `w63`. -/
theorem c3eq1_closed {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (hc3 : oblX6 x 3 = 1)
    (hgen : ∀ i ∈ ({0, 1, 2, 3, 4, 6} : Finset (Fin 7)),
      ∀ j ∈ ({0, 1, 2, 3, 4, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 3 - x 6⟫ ≠ ⟪x j, x 3 - x 6⟫) :
    Minimality.Gen.LexAny F := by
  classical
  have T := type24OfFac F
  have hh4_bd := (hh4_of_cbar F hC).le
  have hs_B := (hsB_of_facets F hc3).le
  have hfac := w63_facings_c3eq1 F hC hc3
  let w : ℝ³ := x 3 - x 6
  obtain ⟨r, hinj, hmono⟩ : ∃ r : Fin 6 → Fin 6,
      (∀ i j : Fin 6, i ≠ j → r i ≠ r j) ∧
      (∀ i j : Fin 6, r i < r j → ⟪x (v012346 i), w⟫ < ⟪x (v012346 j), w⟫) := by
    let r0 : Fin 6 → Fin 6 := fun i =>
      ⟨(Finset.univ.filter fun j : Fin 6 => ⟪x (v012346 j), w⟫ < ⟪x (v012346 i), w⟫).card, by
        have hsub : (Finset.univ.filter fun j : Fin 6 => ⟪x (v012346 j), w⟫ < ⟪x (v012346 i), w⟫) ⊂
            Finset.univ := by
          rw [Finset.ssubset_iff_subset_ne]
          refine ⟨Finset.filter_subset _ _, fun h => ?_⟩
          have hi : i ∈ Finset.univ.filter (fun j : Fin 6 => ⟪x (v012346 j), w⟫ < ⟪x (v012346 i), w⟫) := by
            rw [h]; exact Finset.mem_univ _
          exact lt_irrefl _ (Finset.mem_filter.mp hi).2
        simpa using Finset.card_lt_card hsub⟩
    have hv_mem : ∀ i : Fin 6, v012346 i ∈ ({0, 1, 2, 3, 4, 6} : Finset (Fin 7)) := by
      intro i; fin_cases i <;> decide
    have hv_inj : Function.Injective v012346 := by decide
    have hmono_rev : ∀ i j : Fin 6, ⟪x (v012346 i), w⟫ < ⟪x (v012346 j), w⟫ → r0 i < r0 j := by
      intro i j hij
      change (Finset.univ.filter fun k : Fin 6 => ⟪x (v012346 k), w⟫ < ⟪x (v012346 i), w⟫).card <
        (Finset.univ.filter fun k : Fin 6 => ⟪x (v012346 k), w⟫ < ⟪x (v012346 j), w⟫).card
      refine Finset.card_lt_card ?_
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨fun k hk => ?_, fun h => ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        exact lt_trans hk hij
      · have hi : i ∈ Finset.univ.filter (fun k : Fin 6 => ⟪x (v012346 k), w⟫ < ⟪x (v012346 j), w⟫) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩
        rw [← h] at hi
        exact lt_irrefl _ (Finset.mem_filter.mp hi).2
    have hinj0 : ∀ i j : Fin 6, i ≠ j → r0 i ≠ r0 j := by
      intro i j hij
      rcases lt_or_gt_of_ne (hgen (v012346 i) (hv_mem i) (v012346 j) (hv_mem j)
          (fun heq => hij (hv_inj heq))) with hlt | hgt
      · exact (hmono_rev i j hlt).ne
      · exact (hmono_rev j i hgt).ne'
    refine ⟨r0, hinj0, fun i j hlt => ?_⟩
    have hij : i ≠ j := fun heq => by subst heq; exact lt_irrefl _ hlt
    rcases lt_or_gt_of_ne (hgen (v012346 i) (hv_mem i) (v012346 j) (hv_mem j)
        (fun heq => hij (hv_inj heq))) with h | h
    · exact h
    · exact absurd (lt_trans hlt (hmono_rev j i h)) (lt_irrefl _)
  have h53 : (r 5).1 < (r 3).1 := by
    by_contra hle
    have hge : r 3 ≤ r 5 := not_lt.mp hle
    have hlt := hmono 3 5 (lt_of_le_of_ne hge (hinj 3 5 (by decide)))
    have hz36 : 0 < ⟪x 3 - x 6, w⟫ :=
      real_inner_self_pos.mpr (sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide))
    have hsub : ⟪x (v012346 5), w⟫ < ⟪x (v012346 3), w⟫ := by
      change ⟪x 6, w⟫ < ⟪x 3, w⟫
      rw [← sub_pos, ← inner_sub_left]; exact hz36
    linarith
  have hno_cone :
      ¬ (((r 2).1 < (r 0).1 ∧ (r 4).1 < (r 0).1 ∧ (r 2).1 < (r 5).1 ∧ (r 4).1 < (r 5).1) ∨
         ((r 0).1 < (r 2).1 ∧ (r 3).1 < (r 2).1 ∧ (r 0).1 < (r 4).1 ∧ (r 3).1 < (r 4).1) ∨
         ((r 2).1 < (r 1).1 ∧ (r 0).1 < (r 2).1 ∧ (r 5).1 < (r 2).1 ∧ (r 2).1 < (r 4).1) ∨
         ((r 2).1 < (r 1).1 ∧ (r 4).1 < (r 2).1 ∧ (r 0).1 < (r 4).1 ∧ (r 5).1 < (r 4).1 ∧
           (r 2).1 < (r 3).1)) := by
    have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
    have ha4 : 0 < oblX0 x 4 := T.X0_pos (v := 4) (by decide)
    have hc4p : 0 < oblX6 x 4 := T.X6_pos (v := 4) (by decide)
    have hom3 : 0 < omega3 x := hC.1
    have hom : 0 < omega3 x + 1 := by linarith
    have hh4 : 0 < h236 x 4 := by
      have ev7_4 := fac_eval F 7 4
      rw [F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at ev7_4
      have h7_1 : F.f 7 (x 1) < 0 := F.neg 7 1 (by decide)
      have h7_4 : F.f 7 (x 4) < 0 := F.neg 7 4 (by decide)
      have h10 : F.f 7 (x 0) = (omega3 x + 1) * F.f 7 (x 1) := by
        have ev7_3 := fac_eval F 7 3
        rw [F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at ev7_3
        have hb3 : oblX2 x 3 = oblX0 x 3 * omega3 x + (1 - oblX6 x 3) := by linarith [eq3 F]
        have hmul : oblX0 x 3 * (F.f 7 (x 0) - (omega3 x + 1) * F.f 7 (x 1)) = 0 := by
          linear_combination -ev7_3 + F.f 7 (x 1) * hb3
        exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left ha3.ne')
      have hid : F.f 7 (x 4) = F.f 7 (x 1) * h236 x 4 := by
        rw [ev7_4, h10]; dsimp only [h236]; ring
      rw [hid] at h7_4
      by_contra hn; push Not at hn
      nlinarith [mul_nonneg_of_nonpos_of_nonpos h7_1.le hn]
    have hs4 : 0 ≤ oblX0 x 4 * (omega3 x + 1) - h236 x 4 := by
      have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
      have hom4 : 0 < omega4 x := hC.2.1
      have hom4_eq : oblX2 x 4 * omega4 x = oblX0 x 4 + oblX6 x 4 - 1 := by
        simp only [omega4]; field_simp
      have hs_eq : oblX0 x 4 * (omega3 x + 1) - h236 x 4 = oblX2 x 4 * (1 + omega4 x) := by
        dsimp only [h236]; linarith
      rw [hs_eq]; exact (mul_pos hb4 (by linarith)).le
    let W : ℝ := ⟪w, w⟫
    let D : ℝ := ⟪x 6 - x 2, w⟫
    let k : ℝ := ⟪x 1 - x 2, w⟫
    have hW : 0 < W :=
      real_inner_self_pos.mpr (sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide))
    have hu07 : ⟪u07 x, w⟫ = W / oblX0 x 3 := by
      have hsmul := w63_eq_smul_u07 F hC hc3
      have hdot := congrArg (fun u => ⟪u, w⟫) hsmul
      rw [real_inner_smul_left] at hdot
      exact eq_div_of_mul_eq ha3.ne' (by linarith)
    have hz_id : ∀ v : Fin 7, oblX0 x 3 * ⟪x v - x 2, w⟫ =
        oblX0 x v * W + oblX0 x 3 * oblX6 x v * D + oblX0 x 3 * h236 x v * k := by
      intro v
      rw [pencil236_depth F v w, hu07]
      field_simp [ha3.ne']; rfl
    have hz0 : oblX0 x 3 * ⟪x 0 - x 2, w⟫ = W + oblX0 x 3 * (1 + omega3 x) * k := by
      rw [hz_id 0]
      have ha0 : oblX0 x 0 = 1 := by unfold oblX0; exact div_self T.det_ne
      have hc0 : oblX6 x 0 = 0 := by
        unfold oblX6 vol3; simp; left; ring
      have hh0 : h236 x 0 = 1 + omega3 x := by
        have hb0 : oblX2 x 0 = 0 := by
          unfold oblX2 vol3; simp; left; ring
        dsimp only [h236]; rw [ha0, hb0, hc0]; ring
      rw [ha0, hc0, hh0]; ring
    have hz1 : oblX0 x 3 * ⟪x 1 - x 2, w⟫ = oblX0 x 3 * k := by rfl
    have hz3 : oblX0 x 3 * ⟪x 3 - x 2, w⟫ = oblX0 x 3 * (D + W) := by
      rw [hz_id 3, hc3]
      have hh3 : h236 x 3 = 0 := by
        have hb3 : oblX2 x 3 = oblX0 x 3 * omega3 x + (1 - oblX6 x 3) := by linarith [eq3 F]
        dsimp only [h236]; rw [hb3, hc3]; ring
      rw [hh3]; ring
    have hz4 : oblX0 x 3 * ⟪x 4 - x 2, w⟫ =
        oblX0 x 4 * W + oblX0 x 3 * oblX6 x 4 * D + oblX0 x 3 * h236 x 4 * k := hz_id 4
    have hz6 : oblX0 x 3 * ⟪x 6 - x 2, w⟫ = oblX0 x 3 * D := by rfl
    have hlt_z : ∀ i j : Fin 6, (r i).1 < (r j).1 →
        oblX0 x 3 * ⟪x (v012346 i) - x 2, w⟫ < oblX0 x 3 * ⟪x (v012346 j) - x 2, w⟫ := by
      intro i j hij
      apply mul_lt_mul_of_pos_left _ ha3
      rw [inner_sub_left, inner_sub_left, sub_lt_sub_iff_right]
      exact hmono i j hij
    rintro (⟨h20, h40, h25, h45⟩ | ⟨h02, h32, h04, h34⟩ | ⟨h21, h02, h52, h24⟩ |
        ⟨h21, h42, h04, h54, h23⟩)
    · have p02 : 0 < W + oblX0 x 3 * (1 + omega3 x) * k := by
        have h := hlt_z 2 0 h20
        change oblX0 x 3 * ⟪x 2 - x 2, w⟫ < oblX0 x 3 * ⟪x 0 - x 2, w⟫ at h
        rw [sub_self, inner_zero_left, mul_zero, hz0] at h; exact h
      have p04 : oblX0 x 4 * W + oblX0 x 3 * oblX6 x 4 * D + oblX0 x 3 * h236 x 4 * k <
          W + oblX0 x 3 * (1 + omega3 x) * k := by
        have h := hlt_z 4 0 h40; change oblX0 x 3 * ⟪x 4 - x 2, w⟫ < oblX0 x 3 * ⟪x 0 - x 2, w⟫ at h
        rw [hz4, hz0] at h; exact h
      have p64 : oblX0 x 4 * W + oblX0 x 3 * oblX6 x 4 * D + oblX0 x 3 * h236 x 4 * k <
          oblX0 x 3 * D := by
        have h := hlt_z 4 5 h45; change oblX0 x 3 * ⟪x 4 - x 2, w⟫ < oblX0 x 3 * ⟪x 6 - x 2, w⟫ at h
        rw [hz4, hz6] at h; exact h
      rcases le_or_gt (oblX6 x 4) 1 with hc4 | hc4
      · exact strat_A (oblX0 x 3) (omega3 x) (oblX0 x 4) (oblX6 x 4) (h236 x 4) W D k
          ha3 hom hc4 hc4p hh4_bd hs4 hW p02 p04 p64
      · have hD : 0 < D := by
          have h := hlt_z 2 5 h25
          change oblX0 x 3 * ⟪x 2 - x 2, w⟫ < oblX0 x 3 * ⟪x 6 - x 2, w⟫ at h
          rw [sub_self, inner_zero_left, mul_zero, hz6] at h
          exact (mul_pos_iff_of_pos_left ha3).mp h
        exact strat_A2 (oblX0 x 3) (omega3 x) (oblX0 x 4) (oblX6 x 4) (h236 x 4) W D k
          ha3 hom hc4.le hh4 hs4 hW hD p02 p64
    · have p20 : W + oblX0 x 3 * (1 + omega3 x) * k < 0 := by
        have h := hlt_z 0 2 h02; change oblX0 x 3 * ⟪x 0 - x 2, w⟫ < oblX0 x 3 * ⟪x 2 - x 2, w⟫ at h
        rw [sub_self, inner_zero_left, mul_zero, hz0] at h; exact h
      have p40 : W + oblX0 x 3 * (1 + omega3 x) * k <
          oblX0 x 4 * W + oblX0 x 3 * oblX6 x 4 * D + oblX0 x 3 * h236 x 4 * k := by
        have h := hlt_z 0 4 h04; change oblX0 x 3 * ⟪x 0 - x 2, w⟫ < oblX0 x 3 * ⟪x 4 - x 2, w⟫ at h
        rw [hz0, hz4] at h; exact h
      have p43 : oblX0 x 3 * (D + W) <
          oblX0 x 4 * W + oblX0 x 3 * oblX6 x 4 * D + oblX0 x 3 * h236 x 4 * k := by
        have h := hlt_z 3 4 h34; change oblX0 x 3 * ⟪x 3 - x 2, w⟫ < oblX0 x 3 * ⟪x 4 - x 2, w⟫ at h
        rw [hz3, hz4] at h; exact h
      rcases le_or_gt (oblX6 x 4) 1 with hc4 | hc4
      · exact strat_B (oblX0 x 3) (omega3 x) (oblX0 x 4) (oblX6 x 4) (h236 x 4) W D k
          ha3 hom hc4 hc4p hh4_bd hs_B hW p20 p40 p43
      · have p32 : D + W < 0 := by
          have h := hlt_z 3 2 h32
          change oblX0 x 3 * ⟪x 3 - x 2, w⟫ < oblX0 x 3 * ⟪x 2 - x 2, w⟫ at h
          rw [sub_self, inner_zero_left, mul_zero, hz3] at h
          exact neg_of_mul_neg_right h ha3.le
        exact strat_B2 (oblX0 x 3) (omega3 x) (oblX0 x 4) (oblX6 x 4) (h236 x 4) W D k
          ha3 hom hc4.le hh4 hs_B hW p20 p32 p43
    · have p12 : 0 < k := by
        have h := hlt_z 2 1 h21; change oblX0 x 3 * ⟪x 2 - x 2, w⟫ < oblX0 x 3 * ⟪x 1 - x 2, w⟫ at h
        rw [sub_self, inner_zero_left, mul_zero] at h
        exact (mul_pos_iff_of_pos_left ha3).mp h
      have p20 : W + oblX0 x 3 * (1 + omega3 x) * k < 0 := by
        have h := hlt_z 0 2 h02; change oblX0 x 3 * ⟪x 0 - x 2, w⟫ < oblX0 x 3 * ⟪x 2 - x 2, w⟫ at h
        rw [sub_self, inner_zero_left, mul_zero, hz0] at h; exact h
      exact strat_C (oblX0 x 3) (omega3 x) W k ha3 hom hW p12 p20
    · have p12 : 0 < k := by
        have h := hlt_z 2 1 h21; change oblX0 x 3 * ⟪x 2 - x 2, w⟫ < oblX0 x 3 * ⟪x 1 - x 2, w⟫ at h
        rw [sub_self, inner_zero_left, mul_zero] at h
        exact (mul_pos_iff_of_pos_left ha3).mp h
      have p24 : oblX0 x 4 * W + oblX0 x 3 * oblX6 x 4 * D + oblX0 x 3 * h236 x 4 * k < 0 := by
        have h := hlt_z 4 2 h42; change oblX0 x 3 * ⟪x 4 - x 2, w⟫ < oblX0 x 3 * ⟪x 2 - x 2, w⟫ at h
        rw [sub_self, inner_zero_left, mul_zero, hz4] at h; exact h
      have p32 : 0 < D + W := by
        have h := hlt_z 2 3 h23; change oblX0 x 3 * ⟪x 2 - x 2, w⟫ < oblX0 x 3 * ⟪x 3 - x 2, w⟫ at h
        rw [sub_self, inner_zero_left, mul_zero, hz3] at h
        exact (mul_pos_iff_of_pos_left ha3).mp h
      have p46 : oblX0 x 3 * D <
          oblX0 x 4 * W + oblX0 x 3 * oblX6 x 4 * D + oblX0 x 3 * h236 x 4 * k := by
        have h := hlt_z 5 4 h54; change oblX0 x 3 * ⟪x 6 - x 2, w⟫ < oblX0 x 3 * ⟪x 4 - x 2, w⟫ at h
        rw [hz6, hz4] at h; exact h
      have p04 : W + oblX0 x 3 * (1 + omega3 x) * k <
          oblX0 x 4 * W + oblX0 x 3 * oblX6 x 4 * D + oblX0 x 3 * h236 x 4 * k := by
        have h := hlt_z 0 4 h04; change oblX0 x 3 * ⟪x 0 - x 2, w⟫ < oblX0 x 3 * ⟪x 4 - x 2, w⟫ at h
        rw [hz0, hz4] at h; exact h
      exact strat_C (oblX0 x 3) (omega3 x) W k ha3 hom hW p12 (lt_trans p04 p24)
  have hfin := c3eq1_finite (r 0) (r 1) (r 2) (r 3) (r 4) (r 5)
    (hinj 0 1 (by decide)) (hinj 0 2 (by decide)) (hinj 0 3 (by decide))
    (hinj 0 4 (by decide)) (hinj 0 5 (by decide)) (hinj 1 2 (by decide))
    (hinj 1 3 (by decide)) (hinj 1 4 (by decide)) (hinj 1 5 (by decide))
    (hinj 2 3 (by decide)) (hinj 2 4 (by decide)) (hinj 2 5 (by decide))
    (hinj 3 4 (by decide)) (hinj 3 5 (by decide)) (hinj 4 5 (by decide))
    h53 hno_cone
  have hU_of : ∀ (U : Finset (Fin 9)) (d1 : ℝ³),
      (∀ t ∈ U, (t = 0 → 0 < ⟪F.N 0, d1⟫) ∧ (t = 7 → 0 < ⟪F.N 7, d1⟫) ∧
        (t = 8 → 0 < ⟪F.N 8, d1⟫) ∧ t ≠ 1 ∧ t ≠ 4 ∧ t ≠ 5) →
      ∀ t ∈ U, LexPos3 ⟪F.N t, w⟫ ⟪F.N t, d1⟫ ⟪F.N t, (0 : ℝ³)⟫ := by
    intro U d1 hd1 t ht
    rcases hd1 t ht with ⟨h0, h7, h8, h1, h4, h5⟩
    fin_cases t
    · exact Or.inr ⟨hfac.1, Or.inl (h0 rfl)⟩
    · exact absurd rfl h1
    · exact Or.inl hfac.2.2.1
    · exact Or.inl hfac.2.2.2.1
    · exact absurd rfl h4
    · exact absurd rfl h5
    · exact Or.inl hfac.2.2.2.2.2.2.1
    · exact Or.inr ⟨hfac.2.2.2.2.2.2.2.1, Or.inl (h7 rfl)⟩
    · exact Or.inr ⟨hfac.2.2.2.2.2.2.2.2, Or.inl (h8 rfl)⟩
  have hD_of : ∀ (Dn : Finset (Fin 9)) (d1 : ℝ³),
      (∀ t ∈ Dn, (t = 0 → ⟪F.N 0, d1⟫ < 0) ∧ (t = 7 → ⟪F.N 7, d1⟫ < 0) ∧
        (t = 8 → ⟪F.N 8, d1⟫ < 0) ∧ t ≠ 2 ∧ t ≠ 3 ∧ t ≠ 6) →
      ∀ t ∈ Dn, LexPos3 (-⟪F.N t, w⟫) (-⟪F.N t, d1⟫) (-⟪F.N t, (0 : ℝ³)⟫) := by
    intro Dn d1 hd1 t ht
    rcases hd1 t ht with ⟨h0, h7, h8, h2, h3, h6⟩
    fin_cases t
    · exact Or.inr ⟨neg_eq_zero.mpr hfac.1, Or.inl (neg_pos.mpr (h0 rfl))⟩
    · exact Or.inl (neg_pos.mpr hfac.2.1)
    · exact absurd rfl h2
    · exact absurd rfl h3
    · exact Or.inl (neg_pos.mpr hfac.2.2.2.2.1)
    · exact Or.inl (neg_pos.mpr hfac.2.2.2.2.2.1)
    · exact absurd rfl h6
    · exact Or.inr ⟨neg_eq_zero.mpr hfac.2.2.2.2.2.2.2.1, Or.inl (neg_pos.mpr (h7 rfl))⟩
    · exact Or.inr ⟨neg_eq_zero.mpr hfac.2.2.2.2.2.2.2.2, Or.inl (neg_pos.mpr (h8 rfl))⟩
  let d0264 : ℝ³ := (-F.f 0 (x 6)) • (-(x 4 - x 6)) +
    (|F.f 0 (x 4) - F.f 0 (x 6)| + 1) • (-(x 2 - x 6))
  have hd0264 := tilt_0264_signs F
  rcases hfin with h | h | h | h
  · simp only [c3eq1_ok4, Bool.and_eq_true] at h
    exact close_k4 F c_0264_inj cyc_0264 w d0264
      (hU_of _ d0264 (fun t ht => by
        fin_cases t <;> simp at ht <;> exact ⟨fun h' => absurd h' (by decide),
          fun _ => hd0264.2.1, fun _ => hd0264.2.2, by decide, by decide, by decide⟩))
      (hD_of _ d0264 (fun t ht => by
        fin_cases t <;> simp at ht <;> exact ⟨fun _ => hd0264.1,
          fun h' => absurd h' (by decide), fun h' => absurd h' (by decide),
          by decide, by decide, by decide⟩))
      (lexClause_of_rank6 r hinj hmono (a := 2) (b := 4) (c := 0) (d := 5)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h.2)
      (lexClause_of_rank6 r hinj hmono (a := 0) (b := 5) (c := 2) (d := 4)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h.1)
  · simp only [c3eq1_ok5, c3eq1_ok4, Bool.and_eq_true] at h
    rcases h with ⟨⟨⟨⟨h0123, h0124⟩, h0134⟩, h0234⟩, h1234'⟩
    let d1 : ℝ³ := x 4 - x 2
    have h7 : ⟪F.N 7, d1⟫ < 0 := by
      dsimp only [d1]; rw [← F.hN 7 (x 4) (x 2), F.zero 7 2 (by decide), sub_zero]
      exact F.neg 7 4 (by decide)
    have h8 : 0 < ⟪F.N 8, d1⟫ := by
      dsimp only [d1]; rw [← F.hN 8 (x 4) (x 2), F.zero 8 4 (by decide), zero_sub]
      exact neg_pos.mpr (F.neg 8 2 (by decide))
    have h0 : ⟪F.N 0, d1⟫ < 0 := by
      dsimp only [d1]; rw [← F.hN 0 (x 4) (x 2), F.zero 0 2 (by decide), sub_zero]
      exact F.neg 0 4 (by decide)
    exact close_k5 F c_02364_inj cyc_02364 w d1
      (hU_of _ d1 (fun t ht => by
        fin_cases t <;> simp at ht <;> exact ⟨fun h' => absurd h' (by decide),
          fun h' => absurd h' (by decide), fun _ => h8, by decide, by decide, by decide⟩))
      (hD_of _ d1 (fun t ht => by
        fin_cases t <;> simp at ht <;> exact ⟨fun _ => h0, fun _ => h7,
          fun h' => absurd h' (by decide), by decide, by decide, by decide⟩))
      (lexClause_of_rank6 r hinj hmono (a := 2) (b := 5) (c := 0) (d := 3)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h0123.2)
      (lexClause_of_rank6 r hinj hmono (a := 0) (b := 3) (c := 2) (d := 5)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h0123.1)
      (lexClause_of_rank6 r hinj hmono (a := 2) (b := 4) (c := 0) (d := 3)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h0124.2)
      (lexClause_of_rank6 r hinj hmono (a := 0) (b := 3) (c := 2) (d := 4)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h0124.1)
      (lexClause_of_rank6 r hinj hmono (a := 2) (b := 4) (c := 0) (d := 5)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h0134.2)
      (lexClause_of_rank6 r hinj hmono (a := 0) (b := 5) (c := 2) (d := 4)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h0134.1)
      (lexClause_of_rank6 r hinj hmono (a := 3) (b := 4) (c := 0) (d := 5)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h0234.2)
      (lexClause_of_rank6 r hinj hmono (a := 0) (b := 5) (c := 3) (d := 4)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h0234.1)
      (lexClause_of_rank6 r hinj hmono (a := 3) (b := 4) (c := 2) (d := 5)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h1234'.2)
      (lexClause_of_rank6 r hinj hmono (a := 2) (b := 5) (c := 3) (d := 4)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h1234'.1)
  · simp only [c3eq1_ok5, c3eq1_ok4, Bool.and_eq_true] at h
    rcases h with ⟨⟨⟨⟨h0123, h0124⟩, h0134⟩, h0234⟩, h1234'⟩
    let d1 : ℝ³ := -d0264
    have h0 : 0 < ⟪F.N 0, d1⟫ := by dsimp only [d1]; rw [inner_neg_right]; exact neg_pos.mpr hd0264.1
    have h7 : ⟪F.N 7, d1⟫ < 0 := by dsimp only [d1]; rw [inner_neg_right]; exact neg_neg_of_pos hd0264.2.1
    have h8 : ⟪F.N 8, d1⟫ < 0 := by dsimp only [d1]; rw [inner_neg_right]; exact neg_neg_of_pos hd0264.2.2
    exact close_k5 F c_01234_inj cyc_01234 w d1
      (hU_of _ d1 (fun t ht => by
        fin_cases t <;> simp at ht <;> exact ⟨fun _ => h0, fun h' => absurd h' (by decide),
          fun h' => absurd h' (by decide), by decide, by decide, by decide⟩))
      (hD_of _ d1 (fun t ht => by
        fin_cases t <;> simp at ht <;> exact ⟨fun h' => absurd h' (by decide), fun _ => h7,
          fun _ => h8, by decide, by decide, by decide⟩))
      (lexClause_of_rank6 r hinj hmono (a := 1) (b := 3) (c := 0) (d := 2)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h0123.2)
      (lexClause_of_rank6 r hinj hmono (a := 0) (b := 2) (c := 1) (d := 3)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h0123.1)
      (lexClause_of_rank6 r hinj hmono (a := 1) (b := 4) (c := 0) (d := 2)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h0124.2)
      (lexClause_of_rank6 r hinj hmono (a := 0) (b := 2) (c := 1) (d := 4)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h0124.1)
      (lexClause_of_rank6 r hinj hmono (a := 1) (b := 4) (c := 0) (d := 3)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h0134.2)
      (lexClause_of_rank6 r hinj hmono (a := 0) (b := 3) (c := 1) (d := 4)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h0134.1)
      (lexClause_of_rank6 r hinj hmono (a := 2) (b := 4) (c := 0) (d := 3)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h0234.2)
      (lexClause_of_rank6 r hinj hmono (a := 0) (b := 3) (c := 2) (d := 4)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h0234.1)
      (lexClause_of_rank6 r hinj hmono (a := 2) (b := 4) (c := 1) (d := 3)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h1234'.2)
      (lexClause_of_rank6 r hinj hmono (a := 1) (b := 3) (c := 2) (d := 4)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h1234'.1)
  · simp only [c3eq1_ok6, c3eq1_ok4, Bool.and_eq_true] at h
    rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0123, h0124⟩, h0125⟩, h0134⟩, h0135⟩, h0145⟩,
      h0234⟩, h0235⟩, h0245⟩, h0345⟩, h1234'⟩, h1235⟩, h1245⟩, h1345⟩, h2345⟩
    let d1 : ℝ³ := x 2 - x 4
    have h0 : 0 < ⟪F.N 0, d1⟫ := by
      dsimp only [d1]; rw [← F.hN 0 (x 2) (x 4), F.zero 0 2 (by decide), zero_sub]
      exact neg_pos.mpr (F.neg 0 4 (by decide))
    have h7 : 0 < ⟪F.N 7, d1⟫ := by
      dsimp only [d1]; rw [← F.hN 7 (x 2) (x 4), F.zero 7 2 (by decide), zero_sub]
      exact neg_pos.mpr (F.neg 7 4 (by decide))
    have h8 : ⟪F.N 8, d1⟫ < 0 := by
      dsimp only [d1]; rw [← F.hN 8 (x 2) (x 4), F.zero 8 4 (by decide), sub_zero]
      exact F.neg 8 2 (by decide)
    exact close_k6 F c_012634_inj cyc_012634 w d1
      (hU_of _ d1 (fun t ht => by
        fin_cases t <;> simp at ht <;> exact ⟨fun _ => h0, fun _ => h7,
          fun h' => absurd h' (by decide), by decide, by decide, by decide⟩))
      (hD_of _ d1 (fun t ht => by
        fin_cases t <;> simp at ht <;> exact ⟨fun h' => absurd h' (by decide),
          fun h' => absurd h' (by decide), fun _ => h8, by decide, by decide, by decide⟩))
      (lexClause_of_rank6 r hinj hmono (a := 1) (b := 5) (c := 0) (d := 2)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h0123.2)
      (lexClause_of_rank6 r hinj hmono (a := 0) (b := 2) (c := 1) (d := 5)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h0123.1)
      (lexClause_of_rank6 r hinj hmono (a := 1) (b := 3) (c := 0) (d := 2)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h0124.2)
      (lexClause_of_rank6 r hinj hmono (a := 0) (b := 2) (c := 1) (d := 3)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h0124.1)
      (lexClause_of_rank6 r hinj hmono (a := 1) (b := 4) (c := 0) (d := 2)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h0125.2)
      (lexClause_of_rank6 r hinj hmono (a := 0) (b := 2) (c := 1) (d := 4)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h0125.1)
      (lexClause_of_rank6 r hinj hmono (a := 1) (b := 3) (c := 0) (d := 5)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h0134.2)
      (lexClause_of_rank6 r hinj hmono (a := 0) (b := 5) (c := 1) (d := 3)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h0134.1)
      (lexClause_of_rank6 r hinj hmono (a := 1) (b := 4) (c := 0) (d := 5)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h0135.2)
      (lexClause_of_rank6 r hinj hmono (a := 0) (b := 5) (c := 1) (d := 4)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h0135.1)
      (lexClause_of_rank6 r hinj hmono (a := 1) (b := 4) (c := 0) (d := 3)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h0145.2)
      (lexClause_of_rank6 r hinj hmono (a := 0) (b := 3) (c := 1) (d := 4)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h0145.1)
      (lexClause_of_rank6 r hinj hmono (a := 2) (b := 3) (c := 0) (d := 5)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h0234.2)
      (lexClause_of_rank6 r hinj hmono (a := 0) (b := 5) (c := 2) (d := 3)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h0234.1)
      (lexClause_of_rank6 r hinj hmono (a := 2) (b := 4) (c := 0) (d := 5)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h0235.2)
      (lexClause_of_rank6 r hinj hmono (a := 0) (b := 5) (c := 2) (d := 4)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h0235.1)
      (lexClause_of_rank6 r hinj hmono (a := 2) (b := 4) (c := 0) (d := 3)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h0245.2)
      (lexClause_of_rank6 r hinj hmono (a := 0) (b := 3) (c := 2) (d := 4)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h0245.1)
      (lexClause_of_rank6 r hinj hmono (a := 5) (b := 4) (c := 0) (d := 3)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h0345.2)
      (lexClause_of_rank6 r hinj hmono (a := 0) (b := 3) (c := 5) (d := 4)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h0345.1)
      (lexClause_of_rank6 r hinj hmono (a := 2) (b := 3) (c := 1) (d := 5)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h1234'.2)
      (lexClause_of_rank6 r hinj hmono (a := 1) (b := 5) (c := 2) (d := 3)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h1234'.1)
      (lexClause_of_rank6 r hinj hmono (a := 2) (b := 4) (c := 1) (d := 5)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h1235.2)
      (lexClause_of_rank6 r hinj hmono (a := 1) (b := 5) (c := 2) (d := 4)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h1235.1)
      (lexClause_of_rank6 r hinj hmono (a := 2) (b := 4) (c := 1) (d := 3)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h1245.2)
      (lexClause_of_rank6 r hinj hmono (a := 1) (b := 3) (c := 2) (d := 4)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h1245.1)
      (lexClause_of_rank6 r hinj hmono (a := 5) (b := 4) (c := 1) (d := 3)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h1345.2)
      (lexClause_of_rank6 r hinj hmono (a := 1) (b := 3) (c := 5) (d := 4)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h1345.1)
      (lexClause_of_rank6 r hinj hmono (a := 5) (b := 4) (c := 2) (d := 3)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h2345.2)
      (lexClause_of_rank6 r hinj hmono (a := 2) (b := 3) (c := 5) (d := 4)
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h2345.1)

end Minimality.T24.A20
