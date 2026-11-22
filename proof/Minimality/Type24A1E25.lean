module

public import Minimality.Type24A1Tie
public import Minimality.Type24SAT.K24.CornerOB1

/-!
# Type 24, region A1 off the tie (step T1): `e25_dom` and `a1_e25`

Proves `⟪x 5, x 5 - x 0⟫ ≤ ⟪x 2, x 5 - x 0⟫` (`z5(w05) ≤ z2(w05)`) on `A1` from `¬ LexAny F`,
the T25 rim facts (dispatched over the four T25 rims `0536`, `01635`, `05346`, `016435`), and
`H24K.SAT.OB1 x` (only needed on rim `016435` for clauses `14>63` and `14>65`).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.A1

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell
  Minimality.LexCell Minimality.Split Minimality.T24.M4 Minimality.T24.A7 Minimality.T24.A8
  Minimality.T24.A10 Minimality.T24.Q24 Minimality.T24 Minimality.GenQuad

private theorem e25_le_of_inner_nonneg {x : Fin 7 → ℝ³} (h : 0 ≤ ⟪x 0 - x 5, bT25 x⟫) :
    ⟪x 5, x 5 - x 0⟫ ≤ ⟪x 2, x 5 - x 0⟫ := by
  have heq : ⟪x 2, x 5 - x 0⟫ - ⟪x 5, x 5 - x 0⟫ = ⟪x 0 - x 5, bT25 x⟫ := by
    rw [← inner_sub_left, real_inner_comm]
    have h1 : x 2 - x 5 = -bT25 x := by unfold bT25; abel
    have h2 : x 5 - x 0 = -(x 0 - x 5) := by abel
    rw [h1, h2, inner_neg_left, inner_neg_right, neg_neg]
  linarith

private theorem e11_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    0 < ⟪x 2 - x 5, x 2 - x 5⟫ :=
  real_inner_self_pos.2 (sub_ne_zero.2 fun h => absurd (inj_of_fac F h) (by decide))

private theorem ob1_x21_bT25_neg {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha5 : 1 < oblX0 x 5) (h1 : 0 ≤ ⟪F.N 1, bT25 x⟫) (hO : H24K.SAT.OB1 x) :
    0 ≤ -⟪x 2 - x 1, bT25 x⟫ := by
  have T := type24OfFac F
  have hb5_pos : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc5_pos : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hb5_le : oblX2 x 5 ≤ 1 := by
    by_contra hgt; push Not at hgt
    exact absurd ((t25_016 F).2 hgt) (not_lt.2 h1)
  have hrep5 : bT25 x = oblX0 x 5 • (x 0 - x 1) + (oblX2 x 5 - 1) • (x 2 - x 1) +
      oblX6 x 5 • (x 6 - x 1) := by
    have hr := T.rep 5
    unfold bT25
    linear_combination (norm := module) hr
  have hd22 : 0 < ⟪x 2 - x 1, x 2 - x 1⟫ :=
    real_inner_self_pos.2 (sub_ne_zero.2 fun h => absurd (inj_of_fac F h) (by decide))
  rw [hrep5, inner_add_right, inner_add_right, inner_smul_right, inner_smul_right, inner_smul_right]
  have hal : 0 ≤ -⟪x 2 - x 1, x 0 - x 1⟫ := by
    rw [real_inner_comm]; exact neg_nonneg.2 hO.1
  have hga : 0 ≤ -⟪x 2 - x 1, x 6 - x 1⟫ := neg_nonneg.2 hO.2.2
  have hterm1 : 0 ≤ oblX0 x 5 * (-⟪x 2 - x 1, x 0 - x 1⟫) :=
    mul_nonneg (by linarith) hal
  have hterm2 : 0 ≤ (1 - oblX2 x 5) * ⟪x 2 - x 1, x 2 - x 1⟫ :=
    mul_nonneg (sub_nonneg.2 hb5_le) hd22.le
  have hterm3 : 0 ≤ oblX6 x 5 * (-⟪x 2 - x 1, x 6 - x 1⟫) :=
    mul_nonneg hc5_pos.le hga
  linarith

/-! ### Four rim-specific `e25_dom` lemmas -/

/-- `e25_dom` on rim `0536` (`⟪F.N 1, bT25 x⟫ < 0`, `0 ≤ ⟪F.N 8, bT25 x⟫`). -/
theorem e25_dom_0536 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (d1 d2 : ℝ³) {γ δ : ℝ}
    (hd1 : d1 = γ • (x 2 - x 5) + δ • (x 3 - x 5)) (hδ : 0 < δ)
    (hnLex : ¬ LexAny F)
    (h3 : 0 < ⟪F.N 3, bT25 x⟫) (h4 : 0 < ⟪F.N 4, bT25 x⟫) (h8 : 0 ≤ ⟪F.N 8, bT25 x⟫)
    (t1 : LexPos3 (-⟪F.N 1, bT25 x⟫) (-⟪F.N 1, d1⟫) (-⟪F.N 1, d2⟫)) (h7 : ⟪F.N 7, bT25 x⟫ < 0)
    (t2 : LexPos3 (-⟪F.N 2, bT25 x⟫) (-⟪F.N 2, d1⟫) (-⟪F.N 2, d2⟫))
    (t6 : LexPos3 (-⟪F.N 6, bT25 x⟫) (-⟪F.N 6, d1⟫) (-⟪F.N 6, d2⟫))
    (f0356 : FrontDet (x 0) (x 3) (x 5) (x 6) (bT25 x)) :
    ⟪x 5, x 5 - x 0⟫ ≤ ⟪x 2, x 5 - x 0⟫ := by
  have hk : ¬ GenQuad.LexClause (x 5) (x 6) (x 0) (x 3) (bT25 x) d1 d2 :=
    fun hc => hnLex (lexAny_T25_0536_tilt_le F d1 d2 hd1 hδ h3 h4 h8 t1 h7 t2 t6 f0356 hc)
  obtain ⟨⟨u1, -⟩, -, -, -⟩ := notClause hk
  exact e25_le_of_inner_nonneg (by rw [inner_sub_left]; linarith)

/-- Core `e25_dom` bound on rim `01635` given a contradiction from the 5 shared `LexClause`s. -/
private theorem e25_dom_01635_core {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    {c61 c62 c63 : ℝ}
    (hx6 : x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5))
    (hc61 : 0 < c61) (hc62 : 0 < c62) (hc63 : 1 ≤ c63)
    (d1 d2 : ℝ³)
    (hcontra : GenQuad.LexClause (x 1) (x 3) (x 0) (x 6) (bT25 x) d1 d2 →
      GenQuad.LexClause (x 1) (x 5) (x 0) (x 6) (bT25 x) d1 d2 →
      GenQuad.LexClause (x 1) (x 5) (x 0) (x 3) (bT25 x) d1 d2 →
      GenQuad.LexClause (x 6) (x 5) (x 0) (x 3) (bT25 x) d1 d2 →
      GenQuad.LexClause (x 1) (x 3) (x 6) (x 5) (bT25 x) d1 d2 → False) :
    ⟪x 5, x 5 - x 0⟫ ≤ ⟪x 2, x 5 - x 0⟫ := by
  refine e25_le_of_inner_nonneg ?_
  have E11 := e11_pos F
  have h25 : bT25 x = -(x 2 - x 5) := by unfold bT25; abel
  have h2b : ⟪x 2 - x 5, bT25 x⟫ = -⟪x 2 - x 5, x 2 - x 5⟫ := by
    rw [h25, inner_neg_right]
  have h63 : ⟪x 6 - x 3, bT25 x⟫ =
      -c61 * ⟪x 2 - x 5, x 2 - x 5⟫ + c62 * ⟪x 0 - x 5, bT25 x⟫ + (c63 - 1) * ⟪x 3 - x 5, bT25 x⟫ := by
    have : x 6 - x 3 = (x 6 - x 5) - (x 3 - x 5) := by abel
    rw [this, hx6, inner_sub_left, inner_add_left, inner_add_left,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, h2b]
    ring
  have h03 : ⟪x 0 - x 3, bT25 x⟫ = ⟪x 0 - x 5, bT25 x⟫ - ⟪x 3 - x 5, bT25 x⟫ := by
    rw [← inner_sub_left]; congr 1; abel
  have h53 : ⟪x 5 - x 3, bT25 x⟫ = -⟪x 3 - x 5, bT25 x⟫ := by
    rw [← inner_neg_left]; congr 1; abel
  by_cases k1 : GenQuad.LexClause (x 1) (x 3) (x 0) (x 6) (bT25 x) d1 d2
  swap
  · obtain ⟨-, -, ⟨u3, -⟩, ⟨u4, -⟩⟩ := notClause k1
    have h03_nonneg : 0 ≤ ⟪x 0 - x 3, bT25 x⟫ := by rw [inner_sub_left]; linarith
    have h63_nonneg : 0 ≤ ⟪x 6 - x 3, bT25 x⟫ := by rw [inner_sub_left]; linarith
    have hcomb : (c62 + c63 - 1) * ⟪x 0 - x 5, bT25 x⟫ =
        c61 * ⟪x 2 - x 5, x 2 - x 5⟫ + (c63 - 1) * ⟪x 0 - x 3, bT25 x⟫ + ⟪x 6 - x 3, bT25 x⟫ := by
      linear_combination -h63 - (c63 - 1) * h03
    have hrhs : 0 < c61 * ⟪x 2 - x 5, x 2 - x 5⟫ + (c63 - 1) * ⟪x 0 - x 3, bT25 x⟫ + ⟪x 6 - x 3, bT25 x⟫ := by
      nlinarith [mul_pos hc61 E11, mul_nonneg (sub_nonneg.2 hc63) h03_nonneg]
    have hc_pos : 0 < c62 + c63 - 1 := by linarith
    have hmul : 0 < (c62 + c63 - 1) * ⟪x 0 - x 5, bT25 x⟫ := by linarith
    exact (mul_pos_iff_of_pos_left hc_pos).1 hmul |>.le
  by_cases k5 : GenQuad.LexClause (x 1) (x 5) (x 0) (x 6) (bT25 x) d1 d2
  swap
  · obtain ⟨-, -, ⟨u1, -⟩, -⟩ := notClause k5
    rw [inner_sub_left]; linarith
  by_cases k3 : GenQuad.LexClause (x 1) (x 5) (x 0) (x 3) (bT25 x) d1 d2
  swap
  · obtain ⟨-, -, ⟨u1, -⟩, -⟩ := notClause k3
    rw [inner_sub_left]; linarith
  by_cases k4 : GenQuad.LexClause (x 6) (x 5) (x 0) (x 3) (bT25 x) d1 d2
  swap
  · obtain ⟨-, -, ⟨u1, -⟩, -⟩ := notClause k4
    rw [inner_sub_left]; linarith
  by_cases k2 : GenQuad.LexClause (x 1) (x 3) (x 6) (x 5) (bT25 x) d1 d2
  swap
  · obtain ⟨-, -, ⟨u3, -⟩, ⟨u4, -⟩⟩ := notClause k2
    have h63_nonneg : 0 ≤ ⟪x 6 - x 3, bT25 x⟫ := by rw [inner_sub_left]; linarith
    have h53_nonneg : 0 ≤ ⟪x 5 - x 3, bT25 x⟫ := by rw [inner_sub_left]; linarith
    have hcomb : c62 * ⟪x 0 - x 5, bT25 x⟫ =
        c61 * ⟪x 2 - x 5, x 2 - x 5⟫ + (c63 - 1) * ⟪x 5 - x 3, bT25 x⟫ + ⟪x 6 - x 3, bT25 x⟫ := by
      linear_combination -h63 - (c63 - 1) * h53
    have hrhs : 0 < c61 * ⟪x 2 - x 5, x 2 - x 5⟫ + (c63 - 1) * ⟪x 5 - x 3, bT25 x⟫ + ⟪x 6 - x 3, bT25 x⟫ := by
      nlinarith [mul_pos hc61 E11, mul_nonneg (sub_nonneg.2 hc63) h53_nonneg]
    have hmul : 0 < c62 * ⟪x 0 - x 5, bT25 x⟫ := by linarith
    exact (mul_pos_iff_of_pos_left hc62).1 hmul |>.le
  exact absurd (hcontra k1 k5 k3 k4 k2) id

private theorem ob1_1465_aux {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha5 : 1 < oblX0 x 5) (h1 : 0 ≤ ⟪F.N 1, bT25 x⟫) (hO : H24K.SAT.OB1 x)
    (h15 : 0 ≤ ⟪x 1 - x 5, bT25 x⟫) (h16 : 0 ≤ ⟪x 1 - x 6, bT25 x⟫) :
    0 ≤ ⟪x 0 - x 5, bT25 x⟫ := by
  have T := type24OfFac F
  have hb5_pos : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc5_pos : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have h21_nonneg := ob1_x21_bT25_neg F ha5 h1 hO
  have hid : x 5 - x 1 = oblX0 x 5 • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) +
      oblX6 x 5 • (x 6 - x 1) := by rw [T.rep 5]; abel
  have hx05_eq : oblX0 x 5 • (x 0 - x 5) =
      (oblX0 x 5 - 1) • (x 1 - x 5) + oblX2 x 5 • (-(x 2 - x 1)) + oblX6 x 5 • (x 1 - x 6) := by
    linear_combination (norm := module) -hid
  have hdot := congrArg (fun w => ⟪w, bT25 x⟫) hx05_eq
  simp only [inner_add_left, real_inner_smul_left, inner_neg_left] at hdot
  have hrhs : 0 ≤ (oblX0 x 5 - 1) * ⟪x 1 - x 5, bT25 x⟫ +
      oblX2 x 5 * (-⟪x 2 - x 1, bT25 x⟫) + oblX6 x 5 * ⟪x 1 - x 6, bT25 x⟫ := by
    nlinarith [mul_nonneg (sub_pos.2 ha5).le h15, mul_nonneg hb5_pos.le h21_nonneg, mul_nonneg hc5_pos.le h16]
  nlinarith

/-- `e25_dom` on rim `01635` (`0 < ⟪F.N 1, bT25 x⟫`, `0 ≤ ⟪F.N 8, bT25 x⟫`). -/
theorem e25_dom_01635 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (d1 d2 : ℝ³) {γ δ : ℝ}
    (hd1 : d1 = γ • (x 2 - x 5) + δ • (x 3 - x 5)) (hδ : 0 < δ)
    (hnLex : ¬ LexAny F) {c61 c62 c63 : ℝ}
    (hx6 : x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5))
    (hc61 : 0 < c61) (hc62 : 0 < c62) (hc63 : 1 ≤ c63)
    (t1 : LexPos3 ⟪F.N 1, bT25 x⟫ ⟪F.N 1, d1⟫ ⟪F.N 1, d2⟫)
    (h3 : 0 < ⟪F.N 3, bT25 x⟫) (h8 : 0 ≤ ⟪F.N 8, bT25 x⟫)
    (h0 : ⟪F.N 0, bT25 x⟫ < 0) (h5 : ⟪F.N 5, bT25 x⟫ < 0) (h7 : ⟪F.N 7, bT25 x⟫ < 0)
    (t2 : LexPos3 (-⟪F.N 2, bT25 x⟫) (-⟪F.N 2, d1⟫) (-⟪F.N 2, d2⟫))
    (t6 : LexPos3 (-⟪F.N 6, bT25 x⟫) (-⟪F.N 6, d1⟫) (-⟪F.N 6, d2⟫))
    (f0613 : FrontDet (x 0) (x 6) (x 1) (x 3) (bT25 x))
    (f0615 : FrontDet (x 0) (x 6) (x 1) (x 5) (bT25 x))
    (f0315 : FrontDet (x 0) (x 3) (x 1) (x 5) (bT25 x))
    (f0365 : FrontDet (x 0) (x 3) (x 6) (x 5) (bT25 x))
    (f6513 : FrontDet (x 6) (x 5) (x 1) (x 3) (bT25 x)) :
    ⟪x 5, x 5 - x 0⟫ ≤ ⟪x 2, x 5 - x 0⟫ :=
  e25_dom_01635_core F hx6 hc61 hc62 hc63 d1 d2 fun k1 k5 k3 k4 k2 =>
    hnLex (lexAny_T25_01635_tilt_le F d1 d2 hd1 hδ t1 h3 h8 h0 h5 h7 t2 t6
      f0613 f0615 f0315 f0365 f6513 k1 k5 k3 k4 k2)

/-- `e25_dom` on rim `01635` with flipped `(1, 3; 6, 5)` front (`0 < ⟪F.N 1, bT25 x⟫`, `0 ≤ ⟪F.N 8, bT25 x⟫`). -/
theorem e25_dom_01635_flip {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (d1 d2 : ℝ³) {γ δ : ℝ}
    (hd1 : d1 = γ • (x 2 - x 5) + δ • (x 3 - x 5)) (hδ : 0 < δ)
    (hnLex : ¬ LexAny F) (ha5 : 1 < oblX0 x 5) (hO : H24K.SAT.OB1 x) {c61 c62 c63 : ℝ}
    (hx6 : x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5))
    (hc61 : 0 < c61) (hc62 : 0 < c62) (hc63 : 1 ≤ c63)
    (h1 : 0 ≤ ⟪F.N 1, bT25 x⟫) (t1 : LexPos3 ⟪F.N 1, bT25 x⟫ ⟪F.N 1, d1⟫ ⟪F.N 1, d2⟫)
    (h3 : 0 < ⟪F.N 3, bT25 x⟫) (h8 : 0 ≤ ⟪F.N 8, bT25 x⟫)
    (h0 : ⟪F.N 0, bT25 x⟫ < 0) (h5 : ⟪F.N 5, bT25 x⟫ < 0) (h7 : ⟪F.N 7, bT25 x⟫ < 0)
    (t2 : LexPos3 (-⟪F.N 2, bT25 x⟫) (-⟪F.N 2, d1⟫) (-⟪F.N 2, d2⟫))
    (t6 : LexPos3 (-⟪F.N 6, bT25 x⟫) (-⟪F.N 6, d1⟫) (-⟪F.N 6, d2⟫))
    (f0613 : FrontDet (x 0) (x 6) (x 1) (x 3) (bT25 x))
    (f0615 : FrontDet (x 0) (x 6) (x 1) (x 5) (bT25 x))
    (f0315 : FrontDet (x 0) (x 3) (x 1) (x 5) (bT25 x))
    (f0365 : FrontDet (x 0) (x 3) (x 6) (x 5) (bT25 x))
    (f1365 : FrontDet (x 1) (x 3) (x 6) (x 5) (bT25 x)) :
    ⟪x 5, x 5 - x 0⟫ ≤ ⟪x 2, x 5 - x 0⟫ := by
  by_cases k6 : GenQuad.LexClause (x 6) (x 5) (x 1) (x 3) (bT25 x) d1 d2
  · exact e25_dom_01635_core F hx6 hc61 hc62 hc63 d1 d2 fun k1 k5 k3 k4 _ =>
      hnLex (lexAny_T25_01635_tilt_flip_le F d1 d2 hd1 hδ t1 h3 h8 h0 h5 h7 t2 t6
        f0613 f0615 f0315 f0365 f1365 k1 k5 k3 k4 k6)
  · obtain ⟨⟨u1, -⟩, -, ⟨u3, -⟩, -⟩ := notClause k6
    exact e25_le_of_inner_nonneg
      (ob1_1465_aux F ha5 h1 hO (by rw [inner_sub_left]; linarith) (by rw [inner_sub_left]; linarith))

/-- `e25_dom` on rim `05346` (`⟪F.N 1, bT25 x⟫ < 0`, `⟪F.N 8, bT25 x⟫ < 0`). -/
theorem e25_dom_05346 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (d1 d2 : ℝ³)
    (hnLex : ¬ LexAny F) {p4 q4 : ℝ}
    (hx4 : x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5)) (hp4 : 0 < p4) (hq4 : 1 ≤ q4)
    (hdet : Split.det3 (bT25 x) d1 d2 ≠ 0)
    (h3 : 0 < ⟪F.N 3, bT25 x⟫) (h4 : 0 < ⟪F.N 4, bT25 x⟫)
    (t1 : LexPos3 (-⟪F.N 1, bT25 x⟫) (-⟪F.N 1, d1⟫) (-⟪F.N 1, d2⟫)) (h8 : ⟪F.N 8, bT25 x⟫ < 0)
    (t2 : LexPos3 (-⟪F.N 2, bT25 x⟫) (-⟪F.N 2, d1⟫) (-⟪F.N 2, d2⟫))
    (t6 : LexPos3 (-⟪F.N 6, bT25 x⟫) (-⟪F.N 6, d1⟫) (-⟪F.N 6, d2⟫))
    (hX : GenQuad.CrossOf (x 0) (x 3) (x 5) (x 4))
    (f0356 : FrontDet (x 0) (x 3) (x 5) (x 6) (bT25 x))
    (f0456 : FrontDet (x 0) (x 4) (x 5) (x 6) (bT25 x))
    (f0436 : FrontDet (x 0) (x 4) (x 3) (x 6) (bT25 x))
    (f5436 : FrontDet (x 5) (x 4) (x 3) (x 6) (bT25 x)) :
    ⟪x 5, x 5 - x 0⟫ ≤ ⟪x 2, x 5 - x 0⟫ := by
  refine e25_le_of_inner_nonneg ?_
  have h43 : ⟪x 4 - x 3, bT25 x⟫ = p4 * ⟪x 0 - x 5, bT25 x⟫ + (q4 - 1) * ⟪x 3 - x 5, bT25 x⟫ := by
    have : x 4 - x 3 = (x 4 - x 5) - (x 3 - x 5) := by abel
    rw [this, hx4, inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_left]; ring
  have h03 : ⟪x 0 - x 3, bT25 x⟫ = ⟪x 0 - x 5, bT25 x⟫ - ⟪x 3 - x 5, bT25 x⟫ := by
    rw [← inner_sub_left]; congr 1; abel
  have h53 : ⟪x 5 - x 3, bT25 x⟫ = -⟪x 3 - x 5, bT25 x⟫ := by
    rw [← inner_neg_left]; congr 1; abel
  by_cases k1 : GenQuad.LexClause (x 5) (x 6) (x 0) (x 3) (bT25 x) d1 d2
  swap
  · obtain ⟨⟨u1, -⟩, -, -, -⟩ := notClause k1
    rw [inner_sub_left]; linarith
  by_cases k2 : GenQuad.LexClause (x 5) (x 6) (x 0) (x 4) (bT25 x) d1 d2
  swap
  · obtain ⟨⟨u1, -⟩, -, -, -⟩ := notClause k2
    rw [inner_sub_left]; linarith
  by_cases k3 : GenQuad.LexClause (x 3) (x 6) (x 0) (x 4) (bT25 x) d1 d2
  swap
  · obtain ⟨⟨u1, -⟩, ⟨u2, -⟩, -, -⟩ := notClause k3
    have h03_nonneg : 0 ≤ ⟪x 0 - x 3, bT25 x⟫ := by rw [inner_sub_left]; linarith
    have h43_nonneg : 0 ≤ ⟪x 4 - x 3, bT25 x⟫ := by rw [inner_sub_left]; linarith
    have hcomb : (p4 + q4 - 1) * ⟪x 0 - x 5, bT25 x⟫ =
        (q4 - 1) * ⟪x 0 - x 3, bT25 x⟫ + ⟪x 4 - x 3, bT25 x⟫ := by
      linear_combination -h43 - (q4 - 1) * h03
    have hrhs : 0 ≤ (q4 - 1) * ⟪x 0 - x 3, bT25 x⟫ + ⟪x 4 - x 3, bT25 x⟫ :=
      add_nonneg (mul_nonneg (sub_nonneg.2 hq4) h03_nonneg) h43_nonneg
    have hpq : 0 < p4 + q4 - 1 := by linarith
    have hmul : 0 ≤ (p4 + q4 - 1) * ⟪x 0 - x 5, bT25 x⟫ := by linarith
    exact (mul_nonneg_iff_of_pos_left hpq).1 hmul
  by_cases k4 : GenQuad.LexClause (x 3) (x 6) (x 5) (x 4) (bT25 x) d1 d2
  swap
  · obtain ⟨⟨u1, -⟩, ⟨u2, -⟩, -, -⟩ := notClause k4
    have h53_nonneg : 0 ≤ ⟪x 5 - x 3, bT25 x⟫ := by rw [inner_sub_left]; linarith
    have h43_nonneg : 0 ≤ ⟪x 4 - x 3, bT25 x⟫ := by rw [inner_sub_left]; linarith
    have hcomb : p4 * ⟪x 0 - x 5, bT25 x⟫ =
        (q4 - 1) * ⟪x 5 - x 3, bT25 x⟫ + ⟪x 4 - x 3, bT25 x⟫ := by
      linear_combination -h43 - (q4 - 1) * h53
    have hrhs : 0 ≤ (q4 - 1) * ⟪x 5 - x 3, bT25 x⟫ + ⟪x 4 - x 3, bT25 x⟫ :=
      add_nonneg (mul_nonneg (sub_nonneg.2 hq4) h53_nonneg) h43_nonneg
    have hmul : 0 ≤ p4 * ⟪x 0 - x 5, bT25 x⟫ := by linarith
    exact (mul_nonneg_iff_of_pos_left hp4).1 hmul
  exact absurd (lexAny_T25_05346_tilt_lex F d1 d2 hdet h3 h4 t1 h8 t2 t6 hX f0356 f0456 f0436 f5436 k1 k2 k3 k4) hnLex

/-- `e25_dom` on rim `016435` (`0 < ⟪F.N 1, bT25 x⟫`, `⟪F.N 8, bT25 x⟫ < 0`).
Uses `H24K.SAT.OB1 x` on clauses `m1463` and `m1465` via `ob1_x21_bT25_neg`. -/
theorem e25_dom_016435 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (d1 d2 : ℝ³)
    (hnLex : ¬ LexAny F) (ha5 : 1 < oblX0 x 5) (hO : H24K.SAT.OB1 x)
    {p4 q4 c61 c62 c63 : ℝ}
    (hx4 : x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5)) (hp4 : 0 < p4) (hq4 : 1 < q4)
    (hx6 : x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5))
    (hc61 : 0 < c61) (hc62 : 0 < c62) (hc63 : 1 ≤ c63) (hq4_63 : q4 ≤ c63)
    (hdet : Split.det3 (bT25 x) d1 d2 ≠ 0)
    (h1 : 0 ≤ ⟪F.N 1, bT25 x⟫) (t1 : LexPos3 ⟪F.N 1, bT25 x⟫ ⟪F.N 1, d1⟫ ⟪F.N 1, d2⟫)
    (h3 : 0 < ⟪F.N 3, bT25 x⟫) (h4 : 0 < ⟪F.N 4, bT25 x⟫)
    (h0 : ⟪F.N 0, bT25 x⟫ < 0) (h5 : ⟪F.N 5, bT25 x⟫ < 0)
    (h7 : ⟪F.N 7, bT25 x⟫ < 0) (h8 : ⟪F.N 8, bT25 x⟫ < 0)
    (t2 : LexPos3 (-⟪F.N 2, bT25 x⟫) (-⟪F.N 2, d1⟫) (-⟪F.N 2, d2⟫))
    (t6 : LexPos3 (-⟪F.N 6, bT25 x⟫) (-⟪F.N 6, d1⟫) (-⟪F.N 6, d2⟫))
    (hX : GenQuad.CrossOf (x 0) (x 3) (x 4) (x 5))
    (f0614 : FrontDet (x 0) (x 6) (x 1) (x 4) (bT25 x))
    (f0613 : FrontDet (x 0) (x 6) (x 1) (x 3) (bT25 x))
    (f0615 : FrontDet (x 0) (x 6) (x 1) (x 5) (bT25 x))
    (f0413 : FrontDet (x 0) (x 4) (x 1) (x 3) (bT25 x))
    (f0415 : FrontDet (x 0) (x 4) (x 1) (x 5) (bT25 x))
    (f0315 : FrontDet (x 0) (x 3) (x 1) (x 5) (bT25 x))
    (f0463 : FrontDet (x 0) (x 4) (x 6) (x 3) (bT25 x))
    (f0465 : FrontDet (x 0) (x 4) (x 6) (x 5) (bT25 x))
    (f0365 : FrontDet (x 0) (x 3) (x 6) (x 5) (bT25 x))
    (f1463 : FrontDet (x 1) (x 4) (x 6) (x 3) (bT25 x))
    (f1465 : FrontDet (x 1) (x 4) (x 6) (x 5) (bT25 x))
    (f6513 : FrontDet (x 6) (x 5) (x 1) (x 3) (bT25 x))
    (f4513 : FrontDet (x 4) (x 5) (x 1) (x 3) (bT25 x))
    (f4563 : FrontDet (x 4) (x 5) (x 6) (x 3) (bT25 x)) :
    ⟪x 5, x 5 - x 0⟫ ≤ ⟪x 2, x 5 - x 0⟫ := by
  refine e25_le_of_inner_nonneg ?_
  have E11 := e11_pos F
  have h25 : bT25 x = -(x 2 - x 5) := by unfold bT25; abel
  have h2b : ⟪x 2 - x 5, bT25 x⟫ = -⟪x 2 - x 5, x 2 - x 5⟫ := by
    rw [h25, inner_neg_right]
  have h63 : ⟪x 6 - x 3, bT25 x⟫ =
      -c61 * ⟪x 2 - x 5, x 2 - x 5⟫ + c62 * ⟪x 0 - x 5, bT25 x⟫ + (c63 - 1) * ⟪x 3 - x 5, bT25 x⟫ := by
    have : x 6 - x 3 = (x 6 - x 5) - (x 3 - x 5) := by abel
    rw [this, hx6, inner_sub_left, inner_add_left, inner_add_left,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, h2b]; ring
  have h43 : ⟪x 4 - x 3, bT25 x⟫ = p4 * ⟪x 0 - x 5, bT25 x⟫ + (q4 - 1) * ⟪x 3 - x 5, bT25 x⟫ := by
    have : x 4 - x 3 = (x 4 - x 5) - (x 3 - x 5) := by abel
    rw [this, hx4, inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_left]; ring
  have h03 : ⟪x 0 - x 3, bT25 x⟫ = ⟪x 0 - x 5, bT25 x⟫ - ⟪x 3 - x 5, bT25 x⟫ := by
    rw [← inner_sub_left]; congr 1; abel
  have h53 : ⟪x 5 - x 3, bT25 x⟫ = -⟪x 3 - x 5, bT25 x⟫ := by
    rw [← inner_neg_left]; congr 1; abel
  -- Helper for `0 ≤ ⟪x 1 - x 5, bT25 x⟫` and `0 ≤ ⟪x 1 - x 6, bT25 x⟫` via `OB1`:
  have ob1_1465 : 0 ≤ ⟪x 1 - x 5, bT25 x⟫ → 0 ≤ ⟪x 1 - x 6, bT25 x⟫ → 0 ≤ ⟪x 0 - x 5, bT25 x⟫ := by
    intro h15 h16
    have T := type24OfFac F
    have hb5_pos : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
    have hc5_pos : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
    have h21_pos := ob1_x21_bT25_neg F ha5 h1 hO
    have hid : x 5 - x 1 = oblX0 x 5 • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) +
        oblX6 x 5 • (x 6 - x 1) := by rw [T.rep 5]; abel
    have hx05_eq : oblX0 x 5 • (x 0 - x 5) =
        (oblX0 x 5 - 1) • (x 1 - x 5) + oblX2 x 5 • (-(x 2 - x 1)) + oblX6 x 5 • (x 1 - x 6) := by
      linear_combination (norm := module) -hid
    have hdot := congrArg (fun w => ⟪w, bT25 x⟫) hx05_eq
    simp only [inner_add_left, real_inner_smul_left, inner_neg_left] at hdot
    have hrhs : 0 ≤ (oblX0 x 5 - 1) * ⟪x 1 - x 5, bT25 x⟫ +
        oblX2 x 5 * (-⟪x 2 - x 1, bT25 x⟫) + oblX6 x 5 * ⟪x 1 - x 6, bT25 x⟫ := by
      nlinarith [mul_nonneg (sub_pos.2 ha5).le h15, mul_nonneg hb5_pos.le h21_pos, mul_nonneg hc5_pos.le h16]
    nlinarith
  -- Check the 14 clauses of `lexAny_T25_016435_tilt`:
  by_cases m0615 : GenQuad.LexClause (x 1) (x 5) (x 0) (x 6) (bT25 x) d1 d2
  swap
  · obtain ⟨-, -, ⟨u, -⟩, -⟩ := notClause m0615; rw [inner_sub_left]; linarith
  by_cases m0415 : GenQuad.LexClause (x 1) (x 5) (x 0) (x 4) (bT25 x) d1 d2
  swap
  · obtain ⟨-, -, ⟨u, -⟩, -⟩ := notClause m0415; rw [inner_sub_left]; linarith
  by_cases m0315 : GenQuad.LexClause (x 1) (x 5) (x 0) (x 3) (bT25 x) d1 d2
  swap
  · obtain ⟨-, -, ⟨u, -⟩, -⟩ := notClause m0315; rw [inner_sub_left]; linarith
  by_cases m0465 : GenQuad.LexClause (x 6) (x 5) (x 0) (x 4) (bT25 x) d1 d2
  swap
  · obtain ⟨-, -, ⟨u, -⟩, -⟩ := notClause m0465; rw [inner_sub_left]; linarith
  by_cases m0365 : GenQuad.LexClause (x 6) (x 5) (x 0) (x 3) (bT25 x) d1 d2
  swap
  · obtain ⟨-, -, ⟨u, -⟩, -⟩ := notClause m0365; rw [inner_sub_left]; linarith
  by_cases m0613 : GenQuad.LexClause (x 1) (x 3) (x 0) (x 6) (bT25 x) d1 d2
  swap
  · obtain ⟨-, -, ⟨u3, -⟩, ⟨u4, -⟩⟩ := notClause m0613
    have h03_nonneg : 0 ≤ ⟪x 0 - x 3, bT25 x⟫ := by rw [inner_sub_left]; linarith
    have h63_nonneg : 0 ≤ ⟪x 6 - x 3, bT25 x⟫ := by rw [inner_sub_left]; linarith
    have hcomb : (c62 + c63 - 1) * ⟪x 0 - x 5, bT25 x⟫ =
        c61 * ⟪x 2 - x 5, x 2 - x 5⟫ + (c63 - 1) * ⟪x 0 - x 3, bT25 x⟫ + ⟪x 6 - x 3, bT25 x⟫ := by
      linear_combination -h63 - (c63 - 1) * h03
    have hrhs : 0 < c61 * ⟪x 2 - x 5, x 2 - x 5⟫ + (c63 - 1) * ⟪x 0 - x 3, bT25 x⟫ + ⟪x 6 - x 3, bT25 x⟫ := by
      nlinarith [mul_pos hc61 E11, mul_nonneg (sub_nonneg.2 hc63) h03_nonneg]
    have hc_pos : 0 < c62 + c63 - 1 := by linarith
    have hmul : 0 < (c62 + c63 - 1) * ⟪x 0 - x 5, bT25 x⟫ := by linarith
    exact (mul_pos_iff_of_pos_left hc_pos).1 hmul |>.le
  by_cases m6513 : GenQuad.LexClause (x 1) (x 3) (x 6) (x 5) (bT25 x) d1 d2
  swap
  · obtain ⟨-, -, ⟨u3, -⟩, ⟨u4, -⟩⟩ := notClause m6513
    have h63_nonneg : 0 ≤ ⟪x 6 - x 3, bT25 x⟫ := by rw [inner_sub_left]; linarith
    have h53_nonneg : 0 ≤ ⟪x 5 - x 3, bT25 x⟫ := by rw [inner_sub_left]; linarith
    have hcomb : c62 * ⟪x 0 - x 5, bT25 x⟫ =
        c61 * ⟪x 2 - x 5, x 2 - x 5⟫ + (c63 - 1) * ⟪x 5 - x 3, bT25 x⟫ + ⟪x 6 - x 3, bT25 x⟫ := by
      linear_combination -h63 - (c63 - 1) * h53
    have hrhs : 0 < c61 * ⟪x 2 - x 5, x 2 - x 5⟫ + (c63 - 1) * ⟪x 5 - x 3, bT25 x⟫ + ⟪x 6 - x 3, bT25 x⟫ := by
      nlinarith [mul_pos hc61 E11, mul_nonneg (sub_nonneg.2 hc63) h53_nonneg]
    have hmul : 0 < c62 * ⟪x 0 - x 5, bT25 x⟫ := by linarith
    exact (mul_pos_iff_of_pos_left hc62).1 hmul |>.le
  by_cases m0413 : GenQuad.LexClause (x 1) (x 3) (x 0) (x 4) (bT25 x) d1 d2
  swap
  · obtain ⟨-, -, ⟨u3, -⟩, ⟨u4, -⟩⟩ := notClause m0413
    have h03_nonneg : 0 ≤ ⟪x 0 - x 3, bT25 x⟫ := by rw [inner_sub_left]; linarith
    have h43_nonneg : 0 ≤ ⟪x 4 - x 3, bT25 x⟫ := by rw [inner_sub_left]; linarith
    have hcomb : (p4 + q4 - 1) * ⟪x 0 - x 5, bT25 x⟫ =
        (q4 - 1) * ⟪x 0 - x 3, bT25 x⟫ + ⟪x 4 - x 3, bT25 x⟫ := by
      linear_combination -h43 - (q4 - 1) * h03
    have hrhs : 0 ≤ (q4 - 1) * ⟪x 0 - x 3, bT25 x⟫ + ⟪x 4 - x 3, bT25 x⟫ :=
      add_nonneg (mul_nonneg (by linarith) h03_nonneg) h43_nonneg
    have hpq : 0 < p4 + q4 - 1 := by linarith
    have hmul : 0 ≤ (p4 + q4 - 1) * ⟪x 0 - x 5, bT25 x⟫ := by linarith
    exact (mul_nonneg_iff_of_pos_left hpq).1 hmul
  by_cases m0463 : GenQuad.LexClause (x 6) (x 3) (x 0) (x 4) (bT25 x) d1 d2
  swap
  · obtain ⟨-, -, ⟨u3, -⟩, ⟨u4, -⟩⟩ := notClause m0463
    have h03_nonneg : 0 ≤ ⟪x 0 - x 3, bT25 x⟫ := by rw [inner_sub_left]; linarith
    have h43_nonneg : 0 ≤ ⟪x 4 - x 3, bT25 x⟫ := by rw [inner_sub_left]; linarith
    have hcomb : (p4 + q4 - 1) * ⟪x 0 - x 5, bT25 x⟫ =
        (q4 - 1) * ⟪x 0 - x 3, bT25 x⟫ + ⟪x 4 - x 3, bT25 x⟫ := by
      linear_combination -h43 - (q4 - 1) * h03
    have hrhs : 0 ≤ (q4 - 1) * ⟪x 0 - x 3, bT25 x⟫ + ⟪x 4 - x 3, bT25 x⟫ :=
      add_nonneg (mul_nonneg (by linarith) h03_nonneg) h43_nonneg
    have hpq : 0 < p4 + q4 - 1 := by linarith
    have hmul : 0 ≤ (p4 + q4 - 1) * ⟪x 0 - x 5, bT25 x⟫ := by linarith
    exact (mul_nonneg_iff_of_pos_left hpq).1 hmul
  by_cases m4513 : GenQuad.LexClause (x 1) (x 3) (x 4) (x 5) (bT25 x) d1 d2
  swap
  · obtain ⟨-, -, ⟨u3, -⟩, ⟨u4, -⟩⟩ := notClause m4513
    have h43_nonneg : 0 ≤ ⟪x 4 - x 3, bT25 x⟫ := by rw [inner_sub_left]; linarith
    have h53_nonneg : 0 ≤ ⟪x 5 - x 3, bT25 x⟫ := by rw [inner_sub_left]; linarith
    have hcomb : p4 * ⟪x 0 - x 5, bT25 x⟫ =
        (q4 - 1) * ⟪x 5 - x 3, bT25 x⟫ + ⟪x 4 - x 3, bT25 x⟫ := by
      linear_combination -h43 - (q4 - 1) * h53
    have hrhs : 0 ≤ (q4 - 1) * ⟪x 5 - x 3, bT25 x⟫ + ⟪x 4 - x 3, bT25 x⟫ :=
      add_nonneg (mul_nonneg (by linarith) h53_nonneg) h43_nonneg
    have hmul : 0 ≤ p4 * ⟪x 0 - x 5, bT25 x⟫ := by linarith
    exact (mul_nonneg_iff_of_pos_left hp4).1 hmul
  by_cases m4563 : GenQuad.LexClause (x 6) (x 3) (x 4) (x 5) (bT25 x) d1 d2
  swap
  · obtain ⟨-, -, ⟨u3, -⟩, ⟨u4, -⟩⟩ := notClause m4563
    have h43_nonneg : 0 ≤ ⟪x 4 - x 3, bT25 x⟫ := by rw [inner_sub_left]; linarith
    have h53_nonneg : 0 ≤ ⟪x 5 - x 3, bT25 x⟫ := by rw [inner_sub_left]; linarith
    have hcomb : p4 * ⟪x 0 - x 5, bT25 x⟫ =
        (q4 - 1) * ⟪x 5 - x 3, bT25 x⟫ + ⟪x 4 - x 3, bT25 x⟫ := by
      linear_combination -h43 - (q4 - 1) * h53
    have hrhs : 0 ≤ (q4 - 1) * ⟪x 5 - x 3, bT25 x⟫ + ⟪x 4 - x 3, bT25 x⟫ :=
      add_nonneg (mul_nonneg (by linarith) h53_nonneg) h43_nonneg
    have hmul : 0 ≤ p4 * ⟪x 0 - x 5, bT25 x⟫ := by linarith
    exact (mul_nonneg_iff_of_pos_left hp4).1 hmul
  by_cases m0614 : GenQuad.LexClause (x 1) (x 4) (x 0) (x 6) (bT25 x) d1 d2
  swap
  · obtain ⟨-, -, ⟨u3, -⟩, ⟨u4, -⟩⟩ := notClause m0614
    have h04_nonneg : 0 ≤ ⟪x 0 - x 4, bT25 x⟫ := by rw [inner_sub_left]; linarith
    have h64_nonneg : 0 ≤ ⟪x 6 - x 4, bT25 x⟫ := by rw [inner_sub_left]; linarith
    have hvec : (c63 - q4) • (x 0 - x 4) + q4 • (x 6 - x 4) =
        (q4 * c61) • (x 2 - x 5) + (c63 * (1 - p4) + q4 * (c62 - 1)) • (x 0 - x 5) := by
      have e04 : x 0 - x 4 = (x 0 - x 5) - (x 4 - x 5) := by abel
      have e64 : x 6 - x 4 = (x 6 - x 5) - (x 4 - x 5) := by abel
      rw [e04, e64, hx4, hx6]
      module
    have hN4 : 0 < c63 * (1 - p4) + q4 * (c62 - 1) := by
      have hdot4 := congrArg (fun w => ⟪F.N 4, w⟫) hvec
      have h04_z : ⟪F.N 4, x 0 - x 4⟫ = 0 := by
        rw [F.inner_sub, F.zero 4 0 (by decide), F.zero 4 4 (by decide), sub_self]
      have h64_z : ⟪F.N 4, x 6 - x 4⟫ = 0 := by
        rw [F.inner_sub, F.zero 4 6 (by decide), F.zero 4 4 (by decide), sub_self]
      have h25_4 : ⟪F.N 4, x 2 - x 5⟫ = -⟪F.N 4, bT25 x⟫ := by
        rw [h25, inner_neg_right, neg_neg]
      have h05_4 : ⟪F.N 4, x 0 - x 5⟫ = -F.f 4 (x 5) := by
        rw [F.inner_sub, F.zero 4 0 (by decide), zero_sub]
      simp only [inner_add_right, real_inner_smul_right, h04_z, h64_z, h25_4, h05_4, mul_zero, add_zero] at hdot4
      have hrhs4 : 0 < q4 * c61 * ⟪F.N 4, bT25 x⟫ :=
        mul_pos (mul_pos (by linarith) hc61) h4
      have hf45 : 0 < -F.f 4 (x 5) := neg_pos.2 (F.neg 4 5 (by decide))
      have hmul4 : 0 < (c63 * (1 - p4) + q4 * (c62 - 1)) * (-F.f 4 (x 5)) := by linarith
      exact (mul_pos_iff_of_pos_right hf45).1 hmul4
    have hdotb := congrArg (fun w => ⟪w, bT25 x⟫) hvec
    simp only [inner_add_left, real_inner_smul_left, h2b] at hdotb
    have hlhs : 0 ≤ (c63 - q4) * ⟪x 0 - x 4, bT25 x⟫ + q4 * ⟪x 6 - x 4, bT25 x⟫ :=
      add_nonneg (mul_nonneg (sub_nonneg.2 hq4_63) h04_nonneg) (mul_nonneg (by linarith) h64_nonneg)
    have hq4c61 : 0 < q4 * c61 * ⟪x 2 - x 5, x 2 - x 5⟫ :=
      mul_pos (mul_pos (by linarith) hc61) E11
    have hmul : 0 < (c63 * (1 - p4) + q4 * (c62 - 1)) * ⟪x 0 - x 5, bT25 x⟫ := by linarith
    exact (mul_pos_iff_of_pos_left hN4).1 hmul |>.le
  by_cases m1465 : GenQuad.LexClause (x 6) (x 5) (x 1) (x 4) (bT25 x) d1 d2
  swap
  · obtain ⟨⟨u1, -⟩, -, ⟨u3, -⟩, -⟩ := notClause m1465
    exact ob1_1465 (by rw [inner_sub_left]; linarith) (by rw [inner_sub_left]; linarith)
  by_cases m1463 : GenQuad.LexClause (x 6) (x 3) (x 1) (x 4) (bT25 x) d1 d2
  swap
  · obtain ⟨⟨u1, -⟩, -, ⟨u3, -⟩, ⟨u4, -⟩⟩ := notClause m1463
    have h16 : 0 ≤ ⟪x 1 - x 6, bT25 x⟫ := by rw [inner_sub_left]; linarith
    have h13 : 0 ≤ ⟪x 1 - x 3, bT25 x⟫ := by rw [inner_sub_left]; linarith
    have h43_nonneg : 0 ≤ ⟪x 4 - x 3, bT25 x⟫ := by rw [inner_sub_left]; linarith
    by_contra hneg; push Not at hneg
    have hmul3 : 0 < (q4 - 1) * ⟪x 3 - x 5, bT25 x⟫ := by
      linarith [mul_neg_of_pos_of_neg hp4 hneg]
    have h35_pos : 0 < ⟪x 3 - x 5, bT25 x⟫ :=
      (mul_pos_iff_of_pos_left (by linarith)).1 hmul3
    have h15 : 0 ≤ ⟪x 1 - x 5, bT25 x⟫ := by
      have : ⟪x 1 - x 5, bT25 x⟫ = ⟪x 1 - x 3, bT25 x⟫ + ⟪x 3 - x 5, bT25 x⟫ := by
        rw [← inner_add_left]; congr 1; abel
      linarith
    exact absurd (ob1_1465 h15 h16) (not_le.2 hneg)
  exact absurd (lexAny_T25_016435_tilt_lex F d1 d2 hdet t1 h3 h4 h0 h5 h7 h8 t2 t6 hX
    f0614 f0613 f0615 f0413 f0415 f0315 f0463 f0465 f0365 f1463 f1465 f6513 f4513 f4563
    m0614 m0613 m0615 m0413 m0415 m0315 m0463 m0465 m0365 m1463 m1465 m6513 m4513 m4563) hnLex

/-! ### Top-level `A1E25Sample` and `a1_e25` -/

/-- Minimal T25 sample-fact bundle for `a1_e25`: only the T25 fields of `A1TieSample`
(no `hq_sig1`, no T26 `FrontDet`s, and on rim `016435` only `q4 ≤ c63` and the 14 T25 `FrontDet`s). -/
structure A1E25Sample (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop where
  hc63 : F.f 2 (x 6) ≤ F.f 2 (x 3)
  h4 : ⟪F.N 1, bT25 x⟫ ≤ 0 ∨ ⟪F.N 8, bT25 x⟫ < 0 → 0 < ⟪F.N 4, bT25 x⟫
  t25_fronts_0536 : ⟪F.N 1, bT25 x⟫ ≤ 0 → 0 ≤ ⟪F.N 8, bT25 x⟫ →
    FrontDet (x 0) (x 3) (x 5) (x 6) (bT25 x)
  t25_fronts_05346 : ⟪F.N 1, bT25 x⟫ ≤ 0 → ⟪F.N 8, bT25 x⟫ < 0 →
    FrontDet (x 0) (x 3) (x 5) (x 6) (bT25 x) ∧
    FrontDet (x 0) (x 4) (x 5) (x 6) (bT25 x) ∧
    FrontDet (x 0) (x 4) (x 3) (x 6) (bT25 x) ∧
    FrontDet (x 5) (x 4) (x 3) (x 6) (bT25 x)
  t25_fronts_01635 : 0 ≤ ⟪F.N 1, bT25 x⟫ → 0 ≤ ⟪F.N 8, bT25 x⟫ →
    FrontDet (x 0) (x 6) (x 1) (x 3) (bT25 x) ∧
    FrontDet (x 0) (x 6) (x 1) (x 5) (bT25 x) ∧
    FrontDet (x 0) (x 3) (x 1) (x 5) (bT25 x) ∧
    FrontDet (x 0) (x 3) (x 6) (x 5) (bT25 x) ∧
    (FrontDet (x 6) (x 5) (x 1) (x 3) (bT25 x) ∨ FrontDet (x 1) (x 3) (x 6) (x 5) (bT25 x))
  t25_016435 : 0 ≤ ⟪F.N 1, bT25 x⟫ → ⟪F.N 8, bT25 x⟫ < 0 →
    (∀ {p4 q4 c61 c62 c63 : ℝ},
      x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5) →
      x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5) →
      q4 ≤ c63) ∧
    FrontDet (x 0) (x 6) (x 1) (x 4) (bT25 x) ∧
    FrontDet (x 0) (x 6) (x 1) (x 3) (bT25 x) ∧
    FrontDet (x 0) (x 6) (x 1) (x 5) (bT25 x) ∧
    FrontDet (x 0) (x 4) (x 1) (x 3) (bT25 x) ∧
    FrontDet (x 0) (x 4) (x 1) (x 5) (bT25 x) ∧
    FrontDet (x 0) (x 3) (x 1) (x 5) (bT25 x) ∧
    FrontDet (x 0) (x 4) (x 6) (x 3) (bT25 x) ∧
    FrontDet (x 0) (x 4) (x 6) (x 5) (bT25 x) ∧
    FrontDet (x 0) (x 3) (x 6) (x 5) (bT25 x) ∧
    FrontDet (x 1) (x 4) (x 6) (x 3) (bT25 x) ∧
    FrontDet (x 1) (x 4) (x 6) (x 5) (bT25 x) ∧
    FrontDet (x 6) (x 5) (x 1) (x 3) (bT25 x) ∧
    FrontDet (x 4) (x 5) (x 1) (x 3) (bT25 x) ∧
    FrontDet (x 4) (x 5) (x 6) (x 3) (bT25 x)

/-- Project `A1TieSample` onto `A1E25Sample`. -/
theorem A1TieSample.toE25Sample {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x}
    (hS : A1TieSample x F) : A1E25Sample x F where
  hc63 := hS.hc63
  h4 := hS.h4
  t25_fronts_0536 := hS.t25_fronts_0536
  t25_fronts_05346 := hS.t25_fronts_05346
  t25_fronts_01635 := fun h1 h8 =>
    let ⟨a, b, c, d, e⟩ := hS.t25_fronts_01635 h1 h8
    ⟨a, b, c, d, e.elim Or.inl (fun h => Or.inr h.1)⟩
  t25_016435 := fun h1 h8 =>
    let ⟨hfr, rest⟩ := hS.t25_016435 h1 h8
    ⟨fun hx4 hx6 =>
      let ⟨_, _, _, hx1, _⟩ := x1_frame F
      (hfr hx4 hx1 hx6).2.2.1,
     rest⟩

/-- Core of `a1_e25` taking `hnLex : ¬ LexAny F` directly. -/
theorem a1_e25_core {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hnLex : ¬ LexAny F) (hA1 : Reg.A1 x F) (hO : H24K.SAT.OB1 x) (hS : A1E25Sample x F) :
    ⟪x 5, x 5 - x 0⟫ ≤ ⟪x 2, x 5 - x 0⟫ := by
  obtain ⟨h0, h5, h7, h3⟩ := t25_facets F
  obtain ⟨t2, t6⟩ := t25_tilt_frame F
  have hdet25 := t25_det_ne_zero F
  obtain ⟨p4, q4, hx4, hp4, _, hq4_le, _⟩ := x4_frame F
  have hq4_ge : 1 ≤ q4 := hq4_le hA1.2
  obtain ⟨c61, c62, c63, hx6, hc61_eq, hc62_eq, hc63_eq⟩ := frame5_exists F 6
  have hc61_pos : 0 < c61 := by
    rw [hc61_eq]; exact div_pos_of_neg_of_neg (F.neg 3 6 (by decide)) (F.neg 3 2 (by decide))
  have hc62_pos : 0 < c62 := by
    rw [hc62_eq]; exact div_pos_of_neg_of_neg (F.neg 6 6 (by decide)) (F.neg 6 0 (by decide))
  have hc63 : 1 ≤ c63 := by
    rw [hc63_eq, le_div_iff_of_neg (F.neg 2 3 (by decide))]; simpa using hS.hc63
  have hd1 : (x 3 - x 5 : ℝ³) = (0 : ℝ) • (x 2 - x 5) + (1 : ℝ) • (x 3 - x 5) := by simp
  have hδ : (0 : ℝ) < 1 := one_pos
  have h1_cases : (⟪F.N 1, bT25 x⟫ ≤ 0 ∧ (⟪F.N 1, bT25 x⟫ = 0 → ⟪F.N 1, x 3 - x 5⟫ < 0)) ∨
      (0 ≤ ⟪F.N 1, bT25 x⟫ ∧ (⟪F.N 1, bT25 x⟫ = 0 → 0 ≤ ⟪F.N 1, x 3 - x 5⟫)) := by
    rcases lt_trichotomy ⟪F.N 1, bT25 x⟫ 0 with h | h | h
    · exact Or.inl ⟨h.le, fun he => absurd he h.ne⟩
    · rcases lt_or_ge ⟪F.N 1, x 3 - x 5⟫ 0 with h35 | h35
      · exact Or.inl ⟨h.le, fun _ => h35⟩
      · exact Or.inr ⟨h.ge, fun _ => h35⟩
    · exact Or.inr ⟨h.le, fun he => absurd he h.ne'⟩
  rcases h1_cases with ⟨h1_le, h1_eq⟩ | ⟨h1_ge, h1_eq⟩
  · have t1 := lexNeg3_N1_T25 F (d2 := x 0 - x 5) hd1 hδ h1_le h1_eq
    rcases lt_or_ge ⟪F.N 8, bT25 x⟫ 0 with h8_lt | h8_ge
    · have hq4_gt : 1 < q4 := q4_gt_one_of_facet8 F hx4 hx6 hp4 hc61_pos hc62_pos hc63 h8_lt
      obtain ⟨f0356, f0456, f0436, f5436⟩ := hS.t25_fronts_05346 h1_le h8_lt
      exact e25_dom_05346 F (x 3 - x 5) (x 0 - x 5) hnLex hx4 hp4 hq4_ge hdet25
        h3 (hS.h4 (Or.inl h1_le)) t1 h8_lt t2 t6 (crossOf_0354_of_x4 hx4 hp4 hq4_gt)
        f0356 f0456 f0436 f5436
    · exact e25_dom_0536 F (x 3 - x 5) (x 0 - x 5) hd1 hδ hnLex h3 (hS.h4 (Or.inl h1_le)) h8_ge
        t1 h7 t2 t6 (hS.t25_fronts_0536 h1_le h8_ge)
  · have t1 := lexPos3_N1_T25 F hd1 hδ h1_ge h1_eq
    rcases lt_or_ge ⟪F.N 8, bT25 x⟫ 0 with h8_lt | h8_ge
    · have hq4_gt : 1 < q4 := q4_gt_one_of_facet8 F hx4 hx6 hp4 hc61_pos hc62_pos hc63 h8_lt
      obtain ⟨hq4_63_fn, f0614, f0613, f0615, f0413, f0415, f0315, f0463, f0465, f0365,
        f1463, f1465, f6513, f4513, f4563⟩ := hS.t25_016435 h1_ge h8_lt
      exact e25_dom_016435 F (x 3 - x 5) (x 0 - x 5) hnLex hA1.1 hO hx4 hp4 hq4_gt
        hx6 hc61_pos hc62_pos hc63 (hq4_63_fn hx4 hx6) hdet25
        h1_ge t1 h3 (hS.h4 (Or.inr h8_lt)) h0 h5 h7 h8_lt t2 t6 (crossOf_0345_of_x4 hx4 hp4 hq4_gt)
        f0614 f0613 f0615 f0413 f0415 f0315 f0463 f0465 f0365 f1463 f1465 f6513 f4513 f4563
    · obtain ⟨f0613, f0615, f0315, f0365, h6513⟩ := hS.t25_fronts_01635 h1_ge h8_ge
      rcases h6513 with f6513 | f1365
      · exact e25_dom_01635 F (x 3 - x 5) (x 0 - x 5) hd1 hδ hnLex hx6 hc61_pos hc62_pos hc63
          t1 h3 h8_ge h0 h5 h7 t2 t6 f0613 f0615 f0315 f0365 f6513
      · exact e25_dom_01635_flip F (x 3 - x 5) (x 0 - x 5) hd1 hδ hnLex hA1.1 hO hx6 hc61_pos
          hc62_pos hc63 h1_ge t1 h3 h8_ge h0 h5 h7 t2 t6 f0613 f0615 f0315 f0365 f1365

/-- **Step T1 (`a1_e25`)**: `Hole24R x F`, `Reg.A1 x F`, `H24K.SAT.OB1 x`, and `A1E25Sample x F`
force `⟪x 5, x 5 - x 0⟫ ≤ ⟪x 2, x 5 - x 0⟫` (`z5(w05) ≤ z2(w05)`). Orientation-free (no `det24`). -/
theorem a1_e25 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hR : Hole24R x F) (hA1 : Reg.A1 x F) (hO : H24K.SAT.OB1 x) (hS : A1E25Sample x F) :
    ⟪x 5, x 5 - x 0⟫ ≤ ⟪x 2, x 5 - x 0⟫ :=
  a1_e25_core F hR.2.2.2.2.1 hA1 hO hS

/-- Strict off-tie form of `a1_e25`: `⟪x 2 - x 5, x 5 - x 0⟫ ≠ 0` yields `⟪x 5, x 5 - x 0⟫ < ⟪x 2, x 5 - x 0⟫`. -/
theorem a1_e25_lt {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hR : Hole24R x F) (hA1 : Reg.A1 x F) (hO : H24K.SAT.OB1 x) (hS : A1E25Sample x F)
    (hntie : ⟪x 2 - x 5, x 5 - x 0⟫ ≠ 0) :
    ⟪x 5, x 5 - x 0⟫ < ⟪x 2, x 5 - x 0⟫ := by
  have hle := a1_e25 F hR hA1 hO hS
  refine lt_of_le_of_ne hle ?_
  intro heq
  apply hntie
  rw [inner_sub_left, heq, sub_self]

end Minimality.T24.A1
