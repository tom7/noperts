module

public import Minimality.M4jType24

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.LexCell Minimality.H21 Minimality.H24.SAT
  Minimality.T24.SAT Minimality.T24.RCell Minimality.Split Minimality.T24.M4
  Minimality.T24.A7 Minimality.T24.A8 Minimality.T24.A15 Minimality.T24.Q24

namespace Minimality.T24.A19

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- The 14 front pairs of the 6-rim `1 0 5 3 4 6` at `eb`, from facet data and the two brackets (`nB < 0`). -/
theorem neg6_fronts' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hω4 : 0 < omega4 x)
    (hnb : F.f 3 (x 2) < F.f 3 (x 1)) (h346 : F.f 8 (x 1) < F.f 8 (x 2))
    (h1356 : 0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3)
    (h1456 : 0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4) :
    GenQuad.FrontOf (x 1) (x 5) (x 0) (x 3) (x 2 - x 1) ∧ GenQuad.FrontOf (x 1) (x 5) (x 0) (x 4) (x 2 - x 1) ∧ GenQuad.FrontOf (x 1) (x 5) (x 0) (x 6) (x 2 - x 1) ∧ GenQuad.FrontOf (x 1) (x 3) (x 0) (x 4) (x 2 - x 1) ∧ GenQuad.FrontOf (x 1) (x 3) (x 0) (x 6) (x 2 - x 1) ∧ GenQuad.FrontOf (x 1) (x 4) (x 0) (x 6) (x 2 - x 1) ∧ GenQuad.FrontOf (x 1) (x 3) (x 5) (x 4) (x 2 - x 1) ∧ GenQuad.FrontOf (x 5) (x 6) (x 1) (x 3) (x 2 - x 1) ∧ GenQuad.FrontOf (x 5) (x 6) (x 1) (x 4) (x 2 - x 1) ∧ GenQuad.FrontOf (x 3) (x 6) (x 1) (x 4) (x 2 - x 1) ∧ GenQuad.FrontOf (x 5) (x 6) (x 0) (x 3) (x 2 - x 1) ∧ GenQuad.FrontOf (x 5) (x 6) (x 0) (x 4) (x 2 - x 1) ∧ GenQuad.FrontOf (x 3) (x 6) (x 0) (x 4) (x 2 - x 1) ∧ GenQuad.FrontOf (x 3) (x 6) (x 5) (x 4) (x 2 - x 1) := by
  have T := type24OfFac F
  have hdet := T.det_ne
  have ha0 : oblX0 x 0 = 1 := by simp only [oblX0, det24]; exact div_self hdet
  have ha1 : oblX0 x 1 = 0 := by
    unfold oblX0; rw [show vol3 (x 1 - x 1) (x 2 - x 1) (x 6 - x 1) = 0 by simp [vol3], zero_div]
  have ha6 : oblX0 x 6 = 0 := by
    unfold oblX0; rw [show vol3 (x 6 - x 1) (x 2 - x 1) (x 6 - x 1) = 0 by simp only [vol3]; ring, zero_div]
  have hc0 : oblX6 x 0 = 0 := by
    unfold oblX6; rw [show vol3 (x 0 - x 1) (x 2 - x 1) (x 0 - x 1) = 0 by simp only [vol3]; ring, zero_div]
  have hc1 : oblX6 x 1 = 0 := by
    unfold oblX6; rw [show vol3 (x 0 - x 1) (x 2 - x 1) (x 1 - x 1) = 0 by simp [vol3], zero_div]
  have hc6 : oblX6 x 6 = 1 := by simp only [oblX6, det24]; exact div_self hdet
  have hb1 : oblX2 x 1 = 0 := by
    unfold oblX2; rw [show vol3 (x 0 - x 1) (x 1 - x 1) (x 6 - x 1) = 0 by simp [vol3], zero_div]
  have hb6 : oblX2 x 6 = 0 := by
    unfold oblX2; rw [show vol3 (x 0 - x 1) (x 6 - x 1) (x 6 - x 1) = 0 by simp only [vol3]; ring, zero_div]
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have ha4 : 0 < oblX0 x 4 := T.X0_pos (v := 4) (by decide)
  have ha5 : 0 < oblX0 x 5 := T.X0_pos (v := 5) (by decide)
  have hc3 : 0 < oblX6 x 3 := T.X6_pos (v := 3) (by decide)
  have hc4 : 0 < oblX6 x 4 := T.X6_pos (v := 4) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hB1 : F.f 1 (x 2) - F.f 1 (x 1) < 0 := by
    rw [F.zero 1 1 (by decide)]; linarith [F.neg 1 2 (by decide)]
  have hB2 : 0 < F.f 2 (x 2) - F.f 2 (x 1) := by
    rw [F.zero 2 2 (by decide)]; linarith [F.neg 2 1 (by decide)]
  have hB3 : F.f 3 (x 2) - F.f 3 (x 1) < 0 := by linarith
  have hB6 : 0 < F.f 6 (x 2) - F.f 6 (x 1) := by
    rw [F.zero 6 2 (by decide)]; linarith [F.neg 6 1 (by decide)]
  have hB8 : 0 < F.f 8 (x 2) - F.f 8 (x 1) := by linarith
  have hB4 : F.f 4 (x 2) - F.f 4 (x 1) < 0 := by
    have e := fac_eval F 4 4
    rw [F.zero 4 4 (by decide), F.zero 4 0 (by decide), F.zero 4 6 (by decide)] at e
    have h1 := F.neg 4 1 (by decide)
    have hω := T.eq4
    have key : (F.f 4 (x 2) - F.f 4 (x 1)) * oblX2 x 4 =
        F.f 4 (x 1) * (omega4 x * oblX2 x 4) := by
      linear_combination (-1 : ℝ) * e + F.f 4 (x 1) * hω
    by_contra hge
    push Not at hge
    have h2 : 0 ≤ (F.f 4 (x 2) - F.f 4 (x 1)) * oblX2 x 4 := mul_nonneg hge hb4.le
    have h3 := mul_neg_of_neg_of_pos h1 (mul_pos hω4 hb4)
    linarith
  have b051 : 0 < (((oblX0 x 5) - (oblX0 x 0)) * ((oblX6 x 1) - (oblX6 x 0)) - ((oblX6 x 5) - (oblX6 x 0)) * ((oblX0 x 1) - (oblX0 x 0))) := by (try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]); nlinarith [hc5]
  have O053 := edge_orient F (U := 2) (D := 3) (u := 0) (v := 5) (w := 3) (w1 := 1) hB2 hB3 (F.zero 2 0 (by decide)) (F.zero 3 0 (by decide)) (F.zero 2 5 (by decide)) (F.zero 3 5 (by decide)) (Or.inl (F.neg 2 3 (by decide))) (Or.inl (F.neg 2 1 (by decide))) b051
  try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6] at O053
  have O054 := edge_orient F (U := 2) (D := 3) (u := 0) (v := 5) (w := 4) (w1 := 1) hB2 hB3 (F.zero 2 0 (by decide)) (F.zero 3 0 (by decide)) (F.zero 2 5 (by decide)) (F.zero 3 5 (by decide)) (Or.inl (F.neg 2 4 (by decide))) (Or.inl (F.neg 2 1 (by decide))) b051
  try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6] at O054
  have O056 := edge_orient F (U := 2) (D := 3) (u := 0) (v := 5) (w := 6) (w1 := 1) hB2 hB3 (F.zero 2 0 (by decide)) (F.zero 3 0 (by decide)) (F.zero 2 5 (by decide)) (F.zero 3 5 (by decide)) (Or.inl (F.neg 2 6 (by decide))) (Or.inl (F.neg 2 1 (by decide))) b051
  try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6] at O056
  have b530 : 0 < (((oblX0 x 3) - (oblX0 x 5)) * ((oblX6 x 0) - (oblX6 x 5)) - ((oblX6 x 3) - (oblX6 x 5)) * ((oblX0 x 0) - (oblX0 x 5))) := by (try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]); nlinarith [O053]
  have O531 := edge_orient F (U := 6) (D := 3) (u := 5) (v := 3) (w := 1) (w1 := 0) hB6 hB3 (F.zero 6 5 (by decide)) (F.zero 3 5 (by decide)) (F.zero 6 3 (by decide)) (F.zero 3 3 (by decide)) (Or.inl (F.neg 6 1 (by decide))) (Or.inl (F.neg 6 0 (by decide))) b530
  try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6] at O531
  have O534 := edge_orient F (U := 6) (D := 3) (u := 5) (v := 3) (w := 4) (w1 := 0) hB6 hB3 (F.zero 6 5 (by decide)) (F.zero 3 5 (by decide)) (F.zero 6 3 (by decide)) (F.zero 3 3 (by decide)) (Or.inl (F.neg 6 4 (by decide))) (Or.inl (F.neg 6 0 (by decide))) b530
  try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6] at O534
  have O536 := edge_orient F (U := 6) (D := 3) (u := 5) (v := 3) (w := 6) (w1 := 0) hB6 hB3 (F.zero 6 5 (by decide)) (F.zero 3 5 (by decide)) (F.zero 6 3 (by decide)) (F.zero 3 3 (by decide)) (Or.inl (F.neg 6 6 (by decide))) (Or.inl (F.neg 6 0 (by decide))) b530
  try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6] at O536
  have b345 : 0 < (((oblX0 x 4) - (oblX0 x 3)) * ((oblX6 x 5) - (oblX6 x 3)) - ((oblX6 x 4) - (oblX6 x 3)) * ((oblX0 x 5) - (oblX0 x 3))) := by (try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]); nlinarith [O534]
  have O341 := edge_orient F (U := 8) (D := 3) (u := 3) (v := 4) (w := 1) (w1 := 5) hB8 hB3 (F.zero 8 3 (by decide)) (F.zero 3 3 (by decide)) (F.zero 8 4 (by decide)) (F.zero 3 4 (by decide)) (Or.inl (F.neg 8 1 (by decide))) (Or.inl (F.neg 8 5 (by decide))) b345
  try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6] at O341
  have O340 := edge_orient F (U := 8) (D := 3) (u := 3) (v := 4) (w := 0) (w1 := 5) hB8 hB3 (F.zero 8 3 (by decide)) (F.zero 3 3 (by decide)) (F.zero 8 4 (by decide)) (F.zero 3 4 (by decide)) (Or.inl (F.neg 8 0 (by decide))) (Or.inl (F.neg 8 5 (by decide))) b345
  try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6] at O340
  have O346 := edge_orient F (U := 8) (D := 3) (u := 3) (v := 4) (w := 6) (w1 := 5) hB8 hB3 (F.zero 8 3 (by decide)) (F.zero 3 3 (by decide)) (F.zero 8 4 (by decide)) (F.zero 3 4 (by decide)) (Or.inr (F.neg 3 6 (by decide))) (Or.inl (F.neg 8 5 (by decide))) b345
  try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6] at O346
  have b463 : 0 < (((oblX0 x 6) - (oblX0 x 4)) * ((oblX6 x 3) - (oblX6 x 4)) - ((oblX6 x 6) - (oblX6 x 4)) * ((oblX0 x 3) - (oblX0 x 4))) := by (try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]); nlinarith [O346]
  have O461 := edge_orient F (U := 8) (D := 4) (u := 4) (v := 6) (w := 1) (w1 := 3) hB8 hB4 (F.zero 8 4 (by decide)) (F.zero 4 4 (by decide)) (F.zero 8 6 (by decide)) (F.zero 4 6 (by decide)) (Or.inl (F.neg 8 1 (by decide))) (Or.inr (F.neg 4 3 (by decide))) b463
  try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6] at O461
  have O460 := edge_orient F (U := 8) (D := 4) (u := 4) (v := 6) (w := 0) (w1 := 3) hB8 hB4 (F.zero 8 4 (by decide)) (F.zero 4 4 (by decide)) (F.zero 8 6 (by decide)) (F.zero 4 6 (by decide)) (Or.inl (F.neg 8 0 (by decide))) (Or.inr (F.neg 4 3 (by decide))) b463
  try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6] at O460
  have O465 := edge_orient F (U := 8) (D := 4) (u := 4) (v := 6) (w := 5) (w1 := 3) hB8 hB4 (F.zero 8 4 (by decide)) (F.zero 4 4 (by decide)) (F.zero 8 6 (by decide)) (F.zero 4 6 (by decide)) (Or.inl (F.neg 8 5 (by decide))) (Or.inr (F.neg 4 3 (by decide))) b463
  try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6] at O465
  have O153 : 0 < (((oblX0 x 5) - 0) * ((oblX6 x 3) - 0) - ((oblX6 x 5) - 0) * ((oblX0 x 3) - 0)) := by (try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6] at O531); nlinarith [O531]
  have O134 : 0 < (((oblX0 x 3) - 0) * ((oblX6 x 4) - 0) - ((oblX6 x 3) - 0) * ((oblX0 x 4) - 0)) := by (try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6] at O341); nlinarith [O341]
  have O154 : 0 < (((oblX0 x 5) - 0) * ((oblX6 x 4) - 0) - ((oblX6 x 5) - 0) * ((oblX0 x 4) - 0)) := by
    by_contra hn; push Not at hn
    have h1 := mul_pos hc4 O153; have h2 := mul_pos hc5 O134
    nlinarith [mul_nonneg hc3.le (neg_nonneg.2 hn)]
  have O034 : 0 < (((oblX0 x 3) - 1) * ((oblX6 x 4) - 0) - ((oblX6 x 3) - 0) * ((oblX0 x 4) - 1)) := by (try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6] at O340); nlinarith [O340]
  have O046 : 0 < (((oblX0 x 4) - 1) * (1 - 0) - ((oblX6 x 4) - 0) * (0 - 1)) := by (try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6] at O460); nlinarith [O460]
  have O036 : 0 < (((oblX0 x 3) - 1) * (1 - 0) - ((oblX6 x 3) - 0) * (0 - 1)) := by
    by_contra hn; push Not at hn
    have h2 := mul_pos hc3 O046
    nlinarith [mul_nonneg hc4.le (neg_nonneg.2 hn)]
  have f15_03 : GenQuad.FrontOf (x 1) (x 5) (x 0) (x 3) (x 2 - x 1) := by
    have hD : 0 < crD x 1 5 0 3 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL0 : 0 < crL x 1 5 0 3 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL1 : crL x 1 5 0 3 < crD x 1 5 0 3 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM0 : 0 < crM x 1 5 0 3 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM1 : crM x 1 5 0 3 < crD x 1 5 0 3 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have l0 := div_pos hL0 hD
    have l1 := (div_lt_one hD).2 hL1
    have m0 := div_pos hM0 hD
    have m1 := (div_lt_one hD).2 hM1
    have hD' := hD.ne'
    refine front_dn F (t := 3) hD' l0.le l1.le m0.le m1.le ?_ ?_ ?_ ?_
    · exact hB3
    · exact F.zero 3 0 (by decide)
    · exact F.zero 3 3 (by decide)
    · rw [F.zero 3 5 (by decide)]; nlinarith [mul_neg_of_pos_of_neg l0 (F.neg 3 1 (by decide))]
  have f15_04 : GenQuad.FrontOf (x 1) (x 5) (x 0) (x 4) (x 2 - x 1) := by
    have hD : 0 < crD x 1 5 0 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL0 : 0 < crL x 1 5 0 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL1 : crL x 1 5 0 4 < crD x 1 5 0 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM0 : 0 < crM x 1 5 0 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM1 : crM x 1 5 0 4 < crD x 1 5 0 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have l0 := div_pos hL0 hD
    have l1 := (div_lt_one hD).2 hL1
    have m0 := div_pos hM0 hD
    have m1 := (div_lt_one hD).2 hM1
    have hD' := hD.ne'
    refine front_dn F (t := 3) hD' l0.le l1.le m0.le m1.le ?_ ?_ ?_ ?_
    · exact hB3
    · exact F.zero 3 0 (by decide)
    · exact F.zero 3 4 (by decide)
    · rw [F.zero 3 5 (by decide)]; nlinarith [mul_neg_of_pos_of_neg l0 (F.neg 3 1 (by decide))]
  have f15_06 : GenQuad.FrontOf (x 1) (x 5) (x 0) (x 6) (x 2 - x 1) := by
    have hD : 0 < crD x 1 5 0 6 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL0 : 0 < crL x 1 5 0 6 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL1 : crL x 1 5 0 6 < crD x 1 5 0 6 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM0 : 0 < crM x 1 5 0 6 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM1 : crM x 1 5 0 6 < crD x 1 5 0 6 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have l0 := div_pos hL0 hD
    have l1 := (div_lt_one hD).2 hL1
    have m0 := div_pos hM0 hD
    have m1 := (div_lt_one hD).2 hM1
    have hD' := hD.ne'
    refine front_dn F (t := 1) hD' l0.le l1.le m0.le m1.le ?_ ?_ ?_ ?_
    · exact hB1
    · exact F.zero 1 0 (by decide)
    · exact F.zero 1 6 (by decide)
    · rw [F.zero 1 1 (by decide)]; nlinarith [mul_neg_of_pos_of_neg (sub_pos.2 l1) (F.neg 1 5 (by decide))]
  have f13_04 : GenQuad.FrontOf (x 1) (x 3) (x 0) (x 4) (x 2 - x 1) := by
    have hD : 0 < crD x 1 3 0 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL0 : 0 < crL x 1 3 0 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL1 : crL x 1 3 0 4 < crD x 1 3 0 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM0 : 0 < crM x 1 3 0 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM1 : crM x 1 3 0 4 < crD x 1 3 0 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have l0 := div_pos hL0 hD
    have l1 := (div_lt_one hD).2 hL1
    have m0 := div_pos hM0 hD
    have m1 := (div_lt_one hD).2 hM1
    have hD' := hD.ne'
    refine front_dn F (t := 3) hD' l0.le l1.le m0.le m1.le ?_ ?_ ?_ ?_
    · exact hB3
    · exact F.zero 3 0 (by decide)
    · exact F.zero 3 4 (by decide)
    · rw [F.zero 3 3 (by decide)]; nlinarith [mul_neg_of_pos_of_neg l0 (F.neg 3 1 (by decide))]
  have f13_06 : GenQuad.FrontOf (x 1) (x 3) (x 0) (x 6) (x 2 - x 1) := by
    have hD : 0 < crD x 1 3 0 6 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL0 : 0 < crL x 1 3 0 6 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL1 : crL x 1 3 0 6 < crD x 1 3 0 6 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM0 : 0 < crM x 1 3 0 6 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM1 : crM x 1 3 0 6 < crD x 1 3 0 6 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have l0 := div_pos hL0 hD
    have l1 := (div_lt_one hD).2 hL1
    have m0 := div_pos hM0 hD
    have m1 := (div_lt_one hD).2 hM1
    have hD' := hD.ne'
    refine front_dn F (t := 1) hD' l0.le l1.le m0.le m1.le ?_ ?_ ?_ ?_
    · exact hB1
    · exact F.zero 1 0 (by decide)
    · exact F.zero 1 6 (by decide)
    · rw [F.zero 1 1 (by decide)]; nlinarith [mul_neg_of_pos_of_neg (sub_pos.2 l1) (F.neg 1 3 (by decide))]
  have f14_06 : GenQuad.FrontOf (x 1) (x 4) (x 0) (x 6) (x 2 - x 1) := by
    have hD : 0 < crD x 1 4 0 6 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL0 : 0 < crL x 1 4 0 6 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL1 : crL x 1 4 0 6 < crD x 1 4 0 6 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM0 : 0 < crM x 1 4 0 6 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM1 : crM x 1 4 0 6 < crD x 1 4 0 6 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have l0 := div_pos hL0 hD
    have l1 := (div_lt_one hD).2 hL1
    have m0 := div_pos hM0 hD
    have m1 := (div_lt_one hD).2 hM1
    have hD' := hD.ne'
    refine front_dn F (t := 1) hD' l0.le l1.le m0.le m1.le ?_ ?_ ?_ ?_
    · exact hB1
    · exact F.zero 1 0 (by decide)
    · exact F.zero 1 6 (by decide)
    · rw [F.zero 1 1 (by decide)]; nlinarith [mul_neg_of_pos_of_neg (sub_pos.2 l1) (F.neg 1 4 (by decide))]
  have f13_54 : GenQuad.FrontOf (x 1) (x 3) (x 5) (x 4) (x 2 - x 1) := by
    have hD : 0 < crD x 1 3 5 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL0 : 0 < crL x 1 3 5 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL1 : crL x 1 3 5 4 < crD x 1 3 5 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM0 : 0 < crM x 1 3 5 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM1 : crM x 1 3 5 4 < crD x 1 3 5 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have l0 := div_pos hL0 hD
    have l1 := (div_lt_one hD).2 hL1
    have m0 := div_pos hM0 hD
    have m1 := (div_lt_one hD).2 hM1
    have hD' := hD.ne'
    refine front_dn F (t := 3) hD' l0.le l1.le m0.le m1.le ?_ ?_ ?_ ?_
    · exact hB3
    · exact F.zero 3 5 (by decide)
    · exact F.zero 3 4 (by decide)
    · rw [F.zero 3 3 (by decide)]; nlinarith [mul_neg_of_pos_of_neg l0 (F.neg 3 1 (by decide))]
  have f56_13 : GenQuad.FrontOf (x 5) (x 6) (x 1) (x 3) (x 2 - x 1) := by
    have hD : crD x 5 6 1 3 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL0 : crL x 5 6 1 3 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL1 : crD x 5 6 1 3 < crL x 5 6 1 3 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM0 : crM x 5 6 1 3 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM1 : crD x 5 6 1 3 < crM x 5 6 1 3 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have l0 := div_pos_of_neg_of_neg hL0 hD
    have l1 := (div_lt_one_of_neg hD).2 hL1
    have m0 := div_pos_of_neg_of_neg hM0 hD
    have m1 := (div_lt_one_of_neg hD).2 hM1
    have hD' := hD.ne
    refine front_gen T hD' l0.le l1.le m0.le m1.le ?_
    have e : crL x 5 6 1 3 / crD x 5 6 1 3 * oblX2 x 5 + (1 - crL x 5 6 1 3 / crD x 5 6 1 3) * oblX2 x 6 - (crM x 5 6 1 3 / crD x 5 6 1 3 * oblX2 x 1 + (1 - crM x 5 6 1 3 / crD x 5 6 1 3) * oblX2 x 3) = -(oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3) / crD x 5 6 1 3 := by
      have hk : crL x 5 6 1 3 * oblX2 x 5 - (crD x 5 6 1 3 - crM x 5 6 1 3) * oblX2 x 3 = -(oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3) := by
        simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6]; ring
      rw [hb6, hb1]
      generalize crL x 5 6 1 3 = Nl at *
      generalize crM x 5 6 1 3 = Nm at *
      generalize crD x 5 6 1 3 = D at *
      field_simp; linear_combination hk
    rw [e]; exact div_pos_of_neg_of_neg (by linarith) hD
  have f56_14 : GenQuad.FrontOf (x 5) (x 6) (x 1) (x 4) (x 2 - x 1) := by
    have hD : crD x 5 6 1 4 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL0 : crL x 5 6 1 4 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL1 : crD x 5 6 1 4 < crL x 5 6 1 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM0 : crM x 5 6 1 4 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM1 : crD x 5 6 1 4 < crM x 5 6 1 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have l0 := div_pos_of_neg_of_neg hL0 hD
    have l1 := (div_lt_one_of_neg hD).2 hL1
    have m0 := div_pos_of_neg_of_neg hM0 hD
    have m1 := (div_lt_one_of_neg hD).2 hM1
    have hD' := hD.ne
    refine front_gen T hD' l0.le l1.le m0.le m1.le ?_
    have e : crL x 5 6 1 4 / crD x 5 6 1 4 * oblX2 x 5 + (1 - crL x 5 6 1 4 / crD x 5 6 1 4) * oblX2 x 6 - (crM x 5 6 1 4 / crD x 5 6 1 4 * oblX2 x 1 + (1 - crM x 5 6 1 4 / crD x 5 6 1 4) * oblX2 x 4) = -(oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4) / crD x 5 6 1 4 := by
      have hk : crL x 5 6 1 4 * oblX2 x 5 - (crD x 5 6 1 4 - crM x 5 6 1 4) * oblX2 x 4 = -(oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4) := by
        simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6]; ring
      rw [hb6, hb1]
      generalize crL x 5 6 1 4 = Nl at *
      generalize crM x 5 6 1 4 = Nm at *
      generalize crD x 5 6 1 4 = D at *
      field_simp; linear_combination hk
    rw [e]; exact div_pos_of_neg_of_neg (by linarith) hD
  have f36_14 : GenQuad.FrontOf (x 3) (x 6) (x 1) (x 4) (x 2 - x 1) := by
    have hD : crD x 3 6 1 4 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL0 : crL x 3 6 1 4 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL1 : crD x 3 6 1 4 < crL x 3 6 1 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM0 : crM x 3 6 1 4 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM1 : crD x 3 6 1 4 < crM x 3 6 1 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have l0 := div_pos_of_neg_of_neg hL0 hD
    have l1 := (div_lt_one_of_neg hD).2 hL1
    have m0 := div_pos_of_neg_of_neg hM0 hD
    have m1 := (div_lt_one_of_neg hD).2 hM1
    have hD' := hD.ne
    refine front_up F (t := 8) hD' l0.le l1.le m0.le m1.le ?_ ?_ ?_ ?_
    · exact hB8
    · exact F.zero 8 3 (by decide)
    · exact F.zero 8 6 (by decide)
    · rw [F.zero 8 4 (by decide)]; nlinarith [mul_neg_of_pos_of_neg m0 (F.neg 8 1 (by decide))]
  have f56_03 : GenQuad.FrontOf (x 5) (x 6) (x 0) (x 3) (x 2 - x 1) := by
    have hD : crD x 5 6 0 3 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL0 : crL x 5 6 0 3 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL1 : crD x 5 6 0 3 < crL x 5 6 0 3 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM0 : crM x 5 6 0 3 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM1 : crD x 5 6 0 3 < crM x 5 6 0 3 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have l0 := div_pos_of_neg_of_neg hL0 hD
    have l1 := (div_lt_one_of_neg hD).2 hL1
    have m0 := div_pos_of_neg_of_neg hM0 hD
    have m1 := (div_lt_one_of_neg hD).2 hM1
    have hD' := hD.ne
    refine front_dn F (t := 3) hD' l0.le l1.le m0.le m1.le ?_ ?_ ?_ ?_
    · exact hB3
    · exact F.zero 3 0 (by decide)
    · exact F.zero 3 3 (by decide)
    · rw [F.zero 3 5 (by decide)]; nlinarith [mul_neg_of_pos_of_neg (sub_pos.2 l1) (F.neg 3 6 (by decide))]
  have f56_04 : GenQuad.FrontOf (x 5) (x 6) (x 0) (x 4) (x 2 - x 1) := by
    have hD : crD x 5 6 0 4 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL0 : crL x 5 6 0 4 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL1 : crD x 5 6 0 4 < crL x 5 6 0 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM0 : crM x 5 6 0 4 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM1 : crD x 5 6 0 4 < crM x 5 6 0 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have l0 := div_pos_of_neg_of_neg hL0 hD
    have l1 := (div_lt_one_of_neg hD).2 hL1
    have m0 := div_pos_of_neg_of_neg hM0 hD
    have m1 := (div_lt_one_of_neg hD).2 hM1
    have hD' := hD.ne
    refine front_dn F (t := 3) hD' l0.le l1.le m0.le m1.le ?_ ?_ ?_ ?_
    · exact hB3
    · exact F.zero 3 0 (by decide)
    · exact F.zero 3 4 (by decide)
    · rw [F.zero 3 5 (by decide)]; nlinarith [mul_neg_of_pos_of_neg (sub_pos.2 l1) (F.neg 3 6 (by decide))]
  have f36_04 : GenQuad.FrontOf (x 3) (x 6) (x 0) (x 4) (x 2 - x 1) := by
    have hD : crD x 3 6 0 4 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL0 : crL x 3 6 0 4 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL1 : crD x 3 6 0 4 < crL x 3 6 0 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM0 : crM x 3 6 0 4 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM1 : crD x 3 6 0 4 < crM x 3 6 0 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have l0 := div_pos_of_neg_of_neg hL0 hD
    have l1 := (div_lt_one_of_neg hD).2 hL1
    have m0 := div_pos_of_neg_of_neg hM0 hD
    have m1 := (div_lt_one_of_neg hD).2 hM1
    have hD' := hD.ne
    refine front_dn F (t := 3) hD' l0.le l1.le m0.le m1.le ?_ ?_ ?_ ?_
    · exact hB3
    · exact F.zero 3 0 (by decide)
    · exact F.zero 3 4 (by decide)
    · rw [F.zero 3 3 (by decide)]; nlinarith [mul_neg_of_pos_of_neg (sub_pos.2 l1) (F.neg 3 6 (by decide))]
  have f36_54 : GenQuad.FrontOf (x 3) (x 6) (x 5) (x 4) (x 2 - x 1) := by
    have hD : crD x 3 6 5 4 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL0 : crL x 3 6 5 4 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL1 : crD x 3 6 5 4 < crL x 3 6 5 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM0 : crM x 3 6 5 4 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM1 : crD x 3 6 5 4 < crM x 3 6 5 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have l0 := div_pos_of_neg_of_neg hL0 hD
    have l1 := (div_lt_one_of_neg hD).2 hL1
    have m0 := div_pos_of_neg_of_neg hM0 hD
    have m1 := (div_lt_one_of_neg hD).2 hM1
    have hD' := hD.ne
    refine front_dn F (t := 3) hD' l0.le l1.le m0.le m1.le ?_ ?_ ?_ ?_
    · exact hB3
    · exact F.zero 3 5 (by decide)
    · exact F.zero 3 4 (by decide)
    · rw [F.zero 3 3 (by decide)]; nlinarith [mul_neg_of_pos_of_neg (sub_pos.2 l1) (F.neg 3 6 (by decide))]
  exact ⟨f15_03, f15_04, f15_06, f13_04, f13_06, f14_06, f13_54, f56_13, f56_14, f36_14, f56_03, f56_04, f36_04, f36_54⟩


end Minimality.T24.A19
