module

public import Minimality.Type08S.L2.K89CA

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace
open Minimality Minimality.Type08Sp

namespace Minimality.Type08Sp.C2
noncomputable section



set_option maxHeartbeats 6400000 in
theorem k89c_A_q0 (s : ℝ) (hs : 0 < s) (hs2 : 3 * s ≤ 2) :
    0 < -924*s^4 - 2523*s^3 - 573*s^2 + 2230*s + 1176 := by
  linear_combination (2038 / 3 : ℝ) * (mul_pos hs hs) + 1115 * (mul_nonneg (hs).le (sub_nonneg.2 hs2)) + (3139 / 3 : ℝ) * (mul_nonneg ((mul_pos hs hs)).le (sub_nonneg.2 hs2)) + 308 * (mul_nonneg ((mul_pos (mul_pos hs hs) hs)).le (sub_nonneg.2 hs2))

set_option maxHeartbeats 6400000 in
theorem k89c_A_q3 (s : ℝ) (hs : 0 < s) (hs2 : 3 * s ≤ 2) :
    0 < -277200*s^4 - 414594*s^3 + 90757*s^2 + 353568*s + 127132 := by
  linear_combination 221513 * (mul_pos hs hs) + 176784 * (mul_nonneg (hs).le (sub_nonneg.2 hs2)) + 199798 * (mul_nonneg ((mul_pos hs hs)).le (sub_nonneg.2 hs2)) + 92400 * (mul_nonneg ((mul_pos (mul_pos hs hs) hs)).le (sub_nonneg.2 hs2))

set_option maxHeartbeats 6400000 in
theorem k89c_A_q4 (s : ℝ) (hs : 0 < s) (hs2 : 3 * s ≤ 2) :
    0 < 66000*s^5 - 33855*s^4 - 209655*s^3 - 24194*s^2 + 145660*s + 61496 := by
  linear_combination (118438 / 3 : ℝ) * (mul_pos hs hs) + 66000 * (mul_pos (mul_pos (mul_pos (mul_pos hs hs) hs) hs) hs) + 72830 * (mul_nonneg (hs).le (sub_nonneg.2 hs2)) + (232225 / 3 : ℝ) * (mul_nonneg ((mul_pos hs hs)).le (sub_nonneg.2 hs2)) + 11285 * (mul_nonneg ((mul_pos (mul_pos hs hs) hs)).le (sub_nonneg.2 hs2))

set_option maxHeartbeats 6400000 in
theorem k89c_A_q8 (s : ℝ) (hs : 0 < s) (hs2 : 3 * s ≤ 2) :
    0 < 66000*s^5 - 113055*s^4 - 326429*s^3 + 1352*s^2 + 245828*s + 97648 := by
  linear_combination 102228 * (mul_pos hs hs) + 66000 * (mul_pos (mul_pos (mul_pos (mul_pos hs hs) hs) hs) hs) + 122914 * (mul_nonneg (hs).le (sub_nonneg.2 hs2)) + 133933 * (mul_nonneg ((mul_pos hs hs)).le (sub_nonneg.2 hs2)) + 37685 * (mul_nonneg ((mul_pos (mul_pos hs hs) hs)).le (sub_nonneg.2 hs2))

set_option maxHeartbeats 6400000 in
theorem k89c_A_q9 (s : ℝ) (hs : 0 < s) (hs2 : 3 * s ≤ 2) :
    0 < 66000*s^5 - 113055*s^4 - 326484*s^3 + 1270*s^2 + 245904*s + 97688 := by
  linear_combination (306670 / 3 : ℝ) * (mul_pos hs hs) + 66000 * (mul_pos (mul_pos (mul_pos (mul_pos hs hs) hs) hs) hs) + 122952 * (mul_nonneg (hs).le (sub_nonneg.2 hs2)) + (401854 / 3 : ℝ) * (mul_nonneg ((mul_pos hs hs)).le (sub_nonneg.2 hs2)) + 37685 * (mul_nonneg ((mul_pos (mul_pos hs hs) hs)).le (sub_nonneg.2 hs2))


theorem k89c_hq0 (t : ℝ) (ht1 : 1 < t) (ht2 : t ≤ 5/3) : 0 < -924*t^4 + 1173*t^3 + 1452*t^2 - 497*t - 28 := by
  have h := k89c_A_q0 (t-1) (by linarith) (by linarith)
  exact lt_of_lt_of_eq h (by ring)

theorem k89c_hq3 (t : ℝ) (ht1 : 1 < t) (ht2 : t ≤ 5/3) : 0 < -277200*t^4 + 694206*t^3 - 328661*t^2 + 37072*t + 1715 := by
  have h := k89c_A_q3 (t-1) (by linarith) (by linarith)
  exact lt_of_lt_of_eq h (by ring)

theorem k89c_hq4 (t : ℝ) (ht1 : 1 < t) (ht2 : t ≤ 5/3) : 0 < 66000*t^5 - 363855*t^4 + 585765*t^3 - 258359*t^2 + 30503*t + 1442 := by
  have h := k89c_A_q4 (t-1) (by linarith) (by linarith)
  exact lt_of_lt_of_eq h (by ring)

theorem k89c_hq8 (t : ℝ) (ht1 : 1 < t) (ht2 : t ≤ 5/3) : 0 < 66000*t^5 - 443055*t^4 + 785791*t^3 - 357691*t^2 + 46057*t + 546 := by
  have h := k89c_A_q8 (t-1) (by linarith) (by linarith)
  exact lt_of_lt_of_eq h (by ring)

theorem k89c_hq9 (t : ℝ) (ht1 : 1 < t) (ht2 : t ≤ 5/3) : 0 < 66000*t^5 - 443055*t^4 + 785736*t^3 - 357608*t^2 + 46132*t + 483 := by
  have h := k89c_A_q9 (t-1) (by linarith) (by linarith)
  exact lt_of_lt_of_eq h (by ring)

set_option maxHeartbeats 16000000 in
theorem k89c_conv0 (t : ℝ) (ht1 : 1 < t) (ht2 : t ≤ 5/3) : 0 < k89c_d3 (k89c_sub (k89c_P t 1) (k89c_P t 0)) (k89c_sub (k89c_P t 3) (k89c_P t 0)) k89c_w0 := by
  have h3 : (3 - t) ≠ 0 := by intro h; linarith
  have h0 : t ≠ 0 := by intro h; linarith

  have key : k89c_d3 (k89c_sub (k89c_P t 1) (k89c_P t 0)) (k89c_sub (k89c_P t 3) (k89c_P t 0)) k89c_w0 = (8) / (1) := by
    simp only [k89c_d3, k89c_sub, k89c_P, k89c_w0]
    field_simp
    ring
  rw [key]
  exact div_pos (by norm_num : (0:ℝ) < 8) (by norm_num : (0:ℝ) < 1)

set_option maxHeartbeats 16000000 in
theorem k89c_rA0 (t : ℝ) (ht1 : 1 < t) (ht2 : t ≤ 5/3) : 0 < k89c_d3 (k89c_sub (k89c_P t 1) (k89c_P t 0)) (k89c_vel t (k89c_P t 0)) k89c_w0 := by
  have h3 : (3 - t) ≠ 0 := by intro h; linarith
  have h0 : t ≠ 0 := by intro h; linarith
  have hf0 : 0 < t + 1 := by linarith
  have hf1 : 0 < 5*t - 3 := by linarith
  have hf2 : 0 < 25*t - 7 := by linarith
  have hf3 : 0 < -924*t^4 + 1173*t^3 + 1452*t^2 - 497*t - 28 := k89c_hq0 t ht1 ht2
  have key : k89c_d3 (k89c_sub (k89c_P t 1) (k89c_P t 0)) (k89c_vel t (k89c_P t 0)) k89c_w0 = (((((8) * (t + 1)) * (5*t - 3)) * (25*t - 7)) * (-924*t^4 + 1173*t^3 + 1452*t^2 - 497*t - 28)) / (1) := by
    simp only [k89c_d3, k89c_sub, k89c_vel, k89c_add, k89c_cr, k89c_g, k89c_om, k89c_ta, k89c_o1, k89c_o2, k89c_o3, k89c_ta1, k89c_ta3, k89c_P, k89c_u, k89c_w0]
    field_simp
    ring
  rw [key]
  exact div_pos (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 8) hf0) hf1) hf2) hf3) (by norm_num : (0:ℝ) < 1)

set_option maxHeartbeats 16000000 in
theorem k89c_rB0 (t : ℝ) (ht1 : 1 < t) (ht2 : t ≤ 5/3) : 0 < k89c_d3 (k89c_sub (k89c_P t 0) (k89c_P t 3)) (k89c_vel t (k89c_P t 0)) k89c_w0 := by
  have h3 : (3 - t) ≠ 0 := by intro h; linarith
  have h0 : t ≠ 0 := by intro h; linarith
  have hf0 : 0 < t := by linarith
  have hf1 : 0 < t + 1 := by linarith
  have hf2 : 0 < 3*t - 1 := by linarith
  have hf3 : 0 < 5*t - 3 := by linarith
  have hf4 : 0 < 9*t - 7 := by linarith
  have hf5 : 0 < 21 - 11*t := by linarith
  have hf6 : 0 < 25*t - 7 := by linarith
  have key : k89c_d3 (k89c_sub (k89c_P t 0) (k89c_P t 3)) (k89c_vel t (k89c_P t 0)) k89c_w0 = ((((((((64) * (t)) * (t + 1)) * (3*t - 1)) * (5*t - 3)) * (9*t - 7)) * (21 - 11*t)) * (25*t - 7)) / (1) := by
    simp only [k89c_d3, k89c_sub, k89c_vel, k89c_add, k89c_cr, k89c_g, k89c_om, k89c_ta, k89c_o1, k89c_o2, k89c_o3, k89c_ta1, k89c_ta3, k89c_P, k89c_u, k89c_w0]
    field_simp
    ring
  rw [key]
  exact div_pos (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 64) hf0) hf1) hf2) hf3) hf4) hf5) hf6) (by norm_num : (0:ℝ) < 1)

set_option maxHeartbeats 16000000 in
theorem k89c_conv1 (t : ℝ) (ht1 : 1 < t) (ht2 : t ≤ 5/3) : 0 < k89c_d3 (k89c_sub (k89c_P t 6) (k89c_P t 1)) (k89c_sub (k89c_P t 0) (k89c_P t 1)) k89c_w0 := by
  have h3 : (3 - t) ≠ 0 := by intro h; linarith
  have h0 : t ≠ 0 := by intro h; linarith
  have hf0 : 0 < t + 1 := by linarith
  have hf1 : 0 < 3 - t := by linarith
  have key : k89c_d3 (k89c_sub (k89c_P t 6) (k89c_P t 1)) (k89c_sub (k89c_P t 0) (k89c_P t 1)) k89c_w0 = ((7) * (t + 1)) / ((1) * (3 - t)) := by
    simp only [k89c_d3, k89c_sub, k89c_P, k89c_e, k89c_w0]
    field_simp
    ring
  rw [key]
  exact div_pos (mul_pos (by norm_num : (0:ℝ) < 7) hf0) (mul_pos (by norm_num : (0:ℝ) < 1) hf1)

set_option maxHeartbeats 16000000 in
theorem k89c_rA1 (t : ℝ) (ht1 : 1 < t) (ht2 : t ≤ 5/3) : 0 < k89c_d3 (k89c_sub (k89c_P t 6) (k89c_P t 1)) (k89c_vel t (k89c_P t 1)) k89c_w0 := by
  have h3 : (3 - t) ≠ 0 := by intro h; linarith
  have h0 : t ≠ 0 := by intro h; linarith
  have hf0 : 0 < t + 1 := by linarith
  have hf1 : 0 < 3*t - 1 := by linarith
  have hf2 : 0 < 5*t - 3 := by linarith
  have hf3 : 0 < 9*t - 7 := by linarith
  have hf4 : 0 < 21 - 11*t := by linarith
  have hf5 : 0 < 25*t - 7 := by linarith
  have hf6 : 0 < 3 - t := by linarith
  have key : k89c_d3 (k89c_sub (k89c_P t 6) (k89c_P t 1)) (k89c_vel t (k89c_P t 1)) k89c_w0 = (((((((4) * (t + 1)) * (3*t - 1)) * (5*t - 3)) * (9*t - 7)) * (21 - 11*t)) * (25*t - 7)) / ((1) * (3 - t)) := by
    simp only [k89c_d3, k89c_sub, k89c_vel, k89c_add, k89c_cr, k89c_g, k89c_om, k89c_ta, k89c_o1, k89c_o2, k89c_o3, k89c_ta1, k89c_ta3, k89c_P, k89c_e, k89c_u, k89c_w0]
    field_simp
    ring
  rw [key]
  exact div_pos (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 4) hf0) hf1) hf2) hf3) hf4) hf5) (mul_pos (by norm_num : (0:ℝ) < 1) hf6)

set_option maxHeartbeats 16000000 in
theorem k89c_rB1 (t : ℝ) (ht1 : 1 < t) (ht2 : t ≤ 5/3) : 0 < k89c_d3 (k89c_sub (k89c_P t 1) (k89c_P t 0)) (k89c_vel t (k89c_P t 1)) k89c_w0 := by
  have h3 : (3 - t) ≠ 0 := by intro h; linarith
  have h0 : t ≠ 0 := by intro h; linarith
  have hf0 : 0 < t + 1 := by linarith
  have hf1 : 0 < 3*t - 1 := by linarith
  have hf2 : 0 < -277200*t^4 + 694206*t^3 - 328661*t^2 + 37072*t + 1715 := k89c_hq3 t ht1 ht2
  have key : k89c_d3 (k89c_sub (k89c_P t 1) (k89c_P t 0)) (k89c_vel t (k89c_P t 1)) k89c_w0 = ((((4) * (t + 1)) * (3*t - 1)) * (-277200*t^4 + 694206*t^3 - 328661*t^2 + 37072*t + 1715)) / (1) := by
    simp only [k89c_d3, k89c_sub, k89c_vel, k89c_add, k89c_cr, k89c_g, k89c_om, k89c_ta, k89c_o1, k89c_o2, k89c_o3, k89c_ta1, k89c_ta3, k89c_P, k89c_u, k89c_w0]
    field_simp
    ring
  rw [key]
  exact div_pos (mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 4) hf0) hf1) hf2) (by norm_num : (0:ℝ) < 1)

set_option maxHeartbeats 16000000 in
theorem k89c_conv2 (t : ℝ) (ht1 : 1 < t) (ht2 : t ≤ 5/3) : 0 < k89c_d3 (k89c_sub (k89c_P t 4) (k89c_P t 6)) (k89c_sub (k89c_P t 1) (k89c_P t 6)) k89c_w0 := by
  have h3 : (3 - t) ≠ 0 := by intro h; linarith
  have h0 : t ≠ 0 := by intro h; linarith
  have hf0 : 0 < t + 1 := by linarith
  have hf1 : 0 < 25*t - 7 := by linarith
  have hf2 : 0 < 3 - t := by linarith
  have key : k89c_d3 (k89c_sub (k89c_P t 4) (k89c_P t 6)) (k89c_sub (k89c_P t 1) (k89c_P t 6)) k89c_w0 = (((1) * (t + 1)) * (25*t - 7)) / ((1) * (3 - t)^2) := by
    simp only [k89c_d3, k89c_sub, k89c_P, k89c_e, k89c_w0]
    field_simp
    ring
  rw [key]
  exact div_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 1) hf0) hf1) (mul_pos (by norm_num : (0:ℝ) < 1) (pow_pos hf2 2))

set_option maxHeartbeats 16000000 in
theorem k89c_rA2 (t : ℝ) (ht1 : 1 < t) (ht2 : t ≤ 5/3) : 0 < k89c_d3 (k89c_sub (k89c_P t 4) (k89c_P t 6)) (k89c_vel t (k89c_P t 6)) k89c_w0 := by
  have h3 : (3 - t) ≠ 0 := by intro h; linarith
  have h0 : t ≠ 0 := by intro h; linarith
  have hf0 : 0 < 3*t - 1 := by linarith
  have hf1 : 0 < 25*t - 7 := by linarith
  have hf2 : 0 < t + 1 := by linarith
  have hf3 : 0 < 66000*t^5 - 363855*t^4 + 585765*t^3 - 258359*t^2 + 30503*t + 1442 := k89c_hq4 t ht1 ht2
  have hf4 : 0 < 3 - t := by linarith
  have key : k89c_d3 (k89c_sub (k89c_P t 4) (k89c_P t 6)) (k89c_vel t (k89c_P t 6)) k89c_w0 = (((((2) * (3*t - 1)) * (25*t - 7)) * (t + 1)^2) * (66000*t^5 - 363855*t^4 + 585765*t^3 - 258359*t^2 + 30503*t + 1442)) / ((1) * (3 - t)^2) := by
    simp only [k89c_d3, k89c_sub, k89c_vel, k89c_add, k89c_cr, k89c_g, k89c_om, k89c_ta, k89c_o1, k89c_o2, k89c_o3, k89c_ta1, k89c_ta3, k89c_P, k89c_e, k89c_u, k89c_w0]
    field_simp
    ring
  rw [key]
  exact div_pos (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 2) hf0) hf1) (pow_pos hf2 2)) hf3) (mul_pos (by norm_num : (0:ℝ) < 1) (pow_pos hf4 2))

set_option maxHeartbeats 16000000 in
theorem k89c_rB2 (t : ℝ) (ht1 : 1 < t) (ht2 : t ≤ 5/3) : 0 < k89c_d3 (k89c_sub (k89c_P t 6) (k89c_P t 1)) (k89c_vel t (k89c_P t 6)) k89c_w0 := by
  have h3 : (3 - t) ≠ 0 := by intro h; linarith
  have h0 : t ≠ 0 := by intro h; linarith
  have hf0 : 0 < t + 1 := by linarith
  have hf1 : 0 < 3*t - 1 := by linarith
  have hf2 : 0 < 5*t - 3 := by linarith
  have hf3 : 0 < 9*t - 7 := by linarith
  have hf4 : 0 < 21 - 11*t := by linarith
  have hf5 : 0 < 25*t - 7 := by linarith
  have hf6 : 0 < 3 - t := by linarith
  have key : k89c_d3 (k89c_sub (k89c_P t 6) (k89c_P t 1)) (k89c_vel t (k89c_P t 6)) k89c_w0 = (((((((4) * (t + 1)) * (3*t - 1)) * (5*t - 3)) * (9*t - 7)) * (21 - 11*t)) * (25*t - 7)) / ((1) * (3 - t)^2) := by
    simp only [k89c_d3, k89c_sub, k89c_vel, k89c_add, k89c_cr, k89c_g, k89c_om, k89c_ta, k89c_o1, k89c_o2, k89c_o3, k89c_ta1, k89c_ta3, k89c_P, k89c_e, k89c_u, k89c_w0]
    field_simp
    ring
  rw [key]
  exact div_pos (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 4) hf0) hf1) hf2) hf3) hf4) hf5) (mul_pos (by norm_num : (0:ℝ) < 1) (pow_pos hf6 2))

set_option maxHeartbeats 16000000 in
theorem k89c_conv3 (t : ℝ) (ht1 : 1 < t) (ht2 : t ≤ 5/3) : 0 < k89c_d3 (k89c_sub (k89c_P t 3) (k89c_P t 4)) (k89c_sub (k89c_P t 6) (k89c_P t 4)) k89c_w0 := by
  have h3 : (3 - t) ≠ 0 := by intro h; linarith
  have h0 : t ≠ 0 := by intro h; linarith
  have hf0 : 0 < t + 1 := by linarith
  have hf1 : 0 < 25*t - 7 := by linarith
  have hf2 : 0 < 3 - t := by linarith
  have key : k89c_d3 (k89c_sub (k89c_P t 3) (k89c_P t 4)) (k89c_sub (k89c_P t 6) (k89c_P t 4)) k89c_w0 = (((1) * (t + 1)) * (25*t - 7)) / ((1) * (3 - t)^2) := by
    simp only [k89c_d3, k89c_sub, k89c_P, k89c_e, k89c_w0]
    field_simp
    ring
  rw [key]
  exact div_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 1) hf0) hf1) (mul_pos (by norm_num : (0:ℝ) < 1) (pow_pos hf2 2))

set_option maxHeartbeats 16000000 in
theorem k89c_rA3 (t : ℝ) (ht1 : 1 < t) (ht2 : t ≤ 5/3) : 0 < k89c_d3 (k89c_sub (k89c_P t 3) (k89c_P t 4)) (k89c_vel t (k89c_P t 4)) k89c_w0 := by
  have h3 : (3 - t) ≠ 0 := by intro h; linarith
  have h0 : t ≠ 0 := by intro h; linarith
  have hf0 : 0 < t + 1 := by linarith
  have hf1 : 0 < 3*t - 1 := by linarith
  have hf2 : 0 < 5*t - 3 := by linarith
  have hf3 : 0 < 9*t - 7 := by linarith
  have hf4 : 0 < 21 - 11*t := by linarith
  have hf5 : 0 < 25*t - 7 := by linarith
  have hf6 : 0 < 3 - t := by linarith
  have key : k89c_d3 (k89c_sub (k89c_P t 3) (k89c_P t 4)) (k89c_vel t (k89c_P t 4)) k89c_w0 = (((((((4) * (t + 1)) * (3*t - 1)) * (5*t - 3)) * (9*t - 7)) * (21 - 11*t)) * (25*t - 7)) / ((1) * (3 - t)^2) := by
    simp only [k89c_d3, k89c_sub, k89c_vel, k89c_add, k89c_cr, k89c_g, k89c_om, k89c_ta, k89c_o1, k89c_o2, k89c_o3, k89c_ta1, k89c_ta3, k89c_P, k89c_e, k89c_u, k89c_w0]
    field_simp
    ring
  rw [key]
  exact div_pos (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 4) hf0) hf1) hf2) hf3) hf4) hf5) (mul_pos (by norm_num : (0:ℝ) < 1) (pow_pos hf6 2))

set_option maxHeartbeats 16000000 in
theorem k89c_rB3 (t : ℝ) (ht1 : 1 < t) (ht2 : t ≤ 5/3) : 0 < k89c_d3 (k89c_sub (k89c_P t 4) (k89c_P t 6)) (k89c_vel t (k89c_P t 4)) k89c_w0 := by
  have h3 : (3 - t) ≠ 0 := by intro h; linarith
  have h0 : t ≠ 0 := by intro h; linarith
  have hf0 : 0 < 3*t - 1 := by linarith
  have hf1 : 0 < 5*t - 3 := by linarith
  have hf2 : 0 < 9*t - 7 := by linarith
  have hf3 : 0 < 21 - 11*t := by linarith
  have hf4 : 0 < 25*t - 7 := by linarith
  have hf5 : 0 < t + 1 := by linarith
  have hf6 : 0 < 3 - t := by linarith
  have key : k89c_d3 (k89c_sub (k89c_P t 4) (k89c_P t 6)) (k89c_vel t (k89c_P t 4)) k89c_w0 = (((((((4) * (3*t - 1)) * (5*t - 3)) * (9*t - 7)) * (21 - 11*t)) * (25*t - 7)) * (t + 1)^2) / ((1) * (3 - t)^2) := by
    simp only [k89c_d3, k89c_sub, k89c_vel, k89c_add, k89c_cr, k89c_g, k89c_om, k89c_ta, k89c_o1, k89c_o2, k89c_o3, k89c_ta1, k89c_ta3, k89c_P, k89c_e, k89c_u, k89c_w0]
    field_simp
    ring
  rw [key]
  exact div_pos (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 4) hf0) hf1) hf2) hf3) hf4) (pow_pos hf5 2)) (mul_pos (by norm_num : (0:ℝ) < 1) (pow_pos hf6 2))

set_option maxHeartbeats 16000000 in
theorem k89c_conv4 (t : ℝ) (ht1 : 1 < t) (ht2 : t ≤ 5/3) : 0 < k89c_d3 (k89c_sub (k89c_P t 0) (k89c_P t 3)) (k89c_sub (k89c_P t 4) (k89c_P t 3)) k89c_w0 := by
  have h3 : (3 - t) ≠ 0 := by intro h; linarith
  have h0 : t ≠ 0 := by intro h; linarith
  have hf0 : 0 < t + 1 := by linarith
  have hf1 : 0 < 3 - t := by linarith
  have key : k89c_d3 (k89c_sub (k89c_P t 0) (k89c_P t 3)) (k89c_sub (k89c_P t 4) (k89c_P t 3)) k89c_w0 = ((2) * (t + 1)) / ((1) * (3 - t)) := by
    simp only [k89c_d3, k89c_sub, k89c_P, k89c_e, k89c_w0]
    field_simp
    ring
  rw [key]
  exact div_pos (mul_pos (by norm_num : (0:ℝ) < 2) hf0) (mul_pos (by norm_num : (0:ℝ) < 1) hf1)

set_option maxHeartbeats 16000000 in
theorem k89c_rA4 (t : ℝ) (ht1 : 1 < t) (ht2 : t ≤ 5/3) : 0 < k89c_d3 (k89c_sub (k89c_P t 0) (k89c_P t 3)) (k89c_vel t (k89c_P t 3)) k89c_w0 := by
  have h3 : (3 - t) ≠ 0 := by intro h; linarith
  have h0 : t ≠ 0 := by intro h; linarith
  have hf0 : 0 < 3*t - 1 := by linarith
  have hf1 : 0 < 9*t - 7 := by linarith
  have hf2 : 0 < 66000*t^5 - 443055*t^4 + 785791*t^3 - 357691*t^2 + 46057*t + 546 := k89c_hq8 t ht1 ht2
  have key : k89c_d3 (k89c_sub (k89c_P t 0) (k89c_P t 3)) (k89c_vel t (k89c_P t 3)) k89c_w0 = ((((4) * (3*t - 1)) * (9*t - 7)) * (66000*t^5 - 443055*t^4 + 785791*t^3 - 357691*t^2 + 46057*t + 546)) / (1) := by
    simp only [k89c_d3, k89c_sub, k89c_vel, k89c_add, k89c_cr, k89c_g, k89c_om, k89c_ta, k89c_o1, k89c_o2, k89c_o3, k89c_ta1, k89c_ta3, k89c_P, k89c_u, k89c_w0]
    field_simp
    ring
  rw [key]
  exact div_pos (mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 4) hf0) hf1) hf2) (by norm_num : (0:ℝ) < 1)

set_option maxHeartbeats 16000000 in
theorem k89c_rB4 (t : ℝ) (ht1 : 1 < t) (ht2 : t ≤ 5/3) : 0 < k89c_d3 (k89c_sub (k89c_P t 3) (k89c_P t 4)) (k89c_vel t (k89c_P t 3)) k89c_w0 := by
  have h3 : (3 - t) ≠ 0 := by intro h; linarith
  have h0 : t ≠ 0 := by intro h; linarith
  have hf0 : 0 < t - 1 := by linarith
  have hf1 : 0 < 3*t - 1 := by linarith
  have hf2 : 0 < 25*t - 7 := by linarith
  have hf3 : 0 < 66000*t^5 - 443055*t^4 + 785736*t^3 - 357608*t^2 + 46132*t + 483 := k89c_hq9 t ht1 ht2
  have hf4 : 0 < 3 - t := by linarith
  have key : k89c_d3 (k89c_sub (k89c_P t 3) (k89c_P t 4)) (k89c_vel t (k89c_P t 3)) k89c_w0 = (((((4) * (t - 1)) * (3*t - 1)) * (25*t - 7)) * (66000*t^5 - 443055*t^4 + 785736*t^3 - 357608*t^2 + 46132*t + 483)) / ((1) * (3 - t)) := by
    simp only [k89c_d3, k89c_sub, k89c_vel, k89c_add, k89c_cr, k89c_g, k89c_om, k89c_ta, k89c_o1, k89c_o2, k89c_o3, k89c_ta1, k89c_ta3, k89c_P, k89c_e, k89c_u, k89c_w0]
    field_simp
    ring
  rw [key]
  exact div_pos (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 4) hf0) hf1) hf2) hf3) (mul_pos (by norm_num : (0:ℝ) < 1) hf4)

set_option maxHeartbeats 16000000 in
theorem k89c_ia1 (t : ℝ) (ht1 : 1 < t) (ht2 : t ≤ 5/3) : 0 < k89c_d3 (k89c_sub (k89c_P t 1) (k89c_P t 0)) (k89c_sub (k89c_P t 4) (k89c_P t 0)) k89c_w0 := by
  have h3 : (3 - t) ≠ 0 := by intro h; linarith
  have h0 : t ≠ 0 := by intro h; linarith
  have hf0 : 0 < t + 1 := by linarith
  have hf1 : 0 < 3 - t := by linarith
  have key : k89c_d3 (k89c_sub (k89c_P t 1) (k89c_P t 0)) (k89c_sub (k89c_P t 4) (k89c_P t 0)) k89c_w0 = ((15) * (t + 1)) / ((1) * (3 - t)) := by
    simp only [k89c_d3, k89c_sub, k89c_P, k89c_e, k89c_w0]
    field_simp
    ring
  rw [key]
  exact div_pos (mul_pos (by norm_num : (0:ℝ) < 15) hf0) (mul_pos (by norm_num : (0:ℝ) < 1) hf1)

set_option maxHeartbeats 16000000 in
theorem k89c_ia2 (t : ℝ) (ht1 : 1 < t) (ht2 : t ≤ 5/3) : 0 < k89c_d3 (k89c_sub (k89c_P t 1) (k89c_P t 0)) (k89c_sub (k89c_P t 2) (k89c_P t 0)) k89c_w0 := by
  have h3 : (3 - t) ≠ 0 := by intro h; linarith
  have h0 : t ≠ 0 := by intro h; linarith

  have key : k89c_d3 (k89c_sub (k89c_P t 1) (k89c_P t 0)) (k89c_sub (k89c_P t 2) (k89c_P t 0)) k89c_w0 = (7) / (1) := by
    simp only [k89c_d3, k89c_sub, k89c_P, k89c_w0]
    field_simp
    ring
  rw [key]
  exact div_pos (by norm_num : (0:ℝ) < 7) (by norm_num : (0:ℝ) < 1)

set_option maxHeartbeats 16000000 in
theorem k89c_ia3 (t : ℝ) (ht1 : 1 < t) (ht2 : t ≤ 5/3) : 0 < k89c_d3 (k89c_sub (k89c_P t 4) (k89c_P t 1)) (k89c_sub (k89c_P t 2) (k89c_P t 1)) k89c_w0 := by
  have h3 : (3 - t) ≠ 0 := by intro h; linarith
  have h0 : t ≠ 0 := by intro h; linarith
  have hf0 : 0 < 5*t - 2 := by linarith
  have hf1 : 0 < 3 - t := by linarith
  have key : k89c_d3 (k89c_sub (k89c_P t 4) (k89c_P t 1)) (k89c_sub (k89c_P t 2) (k89c_P t 1)) k89c_w0 = ((4) * (5*t - 2)) / ((1) * (3 - t)) := by
    simp only [k89c_d3, k89c_sub, k89c_P, k89c_e, k89c_w0]
    field_simp
    ring
  rw [key]
  exact div_pos (mul_pos (by norm_num : (0:ℝ) < 4) hf0) (mul_pos (by norm_num : (0:ℝ) < 1) hf1)

set_option maxHeartbeats 16000000 in
theorem k89c_ia4 (t : ℝ) (ht1 : 1 < t) (ht2 : t ≤ 5/3) : 0 < k89c_d3 (k89c_sub (k89c_P t 0) (k89c_P t 4)) (k89c_sub (k89c_P t 2) (k89c_P t 4)) k89c_w0 := by
  have h3 : (3 - t) ≠ 0 := by intro h; linarith
  have h0 : t ≠ 0 := by intro h; linarith
  have hf0 : 0 < t + 1 := by linarith
  have hf1 : 0 < 3 - t := by linarith
  have key : k89c_d3 (k89c_sub (k89c_P t 0) (k89c_P t 4)) (k89c_sub (k89c_P t 2) (k89c_P t 4)) k89c_w0 = ((2) * (t + 1)) / ((1) * (3 - t)) := by
    simp only [k89c_d3, k89c_sub, k89c_P, k89c_e, k89c_w0]
    field_simp
    ring
  rw [key]
  exact div_pos (mul_pos (by norm_num : (0:ℝ) < 2) hf0) (mul_pos (by norm_num : (0:ℝ) < 1) hf1)

set_option maxHeartbeats 16000000 in
theorem k89c_ib1 (t : ℝ) (ht1 : 1 < t) (ht2 : t ≤ 5/3) : 0 < k89c_d3 (k89c_sub (k89c_P t 6) (k89c_P t 0)) (k89c_sub (k89c_P t 4) (k89c_P t 0)) k89c_w0 := by
  have h3 : (3 - t) ≠ 0 := by intro h; linarith
  have h0 : t ≠ 0 := by intro h; linarith
  have hf0 : 0 < t + 1 := by linarith
  have hf1 : 0 < 3 - t := by linarith
  have key : k89c_d3 (k89c_sub (k89c_P t 6) (k89c_P t 0)) (k89c_sub (k89c_P t 4) (k89c_P t 0)) k89c_w0 = ((17) * (t + 1)^2) / ((1) * (3 - t)^2) := by
    simp only [k89c_d3, k89c_sub, k89c_P, k89c_e, k89c_w0]
    field_simp
    ring
  rw [key]
  exact div_pos (mul_pos (by norm_num : (0:ℝ) < 17) (pow_pos hf0 2)) (mul_pos (by norm_num : (0:ℝ) < 1) (pow_pos hf1 2))

set_option maxHeartbeats 16000000 in
theorem k89c_ib2 (t : ℝ) (ht1 : 1 < t) (ht2 : t ≤ 5/3) : 0 < k89c_d3 (k89c_sub (k89c_P t 6) (k89c_P t 0)) (k89c_sub (k89c_P t 5) (k89c_P t 0)) k89c_w0 := by
  have h3 : (3 - t) ≠ 0 := by intro h; linarith
  have h0 : t ≠ 0 := by intro h; linarith
  have hf0 : 0 < t + 1 := by linarith
  have hf1 : 0 < 3 - t := by linarith
  have key : k89c_d3 (k89c_sub (k89c_P t 6) (k89c_P t 0)) (k89c_sub (k89c_P t 5) (k89c_P t 0)) k89c_w0 = ((3) * (t + 1)^2) / ((1) * (3 - t)^2) := by
    simp only [k89c_d3, k89c_sub, k89c_P, k89c_e, k89c_w0]
    field_simp
    ring
  rw [key]
  exact div_pos (mul_pos (by norm_num : (0:ℝ) < 3) (pow_pos hf0 2)) (mul_pos (by norm_num : (0:ℝ) < 1) (pow_pos hf1 2))

set_option maxHeartbeats 16000000 in
theorem k89c_ib3 (t : ℝ) (ht1 : 1 < t) (ht2 : t ≤ 5/3) : 0 < k89c_d3 (k89c_sub (k89c_P t 4) (k89c_P t 6)) (k89c_sub (k89c_P t 5) (k89c_P t 6)) k89c_w0 := by
  have h3 : (3 - t) ≠ 0 := by intro h; linarith
  have h0 : t ≠ 0 := by intro h; linarith
  have hf0 : 0 < t + 1 := by linarith
  have hf1 : 0 < 3 - t := by linarith
  have key : k89c_d3 (k89c_sub (k89c_P t 4) (k89c_P t 6)) (k89c_sub (k89c_P t 5) (k89c_P t 6)) k89c_w0 = ((1) * (t + 1)^2) / ((1) * (3 - t)^2) := by
    simp only [k89c_d3, k89c_sub, k89c_P, k89c_e, k89c_w0]
    field_simp
    ring
  rw [key]
  exact div_pos (mul_pos (by norm_num : (0:ℝ) < 1) (pow_pos hf0 2)) (mul_pos (by norm_num : (0:ℝ) < 1) (pow_pos hf1 2))

set_option maxHeartbeats 16000000 in
theorem k89c_ib4 (t : ℝ) (ht1 : 1 < t) (ht2 : t ≤ 5/3) : 0 < k89c_d3 (k89c_sub (k89c_P t 0) (k89c_P t 4)) (k89c_sub (k89c_P t 5) (k89c_P t 4)) k89c_w0 := by
  have h3 : (3 - t) ≠ 0 := by intro h; linarith
  have h0 : t ≠ 0 := by intro h; linarith
  have hf0 : 0 < t + 1 := by linarith
  have hf1 : 0 < 3 - t := by linarith
  have key : k89c_d3 (k89c_sub (k89c_P t 0) (k89c_P t 4)) (k89c_sub (k89c_P t 5) (k89c_P t 4)) k89c_w0 = ((13) * (t + 1)^2) / ((1) * (3 - t)^2) := by
    simp only [k89c_d3, k89c_sub, k89c_P, k89c_e, k89c_w0]
    field_simp
    ring
  rw [key]
  exact div_pos (mul_pos (by norm_num : (0:ℝ) < 13) (pow_pos hf0 2)) (mul_pos (by norm_num : (0:ℝ) < 1) (pow_pos hf1 2))

end
end Minimality.Type08Sp.C2
