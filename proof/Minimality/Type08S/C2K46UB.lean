module

public import Minimality.Type08S.C2K46UA

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace
open Minimality Minimality.Type08Sp

namespace Minimality.Type08Sp.C2


set_option maxHeartbeats 8000000 in
theorem k54U_conv0 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 ≤ 2 * σ^2) :
    0 < det3 ((k54U_p4 σ l m ea) - (k54U_p0 m)) ((k54U_p5 σ l m ea) - (k54U_p0 m)) (k54U_w σ l ea) := by
  have hpos : 0 < (m^2 * 3 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 4*σ^2 + 4)^1) / (2*(σ^2 + 1)) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54U_p0,k54U_p4,k54U_p5,k54U_w,det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54U_row0 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 ≤ 2 * σ^2) :
    0 < det3 ((k54U_p4 σ l m ea) - (k54U_p0 m)) (cross (k54U_om σ l) (k54U_p0 m) + (k54U_ta σ l m)) (k54U_w σ l ea) := by
  have hQ0 : 0 < -2*σ^4*(l^2) + 3*σ^2*(l^2) + 12*σ^2 + 12 := k54U_U_row0_f0 σ (l^2) hσ (by positivity) hR1 hR2 hp
  have hQ1 : 0 < 4*σ^7*(l^2) + 16*σ^7 - 12*σ^5*(l^2) - 32*σ^5 + 6*σ^4*(l^2) + 24*σ^4 + 14*σ^3*(l^2) - 16*σ^3 - 9*σ^2*(l^2) - 24*σ^2 + 32*σ - 48 := k54U_U_row0_f1 σ (l^2) hσ (by positivity) hR1 hR2 hp
  have hpos : 0 < m^2 * (l^2*σ/(2*(σ^2 + 1))) * 5 * (-2*σ^4*(l^2) + 3*σ^2*(l^2) + 12*σ^2 + 12) * (4*σ^7*(l^2) + 16*σ^7 - 12*σ^5*(l^2) - 32*σ^5 + 6*σ^4*(l^2) + 24*σ^4 + 14*σ^3*(l^2) - 16*σ^3 - 9*σ^2*(l^2) - 24*σ^2 + 32*σ - 48) * (5*σ^2*(l^2) + 12*σ^2 + 12)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^2 := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54U_p0,k54U_p4,k54U_om,k54U_ta,k54U_w,k54U_c1,k54U_c2,k54U_c3,k54U_c4,k54U_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54U_row1 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 ≤ 2 * σ^2) :
    0 < det3 ((k54U_p0 m) - (k54U_p5 σ l m ea)) (cross (k54U_om σ l) (k54U_p0 m) + (k54U_ta σ l m)) (k54U_w σ l ea) := by
  have hQ0 : 0 < (σ - 2) := k54U_U_det6 σ (l^2) hσ (by positivity) hR1 hR2 hp
  have hQ1 : 0 < -2*σ^4*(l^2) + 3*σ^2*(l^2) + 12*σ^2 + 12 := k54U_U_det7 σ (l^2) hσ (by positivity) hR1 hR2 hp
  have hpos : 0 < m^2 * (l^2*σ/(2*(σ^2 + 1))) * 80 * ((σ - 2)) * (σ^2 + 1)^1 * (σ + 2)^1 * (σ)^1 * (-2*σ^4*(l^2) + 3*σ^2*(l^2) + 12*σ^2 + 12) * (5*σ^2*(l^2) + 12*σ^2 + 12)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^3 := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54U_p0,k54U_p5,k54U_om,k54U_ta,k54U_w,k54U_c1,k54U_c2,k54U_c3,k54U_c4,k54U_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54U_conv1 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 ≤ 2 * σ^2) :
    0 < det3 ((k54U_p2 σ l m ea) - (k54U_p4 σ l m ea)) ((k54U_p0 m) - (k54U_p4 σ l m ea)) (k54U_w σ l ea) := by
  have hpos : 0 < (m^2 * 1 * (σ^2 + 1)^1 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^1) / (4*(σ^2 + 1)^3) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54U_p0,k54U_p2,k54U_p4,k54U_w,det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54U_row2 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 ≤ 2 * σ^2) :
    0 < det3 ((k54U_p2 σ l m ea) - (k54U_p4 σ l m ea)) (cross (k54U_om σ l) (k54U_p4 σ l m ea) + (k54U_ta σ l m)) (k54U_w σ l ea) := by
  have hQ0 : 0 < (σ - 2) := k54U_U_det6 σ (l^2) hσ (by positivity) hR1 hR2 hp
  have hQ1 : 0 < -2*σ^4*(l^2) + 3*σ^2*(l^2) + 12*σ^2 + 12 := k54U_U_det7 σ (l^2) hσ (by positivity) hR1 hR2 hp
  have hpos : 0 < m^2 * (l^2*(l^2*σ^2 + 2*σ^2 + 2)/(8*(σ^2 + 1)^3)) * 80 * ((σ - 2)) * (σ^2 + 1)^1 * (σ + 2)^1 * (σ)^1 * (-2*σ^4*(l^2) + 3*σ^2*(l^2) + 12*σ^2 + 12) * (5*σ^2*(l^2) + 12*σ^2 + 12)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^3 := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54U_p2,k54U_p4,k54U_om,k54U_ta,k54U_w,k54U_c1,k54U_c2,k54U_c3,k54U_c4,k54U_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54U_row3 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 ≤ 2 * σ^2) :
    0 < det3 ((k54U_p4 σ l m ea) - (k54U_p0 m)) (cross (k54U_om σ l) (k54U_p4 σ l m ea) + (k54U_ta σ l m)) (k54U_w σ l ea) := by
  have hQ0 : 0 < -20*σ^13*(l^2)^3 - 160*σ^13*(l^2)^2 - 320*σ^13*(l^2) + 140*σ^11*(l^2)^3 + 1040*σ^11*(l^2)^2 + 2400*σ^11*(l^2) + 1920*σ^11 - 30*σ^10*(l^2)^3 - 240*σ^10*(l^2)^2 - 480*σ^10*(l^2) - 10*σ^9*(l^2)^3 + 768*σ^9*(l^2)^2 + 2752*σ^9*(l^2) + 245*σ^8*(l^2)^3 + 1820*σ^8*(l^2)^2 + 4080*σ^8*(l^2) + 2880*σ^8 - 320*σ^7*(l^2)^3 - 3232*σ^7*(l^2)^2 - 11056*σ^7*(l^2) - 19200*σ^7 - 200*σ^6*(l^2)^3 - 140*σ^6*(l^2)^2 + 1080*σ^6*(l^2) - 2880*σ^6 - 2948*σ^5*(l^2)^2 - 19680*σ^5*(l^2) - 38400*σ^5 - 2210*σ^4*(l^2)^2 - 12000*σ^4*(l^2) - 25920*σ^4 - 148*σ^3*(l^2)^2 - 9104*σ^3*(l^2) - 28800*σ^3 - 10*σ^2*(l^2)^2 - 8520*σ^2*(l^2) - 31680*σ^2 - 512*σ*(l^2) - 7680*σ - 11520 := k54U_U_row3_f2 σ (l^2) hσ (by positivity) hR1 hR2 hp
  have hpos : 0 < m^2 * (l^2/(4*(σ^2 + 1)^2)) * 4 * (σ^2 + 1)^1 * (σ)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^1 * (5*σ^2*(l^2) + 12*σ^2 + 12)^1 * (-20*σ^13*(l^2)^3 - 160*σ^13*(l^2)^2 - 320*σ^13*(l^2) + 140*σ^11*(l^2)^3 + 1040*σ^11*(l^2)^2 + 2400*σ^11*(l^2) + 1920*σ^11 - 30*σ^10*(l^2)^3 - 240*σ^10*(l^2)^2 - 480*σ^10*(l^2) - 10*σ^9*(l^2)^3 + 768*σ^9*(l^2)^2 + 2752*σ^9*(l^2) + 245*σ^8*(l^2)^3 + 1820*σ^8*(l^2)^2 + 4080*σ^8*(l^2) + 2880*σ^8 - 320*σ^7*(l^2)^3 - 3232*σ^7*(l^2)^2 - 11056*σ^7*(l^2) - 19200*σ^7 - 200*σ^6*(l^2)^3 - 140*σ^6*(l^2)^2 + 1080*σ^6*(l^2) - 2880*σ^6 - 2948*σ^5*(l^2)^2 - 19680*σ^5*(l^2) - 38400*σ^5 - 2210*σ^4*(l^2)^2 - 12000*σ^4*(l^2) - 25920*σ^4 - 148*σ^3*(l^2)^2 - 9104*σ^3*(l^2) - 28800*σ^3 - 10*σ^2*(l^2)^2 - 8520*σ^2*(l^2) - 31680*σ^2 - 512*σ*(l^2) - 7680*σ - 11520) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54U_p0,k54U_p4,k54U_om,k54U_ta,k54U_w,k54U_c1,k54U_c2,k54U_c3,k54U_c4,k54U_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54U_conv2 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 ≤ 2 * σ^2) :
    0 < det3 ((k54U_p3 σ l m ea) - (k54U_p2 σ l m ea)) ((k54U_p4 σ l m ea) - (k54U_p2 σ l m ea)) (k54U_w σ l ea) := by
  have hpos : 0 < (m^2 * 5 * (σ^2 + 1)^3 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^2) / (8*(σ^2 + 1)^6) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54U_p2,k54U_p3,k54U_p4,k54U_w,det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54U_row4 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 ≤ 2 * σ^2) :
    0 < det3 ((k54U_p3 σ l m ea) - (k54U_p2 σ l m ea)) (cross (k54U_om σ l) (k54U_p2 σ l m ea) + (k54U_ta σ l m)) (k54U_w σ l ea) := by
  have hQ0 : 0 < 20*σ^11*(l^2)^2 + 80*σ^11*(l^2) - 60*σ^9*(l^2)^2 - 160*σ^9*(l^2) + 6*σ^8*(l^2)^2 + 24*σ^8*(l^2) - 26*σ^7*(l^2)^2 + 32*σ^7*(l^2) + 1344*σ^7 + 7*σ^6*(l^2)^2 + 216*σ^6*(l^2) + 576*σ^6 + 28*σ^5*(l^2)^2 + 480*σ^5*(l^2) + 3072*σ^5 + 6*σ^4*(l^2)^2 + 360*σ^4*(l^2) + 1728*σ^4 + 74*σ^3*(l^2)^2 + 464*σ^3*(l^2) + 2112*σ^3 + 5*σ^2*(l^2)^2 + 168*σ^2*(l^2) + 1728*σ^2 + 256*σ*(l^2) + 384*σ + 576 := k54U_U_row4_f3 σ (l^2) hσ (by positivity) hR1 hR2 hp
  have hpos : 0 < m^2 * (l^2*(l^2*σ^2 + 4*σ^2 + 4)/(8*(σ^2 + 1)^3)) * 20 * (σ^2 + 1)^1 * (σ)^1 * (5*σ^2*(l^2) + 12*σ^2 + 12)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^2 * (20*σ^11*(l^2)^2 + 80*σ^11*(l^2) - 60*σ^9*(l^2)^2 - 160*σ^9*(l^2) + 6*σ^8*(l^2)^2 + 24*σ^8*(l^2) - 26*σ^7*(l^2)^2 + 32*σ^7*(l^2) + 1344*σ^7 + 7*σ^6*(l^2)^2 + 216*σ^6*(l^2) + 576*σ^6 + 28*σ^5*(l^2)^2 + 480*σ^5*(l^2) + 3072*σ^5 + 6*σ^4*(l^2)^2 + 360*σ^4*(l^2) + 1728*σ^4 + 74*σ^3*(l^2)^2 + 464*σ^3*(l^2) + 2112*σ^3 + 5*σ^2*(l^2)^2 + 168*σ^2*(l^2) + 1728*σ^2 + 256*σ*(l^2) + 384*σ + 576) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54U_p2,k54U_p3,k54U_om,k54U_ta,k54U_w,k54U_c1,k54U_c2,k54U_c3,k54U_c4,k54U_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54U_row5 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 ≤ 2 * σ^2) :
    0 < det3 ((k54U_p2 σ l m ea) - (k54U_p4 σ l m ea)) (cross (k54U_om σ l) (k54U_p2 σ l m ea) + (k54U_ta σ l m)) (k54U_w σ l ea) := by
  have hQ0 : 0 < (σ - 2) := k54U_U_det6 σ (l^2) hσ (by positivity) hR1 hR2 hp
  have hQ1 : 0 < -2*σ^4*(l^2) + 3*σ^2*(l^2) + 12*σ^2 + 12 := k54U_U_det7 σ (l^2) hσ (by positivity) hR1 hR2 hp
  have hpos : 0 < m^2 * (l^2*(l^2*σ^2 + 2*σ^2 + 2)/(8*(σ^2 + 1)^3)) * 80 * ((σ - 2)) * (σ^2 + 1)^1 * (σ + 2)^1 * (σ)^1 * (-2*σ^4*(l^2) + 3*σ^2*(l^2) + 12*σ^2 + 12) * (5*σ^2*(l^2) + 12*σ^2 + 12)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^3 := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54U_p2,k54U_p4,k54U_om,k54U_ta,k54U_w,k54U_c1,k54U_c2,k54U_c3,k54U_c4,k54U_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54U_conv3 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 ≤ 2 * σ^2) :
    0 < det3 ((k54U_p5 σ l m ea) - (k54U_p3 σ l m ea)) ((k54U_p2 σ l m ea) - (k54U_p3 σ l m ea)) (k54U_w σ l ea) := by
  have hpos : 0 < (m^2 * 5 * (σ^2 + 1)^3 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^2) / (8*(σ^2 + 1)^6) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54U_p2,k54U_p3,k54U_p5,k54U_w,det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54U_row6 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 ≤ 2 * σ^2) :
    0 < det3 ((k54U_p5 σ l m ea) - (k54U_p3 σ l m ea)) (cross (k54U_om σ l) (k54U_p3 σ l m ea) + (k54U_ta σ l m)) (k54U_w σ l ea) := by
  have hQ0 : 0 < (σ - 2) := k54U_U_det6 σ (l^2) hσ (by positivity) hR1 hR2 hp
  have hQ1 : 0 < -2*σ^4*(l^2) + 3*σ^2*(l^2) + 12*σ^2 + 12 := k54U_U_det7 σ (l^2) hσ (by positivity) hR1 hR2 hp
  have hpos : 0 < m^2 * (l^2*σ*(l^2*σ^2 + 2*σ^2 + 2)/(8*(σ^2 + 1)^3)) * 80 * ((σ - 2)) * (σ^2 + 1)^1 * (σ + 2)^1 * (σ)^1 * (-2*σ^4*(l^2) + 3*σ^2*(l^2) + 12*σ^2 + 12) * (5*σ^2*(l^2) + 12*σ^2 + 12)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^3 := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54U_p3,k54U_p5,k54U_om,k54U_ta,k54U_w,k54U_c1,k54U_c2,k54U_c3,k54U_c4,k54U_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54U_row7 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 ≤ 2 * σ^2) :
    0 < det3 ((k54U_p3 σ l m ea) - (k54U_p2 σ l m ea)) (cross (k54U_om σ l) (k54U_p3 σ l m ea) + (k54U_ta σ l m)) (k54U_w σ l ea) := by
  have hQ0 : 0 < (σ - 2) := k54U_U_det6 σ (l^2) hσ (by positivity) hR1 hR2 hp
  have hQ1 : 0 < -2*σ^4*(l^2) + 3*σ^2*(l^2) + 12*σ^2 + 12 := k54U_U_det7 σ (l^2) hσ (by positivity) hR1 hR2 hp
  have hpos : 0 < m^2 * (l^2*σ*(l^2*σ^2 + 4*σ^2 + 4)/(8*(σ^2 + 1)^3)) * 80 * ((σ - 2)) * (σ^2 + 1)^1 * (σ + 2)^1 * (σ)^1 * (-2*σ^4*(l^2) + 3*σ^2*(l^2) + 12*σ^2 + 12) * (5*σ^2*(l^2) + 12*σ^2 + 12)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^3 := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54U_p2,k54U_p3,k54U_om,k54U_ta,k54U_w,k54U_c1,k54U_c2,k54U_c3,k54U_c4,k54U_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54U_conv4 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 ≤ 2 * σ^2) :
    0 < det3 ((k54U_p0 m) - (k54U_p5 σ l m ea)) ((k54U_p3 σ l m ea) - (k54U_p5 σ l m ea)) (k54U_w σ l ea) := by
  have hpos : 0 < (m^2 * 1 * (σ^2 + 1)^1 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^1) / (4*(σ^2 + 1)^3) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54U_p0,k54U_p3,k54U_p5,k54U_w,det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54U_row8 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 ≤ 2 * σ^2) :
    0 < det3 ((k54U_p0 m) - (k54U_p5 σ l m ea)) (cross (k54U_om σ l) (k54U_p5 σ l m ea) + (k54U_ta σ l m)) (k54U_w σ l ea) := by
  have hQ0 : 0 < -10*σ^12*(l^2)^3 - 60*σ^12*(l^2)^2 - 80*σ^12*(l^2) + 70*σ^10*(l^2)^3 + 476*σ^10*(l^2)^2 + 1104*σ^10*(l^2) + 960*σ^10 - 5*σ^8*(l^2)^3 + 316*σ^8*(l^2)^2 + 1328*σ^8*(l^2) + 1440*σ^8 + 40*σ^7*(l^2)^3 + 320*σ^7*(l^2)^2 + 840*σ^7*(l^2) + 720*σ^7 - 160*σ^6*(l^2)^3 - 1616*σ^6*(l^2)^2 - 5000*σ^6*(l^2) - 5280*σ^6 - 10*σ^5*(l^2)^3 + 270*σ^5*(l^2)^2 + 1620*σ^5*(l^2) + 2160*σ^5 - 1396*σ^4*(l^2)^2 - 9168*σ^4*(l^2) - 14880*σ^4 - 50*σ^3*(l^2)^2 + 720*σ^3*(l^2) + 2160*σ^3 - 4024*σ^2*(l^2) - 12960*σ^2 - 60*σ*(l^2) + 720*σ - 3840 := k54U_U_row8_f4 σ (l^2) hσ (by positivity) hR1 hR2 hp
  have hpos : 0 < m^2 * (l^2*σ/(4*(σ^2 + 1)^2)) * 32 * (σ^2 + 1)^1 * (σ)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^1 * (5*σ^2*(l^2) + 12*σ^2 + 12)^1 * (-10*σ^12*(l^2)^3 - 60*σ^12*(l^2)^2 - 80*σ^12*(l^2) + 70*σ^10*(l^2)^3 + 476*σ^10*(l^2)^2 + 1104*σ^10*(l^2) + 960*σ^10 - 5*σ^8*(l^2)^3 + 316*σ^8*(l^2)^2 + 1328*σ^8*(l^2) + 1440*σ^8 + 40*σ^7*(l^2)^3 + 320*σ^7*(l^2)^2 + 840*σ^7*(l^2) + 720*σ^7 - 160*σ^6*(l^2)^3 - 1616*σ^6*(l^2)^2 - 5000*σ^6*(l^2) - 5280*σ^6 - 10*σ^5*(l^2)^3 + 270*σ^5*(l^2)^2 + 1620*σ^5*(l^2) + 2160*σ^5 - 1396*σ^4*(l^2)^2 - 9168*σ^4*(l^2) - 14880*σ^4 - 50*σ^3*(l^2)^2 + 720*σ^3*(l^2) + 2160*σ^3 - 4024*σ^2*(l^2) - 12960*σ^2 - 60*σ*(l^2) + 720*σ - 3840) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54U_p0,k54U_p5,k54U_om,k54U_ta,k54U_w,k54U_c1,k54U_c2,k54U_c3,k54U_c4,k54U_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54U_row9 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 ≤ 2 * σ^2) :
    0 < det3 ((k54U_p5 σ l m ea) - (k54U_p3 σ l m ea)) (cross (k54U_om σ l) (k54U_p5 σ l m ea) + (k54U_ta σ l m)) (k54U_w σ l ea) := by
  have hQ0 : 0 < -20*σ^13*(l^2)^3 - 120*σ^13*(l^2)^2 - 160*σ^13*(l^2) + 140*σ^11*(l^2)^3 + 944*σ^11*(l^2)^2 + 2176*σ^11*(l^2) + 1920*σ^11 + 2*σ^10*(l^2)^3 + 12*σ^10*(l^2)^2 + 16*σ^10*(l^2) - 10*σ^9*(l^2)^3 + 668*σ^9*(l^2)^2 + 2816*σ^9*(l^2) + 3072*σ^9 + 69*σ^8*(l^2)^3 + 574*σ^8*(l^2)^2 + 1552*σ^8*(l^2) + 1344*σ^8 - 320*σ^7*(l^2)^3 - 3236*σ^7*(l^2)^2 - 9968*σ^7*(l^2) - 10752*σ^7 - 8*σ^6*(l^2)^3 + 582*σ^6*(l^2)^2 + 3320*σ^6*(l^2) + 4416*σ^6 - 2840*σ^5*(l^2)^2 - 18880*σ^5*(l^2) - 31488*σ^5 + 20*σ^4*(l^2)^2 + 2048*σ^4*(l^2) + 5184*σ^4 - 8432*σ^3*(l^2) - 28032*σ^3 + 264*σ^2*(l^2) + 2496*σ^2 - 8448*σ + 384 := k54U_U_row9_f5 σ (l^2) hσ (by positivity) hR1 hR2 hp
  have hpos : 0 < m^2 * (l^2*σ*(l^2*σ^2 + 2*σ^2 + 2)/(8*(σ^2 + 1)^3)) * 20 * (σ^2 + 1)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^1 * (5*σ^2*(l^2) + 12*σ^2 + 12)^1 * (-20*σ^13*(l^2)^3 - 120*σ^13*(l^2)^2 - 160*σ^13*(l^2) + 140*σ^11*(l^2)^3 + 944*σ^11*(l^2)^2 + 2176*σ^11*(l^2) + 1920*σ^11 + 2*σ^10*(l^2)^3 + 12*σ^10*(l^2)^2 + 16*σ^10*(l^2) - 10*σ^9*(l^2)^3 + 668*σ^9*(l^2)^2 + 2816*σ^9*(l^2) + 3072*σ^9 + 69*σ^8*(l^2)^3 + 574*σ^8*(l^2)^2 + 1552*σ^8*(l^2) + 1344*σ^8 - 320*σ^7*(l^2)^3 - 3236*σ^7*(l^2)^2 - 9968*σ^7*(l^2) - 10752*σ^7 - 8*σ^6*(l^2)^3 + 582*σ^6*(l^2)^2 + 3320*σ^6*(l^2) + 4416*σ^6 - 2840*σ^5*(l^2)^2 - 18880*σ^5*(l^2) - 31488*σ^5 + 20*σ^4*(l^2)^2 + 2048*σ^4*(l^2) + 5184*σ^4 - 8432*σ^3*(l^2) - 28032*σ^3 + 264*σ^2*(l^2) + 2496*σ^2 - 8448*σ + 384) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54U_p3,k54U_p5,k54U_om,k54U_ta,k54U_w,k54U_c1,k54U_c2,k54U_c3,k54U_c4,k54U_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54U_int1tri {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 ≤ 2 * σ^2) :
    0 < det3 ((k54U_p2 σ l m ea) - (k54U_p0 m)) ((k54U_p3 σ l m ea) - (k54U_p0 m)) (k54U_w σ l ea) := by
  have hpos : 0 < (m^2 * 1 * (σ^2 + 1)^3 * (σ)^1 * (l)^2 * (5*σ^2*(l^2) + 16*σ^2 + 16)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^2) / (8*(σ^2 + 1)^6) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54U_p0,k54U_p2,k54U_p3,k54U_w,det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54U_int1e1 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 ≤ 2 * σ^2) :
    0 < det3 ((k54U_p2 σ l m ea) - (k54U_p0 m)) ((k54U_p1 m ea) - (k54U_p0 m)) (k54U_w σ l ea) := by
  have hpos : 0 < (m^2 * 1 * (σ^2 + 1)^1 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 4*σ^2 + 4)^2) / (4*(σ^2 + 1)^3) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54U_p0,k54U_p1,k54U_p2,k54U_w,det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54U_int1e2 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 ≤ 2 * σ^2) :
    0 < det3 ((k54U_p3 σ l m ea) - (k54U_p2 σ l m ea)) ((k54U_p1 m ea) - (k54U_p2 σ l m ea)) (k54U_w σ l ea) := by
  have hpos : 0 < (m^2 * 1 * (σ^2 + 1)^3 * (σ)^1 * (l)^2 * (5*σ^2*(l^2) + 12*σ^2 + 12)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^2) / (8*(σ^2 + 1)^6) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54U_p1,k54U_p2,k54U_p3,k54U_w,det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54U_int1e3 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 ≤ 2 * σ^2) :
    0 < det3 ((k54U_p0 m) - (k54U_p3 σ l m ea)) ((k54U_p1 m ea) - (k54U_p3 σ l m ea)) (k54U_w σ l ea) := by
  have hpos : 0 < (m^2 * 1 * (σ^2 + 1)^1 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 4*σ^2 + 4)^2) / (4*(σ^2 + 1)^3) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54U_p0,k54U_p1,k54U_p3,k54U_w,det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54U_int6tri {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 ≤ 2 * σ^2) :
    0 < det3 ((k54U_p2 σ l m ea) - (k54U_p0 m)) ((k54U_p3 σ l m ea) - (k54U_p0 m)) (k54U_w σ l ea) := by
  have hpos : 0 < (m^2 * 1 * (σ^2 + 1)^3 * (σ)^1 * (l)^2 * (5*σ^2*(l^2) + 16*σ^2 + 16)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^2) / (8*(σ^2 + 1)^6) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54U_p0,k54U_p2,k54U_p3,k54U_w,det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54U_int6e1 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 ≤ 2 * σ^2) :
    0 < det3 ((k54U_p2 σ l m ea) - (k54U_p0 m)) ((k54U_p6 σ l m ea) - (k54U_p0 m)) (k54U_w σ l ea) := by
  have hpos : 0 < (m^2 * 3 * (σ^2 + 1)^3 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 4*σ^2 + 4)^3) / (16*(σ^2 + 1)^6) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54U_p0,k54U_p2,k54U_p6,k54U_w,det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54U_int6e2 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 ≤ 2 * σ^2) :
    0 < det3 ((k54U_p3 σ l m ea) - (k54U_p2 σ l m ea)) ((k54U_p6 σ l m ea) - (k54U_p2 σ l m ea)) (k54U_w σ l ea) := by
  have hpos : 0 < (m^2 * 1 * (σ^2 + 1)^3 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^2) / (4*(σ^2 + 1)^6) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54U_p2,k54U_p3,k54U_p6,k54U_w,det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54U_int6e3 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 ≤ 2 * σ^2) :
    0 < det3 ((k54U_p0 m) - (k54U_p3 σ l m ea)) ((k54U_p6 σ l m ea) - (k54U_p3 σ l m ea)) (k54U_w σ l ea) := by
  have hpos : 0 < (m^2 * 3 * (σ^2 + 1)^3 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 4*σ^2 + 4)^3) / (16*(σ^2 + 1)^6) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54U_p0,k54U_p3,k54U_p6,k54U_w,det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two]
  field_simp
  ring

theorem k54U_regions {σ l ea : ℝ} (hσ : 0 < σ) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : ea ≤ σ^2 * (2 + ea)) (hR2 : ea * σ^2 < 2 + ea) :
    l^2*(1-σ^2) ≤ 4*(1+σ^2) ∧ l^2*σ^2*(σ^2-1) < 4*(1+σ^2) := by
  have hD : 0 < 1 + σ^2 := by positivity
  have hea' : 2*(1+σ^2)*ea = l^2*σ^2 := by rw [hea]; field_simp
  have h3 : 2*(1+σ^2)*ea*σ^2 = l^2*σ^2*σ^2 := by rw [hea']
  have hs2 : 0 < σ^2 := by positivity
  constructor
  · by_contra h
    push Not at h
    have h1 := mul_le_mul_of_nonneg_left hR1 (by positivity : (0:ℝ) ≤ 2*(1+σ^2))
    have h2 := mul_pos hs2 (sub_pos.2 h)
    nlinarith
  · have h1 := mul_lt_mul_of_pos_left hR2 (by positivity : (0:ℝ) < 2*(1+σ^2))
    nlinarith

set_option maxHeartbeats 8000000 in
theorem a2mc_U {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : ea ≤ σ^2 * (2 + ea)) (hR2 : ea * σ^2 < 2 + ea) (hp : 9 ≤ 2 * σ^2) :
    IsRupert (V8 (k54U_p1 m ea) (k54U_p6 σ l m ea) (k54U_p4 σ l m ea) (k54U_p3 σ l m ea) (k54U_p5 σ l m ea) (k54U_p2 σ l m ea) (k54U_p0 m)) := by
  obtain ⟨hr1, hr2⟩ := k54U_regions hσ hea hR1 hR2
  refine isRupert_of_tiltCert _ (k54U_w σ l ea) ?_ (k54U_om σ l) (k54U_ta σ l m) ?_
  · intro h
    have h1 := congrArg (fun v : ℝ³ => v 1) h
    simp only [k54U_w, pt_one] at h1
    simp at h1
    linarith
  · intro x hx
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · left
      exact ⟨(k54U_p5 σ l m ea), by simp [V8], (k54U_p4 σ l m ea), by simp [V8], k54U_conv0 hσ hl hm hea hr1 hr2 hp, k54U_row0 hσ hl hm hea hr1 hr2 hp, k54U_row1 hσ hl hm hea hr1 hr2 hp⟩
    · right
      exact ⟨(k54U_p0 m), by simp [V8], (k54U_p2 σ l m ea), by simp [V8], (k54U_p3 σ l m ea), by simp [V8], k54U_int1tri hσ hl hm hea hr1 hr2 hp, k54U_int1e1 hσ hl hm hea hr1 hr2 hp, k54U_int1e2 hσ hl hm hea hr1 hr2 hp, k54U_int1e3 hσ hl hm hea hr1 hr2 hp⟩
    · right
      exact ⟨(k54U_p0 m), by simp [V8], (k54U_p2 σ l m ea), by simp [V8], (k54U_p3 σ l m ea), by simp [V8], k54U_int6tri hσ hl hm hea hr1 hr2 hp, k54U_int6e1 hσ hl hm hea hr1 hr2 hp, k54U_int6e2 hσ hl hm hea hr1 hr2 hp, k54U_int6e3 hσ hl hm hea hr1 hr2 hp⟩
    · left
      exact ⟨(k54U_p0 m), by simp [V8], (k54U_p2 σ l m ea), by simp [V8], k54U_conv1 hσ hl hm hea hr1 hr2 hp, k54U_row2 hσ hl hm hea hr1 hr2 hp, k54U_row3 hσ hl hm hea hr1 hr2 hp⟩
    · left
      exact ⟨(k54U_p2 σ l m ea), by simp [V8], (k54U_p5 σ l m ea), by simp [V8], k54U_conv3 hσ hl hm hea hr1 hr2 hp, k54U_row6 hσ hl hm hea hr1 hr2 hp, k54U_row7 hσ hl hm hea hr1 hr2 hp⟩
    · left
      exact ⟨(k54U_p3 σ l m ea), by simp [V8], (k54U_p0 m), by simp [V8], k54U_conv4 hσ hl hm hea hr1 hr2 hp, k54U_row8 hσ hl hm hea hr1 hr2 hp, k54U_row9 hσ hl hm hea hr1 hr2 hp⟩
    · left
      exact ⟨(k54U_p4 σ l m ea), by simp [V8], (k54U_p3 σ l m ea), by simp [V8], k54U_conv2 hσ hl hm hea hr1 hr2 hp, k54U_row4 hσ hl hm hea hr1 hr2 hp, k54U_row5 hσ hl hm hea hr1 hr2 hp⟩

end Minimality.Type08Sp.C2
