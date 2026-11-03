module

public import Minimality.Type08S.C2K46LA

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace
open Minimality Minimality.Type08Sp

namespace Minimality.Type08Sp.C2


set_option maxHeartbeats 8000000 in
theorem k54L_conv0 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 * σ^2 ≤ 2) :
    0 < det3 ((k54L_p4 σ l m ea) - (k54L_p0 m)) ((k54L_p5 σ l m ea) - (k54L_p0 m)) (k54L_w σ l ea) := by
  have hpos : 0 < (m^2 * 3 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 4*σ^2 + 4)^1) / (2*(σ^2 + 1)) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54L_p0,k54L_p1,k54L_p2,k54L_p3,k54L_p4,k54L_p5,k54L_p6,k54L_om,k54L_ta,k54L_w,k54L_c1,k54L_c2,k54L_c3,k54L_c4,k54L_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54L_row0 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 * σ^2 ≤ 2) :
    0 < det3 ((k54L_p4 σ l m ea) - (k54L_p0 m)) (cross (k54L_om σ l) (k54L_p0 m) + (k54L_ta σ l m)) (k54L_w σ l ea) := by
  have hQ0 : 0 < -(2*σ - 1) := k54L_L_det6 σ (l^2) hσ (by positivity) hR1 hR2 hp
  have hQ1 : 0 < 3*σ^2*(l^2) + 12*σ^2 - 2*(l^2) + 12 := k54L_L_det7 σ (l^2) hσ (by positivity) hR1 hR2 hp
  have hpos : 0 < m^2 * (l^2*σ/(2*(σ^2 + 1))) * 80 * (σ^2 + 1)^1 * (-(2*σ - 1)) * (2*σ + 1)^1 * (σ)^1 * (3*σ^2*(l^2) + 12*σ^2 - 2*(l^2) + 12) * (5*σ^2*(l^2) + 12*σ^2 + 12)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^3 := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54L_p0,k54L_p1,k54L_p2,k54L_p3,k54L_p4,k54L_p5,k54L_p6,k54L_om,k54L_ta,k54L_w,k54L_c1,k54L_c2,k54L_c3,k54L_c4,k54L_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54L_row1 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 * σ^2 ≤ 2) :
    0 < det3 ((k54L_p0 m) - (k54L_p5 σ l m ea)) (cross (k54L_om σ l) (k54L_p0 m) + (k54L_ta σ l m)) (k54L_w σ l ea) := by
  have hQ0 : 0 < 3*σ^2*(l^2) + 12*σ^2 - 2*(l^2) + 12 := k54L_L_row1_f0 σ (l^2) hσ (by positivity) hR1 hR2 hp
  have hQ1 : 0 < -16*σ^6*(l^2) - 64*σ^6 - 21*σ^4*(l^2) - 160*σ^4 + 30*σ^3*(l^2) + 96*σ^3 + 10*σ^2*(l^2) - 56*σ^2 + 96*σ + 40 := k54L_L_row1_f1 σ (l^2) hσ (by positivity) hR1 hR2 hp
  have hpos : 0 < m^2 * (l^2*σ/(2*(σ^2 + 1))) * 5 * (σ)^1 * (3*σ^2*(l^2) + 12*σ^2 - 2*(l^2) + 12) * (5*σ^2*(l^2) + 12*σ^2 + 12)^1 * (-16*σ^6*(l^2) - 64*σ^6 - 21*σ^4*(l^2) - 160*σ^4 + 30*σ^3*(l^2) + 96*σ^3 + 10*σ^2*(l^2) - 56*σ^2 + 96*σ + 40) * (σ^2*(l^2) + 4*σ^2 + 4)^2 := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54L_p0,k54L_p1,k54L_p2,k54L_p3,k54L_p4,k54L_p5,k54L_p6,k54L_om,k54L_ta,k54L_w,k54L_c1,k54L_c2,k54L_c3,k54L_c4,k54L_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54L_conv1 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 * σ^2 ≤ 2) :
    0 < det3 ((k54L_p2 σ l m ea) - (k54L_p4 σ l m ea)) ((k54L_p0 m) - (k54L_p4 σ l m ea)) (k54L_w σ l ea) := by
  have hpos : 0 < (m^2 * 1 * (σ^2 + 1)^1 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^1) / (4*(σ^2 + 1)^3) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54L_p0,k54L_p1,k54L_p2,k54L_p3,k54L_p4,k54L_p5,k54L_p6,k54L_om,k54L_ta,k54L_w,k54L_c1,k54L_c2,k54L_c3,k54L_c4,k54L_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54L_row2 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 * σ^2 ≤ 2) :
    0 < det3 ((k54L_p2 σ l m ea) - (k54L_p4 σ l m ea)) (cross (k54L_om σ l) (k54L_p4 σ l m ea) + (k54L_ta σ l m)) (k54L_w σ l ea) := by
  have hQ0 : 0 < -320*σ^11*(l^2)^3 - 2880*σ^11*(l^2)^2 - 8320*σ^11*(l^2) - 7680*σ^11 - 168*σ^9*(l^2)^3 - 4540*σ^9*(l^2)^2 - 21976*σ^9*(l^2) - 28416*σ^9 + 40*σ^8*(l^2)^2 - 112*σ^8*(l^2) - 768*σ^8 + 209*σ^7*(l^2)^3 - 18*σ^7*(l^2)^2 - 14912*σ^7*(l^2) - 35904*σ^7 + 150*σ^6*(l^2)^3 + 1324*σ^6*(l^2)^2 + 3360*σ^6*(l^2) + 768*σ^6 - 18*σ^5*(l^2)^3 + 1534*σ^5*(l^2)^2 + 2680*σ^5*(l^2) - 14016*σ^5 + 1268*σ^4*(l^2)^2 + 6992*σ^4*(l^2) + 6912*σ^4 - 108*σ^3*(l^2)^2 + 3792*σ^3*(l^2) + 4416*σ^3 - 16*σ^2*(l^2)^2 + 3456*σ^2*(l^2) + 8448*σ^2 - 144*σ*(l^2) + 3264*σ - 64*(l^2) + 3072 := k54L_L_row2_f2 σ (l^2) hσ (by positivity) hR1 hR2 hp
  have hpos : 0 < m^2 * (l^2*(l^2*σ^2 + 2*σ^2 + 2)/(8*(σ^2 + 1)^3)) * 20 * (σ^2 + 1)^1 * (σ)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^1 * (5*σ^2*(l^2) + 12*σ^2 + 12)^1 * (-320*σ^11*(l^2)^3 - 2880*σ^11*(l^2)^2 - 8320*σ^11*(l^2) - 7680*σ^11 - 168*σ^9*(l^2)^3 - 4540*σ^9*(l^2)^2 - 21976*σ^9*(l^2) - 28416*σ^9 + 40*σ^8*(l^2)^2 - 112*σ^8*(l^2) - 768*σ^8 + 209*σ^7*(l^2)^3 - 18*σ^7*(l^2)^2 - 14912*σ^7*(l^2) - 35904*σ^7 + 150*σ^6*(l^2)^3 + 1324*σ^6*(l^2)^2 + 3360*σ^6*(l^2) + 768*σ^6 - 18*σ^5*(l^2)^3 + 1534*σ^5*(l^2)^2 + 2680*σ^5*(l^2) - 14016*σ^5 + 1268*σ^4*(l^2)^2 + 6992*σ^4*(l^2) + 6912*σ^4 - 108*σ^3*(l^2)^2 + 3792*σ^3*(l^2) + 4416*σ^3 - 16*σ^2*(l^2)^2 + 3456*σ^2*(l^2) + 8448*σ^2 - 144*σ*(l^2) + 3264*σ - 64*(l^2) + 3072) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54L_p0,k54L_p1,k54L_p2,k54L_p3,k54L_p4,k54L_p5,k54L_p6,k54L_om,k54L_ta,k54L_w,k54L_c1,k54L_c2,k54L_c3,k54L_c4,k54L_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54L_row3 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 * σ^2 ≤ 2) :
    0 < det3 ((k54L_p4 σ l m ea) - (k54L_p0 m)) (cross (k54L_om σ l) (k54L_p4 σ l m ea) + (k54L_ta σ l m)) (k54L_w σ l ea) := by
  have hQ0 : 0 < -160*σ^11*(l^2)^3 - 1440*σ^11*(l^2)^2 - 4160*σ^11*(l^2) - 3840*σ^11 - 90*σ^9*(l^2)^3 - 2330*σ^9*(l^2)^2 - 11180*σ^9*(l^2) - 14400*σ^9 + 44*σ^8*(l^2)^2 + 136*σ^8*(l^2) + 110*σ^7*(l^2)^3 - 30*σ^7*(l^2)^2 - 7760*σ^7*(l^2) - 18480*σ^7 + 75*σ^6*(l^2)^3 + 664*σ^6*(l^2)^2 + 1952*σ^6*(l^2) + 1440*σ^6 - 10*σ^5*(l^2)^3 + 800*σ^5*(l^2)^2 + 1300*σ^5*(l^2) - 7440*σ^5 + 616*σ^4*(l^2)^2 + 3480*σ^4*(l^2) + 4320*σ^4 - 60*σ^3*(l^2)^2 + 1960*σ^3*(l^2) + 2160*σ^3 - 4*σ^2*(l^2)^2 + 1648*σ^2*(l^2) + 4320*σ^2 - 80*σ*(l^2) + 1680*σ - 16*(l^2) + 1440 := k54L_L_row3_f3 σ (l^2) hσ (by positivity) hR1 hR2 hp
  have hpos : 0 < m^2 * (l^2/(4*(σ^2 + 1)^2)) * 32 * (σ^2 + 1)^1 * (σ)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^1 * (5*σ^2*(l^2) + 12*σ^2 + 12)^1 * (-160*σ^11*(l^2)^3 - 1440*σ^11*(l^2)^2 - 4160*σ^11*(l^2) - 3840*σ^11 - 90*σ^9*(l^2)^3 - 2330*σ^9*(l^2)^2 - 11180*σ^9*(l^2) - 14400*σ^9 + 44*σ^8*(l^2)^2 + 136*σ^8*(l^2) + 110*σ^7*(l^2)^3 - 30*σ^7*(l^2)^2 - 7760*σ^7*(l^2) - 18480*σ^7 + 75*σ^6*(l^2)^3 + 664*σ^6*(l^2)^2 + 1952*σ^6*(l^2) + 1440*σ^6 - 10*σ^5*(l^2)^3 + 800*σ^5*(l^2)^2 + 1300*σ^5*(l^2) - 7440*σ^5 + 616*σ^4*(l^2)^2 + 3480*σ^4*(l^2) + 4320*σ^4 - 60*σ^3*(l^2)^2 + 1960*σ^3*(l^2) + 2160*σ^3 - 4*σ^2*(l^2)^2 + 1648*σ^2*(l^2) + 4320*σ^2 - 80*σ*(l^2) + 1680*σ - 16*(l^2) + 1440) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54L_p0,k54L_p1,k54L_p2,k54L_p3,k54L_p4,k54L_p5,k54L_p6,k54L_om,k54L_ta,k54L_w,k54L_c1,k54L_c2,k54L_c3,k54L_c4,k54L_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54L_conv2 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 * σ^2 ≤ 2) :
    0 < det3 ((k54L_p3 σ l m ea) - (k54L_p2 σ l m ea)) ((k54L_p4 σ l m ea) - (k54L_p2 σ l m ea)) (k54L_w σ l ea) := by
  have hpos : 0 < (m^2 * 5 * (σ^2 + 1)^3 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^2) / (8*(σ^2 + 1)^6) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54L_p0,k54L_p1,k54L_p2,k54L_p3,k54L_p4,k54L_p5,k54L_p6,k54L_om,k54L_ta,k54L_w,k54L_c1,k54L_c2,k54L_c3,k54L_c4,k54L_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54L_row4 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 * σ^2 ≤ 2) :
    0 < det3 ((k54L_p3 σ l m ea) - (k54L_p2 σ l m ea)) (cross (k54L_om σ l) (k54L_p2 σ l m ea) + (k54L_ta σ l m)) (k54L_w σ l ea) := by
  have hQ0 : 0 < -(2*σ - 1) := k54L_L_det6 σ (l^2) hσ (by positivity) hR1 hR2 hp
  have hQ1 : 0 < 3*σ^2*(l^2) + 12*σ^2 - 2*(l^2) + 12 := k54L_L_det7 σ (l^2) hσ (by positivity) hR1 hR2 hp
  have hpos : 0 < m^2 * (l^2*(l^2*σ^2 + 4*σ^2 + 4)/(8*(σ^2 + 1)^3)) * 80 * (σ^2 + 1)^1 * (-(2*σ - 1)) * (2*σ + 1)^1 * (σ)^1 * (3*σ^2*(l^2) + 12*σ^2 - 2*(l^2) + 12) * (5*σ^2*(l^2) + 12*σ^2 + 12)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^3 := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54L_p0,k54L_p1,k54L_p2,k54L_p3,k54L_p4,k54L_p5,k54L_p6,k54L_om,k54L_ta,k54L_w,k54L_c1,k54L_c2,k54L_c3,k54L_c4,k54L_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54L_row5 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 * σ^2 ≤ 2) :
    0 < det3 ((k54L_p2 σ l m ea) - (k54L_p4 σ l m ea)) (cross (k54L_om σ l) (k54L_p2 σ l m ea) + (k54L_ta σ l m)) (k54L_w σ l ea) := by
  have hQ0 : 0 < -(2*σ - 1) := k54L_L_det6 σ (l^2) hσ (by positivity) hR1 hR2 hp
  have hQ1 : 0 < 3*σ^2*(l^2) + 12*σ^2 - 2*(l^2) + 12 := k54L_L_det7 σ (l^2) hσ (by positivity) hR1 hR2 hp
  have hpos : 0 < m^2 * (l^2*(l^2*σ^2 + 2*σ^2 + 2)/(8*(σ^2 + 1)^3)) * 80 * (σ^2 + 1)^1 * (-(2*σ - 1)) * (2*σ + 1)^1 * (σ)^1 * (3*σ^2*(l^2) + 12*σ^2 - 2*(l^2) + 12) * (5*σ^2*(l^2) + 12*σ^2 + 12)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^3 := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54L_p0,k54L_p1,k54L_p2,k54L_p3,k54L_p4,k54L_p5,k54L_p6,k54L_om,k54L_ta,k54L_w,k54L_c1,k54L_c2,k54L_c3,k54L_c4,k54L_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54L_conv3 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 * σ^2 ≤ 2) :
    0 < det3 ((k54L_p5 σ l m ea) - (k54L_p3 σ l m ea)) ((k54L_p2 σ l m ea) - (k54L_p3 σ l m ea)) (k54L_w σ l ea) := by
  have hpos : 0 < (m^2 * 5 * (σ^2 + 1)^3 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^2) / (8*(σ^2 + 1)^6) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54L_p0,k54L_p1,k54L_p2,k54L_p3,k54L_p4,k54L_p5,k54L_p6,k54L_om,k54L_ta,k54L_w,k54L_c1,k54L_c2,k54L_c3,k54L_c4,k54L_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54L_row6 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 * σ^2 ≤ 2) :
    0 < det3 ((k54L_p5 σ l m ea) - (k54L_p3 σ l m ea)) (cross (k54L_om σ l) (k54L_p3 σ l m ea) + (k54L_ta σ l m)) (k54L_w σ l ea) := by
  have hQ0 : 0 < -(2*σ - 1) := k54L_L_det6 σ (l^2) hσ (by positivity) hR1 hR2 hp
  have hQ1 : 0 < 3*σ^2*(l^2) + 12*σ^2 - 2*(l^2) + 12 := k54L_L_det7 σ (l^2) hσ (by positivity) hR1 hR2 hp
  have hpos : 0 < m^2 * (l^2*σ*(l^2*σ^2 + 2*σ^2 + 2)/(8*(σ^2 + 1)^3)) * 80 * (σ^2 + 1)^1 * (-(2*σ - 1)) * (2*σ + 1)^1 * (σ)^1 * (3*σ^2*(l^2) + 12*σ^2 - 2*(l^2) + 12) * (5*σ^2*(l^2) + 12*σ^2 + 12)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^3 := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54L_p0,k54L_p1,k54L_p2,k54L_p3,k54L_p4,k54L_p5,k54L_p6,k54L_om,k54L_ta,k54L_w,k54L_c1,k54L_c2,k54L_c3,k54L_c4,k54L_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54L_row7 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 * σ^2 ≤ 2) :
    0 < det3 ((k54L_p3 σ l m ea) - (k54L_p2 σ l m ea)) (cross (k54L_om σ l) (k54L_p3 σ l m ea) + (k54L_ta σ l m)) (k54L_w σ l ea) := by
  have hQ0 : 0 < 80*σ^11*(l^2)^2 + 320*σ^11*(l^2) + 65*σ^9*(l^2)^2 + 560*σ^9*(l^2) - 6*σ^8*(l^2)^2 - 64*σ^8*(l^2) - 94*σ^7*(l^2)^2 + 8*σ^7*(l^2) + 576*σ^7 - 32*σ^6*(l^2)^2 - 96*σ^6*(l^2) + 384*σ^6 - 53*σ^5*(l^2)^2 - 280*σ^5*(l^2) + 1728*σ^5 + 74*σ^4*(l^2)^2 + 640*σ^4*(l^2) + 2112*σ^4 + 26*σ^3*(l^2)^2 + 56*σ^3*(l^2) + 1728*σ^3 + 672*σ^2*(l^2) + 3072*σ^2 + 104*σ*(l^2) + 576*σ + 1344 := k54L_L_row7_f4 σ (l^2) hσ (by positivity) hR1 hR2 hp
  have hpos : 0 < m^2 * (l^2*σ*(l^2*σ^2 + 4*σ^2 + 4)/(8*(σ^2 + 1)^3)) * 20 * (σ^2 + 1)^1 * (5*σ^2*(l^2) + 12*σ^2 + 12)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^2 * (80*σ^11*(l^2)^2 + 320*σ^11*(l^2) + 65*σ^9*(l^2)^2 + 560*σ^9*(l^2) - 6*σ^8*(l^2)^2 - 64*σ^8*(l^2) - 94*σ^7*(l^2)^2 + 8*σ^7*(l^2) + 576*σ^7 - 32*σ^6*(l^2)^2 - 96*σ^6*(l^2) + 384*σ^6 - 53*σ^5*(l^2)^2 - 280*σ^5*(l^2) + 1728*σ^5 + 74*σ^4*(l^2)^2 + 640*σ^4*(l^2) + 2112*σ^4 + 26*σ^3*(l^2)^2 + 56*σ^3*(l^2) + 1728*σ^3 + 672*σ^2*(l^2) + 3072*σ^2 + 104*σ*(l^2) + 576*σ + 1344) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54L_p0,k54L_p1,k54L_p2,k54L_p3,k54L_p4,k54L_p5,k54L_p6,k54L_om,k54L_ta,k54L_w,k54L_c1,k54L_c2,k54L_c3,k54L_c4,k54L_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54L_conv4 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 * σ^2 ≤ 2) :
    0 < det3 ((k54L_p0 m) - (k54L_p5 σ l m ea)) ((k54L_p3 σ l m ea) - (k54L_p5 σ l m ea)) (k54L_w σ l ea) := by
  have hpos : 0 < (m^2 * 1 * (σ^2 + 1)^1 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^1) / (4*(σ^2 + 1)^3) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54L_p0,k54L_p1,k54L_p2,k54L_p3,k54L_p4,k54L_p5,k54L_p6,k54L_om,k54L_ta,k54L_w,k54L_c1,k54L_c2,k54L_c3,k54L_c4,k54L_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54L_row8 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 * σ^2 ≤ 2) :
    0 < det3 ((k54L_p0 m) - (k54L_p5 σ l m ea)) (cross (k54L_om σ l) (k54L_p5 σ l m ea) + (k54L_ta σ l m)) (k54L_w σ l ea) := by
  have hQ0 : 0 < -160*σ^12*(l^2)^2 - 640*σ^12*(l^2) - 320*σ^10*(l^2)^3 - 3170*σ^10*(l^2)^2 - 10080*σ^10*(l^2) - 7680*σ^10 + 12*σ^9*(l^2)^2 + 128*σ^9*(l^2) - 360*σ^8*(l^2)^3 - 6690*σ^8*(l^2)^2 - 31560*σ^8*(l^2) - 40320*σ^8 + 212*σ^7*(l^2)^2 + 976*σ^7*(l^2) + 385*σ^6*(l^2)^3 - 420*σ^6*(l^2)^2 - 27360*σ^6*(l^2) - 70080*σ^6 + 150*σ^5*(l^2)^3 + 1248*σ^5*(l^2)^2 + 3360*σ^5*(l^2) - 50*σ^4*(l^2)^3 + 2860*σ^4*(l^2)^2 + 2040*σ^4*(l^2) - 45120*σ^4 + 1048*σ^3*(l^2)^2 + 4304*σ^3*(l^2) - 400*σ^2*(l^2)^2 + 6480*σ^2*(l^2) - 2880*σ^2 + 1792*σ*(l^2) - 800*(l^2) + 4800 := k54L_L_row8_f5 σ (l^2) hσ (by positivity) hR1 hR2 hp
  have hpos : 0 < m^2 * (l^2*σ/(4*(σ^2 + 1)^2)) * 4 * (σ^2 + 1)^1 * (σ)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^1 * (5*σ^2*(l^2) + 12*σ^2 + 12)^1 * (-160*σ^12*(l^2)^2 - 640*σ^12*(l^2) - 320*σ^10*(l^2)^3 - 3170*σ^10*(l^2)^2 - 10080*σ^10*(l^2) - 7680*σ^10 + 12*σ^9*(l^2)^2 + 128*σ^9*(l^2) - 360*σ^8*(l^2)^3 - 6690*σ^8*(l^2)^2 - 31560*σ^8*(l^2) - 40320*σ^8 + 212*σ^7*(l^2)^2 + 976*σ^7*(l^2) + 385*σ^6*(l^2)^3 - 420*σ^6*(l^2)^2 - 27360*σ^6*(l^2) - 70080*σ^6 + 150*σ^5*(l^2)^3 + 1248*σ^5*(l^2)^2 + 3360*σ^5*(l^2) - 50*σ^4*(l^2)^3 + 2860*σ^4*(l^2)^2 + 2040*σ^4*(l^2) - 45120*σ^4 + 1048*σ^3*(l^2)^2 + 4304*σ^3*(l^2) - 400*σ^2*(l^2)^2 + 6480*σ^2*(l^2) - 2880*σ^2 + 1792*σ*(l^2) - 800*(l^2) + 4800) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54L_p0,k54L_p1,k54L_p2,k54L_p3,k54L_p4,k54L_p5,k54L_p6,k54L_om,k54L_ta,k54L_w,k54L_c1,k54L_c2,k54L_c3,k54L_c4,k54L_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54L_row9 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 * σ^2 ≤ 2) :
    0 < det3 ((k54L_p5 σ l m ea) - (k54L_p3 σ l m ea)) (cross (k54L_om σ l) (k54L_p5 σ l m ea) + (k54L_ta σ l m)) (k54L_w σ l ea) := by
  have hQ0 : 0 < -(2*σ - 1) := k54L_L_det6 σ (l^2) hσ (by positivity) hR1 hR2 hp
  have hQ1 : 0 < 3*σ^2*(l^2) + 12*σ^2 - 2*(l^2) + 12 := k54L_L_det7 σ (l^2) hσ (by positivity) hR1 hR2 hp
  have hpos : 0 < m^2 * (l^2*σ*(l^2*σ^2 + 2*σ^2 + 2)/(8*(σ^2 + 1)^3)) * 80 * (σ^2 + 1)^1 * (-(2*σ - 1)) * (2*σ + 1)^1 * (σ)^1 * (3*σ^2*(l^2) + 12*σ^2 - 2*(l^2) + 12) * (5*σ^2*(l^2) + 12*σ^2 + 12)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^3 := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54L_p0,k54L_p1,k54L_p2,k54L_p3,k54L_p4,k54L_p5,k54L_p6,k54L_om,k54L_ta,k54L_w,k54L_c1,k54L_c2,k54L_c3,k54L_c4,k54L_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54L_int1tri {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 * σ^2 ≤ 2) :
    0 < det3 ((k54L_p2 σ l m ea) - (k54L_p0 m)) ((k54L_p3 σ l m ea) - (k54L_p0 m)) (k54L_w σ l ea) := by
  have hpos : 0 < (m^2 * 1 * (σ^2 + 1)^3 * (σ)^1 * (l)^2 * (5*σ^2*(l^2) + 16*σ^2 + 16)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^2) / (8*(σ^2 + 1)^6) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54L_p0,k54L_p1,k54L_p2,k54L_p3,k54L_p4,k54L_p5,k54L_p6,k54L_om,k54L_ta,k54L_w,k54L_c1,k54L_c2,k54L_c3,k54L_c4,k54L_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54L_int1e1 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 * σ^2 ≤ 2) :
    0 < det3 ((k54L_p2 σ l m ea) - (k54L_p0 m)) ((k54L_p1 m ea) - (k54L_p0 m)) (k54L_w σ l ea) := by
  have hpos : 0 < (m^2 * 1 * (σ^2 + 1)^1 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 4*σ^2 + 4)^2) / (4*(σ^2 + 1)^3) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54L_p0,k54L_p1,k54L_p2,k54L_p3,k54L_p4,k54L_p5,k54L_p6,k54L_om,k54L_ta,k54L_w,k54L_c1,k54L_c2,k54L_c3,k54L_c4,k54L_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54L_int1e2 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 * σ^2 ≤ 2) :
    0 < det3 ((k54L_p3 σ l m ea) - (k54L_p2 σ l m ea)) ((k54L_p1 m ea) - (k54L_p2 σ l m ea)) (k54L_w σ l ea) := by
  have hpos : 0 < (m^2 * 1 * (σ^2 + 1)^3 * (σ)^1 * (l)^2 * (5*σ^2*(l^2) + 12*σ^2 + 12)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^2) / (8*(σ^2 + 1)^6) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54L_p0,k54L_p1,k54L_p2,k54L_p3,k54L_p4,k54L_p5,k54L_p6,k54L_om,k54L_ta,k54L_w,k54L_c1,k54L_c2,k54L_c3,k54L_c4,k54L_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54L_int1e3 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 * σ^2 ≤ 2) :
    0 < det3 ((k54L_p0 m) - (k54L_p3 σ l m ea)) ((k54L_p1 m ea) - (k54L_p3 σ l m ea)) (k54L_w σ l ea) := by
  have hpos : 0 < (m^2 * 1 * (σ^2 + 1)^1 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 4*σ^2 + 4)^2) / (4*(σ^2 + 1)^3) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54L_p0,k54L_p1,k54L_p2,k54L_p3,k54L_p4,k54L_p5,k54L_p6,k54L_om,k54L_ta,k54L_w,k54L_c1,k54L_c2,k54L_c3,k54L_c4,k54L_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54L_int6tri {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 * σ^2 ≤ 2) :
    0 < det3 ((k54L_p2 σ l m ea) - (k54L_p0 m)) ((k54L_p3 σ l m ea) - (k54L_p0 m)) (k54L_w σ l ea) := by
  have hpos : 0 < (m^2 * 1 * (σ^2 + 1)^3 * (σ)^1 * (l)^2 * (5*σ^2*(l^2) + 16*σ^2 + 16)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^2) / (8*(σ^2 + 1)^6) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54L_p0,k54L_p1,k54L_p2,k54L_p3,k54L_p4,k54L_p5,k54L_p6,k54L_om,k54L_ta,k54L_w,k54L_c1,k54L_c2,k54L_c3,k54L_c4,k54L_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54L_int6e1 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 * σ^2 ≤ 2) :
    0 < det3 ((k54L_p2 σ l m ea) - (k54L_p0 m)) ((k54L_p6 σ l m ea) - (k54L_p0 m)) (k54L_w σ l ea) := by
  have hpos : 0 < (m^2 * 3 * (σ^2 + 1)^3 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 4*σ^2 + 4)^3) / (16*(σ^2 + 1)^6) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54L_p0,k54L_p1,k54L_p2,k54L_p3,k54L_p4,k54L_p5,k54L_p6,k54L_om,k54L_ta,k54L_w,k54L_c1,k54L_c2,k54L_c3,k54L_c4,k54L_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54L_int6e2 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 * σ^2 ≤ 2) :
    0 < det3 ((k54L_p3 σ l m ea) - (k54L_p2 σ l m ea)) ((k54L_p6 σ l m ea) - (k54L_p2 σ l m ea)) (k54L_w σ l ea) := by
  have hpos : 0 < (m^2 * 1 * (σ^2 + 1)^3 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^2) / (4*(σ^2 + 1)^6) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54L_p0,k54L_p1,k54L_p2,k54L_p3,k54L_p4,k54L_p5,k54L_p6,k54L_om,k54L_ta,k54L_w,k54L_c1,k54L_c2,k54L_c3,k54L_c4,k54L_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54L_int6e3 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 9 * σ^2 ≤ 2) :
    0 < det3 ((k54L_p0 m) - (k54L_p3 σ l m ea)) ((k54L_p6 σ l m ea) - (k54L_p3 σ l m ea)) (k54L_w σ l ea) := by
  have hpos : 0 < (m^2 * 3 * (σ^2 + 1)^3 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 4*σ^2 + 4)^3) / (16*(σ^2 + 1)^6) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54L_p0,k54L_p1,k54L_p2,k54L_p3,k54L_p4,k54L_p5,k54L_p6,k54L_om,k54L_ta,k54L_w,k54L_c1,k54L_c2,k54L_c3,k54L_c4,k54L_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

theorem k54L_regions {σ l ea : ℝ} (hσ : 0 < σ) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : ea ≤ σ^2 * (2 + ea)) (hR2 : ea * σ^2 < 2 + ea) :
    l^2*(1-σ^2) ≤ 4*(1+σ^2) ∧ l^2*σ^2*(σ^2-1) < 4*(1+σ^2) := by
  have hD : 0 < 1 + σ^2 := by positivity
  have hea' : 2*(1+σ^2)*ea = l^2*σ^2 := by rw [hea]; field_simp
  have h3 : 2*(1+σ^2)*ea*σ^2 = l^2*σ^2*σ^2 := by rw [hea']
  have hs2 : 0 < σ^2 := by positivity
  constructor
  · by_contra h
    push_neg at h
    have h1 := mul_le_mul_of_nonneg_left hR1 (by positivity : (0:ℝ) ≤ 2*(1+σ^2))
    have h2 := mul_pos hs2 (sub_pos.2 h)
    nlinarith
  · have h1 := mul_lt_mul_of_pos_left hR2 (by positivity : (0:ℝ) < 2*(1+σ^2))
    nlinarith

set_option maxHeartbeats 8000000 in
theorem a2mc_L {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : ea ≤ σ^2 * (2 + ea)) (hR2 : ea * σ^2 < 2 + ea) (hp : 9 * σ^2 ≤ 2) :
    IsRupert (V8 (k54L_p1 m ea) (k54L_p6 σ l m ea) (k54L_p4 σ l m ea) (k54L_p3 σ l m ea) (k54L_p5 σ l m ea) (k54L_p2 σ l m ea) (k54L_p0 m)) := by
  obtain ⟨hr1, hr2⟩ := k54L_regions hσ hea hR1 hR2
  refine isRupert_of_tiltCert _ (k54L_w σ l ea) ?_ (k54L_om σ l) (k54L_ta σ l m) ?_
  · intro h
    have h1 := congrArg (fun v : ℝ³ => v 1) h
    simp only [k54L_w, pt_one] at h1
    simp at h1
    linarith
  · intro x hx
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · left
      exact ⟨(k54L_p5 σ l m ea), by simp [V8], (k54L_p4 σ l m ea), by simp [V8], k54L_conv0 hσ hl hm hea hr1 hr2 hp, k54L_row0 hσ hl hm hea hr1 hr2 hp, k54L_row1 hσ hl hm hea hr1 hr2 hp⟩
    · right
      exact ⟨(k54L_p0 m), by simp [V8], (k54L_p2 σ l m ea), by simp [V8], (k54L_p3 σ l m ea), by simp [V8], k54L_int1tri hσ hl hm hea hr1 hr2 hp, k54L_int1e1 hσ hl hm hea hr1 hr2 hp, k54L_int1e2 hσ hl hm hea hr1 hr2 hp, k54L_int1e3 hσ hl hm hea hr1 hr2 hp⟩
    · right
      exact ⟨(k54L_p0 m), by simp [V8], (k54L_p2 σ l m ea), by simp [V8], (k54L_p3 σ l m ea), by simp [V8], k54L_int6tri hσ hl hm hea hr1 hr2 hp, k54L_int6e1 hσ hl hm hea hr1 hr2 hp, k54L_int6e2 hσ hl hm hea hr1 hr2 hp, k54L_int6e3 hσ hl hm hea hr1 hr2 hp⟩
    · left
      exact ⟨(k54L_p0 m), by simp [V8], (k54L_p2 σ l m ea), by simp [V8], k54L_conv1 hσ hl hm hea hr1 hr2 hp, k54L_row2 hσ hl hm hea hr1 hr2 hp, k54L_row3 hσ hl hm hea hr1 hr2 hp⟩
    · left
      exact ⟨(k54L_p2 σ l m ea), by simp [V8], (k54L_p5 σ l m ea), by simp [V8], k54L_conv3 hσ hl hm hea hr1 hr2 hp, k54L_row6 hσ hl hm hea hr1 hr2 hp, k54L_row7 hσ hl hm hea hr1 hr2 hp⟩
    · left
      exact ⟨(k54L_p3 σ l m ea), by simp [V8], (k54L_p0 m), by simp [V8], k54L_conv4 hσ hl hm hea hr1 hr2 hp, k54L_row8 hσ hl hm hea hr1 hr2 hp, k54L_row9 hσ hl hm hea hr1 hr2 hp⟩
    · left
      exact ⟨(k54L_p4 σ l m ea), by simp [V8], (k54L_p3 σ l m ea), by simp [V8], k54L_conv2 hσ hl hm hea hr1 hr2 hp, k54L_row4 hσ hl hm hea hr1 hr2 hp, k54L_row5 hσ hl hm hea hr1 hr2 hp⟩

end Minimality.Type08Sp.C2
