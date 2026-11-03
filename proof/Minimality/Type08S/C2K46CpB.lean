module

public import Minimality.Type08S.C2K46CpA

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace
open Minimality Minimality.Type08Sp

namespace Minimality.Type08Sp.C2


set_option maxHeartbeats 8000000 in
theorem k54Cp_conv0 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 2 ≤ 3 * σ^2) (hq : σ^2 ≤ 5) :
    0 < det3 ((k54Cp_p4 σ l m ea) - (k54Cp_p0 m)) ((k54Cp_p5 σ l m ea) - (k54Cp_p0 m)) (k54Cp_w σ l ea) := by
  have hpos : 0 < (m^2 * 1 * (σ)^1 * (l)^2 * (17*σ^2*(l^2) + 40*σ^2 + 40)^1) / (2*(σ^2 + 1)) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54Cp_p0,k54Cp_p1,k54Cp_p2,k54Cp_p3,k54Cp_p4,k54Cp_p5,k54Cp_p6,k54Cp_om,k54Cp_ta,k54Cp_w,k54Cp_c1,k54Cp_c2,k54Cp_c3,k54Cp_c4,k54Cp_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54Cp_row0 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 2 ≤ 3 * σ^2) (hq : σ^2 ≤ 5) :
    0 < det3 ((k54Cp_p4 σ l m ea) - (k54Cp_p0 m)) (cross (k54Cp_om σ l) (k54Cp_p0 m) + (k54Cp_ta σ l m)) (k54Cp_w σ l ea) := by
  have hQ0 : 0 < -32*σ^10*(l^2)^3 - 200*σ^10*(l^2)^2 - 288*σ^10*(l^2) - 28*σ^9*(l^2)^3 + 510*σ^9*(l^2)^2 + 2864*σ^9*(l^2) + 3520*σ^9 + 226*σ^8*(l^2)^3 + 1378*σ^8*(l^2)^2 + 3120*σ^8*(l^2) + 2880*σ^8 - 41*σ^7*(l^2)^3 + 557*σ^7*(l^2)^2 + 6680*σ^7*(l^2) + 12000*σ^7 + 283*σ^6*(l^2)^3 + 3821*σ^6*(l^2)^2 + 12928*σ^6*(l^2) + 13600*σ^6 + 87*σ^5*(l^2)^3 + 444*σ^5*(l^2)^2 + 5216*σ^5*(l^2) + 14880*σ^5 - 75*σ^4*(l^2)^3 + 1848*σ^4*(l^2)^2 + 14824*σ^4*(l^2) + 23520*σ^4 + 397*σ^3*(l^2)^2 + 1848*σ^3*(l^2) + 7840*σ^3 - 395*σ^2*(l^2)^2 + 4784*σ^2*(l^2) + 17760*σ^2 + 448*σ*(l^2) + 1440*σ - 520*(l^2) + 4960 := k54Cp_Cp_row0_f0 σ (l^2) hσ (by positivity) hR1 hR2 hp hq
  have hpos : 0 < m^2 * (l^2*σ/(2*(σ^2 + 1))) * 10 * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^1 * (-32*σ^10*(l^2)^3 - 200*σ^10*(l^2)^2 - 288*σ^10*(l^2) - 28*σ^9*(l^2)^3 + 510*σ^9*(l^2)^2 + 2864*σ^9*(l^2) + 3520*σ^9 + 226*σ^8*(l^2)^3 + 1378*σ^8*(l^2)^2 + 3120*σ^8*(l^2) + 2880*σ^8 - 41*σ^7*(l^2)^3 + 557*σ^7*(l^2)^2 + 6680*σ^7*(l^2) + 12000*σ^7 + 283*σ^6*(l^2)^3 + 3821*σ^6*(l^2)^2 + 12928*σ^6*(l^2) + 13600*σ^6 + 87*σ^5*(l^2)^3 + 444*σ^5*(l^2)^2 + 5216*σ^5*(l^2) + 14880*σ^5 - 75*σ^4*(l^2)^3 + 1848*σ^4*(l^2)^2 + 14824*σ^4*(l^2) + 23520*σ^4 + 397*σ^3*(l^2)^2 + 1848*σ^3*(l^2) + 7840*σ^3 - 395*σ^2*(l^2)^2 + 4784*σ^2*(l^2) + 17760*σ^2 + 448*σ*(l^2) + 1440*σ - 520*(l^2) + 4960) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54Cp_p0,k54Cp_p1,k54Cp_p2,k54Cp_p3,k54Cp_p4,k54Cp_p5,k54Cp_p6,k54Cp_om,k54Cp_ta,k54Cp_w,k54Cp_c1,k54Cp_c2,k54Cp_c3,k54Cp_c4,k54Cp_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54Cp_row1 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 2 ≤ 3 * σ^2) (hq : σ^2 ≤ 5) :
    0 < det3 ((k54Cp_p0 m) - (k54Cp_p5 σ l m ea)) (cross (k54Cp_om σ l) (k54Cp_p0 m) + (k54Cp_ta σ l m)) (k54Cp_w σ l ea) := by
  have hQ0 : 0 < 52*σ^10*(l^2)^3 + 332*σ^10*(l^2)^2 + 496*σ^10*(l^2) + 1448*σ^9*(l^2)^3 + 10342*σ^9*(l^2)^2 + 24552*σ^9*(l^2) + 19360*σ^9 + 844*σ^8*(l^2)^3 + 7176*σ^8*(l^2)^2 + 19160*σ^8*(l^2) + 15840*σ^8 + 481*σ^7*(l^2)^3 + 14019*σ^7*(l^2)^2 + 58460*σ^7*(l^2) + 66000*σ^7 + 1697*σ^6*(l^2)^3 + 19709*σ^6*(l^2)^2 + 69304*σ^6*(l^2) + 74800*σ^6 - 67*σ^5*(l^2)^3 + 3352*σ^5*(l^2)^2 + 42868*σ^5*(l^2) + 81840*σ^5 + 5*σ^4*(l^2)^3 + 12878*σ^4*(l^2)^2 + 83112*σ^4*(l^2) + 129360*σ^4 - 325*σ^3*(l^2)^2 + 8564*σ^3*(l^2) + 43120*σ^3 + 13*σ^2*(l^2)^2 + 32472*σ^2*(l^2) + 97680*σ^2 - 396*σ*(l^2) + 7920*σ + 27280 := k54Cp_Cp_row1_f1 σ (l^2) hσ (by positivity) hR1 hR2 hp hq
  have hpos : 0 < m^2 * (l^2*σ/(2*(σ^2 + 1))) * 10 * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^1 * (52*σ^10*(l^2)^3 + 332*σ^10*(l^2)^2 + 496*σ^10*(l^2) + 1448*σ^9*(l^2)^3 + 10342*σ^9*(l^2)^2 + 24552*σ^9*(l^2) + 19360*σ^9 + 844*σ^8*(l^2)^3 + 7176*σ^8*(l^2)^2 + 19160*σ^8*(l^2) + 15840*σ^8 + 481*σ^7*(l^2)^3 + 14019*σ^7*(l^2)^2 + 58460*σ^7*(l^2) + 66000*σ^7 + 1697*σ^6*(l^2)^3 + 19709*σ^6*(l^2)^2 + 69304*σ^6*(l^2) + 74800*σ^6 - 67*σ^5*(l^2)^3 + 3352*σ^5*(l^2)^2 + 42868*σ^5*(l^2) + 81840*σ^5 + 5*σ^4*(l^2)^3 + 12878*σ^4*(l^2)^2 + 83112*σ^4*(l^2) + 129360*σ^4 - 325*σ^3*(l^2)^2 + 8564*σ^3*(l^2) + 43120*σ^3 + 13*σ^2*(l^2)^2 + 32472*σ^2*(l^2) + 97680*σ^2 - 396*σ*(l^2) + 7920*σ + 27280) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54Cp_p0,k54Cp_p1,k54Cp_p2,k54Cp_p3,k54Cp_p4,k54Cp_p5,k54Cp_p6,k54Cp_om,k54Cp_ta,k54Cp_w,k54Cp_c1,k54Cp_c2,k54Cp_c3,k54Cp_c4,k54Cp_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54Cp_conv1 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 2 ≤ 3 * σ^2) (hq : σ^2 ≤ 5) :
    0 < det3 ((k54Cp_p2 σ l m ea) - (k54Cp_p4 σ l m ea)) ((k54Cp_p0 m) - (k54Cp_p4 σ l m ea)) (k54Cp_w σ l ea) := by
  have hpos : 0 < (m^2 * 1 * (σ^2 + 1)^1 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^1) / (2*(σ^2 + 1)^3) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54Cp_p0,k54Cp_p1,k54Cp_p2,k54Cp_p3,k54Cp_p4,k54Cp_p5,k54Cp_p6,k54Cp_om,k54Cp_ta,k54Cp_w,k54Cp_c1,k54Cp_c2,k54Cp_c3,k54Cp_c4,k54Cp_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54Cp_row2 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 2 ≤ 3 * σ^2) (hq : σ^2 ≤ 5) :
    0 < det3 ((k54Cp_p2 σ l m ea) - (k54Cp_p4 σ l m ea)) (cross (k54Cp_om σ l) (k54Cp_p4 σ l m ea) + (k54Cp_ta σ l m)) (k54Cp_w σ l ea) := by
  have hQ0 : 0 < 2*σ^2 - 1 := k54Cp_Cp_det5 σ (l^2) hσ (by positivity) hR1 hR2 hp hq
  have hQ1 : 0 < -σ^4*(l^2) - 4*σ^4 + 9*σ^2*(l^2) + 18*σ^2 + 22 := k54Cp_Cp_det6 σ (l^2) hσ (by positivity) hR1 hR2 hp hq
  have hpos : 0 < m^2 * (l^2*(l^2*σ^2 + 2*σ^2 + 2)/(2*(σ^2 + 1)^3)) * 20 * (2*σ^2 - 1) * (σ^2 + 1)^2 * (σ)^1 * (l)^2 * (-σ^4*(l^2) - 4*σ^4 + 9*σ^2*(l^2) + 18*σ^2 + 22) * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^1 * (5*σ^2*(l^2) + 13*σ^2 + 13)^1 := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54Cp_p0,k54Cp_p1,k54Cp_p2,k54Cp_p3,k54Cp_p4,k54Cp_p5,k54Cp_p6,k54Cp_om,k54Cp_ta,k54Cp_w,k54Cp_c1,k54Cp_c2,k54Cp_c3,k54Cp_c4,k54Cp_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54Cp_row3 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 2 ≤ 3 * σ^2) (hq : σ^2 ≤ 5) :
    0 < det3 ((k54Cp_p4 σ l m ea) - (k54Cp_p0 m)) (cross (k54Cp_om σ l) (k54Cp_p4 σ l m ea) + (k54Cp_ta σ l m)) (k54Cp_w σ l ea) := by
  have hQ0 : 0 < -16*σ^10*(l^2)^3 - 100*σ^10*(l^2)^2 - 144*σ^10*(l^2) + 171*σ^9*(l^2)^3 + 1120*σ^9*(l^2)^2 + 2436*σ^9*(l^2) + 1760*σ^9 + 288*σ^8*(l^2)^3 + 1492*σ^8*(l^2)^2 + 2476*σ^8*(l^2) + 1440*σ^8 + 67*σ^7*(l^2)^3 + 1563*σ^7*(l^2)^2 + 5850*σ^7*(l^2) + 6000*σ^7 + 319*σ^6*(l^2)^3 + 3549*σ^6*(l^2)^2 + 9274*σ^6*(l^2) + 6800*σ^6 - 4*σ^5*(l^2)^3 + 426*σ^5*(l^2)^2 + 4374*σ^5*(l^2) + 7440*σ^5 - 85*σ^4*(l^2)^3 + 1562*σ^4*(l^2)^2 + 10086*σ^4*(l^2) + 11760*σ^4 - 17*σ^3*(l^2)^2 + 942*σ^3*(l^2) + 3920*σ^3 - 395*σ^2*(l^2)^2 + 2974*σ^2*(l^2) + 8880*σ^2 - 18*σ*(l^2) + 720*σ - 458*(l^2) + 2480 := k54Cp_Cp_row3_f2 σ (l^2) hσ (by positivity) hR1 hR2 hp hq
  have hpos : 0 < m^2 * (l^2/(4*(σ^2 + 1)^2)) * 40 * (σ^2 + 1)^1 * (σ)^1 * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^1 * (-16*σ^10*(l^2)^3 - 100*σ^10*(l^2)^2 - 144*σ^10*(l^2) + 171*σ^9*(l^2)^3 + 1120*σ^9*(l^2)^2 + 2436*σ^9*(l^2) + 1760*σ^9 + 288*σ^8*(l^2)^3 + 1492*σ^8*(l^2)^2 + 2476*σ^8*(l^2) + 1440*σ^8 + 67*σ^7*(l^2)^3 + 1563*σ^7*(l^2)^2 + 5850*σ^7*(l^2) + 6000*σ^7 + 319*σ^6*(l^2)^3 + 3549*σ^6*(l^2)^2 + 9274*σ^6*(l^2) + 6800*σ^6 - 4*σ^5*(l^2)^3 + 426*σ^5*(l^2)^2 + 4374*σ^5*(l^2) + 7440*σ^5 - 85*σ^4*(l^2)^3 + 1562*σ^4*(l^2)^2 + 10086*σ^4*(l^2) + 11760*σ^4 - 17*σ^3*(l^2)^2 + 942*σ^3*(l^2) + 3920*σ^3 - 395*σ^2*(l^2)^2 + 2974*σ^2*(l^2) + 8880*σ^2 - 18*σ*(l^2) + 720*σ - 458*(l^2) + 2480) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54Cp_p0,k54Cp_p1,k54Cp_p2,k54Cp_p3,k54Cp_p4,k54Cp_p5,k54Cp_p6,k54Cp_om,k54Cp_ta,k54Cp_w,k54Cp_c1,k54Cp_c2,k54Cp_c3,k54Cp_c4,k54Cp_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54Cp_conv2 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 2 ≤ 3 * σ^2) (hq : σ^2 ≤ 5) :
    0 < det3 ((k54Cp_p3 σ l m ea) - (k54Cp_p2 σ l m ea)) ((k54Cp_p4 σ l m ea) - (k54Cp_p2 σ l m ea)) (k54Cp_w σ l ea) := by
  have hpos : 0 < (m^2 * 1 * (σ^2 + 1)^3 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^1 * (5*σ^2*(l^2) + 13*σ^2 + 13)^1) / (2*(σ^2 + 1)^6) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54Cp_p0,k54Cp_p1,k54Cp_p2,k54Cp_p3,k54Cp_p4,k54Cp_p5,k54Cp_p6,k54Cp_om,k54Cp_ta,k54Cp_w,k54Cp_c1,k54Cp_c2,k54Cp_c3,k54Cp_c4,k54Cp_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54Cp_row4 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 2 ≤ 3 * σ^2) (hq : σ^2 ≤ 5) :
    0 < det3 ((k54Cp_p3 σ l m ea) - (k54Cp_p2 σ l m ea)) (cross (k54Cp_om σ l) (k54Cp_p2 σ l m ea) + (k54Cp_ta σ l m)) (k54Cp_w σ l ea) := by
  have hQ0 : 0 < 2*σ^2 - 1 := k54Cp_Cp_det5 σ (l^2) hσ (by positivity) hR1 hR2 hp hq
  have hQ1 : 0 < -σ^4*(l^2) - 4*σ^4 + 9*σ^2*(l^2) + 18*σ^2 + 22 := k54Cp_Cp_det6 σ (l^2) hσ (by positivity) hR1 hR2 hp hq
  have hpos : 0 < m^2 * (l^2*(l^2*σ^2 + 4*σ^2 + 4)/(4*(σ^2 + 1)^3)) * 20 * (2*σ^2 - 1) * (σ^2 + 1)^2 * (σ)^1 * (l)^2 * (-σ^4*(l^2) - 4*σ^4 + 9*σ^2*(l^2) + 18*σ^2 + 22) * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^1 * (5*σ^2*(l^2) + 13*σ^2 + 13)^1 := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54Cp_p0,k54Cp_p1,k54Cp_p2,k54Cp_p3,k54Cp_p4,k54Cp_p5,k54Cp_p6,k54Cp_om,k54Cp_ta,k54Cp_w,k54Cp_c1,k54Cp_c2,k54Cp_c3,k54Cp_c4,k54Cp_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54Cp_row5 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 2 ≤ 3 * σ^2) (hq : σ^2 ≤ 5) :
    0 < det3 ((k54Cp_p2 σ l m ea) - (k54Cp_p4 σ l m ea)) (cross (k54Cp_om σ l) (k54Cp_p2 σ l m ea) + (k54Cp_ta σ l m)) (k54Cp_w σ l ea) := by
  have hQ0 : 0 < 2*σ^2 - 1 := k54Cp_Cp_det5 σ (l^2) hσ (by positivity) hR1 hR2 hp hq
  have hQ1 : 0 < -σ^4*(l^2) - 4*σ^4 + 9*σ^2*(l^2) + 18*σ^2 + 22 := k54Cp_Cp_det6 σ (l^2) hσ (by positivity) hR1 hR2 hp hq
  have hpos : 0 < m^2 * (l^2*(l^2*σ^2 + 2*σ^2 + 2)/(2*(σ^2 + 1)^3)) * 20 * (2*σ^2 - 1) * (σ^2 + 1)^2 * (σ)^1 * (l)^2 * (-σ^4*(l^2) - 4*σ^4 + 9*σ^2*(l^2) + 18*σ^2 + 22) * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^1 * (5*σ^2*(l^2) + 13*σ^2 + 13)^1 := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54Cp_p0,k54Cp_p1,k54Cp_p2,k54Cp_p3,k54Cp_p4,k54Cp_p5,k54Cp_p6,k54Cp_om,k54Cp_ta,k54Cp_w,k54Cp_c1,k54Cp_c2,k54Cp_c3,k54Cp_c4,k54Cp_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54Cp_conv3 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 2 ≤ 3 * σ^2) (hq : σ^2 ≤ 5) :
    0 < det3 ((k54Cp_p5 σ l m ea) - (k54Cp_p3 σ l m ea)) ((k54Cp_p2 σ l m ea) - (k54Cp_p3 σ l m ea)) (k54Cp_w σ l ea) := by
  have hpos : 0 < (m^2 * 1 * (σ^2 + 1)^3 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^1 * (5*σ^2*(l^2) + 13*σ^2 + 13)^1) / (2*(σ^2 + 1)^6) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54Cp_p0,k54Cp_p1,k54Cp_p2,k54Cp_p3,k54Cp_p4,k54Cp_p5,k54Cp_p6,k54Cp_om,k54Cp_ta,k54Cp_w,k54Cp_c1,k54Cp_c2,k54Cp_c3,k54Cp_c4,k54Cp_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54Cp_row6 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 2 ≤ 3 * σ^2) (hq : σ^2 ≤ 5) :
    0 < det3 ((k54Cp_p5 σ l m ea) - (k54Cp_p3 σ l m ea)) (cross (k54Cp_om σ l) (k54Cp_p3 σ l m ea) + (k54Cp_ta σ l m)) (k54Cp_w σ l ea) := by
  have hQ0 : 0 < 2*σ^2 - 1 := k54Cp_Cp_det5 σ (l^2) hσ (by positivity) hR1 hR2 hp hq
  have hQ1 : 0 < -σ^4*(l^2) - 4*σ^4 + 9*σ^2*(l^2) + 18*σ^2 + 22 := k54Cp_Cp_det6 σ (l^2) hσ (by positivity) hR1 hR2 hp hq
  have hpos : 0 < m^2 * (l^2*σ*(l^2*σ^2 + 2*σ^2 + 2)/(4*(σ^2 + 1)^3)) * 20 * (2*σ^2 - 1) * (σ^2 + 1)^2 * (σ)^1 * (l)^2 * (-σ^4*(l^2) - 4*σ^4 + 9*σ^2*(l^2) + 18*σ^2 + 22) * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^1 * (5*σ^2*(l^2) + 13*σ^2 + 13)^1 := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54Cp_p0,k54Cp_p1,k54Cp_p2,k54Cp_p3,k54Cp_p4,k54Cp_p5,k54Cp_p6,k54Cp_om,k54Cp_ta,k54Cp_w,k54Cp_c1,k54Cp_c2,k54Cp_c3,k54Cp_c4,k54Cp_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54Cp_row7 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 2 ≤ 3 * σ^2) (hq : σ^2 ≤ 5) :
    0 < det3 ((k54Cp_p3 σ l m ea) - (k54Cp_p2 σ l m ea)) (cross (k54Cp_om σ l) (k54Cp_p3 σ l m ea) + (k54Cp_ta σ l m)) (k54Cp_w σ l ea) := by
  have hQ0 : 0 < 2*σ^2 - 1 := k54Cp_Cp_det5 σ (l^2) hσ (by positivity) hR1 hR2 hp hq
  have hQ1 : 0 < -σ^4*(l^2) - 4*σ^4 + 9*σ^2*(l^2) + 18*σ^2 + 22 := k54Cp_Cp_det6 σ (l^2) hσ (by positivity) hR1 hR2 hp hq
  have hpos : 0 < m^2 * (l^2*σ*(l^2*σ^2 + 4*σ^2 + 4)/(4*(σ^2 + 1)^3)) * 20 * (2*σ^2 - 1) * (σ^2 + 1)^2 * (σ)^1 * (l)^2 * (-σ^4*(l^2) - 4*σ^4 + 9*σ^2*(l^2) + 18*σ^2 + 22) * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^1 * (5*σ^2*(l^2) + 13*σ^2 + 13)^1 := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54Cp_p0,k54Cp_p1,k54Cp_p2,k54Cp_p3,k54Cp_p4,k54Cp_p5,k54Cp_p6,k54Cp_om,k54Cp_ta,k54Cp_w,k54Cp_c1,k54Cp_c2,k54Cp_c3,k54Cp_c4,k54Cp_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54Cp_conv4 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 2 ≤ 3 * σ^2) (hq : σ^2 ≤ 5) :
    0 < det3 ((k54Cp_p0 m) - (k54Cp_p5 σ l m ea)) ((k54Cp_p3 σ l m ea) - (k54Cp_p5 σ l m ea)) (k54Cp_w σ l ea) := by
  have hpos : 0 < (m^2 * 1 * (σ^2 + 1)^1 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^1) / (4*(σ^2 + 1)^3) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54Cp_p0,k54Cp_p1,k54Cp_p2,k54Cp_p3,k54Cp_p4,k54Cp_p5,k54Cp_p6,k54Cp_om,k54Cp_ta,k54Cp_w,k54Cp_c1,k54Cp_c2,k54Cp_c3,k54Cp_c4,k54Cp_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54Cp_row8 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 2 ≤ 3 * σ^2) (hq : σ^2 ≤ 5) :
    0 < det3 ((k54Cp_p0 m) - (k54Cp_p5 σ l m ea)) (cross (k54Cp_om σ l) (k54Cp_p5 σ l m ea) + (k54Cp_ta σ l m)) (k54Cp_w σ l ea) := by
  have hQ0 : 0 < -16*σ^13*(l^2)^3 - 100*σ^13*(l^2)^2 - 144*σ^13*(l^2) + 26*σ^12*(l^2)^4 + 218*σ^12*(l^2)^3 + 580*σ^12*(l^2)^2 + 496*σ^12*(l^2) + 1539*σ^11*(l^2)^4 + 13962*σ^11*(l^2)^3 + 46990*σ^11*(l^2)^2 + 69720*σ^11*(l^2) + 38720*σ^11 + 1147*σ^10*(l^2)^4 + 10767*σ^10*(l^2)^3 + 37474*σ^10*(l^2)^2 + 56936*σ^10*(l^2) + 31680*σ^10 + 603*σ^9*(l^2)^4 + 19519*σ^9*(l^2)^3 + 113216*σ^9*(l^2)^2 + 238488*σ^9*(l^2) + 170720*σ^9 + 2021*σ^8*(l^2)^4 + 29020*σ^8*(l^2)^3 + 136422*σ^8*(l^2)^2 + 263824*σ^8*(l^2) + 181280*σ^8 - 36*σ^7*(l^2)^4 + 5228*σ^7*(l^2)^3 + 84188*σ^7*(l^2)^2 + 294912*σ^7*(l^2) + 295680*σ^7 + 18471*σ^6*(l^2)^3 + 162742*σ^6*(l^2)^2 + 454816*σ^6*(l^2) + 408320*σ^6 - 313*σ^5*(l^2)^3 + 17188*σ^5*(l^2)^2 + 153168*σ^5*(l^2) + 249920*σ^5 + 63214*σ^4*(l^2)^2 + 343424*σ^4*(l^2) + 454080*σ^4 - 874*σ^3*(l^2)^2 + 26088*σ^3*(l^2) + 102080*σ^3 + 95992*σ^2*(l^2) + 249920*σ^2 - 792*σ*(l^2) + 15840*σ + 54560 := k54Cp_Cp_row8_f3 σ (l^2) hσ (by positivity) hR1 hR2 hp hq
  have hpos : 0 < m^2 * (l^2*σ/(4*(σ^2 + 1)^2)) * 40 * (σ^2 + 1)^1 * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (-16*σ^13*(l^2)^3 - 100*σ^13*(l^2)^2 - 144*σ^13*(l^2) + 26*σ^12*(l^2)^4 + 218*σ^12*(l^2)^3 + 580*σ^12*(l^2)^2 + 496*σ^12*(l^2) + 1539*σ^11*(l^2)^4 + 13962*σ^11*(l^2)^3 + 46990*σ^11*(l^2)^2 + 69720*σ^11*(l^2) + 38720*σ^11 + 1147*σ^10*(l^2)^4 + 10767*σ^10*(l^2)^3 + 37474*σ^10*(l^2)^2 + 56936*σ^10*(l^2) + 31680*σ^10 + 603*σ^9*(l^2)^4 + 19519*σ^9*(l^2)^3 + 113216*σ^9*(l^2)^2 + 238488*σ^9*(l^2) + 170720*σ^9 + 2021*σ^8*(l^2)^4 + 29020*σ^8*(l^2)^3 + 136422*σ^8*(l^2)^2 + 263824*σ^8*(l^2) + 181280*σ^8 - 36*σ^7*(l^2)^4 + 5228*σ^7*(l^2)^3 + 84188*σ^7*(l^2)^2 + 294912*σ^7*(l^2) + 295680*σ^7 + 18471*σ^6*(l^2)^3 + 162742*σ^6*(l^2)^2 + 454816*σ^6*(l^2) + 408320*σ^6 - 313*σ^5*(l^2)^3 + 17188*σ^5*(l^2)^2 + 153168*σ^5*(l^2) + 249920*σ^5 + 63214*σ^4*(l^2)^2 + 343424*σ^4*(l^2) + 454080*σ^4 - 874*σ^3*(l^2)^2 + 26088*σ^3*(l^2) + 102080*σ^3 + 95992*σ^2*(l^2) + 249920*σ^2 - 792*σ*(l^2) + 15840*σ + 54560) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54Cp_p0,k54Cp_p1,k54Cp_p2,k54Cp_p3,k54Cp_p4,k54Cp_p5,k54Cp_p6,k54Cp_om,k54Cp_ta,k54Cp_w,k54Cp_c1,k54Cp_c2,k54Cp_c3,k54Cp_c4,k54Cp_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54Cp_row9 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 2 ≤ 3 * σ^2) (hq : σ^2 ≤ 5) :
    0 < det3 ((k54Cp_p5 σ l m ea) - (k54Cp_p3 σ l m ea)) (cross (k54Cp_om σ l) (k54Cp_p5 σ l m ea) + (k54Cp_ta σ l m)) (k54Cp_w σ l ea) := by
  have hQ0 : 0 < -4*σ^11*(l^2)^2 - 16*σ^11*(l^2) + 6*σ^10*(l^2)^3 + 36*σ^10*(l^2)^2 + 48*σ^10*(l^2) + 342*σ^9*(l^2)^3 + 2270*σ^9*(l^2)^2 + 4920*σ^9*(l^2) + 3520*σ^9 + 253*σ^8*(l^2)^3 + 1746*σ^8*(l^2)^2 + 3944*σ^8*(l^2) + 2880*σ^8 + 134*σ^7*(l^2)^3 + 3180*σ^7*(l^2)^2 + 11896*σ^7*(l^2) + 12000*σ^7 + 448*σ^6*(l^2)^3 + 4710*σ^6*(l^2)^2 + 14432*σ^6*(l^2) + 13600*σ^6 - 8*σ^5*(l^2)^3 + 854*σ^5*(l^2)^2 + 8888*σ^5*(l^2) + 14880*σ^5 + σ^4*(l^2)^3 + 3006*σ^4*(l^2)^2 + 17232*σ^4*(l^2) + 23520*σ^4 - 52*σ^3*(l^2)^2 + 1848*σ^3*(l^2) + 7840*σ^3 + 6*σ^2*(l^2)^2 + 6704*σ^2*(l^2) + 17760*σ^2 - 80*σ*(l^2) + 1440*σ + 8*(l^2) + 4960 := k54Cp_Cp_row9_f4 σ (l^2) hσ (by positivity) hR1 hR2 hp hq
  have hpos : 0 < m^2 * (l^2*σ*(l^2*σ^2 + 2*σ^2 + 2)/(2*(σ^2 + 1)^3)) * 10 * (σ^2 + 1)^1 * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (5*σ^2*(l^2) + 13*σ^2 + 13)^1 * (-4*σ^11*(l^2)^2 - 16*σ^11*(l^2) + 6*σ^10*(l^2)^3 + 36*σ^10*(l^2)^2 + 48*σ^10*(l^2) + 342*σ^9*(l^2)^3 + 2270*σ^9*(l^2)^2 + 4920*σ^9*(l^2) + 3520*σ^9 + 253*σ^8*(l^2)^3 + 1746*σ^8*(l^2)^2 + 3944*σ^8*(l^2) + 2880*σ^8 + 134*σ^7*(l^2)^3 + 3180*σ^7*(l^2)^2 + 11896*σ^7*(l^2) + 12000*σ^7 + 448*σ^6*(l^2)^3 + 4710*σ^6*(l^2)^2 + 14432*σ^6*(l^2) + 13600*σ^6 - 8*σ^5*(l^2)^3 + 854*σ^5*(l^2)^2 + 8888*σ^5*(l^2) + 14880*σ^5 + σ^4*(l^2)^3 + 3006*σ^4*(l^2)^2 + 17232*σ^4*(l^2) + 23520*σ^4 - 52*σ^3*(l^2)^2 + 1848*σ^3*(l^2) + 7840*σ^3 + 6*σ^2*(l^2)^2 + 6704*σ^2*(l^2) + 17760*σ^2 - 80*σ*(l^2) + 1440*σ + 8*(l^2) + 4960) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54Cp_p0,k54Cp_p1,k54Cp_p2,k54Cp_p3,k54Cp_p4,k54Cp_p5,k54Cp_p6,k54Cp_om,k54Cp_ta,k54Cp_w,k54Cp_c1,k54Cp_c2,k54Cp_c3,k54Cp_c4,k54Cp_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54Cp_int1tri {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 2 ≤ 3 * σ^2) (hq : σ^2 ≤ 5) :
    0 < det3 ((k54Cp_p2 σ l m ea) - (k54Cp_p0 m)) ((k54Cp_p3 σ l m ea) - (k54Cp_p0 m)) (k54Cp_w σ l ea) := by
  have hpos : 0 < (m^2 * 1 * (σ^2 + 1)^3 * (σ)^1 * (l)^2 * (10*σ^2*(l^2) + 23*σ^2 + 23)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^2) / (4*(σ^2 + 1)^6) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54Cp_p0,k54Cp_p1,k54Cp_p2,k54Cp_p3,k54Cp_p4,k54Cp_p5,k54Cp_p6,k54Cp_om,k54Cp_ta,k54Cp_w,k54Cp_c1,k54Cp_c2,k54Cp_c3,k54Cp_c4,k54Cp_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54Cp_int1e1 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 2 ≤ 3 * σ^2) (hq : σ^2 ≤ 5) :
    0 < det3 ((k54Cp_p2 σ l m ea) - (k54Cp_p0 m)) ((k54Cp_p1 m ea) - (k54Cp_p0 m)) (k54Cp_w σ l ea) := by
  have hpos : 0 < (m^2 * 1 * (σ^2 + 1)^1 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 4*σ^2 + 4)^2) / (2*(σ^2 + 1)^3) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54Cp_p0,k54Cp_p1,k54Cp_p2,k54Cp_p3,k54Cp_p4,k54Cp_p5,k54Cp_p6,k54Cp_om,k54Cp_ta,k54Cp_w,k54Cp_c1,k54Cp_c2,k54Cp_c3,k54Cp_c4,k54Cp_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54Cp_int1e2 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 2 ≤ 3 * σ^2) (hq : σ^2 ≤ 5) :
    0 < det3 ((k54Cp_p3 σ l m ea) - (k54Cp_p2 σ l m ea)) ((k54Cp_p1 m ea) - (k54Cp_p2 σ l m ea)) (k54Cp_w σ l ea) := by
  have hpos : 0 < (m^2 * 5 * (σ^2 + 1)^3 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^2) / (2*(σ^2 + 1)^6) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54Cp_p0,k54Cp_p1,k54Cp_p2,k54Cp_p3,k54Cp_p4,k54Cp_p5,k54Cp_p6,k54Cp_om,k54Cp_ta,k54Cp_w,k54Cp_c1,k54Cp_c2,k54Cp_c3,k54Cp_c4,k54Cp_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54Cp_int1e3 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 2 ≤ 3 * σ^2) (hq : σ^2 ≤ 5) :
    0 < det3 ((k54Cp_p0 m) - (k54Cp_p3 σ l m ea)) ((k54Cp_p1 m ea) - (k54Cp_p3 σ l m ea)) (k54Cp_w σ l ea) := by
  have hpos : 0 < (m^2 * 1 * (σ^2 + 1)^1 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 4*σ^2 + 4)^2) / (4*(σ^2 + 1)^3) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54Cp_p0,k54Cp_p1,k54Cp_p2,k54Cp_p3,k54Cp_p4,k54Cp_p5,k54Cp_p6,k54Cp_om,k54Cp_ta,k54Cp_w,k54Cp_c1,k54Cp_c2,k54Cp_c3,k54Cp_c4,k54Cp_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54Cp_int6tri {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 2 ≤ 3 * σ^2) (hq : σ^2 ≤ 5) :
    0 < det3 ((k54Cp_p2 σ l m ea) - (k54Cp_p0 m)) ((k54Cp_p3 σ l m ea) - (k54Cp_p0 m)) (k54Cp_w σ l ea) := by
  have hpos : 0 < (m^2 * 1 * (σ^2 + 1)^3 * (σ)^1 * (l)^2 * (10*σ^2*(l^2) + 23*σ^2 + 23)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^2) / (4*(σ^2 + 1)^6) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54Cp_p0,k54Cp_p1,k54Cp_p2,k54Cp_p3,k54Cp_p4,k54Cp_p5,k54Cp_p6,k54Cp_om,k54Cp_ta,k54Cp_w,k54Cp_c1,k54Cp_c2,k54Cp_c3,k54Cp_c4,k54Cp_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54Cp_int6e1 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 2 ≤ 3 * σ^2) (hq : σ^2 ≤ 5) :
    0 < det3 ((k54Cp_p2 σ l m ea) - (k54Cp_p0 m)) ((k54Cp_p6 σ l m ea) - (k54Cp_p0 m)) (k54Cp_w σ l ea) := by
  have hpos : 0 < (m^2 * 1 * (σ^2 + 1)^3 * (σ)^1 * (l)^2 * (8*σ^2*(l^2) + 19*σ^2 + 19)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^2) / (8*(σ^2 + 1)^6) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54Cp_p0,k54Cp_p1,k54Cp_p2,k54Cp_p3,k54Cp_p4,k54Cp_p5,k54Cp_p6,k54Cp_om,k54Cp_ta,k54Cp_w,k54Cp_c1,k54Cp_c2,k54Cp_c3,k54Cp_c4,k54Cp_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54Cp_int6e2 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 2 ≤ 3 * σ^2) (hq : σ^2 ≤ 5) :
    0 < det3 ((k54Cp_p3 σ l m ea) - (k54Cp_p2 σ l m ea)) ((k54Cp_p6 σ l m ea) - (k54Cp_p2 σ l m ea)) (k54Cp_w σ l ea) := by
  have hpos : 0 < (m^2 * 3 * (σ^2 + 1)^3 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^2) / (8*(σ^2 + 1)^6) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54Cp_p0,k54Cp_p1,k54Cp_p2,k54Cp_p3,k54Cp_p4,k54Cp_p5,k54Cp_p6,k54Cp_om,k54Cp_ta,k54Cp_w,k54Cp_c1,k54Cp_c2,k54Cp_c3,k54Cp_c4,k54Cp_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54Cp_int6e3 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 2 ≤ 3 * σ^2) (hq : σ^2 ≤ 5) :
    0 < det3 ((k54Cp_p0 m) - (k54Cp_p3 σ l m ea)) ((k54Cp_p6 σ l m ea) - (k54Cp_p3 σ l m ea)) (k54Cp_w σ l ea) := by
  have hpos : 0 < (m^2 * 3 * (σ^2 + 1)^3 * (σ)^1 * (l)^2 * (3*σ^2*(l^2) + 7*σ^2 + 7)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^2) / (8*(σ^2 + 1)^6) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54Cp_p0,k54Cp_p1,k54Cp_p2,k54Cp_p3,k54Cp_p4,k54Cp_p5,k54Cp_p6,k54Cp_om,k54Cp_ta,k54Cp_w,k54Cp_c1,k54Cp_c2,k54Cp_c3,k54Cp_c4,k54Cp_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

theorem k54Cp_regions {σ l ea : ℝ} (hσ : 0 < σ) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : ea ≤ σ^2 * (2 + ea)) (hR2 : ea * σ^2 < 2 + ea) :
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
theorem a2mc_Cp {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : ea ≤ σ^2 * (2 + ea)) (hR2 : ea * σ^2 < 2 + ea) (hp : 2 ≤ 3 * σ^2) (hq : σ^2 ≤ 5) :
    IsRupert (V8 (k54Cp_p1 m ea) (k54Cp_p6 σ l m ea) (k54Cp_p4 σ l m ea) (k54Cp_p3 σ l m ea) (k54Cp_p5 σ l m ea) (k54Cp_p2 σ l m ea) (k54Cp_p0 m)) := by
  obtain ⟨hr1, hr2⟩ := k54Cp_regions hσ hea hR1 hR2
  refine isRupert_of_tiltCert _ (k54Cp_w σ l ea) ?_ (k54Cp_om σ l) (k54Cp_ta σ l m) ?_
  · intro h
    have h1 := congrArg (fun v : ℝ³ => v 1) h
    simp only [k54Cp_w, pt_one] at h1
    simp at h1
    linarith
  · intro x hx
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · left
      exact ⟨(k54Cp_p5 σ l m ea), by simp [V8], (k54Cp_p4 σ l m ea), by simp [V8], k54Cp_conv0 hσ hl hm hea hr1 hr2 hp hq, k54Cp_row0 hσ hl hm hea hr1 hr2 hp hq, k54Cp_row1 hσ hl hm hea hr1 hr2 hp hq⟩
    · right
      exact ⟨(k54Cp_p0 m), by simp [V8], (k54Cp_p2 σ l m ea), by simp [V8], (k54Cp_p3 σ l m ea), by simp [V8], k54Cp_int1tri hσ hl hm hea hr1 hr2 hp hq, k54Cp_int1e1 hσ hl hm hea hr1 hr2 hp hq, k54Cp_int1e2 hσ hl hm hea hr1 hr2 hp hq, k54Cp_int1e3 hσ hl hm hea hr1 hr2 hp hq⟩
    · right
      exact ⟨(k54Cp_p0 m), by simp [V8], (k54Cp_p2 σ l m ea), by simp [V8], (k54Cp_p3 σ l m ea), by simp [V8], k54Cp_int6tri hσ hl hm hea hr1 hr2 hp hq, k54Cp_int6e1 hσ hl hm hea hr1 hr2 hp hq, k54Cp_int6e2 hσ hl hm hea hr1 hr2 hp hq, k54Cp_int6e3 hσ hl hm hea hr1 hr2 hp hq⟩
    · left
      exact ⟨(k54Cp_p0 m), by simp [V8], (k54Cp_p2 σ l m ea), by simp [V8], k54Cp_conv1 hσ hl hm hea hr1 hr2 hp hq, k54Cp_row2 hσ hl hm hea hr1 hr2 hp hq, k54Cp_row3 hσ hl hm hea hr1 hr2 hp hq⟩
    · left
      exact ⟨(k54Cp_p2 σ l m ea), by simp [V8], (k54Cp_p5 σ l m ea), by simp [V8], k54Cp_conv3 hσ hl hm hea hr1 hr2 hp hq, k54Cp_row6 hσ hl hm hea hr1 hr2 hp hq, k54Cp_row7 hσ hl hm hea hr1 hr2 hp hq⟩
    · left
      exact ⟨(k54Cp_p3 σ l m ea), by simp [V8], (k54Cp_p0 m), by simp [V8], k54Cp_conv4 hσ hl hm hea hr1 hr2 hp hq, k54Cp_row8 hσ hl hm hea hr1 hr2 hp hq, k54Cp_row9 hσ hl hm hea hr1 hr2 hp hq⟩
    · left
      exact ⟨(k54Cp_p4 σ l m ea), by simp [V8], (k54Cp_p3 σ l m ea), by simp [V8], k54Cp_conv2 hσ hl hm hea hr1 hr2 hp hq, k54Cp_row4 hσ hl hm hea hr1 hr2 hp hq, k54Cp_row5 hσ hl hm hea hr1 hr2 hp hq⟩

end Minimality.Type08Sp.C2
