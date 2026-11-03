module

public import Minimality.Type08S.C2K46CA

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace
open Minimality Minimality.Type08Sp

namespace Minimality.Type08Sp.C2


set_option maxHeartbeats 8000000 in
theorem k54C_conv0 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 1 ≤ 5 * σ^2) (hq : 2 * σ^2 ≤ 3) :
    0 < det3 ((k54C_p4 σ l m ea) - (k54C_p0 m)) ((k54C_p5 σ l m ea) - (k54C_p0 m)) (k54C_w σ l ea) := by
  have hpos : 0 < (m^2 * 1 * (σ)^1 * (l)^2 * (17*σ^2*(l^2) + 40*σ^2 + 40)^1) / (4*(σ^2 + 1)) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54C_p0,k54C_p1,k54C_p2,k54C_p3,k54C_p4,k54C_p5,k54C_p6,k54C_om,k54C_ta,k54C_w,k54C_c1,k54C_c2,k54C_c3,k54C_c4,k54C_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54C_row0 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 1 ≤ 5 * σ^2) (hq : 2 * σ^2 ≤ 3) :
    0 < det3 ((k54C_p4 σ l m ea) - (k54C_p0 m)) (cross (k54C_om σ l) (k54C_p0 m) + (k54C_ta σ l m)) (k54C_w σ l ea) := by
  have hQ0 : 0 < 5*σ^11*(l^2)^3 + 13*σ^11*(l^2)^2 - 67*σ^10*(l^2)^3 - 325*σ^10*(l^2)^2 - 396*σ^10*(l^2) + 1697*σ^9*(l^2)^3 + 12878*σ^9*(l^2)^2 + 32472*σ^9*(l^2) + 27280*σ^9 + 481*σ^8*(l^2)^3 + 3352*σ^8*(l^2)^2 + 8564*σ^8*(l^2) + 7920*σ^8 + 844*σ^7*(l^2)^3 + 19709*σ^7*(l^2)^2 + 83112*σ^7*(l^2) + 97680*σ^7 + 1448*σ^6*(l^2)^3 + 14019*σ^6*(l^2)^2 + 42868*σ^6*(l^2) + 43120*σ^6 + 52*σ^5*(l^2)^3 + 7176*σ^5*(l^2)^2 + 69304*σ^5*(l^2) + 129360*σ^5 + 10342*σ^4*(l^2)^2 + 58460*σ^4*(l^2) + 81840*σ^4 + 332*σ^3*(l^2)^2 + 19160*σ^3*(l^2) + 74800*σ^3 + 24552*σ^2*(l^2) + 66000*σ^2 + 496*σ*(l^2) + 15840*σ + 19360 := k54C_C_row0_f0 σ (l^2) hσ (by positivity) hR1 hR2 hp hq
  have hpos : 0 < m^2 * (l^2*σ/(4*(σ^2 + 1))) * 10 * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^1 * (5*σ^11*(l^2)^3 + 13*σ^11*(l^2)^2 - 67*σ^10*(l^2)^3 - 325*σ^10*(l^2)^2 - 396*σ^10*(l^2) + 1697*σ^9*(l^2)^3 + 12878*σ^9*(l^2)^2 + 32472*σ^9*(l^2) + 27280*σ^9 + 481*σ^8*(l^2)^3 + 3352*σ^8*(l^2)^2 + 8564*σ^8*(l^2) + 7920*σ^8 + 844*σ^7*(l^2)^3 + 19709*σ^7*(l^2)^2 + 83112*σ^7*(l^2) + 97680*σ^7 + 1448*σ^6*(l^2)^3 + 14019*σ^6*(l^2)^2 + 42868*σ^6*(l^2) + 43120*σ^6 + 52*σ^5*(l^2)^3 + 7176*σ^5*(l^2)^2 + 69304*σ^5*(l^2) + 129360*σ^5 + 10342*σ^4*(l^2)^2 + 58460*σ^4*(l^2) + 81840*σ^4 + 332*σ^3*(l^2)^2 + 19160*σ^3*(l^2) + 74800*σ^3 + 24552*σ^2*(l^2) + 66000*σ^2 + 496*σ*(l^2) + 15840*σ + 19360) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54C_p0,k54C_p1,k54C_p2,k54C_p3,k54C_p4,k54C_p5,k54C_p6,k54C_om,k54C_ta,k54C_w,k54C_c1,k54C_c2,k54C_c3,k54C_c4,k54C_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54C_row1 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 1 ≤ 5 * σ^2) (hq : 2 * σ^2 ≤ 3) :
    0 < det3 ((k54C_p0 m) - (k54C_p5 σ l m ea)) (cross (k54C_om σ l) (k54C_p0 m) + (k54C_ta σ l m)) (k54C_w σ l ea) := by
  have hQ0 : 0 < -75*σ^11*(l^2)^3 - 395*σ^11*(l^2)^2 - 520*σ^11*(l^2) + 87*σ^10*(l^2)^3 + 397*σ^10*(l^2)^2 + 448*σ^10*(l^2) + 283*σ^9*(l^2)^3 + 1848*σ^9*(l^2)^2 + 4784*σ^9*(l^2) + 4960*σ^9 - 41*σ^8*(l^2)^3 + 444*σ^8*(l^2)^2 + 1848*σ^8*(l^2) + 1440*σ^8 + 226*σ^7*(l^2)^3 + 3821*σ^7*(l^2)^2 + 14824*σ^7*(l^2) + 17760*σ^7 - 28*σ^6*(l^2)^3 + 557*σ^6*(l^2)^2 + 5216*σ^6*(l^2) + 7840*σ^6 - 32*σ^5*(l^2)^3 + 1378*σ^5*(l^2)^2 + 12928*σ^5*(l^2) + 23520*σ^5 + 510*σ^4*(l^2)^2 + 6680*σ^4*(l^2) + 14880*σ^4 - 200*σ^3*(l^2)^2 + 3120*σ^3*(l^2) + 13600*σ^3 + 2864*σ^2*(l^2) + 12000*σ^2 - 288*σ*(l^2) + 2880*σ + 3520 := k54C_C_row1_f1 σ (l^2) hσ (by positivity) hR1 hR2 hp hq
  have hpos : 0 < m^2 * (l^2*σ/(4*(σ^2 + 1))) * 10 * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^1 * (-75*σ^11*(l^2)^3 - 395*σ^11*(l^2)^2 - 520*σ^11*(l^2) + 87*σ^10*(l^2)^3 + 397*σ^10*(l^2)^2 + 448*σ^10*(l^2) + 283*σ^9*(l^2)^3 + 1848*σ^9*(l^2)^2 + 4784*σ^9*(l^2) + 4960*σ^9 - 41*σ^8*(l^2)^3 + 444*σ^8*(l^2)^2 + 1848*σ^8*(l^2) + 1440*σ^8 + 226*σ^7*(l^2)^3 + 3821*σ^7*(l^2)^2 + 14824*σ^7*(l^2) + 17760*σ^7 - 28*σ^6*(l^2)^3 + 557*σ^6*(l^2)^2 + 5216*σ^6*(l^2) + 7840*σ^6 - 32*σ^5*(l^2)^3 + 1378*σ^5*(l^2)^2 + 12928*σ^5*(l^2) + 23520*σ^5 + 510*σ^4*(l^2)^2 + 6680*σ^4*(l^2) + 14880*σ^4 - 200*σ^3*(l^2)^2 + 3120*σ^3*(l^2) + 13600*σ^3 + 2864*σ^2*(l^2) + 12000*σ^2 - 288*σ*(l^2) + 2880*σ + 3520) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54C_p0,k54C_p1,k54C_p2,k54C_p3,k54C_p4,k54C_p5,k54C_p6,k54C_om,k54C_ta,k54C_w,k54C_c1,k54C_c2,k54C_c3,k54C_c4,k54C_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54C_conv1 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 1 ≤ 5 * σ^2) (hq : 2 * σ^2 ≤ 3) :
    0 < det3 ((k54C_p2 σ l m ea) - (k54C_p4 σ l m ea)) ((k54C_p0 m) - (k54C_p4 σ l m ea)) (k54C_w σ l ea) := by
  have hpos : 0 < (m^2 * 1 * (σ^2 + 1)^1 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^1) / (8*(σ^2 + 1)^3) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54C_p0,k54C_p1,k54C_p2,k54C_p3,k54C_p4,k54C_p5,k54C_p6,k54C_om,k54C_ta,k54C_w,k54C_c1,k54C_c2,k54C_c3,k54C_c4,k54C_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54C_row2 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 1 ≤ 5 * σ^2) (hq : 2 * σ^2 ≤ 3) :
    0 < det3 ((k54C_p2 σ l m ea) - (k54C_p4 σ l m ea)) (cross (k54C_om σ l) (k54C_p4 σ l m ea) + (k54C_ta σ l m)) (k54C_w σ l ea) := by
  have hQ0 : 0 < σ^11*(l^2)^3 + 6*σ^11*(l^2)^2 + 8*σ^11*(l^2) - 8*σ^10*(l^2)^3 - 52*σ^10*(l^2)^2 - 80*σ^10*(l^2) + 448*σ^9*(l^2)^3 + 3006*σ^9*(l^2)^2 + 6704*σ^9*(l^2) + 4960*σ^9 + 134*σ^8*(l^2)^3 + 854*σ^8*(l^2)^2 + 1848*σ^8*(l^2) + 1440*σ^8 + 253*σ^7*(l^2)^3 + 4710*σ^7*(l^2)^2 + 17232*σ^7*(l^2) + 17760*σ^7 + 342*σ^6*(l^2)^3 + 3180*σ^6*(l^2)^2 + 8888*σ^6*(l^2) + 7840*σ^6 + 6*σ^5*(l^2)^3 + 1746*σ^5*(l^2)^2 + 14432*σ^5*(l^2) + 23520*σ^5 + 2270*σ^4*(l^2)^2 + 11896*σ^4*(l^2) + 14880*σ^4 + 36*σ^3*(l^2)^2 + 3944*σ^3*(l^2) + 13600*σ^3 - 4*σ^2*(l^2)^2 + 4920*σ^2*(l^2) + 12000*σ^2 + 48*σ*(l^2) + 2880*σ - 16*(l^2) + 3520 := k54C_C_row2_f2 σ (l^2) hσ (by positivity) hR1 hR2 hp hq
  have hpos : 0 < m^2 * (l^2*(l^2*σ^2 + 2*σ^2 + 2)/(4*(σ^2 + 1)^3)) * 10 * (σ^2 + 1)^1 * (σ)^1 * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (5*σ^2*(l^2) + 13*σ^2 + 13)^1 * (σ^11*(l^2)^3 + 6*σ^11*(l^2)^2 + 8*σ^11*(l^2) - 8*σ^10*(l^2)^3 - 52*σ^10*(l^2)^2 - 80*σ^10*(l^2) + 448*σ^9*(l^2)^3 + 3006*σ^9*(l^2)^2 + 6704*σ^9*(l^2) + 4960*σ^9 + 134*σ^8*(l^2)^3 + 854*σ^8*(l^2)^2 + 1848*σ^8*(l^2) + 1440*σ^8 + 253*σ^7*(l^2)^3 + 4710*σ^7*(l^2)^2 + 17232*σ^7*(l^2) + 17760*σ^7 + 342*σ^6*(l^2)^3 + 3180*σ^6*(l^2)^2 + 8888*σ^6*(l^2) + 7840*σ^6 + 6*σ^5*(l^2)^3 + 1746*σ^5*(l^2)^2 + 14432*σ^5*(l^2) + 23520*σ^5 + 2270*σ^4*(l^2)^2 + 11896*σ^4*(l^2) + 14880*σ^4 + 36*σ^3*(l^2)^2 + 3944*σ^3*(l^2) + 13600*σ^3 - 4*σ^2*(l^2)^2 + 4920*σ^2*(l^2) + 12000*σ^2 + 48*σ*(l^2) + 2880*σ - 16*(l^2) + 3520) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54C_p0,k54C_p1,k54C_p2,k54C_p3,k54C_p4,k54C_p5,k54C_p6,k54C_om,k54C_ta,k54C_w,k54C_c1,k54C_c2,k54C_c3,k54C_c4,k54C_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54C_row3 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 1 ≤ 5 * σ^2) (hq : 2 * σ^2 ≤ 3) :
    0 < det3 ((k54C_p4 σ l m ea) - (k54C_p0 m)) (cross (k54C_om σ l) (k54C_p4 σ l m ea) + (k54C_ta σ l m)) (k54C_w σ l ea) := by
  have hQ0 : 0 < -36*σ^12*(l^2)^4 - 313*σ^12*(l^2)^3 - 874*σ^12*(l^2)^2 - 792*σ^12*(l^2) + 2021*σ^11*(l^2)^4 + 18471*σ^11*(l^2)^3 + 63214*σ^11*(l^2)^2 + 95992*σ^11*(l^2) + 54560*σ^11 + 603*σ^10*(l^2)^4 + 5228*σ^10*(l^2)^3 + 17188*σ^10*(l^2)^2 + 26088*σ^10*(l^2) + 15840*σ^10 + 1147*σ^9*(l^2)^4 + 29020*σ^9*(l^2)^3 + 162742*σ^9*(l^2)^2 + 343424*σ^9*(l^2) + 249920*σ^9 + 1539*σ^8*(l^2)^4 + 19519*σ^8*(l^2)^3 + 84188*σ^8*(l^2)^2 + 153168*σ^8*(l^2) + 102080*σ^8 + 26*σ^7*(l^2)^4 + 10767*σ^7*(l^2)^3 + 136422*σ^7*(l^2)^2 + 454816*σ^7*(l^2) + 454080*σ^7 + 13962*σ^6*(l^2)^3 + 113216*σ^6*(l^2)^2 + 294912*σ^6*(l^2) + 249920*σ^6 + 218*σ^5*(l^2)^3 + 37474*σ^5*(l^2)^2 + 263824*σ^5*(l^2) + 408320*σ^5 - 16*σ^4*(l^2)^3 + 46990*σ^4*(l^2)^2 + 238488*σ^4*(l^2) + 295680*σ^4 + 580*σ^3*(l^2)^2 + 56936*σ^3*(l^2) + 181280*σ^3 - 100*σ^2*(l^2)^2 + 69720*σ^2*(l^2) + 170720*σ^2 + 496*σ*(l^2) + 31680*σ - 144*(l^2) + 38720 := k54C_C_row3_f3 σ (l^2) hσ (by positivity) hR1 hR2 hp hq
  have hpos : 0 < m^2 * (l^2/(8*(σ^2 + 1)^2)) * 40 * (σ^2 + 1)^1 * (σ)^1 * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (-36*σ^12*(l^2)^4 - 313*σ^12*(l^2)^3 - 874*σ^12*(l^2)^2 - 792*σ^12*(l^2) + 2021*σ^11*(l^2)^4 + 18471*σ^11*(l^2)^3 + 63214*σ^11*(l^2)^2 + 95992*σ^11*(l^2) + 54560*σ^11 + 603*σ^10*(l^2)^4 + 5228*σ^10*(l^2)^3 + 17188*σ^10*(l^2)^2 + 26088*σ^10*(l^2) + 15840*σ^10 + 1147*σ^9*(l^2)^4 + 29020*σ^9*(l^2)^3 + 162742*σ^9*(l^2)^2 + 343424*σ^9*(l^2) + 249920*σ^9 + 1539*σ^8*(l^2)^4 + 19519*σ^8*(l^2)^3 + 84188*σ^8*(l^2)^2 + 153168*σ^8*(l^2) + 102080*σ^8 + 26*σ^7*(l^2)^4 + 10767*σ^7*(l^2)^3 + 136422*σ^7*(l^2)^2 + 454816*σ^7*(l^2) + 454080*σ^7 + 13962*σ^6*(l^2)^3 + 113216*σ^6*(l^2)^2 + 294912*σ^6*(l^2) + 249920*σ^6 + 218*σ^5*(l^2)^3 + 37474*σ^5*(l^2)^2 + 263824*σ^5*(l^2) + 408320*σ^5 - 16*σ^4*(l^2)^3 + 46990*σ^4*(l^2)^2 + 238488*σ^4*(l^2) + 295680*σ^4 + 580*σ^3*(l^2)^2 + 56936*σ^3*(l^2) + 181280*σ^3 - 100*σ^2*(l^2)^2 + 69720*σ^2*(l^2) + 170720*σ^2 + 496*σ*(l^2) + 31680*σ - 144*(l^2) + 38720) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54C_p0,k54C_p1,k54C_p2,k54C_p3,k54C_p4,k54C_p5,k54C_p6,k54C_om,k54C_ta,k54C_w,k54C_c1,k54C_c2,k54C_c3,k54C_c4,k54C_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54C_conv2 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 1 ≤ 5 * σ^2) (hq : 2 * σ^2 ≤ 3) :
    0 < det3 ((k54C_p3 σ l m ea) - (k54C_p2 σ l m ea)) ((k54C_p4 σ l m ea) - (k54C_p2 σ l m ea)) (k54C_w σ l ea) := by
  have hpos : 0 < (m^2 * 1 * (σ^2 + 1)^3 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^1 * (5*σ^2*(l^2) + 13*σ^2 + 13)^1) / (4*(σ^2 + 1)^6) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54C_p0,k54C_p1,k54C_p2,k54C_p3,k54C_p4,k54C_p5,k54C_p6,k54C_om,k54C_ta,k54C_w,k54C_c1,k54C_c2,k54C_c3,k54C_c4,k54C_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54C_row4 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 1 ≤ 5 * σ^2) (hq : 2 * σ^2 ≤ 3) :
    0 < det3 ((k54C_p3 σ l m ea) - (k54C_p2 σ l m ea)) (cross (k54C_om σ l) (k54C_p2 σ l m ea) + (k54C_ta σ l m)) (k54C_w σ l ea) := by
  have hQ0 : 0 < 2 - σ^2 := k54C_C_det5 σ (l^2) hσ (by positivity) hR1 hR2 hp hq
  have hQ1 : 0 < 9*σ^4*(l^2) + 22*σ^4 - σ^2*(l^2) + 18*σ^2 - 4 := k54C_C_det6 σ (l^2) hσ (by positivity) hR1 hR2 hp hq
  have hpos : 0 < m^2 * (l^2*(l^2*σ^2 + 4*σ^2 + 4)/(8*(σ^2 + 1)^3)) * 20 * (2 - σ^2) * (σ^2 + 1)^2 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^1 * (5*σ^2*(l^2) + 13*σ^2 + 13)^1 * (9*σ^4*(l^2) + 22*σ^4 - σ^2*(l^2) + 18*σ^2 - 4) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54C_p0,k54C_p1,k54C_p2,k54C_p3,k54C_p4,k54C_p5,k54C_p6,k54C_om,k54C_ta,k54C_w,k54C_c1,k54C_c2,k54C_c3,k54C_c4,k54C_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54C_row5 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 1 ≤ 5 * σ^2) (hq : 2 * σ^2 ≤ 3) :
    0 < det3 ((k54C_p2 σ l m ea) - (k54C_p4 σ l m ea)) (cross (k54C_om σ l) (k54C_p2 σ l m ea) + (k54C_ta σ l m)) (k54C_w σ l ea) := by
  have hQ0 : 0 < 2 - σ^2 := k54C_C_det5 σ (l^2) hσ (by positivity) hR1 hR2 hp hq
  have hQ1 : 0 < 9*σ^4*(l^2) + 22*σ^4 - σ^2*(l^2) + 18*σ^2 - 4 := k54C_C_det6 σ (l^2) hσ (by positivity) hR1 hR2 hp hq
  have hpos : 0 < m^2 * (l^2*(l^2*σ^2 + 2*σ^2 + 2)/(8*(σ^2 + 1)^3)) * 20 * (2 - σ^2) * (σ^2 + 1)^2 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^1 * (5*σ^2*(l^2) + 13*σ^2 + 13)^1 * (9*σ^4*(l^2) + 22*σ^4 - σ^2*(l^2) + 18*σ^2 - 4) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54C_p0,k54C_p1,k54C_p2,k54C_p3,k54C_p4,k54C_p5,k54C_p6,k54C_om,k54C_ta,k54C_w,k54C_c1,k54C_c2,k54C_c3,k54C_c4,k54C_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54C_conv3 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 1 ≤ 5 * σ^2) (hq : 2 * σ^2 ≤ 3) :
    0 < det3 ((k54C_p5 σ l m ea) - (k54C_p3 σ l m ea)) ((k54C_p2 σ l m ea) - (k54C_p3 σ l m ea)) (k54C_w σ l ea) := by
  have hpos : 0 < (m^2 * 1 * (σ^2 + 1)^3 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^1 * (5*σ^2*(l^2) + 13*σ^2 + 13)^1) / (4*(σ^2 + 1)^6) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54C_p0,k54C_p1,k54C_p2,k54C_p3,k54C_p4,k54C_p5,k54C_p6,k54C_om,k54C_ta,k54C_w,k54C_c1,k54C_c2,k54C_c3,k54C_c4,k54C_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54C_row6 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 1 ≤ 5 * σ^2) (hq : 2 * σ^2 ≤ 3) :
    0 < det3 ((k54C_p5 σ l m ea) - (k54C_p3 σ l m ea)) (cross (k54C_om σ l) (k54C_p3 σ l m ea) + (k54C_ta σ l m)) (k54C_w σ l ea) := by
  have hQ0 : 0 < 2 - σ^2 := k54C_C_det5 σ (l^2) hσ (by positivity) hR1 hR2 hp hq
  have hQ1 : 0 < 9*σ^4*(l^2) + 22*σ^4 - σ^2*(l^2) + 18*σ^2 - 4 := k54C_C_det6 σ (l^2) hσ (by positivity) hR1 hR2 hp hq
  have hpos : 0 < m^2 * (l^2*σ*(l^2*σ^2 + 2*σ^2 + 2)/(4*(σ^2 + 1)^3)) * 20 * (2 - σ^2) * (σ^2 + 1)^2 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^1 * (5*σ^2*(l^2) + 13*σ^2 + 13)^1 * (9*σ^4*(l^2) + 22*σ^4 - σ^2*(l^2) + 18*σ^2 - 4) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54C_p0,k54C_p1,k54C_p2,k54C_p3,k54C_p4,k54C_p5,k54C_p6,k54C_om,k54C_ta,k54C_w,k54C_c1,k54C_c2,k54C_c3,k54C_c4,k54C_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54C_row7 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 1 ≤ 5 * σ^2) (hq : 2 * σ^2 ≤ 3) :
    0 < det3 ((k54C_p3 σ l m ea) - (k54C_p2 σ l m ea)) (cross (k54C_om σ l) (k54C_p3 σ l m ea) + (k54C_ta σ l m)) (k54C_w σ l ea) := by
  have hQ0 : 0 < 2 - σ^2 := k54C_C_det5 σ (l^2) hσ (by positivity) hR1 hR2 hp hq
  have hQ1 : 0 < 9*σ^4*(l^2) + 22*σ^4 - σ^2*(l^2) + 18*σ^2 - 4 := k54C_C_det6 σ (l^2) hσ (by positivity) hR1 hR2 hp hq
  have hpos : 0 < m^2 * (l^2*σ*(l^2*σ^2 + 4*σ^2 + 4)/(8*(σ^2 + 1)^3)) * 20 * (2 - σ^2) * (σ^2 + 1)^2 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^1 * (5*σ^2*(l^2) + 13*σ^2 + 13)^1 * (9*σ^4*(l^2) + 22*σ^4 - σ^2*(l^2) + 18*σ^2 - 4) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54C_p0,k54C_p1,k54C_p2,k54C_p3,k54C_p4,k54C_p5,k54C_p6,k54C_om,k54C_ta,k54C_w,k54C_c1,k54C_c2,k54C_c3,k54C_c4,k54C_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54C_conv4 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 1 ≤ 5 * σ^2) (hq : 2 * σ^2 ≤ 3) :
    0 < det3 ((k54C_p0 m) - (k54C_p5 σ l m ea)) ((k54C_p3 σ l m ea) - (k54C_p5 σ l m ea)) (k54C_w σ l ea) := by
  have hpos : 0 < (m^2 * 1 * (σ^2 + 1)^1 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^1) / (4*(σ^2 + 1)^3) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54C_p0,k54C_p1,k54C_p2,k54C_p3,k54C_p4,k54C_p5,k54C_p6,k54C_om,k54C_ta,k54C_w,k54C_c1,k54C_c2,k54C_c3,k54C_c4,k54C_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54C_row8 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 1 ≤ 5 * σ^2) (hq : 2 * σ^2 ≤ 3) :
    0 < det3 ((k54C_p0 m) - (k54C_p5 σ l m ea)) (cross (k54C_om σ l) (k54C_p5 σ l m ea) + (k54C_ta σ l m)) (k54C_w σ l ea) := by
  have hQ0 : 0 < -85*σ^11*(l^2)^3 - 395*σ^11*(l^2)^2 - 458*σ^11*(l^2) - 4*σ^10*(l^2)^3 - 17*σ^10*(l^2)^2 - 18*σ^10*(l^2) + 319*σ^9*(l^2)^3 + 1562*σ^9*(l^2)^2 + 2974*σ^9*(l^2) + 2480*σ^9 + 67*σ^8*(l^2)^3 + 426*σ^8*(l^2)^2 + 942*σ^8*(l^2) + 720*σ^8 + 288*σ^7*(l^2)^3 + 3549*σ^7*(l^2)^2 + 10086*σ^7*(l^2) + 8880*σ^7 + 171*σ^6*(l^2)^3 + 1563*σ^6*(l^2)^2 + 4374*σ^6*(l^2) + 3920*σ^6 - 16*σ^5*(l^2)^3 + 1492*σ^5*(l^2)^2 + 9274*σ^5*(l^2) + 11760*σ^5 + 1120*σ^4*(l^2)^2 + 5850*σ^4*(l^2) + 7440*σ^4 - 100*σ^3*(l^2)^2 + 2476*σ^3*(l^2) + 6800*σ^3 + 2436*σ^2*(l^2) + 6000*σ^2 - 144*σ*(l^2) + 1440*σ + 1760 := k54C_C_row8_f4 σ (l^2) hσ (by positivity) hR1 hR2 hp hq
  have hpos : 0 < m^2 * (l^2*σ/(8*(σ^2 + 1)^2)) * 40 * (σ^2 + 1)^1 * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^1 * (-85*σ^11*(l^2)^3 - 395*σ^11*(l^2)^2 - 458*σ^11*(l^2) - 4*σ^10*(l^2)^3 - 17*σ^10*(l^2)^2 - 18*σ^10*(l^2) + 319*σ^9*(l^2)^3 + 1562*σ^9*(l^2)^2 + 2974*σ^9*(l^2) + 2480*σ^9 + 67*σ^8*(l^2)^3 + 426*σ^8*(l^2)^2 + 942*σ^8*(l^2) + 720*σ^8 + 288*σ^7*(l^2)^3 + 3549*σ^7*(l^2)^2 + 10086*σ^7*(l^2) + 8880*σ^7 + 171*σ^6*(l^2)^3 + 1563*σ^6*(l^2)^2 + 4374*σ^6*(l^2) + 3920*σ^6 - 16*σ^5*(l^2)^3 + 1492*σ^5*(l^2)^2 + 9274*σ^5*(l^2) + 11760*σ^5 + 1120*σ^4*(l^2)^2 + 5850*σ^4*(l^2) + 7440*σ^4 - 100*σ^3*(l^2)^2 + 2476*σ^3*(l^2) + 6800*σ^3 + 2436*σ^2*(l^2) + 6000*σ^2 - 144*σ*(l^2) + 1440*σ + 1760) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54C_p0,k54C_p1,k54C_p2,k54C_p3,k54C_p4,k54C_p5,k54C_p6,k54C_om,k54C_ta,k54C_w,k54C_c1,k54C_c2,k54C_c3,k54C_c4,k54C_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54C_row9 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 1 ≤ 5 * σ^2) (hq : 2 * σ^2 ≤ 3) :
    0 < det3 ((k54C_p5 σ l m ea) - (k54C_p3 σ l m ea)) (cross (k54C_om σ l) (k54C_p5 σ l m ea) + (k54C_ta σ l m)) (k54C_w σ l ea) := by
  have hQ0 : 0 < 2 - σ^2 := k54C_C_det5 σ (l^2) hσ (by positivity) hR1 hR2 hp hq
  have hQ1 : 0 < 9*σ^4*(l^2) + 22*σ^4 - σ^2*(l^2) + 18*σ^2 - 4 := k54C_C_det6 σ (l^2) hσ (by positivity) hR1 hR2 hp hq
  have hpos : 0 < m^2 * (l^2*σ*(l^2*σ^2 + 2*σ^2 + 2)/(4*(σ^2 + 1)^3)) * 20 * (2 - σ^2) * (σ^2 + 1)^2 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^1 * (5*σ^2*(l^2) + 13*σ^2 + 13)^1 * (9*σ^4*(l^2) + 22*σ^4 - σ^2*(l^2) + 18*σ^2 - 4) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54C_p0,k54C_p1,k54C_p2,k54C_p3,k54C_p4,k54C_p5,k54C_p6,k54C_om,k54C_ta,k54C_w,k54C_c1,k54C_c2,k54C_c3,k54C_c4,k54C_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54C_int1tri {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 1 ≤ 5 * σ^2) (hq : 2 * σ^2 ≤ 3) :
    0 < det3 ((k54C_p2 σ l m ea) - (k54C_p0 m)) ((k54C_p3 σ l m ea) - (k54C_p0 m)) (k54C_w σ l ea) := by
  have hpos : 0 < (m^2 * 1 * (σ^2 + 1)^3 * (σ)^1 * (l)^2 * (10*σ^2*(l^2) + 23*σ^2 + 23)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^2) / (8*(σ^2 + 1)^6) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54C_p0,k54C_p1,k54C_p2,k54C_p3,k54C_p4,k54C_p5,k54C_p6,k54C_om,k54C_ta,k54C_w,k54C_c1,k54C_c2,k54C_c3,k54C_c4,k54C_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54C_int1e1 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 1 ≤ 5 * σ^2) (hq : 2 * σ^2 ≤ 3) :
    0 < det3 ((k54C_p2 σ l m ea) - (k54C_p0 m)) ((k54C_p1 m ea) - (k54C_p0 m)) (k54C_w σ l ea) := by
  have hpos : 0 < (m^2 * 1 * (σ^2 + 1)^1 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 4*σ^2 + 4)^2) / (8*(σ^2 + 1)^3) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54C_p0,k54C_p1,k54C_p2,k54C_p3,k54C_p4,k54C_p5,k54C_p6,k54C_om,k54C_ta,k54C_w,k54C_c1,k54C_c2,k54C_c3,k54C_c4,k54C_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54C_int1e2 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 1 ≤ 5 * σ^2) (hq : 2 * σ^2 ≤ 3) :
    0 < det3 ((k54C_p3 σ l m ea) - (k54C_p2 σ l m ea)) ((k54C_p1 m ea) - (k54C_p2 σ l m ea)) (k54C_w σ l ea) := by
  have hpos : 0 < (m^2 * 5 * (σ^2 + 1)^3 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^2) / (4*(σ^2 + 1)^6) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54C_p0,k54C_p1,k54C_p2,k54C_p3,k54C_p4,k54C_p5,k54C_p6,k54C_om,k54C_ta,k54C_w,k54C_c1,k54C_c2,k54C_c3,k54C_c4,k54C_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54C_int1e3 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 1 ≤ 5 * σ^2) (hq : 2 * σ^2 ≤ 3) :
    0 < det3 ((k54C_p0 m) - (k54C_p3 σ l m ea)) ((k54C_p1 m ea) - (k54C_p3 σ l m ea)) (k54C_w σ l ea) := by
  have hpos : 0 < (m^2 * 1 * (σ^2 + 1)^1 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 4*σ^2 + 4)^2) / (4*(σ^2 + 1)^3) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54C_p0,k54C_p1,k54C_p2,k54C_p3,k54C_p4,k54C_p5,k54C_p6,k54C_om,k54C_ta,k54C_w,k54C_c1,k54C_c2,k54C_c3,k54C_c4,k54C_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54C_int6tri {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 1 ≤ 5 * σ^2) (hq : 2 * σ^2 ≤ 3) :
    0 < det3 ((k54C_p2 σ l m ea) - (k54C_p0 m)) ((k54C_p3 σ l m ea) - (k54C_p0 m)) (k54C_w σ l ea) := by
  have hpos : 0 < (m^2 * 1 * (σ^2 + 1)^3 * (σ)^1 * (l)^2 * (10*σ^2*(l^2) + 23*σ^2 + 23)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^2) / (8*(σ^2 + 1)^6) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54C_p0,k54C_p1,k54C_p2,k54C_p3,k54C_p4,k54C_p5,k54C_p6,k54C_om,k54C_ta,k54C_w,k54C_c1,k54C_c2,k54C_c3,k54C_c4,k54C_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54C_int6e1 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 1 ≤ 5 * σ^2) (hq : 2 * σ^2 ≤ 3) :
    0 < det3 ((k54C_p2 σ l m ea) - (k54C_p0 m)) ((k54C_p6 σ l m ea) - (k54C_p0 m)) (k54C_w σ l ea) := by
  have hpos : 0 < (m^2 * 3 * (σ^2 + 1)^3 * (σ)^1 * (l)^2 * (3*σ^2*(l^2) + 7*σ^2 + 7)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^2) / (16*(σ^2 + 1)^6) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54C_p0,k54C_p1,k54C_p2,k54C_p3,k54C_p4,k54C_p5,k54C_p6,k54C_om,k54C_ta,k54C_w,k54C_c1,k54C_c2,k54C_c3,k54C_c4,k54C_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54C_int6e2 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 1 ≤ 5 * σ^2) (hq : 2 * σ^2 ≤ 3) :
    0 < det3 ((k54C_p3 σ l m ea) - (k54C_p2 σ l m ea)) ((k54C_p6 σ l m ea) - (k54C_p2 σ l m ea)) (k54C_w σ l ea) := by
  have hpos : 0 < (m^2 * 3 * (σ^2 + 1)^3 * (σ)^1 * (l)^2 * (σ^2*(l^2) + 2*σ^2 + 2)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^2) / (16*(σ^2 + 1)^6) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54C_p0,k54C_p1,k54C_p2,k54C_p3,k54C_p4,k54C_p5,k54C_p6,k54C_om,k54C_ta,k54C_w,k54C_c1,k54C_c2,k54C_c3,k54C_c4,k54C_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem k54C_int6e3 {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : l^2*(1-σ^2) ≤ 4*(1+σ^2)) (hR2 : l^2*σ^2*(σ^2-1) < 4*(1+σ^2)) (hp : 1 ≤ 5 * σ^2) (hq : 2 * σ^2 ≤ 3) :
    0 < det3 ((k54C_p0 m) - (k54C_p3 σ l m ea)) ((k54C_p6 σ l m ea) - (k54C_p3 σ l m ea)) (k54C_w σ l ea) := by
  have hpos : 0 < (m^2 * 1 * (σ^2 + 1)^3 * (σ)^1 * (l)^2 * (8*σ^2*(l^2) + 19*σ^2 + 19)^1 * (σ^2*(l^2) + 4*σ^2 + 4)^2) / (16*(σ^2 + 1)^6) := by positivity
  refine lt_of_lt_of_eq hpos ?_
  subst hea
  simp only [k54C_p0,k54C_p1,k54C_p2,k54C_p3,k54C_p4,k54C_p5,k54C_p6,k54C_om,k54C_ta,k54C_w,k54C_c1,k54C_c2,k54C_c3,k54C_c4,k54C_c5, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, cross_apply_zero, cross_apply_one, cross_apply_two]
  field_simp
  ring

theorem k54C_regions {σ l ea : ℝ} (hσ : 0 < σ) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : ea ≤ σ^2 * (2 + ea)) (hR2 : ea * σ^2 < 2 + ea) :
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
theorem a2mc_C {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m) (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : ea ≤ σ^2 * (2 + ea)) (hR2 : ea * σ^2 < 2 + ea) (hp : 1 ≤ 5 * σ^2) (hq : 2 * σ^2 ≤ 3) :
    IsRupert (V8 (k54C_p1 m ea) (k54C_p6 σ l m ea) (k54C_p4 σ l m ea) (k54C_p3 σ l m ea) (k54C_p5 σ l m ea) (k54C_p2 σ l m ea) (k54C_p0 m)) := by
  obtain ⟨hr1, hr2⟩ := k54C_regions hσ hea hR1 hR2
  refine isRupert_of_tiltCert _ (k54C_w σ l ea) ?_ (k54C_om σ l) (k54C_ta σ l m) ?_
  · intro h
    have h1 := congrArg (fun v : ℝ³ => v 1) h
    simp only [k54C_w, pt_one] at h1
    simp at h1
    linarith
  · intro x hx
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · left
      exact ⟨(k54C_p5 σ l m ea), by simp [V8], (k54C_p4 σ l m ea), by simp [V8], k54C_conv0 hσ hl hm hea hr1 hr2 hp hq, k54C_row0 hσ hl hm hea hr1 hr2 hp hq, k54C_row1 hσ hl hm hea hr1 hr2 hp hq⟩
    · right
      exact ⟨(k54C_p0 m), by simp [V8], (k54C_p2 σ l m ea), by simp [V8], (k54C_p3 σ l m ea), by simp [V8], k54C_int1tri hσ hl hm hea hr1 hr2 hp hq, k54C_int1e1 hσ hl hm hea hr1 hr2 hp hq, k54C_int1e2 hσ hl hm hea hr1 hr2 hp hq, k54C_int1e3 hσ hl hm hea hr1 hr2 hp hq⟩
    · right
      exact ⟨(k54C_p0 m), by simp [V8], (k54C_p2 σ l m ea), by simp [V8], (k54C_p3 σ l m ea), by simp [V8], k54C_int6tri hσ hl hm hea hr1 hr2 hp hq, k54C_int6e1 hσ hl hm hea hr1 hr2 hp hq, k54C_int6e2 hσ hl hm hea hr1 hr2 hp hq, k54C_int6e3 hσ hl hm hea hr1 hr2 hp hq⟩
    · left
      exact ⟨(k54C_p0 m), by simp [V8], (k54C_p2 σ l m ea), by simp [V8], k54C_conv1 hσ hl hm hea hr1 hr2 hp hq, k54C_row2 hσ hl hm hea hr1 hr2 hp hq, k54C_row3 hσ hl hm hea hr1 hr2 hp hq⟩
    · left
      exact ⟨(k54C_p2 σ l m ea), by simp [V8], (k54C_p5 σ l m ea), by simp [V8], k54C_conv3 hσ hl hm hea hr1 hr2 hp hq, k54C_row6 hσ hl hm hea hr1 hr2 hp hq, k54C_row7 hσ hl hm hea hr1 hr2 hp hq⟩
    · left
      exact ⟨(k54C_p3 σ l m ea), by simp [V8], (k54C_p0 m), by simp [V8], k54C_conv4 hσ hl hm hea hr1 hr2 hp hq, k54C_row8 hσ hl hm hea hr1 hr2 hp hq, k54C_row9 hσ hl hm hea hr1 hr2 hp hq⟩
    · left
      exact ⟨(k54C_p4 σ l m ea), by simp [V8], (k54C_p3 σ l m ea), by simp [V8], k54C_conv2 hσ hl hm hea hr1 hr2 hp hq, k54C_row4 hσ hl hm hea hr1 hr2 hp hq, k54C_row5 hσ hl hm hea hr1 hr2 hp hq⟩

end Minimality.Type08Sp.C2
