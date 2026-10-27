module

public import Minimality.CaseC20Bridge
public import Minimality.CaseC20ST
public import Minimality.CaseC20NR
public import Minimality.CaseC20Tests
public import Minimality.CaseC20TestsNR
public import Minimality.CaseC20VSlide

@[expose] public section

/-!
# Type 20, acute case (c): the covering lemmas of Theorem 27.79 (generated)

Each lemma `Frame20.<leaf>` (and its `R`-image `<leaf>_R`) takes the sign hypotheses of one leaf of the
case tree of `CaseC20Final` (positive shape polynomials, signs of metric rows) and closes the frame
with two to four tests of `CaseC20Tests`/`CaseC20TestsNR`: if no test is robust, the weak depth
inequalities of one failure pattern per test hold, and a nonnegative combination of products of
the positive quantities with these rows is a contradiction (`linarith only` with an explicit hint
list found by a linear program over the products).

* `ra4_A`, `ra4_tBR`, `ra4_X`, `ra4_Y` : `V` of class Ra (4-cycle) with `T_A` (`b+ > a−`), 27.32^R
  (`c− > b+`), `X` (`A3` fails), `Y` (`A3` holds) -- 27.64.
* `om1*` : `{T_A, T′}` for `b+ < a−`, `t+ ≤ t−` (27.74 (i)), split on `ω` and the line `ℓ1`.
* `om2a`, `om2b`, `om3*` : `{T_A, V}` (+ `T′`), `V` of class N4, `h+ ≥ d+` or `t+ ≤ t−` (27.74 (ii)).
* `om4a..d*` : `{T′, T_A^R, V^R}` (+ `T′^R`) (27.76), split on `ν` and the lines `ℓν`, `ℓ1^R`.
* `famA1`, `famA2`, `famE` : family A (the pair `T1`, `T2` by the sign of `⟨u1, u2⟩`) and the edge
  crossing at `xa xb` (27.27, 27.31, 27.78).
-/

namespace Minimality.CaseC20

open Finset Filter Minimality.CaseC09 Minimality.CaseC18
open scoped RealInnerProductSpace Topology

/-- Q_A = V + T_A (27.64 (ii)) -/
theorem Frame20.ra4_A {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hW : 0 < -F.S.hp*F.S.sp + F.S.hp - F.S.kp) (hQ : 0 < F.S.hm*F.S.sp*F.S.tp - F.S.hm*F.S.tp + F.S.hp*F.S.sp*F.S.tm - F.S.hp*F.S.sp - F.S.hp*F.S.tm + F.S.hp + F.S.kp*F.S.tm - F.S.kp) (hD : 0 < -F.S.hp*F.S.sm*F.S.sp + F.S.hp*F.S.sm + F.S.hp*F.S.sp - F.S.hp - F.S.km*F.S.sp*F.S.tp + F.S.km*F.S.tp - F.S.kp*F.S.sm + F.S.kp) (hA1 : 0 < F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm)   :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.dep F.S.u_vRa4 0 < F.dep F.S.u_vRa4 6 ∨ F.dep F.S.u_vRa4 0 < F.dep F.S.u_vRa4 1 ∨ F.dep F.S.u_vRa4 4 < F.dep F.S.u_vRa4 6 ∨ F.dep F.S.u_vRa4 4 < F.dep F.S.u_vRa4 1) ∧ (F.dep F.S.u_vRa4 6 < F.dep F.S.u_vRa4 0 ∨ F.dep F.S.u_vRa4 1 < F.dep F.S.u_vRa4 0 ∨ F.dep F.S.u_vRa4 6 < F.dep F.S.u_vRa4 4 ∨ F.dep F.S.u_vRa4 1 < F.dep F.S.u_vRa4 4)
  · exact F.vRa4 (by linarith only [hW]) (by linarith only [hQ]) (by linarith only [hD]) o0.1 o0.2
  by_cases o1 : (F.dep F.S.u_tA 0 < F.dep F.S.u_tA 6 ∨ F.dep F.S.u_tA 0 < F.dep F.S.u_tA 5 ∨ F.dep F.S.u_tA 4 < F.dep F.S.u_tA 6 ∨ F.dep F.S.u_tA 4 < F.dep F.S.u_tA 5) ∧ (F.dep F.S.u_tA 6 < F.dep F.S.u_tA 0 ∨ F.dep F.S.u_tA 5 < F.dep F.S.u_tA 0 ∨ F.dep F.S.u_tA 6 < F.dep F.S.u_tA 4 ∨ F.dep F.S.u_tA 5 < F.dep F.S.u_tA 4)
  · exact F.tA (by linarith only [hA1]) o1.1 o1.2
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_tA] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n1_3), mul_nonneg (hsm1).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.hp_pos F.S.km_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_tA] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(sub_nonneg.2 n0_2), mul_nonneg (hsp1).le (sub_nonneg.2 n1_1), mul_pos ((mul_pos htp1 hsp1)) hga, mul_pos ((mul_pos F.S.hp_pos F.S.kp_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_tA] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(sub_nonneg.2 n1_4), mul_pos ((mul_pos htp1 F.S.sm_pos)) hga, mul_pos ((mul_pos F.S.hp_pos F.S.km_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_tA] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg ((mul_pos F.S.tp_pos htp1)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos htp1 htp1)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos F.S.tp_pos hsp1)).le (sub_nonneg.2 n1_1), mul_pos ((mul_pos F.S.hp_pos hQ)) hde, mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.hp_pos) F.S.kp_pos)) hde, mul_pos ((mul_pos (mul_pos F.S.tm_pos hW) hA1)) hde, mul_pos ((mul_pos (mul_pos htm1 hW) hA1)) hde, mul_pos ((mul_pos (mul_pos F.S.sm_pos F.S.hm_pos) rp)) hde, mul_pos ((mul_pos (mul_pos hsm1 F.S.hm_pos) rp)) hde]

/-- 27.32^R (27.64 (iii)) -/
theorem Frame20.ra4_tBR {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hCr : 0 < -F.S.hp*F.S.sm - F.S.km*F.S.tp + F.S.km)   :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.rFrame.dep F.rFrame.S.u_tB 0 < F.rFrame.dep F.rFrame.S.u_tB 1 ∨ F.rFrame.dep F.rFrame.S.u_tB 0 < F.rFrame.dep F.rFrame.S.u_tB 2 ∨ F.rFrame.dep F.rFrame.S.u_tB 6 < F.rFrame.dep F.rFrame.S.u_tB 1 ∨ F.rFrame.dep F.rFrame.S.u_tB 6 < F.rFrame.dep F.rFrame.S.u_tB 2) ∧ (F.rFrame.dep F.rFrame.S.u_tB 1 < F.rFrame.dep F.rFrame.S.u_tB 0 ∨ F.rFrame.dep F.rFrame.S.u_tB 2 < F.rFrame.dep F.rFrame.S.u_tB 0 ∨ F.rFrame.dep F.rFrame.S.u_tB 1 < F.rFrame.dep F.rFrame.S.u_tB 6 ∨ F.rFrame.dep F.rFrame.S.u_tB 2 < F.rFrame.dep F.rFrame.S.u_tB 6)
  · exact rupert_of_r (F.rFrame.tB (by simp only [rFrame_S, Shape20.swap]; refine pos_of_pos_mul htp1 ?_; linarith only [(mul_pos hsp1 hCr), (mul_pos F.S.sm_pos rp)]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hCr]) o0.1 o0.2)
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  rcases o0 with n0 | n0
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tB] at n0_1 n0_2 n0_3 n0_4
    linarith only [mul_nonneg (hCr).le (sub_nonneg.2 n0_3), mul_pos ((mul_pos F.S.sm_pos hCr)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tB] at n0_1 n0_2 n0_3 n0_4
    linarith only [mul_nonneg ((mul_pos F.S.sm_pos F.S.hm_pos)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos htm1 F.S.km_pos)).le (sub_nonneg.2 n0_2), mul_nonneg ((mul_pos F.S.tm_pos F.S.km_pos)).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos (mul_pos F.S.sm_pos F.S.sm_pos) rm)) hbe, mul_pos ((mul_pos (mul_pos F.S.sm_pos F.S.sm_pos) rm)) hga, mul_pos ((mul_pos (mul_pos F.S.km_pos F.S.km_pos) rm)) hde]

/-- V + Y (27.64 (iv)) -/
theorem Frame20.ra4_Y {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hW : 0 < -F.S.hp*F.S.sp + F.S.hp - F.S.kp) (hQ : 0 < F.S.hm*F.S.sp*F.S.tp - F.S.hm*F.S.tp + F.S.hp*F.S.sp*F.S.tm - F.S.hp*F.S.sp - F.S.hp*F.S.tm + F.S.hp + F.S.kp*F.S.tm - F.S.kp) (hD : 0 < -F.S.hp*F.S.sm*F.S.sp + F.S.hp*F.S.sm + F.S.hp*F.S.sp - F.S.hp - F.S.km*F.S.sp*F.S.tp + F.S.km*F.S.tp - F.S.kp*F.S.sm + F.S.kp) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hCm : 0 < F.S.hp*F.S.sm + F.S.km*F.S.tp - F.S.km) (hA3h : 0 < -F.S.hm*F.S.sm*F.S.tp + F.S.hm - F.S.hp*F.S.sm*F.S.tm + F.S.hp*F.S.sm + F.S.km*F.S.tm - F.S.km)   :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.dep F.S.u_vRa4 0 < F.dep F.S.u_vRa4 6 ∨ F.dep F.S.u_vRa4 0 < F.dep F.S.u_vRa4 1 ∨ F.dep F.S.u_vRa4 4 < F.dep F.S.u_vRa4 6 ∨ F.dep F.S.u_vRa4 4 < F.dep F.S.u_vRa4 1) ∧ (F.dep F.S.u_vRa4 6 < F.dep F.S.u_vRa4 0 ∨ F.dep F.S.u_vRa4 1 < F.dep F.S.u_vRa4 0 ∨ F.dep F.S.u_vRa4 6 < F.dep F.S.u_vRa4 4 ∨ F.dep F.S.u_vRa4 1 < F.dep F.S.u_vRa4 4)
  · exact F.vRa4 (by linarith only [hW]) (by linarith only [hQ]) (by linarith only [hD]) o0.1 o0.2
  by_cases o1 : (F.dep F.S.u_yY 1 < F.dep F.S.u_yY 3 ∨ F.dep F.S.u_yY 1 < F.dep F.S.u_yY 6 ∨ F.dep F.S.u_yY 2 < F.dep F.S.u_yY 6 ∨ F.dep F.S.u_yY 2 < F.dep F.S.u_yY 5) ∧ (F.dep F.S.u_yY 6 < F.dep F.S.u_yY 1 ∨ F.dep F.S.u_yY 6 < F.dep F.S.u_yY 2 ∨ F.dep F.S.u_yY 5 < F.dep F.S.u_yY 2 ∨ F.dep F.S.u_yY 5 < F.dep F.S.u_yY 3) ∧ (F.dep F.S.u_yY 2 < F.dep F.S.u_yY 6 ∨ F.dep F.S.u_yY 2 < F.dep F.S.u_yY 5 ∨ F.dep F.S.u_yY 3 < F.dep F.S.u_yY 5 ∨ F.dep F.S.u_yY 3 < F.dep F.S.u_yY 1) ∧ (F.dep F.S.u_yY 5 < F.dep F.S.u_yY 2 ∨ F.dep F.S.u_yY 5 < F.dep F.S.u_yY 3 ∨ F.dep F.S.u_yY 1 < F.dep F.S.u_yY 3 ∨ F.dep F.S.u_yY 1 < F.dep F.S.u_yY 6) ∧ (F.dep F.S.u_yY 3 < F.dep F.S.u_yY 5 ∨ F.dep F.S.u_yY 3 < F.dep F.S.u_yY 1 ∨ F.dep F.S.u_yY 6 < F.dep F.S.u_yY 1 ∨ F.dep F.S.u_yY 6 < F.dep F.S.u_yY 2)
  · exact F.yY (by refine pos_of_pos_mul htp1 ?_; linarith only [(mul_pos F.S.tm_pos hCm), (mul_pos (mul_pos F.S.tp_pos F.S.sm_pos) hA1r)]) (by linarith only [hA3h]) o1.1 o1.2.1 o1.2.2.1 o1.2.2.2.1 o1.2.2.2.2
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 | n1 | n1 | n1
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tp_pos hsp1)) hal, mul_pos ((mul_pos (mul_pos F.S.tp_pos hsp1) hsm1)) hga, mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.km_pos) hW)) hde, mul_pos ((mul_pos (mul_pos htp1 F.S.km_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos F.S.tm_pos F.S.km_pos) rp)) hde, mul_pos ((mul_pos (mul_pos F.S.tm_pos hD) hA1r)) hde, mul_pos ((mul_pos (mul_pos htm1 hD) hA1r)) hde, mul_pos ((mul_pos (mul_pos hsm1 hW) hA1r)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n1_1), (sub_nonneg.2 n1_2), mul_pos ((mul_pos F.S.tp_pos F.S.sp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.tm_pos)) hbe, mul_pos ((mul_pos F.S.tm_pos htm1)) hbe, mul_pos ((mul_pos htm1 htm1)) hbe, mul_pos ((mul_pos htp1 hsp1)) hga, mul_pos ((mul_pos F.S.hp_pos F.S.kp_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.hp_pos F.S.hm_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg ((mul_pos F.S.hp_pos F.S.km_pos)).le (sub_nonneg.2 n0_2), mul_nonneg ((mul_pos F.S.km_pos hA1r)).le (sub_nonneg.2 n0_2), mul_nonneg ((mul_pos F.S.hp_pos F.S.hp_pos)).le (sub_nonneg.2 n0_4), mul_nonneg ((mul_pos F.S.hp_pos hA1r)).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.kp_pos) hA3h)) hal, mul_pos ((mul_pos (mul_pos F.S.tp_pos hW) hA3h)) hal, mul_pos ((mul_pos (mul_pos htp1 F.S.hp_pos) hD)) hal, mul_pos ((mul_pos (mul_pos htp1 rm) hD)) hal, mul_pos ((mul_pos (mul_pos htp1 hD) hA1r)) hal, mul_pos ((mul_pos (mul_pos htm1 hD) hCm)) hal, mul_pos ((mul_pos (mul_pos hsm1 F.S.hp_pos) rp)) hal, mul_pos ((mul_pos (mul_pos hsm1 rp) rm)) hal, mul_pos ((mul_pos (mul_pos hsm1 rp) hA1r)) hal, mul_pos ((mul_pos (mul_pos hsm1 hQ) hCm)) hal, mul_pos ((mul_pos (mul_pos htp1 F.S.hp_pos) hD)) hga, mul_pos ((mul_pos (mul_pos htp1 hD) hA1r)) hga, mul_pos ((mul_pos (mul_pos hsm1 F.S.hp_pos) rp)) hga, mul_pos ((mul_pos (mul_pos hsm1 rp) hA1r)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.sp_pos hsp1)) hbe, mul_pos ((mul_pos hsp1 hsp1)) hbe, mul_pos ((mul_pos htp1 hsp1)) hga, mul_pos ((mul_pos F.S.hp_pos F.S.kp_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg ((mul_pos F.S.tp_pos htm1)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos htp1 htm1)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos F.S.tp_pos hsp1)).le (sub_nonneg.2 n1_1), mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.kp_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos htp1 F.S.kp_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos F.S.sm_pos hW) hQ)) hde, mul_pos ((mul_pos (mul_pos hsm1 hW) hQ)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n1_1), mul_nonneg (hA3h).le (sub_nonneg.2 n1_1), mul_pos ((mul_pos F.S.tp_pos F.S.kp_pos)) hal, mul_pos ((mul_pos F.S.tp_pos F.S.km_pos)) hal, mul_pos ((mul_pos F.S.tp_pos hA3h)) hal, mul_pos ((mul_pos F.S.tp_pos rp)) hbe, mul_pos ((mul_pos F.S.tp_pos hD)) hbe, mul_pos ((mul_pos htp1 F.S.kp_pos)) hbe, mul_pos ((mul_pos htp1 F.S.km_pos)) hbe, mul_pos ((mul_pos htp1 rp)) hbe, mul_pos ((mul_pos htp1 hD)) hbe, mul_pos ((mul_pos F.S.tm_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sp_pos hCm)) hbe, mul_pos ((mul_pos F.S.sm_pos F.S.kp_pos)) hbe, mul_pos ((mul_pos F.S.sm_pos hA1r)) hbe, mul_pos ((mul_pos hsm1 F.S.hm_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.hp_pos F.S.hm_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg ((mul_pos htm1 F.S.sm_pos)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos htm1 hsm1)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos F.S.tp_pos hsp1)).le (sub_nonneg.2 n1_3), mul_pos ((mul_pos (mul_pos htp1 F.S.km_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos F.S.sm_pos hQ) hCm)) hde, mul_pos ((mul_pos (mul_pos hsm1 F.S.hp_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos hsm1 hQ) hCm)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_3), mul_nonneg (hW).le (sub_nonneg.2 n1_3), mul_nonneg (hD).le (sub_nonneg.2 n1_3), mul_pos ((mul_pos F.S.tp_pos F.S.kp_pos)) hal, mul_pos ((mul_pos F.S.tp_pos hW)) hal, mul_pos ((mul_pos F.S.tp_pos hD)) hal, mul_pos ((mul_pos hsp1 F.S.km_pos)) hbe, mul_pos ((mul_pos hsp1 hCm)) hbe, mul_pos ((mul_pos hsm1 F.S.kp_pos)) hbe]

/-- V + X (27.64 (iv)) -/
theorem Frame20.ra4_X {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hW : 0 < -F.S.hp*F.S.sp + F.S.hp - F.S.kp) (hQ : 0 < F.S.hm*F.S.sp*F.S.tp - F.S.hm*F.S.tp + F.S.hp*F.S.sp*F.S.tm - F.S.hp*F.S.sp - F.S.hp*F.S.tm + F.S.hp + F.S.kp*F.S.tm - F.S.kp) (hD : 0 < -F.S.hp*F.S.sm*F.S.sp + F.S.hp*F.S.sm + F.S.hp*F.S.sp - F.S.hp - F.S.km*F.S.sp*F.S.tp + F.S.km*F.S.tp - F.S.kp*F.S.sm + F.S.kp) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hCm : 0 < F.S.hp*F.S.sm + F.S.km*F.S.tp - F.S.km) (hA3 : 0 < F.S.hm*F.S.sm*F.S.tp - F.S.hm + F.S.hp*F.S.sm*F.S.tm - F.S.hp*F.S.sm - F.S.km*F.S.tm + F.S.km)   :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.dep F.S.u_vRa4 0 < F.dep F.S.u_vRa4 6 ∨ F.dep F.S.u_vRa4 0 < F.dep F.S.u_vRa4 1 ∨ F.dep F.S.u_vRa4 4 < F.dep F.S.u_vRa4 6 ∨ F.dep F.S.u_vRa4 4 < F.dep F.S.u_vRa4 1) ∧ (F.dep F.S.u_vRa4 6 < F.dep F.S.u_vRa4 0 ∨ F.dep F.S.u_vRa4 1 < F.dep F.S.u_vRa4 0 ∨ F.dep F.S.u_vRa4 6 < F.dep F.S.u_vRa4 4 ∨ F.dep F.S.u_vRa4 1 < F.dep F.S.u_vRa4 4)
  · exact F.vRa4 (by linarith only [hW]) (by linarith only [hQ]) (by linarith only [hD]) o0.1 o0.2
  by_cases o1 : (F.dep F.S.u_xX 1 < F.dep F.S.u_xX 6 ∨ F.dep F.S.u_xX 1 < F.dep F.S.u_xX 3 ∨ F.dep F.S.u_xX 5 < F.dep F.S.u_xX 3 ∨ F.dep F.S.u_xX 5 < F.dep F.S.u_xX 2) ∧ (F.dep F.S.u_xX 3 < F.dep F.S.u_xX 1 ∨ F.dep F.S.u_xX 3 < F.dep F.S.u_xX 5 ∨ F.dep F.S.u_xX 2 < F.dep F.S.u_xX 5 ∨ F.dep F.S.u_xX 2 < F.dep F.S.u_xX 6) ∧ (F.dep F.S.u_xX 5 < F.dep F.S.u_xX 3 ∨ F.dep F.S.u_xX 5 < F.dep F.S.u_xX 2 ∨ F.dep F.S.u_xX 6 < F.dep F.S.u_xX 2 ∨ F.dep F.S.u_xX 6 < F.dep F.S.u_xX 1) ∧ (F.dep F.S.u_xX 2 < F.dep F.S.u_xX 5 ∨ F.dep F.S.u_xX 2 < F.dep F.S.u_xX 6 ∨ F.dep F.S.u_xX 1 < F.dep F.S.u_xX 6 ∨ F.dep F.S.u_xX 1 < F.dep F.S.u_xX 3) ∧ (F.dep F.S.u_xX 6 < F.dep F.S.u_xX 2 ∨ F.dep F.S.u_xX 6 < F.dep F.S.u_xX 1 ∨ F.dep F.S.u_xX 3 < F.dep F.S.u_xX 1 ∨ F.dep F.S.u_xX 3 < F.dep F.S.u_xX 5)
  · exact F.xX (by linarith only [hA3]) (by linarith only [hA1r]) (by linarith only [hCm]) o1.1 o1.2.1 o1.2.2.1 o1.2.2.2.1 o1.2.2.2.2
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 | n1 | n1 | n1
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n1_1), mul_nonneg (hsp1).le (sub_nonneg.2 n1_1), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htm1 hCm)) hal, mul_pos ((mul_pos htp1 rm)) hbe, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hbe, mul_pos ((mul_pos htm1 hCm)) hbe, mul_pos ((mul_pos F.S.sm_pos hA1r)) hbe, mul_pos ((mul_pos hsm1 hA1r)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg ((mul_pos F.S.tm_pos htm1)).le (sub_nonneg.2 n0_4), mul_nonneg ((mul_pos F.S.tm_pos F.S.sp_pos)).le (sub_nonneg.2 n0_4), mul_nonneg ((mul_pos F.S.tm_pos hsp1)).le (sub_nonneg.2 n0_4), mul_nonneg ((mul_pos htm1 htm1)).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.tm_pos) hsp1)) hal, mul_pos ((mul_pos (mul_pos F.S.tp_pos htm1) hsp1)) hal, mul_pos ((mul_pos (mul_pos F.S.tp_pos hsp1) hsm1)) hga, mul_pos ((mul_pos hQ hCm)) hde, mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.hm_pos) hD)) hde, mul_pos ((mul_pos (mul_pos htp1 rm) hW)) hde, mul_pos ((mul_pos (mul_pos F.S.tm_pos F.S.km_pos) hW)) hde, mul_pos ((mul_pos (mul_pos F.S.sm_pos F.S.hm_pos) rp)) hde, mul_pos ((mul_pos (mul_pos F.S.sm_pos F.S.km_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos F.S.sm_pos hW) hA3)) hde, mul_pos ((mul_pos (mul_pos hsm1 F.S.hm_pos) hW)) hde, mul_pos ((mul_pos (mul_pos hsm1 F.S.km_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos hsm1 hW) hA3)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(sub_nonneg.2 n0_4), mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.sp_pos) hsp1)) hal, mul_pos ((mul_pos (mul_pos F.S.tp_pos hsp1) hsp1)) hal, mul_pos ((mul_pos (mul_pos F.S.tp_pos hsp1) hsm1)) hga, mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.hm_pos) hD)) hde, mul_pos ((mul_pos (mul_pos F.S.tp_pos hW) hQ)) hde, mul_pos ((mul_pos (mul_pos F.S.tp_pos hW) hD)) hde, mul_pos ((mul_pos (mul_pos F.S.tp_pos hW) hA3)) hde, mul_pos ((mul_pos (mul_pos htp1 rm) hQ)) hde, mul_pos ((mul_pos (mul_pos htp1 hW) hQ)) hde, mul_pos ((mul_pos (mul_pos htp1 hW) hD)) hde, mul_pos ((mul_pos (mul_pos htp1 hW) hA3)) hde, mul_pos ((mul_pos (mul_pos F.S.tm_pos F.S.kp_pos) hD)) hde, mul_pos ((mul_pos (mul_pos F.S.tm_pos F.S.km_pos) hW)) hde, mul_pos ((mul_pos (mul_pos F.S.tm_pos F.S.km_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos F.S.tm_pos rp) rm)) hde, mul_pos ((mul_pos (mul_pos htm1 F.S.km_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos htm1 hD) hA1r)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.hm_pos) hD)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.km_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos hQ) hCm)) hde, mul_pos ((mul_pos (mul_pos hsp1 hD) hA1r)) hde, mul_pos ((mul_pos (mul_pos F.S.sm_pos F.S.hm_pos) rp)) hde, mul_pos ((mul_pos (mul_pos F.S.sm_pos F.S.kp_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos hsm1 F.S.hm_pos) hW)) hde, mul_pos ((mul_pos (mul_pos hsm1 hQ) hA1r)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(sub_nonneg.2 n1_3), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htm1 hCm)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsp1 hA1r)) hal, mul_pos ((mul_pos htp1 rm)) hbe, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hbe, mul_pos ((mul_pos htm1 hCm)) hbe, mul_pos ((mul_pos F.S.sm_pos hA1r)) hbe, mul_pos ((mul_pos hsm1 hA1r)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg ((mul_pos F.S.tp_pos F.S.sp_pos)).le (sub_nonneg.2 n0_4), mul_nonneg ((mul_pos htp1 F.S.sp_pos)).le (sub_nonneg.2 n0_4), mul_nonneg ((mul_pos F.S.sp_pos hsp1)).le (sub_nonneg.2 n0_4), mul_nonneg ((mul_pos hsp1 hsp1)).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.tm_pos) hsp1)) hal, mul_pos ((mul_pos (mul_pos F.S.tp_pos htm1) hsp1)) hal, mul_pos ((mul_pos (mul_pos F.S.tp_pos hsp1) hsm1)) hga, mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.km_pos) hW)) hde, mul_pos ((mul_pos (mul_pos htp1 F.S.km_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos F.S.tm_pos F.S.km_pos) rp)) hde, mul_pos ((mul_pos (mul_pos F.S.tm_pos hD) hA1r)) hde, mul_pos ((mul_pos (mul_pos htm1 hD) hA1r)) hde, mul_pos ((mul_pos (mul_pos hsm1 hW) hA1r)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n1_1), mul_nonneg (hsp1).le (sub_nonneg.2 n1_1), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htm1 hCm)) hal, mul_pos ((mul_pos htp1 rm)) hbe, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hbe, mul_pos ((mul_pos htm1 hCm)) hbe, mul_pos ((mul_pos F.S.sm_pos hA1r)) hbe, mul_pos ((mul_pos hsm1 hA1r)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg ((mul_pos F.S.tm_pos F.S.sm_pos)).le (sub_nonneg.2 n1_4), mul_nonneg ((mul_pos htm1 F.S.sm_pos)).le (sub_nonneg.2 n1_4), mul_nonneg ((mul_pos F.S.sm_pos hsm1)).le (sub_nonneg.2 n1_4), mul_nonneg ((mul_pos hsm1 hsm1)).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.tm_pos) rp)) hbe, mul_pos ((mul_pos (mul_pos F.S.tp_pos hsp1) hA1r)) hbe, mul_pos ((mul_pos (mul_pos F.S.tp_pos hsp1) hCm)) hbe, mul_pos ((mul_pos (mul_pos htp1 F.S.tm_pos) rp)) hbe, mul_pos ((mul_pos (mul_pos htp1 F.S.tm_pos) hD)) hbe, mul_pos ((mul_pos (mul_pos htp1 htm1) hD)) hbe, mul_pos ((mul_pos (mul_pos htp1 F.S.sm_pos) F.S.kp_pos)) hbe, mul_pos ((mul_pos (mul_pos htp1 F.S.sm_pos) hQ)) hbe, mul_pos ((mul_pos (mul_pos htp1 hsm1) hQ)) hbe, mul_pos ((mul_pos (mul_pos hsp1 F.S.sm_pos) hA1r)) hbe, mul_pos ((mul_pos (mul_pos htp1 hsp1) hA3)) hga, mul_pos ((mul_pos (mul_pos htp1 F.S.sm_pos) F.S.kp_pos)) hga, mul_pos ((mul_pos (mul_pos htp1 F.S.sm_pos) hQ)) hga, mul_pos ((mul_pos (mul_pos F.S.tm_pos F.S.sm_pos) rp)) hga, mul_pos ((mul_pos (mul_pos hsp1 F.S.sm_pos) hA1r)) hga, mul_pos ((mul_pos (mul_pos F.S.hp_pos F.S.kp_pos) rm)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg ((mul_pos F.S.tm_pos hA1r)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos htp1 F.S.tm_pos) rm)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos F.S.tm_pos F.S.tm_pos) F.S.hp_pos)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos F.S.tm_pos htm1) hCm)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos F.S.tm_pos hA3)).le (sub_nonneg.2 n0_2), mul_nonneg ((mul_pos F.S.tp_pos hsp1)).le (sub_nonneg.2 n1_1), mul_pos ((mul_pos (mul_pos (mul_pos F.S.tp_pos F.S.hm_pos) rp) hA3)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.tp_pos F.S.hm_pos) hW) hCm)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.tp_pos F.S.hm_pos) hD) hA1r)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.tp_pos F.S.hm_pos) hD) hCm)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.tp_pos F.S.kp_pos) hA1r) hA3)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.tm_pos F.S.hp_pos) F.S.hp_pos) hW)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.tm_pos F.S.hp_pos) F.S.hp_pos) hD)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.tm_pos F.S.hp_pos) F.S.hm_pos) F.S.kp_pos)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.tm_pos F.S.hp_pos) F.S.kp_pos) hA1r)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.tm_pos F.S.hp_pos) F.S.km_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.tm_pos F.S.hp_pos) rp) hA3)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.tm_pos F.S.hp_pos) hD) hA1r)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.tm_pos F.S.hp_pos) hD) hCm)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.tm_pos F.S.hm_pos) F.S.km_pos) rp)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.tm_pos F.S.kp_pos) F.S.km_pos) hA3)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.tm_pos F.S.kp_pos) hCm) hA3)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.tm_pos F.S.km_pos) rp) hA1r)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.tm_pos F.S.km_pos) hW) hA3)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.tm_pos F.S.km_pos) hQ) hA1r)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.tm_pos F.S.km_pos) hQ) hCm)) hde, mul_pos ((mul_pos (mul_pos (mul_pos htm1 F.S.hm_pos) F.S.kp_pos) hCm)) hde, mul_pos ((mul_pos (mul_pos (mul_pos htm1 F.S.kp_pos) hA1r) hCm)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.sp_pos F.S.kp_pos) hA1r) hA1r)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.sp_pos F.S.kp_pos) hA1r) hA3)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.sp_pos hW) hA1r) hCm)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.sp_pos hQ) hA1r) hA3)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.sp_pos hD) hA1r) hA1r)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.sp_pos hD) hA1r) hCm)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.sp_pos hD) hA1r) hA3)) hde, mul_pos ((mul_pos (mul_pos (mul_pos hsp1 F.S.kp_pos) hA1r) hA1r)) hde, mul_pos ((mul_pos (mul_pos (mul_pos hsp1 F.S.kp_pos) hA1r) hA3)) hde, mul_pos ((mul_pos (mul_pos (mul_pos hsp1 hW) hA1r) hCm)) hde, mul_pos ((mul_pos (mul_pos (mul_pos hsp1 hQ) hA1r) hA3)) hde, mul_pos ((mul_pos (mul_pos (mul_pos hsp1 hD) hA1r) hA1r)) hde, mul_pos ((mul_pos (mul_pos (mul_pos hsp1 hD) hA1r) hCm)) hde, mul_pos ((mul_pos (mul_pos (mul_pos hsp1 hD) hA1r) hA3)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.sm_pos F.S.kp_pos) hA1r) hA3)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.sm_pos hQ) hA1r) hA1r)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.sm_pos hQ) hA1r) hCm)) hde, mul_pos ((mul_pos (mul_pos (mul_pos hsm1 F.S.hm_pos) F.S.kp_pos) hA3)) hde, mul_pos ((mul_pos (mul_pos (mul_pos hsm1 F.S.hm_pos) rp) hA1r)) hde, mul_pos ((mul_pos (mul_pos (mul_pos hsm1 F.S.hm_pos) rp) hCm)) hde, mul_pos ((mul_pos (mul_pos (mul_pos hsm1 F.S.hm_pos) hW) hA3)) hde, mul_pos ((mul_pos (mul_pos (mul_pos hsm1 F.S.hm_pos) hQ) hA1r)) hde, mul_pos ((mul_pos (mul_pos (mul_pos hsm1 F.S.hm_pos) hQ) hCm)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(sub_nonneg.2 n1_3), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htm1 hCm)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsp1 hA1r)) hal, mul_pos ((mul_pos htp1 rm)) hbe, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hbe, mul_pos ((mul_pos htm1 hCm)) hbe, mul_pos ((mul_pos F.S.sm_pos hA1r)) hbe, mul_pos ((mul_pos hsm1 hA1r)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg ((mul_pos htm1 hCm)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos hsm1 hA1r)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos htp1 F.S.tm_pos) rm)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos htp1 htm1) rm)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos F.S.tm_pos hsm1) F.S.hp_pos)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos htm1 F.S.sm_pos) hA1r)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos F.S.tm_pos htm1) hA3)).le (sub_nonneg.2 n0_2), mul_nonneg ((mul_pos (mul_pos htm1 htm1) hA3)).le (sub_nonneg.2 n0_2), mul_nonneg ((mul_pos F.S.tp_pos hsp1)).le (sub_nonneg.2 n1_3), mul_pos ((mul_pos (mul_pos F.S.hp_pos rm) hQ)) hde]

/-- 27.74 (i), ω > 0 -/
theorem Frame20.om1p {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (htt : 0 ≤ F.S.tm - F.S.tp) (hom : 0 < (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) (hH : ¬ F.ClassH)  :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.dep F.S.u_tANR 0 < F.dep F.S.u_tANR 6 ∨ F.dep F.S.u_tANR 0 < F.dep F.S.u_tANR 3 ∨ F.dep F.S.u_tANR 4 < F.dep F.S.u_tANR 6 ∨ F.dep F.S.u_tANR 4 < F.dep F.S.u_tANR 3) ∧ (F.dep F.S.u_tANR 6 < F.dep F.S.u_tANR 0 ∨ F.dep F.S.u_tANR 3 < F.dep F.S.u_tANR 0 ∨ F.dep F.S.u_tANR 6 < F.dep F.S.u_tANR 4 ∨ F.dep F.S.u_tANR 3 < F.dep F.S.u_tANR 4)
  · exact F.tANR_slide hx (by linarith only [hA1r]) o0.1 o0.2 hH
  by_cases o1 : (F.dep F.S.u_tP 1 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 1 < F.dep F.S.u_tP 6 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 6) ∧ (F.dep F.S.u_tP 3 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 3 < F.dep F.S.u_tP 4 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 4)
  · exact F.tP (by linarith only [hA1r]) o1.1 o1.2
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n1_2), mul_nonneg (htp1).le (sub_nonneg.2 n1_2), mul_pos ((mul_pos htp1 F.S.tm_pos)) hal, mul_pos ((mul_pos htp1 htm1)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(sub_nonneg.2 n1_4), mul_pos F.S.sp_pos hom, mul_pos hsp1 hom]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n0_2), mul_nonneg (htp1).le (sub_nonneg.2 n0_4), mul_nonneg (htm1).le (sub_nonneg.2 n1_1), mul_pos htm1 hom, mul_nonneg htt hom.le, mul_pos ((mul_pos htp1 htp1)) hal, mul_pos ((mul_pos F.S.hp_pos F.S.hp_pos)) hde, mul_pos ((mul_pos F.S.hp_pos hA1r)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n0_1), mul_nonneg (htp1).le (sub_nonneg.2 n0_4), mul_nonneg htt (sub_nonneg.2 n1_2), mul_pos htm1 hom, mul_nonneg htt hom.le, mul_pos ((mul_pos F.S.hp_pos F.S.hp_pos)) hde, mul_pos ((mul_pos F.S.hp_pos hA1r)) hde]

/-- 27.74 (i), ω < 0 -/
theorem Frame20.om1n {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (htt : 0 ≤ F.S.tm - F.S.tp) (hom : 0 < (-F.S.sm*F.S.tp + F.S.sm + F.S.tp - 1) * F.a12 + (F.S.hp*F.S.km) * F.gg) (hH : ¬ F.ClassH)  :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.dep F.S.u_tANR 0 < F.dep F.S.u_tANR 6 ∨ F.dep F.S.u_tANR 0 < F.dep F.S.u_tANR 3 ∨ F.dep F.S.u_tANR 4 < F.dep F.S.u_tANR 6 ∨ F.dep F.S.u_tANR 4 < F.dep F.S.u_tANR 3) ∧ (F.dep F.S.u_tANR 6 < F.dep F.S.u_tANR 0 ∨ F.dep F.S.u_tANR 3 < F.dep F.S.u_tANR 0 ∨ F.dep F.S.u_tANR 6 < F.dep F.S.u_tANR 4 ∨ F.dep F.S.u_tANR 3 < F.dep F.S.u_tANR 4)
  · exact F.tANR_slide hx (by linarith only [hA1r]) o0.1 o0.2 hH
  by_cases o1 : (F.dep F.S.u_tP 1 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 1 < F.dep F.S.u_tP 6 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 6) ∧ (F.dep F.S.u_tP 3 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 3 < F.dep F.S.u_tP 4 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 4)
  · exact F.tP (by linarith only [hA1r]) o1.1 o1.2
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(sub_nonneg.2 n1_2), mul_pos ((mul_pos htp1 F.S.tm_pos)) hal, mul_pos ((mul_pos htp1 htm1)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (htp1).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n0_3), mul_pos F.S.sp_pos hom, mul_pos hsp1 hom, mul_nonneg htt hom.le]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n1_1), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_3), mul_pos F.S.hm_pos hom, mul_pos ((mul_pos htp1 F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 F.S.hp_pos)) hga, mul_pos ((mul_pos htp1 hA1r)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n0_2), mul_nonneg htt (sub_nonneg.2 n1_1), mul_pos ((mul_pos F.S.hp_pos F.S.hp_pos)) hde, mul_pos ((mul_pos F.S.hp_pos hA1r)) hde]

/-- 27.74 (i), ω = 0, off ℓ1 -/
theorem Frame20.om1z1 {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (htt : 0 ≤ F.S.tm - F.S.tp) (hom1 : 0 ≤ (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) (hom2 : 0 ≤ (-F.S.sm*F.S.tp + F.S.sm + F.S.tp - 1) * F.a12 + (F.S.hp*F.S.km) * F.gg) (hl : 0 < (F.S.km*F.S.tm) * (F.a11 - F.a12) + (-F.S.hm*F.S.sm + F.S.hm + F.S.km*F.S.tm - F.S.km) * F.a12) (hH : ¬ F.ClassH)  :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.dep F.S.u_tANR 0 < F.dep F.S.u_tANR 6 ∨ F.dep F.S.u_tANR 0 < F.dep F.S.u_tANR 3 ∨ F.dep F.S.u_tANR 4 < F.dep F.S.u_tANR 6 ∨ F.dep F.S.u_tANR 4 < F.dep F.S.u_tANR 3) ∧ (F.dep F.S.u_tANR 6 < F.dep F.S.u_tANR 0 ∨ F.dep F.S.u_tANR 3 < F.dep F.S.u_tANR 0 ∨ F.dep F.S.u_tANR 6 < F.dep F.S.u_tANR 4 ∨ F.dep F.S.u_tANR 3 < F.dep F.S.u_tANR 4)
  · exact F.tANR_slide hx (by linarith only [hA1r]) o0.1 o0.2 hH
  by_cases o1 : (F.dep F.S.u_tP 1 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 1 < F.dep F.S.u_tP 6 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 6) ∧ (F.dep F.S.u_tP 3 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 3 < F.dep F.S.u_tP 4 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 4)
  · exact F.tP (by linarith only [hA1r]) o1.1 o1.2
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n1_2), mul_nonneg (htm1).le (sub_nonneg.2 n1_2), mul_pos ((mul_pos htp1 F.S.sm_pos)) hal, mul_pos ((mul_pos htp1 hsm1)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_4), mul_pos htm1 hl, mul_nonneg htt hl.le]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_1), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n1_1), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n1_4), mul_pos htm1 hl, mul_nonneg htt hl.le, mul_pos ((mul_pos htp1 F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 F.S.hp_pos)) hga, mul_pos ((mul_pos htp1 hA1r)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n0_1), mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n0_3), mul_nonneg (htp1).le (sub_nonneg.2 n0_4), mul_nonneg htt (sub_nonneg.2 n1_2), mul_nonneg (F.S.tm_pos).le hom1, mul_nonneg (htm1).le hom1, mul_pos ((mul_pos F.S.hp_pos F.S.hp_pos)) hde, mul_pos ((mul_pos F.S.hp_pos hA1r)) hde]

/-- 27.74 (i), ω = 0, off ℓ1 -/
theorem Frame20.om1z2 {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (htt : 0 ≤ F.S.tm - F.S.tp) (hom1 : 0 ≤ (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) (hom2 : 0 ≤ (-F.S.sm*F.S.tp + F.S.sm + F.S.tp - 1) * F.a12 + (F.S.hp*F.S.km) * F.gg) (hl : 0 < (-F.S.km*F.S.tm) * (F.a11 - F.a12) + (F.S.hm*F.S.sm - F.S.hm - F.S.km*F.S.tm + F.S.km) * F.a12) (hH : ¬ F.ClassH)  :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.dep F.S.u_tANR 0 < F.dep F.S.u_tANR 6 ∨ F.dep F.S.u_tANR 0 < F.dep F.S.u_tANR 3 ∨ F.dep F.S.u_tANR 4 < F.dep F.S.u_tANR 6 ∨ F.dep F.S.u_tANR 4 < F.dep F.S.u_tANR 3) ∧ (F.dep F.S.u_tANR 6 < F.dep F.S.u_tANR 0 ∨ F.dep F.S.u_tANR 3 < F.dep F.S.u_tANR 0 ∨ F.dep F.S.u_tANR 6 < F.dep F.S.u_tANR 4 ∨ F.dep F.S.u_tANR 3 < F.dep F.S.u_tANR 4)
  · exact F.tANR_slide hx (by linarith only [hA1r]) o0.1 o0.2 hH
  by_cases o1 : (F.dep F.S.u_tP 1 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 1 < F.dep F.S.u_tP 6 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 6) ∧ (F.dep F.S.u_tP 3 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 3 < F.dep F.S.u_tP 4 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 4)
  · exact F.tP (by linarith only [hA1r]) o1.1 o1.2
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n1_1), mul_pos htm1 hl, mul_nonneg htt hl.le, mul_pos ((mul_pos htp1 F.S.km_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n1_4), mul_pos htm1 hl, mul_nonneg htt hl.le]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_1), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n1_1), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_1), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos htp1 F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 F.S.hp_pos)) hga, mul_pos ((mul_pos htp1 hA1r)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n0_2), mul_nonneg htt (sub_nonneg.2 n1_1), mul_pos ((mul_pos F.S.hp_pos F.S.hp_pos)) hde, mul_pos ((mul_pos F.S.hp_pos hA1r)) hde]

/-- 27.74 (ii): {T_A, V}, h+ ≥ d+ -/
theorem Frame20.om2a {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1 : 0 < F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) (hVp : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm - F.S.kp*F.S.tm) (hVW : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.sp + F.S.hp*F.S.tm - F.S.hp - F.S.kp*F.S.tm + F.S.kp) (hWp : 0 ≤ -F.S.hp*F.S.sp + F.S.hp - F.S.kp) (hH : ¬ F.ClassH)  :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.dep F.S.u_tA 0 < F.dep F.S.u_tA 6 ∨ F.dep F.S.u_tA 0 < F.dep F.S.u_tA 5 ∨ F.dep F.S.u_tA 4 < F.dep F.S.u_tA 6 ∨ F.dep F.S.u_tA 4 < F.dep F.S.u_tA 5) ∧ (F.dep F.S.u_tA 6 < F.dep F.S.u_tA 0 ∨ F.dep F.S.u_tA 5 < F.dep F.S.u_tA 0 ∨ F.dep F.S.u_tA 6 < F.dep F.S.u_tA 4 ∨ F.dep F.S.u_tA 5 < F.dep F.S.u_tA 4)
  · exact F.tA (by linarith only [hA1]) o0.1 o0.2
  by_cases o1 : (F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 3 ∨ F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 6 ∨ F.dep F.S.u_vN4 4 < F.dep F.S.u_vN4 3 ∨ F.dep F.S.u_vN4 4 < F.dep F.S.u_vN4 6) ∧ (F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 0 ∨ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 0 ∨ F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 4 ∨ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 4)
  · exact F.vN4_slide hx (by linarith only [hVp]) (by linarith only [hVW]) o1.1 o1.2 hH
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n0_3), mul_nonneg (hsm1).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.hp_pos F.S.km_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n0_3), mul_nonneg (hsm1).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.hp_pos F.S.km_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg hWp (sub_nonneg.2 n0_3), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg ((mul_pos F.S.tp_pos hsp1)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos htp1 F.S.tm_pos)).le (sub_nonneg.2 n1_2), mul_nonneg ((mul_pos htp1 htm1)).le (sub_nonneg.2 n1_2), mul_pos ((mul_pos (mul_pos F.S.tp_pos rp) rp)) hde, mul_pos ((mul_pos (mul_pos htp1 F.S.kp_pos) rp)) hde, mul_pos ((mul_pos (mul_pos htp1 rp) rp)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) rp)) hde]

/-- 27.74 (ii): {T_A, V}, t+ ≤ t−, h+ ≤ d+ -/
theorem Frame20.om2b {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1 : 0 < F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) (hVp : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm - F.S.kp*F.S.tm) (hVW : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.sp + F.S.hp*F.S.tm - F.S.hp - F.S.kp*F.S.tm + F.S.kp) (htt : 0 ≤ F.S.tm - F.S.tp) (hWn : 0 ≤ F.S.hp*F.S.sp - F.S.hp + F.S.kp) (hH : ¬ F.ClassH)  :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.dep F.S.u_tA 0 < F.dep F.S.u_tA 6 ∨ F.dep F.S.u_tA 0 < F.dep F.S.u_tA 5 ∨ F.dep F.S.u_tA 4 < F.dep F.S.u_tA 6 ∨ F.dep F.S.u_tA 4 < F.dep F.S.u_tA 5) ∧ (F.dep F.S.u_tA 6 < F.dep F.S.u_tA 0 ∨ F.dep F.S.u_tA 5 < F.dep F.S.u_tA 0 ∨ F.dep F.S.u_tA 6 < F.dep F.S.u_tA 4 ∨ F.dep F.S.u_tA 5 < F.dep F.S.u_tA 4)
  · exact F.tA (by linarith only [hA1]) o0.1 o0.2
  by_cases o1 : (F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 3 ∨ F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 6 ∨ F.dep F.S.u_vN4 4 < F.dep F.S.u_vN4 3 ∨ F.dep F.S.u_vN4 4 < F.dep F.S.u_vN4 6) ∧ (F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 0 ∨ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 0 ∨ F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 4 ∨ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 4)
  · exact F.vN4_slide hx (by linarith only [hVp]) (by linarith only [hVW]) o1.1 o1.2 hH
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n0_4), mul_nonneg (htm1).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos htp1 F.S.sm_pos)) hga, mul_pos ((mul_pos F.S.hp_pos F.S.km_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n0_4), mul_nonneg (hsp1).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos htp1 F.S.sm_pos)) hga, mul_pos ((mul_pos F.S.hp_pos F.S.km_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le (F.S.km_pos).le) htt) (sub_nonneg.2 n0_2), mul_nonneg (mul_nonneg (mul_nonneg (F.S.sm_pos).le (F.S.kp_pos).le) htt) (sub_nonneg.2 n0_3), mul_nonneg (mul_nonneg (mul_nonneg (hsm1).le (F.S.kp_pos).le) htt) (sub_nonneg.2 n0_4), mul_nonneg ((mul_pos htp1 F.S.km_pos)).le (sub_nonneg.2 n1_1), mul_nonneg ((mul_pos htp1 F.S.hm_pos)).le (sub_nonneg.2 n1_4), mul_nonneg ((mul_pos (mul_pos F.S.tp_pos htm1) F.S.hp_pos)).le (sub_nonneg.2 n1_4), mul_nonneg ((mul_pos (mul_pos htp1 htm1) F.S.hp_pos)).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos (mul_pos htp1 hsm1) hVW)) hga, mul_pos ((mul_pos (mul_pos htm1 hsm1) rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg ((mul_pos F.S.tp_pos hsp1)).le (sub_nonneg.2 n0_1), mul_nonneg htt (sub_nonneg.2 n1_2), mul_nonneg ((mul_pos F.S.tp_pos htp1)).le (sub_nonneg.2 n1_2), mul_nonneg ((mul_pos htp1 htm1)).le (sub_nonneg.2 n1_2), mul_nonneg ((mul_pos F.S.tm_pos htm1)).le (sub_nonneg.2 n1_2), mul_nonneg (mul_nonneg htt htt) (sub_nonneg.2 n1_2), mul_pos ((mul_pos (mul_pos F.S.tp_pos rp) hA1)) hde, mul_pos ((mul_pos (mul_pos htp1 F.S.hm_pos) rp)) hde, mul_pos ((mul_pos (mul_pos htp1 rp) hA1)) hde, mul_pos ((mul_pos (mul_pos htm1 F.S.hp_pos) rp)) hde]

/-- 27.74 (ii): {T_A, V, T′}, h+ ≥ d+, p -/
theorem Frame20.om3p {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hVp : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm - F.S.kp*F.S.tm) (hVW : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.sp + F.S.hp*F.S.tm - F.S.hp - F.S.kp*F.S.tm + F.S.kp) (hWp : 0 ≤ -F.S.hp*F.S.sp + F.S.hp - F.S.kp) (hom : 0 < (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) (hH : ¬ F.ClassH)   :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.dep F.S.u_tANR 0 < F.dep F.S.u_tANR 6 ∨ F.dep F.S.u_tANR 0 < F.dep F.S.u_tANR 3 ∨ F.dep F.S.u_tANR 4 < F.dep F.S.u_tANR 6 ∨ F.dep F.S.u_tANR 4 < F.dep F.S.u_tANR 3) ∧ (F.dep F.S.u_tANR 6 < F.dep F.S.u_tANR 0 ∨ F.dep F.S.u_tANR 3 < F.dep F.S.u_tANR 0 ∨ F.dep F.S.u_tANR 6 < F.dep F.S.u_tANR 4 ∨ F.dep F.S.u_tANR 3 < F.dep F.S.u_tANR 4)
  · exact F.tANR_slide hx (by linarith only [hA1r]) o0.1 o0.2 hH
  by_cases o1 : (F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 3 ∨ F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 6 ∨ F.dep F.S.u_vN4 4 < F.dep F.S.u_vN4 3 ∨ F.dep F.S.u_vN4 4 < F.dep F.S.u_vN4 6) ∧ (F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 0 ∨ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 0 ∨ F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 4 ∨ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 4)
  · exact F.vN4_slide hx (by linarith only [hVp]) (by linarith only [hVW]) o1.1 o1.2 hH
  by_cases o2 : (F.dep F.S.u_tP 1 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 1 < F.dep F.S.u_tP 6 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 6) ∧ (F.dep F.S.u_tP 3 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 3 < F.dep F.S.u_tP 4 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 4)
  · exact F.tP (by linarith only [hA1r]) o2.1 o2.2
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n2_2), mul_nonneg (hsp1).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos F.S.tp_pos htp1)) hal, mul_pos ((mul_pos htp1 htp1)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(sub_nonneg.2 n2_4), mul_pos F.S.tp_pos hom, mul_pos htp1 hom]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n2_2), mul_nonneg (hsp1).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos F.S.tp_pos htp1)) hal, mul_pos ((mul_pos htp1 htp1)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(sub_nonneg.2 n2_4), mul_pos F.S.tp_pos hom, mul_pos htp1 hom]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n0_2), mul_nonneg (htp1).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n0_3), mul_nonneg (htm1).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n0_4), mul_nonneg (htp1).le (sub_nonneg.2 n2_1), mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n2_1), mul_nonneg (hsp1).le (sub_nonneg.2 n2_2), mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n2_3), mul_pos htp1 hom, mul_pos F.S.sp_pos hom, mul_pos ((mul_pos htp1 htp1)) hal, mul_pos ((mul_pos htp1 htp1)) hga, mul_pos ((mul_pos F.S.hp_pos F.S.hp_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(sub_nonneg.2 n0_3), mul_pos F.S.tp_pos hom, mul_pos htp1 hom]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n0_1), mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n0_2), mul_nonneg (hsp1).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n2_1), mul_nonneg (htp1).le (sub_nonneg.2 n2_1), mul_pos hsp1 hom, mul_pos ((mul_pos htp1 htp1)) hal, mul_pos ((mul_pos htp1 htp1)) hga, mul_pos ((mul_pos F.S.hp_pos F.S.hp_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hVp).le (sub_nonneg.2 n0_3), mul_pos hVW hom, mul_nonneg hWp hom.le]

/-- 27.74 (ii): {T_A, V, T′}, h+ ≥ d+, n -/
theorem Frame20.om3n {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hVp : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm - F.S.kp*F.S.tm) (hVW : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.sp + F.S.hp*F.S.tm - F.S.hp - F.S.kp*F.S.tm + F.S.kp) (hWp : 0 ≤ -F.S.hp*F.S.sp + F.S.hp - F.S.kp) (hom : 0 < (-F.S.sm*F.S.tp + F.S.sm + F.S.tp - 1) * F.a12 + (F.S.hp*F.S.km) * F.gg) (hH : ¬ F.ClassH)   :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.dep F.S.u_tANR 0 < F.dep F.S.u_tANR 6 ∨ F.dep F.S.u_tANR 0 < F.dep F.S.u_tANR 3 ∨ F.dep F.S.u_tANR 4 < F.dep F.S.u_tANR 6 ∨ F.dep F.S.u_tANR 4 < F.dep F.S.u_tANR 3) ∧ (F.dep F.S.u_tANR 6 < F.dep F.S.u_tANR 0 ∨ F.dep F.S.u_tANR 3 < F.dep F.S.u_tANR 0 ∨ F.dep F.S.u_tANR 6 < F.dep F.S.u_tANR 4 ∨ F.dep F.S.u_tANR 3 < F.dep F.S.u_tANR 4)
  · exact F.tANR_slide hx (by linarith only [hA1r]) o0.1 o0.2 hH
  by_cases o1 : (F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 3 ∨ F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 6 ∨ F.dep F.S.u_vN4 4 < F.dep F.S.u_vN4 3 ∨ F.dep F.S.u_vN4 4 < F.dep F.S.u_vN4 6) ∧ (F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 0 ∨ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 0 ∨ F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 4 ∨ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 4)
  · exact F.vN4_slide hx (by linarith only [hVp]) (by linarith only [hVW]) o1.1 o1.2 hH
  by_cases o2 : (F.dep F.S.u_tP 1 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 1 < F.dep F.S.u_tP 6 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 6) ∧ (F.dep F.S.u_tP 3 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 3 < F.dep F.S.u_tP 4 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 4)
  · exact F.tP (by linarith only [hA1r]) o2.1 o2.2
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(sub_nonneg.2 n2_2), mul_pos ((mul_pos F.S.tp_pos htp1)) hal, mul_pos ((mul_pos htp1 htp1)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hVW).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n1_4), mul_pos hVp hom, mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sm_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hA1r).le (sub_nonneg.2 n0_3), mul_pos hA1r hom]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_1), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n2_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n2_3), mul_pos F.S.hm_pos hom, mul_pos ((mul_pos htp1 F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 F.S.hp_pos)) hga, mul_pos ((mul_pos htp1 hA1r)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg hWp (sub_nonneg.2 n0_3), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n0_2), mul_nonneg (htp1).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n2_1), mul_nonneg (htm1).le (sub_nonneg.2 n2_2), mul_nonneg (hsm1).le (sub_nonneg.2 n2_3), mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n2_4), mul_nonneg (hsm1).le (sub_nonneg.2 n2_4), mul_pos F.S.tp_pos hom, mul_pos htm1 hom, mul_pos ((mul_pos htp1 htp1)) hal, mul_pos ((mul_pos htp1 F.S.sm_pos)) hal, mul_pos ((mul_pos F.S.hp_pos F.S.hp_pos)) hde, mul_pos ((mul_pos F.S.hp_pos hA1r)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg ((mul_pos F.S.tp_pos hsp1)).le (sub_nonneg.2 n0_2), mul_nonneg ((mul_pos F.S.tp_pos htp1)).le (sub_nonneg.2 n1_1), mul_nonneg ((mul_pos htp1 htp1)).le (sub_nonneg.2 n1_1), mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.hm_pos) rp)) hde, mul_pos ((mul_pos (mul_pos F.S.tp_pos rp) rp)) hde, mul_pos ((mul_pos (mul_pos htp1 F.S.kp_pos) rp)) hde, mul_pos ((mul_pos (mul_pos htp1 rp) rp)) hde, mul_pos ((mul_pos (mul_pos F.S.tm_pos F.S.hp_pos) rp)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) rp)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos rp) hA1r)) hde, mul_pos ((mul_pos (mul_pos hsp1 rp) hA1r)) hde]

/-- 27.74 (ii): {T_A, V, T′}, h+ ≥ d+, z1 -/
theorem Frame20.om3z1 {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hVp : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm - F.S.kp*F.S.tm) (hVW : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.sp + F.S.hp*F.S.tm - F.S.hp - F.S.kp*F.S.tm + F.S.kp) (hWp : 0 ≤ -F.S.hp*F.S.sp + F.S.hp - F.S.kp) (hom1 : 0 ≤ (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) (hom2 : 0 ≤ (-F.S.sm*F.S.tp + F.S.sm + F.S.tp - 1) * F.a12 + (F.S.hp*F.S.km) * F.gg) (hl : 0 < (F.S.km*F.S.tm) * (F.a11 - F.a12) + (-F.S.hm*F.S.sm + F.S.hm + F.S.km*F.S.tm - F.S.km) * F.a12) (hH : ¬ F.ClassH)   :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.dep F.S.u_tANR 0 < F.dep F.S.u_tANR 6 ∨ F.dep F.S.u_tANR 0 < F.dep F.S.u_tANR 3 ∨ F.dep F.S.u_tANR 4 < F.dep F.S.u_tANR 6 ∨ F.dep F.S.u_tANR 4 < F.dep F.S.u_tANR 3) ∧ (F.dep F.S.u_tANR 6 < F.dep F.S.u_tANR 0 ∨ F.dep F.S.u_tANR 3 < F.dep F.S.u_tANR 0 ∨ F.dep F.S.u_tANR 6 < F.dep F.S.u_tANR 4 ∨ F.dep F.S.u_tANR 3 < F.dep F.S.u_tANR 4)
  · exact F.tANR_slide hx (by linarith only [hA1r]) o0.1 o0.2 hH
  by_cases o1 : (F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 3 ∨ F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 6 ∨ F.dep F.S.u_vN4 4 < F.dep F.S.u_vN4 3 ∨ F.dep F.S.u_vN4 4 < F.dep F.S.u_vN4 6) ∧ (F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 0 ∨ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 0 ∨ F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 4 ∨ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 4)
  · exact F.vN4_slide hx (by linarith only [hVp]) (by linarith only [hVW]) o1.1 o1.2 hH
  by_cases o2 : (F.dep F.S.u_tP 1 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 1 < F.dep F.S.u_tP 6 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 6) ∧ (F.dep F.S.u_tP 3 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 3 < F.dep F.S.u_tP 4 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 4)
  · exact F.tP (by linarith only [hA1r]) o2.1 o2.2
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n2_2), mul_nonneg (hsp1).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos F.S.tp_pos htp1)) hal, mul_pos ((mul_pos htp1 htp1)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n1_4), mul_nonneg hWp (sub_nonneg.2 n2_4), mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsp1 hA1r)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n2_4), mul_pos htp1 hl]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n0_2), mul_nonneg (hsp1).le (sub_nonneg.2 n0_2), (sub_nonneg.2 n2_1), mul_pos ((mul_pos htp1 htp1)) hal, mul_pos ((mul_pos htp1 htp1)) hga, mul_pos ((mul_pos F.S.hp_pos F.S.hp_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.km_pos).le hom1, mul_pos htp1 hl]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n2_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos htp1 hl, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsp1 hA1r)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.km_pos).le hom1, mul_pos htp1 hl]

/-- 27.74 (ii): {T_A, V, T′}, h+ ≥ d+, z2 -/
theorem Frame20.om3z2 {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hVp : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm - F.S.kp*F.S.tm) (hVW : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.sp + F.S.hp*F.S.tm - F.S.hp - F.S.kp*F.S.tm + F.S.kp) (hWp : 0 ≤ -F.S.hp*F.S.sp + F.S.hp - F.S.kp) (hom1 : 0 ≤ (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) (hom2 : 0 ≤ (-F.S.sm*F.S.tp + F.S.sm + F.S.tp - 1) * F.a12 + (F.S.hp*F.S.km) * F.gg) (hl : 0 < (-F.S.km*F.S.tm) * (F.a11 - F.a12) + (F.S.hm*F.S.sm - F.S.hm - F.S.km*F.S.tm + F.S.km) * F.a12) (hH : ¬ F.ClassH)   :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.dep F.S.u_tANR 0 < F.dep F.S.u_tANR 6 ∨ F.dep F.S.u_tANR 0 < F.dep F.S.u_tANR 3 ∨ F.dep F.S.u_tANR 4 < F.dep F.S.u_tANR 6 ∨ F.dep F.S.u_tANR 4 < F.dep F.S.u_tANR 3) ∧ (F.dep F.S.u_tANR 6 < F.dep F.S.u_tANR 0 ∨ F.dep F.S.u_tANR 3 < F.dep F.S.u_tANR 0 ∨ F.dep F.S.u_tANR 6 < F.dep F.S.u_tANR 4 ∨ F.dep F.S.u_tANR 3 < F.dep F.S.u_tANR 4)
  · exact F.tANR_slide hx (by linarith only [hA1r]) o0.1 o0.2 hH
  by_cases o1 : (F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 3 ∨ F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 6 ∨ F.dep F.S.u_vN4 4 < F.dep F.S.u_vN4 3 ∨ F.dep F.S.u_vN4 4 < F.dep F.S.u_vN4 6) ∧ (F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 0 ∨ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 0 ∨ F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 4 ∨ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 4)
  · exact F.vN4_slide hx (by linarith only [hVp]) (by linarith only [hVW]) o1.1 o1.2 hH
  by_cases o2 : (F.dep F.S.u_tP 1 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 1 < F.dep F.S.u_tP 6 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 6) ∧ (F.dep F.S.u_tP 3 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 3 < F.dep F.S.u_tP 4 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 4)
  · exact F.tP (by linarith only [hA1r]) o2.1 o2.2
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_1), mul_pos htp1 hl, mul_pos ((mul_pos htp1 F.S.km_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n1_4), mul_nonneg hWp (sub_nonneg.2 n2_4), mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos htp1 hl]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n0_2), (sub_nonneg.2 n0_4), mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n2_1), mul_nonneg (htm1).le (sub_nonneg.2 n2_3), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n2_4), mul_pos ((mul_pos htp1 F.S.tm_pos)) hal, mul_pos ((mul_pos F.S.hp_pos F.S.hp_pos)) hde, mul_pos ((mul_pos F.S.hp_pos hA1r)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg hWp (sub_nonneg.2 n0_3), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_1), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n2_2), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n2_3), mul_pos htp1 hl, mul_pos ((mul_pos htp1 F.S.km_pos)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 F.S.hp_pos)) hga, mul_pos ((mul_pos htp1 hA1r)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg ((mul_pos F.S.tp_pos hsp1)).le (sub_nonneg.2 n0_2), mul_nonneg (htp1).le (sub_nonneg.2 n1_1), mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.hm_pos) rp)) hde, mul_pos ((mul_pos (mul_pos F.S.tp_pos rp) rp)) hde, mul_pos ((mul_pos (mul_pos htp1 F.S.kp_pos) rp)) hde, mul_pos ((mul_pos (mul_pos htp1 rp) rp)) hde, mul_pos ((mul_pos (mul_pos F.S.tm_pos F.S.hp_pos) rp)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) rp)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos rp) hA1r)) hde, mul_pos ((mul_pos (mul_pos hsp1 rp) hA1r)) hde]

/-- 27.76 N4 p -/
theorem Frame20.om4ap {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1R : 0 < F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) (hVpR : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVWR : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hKb : 0 < F.S.hm + F.S.km*F.S.tm - F.S.km) (hss : 0 < F.S.sm - F.S.sp) (hnu : 0 < (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) (hHR : ¬ F.ClassHR)  :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.dep F.S.u_tP 1 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 1 < F.dep F.S.u_tP 6 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 6) ∧ (F.dep F.S.u_tP 3 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 3 < F.dep F.S.u_tP 4 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 4)
  · exact F.tP (by linarith only [hA1r]) o0.1 o0.2
  by_cases o1 : (F.rFrame.dep F.rFrame.S.u_tA 0 < F.rFrame.dep F.rFrame.S.u_tA 6 ∨ F.rFrame.dep F.rFrame.S.u_tA 0 < F.rFrame.dep F.rFrame.S.u_tA 5 ∨ F.rFrame.dep F.rFrame.S.u_tA 4 < F.rFrame.dep F.rFrame.S.u_tA 6 ∨ F.rFrame.dep F.rFrame.S.u_tA 4 < F.rFrame.dep F.rFrame.S.u_tA 5) ∧ (F.rFrame.dep F.rFrame.S.u_tA 6 < F.rFrame.dep F.rFrame.S.u_tA 0 ∨ F.rFrame.dep F.rFrame.S.u_tA 5 < F.rFrame.dep F.rFrame.S.u_tA 0 ∨ F.rFrame.dep F.rFrame.S.u_tA 6 < F.rFrame.dep F.rFrame.S.u_tA 4 ∨ F.rFrame.dep F.rFrame.S.u_tA 5 < F.rFrame.dep F.rFrame.S.u_tA 4)
  · exact rupert_of_r (F.rFrame.tA (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1R]) o1.1 o1.2)
  by_cases o2 : (F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 6 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 6) ∧ (F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 4 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 4)
  · exact rupert_of_r (F.rFrame.vN4_slide (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVpR]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVWR]) o2.1 o2.2 (fun h => hHR (F.classH_rFrame_iff.1 h)))
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga, mul_pos ((mul_pos hsm1 F.S.hm_pos)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n1_4), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos htp1 rm)) hga, mul_pos ((mul_pos hsm1 hKb)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hVpR).le (sub_nonneg.2 n0_4), mul_nonneg (hVWR).le (sub_nonneg.2 n1_4), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos htp1 rm)) hga, mul_pos ((mul_pos hsm1 hVWR)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(sub_nonneg.2 n0_3), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n1_4), hnu, mul_pos ((mul_pos htp1 F.S.tm_pos)) hal, mul_pos ((mul_pos F.S.tm_pos hsm1)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n0_1), mul_nonneg (htm1).le (sub_nonneg.2 n0_3), mul_pos F.S.sp_pos hnu, mul_pos hsm1 hnu, mul_pos hss hnu]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n2_4), mul_nonneg (htm1).le (sub_nonneg.2 n2_4), mul_pos F.S.tp_pos hnu, mul_pos htp1 hnu]

/-- 27.76 N4 n -/
theorem Frame20.om4an {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1R : 0 < F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) (hVpR : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVWR : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hKb : 0 < F.S.hm + F.S.km*F.S.tm - F.S.km) (hss : 0 < F.S.sm - F.S.sp) (hnu : 0 < (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) (hHR : ¬ F.ClassHR)  :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.dep F.S.u_tP 1 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 1 < F.dep F.S.u_tP 6 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 6) ∧ (F.dep F.S.u_tP 3 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 3 < F.dep F.S.u_tP 4 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 4)
  · exact F.tP (by linarith only [hA1r]) o0.1 o0.2
  by_cases o1 : (F.rFrame.dep F.rFrame.S.u_tA 0 < F.rFrame.dep F.rFrame.S.u_tA 6 ∨ F.rFrame.dep F.rFrame.S.u_tA 0 < F.rFrame.dep F.rFrame.S.u_tA 5 ∨ F.rFrame.dep F.rFrame.S.u_tA 4 < F.rFrame.dep F.rFrame.S.u_tA 6 ∨ F.rFrame.dep F.rFrame.S.u_tA 4 < F.rFrame.dep F.rFrame.S.u_tA 5) ∧ (F.rFrame.dep F.rFrame.S.u_tA 6 < F.rFrame.dep F.rFrame.S.u_tA 0 ∨ F.rFrame.dep F.rFrame.S.u_tA 5 < F.rFrame.dep F.rFrame.S.u_tA 0 ∨ F.rFrame.dep F.rFrame.S.u_tA 6 < F.rFrame.dep F.rFrame.S.u_tA 4 ∨ F.rFrame.dep F.rFrame.S.u_tA 5 < F.rFrame.dep F.rFrame.S.u_tA 4)
  · exact rupert_of_r (F.rFrame.tA (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1R]) o1.1 o1.2)
  by_cases o2 : (F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 6 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 6) ∧ (F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 4 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 4)
  · exact rupert_of_r (F.rFrame.vN4_slide (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVpR]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVWR]) o2.1 o2.2 (fun h => hHR (F.classH_rFrame_iff.1 h)))
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga, mul_pos ((mul_pos hsm1 F.S.hm_pos)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (htp1).le (sub_nonneg.2 n0_1), (sub_nonneg.2 n0_2), mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n0_3), mul_nonneg (htp1).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n1_3), mul_pos F.S.sp_pos hnu, mul_pos hsm1 hnu, mul_pos hss hnu, mul_pos ((mul_pos htp1 htp1)) hal, mul_pos ((mul_pos htp1 htm1)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_2), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n1_3), mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hVpR).le (sub_nonneg.2 n0_4), mul_nonneg (hVWR).le (sub_nonneg.2 n1_4), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos ((mul_pos htp1 rm)) hga, mul_pos ((mul_pos hsm1 hVWR)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (htp1).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n1_4), mul_nonneg (htp1).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.sm_pos hsm1)) hga, mul_pos ((mul_pos hsm1 hsm1)) hga, mul_pos ((mul_pos F.S.hp_pos F.S.km_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(sub_nonneg.2 n2_4), mul_pos F.S.sp_pos hnu, mul_pos hsm1 hnu, mul_pos hss hnu]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg ((mul_pos htm1 F.S.sp_pos)).le (sub_nonneg.2 n1_1), mul_nonneg ((mul_pos htm1 hss)).le (sub_nonneg.2 n1_1), mul_nonneg ((mul_pos F.S.tp_pos hsm1)).le (sub_nonneg.2 n2_2), mul_nonneg ((mul_pos htp1 hsm1)).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos (mul_pos F.S.tm_pos rm) hA1R)) hde, mul_pos ((mul_pos (mul_pos htm1 rm) hA1R)) hde, mul_pos ((mul_pos (mul_pos hsm1 F.S.kp_pos) rm)) hde, mul_pos ((mul_pos (mul_pos hsm1 F.S.km_pos) rm)) hde, mul_pos ((mul_pos (mul_pos F.S.km_pos rm) hss)) hde]

/-- 27.76 N4 z1 -/
theorem Frame20.om4az1 {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1R : 0 < F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) (hVpR : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVWR : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hKb : 0 < F.S.hm + F.S.km*F.S.tm - F.S.km) (hss : 0 < F.S.sm - F.S.sp) (hnu1 : 0 ≤ (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) (hnu2 : 0 ≤ (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) (hl : 0 < (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) + (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg) (hHR : ¬ F.ClassHR)  :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.dep F.S.u_tP 1 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 1 < F.dep F.S.u_tP 6 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 6) ∧ (F.dep F.S.u_tP 3 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 3 < F.dep F.S.u_tP 4 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 4)
  · exact F.tP (by linarith only [hA1r]) o0.1 o0.2
  by_cases o1 : (F.rFrame.dep F.rFrame.S.u_tA 0 < F.rFrame.dep F.rFrame.S.u_tA 6 ∨ F.rFrame.dep F.rFrame.S.u_tA 0 < F.rFrame.dep F.rFrame.S.u_tA 5 ∨ F.rFrame.dep F.rFrame.S.u_tA 4 < F.rFrame.dep F.rFrame.S.u_tA 6 ∨ F.rFrame.dep F.rFrame.S.u_tA 4 < F.rFrame.dep F.rFrame.S.u_tA 5) ∧ (F.rFrame.dep F.rFrame.S.u_tA 6 < F.rFrame.dep F.rFrame.S.u_tA 0 ∨ F.rFrame.dep F.rFrame.S.u_tA 5 < F.rFrame.dep F.rFrame.S.u_tA 0 ∨ F.rFrame.dep F.rFrame.S.u_tA 6 < F.rFrame.dep F.rFrame.S.u_tA 4 ∨ F.rFrame.dep F.rFrame.S.u_tA 5 < F.rFrame.dep F.rFrame.S.u_tA 4)
  · exact rupert_of_r (F.rFrame.tA (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1R]) o1.1 o1.2)
  by_cases o2 : (F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 6 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 6) ∧ (F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 4 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 4)
  · exact rupert_of_r (F.rFrame.vN4_slide (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVpR]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVWR]) o2.1 o2.2 (fun h => hHR (F.classH_rFrame_iff.1 h)))
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga, mul_pos ((mul_pos hsm1 F.S.hm_pos)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga, mul_pos ((mul_pos hsm1 F.S.hm_pos)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(sub_nonneg.2 n0_3), mul_nonneg (htm1).le (sub_nonneg.2 n0_4), (sub_nonneg.2 n1_4), (sub_nonneg.2 n2_4), mul_pos ((mul_pos htp1 F.S.tm_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hsm1)) hga, mul_pos ((mul_pos hsm1 hsm1)) hga, mul_pos ((mul_pos hsm1 hss)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_4), mul_nonneg (hVWR).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos hsm1 hVpR)) hga, mul_pos ((mul_pos hsm1 hKb)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n2_4), mul_nonneg (hsm1).le (sub_nonneg.2 n2_4), mul_nonneg (hss).le (sub_nonneg.2 n2_4), mul_pos F.S.tm_pos hl]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.sm_pos).le hnu1, mul_nonneg (hsm1).le hnu1, mul_pos F.S.tm_pos hl]

/-- 27.76 N4 z2 -/
theorem Frame20.om4az2 {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1R : 0 < F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) (hVpR : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVWR : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hKb : 0 < F.S.hm + F.S.km*F.S.tm - F.S.km) (hss : 0 < F.S.sm - F.S.sp) (hnu1 : 0 ≤ (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) (hnu2 : 0 ≤ (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) (hl : 0 < (-F.S.tm*F.S.tp + F.S.tm + F.S.tp - 1) * (F.a11 - F.a12) + (-F.S.tm*F.S.tp + F.S.tm + F.S.tp - 1) * F.a12 + (F.S.hm*F.S.hp) * F.gg) (hHR : ¬ F.ClassHR)  :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.dep F.S.u_tP 1 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 1 < F.dep F.S.u_tP 6 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 6) ∧ (F.dep F.S.u_tP 3 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 3 < F.dep F.S.u_tP 4 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 4)
  · exact F.tP (by linarith only [hA1r]) o0.1 o0.2
  by_cases o1 : (F.rFrame.dep F.rFrame.S.u_tA 0 < F.rFrame.dep F.rFrame.S.u_tA 6 ∨ F.rFrame.dep F.rFrame.S.u_tA 0 < F.rFrame.dep F.rFrame.S.u_tA 5 ∨ F.rFrame.dep F.rFrame.S.u_tA 4 < F.rFrame.dep F.rFrame.S.u_tA 6 ∨ F.rFrame.dep F.rFrame.S.u_tA 4 < F.rFrame.dep F.rFrame.S.u_tA 5) ∧ (F.rFrame.dep F.rFrame.S.u_tA 6 < F.rFrame.dep F.rFrame.S.u_tA 0 ∨ F.rFrame.dep F.rFrame.S.u_tA 5 < F.rFrame.dep F.rFrame.S.u_tA 0 ∨ F.rFrame.dep F.rFrame.S.u_tA 6 < F.rFrame.dep F.rFrame.S.u_tA 4 ∨ F.rFrame.dep F.rFrame.S.u_tA 5 < F.rFrame.dep F.rFrame.S.u_tA 4)
  · exact rupert_of_r (F.rFrame.tA (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1R]) o1.1 o1.2)
  by_cases o2 : (F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 6 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 6) ∧ (F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 4 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 4)
  · exact rupert_of_r (F.rFrame.vN4_slide (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVpR]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVWR]) o2.1 o2.2 (fun h => hHR (F.classH_rFrame_iff.1 h)))
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga, mul_pos ((mul_pos hsm1 F.S.hm_pos)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga, mul_pos ((mul_pos hsm1 F.S.hm_pos)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_4), mul_pos F.S.hm_pos hl, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos hsm1 F.S.hm_pos)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_3), mul_nonneg (hVpR).le (sub_nonneg.2 n1_4), mul_nonneg (hKb).le (sub_nonneg.2 n1_4), mul_pos hVpR hl, mul_pos hKb hl, mul_pos ((mul_pos htp1 hVWR)) hal, mul_pos ((mul_pos hsm1 hVpR)) hga, mul_pos ((mul_pos hsm1 hKb)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_1), mul_pos hVpR hl, mul_pos hKb hl]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_1), mul_pos F.S.hm_pos hl]

/-- 27.76 Rv p -/
theorem Frame20.om4bp {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1R : 0 < F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) (hVR : 0 < F.S.hm*F.S.sp + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) (hKb : 0 < F.S.hm + F.S.km*F.S.tm - F.S.km) (hnu : 0 < (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg)   :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.dep F.S.u_tP 1 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 1 < F.dep F.S.u_tP 6 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 6) ∧ (F.dep F.S.u_tP 3 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 3 < F.dep F.S.u_tP 4 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 4)
  · exact F.tP (by linarith only [hA1r]) o0.1 o0.2
  by_cases o1 : (F.rFrame.dep F.rFrame.S.u_tA 0 < F.rFrame.dep F.rFrame.S.u_tA 6 ∨ F.rFrame.dep F.rFrame.S.u_tA 0 < F.rFrame.dep F.rFrame.S.u_tA 5 ∨ F.rFrame.dep F.rFrame.S.u_tA 4 < F.rFrame.dep F.rFrame.S.u_tA 6 ∨ F.rFrame.dep F.rFrame.S.u_tA 4 < F.rFrame.dep F.rFrame.S.u_tA 5) ∧ (F.rFrame.dep F.rFrame.S.u_tA 6 < F.rFrame.dep F.rFrame.S.u_tA 0 ∨ F.rFrame.dep F.rFrame.S.u_tA 5 < F.rFrame.dep F.rFrame.S.u_tA 0 ∨ F.rFrame.dep F.rFrame.S.u_tA 6 < F.rFrame.dep F.rFrame.S.u_tA 4 ∨ F.rFrame.dep F.rFrame.S.u_tA 5 < F.rFrame.dep F.rFrame.S.u_tA 4)
  · exact rupert_of_r (F.rFrame.tA (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1R]) o1.1 o1.2)
  by_cases o2 : (F.rFrame.dep F.rFrame.S.u_vRv 0 < F.rFrame.dep F.rFrame.S.u_vRv 6 ∨ F.rFrame.dep F.rFrame.S.u_vRv 0 < F.rFrame.dep F.rFrame.S.u_vRv 5 ∨ F.rFrame.dep F.rFrame.S.u_vRv 4 < F.rFrame.dep F.rFrame.S.u_vRv 6 ∨ F.rFrame.dep F.rFrame.S.u_vRv 4 < F.rFrame.dep F.rFrame.S.u_vRv 5) ∧ (F.rFrame.dep F.rFrame.S.u_vRv 6 < F.rFrame.dep F.rFrame.S.u_vRv 0 ∨ F.rFrame.dep F.rFrame.S.u_vRv 5 < F.rFrame.dep F.rFrame.S.u_vRv 0 ∨ F.rFrame.dep F.rFrame.S.u_vRv 6 < F.rFrame.dep F.rFrame.S.u_vRv 4 ∨ F.rFrame.dep F.rFrame.S.u_vRv 5 < F.rFrame.dep F.rFrame.S.u_vRv 4)
  · exact rupert_of_r (F.rFrame.vRv (by simp only [rFrame_S, Shape20.swap]; linarith only [hKb]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVR]) o2.1 o2.2)
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos F.S.tm_pos rm)) hga, mul_pos ((mul_pos htm1 rm)) hga, mul_pos ((mul_pos hsm1 hKb)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n1_4), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos htp1 rm)) hga, mul_pos ((mul_pos hsm1 hKb)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos F.S.tm_pos rm)) hga, mul_pos ((mul_pos htm1 rm)) hga, mul_pos ((mul_pos hsm1 hKb)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n0_1), mul_nonneg (htm1).le (sub_nonneg.2 n0_3), mul_pos F.S.tm_pos hnu, mul_pos htm1 hnu]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos F.S.tp_pos rm)) hga, mul_pos ((mul_pos htp1 rm)) hga, mul_pos ((mul_pos hsm1 hKb)) hga]

/-- 27.76 Rv n -/
theorem Frame20.om4bn {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1R : 0 < F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) (hVR : 0 < F.S.hm*F.S.sp + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) (hKb : 0 < F.S.hm + F.S.km*F.S.tm - F.S.km) (hnu : 0 < (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg)   :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.dep F.S.u_tP 1 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 1 < F.dep F.S.u_tP 6 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 6) ∧ (F.dep F.S.u_tP 3 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 3 < F.dep F.S.u_tP 4 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 4)
  · exact F.tP (by linarith only [hA1r]) o0.1 o0.2
  by_cases o1 : (F.rFrame.dep F.rFrame.S.u_tA 0 < F.rFrame.dep F.rFrame.S.u_tA 6 ∨ F.rFrame.dep F.rFrame.S.u_tA 0 < F.rFrame.dep F.rFrame.S.u_tA 5 ∨ F.rFrame.dep F.rFrame.S.u_tA 4 < F.rFrame.dep F.rFrame.S.u_tA 6 ∨ F.rFrame.dep F.rFrame.S.u_tA 4 < F.rFrame.dep F.rFrame.S.u_tA 5) ∧ (F.rFrame.dep F.rFrame.S.u_tA 6 < F.rFrame.dep F.rFrame.S.u_tA 0 ∨ F.rFrame.dep F.rFrame.S.u_tA 5 < F.rFrame.dep F.rFrame.S.u_tA 0 ∨ F.rFrame.dep F.rFrame.S.u_tA 6 < F.rFrame.dep F.rFrame.S.u_tA 4 ∨ F.rFrame.dep F.rFrame.S.u_tA 5 < F.rFrame.dep F.rFrame.S.u_tA 4)
  · exact rupert_of_r (F.rFrame.tA (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1R]) o1.1 o1.2)
  by_cases o2 : (F.rFrame.dep F.rFrame.S.u_vRv 0 < F.rFrame.dep F.rFrame.S.u_vRv 6 ∨ F.rFrame.dep F.rFrame.S.u_vRv 0 < F.rFrame.dep F.rFrame.S.u_vRv 5 ∨ F.rFrame.dep F.rFrame.S.u_vRv 4 < F.rFrame.dep F.rFrame.S.u_vRv 6 ∨ F.rFrame.dep F.rFrame.S.u_vRv 4 < F.rFrame.dep F.rFrame.S.u_vRv 5) ∧ (F.rFrame.dep F.rFrame.S.u_vRv 6 < F.rFrame.dep F.rFrame.S.u_vRv 0 ∨ F.rFrame.dep F.rFrame.S.u_vRv 5 < F.rFrame.dep F.rFrame.S.u_vRv 0 ∨ F.rFrame.dep F.rFrame.S.u_vRv 6 < F.rFrame.dep F.rFrame.S.u_vRv 4 ∨ F.rFrame.dep F.rFrame.S.u_vRv 5 < F.rFrame.dep F.rFrame.S.u_vRv 4)
  · exact rupert_of_r (F.rFrame.vRv (by simp only [rFrame_S, Shape20.swap]; linarith only [hKb]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVR]) o2.1 o2.2)
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga, mul_pos ((mul_pos hsm1 F.S.hm_pos)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_nonneg (hKb).le (sub_nonneg.2 n1_3), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n1_4), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_3), mul_pos ((mul_pos htp1 rm)) hga, mul_pos ((mul_pos hsm1 hKb)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(sub_nonneg.2 n0_4), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n1_4), mul_nonneg (htm1).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.tm_pos hsm1)) hga, mul_pos ((mul_pos htm1 hsm1)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n2_3), mul_nonneg (htp1).le (sub_nonneg.2 n2_3), mul_pos F.S.sm_pos hnu, mul_pos hsm1 hnu]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n1_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos F.S.sm_pos rm)) hbe, mul_pos ((mul_pos F.S.sm_pos rm)) hga, mul_pos ((mul_pos hsm1 hKb)) hga]

/-- 27.76 Rv z1 -/
theorem Frame20.om4bz1 {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1R : 0 < F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) (hVR : 0 < F.S.hm*F.S.sp + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) (hKb : 0 < F.S.hm + F.S.km*F.S.tm - F.S.km) (hnu1 : 0 ≤ (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) (hnu2 : 0 ≤ (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) (hl : 0 < (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) + (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg)   :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.dep F.S.u_tP 1 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 1 < F.dep F.S.u_tP 6 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 6) ∧ (F.dep F.S.u_tP 3 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 3 < F.dep F.S.u_tP 4 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 4)
  · exact F.tP (by linarith only [hA1r]) o0.1 o0.2
  by_cases o1 : (F.rFrame.dep F.rFrame.S.u_tA 0 < F.rFrame.dep F.rFrame.S.u_tA 6 ∨ F.rFrame.dep F.rFrame.S.u_tA 0 < F.rFrame.dep F.rFrame.S.u_tA 5 ∨ F.rFrame.dep F.rFrame.S.u_tA 4 < F.rFrame.dep F.rFrame.S.u_tA 6 ∨ F.rFrame.dep F.rFrame.S.u_tA 4 < F.rFrame.dep F.rFrame.S.u_tA 5) ∧ (F.rFrame.dep F.rFrame.S.u_tA 6 < F.rFrame.dep F.rFrame.S.u_tA 0 ∨ F.rFrame.dep F.rFrame.S.u_tA 5 < F.rFrame.dep F.rFrame.S.u_tA 0 ∨ F.rFrame.dep F.rFrame.S.u_tA 6 < F.rFrame.dep F.rFrame.S.u_tA 4 ∨ F.rFrame.dep F.rFrame.S.u_tA 5 < F.rFrame.dep F.rFrame.S.u_tA 4)
  · exact rupert_of_r (F.rFrame.tA (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1R]) o1.1 o1.2)
  by_cases o2 : (F.rFrame.dep F.rFrame.S.u_vRv 0 < F.rFrame.dep F.rFrame.S.u_vRv 6 ∨ F.rFrame.dep F.rFrame.S.u_vRv 0 < F.rFrame.dep F.rFrame.S.u_vRv 5 ∨ F.rFrame.dep F.rFrame.S.u_vRv 4 < F.rFrame.dep F.rFrame.S.u_vRv 6 ∨ F.rFrame.dep F.rFrame.S.u_vRv 4 < F.rFrame.dep F.rFrame.S.u_vRv 5) ∧ (F.rFrame.dep F.rFrame.S.u_vRv 6 < F.rFrame.dep F.rFrame.S.u_vRv 0 ∨ F.rFrame.dep F.rFrame.S.u_vRv 5 < F.rFrame.dep F.rFrame.S.u_vRv 0 ∨ F.rFrame.dep F.rFrame.S.u_vRv 6 < F.rFrame.dep F.rFrame.S.u_vRv 4 ∨ F.rFrame.dep F.rFrame.S.u_vRv 5 < F.rFrame.dep F.rFrame.S.u_vRv 4)
  · exact rupert_of_r (F.rFrame.vRv (by simp only [rFrame_S, Shape20.swap]; linarith only [hKb]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVR]) o2.1 o2.2)
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n0_1), mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n0_2), mul_nonneg (hsm1).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n1_3), mul_nonneg (hsm1).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n2_3), mul_nonneg (hsm1).le (sub_nonneg.2 n2_3), mul_pos F.S.sp_pos hl, mul_pos hsp1 hl]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_nonneg (hKb).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos hA1r)) hal, mul_pos ((mul_pos htm1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos rm)) hga, mul_pos ((mul_pos htm1 rm)) hga, mul_pos ((mul_pos hsm1 hKb)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n0_4), mul_nonneg (hsp1).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n1_4), mul_nonneg (hsp1).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.sm_pos hsm1)) hga, mul_pos ((mul_pos hsm1 hsm1)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_nonneg (F.S.km_pos).le hnu1, mul_pos ((mul_pos F.S.tm_pos rm)) hga, mul_pos ((mul_pos htm1 rm)) hga, mul_pos ((mul_pos hsm1 hKb)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n2_3), mul_nonneg (htp1).le (sub_nonneg.2 n2_3), mul_pos F.S.tm_pos hl]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n1_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos F.S.sm_pos rm)) hbe, mul_pos ((mul_pos F.S.sm_pos rm)) hga, mul_pos ((mul_pos hsm1 hKb)) hga]

/-- 27.76 Rv z2 -/
theorem Frame20.om4bz2 {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1R : 0 < F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) (hVR : 0 < F.S.hm*F.S.sp + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) (hKb : 0 < F.S.hm + F.S.km*F.S.tm - F.S.km) (hnu1 : 0 ≤ (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) (hnu2 : 0 ≤ (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) (hl : 0 < (-F.S.tm*F.S.tp + F.S.tm + F.S.tp - 1) * (F.a11 - F.a12) + (-F.S.tm*F.S.tp + F.S.tm + F.S.tp - 1) * F.a12 + (F.S.hm*F.S.hp) * F.gg)   :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.dep F.S.u_tP 1 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 1 < F.dep F.S.u_tP 6 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 6) ∧ (F.dep F.S.u_tP 3 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 3 < F.dep F.S.u_tP 4 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 4)
  · exact F.tP (by linarith only [hA1r]) o0.1 o0.2
  by_cases o1 : (F.rFrame.dep F.rFrame.S.u_tA 0 < F.rFrame.dep F.rFrame.S.u_tA 6 ∨ F.rFrame.dep F.rFrame.S.u_tA 0 < F.rFrame.dep F.rFrame.S.u_tA 5 ∨ F.rFrame.dep F.rFrame.S.u_tA 4 < F.rFrame.dep F.rFrame.S.u_tA 6 ∨ F.rFrame.dep F.rFrame.S.u_tA 4 < F.rFrame.dep F.rFrame.S.u_tA 5) ∧ (F.rFrame.dep F.rFrame.S.u_tA 6 < F.rFrame.dep F.rFrame.S.u_tA 0 ∨ F.rFrame.dep F.rFrame.S.u_tA 5 < F.rFrame.dep F.rFrame.S.u_tA 0 ∨ F.rFrame.dep F.rFrame.S.u_tA 6 < F.rFrame.dep F.rFrame.S.u_tA 4 ∨ F.rFrame.dep F.rFrame.S.u_tA 5 < F.rFrame.dep F.rFrame.S.u_tA 4)
  · exact rupert_of_r (F.rFrame.tA (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1R]) o1.1 o1.2)
  by_cases o2 : (F.rFrame.dep F.rFrame.S.u_vRv 0 < F.rFrame.dep F.rFrame.S.u_vRv 6 ∨ F.rFrame.dep F.rFrame.S.u_vRv 0 < F.rFrame.dep F.rFrame.S.u_vRv 5 ∨ F.rFrame.dep F.rFrame.S.u_vRv 4 < F.rFrame.dep F.rFrame.S.u_vRv 6 ∨ F.rFrame.dep F.rFrame.S.u_vRv 4 < F.rFrame.dep F.rFrame.S.u_vRv 5) ∧ (F.rFrame.dep F.rFrame.S.u_vRv 6 < F.rFrame.dep F.rFrame.S.u_vRv 0 ∨ F.rFrame.dep F.rFrame.S.u_vRv 5 < F.rFrame.dep F.rFrame.S.u_vRv 0 ∨ F.rFrame.dep F.rFrame.S.u_vRv 6 < F.rFrame.dep F.rFrame.S.u_vRv 4 ∨ F.rFrame.dep F.rFrame.S.u_vRv 5 < F.rFrame.dep F.rFrame.S.u_vRv 4)
  · exact rupert_of_r (F.rFrame.vRv (by simp only [rFrame_S, Shape20.swap]; linarith only [hKb]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVR]) o2.1 o2.2)
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga, mul_pos ((mul_pos hsm1 F.S.hm_pos)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.km_pos).le hnu2, mul_pos F.S.km_pos hl, mul_pos hKb hl, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos hA1r)) hal, mul_pos ((mul_pos htm1 hA1r)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n1_4), mul_nonneg (hsm1).le (sub_nonneg.2 n1_4), mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n2_4), mul_nonneg (htp1).le (sub_nonneg.2 n2_4), hl, mul_pos F.S.tm_pos hl, mul_pos ((mul_pos F.S.tp_pos htp1)) hal, mul_pos ((mul_pos htp1 htp1)) hal, mul_pos ((mul_pos F.S.tp_pos htm1)) hga, mul_pos ((mul_pos htp1 htm1)) hga, mul_pos ((mul_pos F.S.tm_pos hsm1)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n0_1), mul_nonneg (htm1).le (sub_nonneg.2 n0_1), mul_pos F.S.sm_pos hl, mul_pos hsm1 hl]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos hKb hl, mul_pos ((mul_pos htp1 hKb)) hal, mul_pos ((mul_pos F.S.tp_pos rm)) hga, mul_pos ((mul_pos hsm1 hKb)) hga]

/-- 27.76 N4, d− < c+ p -/
theorem Frame20.om4cp {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1Rr : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVpR : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVWR : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hKb : 0 < F.S.hm + F.S.km*F.S.tm - F.S.km) (hss : 0 < F.S.sm - F.S.sp) (hnu : 0 < (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) (hHR : ¬ F.ClassHR)   :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.dep F.S.u_tP 1 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 1 < F.dep F.S.u_tP 6 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 6) ∧ (F.dep F.S.u_tP 3 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 3 < F.dep F.S.u_tP 4 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 4)
  · exact F.tP (by linarith only [hA1r]) o0.1 o0.2
  by_cases o1 : (F.rFrame.dep F.rFrame.S.u_tANR 0 < F.rFrame.dep F.rFrame.S.u_tANR 6 ∨ F.rFrame.dep F.rFrame.S.u_tANR 0 < F.rFrame.dep F.rFrame.S.u_tANR 3 ∨ F.rFrame.dep F.rFrame.S.u_tANR 4 < F.rFrame.dep F.rFrame.S.u_tANR 6 ∨ F.rFrame.dep F.rFrame.S.u_tANR 4 < F.rFrame.dep F.rFrame.S.u_tANR 3) ∧ (F.rFrame.dep F.rFrame.S.u_tANR 6 < F.rFrame.dep F.rFrame.S.u_tANR 0 ∨ F.rFrame.dep F.rFrame.S.u_tANR 3 < F.rFrame.dep F.rFrame.S.u_tANR 0 ∨ F.rFrame.dep F.rFrame.S.u_tANR 6 < F.rFrame.dep F.rFrame.S.u_tANR 4 ∨ F.rFrame.dep F.rFrame.S.u_tANR 3 < F.rFrame.dep F.rFrame.S.u_tANR 4)
  · exact rupert_of_r (F.rFrame.tANR_slide (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1Rr]) o1.1 o1.2 (fun h => hHR (F.classH_rFrame_iff.1 h)))
  by_cases o2 : (F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 6 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 6) ∧ (F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 4 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 4)
  · exact rupert_of_r (F.rFrame.vN4_slide (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVpR]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVWR]) o2.1 o2.2 (fun h => hHR (F.classH_rFrame_iff.1 h)))
  by_cases o3 : (F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 6 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 6) ∧ (F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 4 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 4)
  · exact rupert_of_r (F.rFrame.tP (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1Rr]) o3.1 o3.2)
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  simp only [not_and_or, not_or, not_lt] at o3
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2 <;>
    rcases o3 with n3 | n3
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_4), mul_nonneg (hVpR).le (sub_nonneg.2 n1_1), mul_nonneg (hKb).le (sub_nonneg.2 n1_2), mul_nonneg (hVpR).le (sub_nonneg.2 n1_4), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_2), mul_nonneg (hA1Rr).le (sub_nonneg.2 n2_2), mul_nonneg (rm).le (sub_nonneg.2 n3_1), mul_nonneg (hVWR).le (sub_nonneg.2 n3_1), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos hsm1 rm)) hbe, mul_pos ((mul_pos hsm1 hVpR)) hbe, mul_pos ((mul_pos hsm1 hKb)) hbe, mul_pos ((mul_pos rm hss)) hbe, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_2), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_nonneg (hKb).le (sub_nonneg.2 n1_2), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n1_3), mul_nonneg (hKb).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_2), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_3), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos rm hss)) hbe, mul_pos ((mul_pos rm hss)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sm_pos hA1Rr)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n1_3), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n1_3), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [(sub_nonneg.2 n0_3), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n1_3), mul_pos F.S.tm_pos hnu, mul_pos htm1 hnu, mul_pos ((mul_pos htp1 F.S.tm_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n3_1), mul_pos ((mul_pos hsm1 F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hsm1 F.S.km_pos)) hga, mul_pos ((mul_pos hsm1 hA1Rr)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n0_1), mul_nonneg (htm1).le (sub_nonneg.2 n0_3), mul_pos F.S.sm_pos hnu, mul_pos hsm1 hnu]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n3_1), mul_pos ((mul_pos hsm1 F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hsm1 F.S.km_pos)) hga, mul_pos ((mul_pos hsm1 hA1Rr)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n2_4), mul_pos hVpR hnu, mul_pos hKb hnu]

/-- 27.76 N4, d− < c+ z1 -/
theorem Frame20.om4cz1 {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1Rr : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVpR : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVWR : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hKb : 0 < F.S.hm + F.S.km*F.S.tm - F.S.km) (hss : 0 < F.S.sm - F.S.sp) (hnu1 : 0 ≤ (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) (hnu2 : 0 ≤ (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) (hl : 0 < (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) + (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg) (hHR : ¬ F.ClassHR)   :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.dep F.S.u_tP 1 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 1 < F.dep F.S.u_tP 6 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 6) ∧ (F.dep F.S.u_tP 3 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 3 < F.dep F.S.u_tP 4 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 4)
  · exact F.tP (by linarith only [hA1r]) o0.1 o0.2
  by_cases o1 : (F.rFrame.dep F.rFrame.S.u_tANR 0 < F.rFrame.dep F.rFrame.S.u_tANR 6 ∨ F.rFrame.dep F.rFrame.S.u_tANR 0 < F.rFrame.dep F.rFrame.S.u_tANR 3 ∨ F.rFrame.dep F.rFrame.S.u_tANR 4 < F.rFrame.dep F.rFrame.S.u_tANR 6 ∨ F.rFrame.dep F.rFrame.S.u_tANR 4 < F.rFrame.dep F.rFrame.S.u_tANR 3) ∧ (F.rFrame.dep F.rFrame.S.u_tANR 6 < F.rFrame.dep F.rFrame.S.u_tANR 0 ∨ F.rFrame.dep F.rFrame.S.u_tANR 3 < F.rFrame.dep F.rFrame.S.u_tANR 0 ∨ F.rFrame.dep F.rFrame.S.u_tANR 6 < F.rFrame.dep F.rFrame.S.u_tANR 4 ∨ F.rFrame.dep F.rFrame.S.u_tANR 3 < F.rFrame.dep F.rFrame.S.u_tANR 4)
  · exact rupert_of_r (F.rFrame.tANR_slide (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1Rr]) o1.1 o1.2 (fun h => hHR (F.classH_rFrame_iff.1 h)))
  by_cases o2 : (F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 6 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 6) ∧ (F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 4 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 4)
  · exact rupert_of_r (F.rFrame.vN4_slide (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVpR]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVWR]) o2.1 o2.2 (fun h => hHR (F.classH_rFrame_iff.1 h)))
  by_cases o3 : (F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 6 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 6) ∧ (F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 4 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 4)
  · exact rupert_of_r (F.rFrame.tP (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1Rr]) o3.1 o3.2)
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  simp only [not_and_or, not_or, not_lt] at o3
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2 <;>
    rcases o3 with n3 | n3
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sp_pos hA1Rr)) hbe, mul_pos ((mul_pos hsp1 hA1Rr)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sp_pos hA1Rr)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hA1Rr hss)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_nonneg (hVpR).le (sub_nonneg.2 n0_2), mul_nonneg (hVWR).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n3_4), mul_nonneg (hVpR).le (sub_nonneg.2 n3_4), mul_nonneg (F.S.km_pos).le hnu1, mul_pos F.S.km_pos hl, mul_pos hVpR hl, mul_pos hKb hl]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (hVWR).le (sub_nonneg.2 n0_3), mul_nonneg (hVWR).le (sub_nonneg.2 n1_4), mul_nonneg (hVWR).le (sub_nonneg.2 n3_1), mul_pos hVpR hl, mul_pos hKb hl, mul_pos ((mul_pos hsm1 hVWR)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n3_1), mul_pos ((mul_pos hsm1 F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hsm1 F.S.km_pos)) hga, mul_pos ((mul_pos hsm1 hA1Rr)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (hA1r).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_nonneg (hA1r).le (sub_nonneg.2 n1_3), mul_pos hA1r hl, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sm_pos hA1Rr)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [(sub_nonneg.2 n0_3), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n2_4), mul_nonneg (htp1).le (sub_nonneg.2 n2_4), mul_pos ((mul_pos htp1 F.S.tm_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos hsm1 hVpR)) hbe, mul_pos ((mul_pos hsm1 hKb)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [(sub_nonneg.2 n0_3), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.tm_pos).le hnu1, mul_nonneg (htm1).le hnu1, mul_pos ((mul_pos htp1 F.S.tm_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sp_pos hA1Rr)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hA1Rr hss)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n2_4), mul_nonneg (hsm1).le (sub_nonneg.2 n2_4), mul_nonneg (hss).le (sub_nonneg.2 n2_4), mul_pos F.S.tm_pos hl]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVpR).le (sub_nonneg.2 n1_2), mul_nonneg (hKb).le (sub_nonneg.2 n1_2), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_2), mul_nonneg (hA1Rr).le (sub_nonneg.2 n2_2), mul_nonneg (rm).le (sub_nonneg.2 n3_1), mul_nonneg (hVWR).le (sub_nonneg.2 n3_1), mul_pos ((mul_pos hsm1 rm)) hbe, mul_pos ((mul_pos hsm1 hVpR)) hbe, mul_pos ((mul_pos hsm1 hKb)) hbe, mul_pos ((mul_pos rm hss)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n1_2), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_1), mul_pos ((mul_pos rm hss)) hbe, mul_pos ((mul_pos rm hss)) hga]

/-- 27.76 N4, d− < c+ z2 -/
theorem Frame20.om4cz2 {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1Rr : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVpR : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVWR : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hKb : 0 < F.S.hm + F.S.km*F.S.tm - F.S.km) (hss : 0 < F.S.sm - F.S.sp) (hnu1 : 0 ≤ (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) (hnu2 : 0 ≤ (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) (hl : 0 < (-F.S.tm*F.S.tp + F.S.tm + F.S.tp - 1) * (F.a11 - F.a12) + (-F.S.tm*F.S.tp + F.S.tm + F.S.tp - 1) * F.a12 + (F.S.hm*F.S.hp) * F.gg) (hHR : ¬ F.ClassHR)   :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.dep F.S.u_tP 1 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 1 < F.dep F.S.u_tP 6 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 6) ∧ (F.dep F.S.u_tP 3 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 3 < F.dep F.S.u_tP 4 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 4)
  · exact F.tP (by linarith only [hA1r]) o0.1 o0.2
  by_cases o1 : (F.rFrame.dep F.rFrame.S.u_tANR 0 < F.rFrame.dep F.rFrame.S.u_tANR 6 ∨ F.rFrame.dep F.rFrame.S.u_tANR 0 < F.rFrame.dep F.rFrame.S.u_tANR 3 ∨ F.rFrame.dep F.rFrame.S.u_tANR 4 < F.rFrame.dep F.rFrame.S.u_tANR 6 ∨ F.rFrame.dep F.rFrame.S.u_tANR 4 < F.rFrame.dep F.rFrame.S.u_tANR 3) ∧ (F.rFrame.dep F.rFrame.S.u_tANR 6 < F.rFrame.dep F.rFrame.S.u_tANR 0 ∨ F.rFrame.dep F.rFrame.S.u_tANR 3 < F.rFrame.dep F.rFrame.S.u_tANR 0 ∨ F.rFrame.dep F.rFrame.S.u_tANR 6 < F.rFrame.dep F.rFrame.S.u_tANR 4 ∨ F.rFrame.dep F.rFrame.S.u_tANR 3 < F.rFrame.dep F.rFrame.S.u_tANR 4)
  · exact rupert_of_r (F.rFrame.tANR_slide (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1Rr]) o1.1 o1.2 (fun h => hHR (F.classH_rFrame_iff.1 h)))
  by_cases o2 : (F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 6 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 6) ∧ (F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 4 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 4)
  · exact rupert_of_r (F.rFrame.vN4_slide (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVpR]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVWR]) o2.1 o2.2 (fun h => hHR (F.classH_rFrame_iff.1 h)))
  by_cases o3 : (F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 6 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 6) ∧ (F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 4 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 4)
  · exact rupert_of_r (F.rFrame.tP (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1Rr]) o3.1 o3.2)
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  simp only [not_and_or, not_or, not_lt] at o3
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2 <;>
    rcases o3 with n3 | n3
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_3), mul_nonneg (hVWR).le (sub_nonneg.2 n1_3), mul_pos F.S.km_pos hl, mul_pos hVpR hl, mul_pos hKb hl, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_3), mul_nonneg (hVpR).le (sub_nonneg.2 n1_3), mul_nonneg (hKb).le (sub_nonneg.2 n1_3), mul_pos F.S.km_pos hl, mul_pos hVWR hl, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_3), mul_nonneg (hVWR).le (sub_nonneg.2 n1_3), mul_pos F.S.km_pos hl, mul_pos hVpR hl, mul_pos hKb hl, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos hA1r)) hal, mul_pos ((mul_pos htm1 hA1r)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_3), mul_pos F.S.hm_pos hl, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.tp_pos hA1Rr)) hbe, mul_pos ((mul_pos htp1 hA1Rr)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_1), mul_pos hVpR hl, mul_pos hKb hl]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n3_4), mul_nonneg (hVpR).le (sub_nonneg.2 n3_4), mul_pos F.S.km_pos hl, mul_pos hVpR hl, mul_pos hKb hl, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n0_1), mul_pos hsm1 hl, mul_pos hss hl]

/-- 27.76 N4, d− < c+, ν<0, op -/
theorem Frame20.om4cnop {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1Rr : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVpR : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVWR : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hKb : 0 < F.S.hm + F.S.km*F.S.tm - F.S.km) (hss : 0 < F.S.sm - F.S.sp) (hnu : 0 < (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) (hom : 0 < (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) (hHR : ¬ F.ClassHR)   :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.dep F.S.u_tP 1 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 1 < F.dep F.S.u_tP 6 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 6) ∧ (F.dep F.S.u_tP 3 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 3 < F.dep F.S.u_tP 4 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 4)
  · exact F.tP (by linarith only [hA1r]) o0.1 o0.2
  by_cases o1 : (F.rFrame.dep F.rFrame.S.u_tANR 0 < F.rFrame.dep F.rFrame.S.u_tANR 6 ∨ F.rFrame.dep F.rFrame.S.u_tANR 0 < F.rFrame.dep F.rFrame.S.u_tANR 3 ∨ F.rFrame.dep F.rFrame.S.u_tANR 4 < F.rFrame.dep F.rFrame.S.u_tANR 6 ∨ F.rFrame.dep F.rFrame.S.u_tANR 4 < F.rFrame.dep F.rFrame.S.u_tANR 3) ∧ (F.rFrame.dep F.rFrame.S.u_tANR 6 < F.rFrame.dep F.rFrame.S.u_tANR 0 ∨ F.rFrame.dep F.rFrame.S.u_tANR 3 < F.rFrame.dep F.rFrame.S.u_tANR 0 ∨ F.rFrame.dep F.rFrame.S.u_tANR 6 < F.rFrame.dep F.rFrame.S.u_tANR 4 ∨ F.rFrame.dep F.rFrame.S.u_tANR 3 < F.rFrame.dep F.rFrame.S.u_tANR 4)
  · exact rupert_of_r (F.rFrame.tANR_slide (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1Rr]) o1.1 o1.2 (fun h => hHR (F.classH_rFrame_iff.1 h)))
  by_cases o2 : (F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 6 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 6) ∧ (F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 4 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 4)
  · exact rupert_of_r (F.rFrame.vN4_slide (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVpR]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVWR]) o2.1 o2.2 (fun h => hHR (F.classH_rFrame_iff.1 h)))
  by_cases o3 : (F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 6 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 6) ∧ (F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 4 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 4)
  · exact rupert_of_r (F.rFrame.tP (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1Rr]) o3.1 o3.2)
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  simp only [not_and_or, not_or, not_lt] at o3
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2 <;>
    rcases o3 with n3 | n3
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_pos F.S.hm_pos hom, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_pos F.S.hm_pos hom, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_2), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n1_4), mul_nonneg (hVpR).le (sub_nonneg.2 n1_4), mul_nonneg (hKb).le (sub_nonneg.2 n1_4), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n3_1), mul_nonneg (hVWR).le (sub_nonneg.2 n3_1), mul_pos F.S.km_pos hnu, mul_pos F.S.hm_pos hom, mul_pos hVpR hom, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos hsm1 F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hVWR)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_pos F.S.hm_pos hom, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [(sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos hsm1)) hbe, mul_pos ((mul_pos hsm1 hsm1)) hbe, mul_pos ((mul_pos hsm1 hss)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n2_4), mul_pos hVpR hnu, mul_pos hKb hnu]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_4), mul_pos hVpR hom, mul_pos hKb hom]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [(sub_nonneg.2 n0_4), mul_pos F.S.tp_pos hom, mul_pos htp1 hom]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_4), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_1), mul_pos F.S.kp_pos hom, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sp_pos hA1Rr)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hA1Rr hss)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_4), mul_pos hVpR hom, mul_pos hKb hom]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n1_1), mul_nonneg (hsm1).le (sub_nonneg.2 n1_2), mul_nonneg (hsm1).le (sub_nonneg.2 n3_1), (sub_nonneg.2 n3_2), mul_pos ((mul_pos hsm1 hsm1)) hbe, mul_pos ((mul_pos hsm1 hsm1)) hga, mul_pos ((mul_pos F.S.km_pos F.S.km_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVpR).le (sub_nonneg.2 n0_4), mul_nonneg (hKb).le (sub_nonneg.2 n1_1), mul_nonneg (hKb).le (sub_nonneg.2 n1_4), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_1), mul_pos hVWR hom, mul_pos ((mul_pos rm hss)) hbe, mul_pos ((mul_pos rm hss)) hga]

/-- 27.76 N4, d− < c+, ν<0, om -/
theorem Frame20.om4cnom {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1Rr : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVpR : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVWR : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hKb : 0 < F.S.hm + F.S.km*F.S.tm - F.S.km) (hss : 0 < F.S.sm - F.S.sp) (hnu : 0 < (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) (hom : 0 < (-F.S.sm*F.S.tp + F.S.sm + F.S.tp - 1) * F.a12 + (F.S.hp*F.S.km) * F.gg) (hHR : ¬ F.ClassHR)   :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.dep F.S.u_tP 1 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 1 < F.dep F.S.u_tP 6 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 6) ∧ (F.dep F.S.u_tP 3 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 3 < F.dep F.S.u_tP 4 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 4)
  · exact F.tP (by linarith only [hA1r]) o0.1 o0.2
  by_cases o1 : (F.rFrame.dep F.rFrame.S.u_tANR 0 < F.rFrame.dep F.rFrame.S.u_tANR 6 ∨ F.rFrame.dep F.rFrame.S.u_tANR 0 < F.rFrame.dep F.rFrame.S.u_tANR 3 ∨ F.rFrame.dep F.rFrame.S.u_tANR 4 < F.rFrame.dep F.rFrame.S.u_tANR 6 ∨ F.rFrame.dep F.rFrame.S.u_tANR 4 < F.rFrame.dep F.rFrame.S.u_tANR 3) ∧ (F.rFrame.dep F.rFrame.S.u_tANR 6 < F.rFrame.dep F.rFrame.S.u_tANR 0 ∨ F.rFrame.dep F.rFrame.S.u_tANR 3 < F.rFrame.dep F.rFrame.S.u_tANR 0 ∨ F.rFrame.dep F.rFrame.S.u_tANR 6 < F.rFrame.dep F.rFrame.S.u_tANR 4 ∨ F.rFrame.dep F.rFrame.S.u_tANR 3 < F.rFrame.dep F.rFrame.S.u_tANR 4)
  · exact rupert_of_r (F.rFrame.tANR_slide (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1Rr]) o1.1 o1.2 (fun h => hHR (F.classH_rFrame_iff.1 h)))
  by_cases o2 : (F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 6 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 6) ∧ (F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 4 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 4)
  · exact rupert_of_r (F.rFrame.vN4_slide (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVpR]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVWR]) o2.1 o2.2 (fun h => hHR (F.classH_rFrame_iff.1 h)))
  by_cases o3 : (F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 6 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 6) ∧ (F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 4 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 4)
  · exact rupert_of_r (F.rFrame.tP (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1Rr]) o3.1 o3.2)
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  simp only [not_and_or, not_or, not_lt] at o3
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2 <;>
    rcases o3 with n3 | n3
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_2), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hom, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_2), mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hom, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hnu, mul_pos hKb hom, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_nonneg (hVWR).le (sub_nonneg.2 n1_4), mul_nonneg (hKb).le (sub_nonneg.2 n3_1), mul_nonneg (hVpR).le (sub_nonneg.2 n3_3), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos hsm1 hKb)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos hVpR hom, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n2_4), mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.tp_pos hnu, mul_pos htp1 hnu, mul_pos hss hnu]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sp_pos hA1Rr)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hA1Rr hss)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n1_3), mul_pos F.S.sp_pos hom, mul_pos hss hom]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n1_4), mul_nonneg (hVWR).le (sub_nonneg.2 n3_1), mul_nonneg (hVWR).le (sub_nonneg.2 n3_4), mul_pos ((mul_pos hsm1 hVpR)) hbe, mul_pos ((mul_pos hsm1 hKb)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n2_4), mul_pos hsm1 hnu, mul_pos hss hnu]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n3_1), mul_pos ((mul_pos hsm1 F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hsm1 F.S.km_pos)) hga, mul_pos ((mul_pos hsm1 hA1Rr)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n1_2), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_1), mul_pos ((mul_pos rm hss)) hbe, mul_pos ((mul_pos rm hss)) hga]

/-- 27.76 N4, d− < c+, ν<0, oz1 -/
theorem Frame20.om4cnoz1 {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1Rr : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVpR : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVWR : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hKb : 0 < F.S.hm + F.S.km*F.S.tm - F.S.km) (hss : 0 < F.S.sm - F.S.sp) (hnu : 0 < (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) (hom1 : 0 ≤ (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) (hom2 : 0 ≤ (-F.S.sm*F.S.tp + F.S.sm + F.S.tp - 1) * F.a12 + (F.S.hp*F.S.km) * F.gg) (hl2 : 0 < (F.S.hp*F.S.sp) * (F.a22 - F.a12) + (F.S.hp*F.S.sp - F.S.hp - F.S.kp*F.S.tp + F.S.kp) * F.a12) (hHR : ¬ F.ClassHR)   :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.dep F.S.u_tP 1 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 1 < F.dep F.S.u_tP 6 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 6) ∧ (F.dep F.S.u_tP 3 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 3 < F.dep F.S.u_tP 4 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 4)
  · exact F.tP (by linarith only [hA1r]) o0.1 o0.2
  by_cases o1 : (F.rFrame.dep F.rFrame.S.u_tANR 0 < F.rFrame.dep F.rFrame.S.u_tANR 6 ∨ F.rFrame.dep F.rFrame.S.u_tANR 0 < F.rFrame.dep F.rFrame.S.u_tANR 3 ∨ F.rFrame.dep F.rFrame.S.u_tANR 4 < F.rFrame.dep F.rFrame.S.u_tANR 6 ∨ F.rFrame.dep F.rFrame.S.u_tANR 4 < F.rFrame.dep F.rFrame.S.u_tANR 3) ∧ (F.rFrame.dep F.rFrame.S.u_tANR 6 < F.rFrame.dep F.rFrame.S.u_tANR 0 ∨ F.rFrame.dep F.rFrame.S.u_tANR 3 < F.rFrame.dep F.rFrame.S.u_tANR 0 ∨ F.rFrame.dep F.rFrame.S.u_tANR 6 < F.rFrame.dep F.rFrame.S.u_tANR 4 ∨ F.rFrame.dep F.rFrame.S.u_tANR 3 < F.rFrame.dep F.rFrame.S.u_tANR 4)
  · exact rupert_of_r (F.rFrame.tANR_slide (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1Rr]) o1.1 o1.2 (fun h => hHR (F.classH_rFrame_iff.1 h)))
  by_cases o2 : (F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 6 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 6) ∧ (F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 4 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 4)
  · exact rupert_of_r (F.rFrame.vN4_slide (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVpR]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVWR]) o2.1 o2.2 (fun h => hHR (F.classH_rFrame_iff.1 h)))
  by_cases o3 : (F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 6 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 6) ∧ (F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 4 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 4)
  · exact rupert_of_r (F.rFrame.tP (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1Rr]) o3.1 o3.2)
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  simp only [not_and_or, not_or, not_lt] at o3
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2 <;>
    rcases o3 with n3 | n3
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hnu, mul_nonneg (hKb).le hom2, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_2), mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hnu, mul_nonneg (F.S.km_pos).le hom2, mul_nonneg (hKb).le hom2, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_nonneg (hKb).le (sub_nonneg.2 n1_2), mul_nonneg (hKb).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_2), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_3), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos rm hss)) hbe, mul_pos ((mul_pos rm hss)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sp_pos hA1Rr)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hA1Rr hss)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [(sub_nonneg.2 n2_4), mul_pos F.S.sm_pos hnu, mul_pos hsm1 hnu]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sp_pos hA1Rr)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hA1Rr hss)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n3_3), mul_pos hsm1 hl2]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.tm_pos hA1Rr)) hbe, mul_pos ((mul_pos htm1 hA1Rr)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n2_4), mul_pos hVpR hnu, mul_pos hKb hnu]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sp_pos hA1Rr)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hA1Rr hss)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n1_2), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_1), mul_pos ((mul_pos rm hss)) hbe, mul_pos ((mul_pos rm hss)) hga]

/-- 27.76 N4, d− < c+, ν<0, oz2 -/
theorem Frame20.om4cnoz2 {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1Rr : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVpR : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVWR : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hKb : 0 < F.S.hm + F.S.km*F.S.tm - F.S.km) (hss : 0 < F.S.sm - F.S.sp) (hnu : 0 < (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) (hom1 : 0 ≤ (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) (hom2 : 0 ≤ (-F.S.sm*F.S.tp + F.S.sm + F.S.tp - 1) * F.a12 + (F.S.hp*F.S.km) * F.gg) (hl2 : 0 < (-F.S.hp*F.S.sp) * (F.a22 - F.a12) + (-F.S.hp*F.S.sp + F.S.hp + F.S.kp*F.S.tp - F.S.kp) * F.a12) (hHR : ¬ F.ClassHR)   :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.dep F.S.u_tP 1 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 1 < F.dep F.S.u_tP 6 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 6) ∧ (F.dep F.S.u_tP 3 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 3 < F.dep F.S.u_tP 4 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 4)
  · exact F.tP (by linarith only [hA1r]) o0.1 o0.2
  by_cases o1 : (F.rFrame.dep F.rFrame.S.u_tANR 0 < F.rFrame.dep F.rFrame.S.u_tANR 6 ∨ F.rFrame.dep F.rFrame.S.u_tANR 0 < F.rFrame.dep F.rFrame.S.u_tANR 3 ∨ F.rFrame.dep F.rFrame.S.u_tANR 4 < F.rFrame.dep F.rFrame.S.u_tANR 6 ∨ F.rFrame.dep F.rFrame.S.u_tANR 4 < F.rFrame.dep F.rFrame.S.u_tANR 3) ∧ (F.rFrame.dep F.rFrame.S.u_tANR 6 < F.rFrame.dep F.rFrame.S.u_tANR 0 ∨ F.rFrame.dep F.rFrame.S.u_tANR 3 < F.rFrame.dep F.rFrame.S.u_tANR 0 ∨ F.rFrame.dep F.rFrame.S.u_tANR 6 < F.rFrame.dep F.rFrame.S.u_tANR 4 ∨ F.rFrame.dep F.rFrame.S.u_tANR 3 < F.rFrame.dep F.rFrame.S.u_tANR 4)
  · exact rupert_of_r (F.rFrame.tANR_slide (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1Rr]) o1.1 o1.2 (fun h => hHR (F.classH_rFrame_iff.1 h)))
  by_cases o2 : (F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 6 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 6) ∧ (F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 4 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 4)
  · exact rupert_of_r (F.rFrame.vN4_slide (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVpR]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVWR]) o2.1 o2.2 (fun h => hHR (F.classH_rFrame_iff.1 h)))
  by_cases o3 : (F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 6 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 6) ∧ (F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 4 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 4)
  · exact rupert_of_r (F.rFrame.tP (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1Rr]) o3.1 o3.2)
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  simp only [not_and_or, not_or, not_lt] at o3
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2 <;>
    rcases o3 with n3 | n3
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hnu, mul_nonneg (hKb).le hom2, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_2), mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hnu, mul_nonneg (F.S.km_pos).le hom2, mul_nonneg (hKb).le hom2, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_nonneg (hKb).le (sub_nonneg.2 n3_4), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_nonneg (hKb).le (sub_nonneg.2 n1_2), mul_nonneg (hKb).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_2), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_3), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos rm hss)) hbe, mul_pos ((mul_pos rm hss)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sp_pos hA1Rr)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hA1Rr hss)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n2_4), mul_pos hsm1 hnu, mul_pos hss hnu]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sp_pos hA1Rr)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hA1Rr hss)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n1_4), mul_pos hsm1 hl2]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n3_1), mul_pos ((mul_pos hsm1 F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hsm1 F.S.km_pos)) hga, mul_pos ((mul_pos hsm1 hA1Rr)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n2_4), mul_nonneg (htp1).le (sub_nonneg.2 n2_4), mul_pos F.S.sp_pos hnu, mul_pos hsm1 hnu, mul_pos hss hnu]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sp_pos hA1Rr)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hA1Rr hss)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n1_2), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_1), mul_pos ((mul_pos rm hss)) hbe, mul_pos ((mul_pos rm hss)) hga]

/-- 27.76 Rv, d− < c+ p -/
theorem Frame20.om4dp {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1Rr : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVR : 0 < F.S.hm*F.S.sp + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) (hKb : 0 < F.S.hm + F.S.km*F.S.tm - F.S.km) (hnu : 0 < (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) (hHR : ¬ F.ClassHR)  :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.dep F.S.u_tP 1 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 1 < F.dep F.S.u_tP 6 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 6) ∧ (F.dep F.S.u_tP 3 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 3 < F.dep F.S.u_tP 4 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 4)
  · exact F.tP (by linarith only [hA1r]) o0.1 o0.2
  by_cases o1 : (F.rFrame.dep F.rFrame.S.u_tANR 0 < F.rFrame.dep F.rFrame.S.u_tANR 6 ∨ F.rFrame.dep F.rFrame.S.u_tANR 0 < F.rFrame.dep F.rFrame.S.u_tANR 3 ∨ F.rFrame.dep F.rFrame.S.u_tANR 4 < F.rFrame.dep F.rFrame.S.u_tANR 6 ∨ F.rFrame.dep F.rFrame.S.u_tANR 4 < F.rFrame.dep F.rFrame.S.u_tANR 3) ∧ (F.rFrame.dep F.rFrame.S.u_tANR 6 < F.rFrame.dep F.rFrame.S.u_tANR 0 ∨ F.rFrame.dep F.rFrame.S.u_tANR 3 < F.rFrame.dep F.rFrame.S.u_tANR 0 ∨ F.rFrame.dep F.rFrame.S.u_tANR 6 < F.rFrame.dep F.rFrame.S.u_tANR 4 ∨ F.rFrame.dep F.rFrame.S.u_tANR 3 < F.rFrame.dep F.rFrame.S.u_tANR 4)
  · exact rupert_of_r (F.rFrame.tANR_slide (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1Rr]) o1.1 o1.2 (fun h => hHR (F.classH_rFrame_iff.1 h)))
  by_cases o2 : (F.rFrame.dep F.rFrame.S.u_vRv 0 < F.rFrame.dep F.rFrame.S.u_vRv 6 ∨ F.rFrame.dep F.rFrame.S.u_vRv 0 < F.rFrame.dep F.rFrame.S.u_vRv 5 ∨ F.rFrame.dep F.rFrame.S.u_vRv 4 < F.rFrame.dep F.rFrame.S.u_vRv 6 ∨ F.rFrame.dep F.rFrame.S.u_vRv 4 < F.rFrame.dep F.rFrame.S.u_vRv 5) ∧ (F.rFrame.dep F.rFrame.S.u_vRv 6 < F.rFrame.dep F.rFrame.S.u_vRv 0 ∨ F.rFrame.dep F.rFrame.S.u_vRv 5 < F.rFrame.dep F.rFrame.S.u_vRv 0 ∨ F.rFrame.dep F.rFrame.S.u_vRv 6 < F.rFrame.dep F.rFrame.S.u_vRv 4 ∨ F.rFrame.dep F.rFrame.S.u_vRv 5 < F.rFrame.dep F.rFrame.S.u_vRv 4)
  · exact rupert_of_r (F.rFrame.vRv (by simp only [rFrame_S, Shape20.swap]; linarith only [hKb]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVR]) o2.1 o2.2)
  by_cases o3 : (F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 6 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 6) ∧ (F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 4 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 4)
  · exact rupert_of_r (F.rFrame.tP (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1Rr]) o3.1 o3.2)
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  simp only [not_and_or, not_or, not_lt] at o3
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2 <;>
    rcases o3 with n3 | n3
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, mul_pos ((mul_pos hA1Rr hKb)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos F.S.tm_pos rm)) hga, mul_pos ((mul_pos htm1 rm)) hga, mul_pos ((mul_pos hsm1 hKb)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos F.S.tp_pos rm)) hga, mul_pos ((mul_pos htp1 rm)) hga, mul_pos ((mul_pos hsm1 hKb)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n3_1), mul_pos ((mul_pos hsm1 F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hsm1 F.S.km_pos)) hga, mul_pos ((mul_pos hsm1 hA1Rr)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n3_1), mul_pos ((mul_pos hsm1 F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hsm1 F.S.km_pos)) hga, mul_pos ((mul_pos hsm1 hA1Rr)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, mul_pos ((mul_pos hA1Rr hKb)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, mul_pos ((mul_pos hA1Rr hKb)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos F.S.tm_pos rm)) hga, mul_pos ((mul_pos htm1 rm)) hga, mul_pos ((mul_pos hsm1 hKb)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos F.S.tm_pos rm)) hga, mul_pos ((mul_pos htm1 rm)) hga, mul_pos ((mul_pos hsm1 hKb)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, mul_pos ((mul_pos hA1Rr hKb)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, mul_pos ((mul_pos hA1Rr hKb)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n1_2), mul_nonneg (rm).le (sub_nonneg.2 n1_4), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_nonneg (rm).le (sub_nonneg.2 n3_1), mul_nonneg (hKb).le (sub_nonneg.2 n3_1), mul_nonneg (rm).le (sub_nonneg.2 n3_4), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos F.S.tp_pos rm)) hbe, mul_pos ((mul_pos htp1 rm)) hbe, mul_pos ((mul_pos hsm1 hKb)) hbe, mul_pos ((mul_pos F.S.sm_pos rm)) hga, mul_pos ((mul_pos hsm1 hKb)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n1_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos F.S.sm_pos rm)) hbe, mul_pos ((mul_pos F.S.sm_pos rm)) hga, mul_pos ((mul_pos hsm1 hKb)) hga]

/-- 27.76 Rv, d− < c+ n -/
theorem Frame20.om4dn {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1Rr : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVR : 0 < F.S.hm*F.S.sp + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) (hKb : 0 < F.S.hm + F.S.km*F.S.tm - F.S.km) (hnu : 0 < (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) (hHR : ¬ F.ClassHR)  :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.dep F.S.u_tP 1 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 1 < F.dep F.S.u_tP 6 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 6) ∧ (F.dep F.S.u_tP 3 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 3 < F.dep F.S.u_tP 4 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 4)
  · exact F.tP (by linarith only [hA1r]) o0.1 o0.2
  by_cases o1 : (F.rFrame.dep F.rFrame.S.u_tANR 0 < F.rFrame.dep F.rFrame.S.u_tANR 6 ∨ F.rFrame.dep F.rFrame.S.u_tANR 0 < F.rFrame.dep F.rFrame.S.u_tANR 3 ∨ F.rFrame.dep F.rFrame.S.u_tANR 4 < F.rFrame.dep F.rFrame.S.u_tANR 6 ∨ F.rFrame.dep F.rFrame.S.u_tANR 4 < F.rFrame.dep F.rFrame.S.u_tANR 3) ∧ (F.rFrame.dep F.rFrame.S.u_tANR 6 < F.rFrame.dep F.rFrame.S.u_tANR 0 ∨ F.rFrame.dep F.rFrame.S.u_tANR 3 < F.rFrame.dep F.rFrame.S.u_tANR 0 ∨ F.rFrame.dep F.rFrame.S.u_tANR 6 < F.rFrame.dep F.rFrame.S.u_tANR 4 ∨ F.rFrame.dep F.rFrame.S.u_tANR 3 < F.rFrame.dep F.rFrame.S.u_tANR 4)
  · exact rupert_of_r (F.rFrame.tANR_slide (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1Rr]) o1.1 o1.2 (fun h => hHR (F.classH_rFrame_iff.1 h)))
  by_cases o2 : (F.rFrame.dep F.rFrame.S.u_vRv 0 < F.rFrame.dep F.rFrame.S.u_vRv 6 ∨ F.rFrame.dep F.rFrame.S.u_vRv 0 < F.rFrame.dep F.rFrame.S.u_vRv 5 ∨ F.rFrame.dep F.rFrame.S.u_vRv 4 < F.rFrame.dep F.rFrame.S.u_vRv 6 ∨ F.rFrame.dep F.rFrame.S.u_vRv 4 < F.rFrame.dep F.rFrame.S.u_vRv 5) ∧ (F.rFrame.dep F.rFrame.S.u_vRv 6 < F.rFrame.dep F.rFrame.S.u_vRv 0 ∨ F.rFrame.dep F.rFrame.S.u_vRv 5 < F.rFrame.dep F.rFrame.S.u_vRv 0 ∨ F.rFrame.dep F.rFrame.S.u_vRv 6 < F.rFrame.dep F.rFrame.S.u_vRv 4 ∨ F.rFrame.dep F.rFrame.S.u_vRv 5 < F.rFrame.dep F.rFrame.S.u_vRv 4)
  · exact rupert_of_r (F.rFrame.vRv (by simp only [rFrame_S, Shape20.swap]; linarith only [hKb]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVR]) o2.1 o2.2)
  by_cases o3 : (F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 6 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 6) ∧ (F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 4 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 4)
  · exact rupert_of_r (F.rFrame.tP (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1Rr]) o3.1 o3.2)
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  simp only [not_and_or, not_or, not_lt] at o3
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2 <;>
    rcases o3 with n3 | n3
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, mul_pos ((mul_pos hA1Rr hKb)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_2), mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n3_4), mul_nonneg (hKb).le (sub_nonneg.2 n3_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos rm)) hga, mul_pos ((mul_pos htm1 rm)) hga, mul_pos ((mul_pos hsm1 hKb)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_nonneg (hKb).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos ((mul_pos htp1 F.S.hm_pos)) hal, mul_pos ((mul_pos F.S.sp_pos rm)) hga, mul_pos ((mul_pos hsp1 rm)) hga, mul_pos ((mul_pos hsm1 hKb)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, mul_pos ((mul_pos hA1Rr hKb)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.tp_pos hA1Rr)) hbe, mul_pos ((mul_pos htp1 hA1Rr)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hA1Rr).le (sub_nonneg.2 n2_4), mul_pos hA1Rr hnu, mul_pos ((mul_pos F.S.sp_pos rm)) hga, mul_pos ((mul_pos hsm1 hVR)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, mul_pos ((mul_pos hA1Rr hKb)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, mul_pos ((mul_pos hA1Rr hKb)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hA1Rr).le (sub_nonneg.2 n2_4), mul_pos hA1Rr hnu, mul_pos ((mul_pos F.S.sp_pos rm)) hga, mul_pos ((mul_pos hsm1 hVR)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [(sub_nonneg.2 n2_3), mul_pos F.S.sp_pos hnu, mul_pos hsp1 hnu]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n1_2), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_2), mul_nonneg (hKb).le (sub_nonneg.2 n3_1), mul_pos ((mul_pos F.S.sm_pos rm)) hbe, mul_pos ((mul_pos hsm1 hKb)) hbe, mul_pos ((mul_pos F.S.sm_pos rm)) hga, mul_pos ((mul_pos hsm1 hKb)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, mul_pos ((mul_pos hA1Rr hKb)) hal]

/-- 27.76 Rv, d− < c+ z1 -/
theorem Frame20.om4dz1 {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1Rr : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVR : 0 < F.S.hm*F.S.sp + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) (hKb : 0 < F.S.hm + F.S.km*F.S.tm - F.S.km) (hnu1 : 0 ≤ (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) (hnu2 : 0 ≤ (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) (hl : 0 < (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) + (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg) (hHR : ¬ F.ClassHR)  :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.dep F.S.u_tP 1 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 1 < F.dep F.S.u_tP 6 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 6) ∧ (F.dep F.S.u_tP 3 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 3 < F.dep F.S.u_tP 4 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 4)
  · exact F.tP (by linarith only [hA1r]) o0.1 o0.2
  by_cases o1 : (F.rFrame.dep F.rFrame.S.u_tANR 0 < F.rFrame.dep F.rFrame.S.u_tANR 6 ∨ F.rFrame.dep F.rFrame.S.u_tANR 0 < F.rFrame.dep F.rFrame.S.u_tANR 3 ∨ F.rFrame.dep F.rFrame.S.u_tANR 4 < F.rFrame.dep F.rFrame.S.u_tANR 6 ∨ F.rFrame.dep F.rFrame.S.u_tANR 4 < F.rFrame.dep F.rFrame.S.u_tANR 3) ∧ (F.rFrame.dep F.rFrame.S.u_tANR 6 < F.rFrame.dep F.rFrame.S.u_tANR 0 ∨ F.rFrame.dep F.rFrame.S.u_tANR 3 < F.rFrame.dep F.rFrame.S.u_tANR 0 ∨ F.rFrame.dep F.rFrame.S.u_tANR 6 < F.rFrame.dep F.rFrame.S.u_tANR 4 ∨ F.rFrame.dep F.rFrame.S.u_tANR 3 < F.rFrame.dep F.rFrame.S.u_tANR 4)
  · exact rupert_of_r (F.rFrame.tANR_slide (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1Rr]) o1.1 o1.2 (fun h => hHR (F.classH_rFrame_iff.1 h)))
  by_cases o2 : (F.rFrame.dep F.rFrame.S.u_vRv 0 < F.rFrame.dep F.rFrame.S.u_vRv 6 ∨ F.rFrame.dep F.rFrame.S.u_vRv 0 < F.rFrame.dep F.rFrame.S.u_vRv 5 ∨ F.rFrame.dep F.rFrame.S.u_vRv 4 < F.rFrame.dep F.rFrame.S.u_vRv 6 ∨ F.rFrame.dep F.rFrame.S.u_vRv 4 < F.rFrame.dep F.rFrame.S.u_vRv 5) ∧ (F.rFrame.dep F.rFrame.S.u_vRv 6 < F.rFrame.dep F.rFrame.S.u_vRv 0 ∨ F.rFrame.dep F.rFrame.S.u_vRv 5 < F.rFrame.dep F.rFrame.S.u_vRv 0 ∨ F.rFrame.dep F.rFrame.S.u_vRv 6 < F.rFrame.dep F.rFrame.S.u_vRv 4 ∨ F.rFrame.dep F.rFrame.S.u_vRv 5 < F.rFrame.dep F.rFrame.S.u_vRv 4)
  · exact rupert_of_r (F.rFrame.vRv (by simp only [rFrame_S, Shape20.swap]; linarith only [hKb]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVR]) o2.1 o2.2)
  by_cases o3 : (F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 6 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 6) ∧ (F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 4 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 4)
  · exact rupert_of_r (F.rFrame.tP (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1Rr]) o3.1 o3.2)
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  simp only [not_and_or, not_or, not_lt] at o3
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2 <;>
    rcases o3 with n3 | n3
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (hA1r).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_nonneg (hA1r).le (sub_nonneg.2 n3_4), mul_pos hA1r hl, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (hA1r).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_nonneg (hA1r).le (sub_nonneg.2 n3_4), mul_nonneg (hKb).le (sub_nonneg.2 n3_4), mul_pos hA1r hl, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos rm)) hga, mul_pos ((mul_pos htm1 rm)) hga, mul_pos ((mul_pos hsm1 hKb)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, mul_pos ((mul_pos hA1Rr hKb)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, mul_pos ((mul_pos hA1Rr hKb)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_nonneg (rm).le (sub_nonneg.2 n0_2), mul_nonneg (rm).le (sub_nonneg.2 n0_3), mul_nonneg (hKb).le (sub_nonneg.2 n1_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_4), mul_nonneg (rm).le (sub_nonneg.2 n1_4), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n3_1), mul_nonneg (rm).le (sub_nonneg.2 n3_1), mul_nonneg (hKb).le (sub_nonneg.2 n3_3), mul_nonneg (F.S.km_pos).le hnu1, mul_pos F.S.km_pos hl, mul_pos rm hl, mul_pos ((mul_pos htp1 hKb)) hal, mul_pos ((mul_pos F.S.tp_pos rm)) hbe, mul_pos ((mul_pos htp1 rm)) hbe, mul_pos ((mul_pos hsm1 F.S.hm_pos)) hbe, mul_pos ((mul_pos F.S.sm_pos rm)) hga, mul_pos ((mul_pos hsm1 hKb)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_nonneg (hA1r).le (sub_nonneg.2 n0_3), mul_nonneg (hA1r).le (sub_nonneg.2 n1_3), mul_pos hA1r hl, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.tm_pos hA1Rr)) hbe, mul_pos ((mul_pos htm1 hA1Rr)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, mul_pos ((mul_pos hA1Rr hKb)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, mul_pos ((mul_pos hA1Rr hKb)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, mul_pos ((mul_pos hA1Rr hKb)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, mul_pos ((mul_pos hA1Rr hKb)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, mul_pos ((mul_pos hA1Rr hKb)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n1_2), mul_nonneg (rm).le (sub_nonneg.2 n1_4), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_2), mul_nonneg (rm).le (sub_nonneg.2 n3_1), mul_nonneg (hKb).le (sub_nonneg.2 n3_1), mul_nonneg (rm).le (sub_nonneg.2 n3_4), mul_pos ((mul_pos F.S.tp_pos rm)) hbe, mul_pos ((mul_pos htp1 rm)) hbe, mul_pos ((mul_pos hsm1 hKb)) hbe, mul_pos ((mul_pos F.S.sm_pos rm)) hga, mul_pos ((mul_pos hsm1 hKb)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, mul_pos ((mul_pos hA1Rr hKb)) hal]

/-- 27.76 Rv, d− < c+ z2 -/
theorem Frame20.om4dz2 {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1Rr : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVR : 0 < F.S.hm*F.S.sp + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) (hKb : 0 < F.S.hm + F.S.km*F.S.tm - F.S.km) (hnu1 : 0 ≤ (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) (hnu2 : 0 ≤ (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) (hl : 0 < (-F.S.tm*F.S.tp + F.S.tm + F.S.tp - 1) * (F.a11 - F.a12) + (-F.S.tm*F.S.tp + F.S.tm + F.S.tp - 1) * F.a12 + (F.S.hm*F.S.hp) * F.gg) (hHR : ¬ F.ClassHR)  :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.dep F.S.u_tP 1 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 1 < F.dep F.S.u_tP 6 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 6) ∧ (F.dep F.S.u_tP 3 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 3 < F.dep F.S.u_tP 4 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 4)
  · exact F.tP (by linarith only [hA1r]) o0.1 o0.2
  by_cases o1 : (F.rFrame.dep F.rFrame.S.u_tANR 0 < F.rFrame.dep F.rFrame.S.u_tANR 6 ∨ F.rFrame.dep F.rFrame.S.u_tANR 0 < F.rFrame.dep F.rFrame.S.u_tANR 3 ∨ F.rFrame.dep F.rFrame.S.u_tANR 4 < F.rFrame.dep F.rFrame.S.u_tANR 6 ∨ F.rFrame.dep F.rFrame.S.u_tANR 4 < F.rFrame.dep F.rFrame.S.u_tANR 3) ∧ (F.rFrame.dep F.rFrame.S.u_tANR 6 < F.rFrame.dep F.rFrame.S.u_tANR 0 ∨ F.rFrame.dep F.rFrame.S.u_tANR 3 < F.rFrame.dep F.rFrame.S.u_tANR 0 ∨ F.rFrame.dep F.rFrame.S.u_tANR 6 < F.rFrame.dep F.rFrame.S.u_tANR 4 ∨ F.rFrame.dep F.rFrame.S.u_tANR 3 < F.rFrame.dep F.rFrame.S.u_tANR 4)
  · exact rupert_of_r (F.rFrame.tANR_slide (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1Rr]) o1.1 o1.2 (fun h => hHR (F.classH_rFrame_iff.1 h)))
  by_cases o2 : (F.rFrame.dep F.rFrame.S.u_vRv 0 < F.rFrame.dep F.rFrame.S.u_vRv 6 ∨ F.rFrame.dep F.rFrame.S.u_vRv 0 < F.rFrame.dep F.rFrame.S.u_vRv 5 ∨ F.rFrame.dep F.rFrame.S.u_vRv 4 < F.rFrame.dep F.rFrame.S.u_vRv 6 ∨ F.rFrame.dep F.rFrame.S.u_vRv 4 < F.rFrame.dep F.rFrame.S.u_vRv 5) ∧ (F.rFrame.dep F.rFrame.S.u_vRv 6 < F.rFrame.dep F.rFrame.S.u_vRv 0 ∨ F.rFrame.dep F.rFrame.S.u_vRv 5 < F.rFrame.dep F.rFrame.S.u_vRv 0 ∨ F.rFrame.dep F.rFrame.S.u_vRv 6 < F.rFrame.dep F.rFrame.S.u_vRv 4 ∨ F.rFrame.dep F.rFrame.S.u_vRv 5 < F.rFrame.dep F.rFrame.S.u_vRv 4)
  · exact rupert_of_r (F.rFrame.vRv (by simp only [rFrame_S, Shape20.swap]; linarith only [hKb]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVR]) o2.1 o2.2)
  by_cases o3 : (F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 6 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 6) ∧ (F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 4 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 4)
  · exact rupert_of_r (F.rFrame.tP (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1Rr]) o3.1 o3.2)
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  simp only [not_and_or, not_or, not_lt] at o3
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2 <;>
    rcases o3 with n3 | n3
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, mul_pos ((mul_pos hA1Rr hKb)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, mul_pos ((mul_pos hA1Rr hKb)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_nonneg (F.S.km_pos).le hnu1, mul_pos ((mul_pos F.S.tm_pos rm)) hga, mul_pos ((mul_pos htm1 rm)) hga, mul_pos ((mul_pos hsm1 hKb)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, mul_pos ((mul_pos hA1Rr hKb)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_nonneg (hKb).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos rm)) hga, mul_pos ((mul_pos htm1 rm)) hga, mul_pos ((mul_pos hsm1 hKb)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_3), mul_pos F.S.hm_pos hl, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, mul_pos ((mul_pos hA1Rr hKb)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, mul_pos ((mul_pos hA1Rr hKb)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.km_pos hl, mul_pos hKb hl, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos hA1r)) hal, mul_pos ((mul_pos htm1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos rm)) hga, mul_pos ((mul_pos htm1 rm)) hga, mul_pos ((mul_pos hsm1 hKb)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, mul_pos ((mul_pos hA1Rr hKb)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, mul_pos ((mul_pos hA1Rr hKb)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n3_3), mul_nonneg (F.S.km_pos).le hnu1, mul_pos F.S.hm_pos hl, mul_pos ((mul_pos htp1 F.S.km_pos)) hal, mul_pos ((mul_pos htp1 hKb)) hal, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos F.S.tp_pos rm)) hga, mul_pos ((mul_pos hsm1 F.S.km_pos)) hga, mul_pos ((mul_pos hsm1 hA1Rr)) hga, mul_pos ((mul_pos hsm1 hKb)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, mul_pos ((mul_pos hA1Rr hKb)) hal]

/-- family A, T1 (⟨u1,u2⟩ > 0) -/
theorem Frame20.famA1 {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1 : 0 < F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) (hA2 : 0 < F.S.hm*F.S.sm*F.S.tp + F.S.hp*F.S.sm*F.S.tm - F.S.km*F.S.tm) (hA3 : 0 < -F.S.hm*F.S.sm*F.S.tp + F.S.hm - F.S.hp*F.S.sm*F.S.tm + F.S.hp*F.S.sm + F.S.km*F.S.tm - F.S.km) (hg : 0 < (F.S.tp^2 - F.S.tp) * (F.a11 - F.a12) + (F.S.tp^2 - 2*F.S.tp + 1) * F.a12 + (F.S.hp^2) * F.gg)   :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.dep F.S.u_tA 0 < F.dep F.S.u_tA 6 ∨ F.dep F.S.u_tA 0 < F.dep F.S.u_tA 5 ∨ F.dep F.S.u_tA 4 < F.dep F.S.u_tA 6 ∨ F.dep F.S.u_tA 4 < F.dep F.S.u_tA 5) ∧ (F.dep F.S.u_tA 6 < F.dep F.S.u_tA 0 ∨ F.dep F.S.u_tA 5 < F.dep F.S.u_tA 0 ∨ F.dep F.S.u_tA 6 < F.dep F.S.u_tA 4 ∨ F.dep F.S.u_tA 5 < F.dep F.S.u_tA 4)
  · exact F.tA (by linarith only [hA1]) o0.1 o0.2
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  rcases o0 with n0 | n0
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tA] at n0_1 n0_2 n0_3 n0_4
    linarith only [mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n0_3), mul_nonneg (hsm1).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.hp_pos F.S.km_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tA] at n0_1 n0_2 n0_3 n0_4
    linarith only [mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hsp1).le (sub_nonneg.2 n0_1), mul_pos F.S.tm_pos hg, mul_pos htm1 hg]

/-- family A, T2 (⟨u1,u2⟩ ≤ 0) -/
theorem Frame20.famA2 {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1 : 0 < F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) (hA2 : 0 < F.S.hm*F.S.sm*F.S.tp + F.S.hp*F.S.sm*F.S.tm - F.S.km*F.S.tm) (hA3 : 0 < -F.S.hm*F.S.sm*F.S.tp + F.S.hm - F.S.hp*F.S.sm*F.S.tm + F.S.hp*F.S.sm + F.S.km*F.S.tm - F.S.km) (hg : 0 ≤ (-F.S.tp^2 + F.S.tp) * (F.a11 - F.a12) + (-F.S.tp^2 + 2*F.S.tp - 1) * F.a12 + (-F.S.hp^2) * F.gg)   :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.dep F.S.u_yT2 1 < F.dep F.S.u_yT2 3 ∨ F.dep F.S.u_yT2 1 < F.dep F.S.u_yT2 0 ∨ F.dep F.S.u_yT2 2 < F.dep F.S.u_yT2 0 ∨ F.dep F.S.u_yT2 2 < F.dep F.S.u_yT2 5) ∧ (F.dep F.S.u_yT2 0 < F.dep F.S.u_yT2 1 ∨ F.dep F.S.u_yT2 0 < F.dep F.S.u_yT2 2 ∨ F.dep F.S.u_yT2 5 < F.dep F.S.u_yT2 2 ∨ F.dep F.S.u_yT2 5 < F.dep F.S.u_yT2 3) ∧ (F.dep F.S.u_yT2 2 < F.dep F.S.u_yT2 0 ∨ F.dep F.S.u_yT2 2 < F.dep F.S.u_yT2 5 ∨ F.dep F.S.u_yT2 3 < F.dep F.S.u_yT2 5 ∨ F.dep F.S.u_yT2 3 < F.dep F.S.u_yT2 1) ∧ (F.dep F.S.u_yT2 5 < F.dep F.S.u_yT2 2 ∨ F.dep F.S.u_yT2 5 < F.dep F.S.u_yT2 3 ∨ F.dep F.S.u_yT2 1 < F.dep F.S.u_yT2 3 ∨ F.dep F.S.u_yT2 1 < F.dep F.S.u_yT2 0) ∧ (F.dep F.S.u_yT2 3 < F.dep F.S.u_yT2 5 ∨ F.dep F.S.u_yT2 3 < F.dep F.S.u_yT2 1 ∨ F.dep F.S.u_yT2 0 < F.dep F.S.u_yT2 1 ∨ F.dep F.S.u_yT2 0 < F.dep F.S.u_yT2 2)
  · exact F.yT2 (by linarith only [hA2]) (by linarith only [hA3]) o0.1 o0.2.1 o0.2.2.1 o0.2.2.2.1 o0.2.2.2.2
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  rcases o0 with n0 | n0 | n0 | n0 | n0
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_yT2] at n0_1 n0_2 n0_3 n0_4
    linarith only [mul_nonneg ((mul_pos F.S.tp_pos F.S.tm_pos)).le (sub_nonneg.2 n0_2), mul_nonneg ((mul_pos F.S.tp_pos htm1)).le (sub_nonneg.2 n0_2), mul_nonneg (htp1).le (sub_nonneg.2 n0_3), mul_pos ((mul_pos (mul_pos htp1 F.S.tm_pos) F.S.sp_pos)) hbe, mul_pos ((mul_pos (mul_pos htp1 htm1) F.S.sp_pos)) hbe, mul_pos ((mul_pos (mul_pos htp1 htp1) F.S.sp_pos)) hga, mul_pos ((mul_pos (mul_pos F.S.tm_pos F.S.hp_pos) rp)) hde, mul_pos ((mul_pos (mul_pos htm1 F.S.hp_pos) rp)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) F.S.hp_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_yT2] at n0_1 n0_2 n0_3 n0_4
    linarith only [mul_nonneg (htp1).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.tm_pos).le hg, mul_pos ((mul_pos F.S.hp_pos hA1)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_yT2] at n0_1 n0_2 n0_3 n0_4
    linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.hp_pos F.S.hm_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_yT2] at n0_1 n0_2 n0_3 n0_4
    linarith only [mul_nonneg (htp1).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.tm_pos).le hg, mul_pos ((mul_pos F.S.hp_pos hA1)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_yT2] at n0_1 n0_2 n0_3 n0_4
    linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n0_1), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.hp_pos F.S.hm_pos)) hde]

/-- 27.78: the edge crossing at xa xb -/
theorem Frame20.famE {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1 : 0 < F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) (hA1R : 0 < F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) (hA2f : 0 ≤ -F.S.hm*F.S.sm*F.S.tp - F.S.hp*F.S.sm*F.S.tm + F.S.km*F.S.tm) (hA2Rf : 0 ≤ F.S.hp*F.S.sp - F.S.km*F.S.sp*F.S.tp - F.S.kp*F.S.sm*F.S.tp)   :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.dep F.S.u_eXb 0 < F.dep F.S.u_eXb 5 ∨ F.dep F.S.u_eXb 0 < F.dep F.S.u_eXb 6 ∨ F.dep F.S.u_eXb 4 < F.dep F.S.u_eXb 5 ∨ F.dep F.S.u_eXb 4 < F.dep F.S.u_eXb 6) ∧ (F.dep F.S.u_eXb 5 < F.dep F.S.u_eXb 0 ∨ F.dep F.S.u_eXb 6 < F.dep F.S.u_eXb 0 ∨ F.dep F.S.u_eXb 5 < F.dep F.S.u_eXb 4 ∨ F.dep F.S.u_eXb 6 < F.dep F.S.u_eXb 4)
  · exact F.eXb (by linarith only [hA2Rf, (mul_pos F.S.tp_pos hA1R)]) (by linarith only [hA2f, (mul_pos F.S.sm_pos hA1)]) o0.1 o0.2
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  rcases o0 with n0 | n0
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_eXb] at n0_1 n0_2 n0_3 n0_4
    linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_3), mul_pos ((mul_pos F.S.sm_pos F.S.hp_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_eXb] at n0_1 n0_2 n0_3 n0_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_nonneg (rp).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos F.S.kp_pos)) hal, mul_pos ((mul_pos F.S.tp_pos rp)) hal, mul_pos ((mul_pos F.S.tp_pos F.S.kp_pos)) hbe, mul_pos ((mul_pos hsp1 F.S.hp_pos)) hbe]

/-- Q_A = V + T_A (27.64 (ii)) (R-image) -/
theorem Frame20.ra4_A_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hW : 0 < -F.S.hm - F.S.km*F.S.tm + F.S.km) (hQ : 0 < F.S.hm*F.S.sp - F.S.hm + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp - F.S.km*F.S.tm + F.S.km + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) (hD : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.sm*F.S.tm + F.S.hp*F.S.sm - F.S.km*F.S.tm*F.S.tp + F.S.km*F.S.tm + F.S.km*F.S.tp - F.S.km) (hA1 : 0 < F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp)   :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.rFrame.dep F.rFrame.S.u_vRa4 0 < F.rFrame.dep F.rFrame.S.u_vRa4 6 ∨ F.rFrame.dep F.rFrame.S.u_vRa4 0 < F.rFrame.dep F.rFrame.S.u_vRa4 1 ∨ F.rFrame.dep F.rFrame.S.u_vRa4 4 < F.rFrame.dep F.rFrame.S.u_vRa4 6 ∨ F.rFrame.dep F.rFrame.S.u_vRa4 4 < F.rFrame.dep F.rFrame.S.u_vRa4 1) ∧ (F.rFrame.dep F.rFrame.S.u_vRa4 6 < F.rFrame.dep F.rFrame.S.u_vRa4 0 ∨ F.rFrame.dep F.rFrame.S.u_vRa4 1 < F.rFrame.dep F.rFrame.S.u_vRa4 0 ∨ F.rFrame.dep F.rFrame.S.u_vRa4 6 < F.rFrame.dep F.rFrame.S.u_vRa4 4 ∨ F.rFrame.dep F.rFrame.S.u_vRa4 1 < F.rFrame.dep F.rFrame.S.u_vRa4 4)
  · exact rupert_of_r (F.rFrame.vRa4 (by simp only [rFrame_S, Shape20.swap]; linarith only [hW]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hQ]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hD]) o0.1 o0.2)
  by_cases o1 : (F.rFrame.dep F.rFrame.S.u_tA 0 < F.rFrame.dep F.rFrame.S.u_tA 6 ∨ F.rFrame.dep F.rFrame.S.u_tA 0 < F.rFrame.dep F.rFrame.S.u_tA 5 ∨ F.rFrame.dep F.rFrame.S.u_tA 4 < F.rFrame.dep F.rFrame.S.u_tA 6 ∨ F.rFrame.dep F.rFrame.S.u_tA 4 < F.rFrame.dep F.rFrame.S.u_tA 5) ∧ (F.rFrame.dep F.rFrame.S.u_tA 6 < F.rFrame.dep F.rFrame.S.u_tA 0 ∨ F.rFrame.dep F.rFrame.S.u_tA 5 < F.rFrame.dep F.rFrame.S.u_tA 0 ∨ F.rFrame.dep F.rFrame.S.u_tA 6 < F.rFrame.dep F.rFrame.S.u_tA 4 ∨ F.rFrame.dep F.rFrame.S.u_tA 5 < F.rFrame.dep F.rFrame.S.u_tA 4)
  · exact rupert_of_r (F.rFrame.tA (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1]) o1.1 o1.2)
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_tA] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n1_3), mul_nonneg (htp1).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.hp_pos F.S.km_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_tA] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_4), mul_nonneg (hW).le (sub_nonneg.2 n1_3), mul_pos ((mul_pos F.S.sm_pos F.S.hm_pos)) hbe, mul_pos ((mul_pos F.S.sm_pos hW)) hbe, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_tA] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.tp_pos hsm1)) hga, mul_pos ((mul_pos F.S.hp_pos F.S.km_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_tA] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg ((mul_pos F.S.sm_pos hsm1)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos hsm1 hsm1)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos htm1 F.S.sm_pos)).le (sub_nonneg.2 n1_1), mul_pos ((mul_pos F.S.km_pos hQ)) hde, mul_pos ((mul_pos (mul_pos F.S.tp_pos hW) hA1)) hde, mul_pos ((mul_pos (mul_pos htp1 hW) hA1)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.kp_pos) hW)) hde, mul_pos ((mul_pos (mul_pos hsp1 F.S.kp_pos) hW)) hde, mul_pos ((mul_pos (mul_pos F.S.sm_pos F.S.hm_pos) F.S.kp_pos)) hde, mul_pos ((mul_pos (mul_pos F.S.sm_pos F.S.hm_pos) F.S.km_pos)) hde]

/-- 27.32^R (27.64 (iii)) (R-image) -/
theorem Frame20.ra4_tBR_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hCr : 0 < -F.S.hp*F.S.sm + F.S.hp - F.S.km*F.S.tp)   :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.dep F.S.u_tB 0 < F.dep F.S.u_tB 1 ∨ F.dep F.S.u_tB 0 < F.dep F.S.u_tB 2 ∨ F.dep F.S.u_tB 6 < F.dep F.S.u_tB 1 ∨ F.dep F.S.u_tB 6 < F.dep F.S.u_tB 2) ∧ (F.dep F.S.u_tB 1 < F.dep F.S.u_tB 0 ∨ F.dep F.S.u_tB 2 < F.dep F.S.u_tB 0 ∨ F.dep F.S.u_tB 1 < F.dep F.S.u_tB 6 ∨ F.dep F.S.u_tB 2 < F.dep F.S.u_tB 6)
  · exact F.tB (by refine pos_of_pos_mul hsm1 ?_; linarith only [(mul_pos F.S.tp_pos rm), (mul_pos htm1 hCr)]) (by linarith only [hCr]) o0.1 o0.2
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  rcases o0 with n0 | n0
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tB] at n0_1 n0_2 n0_3 n0_4
    linarith only [mul_nonneg (hCr).le (sub_nonneg.2 n0_3), mul_pos ((mul_pos F.S.tp_pos hCr)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tB] at n0_1 n0_2 n0_3 n0_4
    linarith only [mul_nonneg ((mul_pos F.S.tp_pos hsp1)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos htp1 hsp1)).le (sub_nonneg.2 n0_2), mul_nonneg ((mul_pos htp1 F.S.sp_pos)).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos (mul_pos htp1 rp) hA1r)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.km_pos) rp)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos rp) hCr)) hde, mul_pos ((mul_pos (mul_pos F.S.sm_pos F.S.hp_pos) rp)) hde, mul_pos ((mul_pos (mul_pos hsm1 rp) rp)) hde]

/-- V + Y (27.64 (iv)) (R-image) -/
theorem Frame20.ra4_Y_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hW : 0 < -F.S.hm - F.S.km*F.S.tm + F.S.km) (hQ : 0 < F.S.hm*F.S.sp - F.S.hm + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp - F.S.km*F.S.tm + F.S.km + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) (hD : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.sm*F.S.tm + F.S.hp*F.S.sm - F.S.km*F.S.tm*F.S.tp + F.S.km*F.S.tm + F.S.km*F.S.tp - F.S.km) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hCm : 0 < F.S.hp*F.S.sm - F.S.hp + F.S.km*F.S.tp) (hA3h : 0 < F.S.hp*F.S.sp - F.S.hp - F.S.km*F.S.sp*F.S.tp + F.S.km*F.S.tp - F.S.kp*F.S.sm*F.S.tp + F.S.kp)   :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.rFrame.dep F.rFrame.S.u_vRa4 0 < F.rFrame.dep F.rFrame.S.u_vRa4 6 ∨ F.rFrame.dep F.rFrame.S.u_vRa4 0 < F.rFrame.dep F.rFrame.S.u_vRa4 1 ∨ F.rFrame.dep F.rFrame.S.u_vRa4 4 < F.rFrame.dep F.rFrame.S.u_vRa4 6 ∨ F.rFrame.dep F.rFrame.S.u_vRa4 4 < F.rFrame.dep F.rFrame.S.u_vRa4 1) ∧ (F.rFrame.dep F.rFrame.S.u_vRa4 6 < F.rFrame.dep F.rFrame.S.u_vRa4 0 ∨ F.rFrame.dep F.rFrame.S.u_vRa4 1 < F.rFrame.dep F.rFrame.S.u_vRa4 0 ∨ F.rFrame.dep F.rFrame.S.u_vRa4 6 < F.rFrame.dep F.rFrame.S.u_vRa4 4 ∨ F.rFrame.dep F.rFrame.S.u_vRa4 1 < F.rFrame.dep F.rFrame.S.u_vRa4 4)
  · exact rupert_of_r (F.rFrame.vRa4 (by simp only [rFrame_S, Shape20.swap]; linarith only [hW]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hQ]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hD]) o0.1 o0.2)
  by_cases o1 : (F.rFrame.dep F.rFrame.S.u_yY 1 < F.rFrame.dep F.rFrame.S.u_yY 3 ∨ F.rFrame.dep F.rFrame.S.u_yY 1 < F.rFrame.dep F.rFrame.S.u_yY 6 ∨ F.rFrame.dep F.rFrame.S.u_yY 2 < F.rFrame.dep F.rFrame.S.u_yY 6 ∨ F.rFrame.dep F.rFrame.S.u_yY 2 < F.rFrame.dep F.rFrame.S.u_yY 5) ∧ (F.rFrame.dep F.rFrame.S.u_yY 6 < F.rFrame.dep F.rFrame.S.u_yY 1 ∨ F.rFrame.dep F.rFrame.S.u_yY 6 < F.rFrame.dep F.rFrame.S.u_yY 2 ∨ F.rFrame.dep F.rFrame.S.u_yY 5 < F.rFrame.dep F.rFrame.S.u_yY 2 ∨ F.rFrame.dep F.rFrame.S.u_yY 5 < F.rFrame.dep F.rFrame.S.u_yY 3) ∧ (F.rFrame.dep F.rFrame.S.u_yY 2 < F.rFrame.dep F.rFrame.S.u_yY 6 ∨ F.rFrame.dep F.rFrame.S.u_yY 2 < F.rFrame.dep F.rFrame.S.u_yY 5 ∨ F.rFrame.dep F.rFrame.S.u_yY 3 < F.rFrame.dep F.rFrame.S.u_yY 5 ∨ F.rFrame.dep F.rFrame.S.u_yY 3 < F.rFrame.dep F.rFrame.S.u_yY 1) ∧ (F.rFrame.dep F.rFrame.S.u_yY 5 < F.rFrame.dep F.rFrame.S.u_yY 2 ∨ F.rFrame.dep F.rFrame.S.u_yY 5 < F.rFrame.dep F.rFrame.S.u_yY 3 ∨ F.rFrame.dep F.rFrame.S.u_yY 1 < F.rFrame.dep F.rFrame.S.u_yY 3 ∨ F.rFrame.dep F.rFrame.S.u_yY 1 < F.rFrame.dep F.rFrame.S.u_yY 6) ∧ (F.rFrame.dep F.rFrame.S.u_yY 3 < F.rFrame.dep F.rFrame.S.u_yY 5 ∨ F.rFrame.dep F.rFrame.S.u_yY 3 < F.rFrame.dep F.rFrame.S.u_yY 1 ∨ F.rFrame.dep F.rFrame.S.u_yY 6 < F.rFrame.dep F.rFrame.S.u_yY 1 ∨ F.rFrame.dep F.rFrame.S.u_yY 6 < F.rFrame.dep F.rFrame.S.u_yY 2)
  · exact rupert_of_r (F.rFrame.yY (by simp only [rFrame_S, Shape20.swap]; refine pos_of_pos_mul hsm1 ?_; linarith only [(mul_pos F.S.sp_pos hCm), (mul_pos (mul_pos F.S.tp_pos F.S.sm_pos) hA1r)]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hA3h]) o1.1 o1.2.1 o1.2.2.1 o1.2.2.2.1 o1.2.2.2.2)
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 | n1 | n1 | n1
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg ((mul_pos F.S.tp_pos F.S.sp_pos)).le (sub_nonneg.2 n0_3), mul_nonneg ((mul_pos F.S.tp_pos hsp1)).le (sub_nonneg.2 n0_3), mul_nonneg (htp1).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos (mul_pos htp1 htm1) F.S.sm_pos)) hbe, mul_pos ((mul_pos (mul_pos htp1 htm1) F.S.sm_pos)) hga, mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.hp_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos htp1 F.S.hp_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos htp1 F.S.kp_pos) hW)) hde, mul_pos ((mul_pos (mul_pos htp1 hW) hA1r)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) rm)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) hW)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos hD) hA1r)) hde, mul_pos ((mul_pos (mul_pos hsp1 hD) hA1r)) hde, mul_pos ((mul_pos (mul_pos F.S.sm_pos F.S.hp_pos) hW)) hde, mul_pos ((mul_pos (mul_pos F.S.sm_pos F.S.kp_pos) hD)) hde, mul_pos ((mul_pos (mul_pos hsm1 rp) hW)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n1_1), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_1), mul_nonneg (hA1r).le (sub_nonneg.2 n1_1), mul_nonneg (hA3h).le (sub_nonneg.2 n1_1), mul_pos ((mul_pos F.S.tp_pos F.S.hm_pos)) hal, mul_pos ((mul_pos F.S.tp_pos hQ)) hal, mul_pos ((mul_pos F.S.tp_pos hD)) hal, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 F.S.kp_pos)) hal, mul_pos ((mul_pos htp1 hQ)) hal, mul_pos ((mul_pos htp1 hD)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos hCm)) hal, mul_pos ((mul_pos htm1 F.S.kp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos F.S.hp_pos)) hal, mul_pos ((mul_pos hsp1 F.S.hm_pos)) hal, mul_pos ((mul_pos hsm1 F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sm_pos F.S.hp_pos)) hbe, mul_pos ((mul_pos F.S.sm_pos F.S.hm_pos)) hbe, mul_pos ((mul_pos F.S.sm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sm_pos hA3h)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.kp_pos F.S.km_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n0_4), mul_nonneg ((mul_pos F.S.tm_pos F.S.sm_pos)).le (sub_nonneg.2 n0_4), mul_nonneg ((mul_pos F.S.tm_pos hsm1)).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos (mul_pos htm1 F.S.sp_pos) F.S.sm_pos)) hbe, mul_pos ((mul_pos (mul_pos htm1 hsp1) F.S.sm_pos)) hbe, mul_pos ((mul_pos (mul_pos htp1 htm1) F.S.sm_pos)) hga, mul_pos ((mul_pos (mul_pos htp1 F.S.kp_pos) hW)) hde, mul_pos ((mul_pos (mul_pos htp1 F.S.kp_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos htp1 hW) hA1r)) hde, mul_pos ((mul_pos (mul_pos htp1 hQ) hA1r)) hde, mul_pos ((mul_pos (mul_pos F.S.tm_pos hD) hA1r)) hde, mul_pos ((mul_pos (mul_pos htm1 hD) hA1r)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) rm)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) hW)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos rp) rm)) hde, mul_pos ((mul_pos (mul_pos hsp1 hD) hA1r)) hde, mul_pos ((mul_pos (mul_pos F.S.sm_pos F.S.hp_pos) hW)) hde, mul_pos ((mul_pos (mul_pos F.S.sm_pos F.S.kp_pos) hD)) hde, mul_pos ((mul_pos (mul_pos F.S.sm_pos rp) hQ)) hde, mul_pos ((mul_pos (mul_pos hsm1 rp) hQ)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.tm_pos htm1)) hal, mul_pos ((mul_pos htm1 htm1)) hal, mul_pos ((mul_pos htm1 hsm1)) hga, mul_pos ((mul_pos F.S.hm_pos F.S.km_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg ((mul_pos F.S.tp_pos hsp1)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos htp1 hsp1)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos htm1 F.S.sm_pos)).le (sub_nonneg.2 n1_1), mul_pos ((mul_pos (mul_pos F.S.tm_pos F.S.km_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos F.S.tm_pos hW) hQ)) hde, mul_pos ((mul_pos (mul_pos htm1 hW) hQ)) hde, mul_pos ((mul_pos (mul_pos F.S.sm_pos F.S.hm_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos hsm1 F.S.hm_pos) hQ)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n1_1), (sub_nonneg.2 n1_2), mul_pos ((mul_pos F.S.sp_pos F.S.sp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hsp1)) hal, mul_pos ((mul_pos hsp1 hsp1)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.sm_pos)) hbe, mul_pos ((mul_pos htm1 hsm1)) hga, mul_pos ((mul_pos F.S.hm_pos F.S.km_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.kp_pos F.S.km_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg ((mul_pos F.S.sp_pos hsp1)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos hsp1 hsp1)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos htm1 F.S.sm_pos)).le (sub_nonneg.2 n1_3), mul_pos ((mul_pos (mul_pos F.S.tp_pos hQ) hCm)) hde, mul_pos ((mul_pos (mul_pos htp1 F.S.km_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos htp1 hQ) hCm)) hde, mul_pos ((mul_pos (mul_pos hsm1 F.S.hp_pos) hQ)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_3), mul_nonneg (hW).le (sub_nonneg.2 n1_3), mul_nonneg (hA1r).le (sub_nonneg.2 n1_3), mul_pos ((mul_pos F.S.tp_pos hQ)) hal, mul_pos ((mul_pos htp1 hQ)) hal, mul_pos ((mul_pos F.S.tm_pos hA1r)) hal, mul_pos ((mul_pos htm1 F.S.kp_pos)) hal, mul_pos ((mul_pos hsp1 F.S.hm_pos)) hal, mul_pos ((mul_pos F.S.sm_pos F.S.hm_pos)) hbe, mul_pos ((mul_pos F.S.sm_pos hW)) hbe, mul_pos ((mul_pos F.S.sm_pos hA1r)) hbe]

/-- V + X (27.64 (iv)) (R-image) -/
theorem Frame20.ra4_X_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hW : 0 < -F.S.hm - F.S.km*F.S.tm + F.S.km) (hQ : 0 < F.S.hm*F.S.sp - F.S.hm + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp - F.S.km*F.S.tm + F.S.km + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) (hD : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.sm*F.S.tm + F.S.hp*F.S.sm - F.S.km*F.S.tm*F.S.tp + F.S.km*F.S.tm + F.S.km*F.S.tp - F.S.km) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hCm : 0 < F.S.hp*F.S.sm - F.S.hp + F.S.km*F.S.tp) (hA3 : 0 < -F.S.hp*F.S.sp + F.S.hp + F.S.km*F.S.sp*F.S.tp - F.S.km*F.S.tp + F.S.kp*F.S.sm*F.S.tp - F.S.kp)   :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.rFrame.dep F.rFrame.S.u_vRa4 0 < F.rFrame.dep F.rFrame.S.u_vRa4 6 ∨ F.rFrame.dep F.rFrame.S.u_vRa4 0 < F.rFrame.dep F.rFrame.S.u_vRa4 1 ∨ F.rFrame.dep F.rFrame.S.u_vRa4 4 < F.rFrame.dep F.rFrame.S.u_vRa4 6 ∨ F.rFrame.dep F.rFrame.S.u_vRa4 4 < F.rFrame.dep F.rFrame.S.u_vRa4 1) ∧ (F.rFrame.dep F.rFrame.S.u_vRa4 6 < F.rFrame.dep F.rFrame.S.u_vRa4 0 ∨ F.rFrame.dep F.rFrame.S.u_vRa4 1 < F.rFrame.dep F.rFrame.S.u_vRa4 0 ∨ F.rFrame.dep F.rFrame.S.u_vRa4 6 < F.rFrame.dep F.rFrame.S.u_vRa4 4 ∨ F.rFrame.dep F.rFrame.S.u_vRa4 1 < F.rFrame.dep F.rFrame.S.u_vRa4 4)
  · exact rupert_of_r (F.rFrame.vRa4 (by simp only [rFrame_S, Shape20.swap]; linarith only [hW]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hQ]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hD]) o0.1 o0.2)
  by_cases o1 : (F.rFrame.dep F.rFrame.S.u_xX 1 < F.rFrame.dep F.rFrame.S.u_xX 6 ∨ F.rFrame.dep F.rFrame.S.u_xX 1 < F.rFrame.dep F.rFrame.S.u_xX 3 ∨ F.rFrame.dep F.rFrame.S.u_xX 5 < F.rFrame.dep F.rFrame.S.u_xX 3 ∨ F.rFrame.dep F.rFrame.S.u_xX 5 < F.rFrame.dep F.rFrame.S.u_xX 2) ∧ (F.rFrame.dep F.rFrame.S.u_xX 3 < F.rFrame.dep F.rFrame.S.u_xX 1 ∨ F.rFrame.dep F.rFrame.S.u_xX 3 < F.rFrame.dep F.rFrame.S.u_xX 5 ∨ F.rFrame.dep F.rFrame.S.u_xX 2 < F.rFrame.dep F.rFrame.S.u_xX 5 ∨ F.rFrame.dep F.rFrame.S.u_xX 2 < F.rFrame.dep F.rFrame.S.u_xX 6) ∧ (F.rFrame.dep F.rFrame.S.u_xX 5 < F.rFrame.dep F.rFrame.S.u_xX 3 ∨ F.rFrame.dep F.rFrame.S.u_xX 5 < F.rFrame.dep F.rFrame.S.u_xX 2 ∨ F.rFrame.dep F.rFrame.S.u_xX 6 < F.rFrame.dep F.rFrame.S.u_xX 2 ∨ F.rFrame.dep F.rFrame.S.u_xX 6 < F.rFrame.dep F.rFrame.S.u_xX 1) ∧ (F.rFrame.dep F.rFrame.S.u_xX 2 < F.rFrame.dep F.rFrame.S.u_xX 5 ∨ F.rFrame.dep F.rFrame.S.u_xX 2 < F.rFrame.dep F.rFrame.S.u_xX 6 ∨ F.rFrame.dep F.rFrame.S.u_xX 1 < F.rFrame.dep F.rFrame.S.u_xX 6 ∨ F.rFrame.dep F.rFrame.S.u_xX 1 < F.rFrame.dep F.rFrame.S.u_xX 3) ∧ (F.rFrame.dep F.rFrame.S.u_xX 6 < F.rFrame.dep F.rFrame.S.u_xX 2 ∨ F.rFrame.dep F.rFrame.S.u_xX 6 < F.rFrame.dep F.rFrame.S.u_xX 1 ∨ F.rFrame.dep F.rFrame.S.u_xX 3 < F.rFrame.dep F.rFrame.S.u_xX 1 ∨ F.rFrame.dep F.rFrame.S.u_xX 3 < F.rFrame.dep F.rFrame.S.u_xX 5)
  · exact rupert_of_r (F.rFrame.xX (by simp only [rFrame_S, Shape20.swap]; linarith only [hA3]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1r]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hCm]) o1.1 o1.2.1 o1.2.2.1 o1.2.2.2.1 o1.2.2.2.2)
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 | n1 | n1 | n1
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(sub_nonneg.2 n1_1), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos F.S.tp_pos hCm)) hal, mul_pos ((mul_pos htp1 hCm)) hal, mul_pos ((mul_pos hsm1 F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos htm1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hsp1 hCm)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(sub_nonneg.2 n0_4), mul_pos ((mul_pos (mul_pos F.S.tp_pos htm1) F.S.sm_pos)) hbe, mul_pos ((mul_pos (mul_pos htp1 htm1) F.S.sm_pos)) hbe, mul_pos ((mul_pos (mul_pos htp1 htm1) F.S.sm_pos)) hga, mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.hm_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.kp_pos) rm)) hde, mul_pos ((mul_pos (mul_pos F.S.tp_pos hW) hA3)) hde, mul_pos ((mul_pos (mul_pos F.S.tp_pos hQ) hD)) hde, mul_pos ((mul_pos (mul_pos htp1 F.S.kp_pos) hW)) hde, mul_pos ((mul_pos (mul_pos htp1 hW) hA3)) hde, mul_pos ((mul_pos (mul_pos htp1 hQ) hD)) hde, mul_pos ((mul_pos (mul_pos F.S.tm_pos F.S.hp_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos F.S.tm_pos hW) hQ)) hde, mul_pos ((mul_pos (mul_pos F.S.tm_pos hQ) hCm)) hde, mul_pos ((mul_pos (mul_pos htm1 hW) hQ)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) hW)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.km_pos) hD)) hde, mul_pos ((mul_pos (mul_pos F.S.sm_pos F.S.kp_pos) hD)) hde, mul_pos ((mul_pos (mul_pos F.S.sm_pos hD) hA1r)) hde, mul_pos ((mul_pos (mul_pos hsm1 F.S.hp_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos hsm1 hD) hA1r)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(sub_nonneg.2 n0_4), mul_pos ((mul_pos (mul_pos F.S.tp_pos htm1) F.S.sm_pos)) hbe, mul_pos ((mul_pos (mul_pos htp1 htm1) F.S.sm_pos)) hbe, mul_pos ((mul_pos (mul_pos htp1 htm1) F.S.sm_pos)) hga, mul_pos ((mul_pos (mul_pos F.S.tp_pos hW) hCm)) hde, mul_pos ((mul_pos (mul_pos F.S.tp_pos hW) hA3)) hde, mul_pos ((mul_pos (mul_pos htp1 F.S.kp_pos) hW)) hde, mul_pos ((mul_pos (mul_pos htp1 hW) hCm)) hde, mul_pos ((mul_pos (mul_pos htp1 hW) hA3)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) rm)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) hW)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos hW) hA1r)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos hD) hA1r)) hde, mul_pos ((mul_pos (mul_pos hsp1 hW) hA1r)) hde, mul_pos ((mul_pos (mul_pos hsp1 hD) hA1r)) hde, mul_pos ((mul_pos (mul_pos hsm1 F.S.hp_pos) hQ)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(sub_nonneg.2 n1_3), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos F.S.tp_pos hCm)) hal, mul_pos ((mul_pos htp1 hCm)) hal, mul_pos ((mul_pos hsm1 F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos htm1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hsp1 hCm)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(sub_nonneg.2 n0_4), mul_pos ((mul_pos htm1 F.S.sm_pos)) hbe, mul_pos ((mul_pos (mul_pos htp1 htm1) F.S.sm_pos)) hga, mul_pos ((mul_pos (mul_pos htp1 F.S.kp_pos) hW)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) hW)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.km_pos) hW)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.km_pos) hD)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos hW) hA1r)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos hW) hA3)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos hD) hA1r)) hde, mul_pos ((mul_pos (mul_pos hsp1 hW) hA1r)) hde, mul_pos ((mul_pos (mul_pos hsp1 hW) hCm)) hde, mul_pos ((mul_pos (mul_pos hsp1 hW) hA3)) hde, mul_pos ((mul_pos (mul_pos hsp1 hD) hA1r)) hde, mul_pos ((mul_pos (mul_pos hsm1 F.S.hp_pos) hQ)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(sub_nonneg.2 n1_1), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos F.S.tp_pos hCm)) hal, mul_pos ((mul_pos htp1 hCm)) hal, mul_pos ((mul_pos hsm1 F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos htm1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hsp1 hCm)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg ((mul_pos F.S.tp_pos F.S.km_pos)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos F.S.tp_pos hA1r)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos F.S.tp_pos hA3)).le (sub_nonneg.2 n0_2), mul_nonneg ((mul_pos htp1 hA3)).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos (mul_pos F.S.tp_pos htm1) F.S.kp_pos)) hal, mul_pos ((mul_pos (mul_pos F.S.tp_pos htm1) hA1r)) hal, mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.sm_pos) F.S.hm_pos)) hal, mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.sm_pos) hQ)) hal, mul_pos ((mul_pos (mul_pos htp1 htm1) hA1r)) hal, mul_pos ((mul_pos (mul_pos htp1 F.S.sp_pos) F.S.hm_pos)) hal, mul_pos ((mul_pos (mul_pos htp1 F.S.sp_pos) rm)) hal, mul_pos ((mul_pos (mul_pos htm1 hsp1) hCm)) hal, mul_pos ((mul_pos (mul_pos htm1 hsm1) hA3)) hal, mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.sp_pos) hW)) hal, mul_pos ((mul_pos (mul_pos F.S.sp_pos hsp1) hW)) hal, mul_pos ((mul_pos (mul_pos F.S.sp_pos hsm1) F.S.hm_pos)) hal, mul_pos ((mul_pos (mul_pos htp1 F.S.sp_pos) rm)) hbe, mul_pos ((mul_pos (mul_pos htm1 F.S.sm_pos) hA1r)) hbe, mul_pos ((mul_pos (mul_pos htm1 F.S.sm_pos) hCm)) hbe, mul_pos ((mul_pos (mul_pos F.S.sp_pos hsm1) hD)) hbe, mul_pos ((mul_pos (mul_pos F.S.km_pos rp) rm)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg ((mul_pos (mul_pos F.S.tp_pos F.S.sp_pos) F.S.km_pos)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos F.S.tp_pos F.S.sp_pos) hA1r)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos F.S.tp_pos F.S.sp_pos) hA3)).le (sub_nonneg.2 n0_2), mul_nonneg ((mul_pos (mul_pos htp1 F.S.sp_pos) hA3)).le (sub_nonneg.2 n0_2), mul_nonneg ((mul_pos htm1 F.S.sm_pos)).le (sub_nonneg.2 n1_1), mul_pos ((mul_pos (mul_pos (mul_pos htp1 F.S.kp_pos) F.S.km_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos (mul_pos htp1 F.S.kp_pos) F.S.km_pos) hD)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.tm_pos F.S.hm_pos) hA1r) hA3)) hde, mul_pos ((mul_pos (mul_pos (mul_pos htm1 F.S.hm_pos) hA1r) hA3)) hde, mul_pos ((mul_pos (mul_pos (mul_pos htm1 F.S.km_pos) hA1r) hA1r)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) F.S.hp_pos) rm)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) F.S.km_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) hW) hA1r)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) hW) hCm)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) hD) hA1r)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.sp_pos F.S.hm_pos) F.S.kp_pos) F.S.km_pos)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.sp_pos F.S.hm_pos) F.S.km_pos) hA1r)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.sp_pos F.S.hm_pos) F.S.km_pos) hA3)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.sp_pos F.S.kp_pos) hW) hCm)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.sp_pos F.S.kp_pos) hD) hCm)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.sp_pos F.S.km_pos) hW) hA1r)) hde, mul_pos ((mul_pos (mul_pos (mul_pos hsp1 F.S.hp_pos) hD) hA1r)) hde, mul_pos ((mul_pos (mul_pos (mul_pos hsp1 F.S.hm_pos) F.S.kp_pos) hCm)) hde, mul_pos ((mul_pos (mul_pos (mul_pos hsp1 F.S.kp_pos) hW) hCm)) hde, mul_pos ((mul_pos (mul_pos (mul_pos hsp1 F.S.kp_pos) hD) hCm)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.sm_pos F.S.hm_pos) F.S.kp_pos) hA1r)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.sm_pos F.S.hm_pos) F.S.kp_pos) hA3)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.sm_pos F.S.kp_pos) hW) hA1r)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.sm_pos F.S.kp_pos) hW) hA3)) hde, mul_pos ((mul_pos (mul_pos (mul_pos hsm1 F.S.kp_pos) hW) hA3)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(sub_nonneg.2 n1_3), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos F.S.tp_pos hCm)) hal, mul_pos ((mul_pos htp1 hCm)) hal, mul_pos ((mul_pos hsm1 F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos htm1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hsp1 hCm)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg ((mul_pos hsp1 hCm)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos F.S.tp_pos hsp1) hA1r)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos htp1 F.S.sp_pos) F.S.km_pos)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos htp1 F.S.sp_pos) hA1r)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos htp1 hsp1) hA1r)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos F.S.sm_pos hsm1) rp)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos hsm1 hsm1) rp)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos F.S.sp_pos hsp1) hA3)).le (sub_nonneg.2 n0_2), mul_nonneg ((mul_pos (mul_pos hsp1 hsp1) hA3)).le (sub_nonneg.2 n0_2), mul_nonneg ((mul_pos htm1 F.S.sm_pos)).le (sub_nonneg.2 n1_3), mul_pos ((mul_pos (mul_pos F.S.km_pos rp) hQ)) hde]

/-- 27.74 (i), ω > 0 (R-image) -/
theorem Frame20.om1p_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (htt : 0 ≤ -F.S.sm + F.S.sp) (hom : 0 < (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) (hHR : ¬ F.ClassHR)  :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.rFrame.dep F.rFrame.S.u_tANR 0 < F.rFrame.dep F.rFrame.S.u_tANR 6 ∨ F.rFrame.dep F.rFrame.S.u_tANR 0 < F.rFrame.dep F.rFrame.S.u_tANR 3 ∨ F.rFrame.dep F.rFrame.S.u_tANR 4 < F.rFrame.dep F.rFrame.S.u_tANR 6 ∨ F.rFrame.dep F.rFrame.S.u_tANR 4 < F.rFrame.dep F.rFrame.S.u_tANR 3) ∧ (F.rFrame.dep F.rFrame.S.u_tANR 6 < F.rFrame.dep F.rFrame.S.u_tANR 0 ∨ F.rFrame.dep F.rFrame.S.u_tANR 3 < F.rFrame.dep F.rFrame.S.u_tANR 0 ∨ F.rFrame.dep F.rFrame.S.u_tANR 6 < F.rFrame.dep F.rFrame.S.u_tANR 4 ∨ F.rFrame.dep F.rFrame.S.u_tANR 3 < F.rFrame.dep F.rFrame.S.u_tANR 4)
  · exact rupert_of_r (F.rFrame.tANR_slide (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1r]) o0.1 o0.2 (fun h => hHR (F.classH_rFrame_iff.1 h)))
  by_cases o1 : (F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 6 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 6) ∧ (F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 4 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 4)
  · exact rupert_of_r (F.rFrame.tP (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1r]) o1.1 o1.2)
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n1_2), mul_nonneg (htp1).le (sub_nonneg.2 n1_2), mul_nonneg htt (sub_nonneg.2 n1_2), mul_pos ((mul_pos F.S.sp_pos hsm1)) hbe, mul_pos ((mul_pos hsm1 hsm1)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(sub_nonneg.2 n1_4), mul_pos F.S.sm_pos hom, mul_pos hsm1 hom]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n0_1), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n0_2), mul_nonneg (htm1).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n0_3), mul_nonneg (hsp1).le (sub_nonneg.2 n0_4), mul_nonneg (htp1).le (sub_nonneg.2 n1_1), mul_nonneg (hsp1).le (sub_nonneg.2 n1_1), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n1_2), mul_nonneg (htm1).le (sub_nonneg.2 n1_2), mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n1_3), mul_pos htp1 hom, mul_nonneg htt hom.le, mul_pos ((mul_pos htp1 hsm1)) hbe, mul_pos ((mul_pos hsm1 hsm1)) hbe, mul_pos ((mul_pos hsm1 hsm1)) hga, mul_pos ((mul_pos F.S.km_pos F.S.km_pos)) hde, mul_pos ((mul_pos F.S.km_pos hA1r)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n0_2), mul_nonneg htt (sub_nonneg.2 n0_4), mul_nonneg htt (sub_nonneg.2 n1_2), mul_nonneg htt hom.le, mul_pos ((mul_pos F.S.km_pos F.S.km_pos)) hde, mul_pos ((mul_pos F.S.km_pos hA1r)) hde]

/-- 27.74 (i), ω < 0 (R-image) -/
theorem Frame20.om1n_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (htt : 0 ≤ -F.S.sm + F.S.sp) (hom : 0 < (-F.S.sm*F.S.tp + F.S.sm + F.S.tp - 1) * F.a12 + (F.S.hp*F.S.km) * F.gg) (hHR : ¬ F.ClassHR)  :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.rFrame.dep F.rFrame.S.u_tANR 0 < F.rFrame.dep F.rFrame.S.u_tANR 6 ∨ F.rFrame.dep F.rFrame.S.u_tANR 0 < F.rFrame.dep F.rFrame.S.u_tANR 3 ∨ F.rFrame.dep F.rFrame.S.u_tANR 4 < F.rFrame.dep F.rFrame.S.u_tANR 6 ∨ F.rFrame.dep F.rFrame.S.u_tANR 4 < F.rFrame.dep F.rFrame.S.u_tANR 3) ∧ (F.rFrame.dep F.rFrame.S.u_tANR 6 < F.rFrame.dep F.rFrame.S.u_tANR 0 ∨ F.rFrame.dep F.rFrame.S.u_tANR 3 < F.rFrame.dep F.rFrame.S.u_tANR 0 ∨ F.rFrame.dep F.rFrame.S.u_tANR 6 < F.rFrame.dep F.rFrame.S.u_tANR 4 ∨ F.rFrame.dep F.rFrame.S.u_tANR 3 < F.rFrame.dep F.rFrame.S.u_tANR 4)
  · exact rupert_of_r (F.rFrame.tANR_slide (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1r]) o0.1 o0.2 (fun h => hHR (F.classH_rFrame_iff.1 h)))
  by_cases o1 : (F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 6 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 6) ∧ (F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 4 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 4)
  · exact rupert_of_r (F.rFrame.tP (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1r]) o1.1 o1.2)
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(sub_nonneg.2 n0_3), mul_pos hsp1 hom, mul_pos F.S.sm_pos hom, mul_nonneg htt hom.le]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(sub_nonneg.2 n0_3), mul_pos hsp1 hom, mul_pos F.S.sm_pos hom, mul_nonneg htt hom.le]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n1_3), mul_pos F.S.kp_pos hom, mul_pos F.S.km_pos hom, mul_pos ((mul_pos hsm1 hA1r)) hbe, mul_pos ((mul_pos hsm1 F.S.km_pos)) hga, mul_pos ((mul_pos hsm1 hA1r)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n0_2), mul_nonneg htt (sub_nonneg.2 n1_1), mul_pos ((mul_pos F.S.km_pos F.S.km_pos)) hde, mul_pos ((mul_pos F.S.km_pos hA1r)) hde]

/-- 27.74 (i), ω = 0, off ℓ1 (R-image) -/
theorem Frame20.om1z1_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (htt : 0 ≤ -F.S.sm + F.S.sp) (hom1 : 0 ≤ (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) (hom2 : 0 ≤ (-F.S.sm*F.S.tp + F.S.sm + F.S.tp - 1) * F.a12 + (F.S.hp*F.S.km) * F.gg) (hl : 0 < (F.S.hp*F.S.sp) * (F.a22 - F.a12) + (F.S.hp*F.S.sp - F.S.hp - F.S.kp*F.S.tp + F.S.kp) * F.a12) (hHR : ¬ F.ClassHR)  :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.rFrame.dep F.rFrame.S.u_tANR 0 < F.rFrame.dep F.rFrame.S.u_tANR 6 ∨ F.rFrame.dep F.rFrame.S.u_tANR 0 < F.rFrame.dep F.rFrame.S.u_tANR 3 ∨ F.rFrame.dep F.rFrame.S.u_tANR 4 < F.rFrame.dep F.rFrame.S.u_tANR 6 ∨ F.rFrame.dep F.rFrame.S.u_tANR 4 < F.rFrame.dep F.rFrame.S.u_tANR 3) ∧ (F.rFrame.dep F.rFrame.S.u_tANR 6 < F.rFrame.dep F.rFrame.S.u_tANR 0 ∨ F.rFrame.dep F.rFrame.S.u_tANR 3 < F.rFrame.dep F.rFrame.S.u_tANR 0 ∨ F.rFrame.dep F.rFrame.S.u_tANR 6 < F.rFrame.dep F.rFrame.S.u_tANR 4 ∨ F.rFrame.dep F.rFrame.S.u_tANR 3 < F.rFrame.dep F.rFrame.S.u_tANR 4)
  · exact rupert_of_r (F.rFrame.tANR_slide (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1r]) o0.1 o0.2 (fun h => hHR (F.classH_rFrame_iff.1 h)))
  by_cases o1 : (F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 6 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 6) ∧ (F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 4 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 4)
  · exact rupert_of_r (F.rFrame.tP (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1r]) o1.1 o1.2)
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n1_2), mul_nonneg (hsp1).le (sub_nonneg.2 n1_2), mul_pos ((mul_pos F.S.sm_pos hsm1)) hbe, mul_pos ((mul_pos hsm1 hsm1)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_4), mul_pos hsp1 hl, mul_nonneg htt hl.le]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_1), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n1_1), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos hsm1 F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hA1r)) hbe, mul_pos ((mul_pos hsm1 F.S.km_pos)) hga, mul_pos ((mul_pos hsm1 hA1r)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n0_2), mul_nonneg htt (sub_nonneg.2 n1_1), mul_pos ((mul_pos F.S.km_pos F.S.km_pos)) hde, mul_pos ((mul_pos F.S.km_pos hA1r)) hde]

/-- 27.74 (i), ω = 0, off ℓ1 (R-image) -/
theorem Frame20.om1z2_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (htt : 0 ≤ -F.S.sm + F.S.sp) (hom1 : 0 ≤ (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) (hom2 : 0 ≤ (-F.S.sm*F.S.tp + F.S.sm + F.S.tp - 1) * F.a12 + (F.S.hp*F.S.km) * F.gg) (hl : 0 < (-F.S.hp*F.S.sp) * (F.a22 - F.a12) + (-F.S.hp*F.S.sp + F.S.hp + F.S.kp*F.S.tp - F.S.kp) * F.a12) (hHR : ¬ F.ClassHR)  :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.rFrame.dep F.rFrame.S.u_tANR 0 < F.rFrame.dep F.rFrame.S.u_tANR 6 ∨ F.rFrame.dep F.rFrame.S.u_tANR 0 < F.rFrame.dep F.rFrame.S.u_tANR 3 ∨ F.rFrame.dep F.rFrame.S.u_tANR 4 < F.rFrame.dep F.rFrame.S.u_tANR 6 ∨ F.rFrame.dep F.rFrame.S.u_tANR 4 < F.rFrame.dep F.rFrame.S.u_tANR 3) ∧ (F.rFrame.dep F.rFrame.S.u_tANR 6 < F.rFrame.dep F.rFrame.S.u_tANR 0 ∨ F.rFrame.dep F.rFrame.S.u_tANR 3 < F.rFrame.dep F.rFrame.S.u_tANR 0 ∨ F.rFrame.dep F.rFrame.S.u_tANR 6 < F.rFrame.dep F.rFrame.S.u_tANR 4 ∨ F.rFrame.dep F.rFrame.S.u_tANR 3 < F.rFrame.dep F.rFrame.S.u_tANR 4)
  · exact rupert_of_r (F.rFrame.tANR_slide (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1r]) o0.1 o0.2 (fun h => hHR (F.classH_rFrame_iff.1 h)))
  by_cases o1 : (F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 6 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 6) ∧ (F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 4 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 4)
  · exact rupert_of_r (F.rFrame.tP (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1r]) o1.1 o1.2)
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n1_1), mul_pos hsp1 hl, mul_nonneg htt hl.le, mul_pos ((mul_pos hsm1 F.S.hp_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n1_4), mul_pos hsp1 hl, mul_nonneg htt hl.le]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n1_1), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_2), mul_pos ((mul_pos hsm1 F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hA1r)) hbe, mul_pos ((mul_pos hsm1 F.S.km_pos)) hga, mul_pos ((mul_pos hsm1 hA1r)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n0_2), mul_nonneg htt (sub_nonneg.2 n1_1), mul_pos ((mul_pos F.S.km_pos F.S.km_pos)) hde, mul_pos ((mul_pos F.S.km_pos hA1r)) hde]

/-- 27.74 (ii): {T_A, V}, h+ ≥ d+ (R-image) -/
theorem Frame20.om2a_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1 : 0 < F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) (hVp : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVW : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hWp : 0 ≤ -F.S.hm - F.S.km*F.S.tm + F.S.km) (hHR : ¬ F.ClassHR)  :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.rFrame.dep F.rFrame.S.u_tA 0 < F.rFrame.dep F.rFrame.S.u_tA 6 ∨ F.rFrame.dep F.rFrame.S.u_tA 0 < F.rFrame.dep F.rFrame.S.u_tA 5 ∨ F.rFrame.dep F.rFrame.S.u_tA 4 < F.rFrame.dep F.rFrame.S.u_tA 6 ∨ F.rFrame.dep F.rFrame.S.u_tA 4 < F.rFrame.dep F.rFrame.S.u_tA 5) ∧ (F.rFrame.dep F.rFrame.S.u_tA 6 < F.rFrame.dep F.rFrame.S.u_tA 0 ∨ F.rFrame.dep F.rFrame.S.u_tA 5 < F.rFrame.dep F.rFrame.S.u_tA 0 ∨ F.rFrame.dep F.rFrame.S.u_tA 6 < F.rFrame.dep F.rFrame.S.u_tA 4 ∨ F.rFrame.dep F.rFrame.S.u_tA 5 < F.rFrame.dep F.rFrame.S.u_tA 4)
  · exact rupert_of_r (F.rFrame.tA (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1]) o0.1 o0.2)
  by_cases o1 : (F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 6 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 6) ∧ (F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 4 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 4)
  · exact rupert_of_r (F.rFrame.vN4_slide (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVp]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVW]) o1.1 o1.2 (fun h => hHR (F.classH_rFrame_iff.1 h)))
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n0_3), mul_nonneg (htp1).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.hp_pos F.S.km_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n0_3), mul_nonneg (htp1).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.hp_pos F.S.km_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg hWp (sub_nonneg.2 n0_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg ((mul_pos htm1 F.S.sm_pos)).le (sub_nonneg.2 n0_1), mul_nonneg (hsm1).le (sub_nonneg.2 n1_2), mul_pos ((mul_pos (mul_pos F.S.tp_pos rm) rm)) hde, mul_pos ((mul_pos (mul_pos htp1 rm) rm)) hde, mul_pos ((mul_pos (mul_pos F.S.tm_pos F.S.km_pos) rm)) hde, mul_pos ((mul_pos (mul_pos hsm1 F.S.hm_pos) rm)) hde]

/-- 27.74 (ii): {T_A, V}, t+ ≤ t−, h+ ≤ d+ (R-image) -/
theorem Frame20.om2b_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1 : 0 < F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) (hVp : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVW : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (htt : 0 ≤ -F.S.sm + F.S.sp) (hWn : 0 ≤ F.S.hm + F.S.km*F.S.tm - F.S.km) (hHR : ¬ F.ClassHR)  :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.rFrame.dep F.rFrame.S.u_tA 0 < F.rFrame.dep F.rFrame.S.u_tA 6 ∨ F.rFrame.dep F.rFrame.S.u_tA 0 < F.rFrame.dep F.rFrame.S.u_tA 5 ∨ F.rFrame.dep F.rFrame.S.u_tA 4 < F.rFrame.dep F.rFrame.S.u_tA 6 ∨ F.rFrame.dep F.rFrame.S.u_tA 4 < F.rFrame.dep F.rFrame.S.u_tA 5) ∧ (F.rFrame.dep F.rFrame.S.u_tA 6 < F.rFrame.dep F.rFrame.S.u_tA 0 ∨ F.rFrame.dep F.rFrame.S.u_tA 5 < F.rFrame.dep F.rFrame.S.u_tA 0 ∨ F.rFrame.dep F.rFrame.S.u_tA 6 < F.rFrame.dep F.rFrame.S.u_tA 4 ∨ F.rFrame.dep F.rFrame.S.u_tA 5 < F.rFrame.dep F.rFrame.S.u_tA 4)
  · exact rupert_of_r (F.rFrame.tA (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1]) o0.1 o0.2)
  by_cases o1 : (F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 6 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 6) ∧ (F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 4 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 4)
  · exact rupert_of_r (F.rFrame.vN4_slide (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVp]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVW]) o1.1 o1.2 (fun h => hHR (F.classH_rFrame_iff.1 h)))
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg hWn (sub_nonneg.2 n0_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n0_4), mul_nonneg (htp1).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tp_pos hsm1)) hga, mul_pos ((mul_pos F.S.hp_pos F.S.km_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (mul_nonneg (mul_nonneg (htm1).le (F.S.hp_pos).le) htt) (sub_nonneg.2 n0_2), mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le (F.S.hm_pos).le) htt) (sub_nonneg.2 n0_3), mul_nonneg (mul_nonneg (mul_nonneg (htp1).le (F.S.hm_pos).le) htt) (sub_nonneg.2 n0_4), mul_nonneg ((mul_pos (mul_pos F.S.sp_pos hsm1) F.S.hp_pos)).le (sub_nonneg.2 n1_1), mul_nonneg ((mul_pos (mul_pos hsp1 hsm1) F.S.hp_pos)).le (sub_nonneg.2 n1_1), mul_nonneg ((mul_pos hsp1 F.S.km_pos)).le (sub_nonneg.2 n1_4), mul_nonneg ((mul_pos hsm1 F.S.kp_pos)).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos (mul_pos htp1 hsp1) rm)) hga, mul_pos ((mul_pos (mul_pos htp1 hsm1) hVW)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg ((mul_pos htm1 F.S.sm_pos)).le (sub_nonneg.2 n0_1), mul_nonneg (mul_nonneg (F.S.tm_pos).le htt) (sub_nonneg.2 n1_2), mul_nonneg (mul_nonneg (htm1).le htt) (sub_nonneg.2 n1_2), mul_nonneg ((mul_pos F.S.sp_pos hsp1)).le (sub_nonneg.2 n1_2), mul_nonneg ((mul_pos hsp1 hsp1)).le (sub_nonneg.2 n1_2), mul_pos ((mul_pos (mul_pos F.S.tp_pos rm) hA1)) hde, mul_pos ((mul_pos (mul_pos htp1 rm) hA1)) hde, mul_pos ((mul_pos (mul_pos hsp1 F.S.km_pos) rm)) hde, mul_pos ((mul_pos (mul_pos hsm1 F.S.kp_pos) rm)) hde]

/-- 27.74 (ii): {T_A, V, T′}, h+ ≥ d+, p (R-image) -/
theorem Frame20.om3p_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVp : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVW : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hWp : 0 ≤ -F.S.hm - F.S.km*F.S.tm + F.S.km) (hom : 0 < (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) (hHR : ¬ F.ClassHR)   :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.rFrame.dep F.rFrame.S.u_tANR 0 < F.rFrame.dep F.rFrame.S.u_tANR 6 ∨ F.rFrame.dep F.rFrame.S.u_tANR 0 < F.rFrame.dep F.rFrame.S.u_tANR 3 ∨ F.rFrame.dep F.rFrame.S.u_tANR 4 < F.rFrame.dep F.rFrame.S.u_tANR 6 ∨ F.rFrame.dep F.rFrame.S.u_tANR 4 < F.rFrame.dep F.rFrame.S.u_tANR 3) ∧ (F.rFrame.dep F.rFrame.S.u_tANR 6 < F.rFrame.dep F.rFrame.S.u_tANR 0 ∨ F.rFrame.dep F.rFrame.S.u_tANR 3 < F.rFrame.dep F.rFrame.S.u_tANR 0 ∨ F.rFrame.dep F.rFrame.S.u_tANR 6 < F.rFrame.dep F.rFrame.S.u_tANR 4 ∨ F.rFrame.dep F.rFrame.S.u_tANR 3 < F.rFrame.dep F.rFrame.S.u_tANR 4)
  · exact rupert_of_r (F.rFrame.tANR_slide (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1r]) o0.1 o0.2 (fun h => hHR (F.classH_rFrame_iff.1 h)))
  by_cases o1 : (F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 6 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 6) ∧ (F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 4 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 4)
  · exact rupert_of_r (F.rFrame.vN4_slide (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVp]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVW]) o1.1 o1.2 (fun h => hHR (F.classH_rFrame_iff.1 h)))
  by_cases o2 : (F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 6 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 6) ∧ (F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 4 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 4)
  · exact rupert_of_r (F.rFrame.tP (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1r]) o2.1 o2.2)
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos htm1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hVp).le (sub_nonneg.2 n2_4), mul_pos hVW hom, mul_nonneg hWp hom.le]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos htm1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hVp).le (sub_nonneg.2 n2_4), mul_pos hVW hom, mul_nonneg hWp hom.le]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n2_1), mul_pos F.S.kp_pos hom, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sm_pos hA1r)) hbe, mul_pos ((mul_pos hsm1 hA1r)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(sub_nonneg.2 n0_3), mul_pos F.S.sm_pos hom, mul_pos hsm1 hom]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_1), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos hsm1 F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hA1r)) hbe, mul_pos ((mul_pos hsm1 F.S.km_pos)) hga, mul_pos ((mul_pos hsm1 hA1r)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(sub_nonneg.2 n0_3), mul_pos F.S.sm_pos hom, mul_pos hsm1 hom]

/-- 27.74 (ii): {T_A, V, T′}, h+ ≥ d+, n (R-image) -/
theorem Frame20.om3n_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVp : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVW : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hWp : 0 ≤ -F.S.hm - F.S.km*F.S.tm + F.S.km) (hom : 0 < (-F.S.sm*F.S.tp + F.S.sm + F.S.tp - 1) * F.a12 + (F.S.hp*F.S.km) * F.gg) (hHR : ¬ F.ClassHR)   :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.rFrame.dep F.rFrame.S.u_tANR 0 < F.rFrame.dep F.rFrame.S.u_tANR 6 ∨ F.rFrame.dep F.rFrame.S.u_tANR 0 < F.rFrame.dep F.rFrame.S.u_tANR 3 ∨ F.rFrame.dep F.rFrame.S.u_tANR 4 < F.rFrame.dep F.rFrame.S.u_tANR 6 ∨ F.rFrame.dep F.rFrame.S.u_tANR 4 < F.rFrame.dep F.rFrame.S.u_tANR 3) ∧ (F.rFrame.dep F.rFrame.S.u_tANR 6 < F.rFrame.dep F.rFrame.S.u_tANR 0 ∨ F.rFrame.dep F.rFrame.S.u_tANR 3 < F.rFrame.dep F.rFrame.S.u_tANR 0 ∨ F.rFrame.dep F.rFrame.S.u_tANR 6 < F.rFrame.dep F.rFrame.S.u_tANR 4 ∨ F.rFrame.dep F.rFrame.S.u_tANR 3 < F.rFrame.dep F.rFrame.S.u_tANR 4)
  · exact rupert_of_r (F.rFrame.tANR_slide (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1r]) o0.1 o0.2 (fun h => hHR (F.classH_rFrame_iff.1 h)))
  by_cases o1 : (F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 6 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 6) ∧ (F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 4 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 4)
  · exact rupert_of_r (F.rFrame.vN4_slide (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVp]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVW]) o1.1 o1.2 (fun h => hHR (F.classH_rFrame_iff.1 h)))
  by_cases o2 : (F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 6 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 6) ∧ (F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 4 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 4)
  · exact rupert_of_r (F.rFrame.tP (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1r]) o2.1 o2.2)
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(sub_nonneg.2 n0_3), mul_pos F.S.tp_pos hom, mul_pos htp1 hom]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n1_4), mul_nonneg hWp hom.le, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hVp).le (sub_nonneg.2 n0_3), mul_pos hVW hom, mul_nonneg hWp hom.le]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hsm1).le (sub_nonneg.2 n0_2), mul_nonneg (hsm1).le (sub_nonneg.2 n2_1), (sub_nonneg.2 n2_2), mul_pos ((mul_pos hsm1 hsm1)) hbe, mul_pos ((mul_pos hsm1 hsm1)) hga, mul_pos ((mul_pos F.S.km_pos F.S.km_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg hWp (sub_nonneg.2 n0_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hVW).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n1_2), mul_nonneg (hA1r).le (sub_nonneg.2 n1_2), mul_nonneg (rm).le (sub_nonneg.2 n2_2), mul_nonneg (rm).le (sub_nonneg.2 n2_3), mul_nonneg (hVW).le (sub_nonneg.2 n2_3), mul_pos rm hom, mul_pos hVW hom, mul_pos ((mul_pos hsp1 rm)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg ((mul_pos htm1 F.S.sm_pos)).le (sub_nonneg.2 n0_2), mul_nonneg ((mul_pos F.S.sm_pos hsm1)).le (sub_nonneg.2 n1_1), mul_nonneg ((mul_pos hsm1 hsm1)).le (sub_nonneg.2 n1_1), mul_pos ((mul_pos (mul_pos F.S.tp_pos rm) rm)) hde, mul_pos ((mul_pos (mul_pos htp1 rm) rm)) hde, mul_pos ((mul_pos (mul_pos F.S.tm_pos F.S.km_pos) rm)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.km_pos) rm)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos rm) hA1r)) hde, mul_pos ((mul_pos (mul_pos hsp1 rm) hA1r)) hde, mul_pos ((mul_pos (mul_pos F.S.sm_pos F.S.kp_pos) rm)) hde, mul_pos ((mul_pos (mul_pos hsm1 F.S.hm_pos) rm)) hde]

/-- 27.74 (ii): {T_A, V, T′}, h+ ≥ d+, z1 (R-image) -/
theorem Frame20.om3z1_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVp : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVW : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hWp : 0 ≤ -F.S.hm - F.S.km*F.S.tm + F.S.km) (hom1 : 0 ≤ (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) (hom2 : 0 ≤ (-F.S.sm*F.S.tp + F.S.sm + F.S.tp - 1) * F.a12 + (F.S.hp*F.S.km) * F.gg) (hl : 0 < (F.S.hp*F.S.sp) * (F.a22 - F.a12) + (F.S.hp*F.S.sp - F.S.hp - F.S.kp*F.S.tp + F.S.kp) * F.a12) (hHR : ¬ F.ClassHR)   :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.rFrame.dep F.rFrame.S.u_tANR 0 < F.rFrame.dep F.rFrame.S.u_tANR 6 ∨ F.rFrame.dep F.rFrame.S.u_tANR 0 < F.rFrame.dep F.rFrame.S.u_tANR 3 ∨ F.rFrame.dep F.rFrame.S.u_tANR 4 < F.rFrame.dep F.rFrame.S.u_tANR 6 ∨ F.rFrame.dep F.rFrame.S.u_tANR 4 < F.rFrame.dep F.rFrame.S.u_tANR 3) ∧ (F.rFrame.dep F.rFrame.S.u_tANR 6 < F.rFrame.dep F.rFrame.S.u_tANR 0 ∨ F.rFrame.dep F.rFrame.S.u_tANR 3 < F.rFrame.dep F.rFrame.S.u_tANR 0 ∨ F.rFrame.dep F.rFrame.S.u_tANR 6 < F.rFrame.dep F.rFrame.S.u_tANR 4 ∨ F.rFrame.dep F.rFrame.S.u_tANR 3 < F.rFrame.dep F.rFrame.S.u_tANR 4)
  · exact rupert_of_r (F.rFrame.tANR_slide (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1r]) o0.1 o0.2 (fun h => hHR (F.classH_rFrame_iff.1 h)))
  by_cases o1 : (F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 6 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 6) ∧ (F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 4 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 4)
  · exact rupert_of_r (F.rFrame.vN4_slide (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVp]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVW]) o1.1 o1.2 (fun h => hHR (F.classH_rFrame_iff.1 h)))
  by_cases o2 : (F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 6 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 6) ∧ (F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 4 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 4)
  · exact rupert_of_r (F.rFrame.tP (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1r]) o2.1 o2.2)
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos htm1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n1_4), mul_nonneg hWp (sub_nonneg.2 n2_4), mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sm_pos hA1r)) hbe, mul_pos ((mul_pos hsm1 hA1r)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_3), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n2_4), mul_pos hsm1 hl]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_1), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos hsm1 F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hA1r)) hbe, mul_pos ((mul_pos hsm1 F.S.km_pos)) hga, mul_pos ((mul_pos hsm1 hA1r)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.hp_pos).le hom1, mul_pos hsm1 hl]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n2_1), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_4), mul_pos hsm1 hl, mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.hp_pos).le hom1, mul_pos hsm1 hl]

/-- 27.74 (ii): {T_A, V, T′}, h+ ≥ d+, z2 (R-image) -/
theorem Frame20.om3z2_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVp : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVW : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hWp : 0 ≤ -F.S.hm - F.S.km*F.S.tm + F.S.km) (hom1 : 0 ≤ (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) (hom2 : 0 ≤ (-F.S.sm*F.S.tp + F.S.sm + F.S.tp - 1) * F.a12 + (F.S.hp*F.S.km) * F.gg) (hl : 0 < (-F.S.hp*F.S.sp) * (F.a22 - F.a12) + (-F.S.hp*F.S.sp + F.S.hp + F.S.kp*F.S.tp - F.S.kp) * F.a12) (hHR : ¬ F.ClassHR)   :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.rFrame.dep F.rFrame.S.u_tANR 0 < F.rFrame.dep F.rFrame.S.u_tANR 6 ∨ F.rFrame.dep F.rFrame.S.u_tANR 0 < F.rFrame.dep F.rFrame.S.u_tANR 3 ∨ F.rFrame.dep F.rFrame.S.u_tANR 4 < F.rFrame.dep F.rFrame.S.u_tANR 6 ∨ F.rFrame.dep F.rFrame.S.u_tANR 4 < F.rFrame.dep F.rFrame.S.u_tANR 3) ∧ (F.rFrame.dep F.rFrame.S.u_tANR 6 < F.rFrame.dep F.rFrame.S.u_tANR 0 ∨ F.rFrame.dep F.rFrame.S.u_tANR 3 < F.rFrame.dep F.rFrame.S.u_tANR 0 ∨ F.rFrame.dep F.rFrame.S.u_tANR 6 < F.rFrame.dep F.rFrame.S.u_tANR 4 ∨ F.rFrame.dep F.rFrame.S.u_tANR 3 < F.rFrame.dep F.rFrame.S.u_tANR 4)
  · exact rupert_of_r (F.rFrame.tANR_slide (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1r]) o0.1 o0.2 (fun h => hHR (F.classH_rFrame_iff.1 h)))
  by_cases o1 : (F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 6 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 6) ∧ (F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 4 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 4)
  · exact rupert_of_r (F.rFrame.vN4_slide (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVp]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVW]) o1.1 o1.2 (fun h => hHR (F.classH_rFrame_iff.1 h)))
  by_cases o2 : (F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 6 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 6) ∧ (F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 4 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 4)
  · exact rupert_of_r (F.rFrame.tP (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1r]) o2.1 o2.2)
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_1), mul_pos hsm1 hl, mul_pos ((mul_pos hsm1 F.S.hp_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_4), mul_pos hsm1 hl]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_1), mul_pos hsm1 hl, mul_pos ((mul_pos hsm1 F.S.hp_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_4), mul_pos hsm1 hl]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hsp1).le (sub_nonneg.2 n0_2), mul_nonneg (hsm1).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n0_4), mul_nonneg (hsp1).le (sub_nonneg.2 n0_4), mul_nonneg (hsp1).le (sub_nonneg.2 n2_1), mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n2_1), mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n2_4), mul_nonneg (htp1).le (sub_nonneg.2 n2_4), mul_pos ((mul_pos hsm1 hsm1)) hbe, mul_pos ((mul_pos hsm1 hsm1)) hga, mul_pos ((mul_pos F.S.km_pos F.S.km_pos)) hde, mul_pos ((mul_pos F.S.km_pos hA1r)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg hWp (sub_nonneg.2 n0_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n2_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_1), mul_pos ((mul_pos hsm1 F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hA1r)) hbe, mul_pos ((mul_pos hsm1 F.S.km_pos)) hga, mul_pos ((mul_pos hsm1 hA1r)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg ((mul_pos htm1 F.S.sm_pos)).le (sub_nonneg.2 n0_2), mul_nonneg (hsm1).le (sub_nonneg.2 n1_1), mul_pos ((mul_pos (mul_pos F.S.tp_pos rm) rm)) hde, mul_pos ((mul_pos (mul_pos htp1 rm) rm)) hde, mul_pos ((mul_pos (mul_pos F.S.tm_pos F.S.km_pos) rm)) hde, mul_pos ((mul_pos (mul_pos F.S.tm_pos rm) hA1r)) hde, mul_pos ((mul_pos (mul_pos htm1 rm) hA1r)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.km_pos) rm)) hde, mul_pos ((mul_pos (mul_pos F.S.sm_pos F.S.kp_pos) rm)) hde, mul_pos ((mul_pos (mul_pos hsm1 F.S.hm_pos) rm)) hde]

/-- 27.76 N4 p (R-image) -/
theorem Frame20.om4ap_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hA1R : 0 < F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) (hVpR : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm - F.S.kp*F.S.tm) (hVWR : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.sp + F.S.hp*F.S.tm - F.S.hp - F.S.kp*F.S.tm + F.S.kp) (hKb : 0 < F.S.hp*F.S.sp - F.S.hp + F.S.kp) (hss : 0 < -F.S.tm + F.S.tp) (hnu : 0 < (-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 + (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg) (hH : ¬ F.ClassH)  :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 6 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 6) ∧ (F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 4 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 4)
  · exact rupert_of_r (F.rFrame.tP (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1r]) o0.1 o0.2)
  by_cases o1 : (F.dep F.S.u_tA 0 < F.dep F.S.u_tA 6 ∨ F.dep F.S.u_tA 0 < F.dep F.S.u_tA 5 ∨ F.dep F.S.u_tA 4 < F.dep F.S.u_tA 6 ∨ F.dep F.S.u_tA 4 < F.dep F.S.u_tA 5) ∧ (F.dep F.S.u_tA 6 < F.dep F.S.u_tA 0 ∨ F.dep F.S.u_tA 5 < F.dep F.S.u_tA 0 ∨ F.dep F.S.u_tA 6 < F.dep F.S.u_tA 4 ∨ F.dep F.S.u_tA 5 < F.dep F.S.u_tA 4)
  · exact F.tA (by linarith only [hA1R]) o1.1 o1.2
  by_cases o2 : (F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 3 ∨ F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 6 ∨ F.dep F.S.u_vN4 4 < F.dep F.S.u_vN4 3 ∨ F.dep F.S.u_vN4 4 < F.dep F.S.u_vN4 6) ∧ (F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 0 ∨ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 0 ∨ F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 4 ∨ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 4)
  · exact F.vN4_slide hx (by linarith only [hVpR]) (by linarith only [hVWR]) o2.1 o2.2 hH
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hA1r hss)) hbe, mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hA1r hss)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hVpR)) hbe, mul_pos ((mul_pos hA1r hss)) hbe, mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hA1r hss)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n1_4), mul_pos F.S.hp_pos hnu, mul_pos ((mul_pos htp1 hKb)) hga, mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(sub_nonneg.2 n0_3), mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n1_4), hnu, mul_pos ((mul_pos F.S.sp_pos hsm1)) hbe, mul_pos ((mul_pos htp1 F.S.sp_pos)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hsp1).le (sub_nonneg.2 n0_3), mul_pos htp1 hnu, mul_pos F.S.tm_pos hnu, mul_pos hss hnu]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n2_4), mul_pos hVpR hnu, mul_pos hKb hnu]

/-- 27.76 N4 n (R-image) -/
theorem Frame20.om4an_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hA1R : 0 < F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) (hVpR : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm - F.S.kp*F.S.tm) (hVWR : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.sp + F.S.hp*F.S.tm - F.S.hp - F.S.kp*F.S.tm + F.S.kp) (hKb : 0 < F.S.hp*F.S.sp - F.S.hp + F.S.kp) (hss : 0 < -F.S.tm + F.S.tp) (hnu : 0 < (F.S.sm*F.S.sp*F.S.tp - F.S.sm*F.S.tp - F.S.sp*F.S.tp + F.S.tp) * F.a12 + (-F.S.hp*F.S.km*F.S.sp + F.S.hp*F.S.km - F.S.km*F.S.kp) * F.gg) (hH : ¬ F.ClassH)  :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 6 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 6) ∧ (F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 4 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 4)
  · exact rupert_of_r (F.rFrame.tP (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1r]) o0.1 o0.2)
  by_cases o1 : (F.dep F.S.u_tA 0 < F.dep F.S.u_tA 6 ∨ F.dep F.S.u_tA 0 < F.dep F.S.u_tA 5 ∨ F.dep F.S.u_tA 4 < F.dep F.S.u_tA 6 ∨ F.dep F.S.u_tA 4 < F.dep F.S.u_tA 5) ∧ (F.dep F.S.u_tA 6 < F.dep F.S.u_tA 0 ∨ F.dep F.S.u_tA 5 < F.dep F.S.u_tA 0 ∨ F.dep F.S.u_tA 6 < F.dep F.S.u_tA 4 ∨ F.dep F.S.u_tA 5 < F.dep F.S.u_tA 4)
  · exact F.tA (by linarith only [hA1R]) o1.1 o1.2
  by_cases o2 : (F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 3 ∨ F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 6 ∨ F.dep F.S.u_vN4 4 < F.dep F.S.u_vN4 3 ∨ F.dep F.S.u_vN4 4 < F.dep F.S.u_vN4 6) ∧ (F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 0 ∨ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 0 ∨ F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 4 ∨ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 4)
  · exact F.vN4_slide hx (by linarith only [hVpR]) (by linarith only [hVWR]) o2.1 o2.2 hH
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hVpR)) hbe, mul_pos ((mul_pos htp1 F.S.kp_pos)) hga, mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hA1r hss)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hA1r hss)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hA1r hss)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hVpR).le (sub_nonneg.2 n0_4), mul_nonneg (hVWR).le (sub_nonneg.2 n1_4), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_4), mul_pos ((mul_pos htp1 hVpR)) hga, mul_pos ((mul_pos htp1 hKb)) hga, mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n0_4), mul_nonneg (htp1).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n1_4), mul_nonneg (htp1).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos htp1 F.S.sp_pos)) hga, mul_pos ((mul_pos htp1 hsp1)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n2_4), mul_nonneg (hsm1).le (sub_nonneg.2 n2_4), mul_pos htp1 hnu, mul_pos F.S.tm_pos hnu, mul_pos hss hnu]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg ((mul_pos F.S.tm_pos hsp1)).le (sub_nonneg.2 n1_1), mul_nonneg ((mul_pos hsp1 hss)).le (sub_nonneg.2 n1_1), mul_nonneg ((mul_pos htp1 F.S.sm_pos)).le (sub_nonneg.2 n2_2), mul_nonneg ((mul_pos htp1 hsm1)).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos (mul_pos htp1 F.S.hp_pos) rp)) hde, mul_pos ((mul_pos (mul_pos htp1 F.S.hm_pos) rp)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos rp) hA1R)) hde, mul_pos ((mul_pos (mul_pos hsp1 rp) hA1R)) hde, mul_pos ((mul_pos (mul_pos F.S.hp_pos rp) hss)) hde]

/-- 27.76 N4 z1 (R-image) -/
theorem Frame20.om4az1_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hA1R : 0 < F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) (hVpR : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm - F.S.kp*F.S.tm) (hVWR : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.sp + F.S.hp*F.S.tm - F.S.hp - F.S.kp*F.S.tm + F.S.kp) (hKb : 0 < F.S.hp*F.S.sp - F.S.hp + F.S.kp) (hss : 0 < -F.S.tm + F.S.tp) (hnu1 : 0 ≤ (-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 + (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg) (hnu2 : 0 ≤ (F.S.sm*F.S.sp*F.S.tp - F.S.sm*F.S.tp - F.S.sp*F.S.tp + F.S.tp) * F.a12 + (-F.S.hp*F.S.km*F.S.sp + F.S.hp*F.S.km - F.S.km*F.S.kp) * F.gg) (hl : 0 < (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * (F.a22 - F.a12) + (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * F.a12 + (-F.S.km*F.S.kp) * F.gg) (hH : ¬ F.ClassH)  :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 6 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 6) ∧ (F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 4 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 4)
  · exact rupert_of_r (F.rFrame.tP (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1r]) o0.1 o0.2)
  by_cases o1 : (F.dep F.S.u_tA 0 < F.dep F.S.u_tA 6 ∨ F.dep F.S.u_tA 0 < F.dep F.S.u_tA 5 ∨ F.dep F.S.u_tA 4 < F.dep F.S.u_tA 6 ∨ F.dep F.S.u_tA 4 < F.dep F.S.u_tA 5) ∧ (F.dep F.S.u_tA 6 < F.dep F.S.u_tA 0 ∨ F.dep F.S.u_tA 5 < F.dep F.S.u_tA 0 ∨ F.dep F.S.u_tA 6 < F.dep F.S.u_tA 4 ∨ F.dep F.S.u_tA 5 < F.dep F.S.u_tA 4)
  · exact F.tA (by linarith only [hA1R]) o1.1 o1.2
  by_cases o2 : (F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 3 ∨ F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 6 ∨ F.dep F.S.u_vN4 4 < F.dep F.S.u_vN4 3 ∨ F.dep F.S.u_vN4 4 < F.dep F.S.u_vN4 6) ∧ (F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 0 ∨ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 0 ∨ F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 4 ∨ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 4)
  · exact F.vN4_slide hx (by linarith only [hVpR]) (by linarith only [hVWR]) o2.1 o2.2 hH
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hA1r hss)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hA1r hss)) hbe, mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hA1r hss)) hbe, mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hVpR).le (sub_nonneg.2 n0_4), mul_nonneg (hVWR).le (sub_nonneg.2 n1_4), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_4), mul_pos ((mul_pos htp1 hVWR)) hga, mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n1_4), mul_nonneg (F.S.hp_pos).le hnu1, mul_pos ((mul_pos htp1 hKb)) hga, mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n2_4), mul_nonneg (htm1).le (sub_nonneg.2 n2_4), mul_nonneg (hss).le hnu2, mul_pos F.S.sp_pos hl]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.sm_pos).le hnu1, mul_nonneg (hsm1).le hnu1, mul_pos F.S.sp_pos hl]

/-- 27.76 N4 z2 (R-image) -/
theorem Frame20.om4az2_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hA1R : 0 < F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) (hVpR : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm - F.S.kp*F.S.tm) (hVWR : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.sp + F.S.hp*F.S.tm - F.S.hp - F.S.kp*F.S.tm + F.S.kp) (hKb : 0 < F.S.hp*F.S.sp - F.S.hp + F.S.kp) (hss : 0 < -F.S.tm + F.S.tp) (hnu1 : 0 ≤ (-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 + (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg) (hnu2 : 0 ≤ (F.S.sm*F.S.sp*F.S.tp - F.S.sm*F.S.tp - F.S.sp*F.S.tp + F.S.tp) * F.a12 + (-F.S.hp*F.S.km*F.S.sp + F.S.hp*F.S.km - F.S.km*F.S.kp) * F.gg) (hl : 0 < (-F.S.sm*F.S.sp + F.S.sm + F.S.sp - 1) * (F.a22 - F.a12) + (-F.S.sm*F.S.sp + F.S.sm + F.S.sp - 1) * F.a12 + (F.S.km*F.S.kp) * F.gg) (hH : ¬ F.ClassH)  :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 6 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 6) ∧ (F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 4 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 4)
  · exact rupert_of_r (F.rFrame.tP (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1r]) o0.1 o0.2)
  by_cases o1 : (F.dep F.S.u_tA 0 < F.dep F.S.u_tA 6 ∨ F.dep F.S.u_tA 0 < F.dep F.S.u_tA 5 ∨ F.dep F.S.u_tA 4 < F.dep F.S.u_tA 6 ∨ F.dep F.S.u_tA 4 < F.dep F.S.u_tA 5) ∧ (F.dep F.S.u_tA 6 < F.dep F.S.u_tA 0 ∨ F.dep F.S.u_tA 5 < F.dep F.S.u_tA 0 ∨ F.dep F.S.u_tA 6 < F.dep F.S.u_tA 4 ∨ F.dep F.S.u_tA 5 < F.dep F.S.u_tA 4)
  · exact F.tA (by linarith only [hA1R]) o1.1 o1.2
  by_cases o2 : (F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 3 ∨ F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 6 ∨ F.dep F.S.u_vN4 4 < F.dep F.S.u_vN4 3 ∨ F.dep F.S.u_vN4 4 < F.dep F.S.u_vN4 6) ∧ (F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 0 ∨ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 0 ∨ F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 4 ∨ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 4)
  · exact F.vN4_slide hx (by linarith only [hVpR]) (by linarith only [hVWR]) o2.1 o2.2 hH
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_4), mul_pos F.S.hp_pos hl, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hVpR)) hbe, mul_pos ((mul_pos hA1r hss)) hbe, mul_pos ((mul_pos htp1 F.S.kp_pos)) hga, mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_4), mul_pos F.S.hp_pos hl, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hVpR)) hbe, mul_pos ((mul_pos hA1r hss)) hbe, mul_pos ((mul_pos htp1 F.S.kp_pos)) hga, mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.hp_pos hl, mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hA1r hss)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (rm).le (sub_nonneg.2 n0_3), mul_nonneg (rm).le (sub_nonneg.2 n1_4), mul_pos rm hl, mul_pos ((mul_pos hsm1 rm)) hbe, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (rm).le (sub_nonneg.2 n0_3), mul_nonneg (rm).le (sub_nonneg.2 n1_4), mul_pos rm hl, mul_pos ((mul_pos hsm1 rm)) hbe, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_1), mul_pos hVpR hl, mul_pos hKb hl]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hA1R).le (sub_nonneg.2 n0_1), mul_pos hA1R hl]

/-- 27.76 Rv p (R-image) -/
theorem Frame20.om4bp_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hA1R : 0 < F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) (hVR : 0 < F.S.hm*F.S.sp*F.S.tp - F.S.hm*F.S.tp + F.S.hp*F.S.sp*F.S.tm - F.S.hp*F.S.tm + F.S.kp*F.S.tm) (hKb : 0 < F.S.hp*F.S.sp - F.S.hp + F.S.kp) (hnu : 0 < (-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 + (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg)   :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 6 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 6) ∧ (F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 4 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 4)
  · exact rupert_of_r (F.rFrame.tP (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1r]) o0.1 o0.2)
  by_cases o1 : (F.dep F.S.u_tA 0 < F.dep F.S.u_tA 6 ∨ F.dep F.S.u_tA 0 < F.dep F.S.u_tA 5 ∨ F.dep F.S.u_tA 4 < F.dep F.S.u_tA 6 ∨ F.dep F.S.u_tA 4 < F.dep F.S.u_tA 5) ∧ (F.dep F.S.u_tA 6 < F.dep F.S.u_tA 0 ∨ F.dep F.S.u_tA 5 < F.dep F.S.u_tA 0 ∨ F.dep F.S.u_tA 6 < F.dep F.S.u_tA 4 ∨ F.dep F.S.u_tA 5 < F.dep F.S.u_tA 4)
  · exact F.tA (by linarith only [hA1R]) o1.1 o1.2
  by_cases o2 : (F.dep F.S.u_vRv 0 < F.dep F.S.u_vRv 6 ∨ F.dep F.S.u_vRv 0 < F.dep F.S.u_vRv 5 ∨ F.dep F.S.u_vRv 4 < F.dep F.S.u_vRv 6 ∨ F.dep F.S.u_vRv 4 < F.dep F.S.u_vRv 5) ∧ (F.dep F.S.u_vRv 6 < F.dep F.S.u_vRv 0 ∨ F.dep F.S.u_vRv 5 < F.dep F.S.u_vRv 0 ∨ F.dep F.S.u_vRv 6 < F.dep F.S.u_vRv 4 ∨ F.dep F.S.u_vRv 5 < F.dep F.S.u_vRv 4)
  · exact F.vRv (by linarith only [hKb]) (by linarith only [hVR]) o2.1 o2.2
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.hp_pos hnu, mul_pos ((mul_pos F.S.tp_pos rp)) hga, mul_pos ((mul_pos htp1 rp)) hga, mul_pos ((mul_pos htp1 hKb)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n1_4), mul_pos F.S.hp_pos hnu, mul_pos ((mul_pos htp1 hKb)) hga, mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.hp_pos hnu, mul_pos ((mul_pos F.S.tp_pos rp)) hga, mul_pos ((mul_pos htp1 rp)) hga, mul_pos ((mul_pos htp1 hKb)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hsp1).le (sub_nonneg.2 n0_3), mul_pos F.S.sp_pos hnu, mul_pos hsp1 hnu]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n1_1), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos F.S.tp_pos rp)) hal, mul_pos ((mul_pos F.S.tp_pos rp)) hga, mul_pos ((mul_pos htp1 hKb)) hga]

/-- 27.76 Rv n (R-image) -/
theorem Frame20.om4bn_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hA1R : 0 < F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) (hVR : 0 < F.S.hm*F.S.sp*F.S.tp - F.S.hm*F.S.tp + F.S.hp*F.S.sp*F.S.tm - F.S.hp*F.S.tm + F.S.kp*F.S.tm) (hKb : 0 < F.S.hp*F.S.sp - F.S.hp + F.S.kp) (hnu : 0 < (F.S.sm*F.S.sp*F.S.tp - F.S.sm*F.S.tp - F.S.sp*F.S.tp + F.S.tp) * F.a12 + (-F.S.hp*F.S.km*F.S.sp + F.S.hp*F.S.km - F.S.km*F.S.kp) * F.gg)   :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 6 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 6) ∧ (F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 4 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 4)
  · exact rupert_of_r (F.rFrame.tP (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1r]) o0.1 o0.2)
  by_cases o1 : (F.dep F.S.u_tA 0 < F.dep F.S.u_tA 6 ∨ F.dep F.S.u_tA 0 < F.dep F.S.u_tA 5 ∨ F.dep F.S.u_tA 4 < F.dep F.S.u_tA 6 ∨ F.dep F.S.u_tA 4 < F.dep F.S.u_tA 5) ∧ (F.dep F.S.u_tA 6 < F.dep F.S.u_tA 0 ∨ F.dep F.S.u_tA 5 < F.dep F.S.u_tA 0 ∨ F.dep F.S.u_tA 6 < F.dep F.S.u_tA 4 ∨ F.dep F.S.u_tA 5 < F.dep F.S.u_tA 4)
  · exact F.tA (by linarith only [hA1R]) o1.1 o1.2
  by_cases o2 : (F.dep F.S.u_vRv 0 < F.dep F.S.u_vRv 6 ∨ F.dep F.S.u_vRv 0 < F.dep F.S.u_vRv 5 ∨ F.dep F.S.u_vRv 4 < F.dep F.S.u_vRv 6 ∨ F.dep F.S.u_vRv 4 < F.dep F.S.u_vRv 5) ∧ (F.dep F.S.u_vRv 6 < F.dep F.S.u_vRv 0 ∨ F.dep F.S.u_vRv 5 < F.dep F.S.u_vRv 0 ∨ F.dep F.S.u_vRv 6 < F.dep F.S.u_vRv 4 ∨ F.dep F.S.u_vRv 5 < F.dep F.S.u_vRv 4)
  · exact F.vRv (by linarith only [hKb]) (by linarith only [hVR]) o2.1 o2.2
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos htp1 F.S.kp_pos)) hga, mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(sub_nonneg.2 n0_4), mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n1_4), mul_nonneg (htp1).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.tp_pos htp1)) hga, mul_pos ((mul_pos htp1 htp1)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n1_4), mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n2_4), mul_nonneg (hsp1).le (sub_nonneg.2 n2_4), mul_pos ((mul_pos hsp1 F.S.sm_pos)) hga, mul_pos ((mul_pos F.S.kp_pos F.S.km_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(sub_nonneg.2 n2_3), mul_pos F.S.sp_pos hnu, mul_pos hsp1 hnu]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n1_1), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos F.S.tp_pos rp)) hal, mul_pos ((mul_pos F.S.tp_pos rp)) hga, mul_pos ((mul_pos htp1 hKb)) hga]

/-- 27.76 Rv z1 (R-image) -/
theorem Frame20.om4bz1_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hA1R : 0 < F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) (hVR : 0 < F.S.hm*F.S.sp*F.S.tp - F.S.hm*F.S.tp + F.S.hp*F.S.sp*F.S.tm - F.S.hp*F.S.tm + F.S.kp*F.S.tm) (hKb : 0 < F.S.hp*F.S.sp - F.S.hp + F.S.kp) (hnu1 : 0 ≤ (-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 + (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg) (hnu2 : 0 ≤ (F.S.sm*F.S.sp*F.S.tp - F.S.sm*F.S.tp - F.S.sp*F.S.tp + F.S.tp) * F.a12 + (-F.S.hp*F.S.km*F.S.sp + F.S.hp*F.S.km - F.S.km*F.S.kp) * F.gg) (hl : 0 < (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * (F.a22 - F.a12) + (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * F.a12 + (-F.S.km*F.S.kp) * F.gg)   :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 6 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 6) ∧ (F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 4 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 4)
  · exact rupert_of_r (F.rFrame.tP (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1r]) o0.1 o0.2)
  by_cases o1 : (F.dep F.S.u_tA 0 < F.dep F.S.u_tA 6 ∨ F.dep F.S.u_tA 0 < F.dep F.S.u_tA 5 ∨ F.dep F.S.u_tA 4 < F.dep F.S.u_tA 6 ∨ F.dep F.S.u_tA 4 < F.dep F.S.u_tA 5) ∧ (F.dep F.S.u_tA 6 < F.dep F.S.u_tA 0 ∨ F.dep F.S.u_tA 5 < F.dep F.S.u_tA 0 ∨ F.dep F.S.u_tA 6 < F.dep F.S.u_tA 4 ∨ F.dep F.S.u_tA 5 < F.dep F.S.u_tA 4)
  · exact F.tA (by linarith only [hA1R]) o1.1 o1.2
  by_cases o2 : (F.dep F.S.u_vRv 0 < F.dep F.S.u_vRv 6 ∨ F.dep F.S.u_vRv 0 < F.dep F.S.u_vRv 5 ∨ F.dep F.S.u_vRv 4 < F.dep F.S.u_vRv 6 ∨ F.dep F.S.u_vRv 4 < F.dep F.S.u_vRv 5) ∧ (F.dep F.S.u_vRv 6 < F.dep F.S.u_vRv 0 ∨ F.dep F.S.u_vRv 5 < F.dep F.S.u_vRv 0 ∨ F.dep F.S.u_vRv 6 < F.dep F.S.u_vRv 4 ∨ F.dep F.S.u_vRv 5 < F.dep F.S.u_vRv 4)
  · exact F.vRv (by linarith only [hKb]) (by linarith only [hVR]) o2.1 o2.2
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hKb).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sm_pos hA1r)) hbe, mul_pos ((mul_pos hsm1 hA1r)) hbe, mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hsp1).le (sub_nonneg.2 n0_1), mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n0_2), mul_nonneg (hsp1).le (sub_nonneg.2 n0_4), (sub_nonneg.2 n2_4), mul_pos ((mul_pos F.S.sm_pos hsm1)) hbe, mul_pos ((mul_pos hsm1 hsm1)) hbe, mul_pos ((mul_pos F.S.tp_pos hsp1)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n1_4), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_3), mul_pos ((mul_pos htp1 hKb)) hga, mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_4), mul_nonneg (F.S.hp_pos).le hnu1, mul_pos ((mul_pos F.S.tp_pos rp)) hga, mul_pos ((mul_pos htp1 rp)) hga, mul_pos ((mul_pos htp1 hKb)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n2_3), mul_nonneg (hsm1).le (sub_nonneg.2 n2_3), mul_pos F.S.sp_pos hl]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n1_1), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos F.S.tp_pos rp)) hal, mul_pos ((mul_pos F.S.tp_pos rp)) hga, mul_pos ((mul_pos htp1 hKb)) hga]

/-- 27.76 Rv z2 (R-image) -/
theorem Frame20.om4bz2_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hA1R : 0 < F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) (hVR : 0 < F.S.hm*F.S.sp*F.S.tp - F.S.hm*F.S.tp + F.S.hp*F.S.sp*F.S.tm - F.S.hp*F.S.tm + F.S.kp*F.S.tm) (hKb : 0 < F.S.hp*F.S.sp - F.S.hp + F.S.kp) (hnu1 : 0 ≤ (-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 + (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg) (hnu2 : 0 ≤ (F.S.sm*F.S.sp*F.S.tp - F.S.sm*F.S.tp - F.S.sp*F.S.tp + F.S.tp) * F.a12 + (-F.S.hp*F.S.km*F.S.sp + F.S.hp*F.S.km - F.S.km*F.S.kp) * F.gg) (hl : 0 < (-F.S.sm*F.S.sp + F.S.sm + F.S.sp - 1) * (F.a22 - F.a12) + (-F.S.sm*F.S.sp + F.S.sm + F.S.sp - 1) * F.a12 + (F.S.km*F.S.kp) * F.gg)   :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 1 < F.rFrame.dep F.rFrame.S.u_tP 6 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 3 ∨ F.rFrame.dep F.rFrame.S.u_tP 4 < F.rFrame.dep F.rFrame.S.u_tP 6) ∧ (F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 1 ∨ F.rFrame.dep F.rFrame.S.u_tP 3 < F.rFrame.dep F.rFrame.S.u_tP 4 ∨ F.rFrame.dep F.rFrame.S.u_tP 6 < F.rFrame.dep F.rFrame.S.u_tP 4)
  · exact rupert_of_r (F.rFrame.tP (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1r]) o0.1 o0.2)
  by_cases o1 : (F.dep F.S.u_tA 0 < F.dep F.S.u_tA 6 ∨ F.dep F.S.u_tA 0 < F.dep F.S.u_tA 5 ∨ F.dep F.S.u_tA 4 < F.dep F.S.u_tA 6 ∨ F.dep F.S.u_tA 4 < F.dep F.S.u_tA 5) ∧ (F.dep F.S.u_tA 6 < F.dep F.S.u_tA 0 ∨ F.dep F.S.u_tA 5 < F.dep F.S.u_tA 0 ∨ F.dep F.S.u_tA 6 < F.dep F.S.u_tA 4 ∨ F.dep F.S.u_tA 5 < F.dep F.S.u_tA 4)
  · exact F.tA (by linarith only [hA1R]) o1.1 o1.2
  by_cases o2 : (F.dep F.S.u_vRv 0 < F.dep F.S.u_vRv 6 ∨ F.dep F.S.u_vRv 0 < F.dep F.S.u_vRv 5 ∨ F.dep F.S.u_vRv 4 < F.dep F.S.u_vRv 6 ∨ F.dep F.S.u_vRv 4 < F.dep F.S.u_vRv 5) ∧ (F.dep F.S.u_vRv 6 < F.dep F.S.u_vRv 0 ∨ F.dep F.S.u_vRv 5 < F.dep F.S.u_vRv 0 ∨ F.dep F.S.u_vRv 6 < F.dep F.S.u_vRv 4 ∨ F.dep F.S.u_vRv 5 < F.dep F.S.u_vRv 4)
  · exact F.vRv (by linarith only [hKb]) (by linarith only [hVR]) o2.1 o2.2
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n1_1), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos F.S.tp_pos rp)) hal, mul_pos ((mul_pos F.S.tp_pos rp)) hga, mul_pos ((mul_pos htp1 hKb)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (rp).le (sub_nonneg.2 n0_3), mul_nonneg (rp).le (sub_nonneg.2 n1_4), mul_pos rp hl, mul_pos ((mul_pos hsm1 rp)) hbe, mul_pos ((mul_pos htp1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_4), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_3), mul_pos F.S.hp_pos hl, mul_pos hKb hl, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos htm1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos htp1 F.S.kp_pos)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(sub_nonneg.2 n0_1), mul_pos F.S.tm_pos hl, mul_pos htm1 hl]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hKb).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_4), mul_pos hKb hl, mul_pos ((mul_pos hsm1 hKb)) hbe, mul_pos ((mul_pos htp1 hKb)) hga, mul_pos ((mul_pos F.S.sm_pos rp)) hga]

/-- family A, T1 (⟨u1,u2⟩ > 0) (R-image) -/
theorem Frame20.famA1_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1 : 0 < F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) (hA2 : 0 < -F.S.hp*F.S.sp + F.S.km*F.S.sp*F.S.tp + F.S.kp*F.S.sm*F.S.tp) (hA3 : 0 < F.S.hp*F.S.sp - F.S.hp - F.S.km*F.S.sp*F.S.tp + F.S.km*F.S.tp - F.S.kp*F.S.sm*F.S.tp + F.S.kp) (hg : 0 < (F.S.sm^2 - F.S.sm) * (F.a22 - F.a12) + (F.S.sm^2 - 2*F.S.sm + 1) * F.a12 + (F.S.km^2) * F.gg)   :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.rFrame.dep F.rFrame.S.u_tA 0 < F.rFrame.dep F.rFrame.S.u_tA 6 ∨ F.rFrame.dep F.rFrame.S.u_tA 0 < F.rFrame.dep F.rFrame.S.u_tA 5 ∨ F.rFrame.dep F.rFrame.S.u_tA 4 < F.rFrame.dep F.rFrame.S.u_tA 6 ∨ F.rFrame.dep F.rFrame.S.u_tA 4 < F.rFrame.dep F.rFrame.S.u_tA 5) ∧ (F.rFrame.dep F.rFrame.S.u_tA 6 < F.rFrame.dep F.rFrame.S.u_tA 0 ∨ F.rFrame.dep F.rFrame.S.u_tA 5 < F.rFrame.dep F.rFrame.S.u_tA 0 ∨ F.rFrame.dep F.rFrame.S.u_tA 6 < F.rFrame.dep F.rFrame.S.u_tA 4 ∨ F.rFrame.dep F.rFrame.S.u_tA 5 < F.rFrame.dep F.rFrame.S.u_tA 4)
  · exact rupert_of_r (F.rFrame.tA (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1]) o0.1 o0.2)
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  rcases o0 with n0 | n0
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tA] at n0_1 n0_2 n0_3 n0_4
    linarith only [mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n0_3), mul_nonneg (htp1).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.hp_pos F.S.km_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tA] at n0_1 n0_2 n0_3 n0_4
    linarith only [mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hsp1).le (sub_nonneg.2 n0_1), mul_pos F.S.tp_pos hg, mul_pos htp1 hg]

/-- family A, T2 (⟨u1,u2⟩ ≤ 0) (R-image) -/
theorem Frame20.famA2_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1 : 0 < F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) (hA2 : 0 < -F.S.hp*F.S.sp + F.S.km*F.S.sp*F.S.tp + F.S.kp*F.S.sm*F.S.tp) (hA3 : 0 < F.S.hp*F.S.sp - F.S.hp - F.S.km*F.S.sp*F.S.tp + F.S.km*F.S.tp - F.S.kp*F.S.sm*F.S.tp + F.S.kp) (hg : 0 ≤ (-F.S.sm^2 + F.S.sm) * (F.a22 - F.a12) + (-F.S.sm^2 + 2*F.S.sm - 1) * F.a12 + (-F.S.km^2) * F.gg)   :
    IsRupert (Finset.univ.image x) := by
  have hal : 0 < F.a11 - F.a12 := sub_pos.2 hα
  have hbe : 0 < F.a22 - F.a12 := sub_pos.2 hβ
  have hga : 0 < F.a12 := F.A12_pos
  have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  by_cases o0 : (F.rFrame.dep F.rFrame.S.u_yT2 1 < F.rFrame.dep F.rFrame.S.u_yT2 3 ∨ F.rFrame.dep F.rFrame.S.u_yT2 1 < F.rFrame.dep F.rFrame.S.u_yT2 0 ∨ F.rFrame.dep F.rFrame.S.u_yT2 2 < F.rFrame.dep F.rFrame.S.u_yT2 0 ∨ F.rFrame.dep F.rFrame.S.u_yT2 2 < F.rFrame.dep F.rFrame.S.u_yT2 5) ∧ (F.rFrame.dep F.rFrame.S.u_yT2 0 < F.rFrame.dep F.rFrame.S.u_yT2 1 ∨ F.rFrame.dep F.rFrame.S.u_yT2 0 < F.rFrame.dep F.rFrame.S.u_yT2 2 ∨ F.rFrame.dep F.rFrame.S.u_yT2 5 < F.rFrame.dep F.rFrame.S.u_yT2 2 ∨ F.rFrame.dep F.rFrame.S.u_yT2 5 < F.rFrame.dep F.rFrame.S.u_yT2 3) ∧ (F.rFrame.dep F.rFrame.S.u_yT2 2 < F.rFrame.dep F.rFrame.S.u_yT2 0 ∨ F.rFrame.dep F.rFrame.S.u_yT2 2 < F.rFrame.dep F.rFrame.S.u_yT2 5 ∨ F.rFrame.dep F.rFrame.S.u_yT2 3 < F.rFrame.dep F.rFrame.S.u_yT2 5 ∨ F.rFrame.dep F.rFrame.S.u_yT2 3 < F.rFrame.dep F.rFrame.S.u_yT2 1) ∧ (F.rFrame.dep F.rFrame.S.u_yT2 5 < F.rFrame.dep F.rFrame.S.u_yT2 2 ∨ F.rFrame.dep F.rFrame.S.u_yT2 5 < F.rFrame.dep F.rFrame.S.u_yT2 3 ∨ F.rFrame.dep F.rFrame.S.u_yT2 1 < F.rFrame.dep F.rFrame.S.u_yT2 3 ∨ F.rFrame.dep F.rFrame.S.u_yT2 1 < F.rFrame.dep F.rFrame.S.u_yT2 0) ∧ (F.rFrame.dep F.rFrame.S.u_yT2 3 < F.rFrame.dep F.rFrame.S.u_yT2 5 ∨ F.rFrame.dep F.rFrame.S.u_yT2 3 < F.rFrame.dep F.rFrame.S.u_yT2 1 ∨ F.rFrame.dep F.rFrame.S.u_yT2 0 < F.rFrame.dep F.rFrame.S.u_yT2 1 ∨ F.rFrame.dep F.rFrame.S.u_yT2 0 < F.rFrame.dep F.rFrame.S.u_yT2 2)
  · exact rupert_of_r (F.rFrame.yT2 (by simp only [rFrame_S, Shape20.swap]; linarith only [hA2]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hA3]) o0.1 o0.2.1 o0.2.2.1 o0.2.2.2.1 o0.2.2.2.2)
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  rcases o0 with n0 | n0 | n0 | n0 | n0
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_yT2] at n0_1 n0_2 n0_3 n0_4
    linarith only [mul_nonneg ((mul_pos F.S.tm_pos F.S.sm_pos)).le (sub_nonneg.2 n0_2), mul_nonneg ((mul_pos htm1 F.S.sm_pos)).le (sub_nonneg.2 n0_2), mul_nonneg (hsm1).le (sub_nonneg.2 n0_3), mul_pos ((mul_pos (mul_pos F.S.tm_pos F.S.sp_pos) hsm1)) hal, mul_pos ((mul_pos (mul_pos F.S.tm_pos hsp1) hsm1)) hal, mul_pos ((mul_pos (mul_pos F.S.tm_pos hsm1) hsm1)) hga, mul_pos ((mul_pos (mul_pos F.S.tp_pos rm) rm)) hde, mul_pos ((mul_pos (mul_pos htp1 rm) rm)) hde, mul_pos ((mul_pos (mul_pos F.S.tm_pos F.S.km_pos) F.S.km_pos)) hde, mul_pos ((mul_pos (mul_pos F.S.tm_pos F.S.km_pos) rm)) hde, mul_pos ((mul_pos (mul_pos hsm1 F.S.hm_pos) rm)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_yT2] at n0_1 n0_2 n0_3 n0_4
    linarith only [mul_nonneg (hsm1).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.sp_pos).le hg, mul_pos ((mul_pos F.S.km_pos hA1)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_yT2] at n0_1 n0_2 n0_3 n0_4
    linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.kp_pos F.S.km_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_yT2] at n0_1 n0_2 n0_3 n0_4
    linarith only [mul_nonneg (hsm1).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.sp_pos).le hg, mul_pos ((mul_pos F.S.km_pos hA1)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4
    simp only [rFrame_dep, C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_yT2] at n0_1 n0_2 n0_3 n0_4
    linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n0_1), mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.kp_pos F.S.km_pos)) hde]

end Minimality.CaseC20

end
