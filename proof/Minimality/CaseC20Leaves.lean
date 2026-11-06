module

public import Minimality.CaseC20Core

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

/-! ### The `R`-images by transport

`X_R` is `X` for the mirror frame `F.rFrame`, whose shape is `F.S.swap`: each hypothesis of `X_R`
is the corresponding hypothesis of `X` after `rFrame_S`, `Shape20.swap` (`rh`). -/

lemma rFrame_a12 {x : Fin 7 → ℝ³} (F : Frame20 x) : F.rFrame.a12 = F.a12 := by
  show ⟪x (rperm 1) - x (rperm 5), x (rperm 6) - x (rperm 5)⟫ = _
  show ⟪x 6 - x 5, x 1 - x 5⟫ = _
  exact real_inner_comm _ _

lemma rFrame_a11 {x : Fin 7 → ℝ³} (F : Frame20 x) : F.rFrame.a11 = F.a22 := rfl

lemma rFrame_a22 {x : Fin 7 → ℝ³} (F : Frame20 x) : F.rFrame.a22 = F.a11 := rfl

lemma rFrame_gg {x : Fin 7 → ℝ³} (F : Frame20 x) : F.rFrame.gg = F.gg := by
  show ⟪-F.e, -F.e⟫ = ⟪F.e, F.e⟫
  simp

/-- A hypothesis of an `R`-image theorem as the hypothesis of the mirror frame. -/
local macro "rh " h:term : term =>
  `(by (try simp only [rFrame_S, Shape20.swap, rFrame_a11, rFrame_a22, rFrame_a12, rFrame_gg]); linarith only [$h])

/-- Q_A = V + T_A (27.64 (ii)) -/
theorem Frame20.ra4_A {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hW : 0 < -F.S.hp*F.S.sp + F.S.hp - F.S.kp) (hQ : 0 < F.S.hm*F.S.sp*F.S.tp - F.S.hm*F.S.tp + F.S.hp*F.S.sp*F.S.tm - F.S.hp*F.S.sp - F.S.hp*F.S.tm + F.S.hp + F.S.kp*F.S.tm - F.S.kp) (hD : 0 < -F.S.hp*F.S.sm*F.S.sp + F.S.hp*F.S.sm + F.S.hp*F.S.sp - F.S.hp - F.S.km*F.S.sp*F.S.tp + F.S.km*F.S.tp - F.S.kp*F.S.sm + F.S.kp) (hA1 : 0 < F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm)   :
    IsRupert (Finset.univ.image x) :=
  F.ra4_A_cc hx hα hβ hW.le hQ hD.le hA1

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
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_6, Shape20.u_tB] at n0_1 n0_2 n0_3 n0_4
  · linarith only [mul_nonneg (hCr).le (sub_nonneg.2 n0_3), mul_pos ((mul_pos F.S.sm_pos hCr)) hbe]
  · linarith only [mul_nonneg ((mul_pos F.S.sm_pos F.S.hm_pos)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos htm1 F.S.km_pos)).le (sub_nonneg.2 n0_2), mul_nonneg ((mul_pos F.S.tm_pos F.S.km_pos)).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos (mul_pos F.S.sm_pos F.S.sm_pos) rm)) hbe, mul_pos ((mul_pos (mul_pos F.S.sm_pos F.S.sm_pos) rm)) hga, mul_pos ((mul_pos (mul_pos F.S.km_pos F.S.km_pos) rm)) hde]

/-- V + Y (27.64 (iv)) -/
theorem Frame20.ra4_Y {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hW : 0 < -F.S.hp*F.S.sp + F.S.hp - F.S.kp) (hQ : 0 < F.S.hm*F.S.sp*F.S.tp - F.S.hm*F.S.tp + F.S.hp*F.S.sp*F.S.tm - F.S.hp*F.S.sp - F.S.hp*F.S.tm + F.S.hp + F.S.kp*F.S.tm - F.S.kp) (hD : 0 < -F.S.hp*F.S.sm*F.S.sp + F.S.hp*F.S.sm + F.S.hp*F.S.sp - F.S.hp - F.S.km*F.S.sp*F.S.tp + F.S.km*F.S.tp - F.S.kp*F.S.sm + F.S.kp) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hCm : 0 < F.S.hp*F.S.sm + F.S.km*F.S.tp - F.S.km) (hA3h : 0 < -F.S.hm*F.S.sm*F.S.tp + F.S.hm - F.S.hp*F.S.sm*F.S.tm + F.S.hp*F.S.sm + F.S.km*F.S.tm - F.S.km)   :
    IsRupert (Finset.univ.image x) :=
  F.ra4_Y_cc hx hα hβ hW.le hQ hD.le hA1r hCm.le hA3h.le

/-- V + X (27.64 (iv)) -/
theorem Frame20.ra4_X {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hW : 0 < -F.S.hp*F.S.sp + F.S.hp - F.S.kp) (hQ : 0 < F.S.hm*F.S.sp*F.S.tp - F.S.hm*F.S.tp + F.S.hp*F.S.sp*F.S.tm - F.S.hp*F.S.sp - F.S.hp*F.S.tm + F.S.hp + F.S.kp*F.S.tm - F.S.kp) (hD : 0 < -F.S.hp*F.S.sm*F.S.sp + F.S.hp*F.S.sm + F.S.hp*F.S.sp - F.S.hp - F.S.km*F.S.sp*F.S.tp + F.S.km*F.S.tp - F.S.kp*F.S.sm + F.S.kp) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hCm : 0 < F.S.hp*F.S.sm + F.S.km*F.S.tp - F.S.km) (hA3 : 0 < F.S.hm*F.S.sm*F.S.tp - F.S.hm + F.S.hp*F.S.sm*F.S.tm - F.S.hp*F.S.sm - F.S.km*F.S.tm + F.S.km)   :
    IsRupert (Finset.univ.image x) :=
  F.ra4_X_cc hx hα hβ hW.le hQ hD.le hA1r hCm.le hA3.le

/-- 27.74 (i), ω > 0 -/
theorem Frame20.om1p {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (htt : 0 ≤ F.S.tm - F.S.tp) (hom : 0 < (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) :
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
  · exact F.tANR_any hx (by linarith only [hA1r]) o0.1 o0.2
  by_cases o1 : (F.dep F.S.u_tP 1 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 1 < F.dep F.S.u_tP 6 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 6) ∧ (F.dep F.S.u_tP 3 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 3 < F.dep F.S.u_tP 4 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 4)
  · exact F.tP (by linarith only [hA1r]) o1.1 o1.2
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_6, Shape20.u_tANR, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
  · linarith only [mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n1_2), mul_nonneg (htp1).le (sub_nonneg.2 n1_2), mul_pos ((mul_pos htp1 F.S.tm_pos)) hal, mul_pos ((mul_pos htp1 htm1)) hal]
  · linarith only [(sub_nonneg.2 n1_4), mul_pos F.S.sp_pos hom, mul_pos hsp1 hom]
  · linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n0_2), mul_nonneg (htp1).le (sub_nonneg.2 n0_4), mul_nonneg (htm1).le (sub_nonneg.2 n1_1), mul_pos htm1 hom, mul_nonneg htt hom.le, mul_pos ((mul_pos htp1 htp1)) hal, mul_pos ((mul_pos F.S.hp_pos F.S.hp_pos)) hde, mul_pos ((mul_pos F.S.hp_pos hA1r)) hde]
  · linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n0_1), mul_nonneg (htp1).le (sub_nonneg.2 n0_4), mul_nonneg htt (sub_nonneg.2 n1_2), mul_pos htm1 hom, mul_nonneg htt hom.le, mul_pos ((mul_pos F.S.hp_pos F.S.hp_pos)) hde, mul_pos ((mul_pos F.S.hp_pos hA1r)) hde]

/-- 27.74 (i), ω < 0 -/
theorem Frame20.om1n {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (htt : 0 ≤ F.S.tm - F.S.tp) (hom : 0 < (-F.S.sm*F.S.tp + F.S.sm + F.S.tp - 1) * F.a12 + (F.S.hp*F.S.km) * F.gg) :
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
  · exact F.tANR_any hx (by linarith only [hA1r]) o0.1 o0.2
  by_cases o1 : (F.dep F.S.u_tP 1 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 1 < F.dep F.S.u_tP 6 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 6) ∧ (F.dep F.S.u_tP 3 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 3 < F.dep F.S.u_tP 4 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 4)
  · exact F.tP (by linarith only [hA1r]) o1.1 o1.2
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_6, Shape20.u_tANR, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
  · linarith only [(sub_nonneg.2 n1_2), mul_pos ((mul_pos htp1 F.S.tm_pos)) hal, mul_pos ((mul_pos htp1 htm1)) hal]
  · linarith only [mul_nonneg (htp1).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n0_3), mul_pos F.S.sp_pos hom, mul_pos hsp1 hom, mul_nonneg htt hom.le]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n1_1), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_3), mul_pos F.S.hm_pos hom, mul_pos ((mul_pos htp1 F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 F.S.hp_pos)) hga, mul_pos ((mul_pos htp1 hA1r)) hga]
  · linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n0_2), mul_nonneg htt (sub_nonneg.2 n1_1), mul_pos ((mul_pos F.S.hp_pos F.S.hp_pos)) hde, mul_pos ((mul_pos F.S.hp_pos hA1r)) hde]

/-- 27.74 (i), ω = 0, off ℓ1 -/
theorem Frame20.om1z1 {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (htt : 0 ≤ F.S.tm - F.S.tp) (hom1 : 0 ≤ (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) (hom2 : 0 ≤ (-F.S.sm*F.S.tp + F.S.sm + F.S.tp - 1) * F.a12 + (F.S.hp*F.S.km) * F.gg) (hl : 0 < (F.S.km*F.S.tm) * (F.a11 - F.a12) + (-F.S.hm*F.S.sm + F.S.hm + F.S.km*F.S.tm - F.S.km) * F.a12) :
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
  · exact F.tANR_any hx (by linarith only [hA1r]) o0.1 o0.2
  by_cases o1 : (F.dep F.S.u_tP 1 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 1 < F.dep F.S.u_tP 6 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 6) ∧ (F.dep F.S.u_tP 3 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 3 < F.dep F.S.u_tP 4 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 4)
  · exact F.tP (by linarith only [hA1r]) o1.1 o1.2
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_6, Shape20.u_tANR, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
  · linarith only [mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n1_2), mul_nonneg (htm1).le (sub_nonneg.2 n1_2), mul_pos ((mul_pos htp1 F.S.sm_pos)) hal, mul_pos ((mul_pos htp1 hsm1)) hal]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_4), mul_pos htm1 hl, mul_nonneg htt hl.le]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_1), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n1_1), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n1_4), mul_pos htm1 hl, mul_nonneg htt hl.le, mul_pos ((mul_pos htp1 F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 F.S.hp_pos)) hga, mul_pos ((mul_pos htp1 hA1r)) hga]
  · linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n0_1), mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n0_3), mul_nonneg (htp1).le (sub_nonneg.2 n0_4), mul_nonneg htt (sub_nonneg.2 n1_2), mul_nonneg (F.S.tm_pos).le hom1, mul_nonneg (htm1).le hom1, mul_pos ((mul_pos F.S.hp_pos F.S.hp_pos)) hde, mul_pos ((mul_pos F.S.hp_pos hA1r)) hde]

/-- 27.74 (i), ω = 0, off ℓ1 -/
theorem Frame20.om1z2 {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (htt : 0 ≤ F.S.tm - F.S.tp) (hom1 : 0 ≤ (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) (hom2 : 0 ≤ (-F.S.sm*F.S.tp + F.S.sm + F.S.tp - 1) * F.a12 + (F.S.hp*F.S.km) * F.gg) (hl : 0 < (-F.S.km*F.S.tm) * (F.a11 - F.a12) + (F.S.hm*F.S.sm - F.S.hm - F.S.km*F.S.tm + F.S.km) * F.a12) :
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
  · exact F.tANR_any hx (by linarith only [hA1r]) o0.1 o0.2
  by_cases o1 : (F.dep F.S.u_tP 1 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 1 < F.dep F.S.u_tP 6 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 6) ∧ (F.dep F.S.u_tP 3 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 3 < F.dep F.S.u_tP 4 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 4)
  · exact F.tP (by linarith only [hA1r]) o1.1 o1.2
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_6, Shape20.u_tANR, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n1_1), mul_pos htm1 hl, mul_nonneg htt hl.le, mul_pos ((mul_pos htp1 F.S.km_pos)) hal]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n1_4), mul_pos htm1 hl, mul_nonneg htt hl.le]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_1), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n1_1), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_1), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos htp1 F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 F.S.hp_pos)) hga, mul_pos ((mul_pos htp1 hA1r)) hga]
  · linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n0_2), mul_nonneg htt (sub_nonneg.2 n1_1), mul_pos ((mul_pos F.S.hp_pos F.S.hp_pos)) hde, mul_pos ((mul_pos F.S.hp_pos hA1r)) hde]

/-- 27.74 (ii): {T_A, V}, h+ ≥ d+ -/
theorem Frame20.om2a {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1 : 0 < F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) (hVp : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm - F.S.kp*F.S.tm) (hVW : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.sp + F.S.hp*F.S.tm - F.S.hp - F.S.kp*F.S.tm + F.S.kp) (hWp : 0 ≤ -F.S.hp*F.S.sp + F.S.hp - F.S.kp) :
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
  · exact F.vN4_any hx (by linarith only [hVp]) (by linarith only [hVW]) o1.1 o1.2
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
  · linarith only [mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n0_3), mul_nonneg (hsm1).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.hp_pos F.S.km_pos)) hde]
  · linarith only [mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n0_3), mul_nonneg (hsm1).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.hp_pos F.S.km_pos)) hde]
  · linarith only [mul_nonneg hWp (sub_nonneg.2 n0_3), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos hsm1 rp)) hga]
  · linarith only [mul_nonneg ((mul_pos F.S.tp_pos hsp1)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos htp1 F.S.tm_pos)).le (sub_nonneg.2 n1_2), mul_nonneg ((mul_pos htp1 htm1)).le (sub_nonneg.2 n1_2), mul_pos ((mul_pos (mul_pos F.S.tp_pos rp) rp)) hde, mul_pos ((mul_pos (mul_pos htp1 F.S.kp_pos) rp)) hde, mul_pos ((mul_pos (mul_pos htp1 rp) rp)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) rp)) hde]

/-- 27.74 (ii): {T_A, V}, t+ ≤ t−, h+ ≤ d+ -/
theorem Frame20.om2b {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1 : 0 < F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) (hVp : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm - F.S.kp*F.S.tm) (hVW : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.sp + F.S.hp*F.S.tm - F.S.hp - F.S.kp*F.S.tm + F.S.kp) (htt : 0 ≤ F.S.tm - F.S.tp) (hWn : 0 ≤ F.S.hp*F.S.sp - F.S.hp + F.S.kp) :
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
  · exact F.vN4_any hx (by linarith only [hVp]) (by linarith only [hVW]) o1.1 o1.2
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
  · linarith only [mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n0_4), mul_nonneg (htm1).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos htp1 F.S.sm_pos)) hga, mul_pos ((mul_pos F.S.hp_pos F.S.km_pos)) hde]
  · linarith only [mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n0_4), mul_nonneg (hsp1).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos htp1 F.S.sm_pos)) hga, mul_pos ((mul_pos F.S.hp_pos F.S.km_pos)) hde]
  · linarith only [mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le (F.S.km_pos).le) htt) (sub_nonneg.2 n0_2), mul_nonneg (mul_nonneg (mul_nonneg (F.S.sm_pos).le (F.S.kp_pos).le) htt) (sub_nonneg.2 n0_3), mul_nonneg (mul_nonneg (mul_nonneg (hsm1).le (F.S.kp_pos).le) htt) (sub_nonneg.2 n0_4), mul_nonneg ((mul_pos htp1 F.S.km_pos)).le (sub_nonneg.2 n1_1), mul_nonneg ((mul_pos htp1 F.S.hm_pos)).le (sub_nonneg.2 n1_4), mul_nonneg ((mul_pos (mul_pos F.S.tp_pos htm1) F.S.hp_pos)).le (sub_nonneg.2 n1_4), mul_nonneg ((mul_pos (mul_pos htp1 htm1) F.S.hp_pos)).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos (mul_pos htp1 hsm1) hVW)) hga, mul_pos ((mul_pos (mul_pos htm1 hsm1) rp)) hga]
  · linarith only [mul_nonneg ((mul_pos F.S.tp_pos hsp1)).le (sub_nonneg.2 n0_1), mul_nonneg htt (sub_nonneg.2 n1_2), mul_nonneg ((mul_pos F.S.tp_pos htp1)).le (sub_nonneg.2 n1_2), mul_nonneg ((mul_pos htp1 htm1)).le (sub_nonneg.2 n1_2), mul_nonneg ((mul_pos F.S.tm_pos htm1)).le (sub_nonneg.2 n1_2), mul_nonneg (mul_nonneg htt htt) (sub_nonneg.2 n1_2), mul_pos ((mul_pos (mul_pos F.S.tp_pos rp) hA1)) hde, mul_pos ((mul_pos (mul_pos htp1 F.S.hm_pos) rp)) hde, mul_pos ((mul_pos (mul_pos htp1 rp) hA1)) hde, mul_pos ((mul_pos (mul_pos htm1 F.S.hp_pos) rp)) hde]

/-- 27.74 (ii): {T_A, V, T′}, h+ ≥ d+, p -/
theorem Frame20.om3p {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hVp : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm - F.S.kp*F.S.tm) (hVW : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.sp + F.S.hp*F.S.tm - F.S.hp - F.S.kp*F.S.tm + F.S.kp) (hWp : 0 ≤ -F.S.hp*F.S.sp + F.S.hp - F.S.kp) (hom : 0 < (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg)  :
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
  · exact F.tANR_any hx (by linarith only [hA1r]) o0.1 o0.2
  by_cases o1 : (F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 3 ∨ F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 6 ∨ F.dep F.S.u_vN4 4 < F.dep F.S.u_vN4 3 ∨ F.dep F.S.u_vN4 4 < F.dep F.S.u_vN4 6) ∧ (F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 0 ∨ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 0 ∨ F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 4 ∨ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 4)
  · exact F.vN4_any hx (by linarith only [hVp]) (by linarith only [hVW]) o1.1 o1.2
  by_cases o2 : (F.dep F.S.u_tP 1 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 1 < F.dep F.S.u_tP 6 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 6) ∧ (F.dep F.S.u_tP 3 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 3 < F.dep F.S.u_tP 4 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 4)
  · exact F.tP (by linarith only [hA1r]) o2.1 o2.2
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
  · linarith only [mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n2_2), mul_nonneg (hsp1).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos F.S.tp_pos htp1)) hal, mul_pos ((mul_pos htp1 htp1)) hal]
  · linarith only [(sub_nonneg.2 n2_4), mul_pos F.S.tp_pos hom, mul_pos htp1 hom]
  · linarith only [mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n2_2), mul_nonneg (hsp1).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos F.S.tp_pos htp1)) hal, mul_pos ((mul_pos htp1 htp1)) hal]
  · linarith only [(sub_nonneg.2 n2_4), mul_pos F.S.tp_pos hom, mul_pos htp1 hom]
  · linarith only [mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n0_2), mul_nonneg (htp1).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n0_3), mul_nonneg (htm1).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n0_4), mul_nonneg (htp1).le (sub_nonneg.2 n2_1), mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n2_1), mul_nonneg (hsp1).le (sub_nonneg.2 n2_2), mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n2_3), mul_pos htp1 hom, mul_pos F.S.sp_pos hom, mul_pos ((mul_pos htp1 htp1)) hal, mul_pos ((mul_pos htp1 htp1)) hga, mul_pos ((mul_pos F.S.hp_pos F.S.hp_pos)) hde]
  · linarith only [(sub_nonneg.2 n0_3), mul_pos F.S.tp_pos hom, mul_pos htp1 hom]
  · linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n0_1), mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n0_2), mul_nonneg (hsp1).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n2_1), mul_nonneg (htp1).le (sub_nonneg.2 n2_1), mul_pos hsp1 hom, mul_pos ((mul_pos htp1 htp1)) hal, mul_pos ((mul_pos htp1 htp1)) hga, mul_pos ((mul_pos F.S.hp_pos F.S.hp_pos)) hde]
  · linarith only [mul_nonneg (hVp).le (sub_nonneg.2 n0_3), mul_pos hVW hom, mul_nonneg hWp hom.le]

/-- 27.74 (ii): {T_A, V, T′}, h+ ≥ d+, n -/
theorem Frame20.om3n {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hVp : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm - F.S.kp*F.S.tm) (hVW : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.sp + F.S.hp*F.S.tm - F.S.hp - F.S.kp*F.S.tm + F.S.kp) (hWp : 0 ≤ -F.S.hp*F.S.sp + F.S.hp - F.S.kp) (hom : 0 < (-F.S.sm*F.S.tp + F.S.sm + F.S.tp - 1) * F.a12 + (F.S.hp*F.S.km) * F.gg)  :
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
  · exact F.tANR_any hx (by linarith only [hA1r]) o0.1 o0.2
  by_cases o1 : (F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 3 ∨ F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 6 ∨ F.dep F.S.u_vN4 4 < F.dep F.S.u_vN4 3 ∨ F.dep F.S.u_vN4 4 < F.dep F.S.u_vN4 6) ∧ (F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 0 ∨ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 0 ∨ F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 4 ∨ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 4)
  · exact F.vN4_any hx (by linarith only [hVp]) (by linarith only [hVW]) o1.1 o1.2
  by_cases o2 : (F.dep F.S.u_tP 1 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 1 < F.dep F.S.u_tP 6 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 6) ∧ (F.dep F.S.u_tP 3 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 3 < F.dep F.S.u_tP 4 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 4)
  · exact F.tP (by linarith only [hA1r]) o2.1 o2.2
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
  · linarith only [(sub_nonneg.2 n2_2), mul_pos ((mul_pos F.S.tp_pos htp1)) hal, mul_pos ((mul_pos htp1 htp1)) hal]
  · linarith only [mul_nonneg (hVW).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n1_4), mul_pos hVp hom, mul_pos ((mul_pos hsm1 rp)) hga]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sm_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal]
  · linarith only [mul_nonneg (hA1r).le (sub_nonneg.2 n0_3), mul_pos hA1r hom]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_1), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n2_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n2_3), mul_pos F.S.hm_pos hom, mul_pos ((mul_pos htp1 F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 F.S.hp_pos)) hga, mul_pos ((mul_pos htp1 hA1r)) hga]
  · linarith only [mul_nonneg hWp (sub_nonneg.2 n0_3), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos hsm1 rp)) hga]
  · linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n0_2), mul_nonneg (htp1).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n2_1), mul_nonneg (htm1).le (sub_nonneg.2 n2_2), mul_nonneg (hsm1).le (sub_nonneg.2 n2_3), mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n2_4), mul_nonneg (hsm1).le (sub_nonneg.2 n2_4), mul_pos F.S.tp_pos hom, mul_pos htm1 hom, mul_pos ((mul_pos htp1 htp1)) hal, mul_pos ((mul_pos htp1 F.S.sm_pos)) hal, mul_pos ((mul_pos F.S.hp_pos F.S.hp_pos)) hde, mul_pos ((mul_pos F.S.hp_pos hA1r)) hde]
  · linarith only [mul_nonneg ((mul_pos F.S.tp_pos hsp1)).le (sub_nonneg.2 n0_2), mul_nonneg ((mul_pos F.S.tp_pos htp1)).le (sub_nonneg.2 n1_1), mul_nonneg ((mul_pos htp1 htp1)).le (sub_nonneg.2 n1_1), mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.hm_pos) rp)) hde, mul_pos ((mul_pos (mul_pos F.S.tp_pos rp) rp)) hde, mul_pos ((mul_pos (mul_pos htp1 F.S.kp_pos) rp)) hde, mul_pos ((mul_pos (mul_pos htp1 rp) rp)) hde, mul_pos ((mul_pos (mul_pos F.S.tm_pos F.S.hp_pos) rp)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) rp)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos rp) hA1r)) hde, mul_pos ((mul_pos (mul_pos hsp1 rp) hA1r)) hde]

/-- 27.74 (ii): {T_A, V, T′}, h+ ≥ d+, z1 -/
theorem Frame20.om3z1 {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hVp : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm - F.S.kp*F.S.tm) (hVW : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.sp + F.S.hp*F.S.tm - F.S.hp - F.S.kp*F.S.tm + F.S.kp) (hWp : 0 ≤ -F.S.hp*F.S.sp + F.S.hp - F.S.kp) (hom1 : 0 ≤ (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) (hom2 : 0 ≤ (-F.S.sm*F.S.tp + F.S.sm + F.S.tp - 1) * F.a12 + (F.S.hp*F.S.km) * F.gg) (hl : 0 < (F.S.km*F.S.tm) * (F.a11 - F.a12) + (-F.S.hm*F.S.sm + F.S.hm + F.S.km*F.S.tm - F.S.km) * F.a12)  :
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
  · exact F.tANR_any hx (by linarith only [hA1r]) o0.1 o0.2
  by_cases o1 : (F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 3 ∨ F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 6 ∨ F.dep F.S.u_vN4 4 < F.dep F.S.u_vN4 3 ∨ F.dep F.S.u_vN4 4 < F.dep F.S.u_vN4 6) ∧ (F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 0 ∨ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 0 ∨ F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 4 ∨ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 4)
  · exact F.vN4_any hx (by linarith only [hVp]) (by linarith only [hVW]) o1.1 o1.2
  by_cases o2 : (F.dep F.S.u_tP 1 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 1 < F.dep F.S.u_tP 6 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 6) ∧ (F.dep F.S.u_tP 3 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 3 < F.dep F.S.u_tP 4 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 4)
  · exact F.tP (by linarith only [hA1r]) o2.1 o2.2
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
  · linarith only [mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n2_2), mul_nonneg (hsp1).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos F.S.tp_pos htp1)) hal, mul_pos ((mul_pos htp1 htp1)) hal]
  · linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n1_4), mul_nonneg hWp (sub_nonneg.2 n2_4), mul_pos ((mul_pos hsm1 rp)) hga]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsp1 hA1r)) hal]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n2_4), mul_pos htp1 hl]
  · linarith only [mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n0_2), mul_nonneg (hsp1).le (sub_nonneg.2 n0_2), (sub_nonneg.2 n2_1), mul_pos ((mul_pos htp1 htp1)) hal, mul_pos ((mul_pos htp1 htp1)) hga, mul_pos ((mul_pos F.S.hp_pos F.S.hp_pos)) hde]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.km_pos).le hom1, mul_pos htp1 hl]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n2_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos htp1 hl, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsp1 hA1r)) hal]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.km_pos).le hom1, mul_pos htp1 hl]

/-- 27.74 (ii): {T_A, V, T′}, h+ ≥ d+, z2 -/
theorem Frame20.om3z2 {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hVp : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm - F.S.kp*F.S.tm) (hVW : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.sp + F.S.hp*F.S.tm - F.S.hp - F.S.kp*F.S.tm + F.S.kp) (hWp : 0 ≤ -F.S.hp*F.S.sp + F.S.hp - F.S.kp) (hom1 : 0 ≤ (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) (hom2 : 0 ≤ (-F.S.sm*F.S.tp + F.S.sm + F.S.tp - 1) * F.a12 + (F.S.hp*F.S.km) * F.gg) (hl : 0 < (-F.S.km*F.S.tm) * (F.a11 - F.a12) + (F.S.hm*F.S.sm - F.S.hm - F.S.km*F.S.tm + F.S.km) * F.a12)  :
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
  · exact F.tANR_any hx (by linarith only [hA1r]) o0.1 o0.2
  by_cases o1 : (F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 3 ∨ F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 6 ∨ F.dep F.S.u_vN4 4 < F.dep F.S.u_vN4 3 ∨ F.dep F.S.u_vN4 4 < F.dep F.S.u_vN4 6) ∧ (F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 0 ∨ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 0 ∨ F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 4 ∨ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 4)
  · exact F.vN4_any hx (by linarith only [hVp]) (by linarith only [hVW]) o1.1 o1.2
  by_cases o2 : (F.dep F.S.u_tP 1 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 1 < F.dep F.S.u_tP 6 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 6) ∧ (F.dep F.S.u_tP 3 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 3 < F.dep F.S.u_tP 4 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 4)
  · exact F.tP (by linarith only [hA1r]) o2.1 o2.2
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  simp only [not_and_or, not_or, not_lt] at o2
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 <;>
    rcases o2 with n2 | n2
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_6, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_1), mul_pos htp1 hl, mul_pos ((mul_pos htp1 F.S.km_pos)) hal]
  · linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n1_4), mul_nonneg hWp (sub_nonneg.2 n2_4), mul_pos ((mul_pos hsm1 rp)) hga]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos htp1 hl]
  · linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n0_2), (sub_nonneg.2 n0_4), mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n2_1), mul_nonneg (htm1).le (sub_nonneg.2 n2_3), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n2_4), mul_pos ((mul_pos htp1 F.S.tm_pos)) hal, mul_pos ((mul_pos F.S.hp_pos F.S.hp_pos)) hde, mul_pos ((mul_pos F.S.hp_pos hA1r)) hde]
  · linarith only [mul_nonneg hWp (sub_nonneg.2 n0_3), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos hsm1 rp)) hga]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_1), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n2_2), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n2_3), mul_pos htp1 hl, mul_pos ((mul_pos htp1 F.S.km_pos)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 F.S.hp_pos)) hga, mul_pos ((mul_pos htp1 hA1r)) hga]
  · linarith only [mul_nonneg ((mul_pos F.S.tp_pos hsp1)).le (sub_nonneg.2 n0_2), mul_nonneg (htp1).le (sub_nonneg.2 n1_1), mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.hm_pos) rp)) hde, mul_pos ((mul_pos (mul_pos F.S.tp_pos rp) rp)) hde, mul_pos ((mul_pos (mul_pos htp1 F.S.kp_pos) rp)) hde, mul_pos ((mul_pos (mul_pos htp1 rp) rp)) hde, mul_pos ((mul_pos (mul_pos F.S.tm_pos F.S.hp_pos) rp)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) rp)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos rp) hA1r)) hde, mul_pos ((mul_pos (mul_pos hsp1 rp) hA1r)) hde]

/-- 27.76 N4 p -/
theorem Frame20.om4ap {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1R : 0 < F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) (hVpR : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVWR : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hKb : 0 < F.S.hm + F.S.km*F.S.tm - F.S.km) (hss : 0 < F.S.sm - F.S.sp) (hnu : 0 < (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) :
    IsRupert (Finset.univ.image x) :=
  F.om4ap_cc hx hα hβ hA1r hA1R hVpR hVWR hKb.le hss hnu

/-- 27.76 N4 n -/
theorem Frame20.om4an {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1R : 0 < F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) (hVpR : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVWR : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hKb : 0 < F.S.hm + F.S.km*F.S.tm - F.S.km) (hss : 0 < F.S.sm - F.S.sp) (hnu : 0 < (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) :
    IsRupert (Finset.univ.image x) :=
  F.om4an_cc hx hα hβ hA1r hA1R hVpR hVWR hKb.le hss hnu

/-- 27.76 N4 z1 -/
theorem Frame20.om4az1 {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1R : 0 < F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) (hVpR : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVWR : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hKb : 0 < F.S.hm + F.S.km*F.S.tm - F.S.km) (hss : 0 < F.S.sm - F.S.sp) (hnu1 : 0 ≤ (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) (hnu2 : 0 ≤ (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) (hl : 0 < (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) + (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg) :
    IsRupert (Finset.univ.image x) :=
  F.om4az1_cc hx hα hβ hA1r hA1R hVpR hVWR hKb.le hss hnu1 hnu2 hl

/-- 27.76 N4 z2 -/
theorem Frame20.om4az2 {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1R : 0 < F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) (hVpR : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVWR : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hKb : 0 < F.S.hm + F.S.km*F.S.tm - F.S.km) (hss : 0 < F.S.sm - F.S.sp) (hnu1 : 0 ≤ (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) (hnu2 : 0 ≤ (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) (hl : 0 < (-F.S.tm*F.S.tp + F.S.tm + F.S.tp - 1) * (F.a11 - F.a12) + (-F.S.tm*F.S.tp + F.S.tm + F.S.tp - 1) * F.a12 + (F.S.hm*F.S.hp) * F.gg) :
    IsRupert (Finset.univ.image x) :=
  F.om4az2_cc hx hα hβ hA1r hA1R hVpR hVWR hKb.le hss hnu1 hnu2 hl

/-- 27.76 Rv p -/
theorem Frame20.om4bp {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1R : 0 < F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) (hVR : 0 < F.S.hm*F.S.sp + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) (hKb : 0 < F.S.hm + F.S.km*F.S.tm - F.S.km) (hnu : 0 < (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg)   :
    IsRupert (Finset.univ.image x) :=
  F.om4bp_cc hx hα hβ hA1r hA1R hVR hKb.le hnu

/-- 27.76 Rv n -/
theorem Frame20.om4bn {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1R : 0 < F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) (hVR : 0 < F.S.hm*F.S.sp + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) (hKb : 0 < F.S.hm + F.S.km*F.S.tm - F.S.km) (hnu : 0 < (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg)   :
    IsRupert (Finset.univ.image x) :=
  F.om4bn_cc hx hα hβ hA1r hA1R hVR hKb.le hnu

/-- 27.76 Rv z1 -/
theorem Frame20.om4bz1 {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1R : 0 < F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) (hVR : 0 < F.S.hm*F.S.sp + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) (hKb : 0 < F.S.hm + F.S.km*F.S.tm - F.S.km) (hnu1 : 0 ≤ (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) (hnu2 : 0 ≤ (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) (hl : 0 < (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) + (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg)   :
    IsRupert (Finset.univ.image x) :=
  F.om4bz1_cc hx hα hβ hA1r hA1R hVR hKb.le hnu1 hnu2 hl

/-- 27.76 Rv z2 -/
theorem Frame20.om4bz2 {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1R : 0 < F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) (hVR : 0 < F.S.hm*F.S.sp + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) (hKb : 0 < F.S.hm + F.S.km*F.S.tm - F.S.km) (hnu1 : 0 ≤ (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) (hnu2 : 0 ≤ (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) (hl : 0 < (-F.S.tm*F.S.tp + F.S.tm + F.S.tp - 1) * (F.a11 - F.a12) + (-F.S.tm*F.S.tp + F.S.tm + F.S.tp - 1) * F.a12 + (F.S.hm*F.S.hp) * F.gg)   :
    IsRupert (Finset.univ.image x) :=
  F.om4bz2_cc hx hα hβ hA1r hA1R hVR hKb.le hnu1 hnu2 hl

/-- 27.76 N4, d− < c+ p -/
theorem Frame20.om4cp {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1Rr : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVpR : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVWR : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hKb : 0 < F.S.hm + F.S.km*F.S.tm - F.S.km) (hss : 0 < F.S.sm - F.S.sp) (hnu : 0 < (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg)  :
    IsRupert (Finset.univ.image x) :=
  F.om4cp_cc hx hα hβ hA1r hA1Rr hVpR hVWR hKb.le hss hnu

/-- 27.76 N4, d− < c+ z1 -/
theorem Frame20.om4cz1 {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1Rr : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVpR : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVWR : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hKb : 0 < F.S.hm + F.S.km*F.S.tm - F.S.km) (hss : 0 < F.S.sm - F.S.sp) (hnu1 : 0 ≤ (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) (hnu2 : 0 ≤ (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) (hl : 0 < (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) + (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg)  :
    IsRupert (Finset.univ.image x) :=
  F.om4cz1_cc hx hα hβ hA1r hA1Rr hVpR hVWR hKb.le hss hnu1 hnu2 hl

/-- 27.76 N4, d− < c+ z2 -/
theorem Frame20.om4cz2 {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1Rr : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVpR : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVWR : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hKb : 0 < F.S.hm + F.S.km*F.S.tm - F.S.km) (hss : 0 < F.S.sm - F.S.sp) (hnu1 : 0 ≤ (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) (hnu2 : 0 ≤ (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) (hl : 0 < (-F.S.tm*F.S.tp + F.S.tm + F.S.tp - 1) * (F.a11 - F.a12) + (-F.S.tm*F.S.tp + F.S.tm + F.S.tp - 1) * F.a12 + (F.S.hm*F.S.hp) * F.gg)  :
    IsRupert (Finset.univ.image x) :=
  F.om4cz2_cc hx hα hβ hA1r hA1Rr hVpR hVWR hKb.le hss hnu1 hnu2 hl

/-- 27.76 N4, d− < c+, ν<0, op -/
theorem Frame20.om4cnop {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1Rr : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVpR : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVWR : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hKb : 0 < F.S.hm + F.S.km*F.S.tm - F.S.km) (hss : 0 < F.S.sm - F.S.sp) (hnu : 0 < (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) (hom : 0 < (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg)  :
    IsRupert (Finset.univ.image x) :=
  F.om4cnop_cc hx hα hβ hA1r hA1Rr hVpR hVWR hKb.le hss hnu hom

/-- 27.76 N4, d− < c+, ν<0, om -/
theorem Frame20.om4cnom {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1Rr : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVpR : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVWR : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hKb : 0 < F.S.hm + F.S.km*F.S.tm - F.S.km) (hss : 0 < F.S.sm - F.S.sp) (hnu : 0 < (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) (hom : 0 < (-F.S.sm*F.S.tp + F.S.sm + F.S.tp - 1) * F.a12 + (F.S.hp*F.S.km) * F.gg)  :
    IsRupert (Finset.univ.image x) :=
  F.om4cnom_cc hx hα hβ hA1r hA1Rr hVpR hVWR hKb.le hss hnu hom

/-- 27.76 N4, d− < c+, ν<0, oz1 -/
theorem Frame20.om4cnoz1 {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1Rr : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVpR : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVWR : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hKb : 0 < F.S.hm + F.S.km*F.S.tm - F.S.km) (hss : 0 < F.S.sm - F.S.sp) (hnu : 0 < (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) (hom1 : 0 ≤ (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) (hom2 : 0 ≤ (-F.S.sm*F.S.tp + F.S.sm + F.S.tp - 1) * F.a12 + (F.S.hp*F.S.km) * F.gg) (hl2 : 0 < (F.S.hp*F.S.sp) * (F.a22 - F.a12) + (F.S.hp*F.S.sp - F.S.hp - F.S.kp*F.S.tp + F.S.kp) * F.a12)  :
    IsRupert (Finset.univ.image x) :=
  F.om4cnoz1_cc hx hα hβ hA1r hA1Rr hVpR hVWR hKb.le hss hnu hom1 hom2 hl2

/-- 27.76 N4, d− < c+, ν<0, oz2 -/
theorem Frame20.om4cnoz2 {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1Rr : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVpR : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVWR : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hKb : 0 < F.S.hm + F.S.km*F.S.tm - F.S.km) (hss : 0 < F.S.sm - F.S.sp) (hnu : 0 < (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) (hom1 : 0 ≤ (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) (hom2 : 0 ≤ (-F.S.sm*F.S.tp + F.S.sm + F.S.tp - 1) * F.a12 + (F.S.hp*F.S.km) * F.gg) (hl2 : 0 < (-F.S.hp*F.S.sp) * (F.a22 - F.a12) + (-F.S.hp*F.S.sp + F.S.hp + F.S.kp*F.S.tp - F.S.kp) * F.a12)  :
    IsRupert (Finset.univ.image x) :=
  F.om4cnoz2_cc hx hα hβ hA1r hA1Rr hVpR hVWR hKb.le hss hnu hom1 hom2 hl2

/-- 27.76 Rv, d− < c+ p -/
theorem Frame20.om4dp {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1Rr : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVR : 0 < F.S.hm*F.S.sp + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) (hKb : 0 < F.S.hm + F.S.km*F.S.tm - F.S.km) (hnu : 0 < (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) :
    IsRupert (Finset.univ.image x) :=
  F.om4dp_cc hx hα hβ hA1r hA1Rr hVR hKb.le hnu

/-- 27.76 Rv, d− < c+ n -/
theorem Frame20.om4dn {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1Rr : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVR : 0 < F.S.hm*F.S.sp + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) (hKb : 0 < F.S.hm + F.S.km*F.S.tm - F.S.km) (hnu : 0 < (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) :
    IsRupert (Finset.univ.image x) :=
  F.om4dn_cc hx hα hβ hA1r hA1Rr hVR hKb.le hnu

/-- 27.76 Rv, d− < c+ z1 -/
theorem Frame20.om4dz1 {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1Rr : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVR : 0 < F.S.hm*F.S.sp + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) (hKb : 0 < F.S.hm + F.S.km*F.S.tm - F.S.km) (hnu1 : 0 ≤ (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) (hnu2 : 0 ≤ (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) (hl : 0 < (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) + (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg) :
    IsRupert (Finset.univ.image x) :=
  F.om4dz1_cc hx hα hβ hA1r hA1Rr hVR hKb.le hnu1 hnu2 hl

/-- 27.76 Rv, d− < c+ z2 -/
theorem Frame20.om4dz2 {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1Rr : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVR : 0 < F.S.hm*F.S.sp + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) (hKb : 0 < F.S.hm + F.S.km*F.S.tm - F.S.km) (hnu1 : 0 ≤ (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) (hnu2 : 0 ≤ (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) (hl : 0 < (-F.S.tm*F.S.tp + F.S.tm + F.S.tp - 1) * (F.a11 - F.a12) + (-F.S.tm*F.S.tp + F.S.tm + F.S.tp - 1) * F.a12 + (F.S.hm*F.S.hp) * F.gg) :
    IsRupert (Finset.univ.image x) :=
  F.om4dz2_cc hx hα hβ hA1r hA1Rr hVR hKb.le hnu1 hnu2 hl

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
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_4, F.ptC_5, F.ptC_6, Shape20.u_tA] at n0_1 n0_2 n0_3 n0_4
  · linarith only [mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n0_3), mul_nonneg (hsm1).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.hp_pos F.S.km_pos)) hde]
  · linarith only [mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hsp1).le (sub_nonneg.2 n0_1), mul_pos F.S.tm_pos hg, mul_pos htm1 hg]

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
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_5, Shape20.u_yT2] at n0_1 n0_2 n0_3 n0_4
  · linarith only [mul_nonneg ((mul_pos F.S.tp_pos F.S.tm_pos)).le (sub_nonneg.2 n0_2), mul_nonneg ((mul_pos F.S.tp_pos htm1)).le (sub_nonneg.2 n0_2), mul_nonneg (htp1).le (sub_nonneg.2 n0_3), mul_pos ((mul_pos (mul_pos htp1 F.S.tm_pos) F.S.sp_pos)) hbe, mul_pos ((mul_pos (mul_pos htp1 htm1) F.S.sp_pos)) hbe, mul_pos ((mul_pos (mul_pos htp1 htp1) F.S.sp_pos)) hga, mul_pos ((mul_pos (mul_pos F.S.tm_pos F.S.hp_pos) rp)) hde, mul_pos ((mul_pos (mul_pos htm1 F.S.hp_pos) rp)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) F.S.hp_pos)) hde]
  · linarith only [mul_nonneg (htp1).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.tm_pos).le hg, mul_pos ((mul_pos F.S.hp_pos hA1)) hde]
  · linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.hp_pos F.S.hm_pos)) hde]
  · linarith only [mul_nonneg (htp1).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.tm_pos).le hg, mul_pos ((mul_pos F.S.hp_pos hA1)) hde]
  · linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n0_1), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.hp_pos F.S.hm_pos)) hde]

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
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_4, F.ptC_5, F.ptC_6, Shape20.u_eXb] at n0_1 n0_2 n0_3 n0_4
  · linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_3), mul_pos ((mul_pos F.S.sm_pos F.S.hp_pos)) hbe]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_nonneg (rp).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos F.S.kp_pos)) hal, mul_pos ((mul_pos F.S.tp_pos rp)) hal, mul_pos ((mul_pos F.S.tp_pos F.S.kp_pos)) hbe, mul_pos ((mul_pos hsp1 F.S.hp_pos)) hbe]

/-- Q_A = V + T_A (27.64 (ii)) (R-image) -/
theorem Frame20.ra4_A_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hW : 0 < -F.S.hm - F.S.km*F.S.tm + F.S.km) (hQ : 0 < F.S.hm*F.S.sp - F.S.hm + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp - F.S.km*F.S.tm + F.S.km + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) (hD : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.sm*F.S.tm + F.S.hp*F.S.sm - F.S.km*F.S.tm*F.S.tp + F.S.km*F.S.tm + F.S.km*F.S.tp - F.S.km) (hA1 : 0 < F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp)   :
    IsRupert (Finset.univ.image x) :=
  F.ra4_A_R_cc hx hα hβ hW.le hQ hD.le hA1

/-- 27.32^R (27.64 (iii)) (R-image) -/
theorem Frame20.ra4_tBR_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hCr : 0 < -F.S.hp*F.S.sm + F.S.hp - F.S.km*F.S.tp)   :
    IsRupert (Finset.univ.image x) :=
  rupert_of_r (F.rFrame.ra4_tBR (hx.comp rperm_bijective.1) (rh hβ) (rh hα) (rh hA1r) (rh hCr))

/-- V + Y (27.64 (iv)) (R-image) -/
theorem Frame20.ra4_Y_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hW : 0 < -F.S.hm - F.S.km*F.S.tm + F.S.km) (hQ : 0 < F.S.hm*F.S.sp - F.S.hm + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp - F.S.km*F.S.tm + F.S.km + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) (hD : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.sm*F.S.tm + F.S.hp*F.S.sm - F.S.km*F.S.tm*F.S.tp + F.S.km*F.S.tm + F.S.km*F.S.tp - F.S.km) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hCm : 0 < F.S.hp*F.S.sm - F.S.hp + F.S.km*F.S.tp) (hA3h : 0 < F.S.hp*F.S.sp - F.S.hp - F.S.km*F.S.sp*F.S.tp + F.S.km*F.S.tp - F.S.kp*F.S.sm*F.S.tp + F.S.kp)   :
    IsRupert (Finset.univ.image x) :=
  F.ra4_Y_R_cc hx hα hβ hW.le hQ hD.le hA1r hCm.le hA3h.le

/-- V + X (27.64 (iv)) (R-image) -/
theorem Frame20.ra4_X_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hW : 0 < -F.S.hm - F.S.km*F.S.tm + F.S.km) (hQ : 0 < F.S.hm*F.S.sp - F.S.hm + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp - F.S.km*F.S.tm + F.S.km + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) (hD : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.sm*F.S.tm + F.S.hp*F.S.sm - F.S.km*F.S.tm*F.S.tp + F.S.km*F.S.tm + F.S.km*F.S.tp - F.S.km) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hCm : 0 < F.S.hp*F.S.sm - F.S.hp + F.S.km*F.S.tp) (hA3 : 0 < -F.S.hp*F.S.sp + F.S.hp + F.S.km*F.S.sp*F.S.tp - F.S.km*F.S.tp + F.S.kp*F.S.sm*F.S.tp - F.S.kp)   :
    IsRupert (Finset.univ.image x) :=
  F.ra4_X_R_cc hx hα hβ hW.le hQ hD.le hA1r hCm.le hA3.le

/-- 27.74 (i), ω > 0 (R-image) -/
theorem Frame20.om1p_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (htt : 0 ≤ -F.S.sm + F.S.sp) (hom : 0 < (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) :
    IsRupert (Finset.univ.image x) :=
  rupert_of_r (F.rFrame.om1p (hx.comp rperm_bijective.1) (rh hβ) (rh hα) (rh hA1r) (rh htt) (rh hom))

/-- 27.74 (i), ω < 0 (R-image) -/
theorem Frame20.om1n_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (htt : 0 ≤ -F.S.sm + F.S.sp) (hom : 0 < (-F.S.sm*F.S.tp + F.S.sm + F.S.tp - 1) * F.a12 + (F.S.hp*F.S.km) * F.gg) :
    IsRupert (Finset.univ.image x) :=
  rupert_of_r (F.rFrame.om1n (hx.comp rperm_bijective.1) (rh hβ) (rh hα) (rh hA1r) (rh htt) (rh hom))

/-- 27.74 (i), ω = 0, off ℓ1 (R-image) -/
theorem Frame20.om1z1_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (htt : 0 ≤ -F.S.sm + F.S.sp) (hom1 : 0 ≤ (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) (hom2 : 0 ≤ (-F.S.sm*F.S.tp + F.S.sm + F.S.tp - 1) * F.a12 + (F.S.hp*F.S.km) * F.gg) (hl : 0 < (F.S.hp*F.S.sp) * (F.a22 - F.a12) + (F.S.hp*F.S.sp - F.S.hp - F.S.kp*F.S.tp + F.S.kp) * F.a12) :
    IsRupert (Finset.univ.image x) :=
  rupert_of_r (F.rFrame.om1z1 (hx.comp rperm_bijective.1) (rh hβ) (rh hα) (rh hA1r) (rh htt) (rh hom1) (rh hom2) (rh hl))

/-- 27.74 (i), ω = 0, off ℓ1 (R-image) -/
theorem Frame20.om1z2_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (htt : 0 ≤ -F.S.sm + F.S.sp) (hom1 : 0 ≤ (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) (hom2 : 0 ≤ (-F.S.sm*F.S.tp + F.S.sm + F.S.tp - 1) * F.a12 + (F.S.hp*F.S.km) * F.gg) (hl : 0 < (-F.S.hp*F.S.sp) * (F.a22 - F.a12) + (-F.S.hp*F.S.sp + F.S.hp + F.S.kp*F.S.tp - F.S.kp) * F.a12) :
    IsRupert (Finset.univ.image x) :=
  rupert_of_r (F.rFrame.om1z2 (hx.comp rperm_bijective.1) (rh hβ) (rh hα) (rh hA1r) (rh htt) (rh hom1) (rh hom2) (rh hl))

/-- 27.74 (ii): {T_A, V}, h+ ≥ d+ (R-image) -/
theorem Frame20.om2a_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1 : 0 < F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) (hVp : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVW : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hWp : 0 ≤ -F.S.hm - F.S.km*F.S.tm + F.S.km) :
    IsRupert (Finset.univ.image x) :=
  rupert_of_r (F.rFrame.om2a (hx.comp rperm_bijective.1) (rh hβ) (rh hα) (rh hA1) (rh hVp) (rh hVW) (rh hWp))

/-- 27.74 (ii): {T_A, V}, t+ ≤ t−, h+ ≤ d+ (R-image) -/
theorem Frame20.om2b_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1 : 0 < F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) (hVp : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVW : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (htt : 0 ≤ -F.S.sm + F.S.sp) (hWn : 0 ≤ F.S.hm + F.S.km*F.S.tm - F.S.km) :
    IsRupert (Finset.univ.image x) :=
  rupert_of_r (F.rFrame.om2b (hx.comp rperm_bijective.1) (rh hβ) (rh hα) (rh hA1) (rh hVp) (rh hVW) (rh htt) (rh hWn))

/-- 27.74 (ii): {T_A, V, T′}, h+ ≥ d+, p (R-image) -/
theorem Frame20.om3p_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVp : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVW : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hWp : 0 ≤ -F.S.hm - F.S.km*F.S.tm + F.S.km) (hom : 0 < (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg)  :
    IsRupert (Finset.univ.image x) :=
  rupert_of_r (F.rFrame.om3p (hx.comp rperm_bijective.1) (rh hβ) (rh hα) (rh hA1r) (rh hVp) (rh hVW) (rh hWp) (rh hom))

/-- 27.74 (ii): {T_A, V, T′}, h+ ≥ d+, n (R-image) -/
theorem Frame20.om3n_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVp : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVW : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hWp : 0 ≤ -F.S.hm - F.S.km*F.S.tm + F.S.km) (hom : 0 < (-F.S.sm*F.S.tp + F.S.sm + F.S.tp - 1) * F.a12 + (F.S.hp*F.S.km) * F.gg)  :
    IsRupert (Finset.univ.image x) :=
  rupert_of_r (F.rFrame.om3n (hx.comp rperm_bijective.1) (rh hβ) (rh hα) (rh hA1r) (rh hVp) (rh hVW) (rh hWp) (rh hom))

/-- 27.74 (ii): {T_A, V, T′}, h+ ≥ d+, z1 (R-image) -/
theorem Frame20.om3z1_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVp : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVW : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hWp : 0 ≤ -F.S.hm - F.S.km*F.S.tm + F.S.km) (hom1 : 0 ≤ (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) (hom2 : 0 ≤ (-F.S.sm*F.S.tp + F.S.sm + F.S.tp - 1) * F.a12 + (F.S.hp*F.S.km) * F.gg) (hl : 0 < (F.S.hp*F.S.sp) * (F.a22 - F.a12) + (F.S.hp*F.S.sp - F.S.hp - F.S.kp*F.S.tp + F.S.kp) * F.a12)  :
    IsRupert (Finset.univ.image x) :=
  rupert_of_r (F.rFrame.om3z1 (hx.comp rperm_bijective.1) (rh hβ) (rh hα) (rh hA1r) (rh hVp) (rh hVW) (rh hWp) (rh hom1) (rh hom2) (rh hl))

/-- 27.74 (ii): {T_A, V, T′}, h+ ≥ d+, z2 (R-image) -/
theorem Frame20.om3z2_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVp : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVW : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hWp : 0 ≤ -F.S.hm - F.S.km*F.S.tm + F.S.km) (hom1 : 0 ≤ (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) (hom2 : 0 ≤ (-F.S.sm*F.S.tp + F.S.sm + F.S.tp - 1) * F.a12 + (F.S.hp*F.S.km) * F.gg) (hl : 0 < (-F.S.hp*F.S.sp) * (F.a22 - F.a12) + (-F.S.hp*F.S.sp + F.S.hp + F.S.kp*F.S.tp - F.S.kp) * F.a12)  :
    IsRupert (Finset.univ.image x) :=
  rupert_of_r (F.rFrame.om3z2 (hx.comp rperm_bijective.1) (rh hβ) (rh hα) (rh hA1r) (rh hVp) (rh hVW) (rh hWp) (rh hom1) (rh hom2) (rh hl))

/-- 27.76 N4 p (R-image) -/
theorem Frame20.om4ap_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hA1R : 0 < F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) (hVpR : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm - F.S.kp*F.S.tm) (hVWR : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.sp + F.S.hp*F.S.tm - F.S.hp - F.S.kp*F.S.tm + F.S.kp) (hKb : 0 < F.S.hp*F.S.sp - F.S.hp + F.S.kp) (hss : 0 < -F.S.tm + F.S.tp) (hnu : 0 < (-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 + (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg) :
    IsRupert (Finset.univ.image x) :=
  F.om4ap_R_cc hx hα hβ hA1r hA1R hVpR hVWR hKb.le hss hnu

/-- 27.76 N4 n (R-image) -/
theorem Frame20.om4an_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hA1R : 0 < F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) (hVpR : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm - F.S.kp*F.S.tm) (hVWR : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.sp + F.S.hp*F.S.tm - F.S.hp - F.S.kp*F.S.tm + F.S.kp) (hKb : 0 < F.S.hp*F.S.sp - F.S.hp + F.S.kp) (hss : 0 < -F.S.tm + F.S.tp) (hnu : 0 < (F.S.sm*F.S.sp*F.S.tp - F.S.sm*F.S.tp - F.S.sp*F.S.tp + F.S.tp) * F.a12 + (-F.S.hp*F.S.km*F.S.sp + F.S.hp*F.S.km - F.S.km*F.S.kp) * F.gg) :
    IsRupert (Finset.univ.image x) :=
  F.om4an_R_cc hx hα hβ hA1r hA1R hVpR hVWR hKb.le hss hnu

/-- 27.76 N4 z1 (R-image) -/
theorem Frame20.om4az1_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hA1R : 0 < F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) (hVpR : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm - F.S.kp*F.S.tm) (hVWR : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.sp + F.S.hp*F.S.tm - F.S.hp - F.S.kp*F.S.tm + F.S.kp) (hKb : 0 < F.S.hp*F.S.sp - F.S.hp + F.S.kp) (hss : 0 < -F.S.tm + F.S.tp) (hnu1 : 0 ≤ (-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 + (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg) (hnu2 : 0 ≤ (F.S.sm*F.S.sp*F.S.tp - F.S.sm*F.S.tp - F.S.sp*F.S.tp + F.S.tp) * F.a12 + (-F.S.hp*F.S.km*F.S.sp + F.S.hp*F.S.km - F.S.km*F.S.kp) * F.gg) (hl : 0 < (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * (F.a22 - F.a12) + (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * F.a12 + (-F.S.km*F.S.kp) * F.gg) :
    IsRupert (Finset.univ.image x) :=
  F.om4az1_R_cc hx hα hβ hA1r hA1R hVpR hVWR hKb.le hss hnu1 hnu2 hl

/-- 27.76 N4 z2 (R-image) -/
theorem Frame20.om4az2_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hA1R : 0 < F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) (hVpR : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm - F.S.kp*F.S.tm) (hVWR : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.sp + F.S.hp*F.S.tm - F.S.hp - F.S.kp*F.S.tm + F.S.kp) (hKb : 0 < F.S.hp*F.S.sp - F.S.hp + F.S.kp) (hss : 0 < -F.S.tm + F.S.tp) (hnu1 : 0 ≤ (-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 + (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg) (hnu2 : 0 ≤ (F.S.sm*F.S.sp*F.S.tp - F.S.sm*F.S.tp - F.S.sp*F.S.tp + F.S.tp) * F.a12 + (-F.S.hp*F.S.km*F.S.sp + F.S.hp*F.S.km - F.S.km*F.S.kp) * F.gg) (hl : 0 < (-F.S.sm*F.S.sp + F.S.sm + F.S.sp - 1) * (F.a22 - F.a12) + (-F.S.sm*F.S.sp + F.S.sm + F.S.sp - 1) * F.a12 + (F.S.km*F.S.kp) * F.gg) :
    IsRupert (Finset.univ.image x) :=
  F.om4az2_R_cc hx hα hβ hA1r hA1R hVpR hVWR hKb.le hss hnu1 hnu2 hl

/-- 27.76 Rv p (R-image) -/
theorem Frame20.om4bp_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hA1R : 0 < F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) (hVR : 0 < F.S.hm*F.S.sp*F.S.tp - F.S.hm*F.S.tp + F.S.hp*F.S.sp*F.S.tm - F.S.hp*F.S.tm + F.S.kp*F.S.tm) (hKb : 0 < F.S.hp*F.S.sp - F.S.hp + F.S.kp) (hnu : 0 < (-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 + (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg)   :
    IsRupert (Finset.univ.image x) :=
  F.om4bp_R_cc hx hα hβ hA1r hA1R hVR hKb.le hnu

/-- 27.76 Rv n (R-image) -/
theorem Frame20.om4bn_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hA1R : 0 < F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) (hVR : 0 < F.S.hm*F.S.sp*F.S.tp - F.S.hm*F.S.tp + F.S.hp*F.S.sp*F.S.tm - F.S.hp*F.S.tm + F.S.kp*F.S.tm) (hKb : 0 < F.S.hp*F.S.sp - F.S.hp + F.S.kp) (hnu : 0 < (F.S.sm*F.S.sp*F.S.tp - F.S.sm*F.S.tp - F.S.sp*F.S.tp + F.S.tp) * F.a12 + (-F.S.hp*F.S.km*F.S.sp + F.S.hp*F.S.km - F.S.km*F.S.kp) * F.gg)   :
    IsRupert (Finset.univ.image x) :=
  F.om4bn_R_cc hx hα hβ hA1r hA1R hVR hKb.le hnu

/-- 27.76 Rv z1 (R-image) -/
theorem Frame20.om4bz1_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hA1R : 0 < F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) (hVR : 0 < F.S.hm*F.S.sp*F.S.tp - F.S.hm*F.S.tp + F.S.hp*F.S.sp*F.S.tm - F.S.hp*F.S.tm + F.S.kp*F.S.tm) (hKb : 0 < F.S.hp*F.S.sp - F.S.hp + F.S.kp) (hnu1 : 0 ≤ (-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 + (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg) (hnu2 : 0 ≤ (F.S.sm*F.S.sp*F.S.tp - F.S.sm*F.S.tp - F.S.sp*F.S.tp + F.S.tp) * F.a12 + (-F.S.hp*F.S.km*F.S.sp + F.S.hp*F.S.km - F.S.km*F.S.kp) * F.gg) (hl : 0 < (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * (F.a22 - F.a12) + (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * F.a12 + (-F.S.km*F.S.kp) * F.gg)   :
    IsRupert (Finset.univ.image x) :=
  F.om4bz1_R_cc hx hα hβ hA1r hA1R hVR hKb.le hnu1 hnu2 hl

/-- 27.76 Rv z2 (R-image) -/
theorem Frame20.om4bz2_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hA1R : 0 < F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) (hVR : 0 < F.S.hm*F.S.sp*F.S.tp - F.S.hm*F.S.tp + F.S.hp*F.S.sp*F.S.tm - F.S.hp*F.S.tm + F.S.kp*F.S.tm) (hKb : 0 < F.S.hp*F.S.sp - F.S.hp + F.S.kp) (hnu1 : 0 ≤ (-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 + (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg) (hnu2 : 0 ≤ (F.S.sm*F.S.sp*F.S.tp - F.S.sm*F.S.tp - F.S.sp*F.S.tp + F.S.tp) * F.a12 + (-F.S.hp*F.S.km*F.S.sp + F.S.hp*F.S.km - F.S.km*F.S.kp) * F.gg) (hl : 0 < (-F.S.sm*F.S.sp + F.S.sm + F.S.sp - 1) * (F.a22 - F.a12) + (-F.S.sm*F.S.sp + F.S.sm + F.S.sp - 1) * F.a12 + (F.S.km*F.S.kp) * F.gg)   :
    IsRupert (Finset.univ.image x) :=
  F.om4bz2_R_cc hx hα hβ hA1r hA1R hVR hKb.le hnu1 hnu2 hl

/-- family A, T1 (⟨u1,u2⟩ > 0) (R-image) -/
theorem Frame20.famA1_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1 : 0 < F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) (hA2 : 0 < -F.S.hp*F.S.sp + F.S.km*F.S.sp*F.S.tp + F.S.kp*F.S.sm*F.S.tp) (hA3 : 0 < F.S.hp*F.S.sp - F.S.hp - F.S.km*F.S.sp*F.S.tp + F.S.km*F.S.tp - F.S.kp*F.S.sm*F.S.tp + F.S.kp) (hg : 0 < (F.S.sm^2 - F.S.sm) * (F.a22 - F.a12) + (F.S.sm^2 - 2*F.S.sm + 1) * F.a12 + (F.S.km^2) * F.gg)   :
    IsRupert (Finset.univ.image x) :=
  rupert_of_r (F.rFrame.famA1 (hx.comp rperm_bijective.1) (rh hβ) (rh hα) (rh hA1) (rh hA2) (rh hA3) (rh hg))

/-- family A, T2 (⟨u1,u2⟩ ≤ 0) (R-image) -/
theorem Frame20.famA2_R {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1 : 0 < F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) (hA2 : 0 < -F.S.hp*F.S.sp + F.S.km*F.S.sp*F.S.tp + F.S.kp*F.S.sm*F.S.tp) (hA3 : 0 < F.S.hp*F.S.sp - F.S.hp - F.S.km*F.S.sp*F.S.tp + F.S.km*F.S.tp - F.S.kp*F.S.sm*F.S.tp + F.S.kp) (hg : 0 ≤ (-F.S.sm^2 + F.S.sm) * (F.a22 - F.a12) + (-F.S.sm^2 + 2*F.S.sm - 1) * F.a12 + (-F.S.km^2) * F.gg)   :
    IsRupert (Finset.univ.image x) :=
  rupert_of_r (F.rFrame.famA2 (hx.comp rperm_bijective.1) (rh hβ) (rh hα) (rh hA1) (rh hA2) (rh hA3) (rh hg))

end Minimality.CaseC20

end

