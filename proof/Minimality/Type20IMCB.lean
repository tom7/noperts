module

public import Minimality.Type20IMCA

@[expose] public section

/-!
# Type 20, item I_MC (part B): the generic leaves L1, L2, L4-L7, L9, L10

Silhouette leaves of I_MC that need no special position of the shape: the polynomial depths,
facings and unimodality at the covering views, for the sign regions `A < 0`, `Q < 0` (L1, L2) and
`A > 0`, `Q >= 0` (L4-L7, L9, L10), with their shape algebra (`G5a`).
-/

section

/-!
# G1: leaf L1 of I_MC, view `s35:1346[C^D^]` (needs only `A < 0`)
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace Frame20
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- **I_MC leaf L1** (`A < 0`): on the I_MC locus with `A = hm tp - hm + hp tm < 0`, the point set
is Rupert, by the segment leaf `s35:1346[C^D^]` (view `x5 - x3`). -/
theorem imc_L1 (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hI : F.IMC) (hA : (F.S.hm*F.S.tp-F.S.hm+F.S.hp*F.S.tm) < 0) : IsRupert (Finset.univ.image x) := by
  set FF := h20s_fac hR with hFF
  obtain ⟨r, B, P⟩ := F.par hI
  have ht := F.one_sub_tm_pos; have hs := F.one_sub_sp_pos; have hs' := F.one_sub_sm_pos
  have ht' := F.one_sub_tp_pos
  have tp := F.S.tp_pos; have tm := F.S.tm_pos; have hm := F.S.hm_pos; have hp := F.S.hp_pos
  have km := F.S.km_pos; have sm := F.S.sm_pos; have kp := F.S.kp_pos
  have roof := F.roof_pos; have lroof := F.lroof_pos
  have hq := IVT.seg_vec F 3 5 ⟨-F.S.tm, 0, F.S.hm⟩ (by rw [F.ptC_3, F.ptC_5]; simp [C3.sub])
  refine h20s_I_s35 FF hx ?_ ?_ ?_ ?_
  · exact (F.nrm_E FF).seg_pos hq (by simp only; linarith)
  · refine (F.nrm_F FF).seg_pos hq ?_
    simp only
    have e : (1 - F.S.tp) * (-F.S.tm * (F.S.kp - F.S.hp * (1 - F.S.sp)) + 0 * (F.S.kp * F.S.tp) + F.S.hm * (F.S.tp * (1 - F.S.sp))) =
        -((1 - F.S.sp) * F.S.tp * (F.S.hm*F.S.tp-F.S.hm+F.S.hp*F.S.tm)) + F.S.tm * (F.S.hp*(1-F.S.sp)-F.S.kp*(1-F.S.tp)) := by ring
    apply pos_of_mul_pos' ht'
    rw [e]
    nlinarith [mul_pos (mul_pos hs tp) (neg_pos.2 hA), mul_pos tm roof]
  · refine (F.nrm_G FF).seg_neg hq ?_
    simp only
    nlinarith [mul_pos tm km, mul_pos hm hs']
  · rw [hq]
    refine F.robUni_of_dep _ _ (robUni4 ?_ ?_)
    · rintro ⟨a1, a2, a3, a4⟩
      have key : F.dep ⟨-F.S.tm, 0, F.S.hm⟩ 1 < F.dep ⟨-F.S.tm, 0, F.S.hm⟩ 6 := by
        refine F.dlt P _ ?_
        have e : F.Dd B ⟨-F.S.tm, 0, F.S.hm⟩ 6 - F.Dd B ⟨-F.S.tm, 0, F.S.hm⟩ 1 = F.S.hp * F.S.tm * (F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm)) := by
          simp only [Dd]; ring
        have := mul_pos (mul_pos hp tm) lroof
        linarith
      exact absurd a3 (not_le.2 key)
    · rintro ⟨a1, a2, a3, a4⟩
      have key : F.dep ⟨-F.S.tm, 0, F.S.hm⟩ 3 < F.dep ⟨-F.S.tm, 0, F.S.hm⟩ 1 := by
        refine F.dlt P _ ?_
        have e : F.Dd B ⟨-F.S.tm, 0, F.S.hm⟩ 1 - F.Dd B ⟨-F.S.tm, 0, F.S.hm⟩ 3 = -(F.S.sm * F.S.hm * (1-F.S.tm) * (F.S.hm*F.S.tp-F.S.hm+F.S.hp*F.S.tm)) := by
          simp only [Dd]; ring
        have := mul_pos (mul_pos (mul_pos sm hm) ht) (neg_pos.2 hA)
        linarith
      exact absurd a1 (not_le.2 key)

end Frame20
end Minimality.CaseC20

end

section

/-!
# G2: leaf L2 of I_MC, view `s01:0546[C^E^]` (`A > 0`, `Q < 0`)
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace Frame20
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- **I_MC leaf L2** (`A > 0`, `Q < 0`): on the I_MC locus the point set is Rupert, by the segment
leaf `s01:0546[C^E^]` (view `x1 - x0`; literals `D+` is `sm A > 0`, `H-` is `-kp (1-tp) < 0`;
the depths in the cycle `0,5,4,6` die on `z0 < z6` (that is `Q < 0`) and `z5 < z4`). -/
theorem imc_L2 (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hI : F.IMC) (hA : 0 < (F.S.hm*F.S.tp-F.S.hm+F.S.hp*F.S.tm)) (hQ : (F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm)) < 0) : IsRupert (Finset.univ.image x) := by
  set FF := h20s_fac hR with hFF
  obtain ⟨r, B, P⟩ := F.par hI
  have ht := F.one_sub_tm_pos; have hs := F.one_sub_sp_pos; have hs' := F.one_sub_sm_pos
  have ht' := F.one_sub_tp_pos
  have tp := F.S.tp_pos; have tm := F.S.tm_pos; have hm := F.S.hm_pos; have hp := F.S.hp_pos
  have km := F.S.km_pos; have sm := F.S.sm_pos; have kp := F.S.kp_pos
  have hq := IVT.seg_vec F 0 1 ⟨1 - F.S.tp, 0, -F.S.hp⟩ (by rw [F.ptC_0, F.ptC_1]; simp [C3.sub])
  refine h20s_I_s01 FF hx ?_ ?_ ?_
  · refine (F.nrm_D FF).seg_pos hq ?_
    simp only
    have e : (1 - F.S.tp) * -(F.S.hm * F.S.sm) + 0 * -(F.S.km * F.S.tm) + -F.S.hp * -(F.S.sm * F.S.tm) = F.S.sm * (F.S.hm*F.S.tp-F.S.hm+F.S.hp*F.S.tm) := by ring
    rw [e]; exact mul_pos sm hA
  · refine (F.nrm_H FF).seg_neg hq ?_
    simp only
    nlinarith [mul_pos ht' kp]
  · rw [hq]
    refine F.robUni_of_dep _ _ (robUni4 ?_ ?_)
    · rintro ⟨a1, a2, a3, a4⟩
      have key : F.dep ⟨1 - F.S.tp, 0, -F.S.hp⟩ 0 < F.dep ⟨1 - F.S.tp, 0, -F.S.hp⟩ 6 := by
        refine F.dlt P _ ?_
        have e : F.Dd B ⟨1 - F.S.tp, 0, -F.S.hp⟩ 6 - F.Dd B ⟨1 - F.S.tp, 0, -F.S.hp⟩ 0 =
            -(F.S.hp * (1 - F.S.tp) * (F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))) := by
          simp only [Dd]; ring
        have := mul_pos (mul_pos hp ht') (neg_pos.2 hQ)
        linarith
      exact absurd a3 (not_le.2 key)
    · rintro ⟨a1, a2, a3, a4⟩
      have key : F.dep ⟨1 - F.S.tp, 0, -F.S.hp⟩ 5 < F.dep ⟨1 - F.S.tp, 0, -F.S.hp⟩ 4 := by
        refine F.dlt P _ ?_
        have e : F.Dd B ⟨1 - F.S.tp, 0, -F.S.hp⟩ 4 - F.Dd B ⟨1 - F.S.tp, 0, -F.S.hp⟩ 5 =
            F.S.hp * F.S.sm * (1 - F.S.tp) * F.S.hm := by
          simp only [Dd]; ring
        have := mul_pos (mul_pos (mul_pos hp sm) ht') hm
        linarith
      exact absurd a3 (not_le.2 key)

end Frame20
end Minimality.CaseC20

end

section

/-!
# G3: leaf L6 of I_MC, line view `LCF:01346[C^F^]` (`Q >= 0`, `K > 0`, `F15 >= 0`, `Vq > 0`)
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace Frame20
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- **I_MC leaf L6**: with `Q >= 0`, `K = km - hm > 0`, `F15 >= 0`, `Vq > 0` the point set is Rupert,
by the line leaf `LCF:01346[C^F^]` (view `N_C x N_F`, either orientation).  The view is
`nu * (tp (1-sp), 0, -F15)`; facings (A, E, G up; B, D, H down): `sm R1`, `roof`,
`(1-sm) F15 + km tp (1-sp)`, `-kp sp tp`, `-sm Vq`, `-kp tp (1-sp)`; depth order
`z1 > z3 > z4`, `z1 > z0 > z6`. -/
theorem imc_L6 (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hI : F.IMC) (hQ : 0 ≤ (F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))) (hK : 0 < (F.S.km-F.S.hm)) (hF : 0 ≤ (F.S.kp-F.S.hp*(1-F.S.sp))) (hV : 0 < ((1-F.S.sp)*(F.S.hm*F.S.tp+F.S.hp*F.S.tm)-F.S.kp*F.S.tm)) :
    IsRupert (Finset.univ.image x) := by
  set FF := h20s_fac hR with hFF
  obtain ⟨r, B, P⟩ := F.par hI
  have ht := F.one_sub_tm_pos; have hs := F.one_sub_sp_pos; have hs' := F.one_sub_sm_pos
  have ht' := F.one_sub_tp_pos
  have tp := F.S.tp_pos; have tm := F.S.tm_pos; have hm := F.S.hm_pos; have hp := F.S.hp_pos
  have km := F.S.km_pos; have sm := F.S.sm_pos; have kp := F.S.kp_pos; have sp := F.S.sp_pos
  have roof := F.roof_pos; have lroof := F.lroof_pos
  have hc0 : 0 < (F.S.hm*F.S.tp+F.S.hp*F.S.tm) := by positivity
  have hR1 : 0 < ((1-F.S.sp)*(F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm))+(1-F.S.tm)*F.S.kp) := by
    nlinarith [mul_pos (mul_pos hm tp) hs, mul_nonneg ht.le hF]
  have fG : 0 < F.S.km * (F.S.tp * (1 - F.S.sp)) + (F.S.kp-F.S.hp*(1-F.S.sp)) * (1 - F.S.sm) := by
    nlinarith [mul_pos (mul_pos km tp) hs, mul_nonneg hs'.le hF]
  obtain ⟨ν, hν, hc⟩ := F.line_view FF 2 5 (F.nrm_C FF) (F.nrm_F FF) (κ := -(F.S.hm*F.S.tp+F.S.hp*F.S.tm))
    (wx := F.S.tp * (1 - F.S.sp)) (wy := 0) (wz := -(F.S.kp-F.S.hp*(1-F.S.sp))) (neg_ne_zero.2 hc0.ne')
    (Or.inl (mul_pos tp hs).ne') (by ring) (by ring) (by ring)
  have dscale := fun j => F.dep_scale ν (F.S.tp * (1 - F.S.sp)) 0 (-(F.S.kp-F.S.hp*(1-F.S.sp))) j
  have hU : RobUni (fun a : ZMod 5 => ⟪x (h20s_LCF.c a), cross (FF.N 2) (FF.N 5)⟫) := by
    rw [hc]
    refine F.robUni_line _ ⟨F.S.tp * (1 - F.S.sp), 0, -(F.S.kp-F.S.hp*(1-F.S.sp))⟩ hν ?_
    have d13 : F.dep ⟨F.S.tp * (1 - F.S.sp), 0, -(F.S.kp-F.S.hp*(1-F.S.sp))⟩ 3 < F.dep ⟨F.S.tp * (1 - F.S.sp), 0, -(F.S.kp-F.S.hp*(1-F.S.sp))⟩ 1 := by
      refine F.dlt P _ ?_
      have e : F.Dd B ⟨F.S.tp * (1 - F.S.sp), 0, -(F.S.kp-F.S.hp*(1-F.S.sp))⟩ 1 - F.Dd B ⟨F.S.tp * (1 - F.S.sp), 0, -(F.S.kp-F.S.hp*(1-F.S.sp))⟩ 3 =
          F.S.sm * F.S.hm * (1-F.S.tm) * (F.S.hp*(1-F.S.sp)-F.S.kp*(1-F.S.tp)) := by
        simp only [Dd]; ring
      have := mul_pos (mul_pos (mul_pos sm hm) ht) roof
      linarith
    have d34 : F.dep ⟨F.S.tp * (1 - F.S.sp), 0, -(F.S.kp-F.S.hp*(1-F.S.sp))⟩ 4 < F.dep ⟨F.S.tp * (1 - F.S.sp), 0, -(F.S.kp-F.S.hp*(1-F.S.sp))⟩ 3 := by
      refine F.dlt P _ ?_
      have e : F.Dd B ⟨F.S.tp * (1 - F.S.sp), 0, -(F.S.kp-F.S.hp*(1-F.S.sp))⟩ 3 - F.Dd B ⟨F.S.tp * (1 - F.S.sp), 0, -(F.S.kp-F.S.hp*(1-F.S.sp))⟩ 4 =
          F.S.sm * (F.S.km-F.S.hm) * (1-F.S.tm) * (F.S.hp*(1-F.S.sp)-F.S.kp*(1-F.S.tp)) := by
        simp only [Dd]; ring
      have := mul_pos (mul_pos (mul_pos sm hK) ht) roof
      linarith
    have d01 : F.dep ⟨F.S.tp * (1 - F.S.sp), 0, -(F.S.kp-F.S.hp*(1-F.S.sp))⟩ 0 < F.dep ⟨F.S.tp * (1 - F.S.sp), 0, -(F.S.kp-F.S.hp*(1-F.S.sp))⟩ 1 := by
      refine F.dlt P _ ?_
      have e : F.Dd B ⟨F.S.tp * (1 - F.S.sp), 0, -(F.S.kp-F.S.hp*(1-F.S.sp))⟩ 1 - F.Dd B ⟨F.S.tp * (1 - F.S.sp), 0, -(F.S.kp-F.S.hp*(1-F.S.sp))⟩ 0 =
          F.S.hp * F.S.sm * (1 - F.S.tp) * ((1-F.S.sp)*(F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm))+(1-F.S.tm)*F.S.kp) := by
        simp only [Dd]; ring
      have := mul_pos (mul_pos (mul_pos hp sm) ht') hR1
      linarith
    have d60 : F.dep ⟨F.S.tp * (1 - F.S.sp), 0, -(F.S.kp-F.S.hp*(1-F.S.sp))⟩ 6 < F.dep ⟨F.S.tp * (1 - F.S.sp), 0, -(F.S.kp-F.S.hp*(1-F.S.sp))⟩ 0 := by
      refine F.dlt P _ ?_
      have e : F.Dd B ⟨F.S.tp * (1 - F.S.sp), 0, -(F.S.kp-F.S.hp*(1-F.S.sp))⟩ 0 - F.Dd B ⟨F.S.tp * (1 - F.S.sp), 0, -(F.S.kp-F.S.hp*(1-F.S.sp))⟩ 6 =
          F.S.hp * (F.S.tp * (1 - F.S.sp) * (F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm)) + F.S.sm * (1-F.S.tm) * (F.S.hp*(1-F.S.sp)-F.S.kp*(1-F.S.tp))) := by
        simp only [Dd]; ring
      have h1 : 0 ≤ F.S.tp * (1 - F.S.sp) * (F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm)) := mul_nonneg (mul_pos tp hs).le hQ
      have h2 : 0 < F.S.sm * (1-F.S.tm) * (F.S.hp*(1-F.S.sp)-F.S.kp*(1-F.S.tp)) := mul_pos (mul_pos sm ht) roof
      have := mul_pos hp (add_pos_of_nonneg_of_pos h1 h2)
      linarith
    exact robUni5_L6 d13 d34 d01 d60
  rcases lt_or_gt_of_ne hν with hneg | hpos
  · refine h20s_I_LCF FF hx ?_ ?_ ?_ ?_ ?_ ?_ hU
    · rw [hc]; refine (F.nrm_A FF).fneg' hneg ?_
      nlinarith [mul_pos sm hR1]
    · rw [hc]; refine (F.nrm_B FF).fpos' hneg ?_
      nlinarith [mul_pos (mul_pos sp tp) kp]
    · rw [hc]; refine (F.nrm_D FF).fpos' hneg ?_
      nlinarith [mul_pos sm hV]
    · rw [hc]; refine (F.nrm_E FF).fneg' hneg ?_
      nlinarith [roof]
    · rw [hc]; refine (F.nrm_G FF).fneg' hneg ?_
      nlinarith [fG]
    · rw [hc]; refine (F.nrm_H FF).fpos' hneg ?_
      nlinarith [mul_pos kp (mul_pos tp hs)]
  · refine h20s_I_LCF' FF hx ?_ ?_ ?_ ?_ ?_ ?_ hU
    · rw [hc]; refine (F.nrm_A FF).fpos hpos ?_
      nlinarith [mul_pos sm hR1]
    · rw [hc]; refine (F.nrm_B FF).fneg hpos ?_
      nlinarith [mul_pos (mul_pos sp tp) kp]
    · rw [hc]; refine (F.nrm_D FF).fneg hpos ?_
      nlinarith [mul_pos sm hV]
    · rw [hc]; refine (F.nrm_E FF).fpos hpos ?_
      nlinarith [roof]
    · rw [hc]; refine (F.nrm_G FF).fpos hpos ?_
      nlinarith [fG]
    · rw [hc]; refine (F.nrm_H FF).fneg hpos ?_
      nlinarith [mul_pos kp (mul_pos tp hs)]

end Frame20
end Minimality.CaseC20

end

section

/-!
# G4: leaf L7 of I_MC, line view `LAF:01352[AvFv]` (`Q > 0`, `A > 0`, `F15 >= 0`, `VM > 0`)
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace Frame20
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

set_option maxHeartbeats 1600000 in
/-- **I_MC leaf L7**: with `Q > 0`, `A > 0`, `F15 >= 0`, `VM > 0` the point set is Rupert, by the
line leaf `LAF:01352[AvFv]` (view `N_A x N_F = nu * (tp Y1, -sm R1, f5)`, either orientation).
Facings (B, C up; D, E, G, H down): `kp tp f2`, `sm c0 R1`, `-hm sm VM`, `-roof Q`, `-lroof f3`,
`-kp tp Y1`.  Depths `z0 = z1 > z3 > z5` and `z1 > z2`, the last from
`Dd1 - Dd2 = roof*P2 + F15*sp*lroof*((1-tp)*den + hp*sm*t) + sm*t*W*F15*roof + hp*sp*sm*R1*(B-den)`. -/
theorem imc_L7 (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hI : F.IMC) (hQ : 0 < (F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))) (hA : 0 < (F.S.hm*F.S.tp-F.S.hm+F.S.hp*F.S.tm)) (hF : 0 ≤ (F.S.kp-F.S.hp*(1-F.S.sp))) (hVM : 0 < (((1-F.S.sp)*(F.S.hm*F.S.tp+F.S.hp*F.S.tm)-F.S.kp*F.S.tm)-F.S.tp*(F.S.km*(1-F.S.sp)-F.S.kp*F.S.sm))) :
    IsRupert (Finset.univ.image x) := by
  set FF := h20s_fac hR with hFF
  obtain ⟨r, B, P⟩ := F.par hI
  have hden := P.hden; have hB := P.hB
  have ht := F.one_sub_tm_pos; have hs := F.one_sub_sp_pos; have hs' := F.one_sub_sm_pos
  have ht' := F.one_sub_tp_pos
  have tp := F.S.tp_pos; have tm := F.S.tm_pos; have hm := F.S.hm_pos; have hp := F.S.hp_pos
  have km := F.S.km_pos; have sm := F.S.sm_pos; have kp := F.S.kp_pos; have sp := F.S.sp_pos
  have roof := F.roof_pos; have lroof := F.lroof_pos
  have hc0 : 0 < (F.S.hm*F.S.tp+F.S.hp*F.S.tm) := by positivity
  have hR1 : 0 < ((1-F.S.sp)*(F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm))+(1-F.S.tm)*F.S.kp) := by
    nlinarith [mul_pos (mul_pos hm tp) hs, mul_nonneg ht.le hF]
  have hW : 0 < ((F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))+F.S.hp*F.S.sm*(1-F.S.tm)) := by
    have : 0 < F.S.hp * F.S.sm * (1-F.S.tm) := mul_pos (mul_pos hp sm) ht
    linarith
  have hE0 : 0 < (F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm)) := by
    have e : F.S.sm * (F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm)) = (F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm)) + (F.S.hm+F.S.km*F.S.tm-F.S.km) := by ring
    have : 0 < F.S.sm * (F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm)) := by rw [e]; linarith
    exact pos_of_mul_pos' sm this
  have hY1 : 0 < ((1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*F.S.sm*(1-F.S.tm)) := by
    have := mul_pos (mul_pos kp sm) ht
    have := mul_pos hs hden
    linarith
  have hf5 : 0 < (F.S.hp*(1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*((F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))+F.S.hp*F.S.sm*(1-F.S.tm))) := by
    have := mul_pos (mul_pos hp hs) hden
    have := mul_pos kp hW
    linarith
  have hf2 : 0 < (F.S.sm*((F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm))+F.S.kp*(1-F.S.tm))-F.S.sp*(F.S.hm+F.S.km*F.S.tm-F.S.km)) := by
    have e : (F.S.sm*((F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm))+F.S.kp*(1-F.S.tm))-F.S.sp*(F.S.hm+F.S.km*F.S.tm-F.S.km)) = (F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm)) + (1 - F.S.sp) * (F.S.hm+F.S.km*F.S.tm-F.S.km) + F.S.sm * F.S.kp * (1-F.S.tm) := by ring
    rw [e]
    have := mul_pos hs hden
    have := mul_pos (mul_pos sm kp) ht
    linarith
  have hkmhp : 0 < F.S.km - F.S.hp * F.S.sm := by
    have e : (F.S.km - F.S.hp * F.S.sm) * (1-F.S.tm) = (F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm)) + F.S.hm * (1 - F.S.sm * F.S.tp) := by ring
    have h1 : 0 < F.S.hm * (1 - F.S.sm * F.S.tp) := mul_pos hm (by nlinarith)
    have : 0 < (F.S.km - F.S.hp * F.S.sm) * (1-F.S.tm) := by rw [e]; linarith
    exact pos_of_mul_pos' ht (by linarith [mul_comm (F.S.km - F.S.hp * F.S.sm) (1-F.S.tm)])
  have hf3 : 0 < ((1-F.S.sm*F.S.tp)*(F.S.kp-F.S.hp*(1-F.S.sp))+(1-F.S.sp)*F.S.tp*(F.S.km-F.S.hp*F.S.sm)) := by
    have h1 : 0 ≤ (1 - F.S.sm * F.S.tp) * (F.S.kp-F.S.hp*(1-F.S.sp)) := mul_nonneg (by nlinarith) hF
    have h2 : 0 < (1 - F.S.sp) * F.S.tp * (F.S.km - F.S.hp * F.S.sm) := mul_pos (mul_pos hs tp) hkmhp
    have e : ((1-F.S.sm*F.S.tp)*(F.S.kp-F.S.hp*(1-F.S.sp))+(1-F.S.sp)*F.S.tp*(F.S.km-F.S.hp*F.S.sm)) = (1 - F.S.sm * F.S.tp) * (F.S.kp-F.S.hp*(1-F.S.sp)) + (1 - F.S.sp) * F.S.tp * (F.S.km - F.S.hp * F.S.sm) := by ring
    rw [e]; linarith
  obtain ⟨ν, hν, hc⟩ := F.line_view FF 0 5 (F.nrm_A FF) (F.nrm_F FF) (κ := 1)
    (wx := F.S.tp * ((1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*F.S.sm*(1-F.S.tm))) (wy := -F.S.sm * ((1-F.S.sp)*(F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm))+(1-F.S.tm)*F.S.kp)) (wz := (F.S.hp*(1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*((F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))+F.S.hp*F.S.sm*(1-F.S.tm)))) one_ne_zero
    (Or.inl (mul_pos tp hY1).ne') (by ring) (by ring) (by ring)
  have hU : RobUni (fun a : ZMod 5 => ⟪x (h20s_LAF.c a), cross (FF.N 0) (FF.N 5)⟫) := by
    rw [hc]
    refine F.robUni_line _ ⟨F.S.tp * ((1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*F.S.sm*(1-F.S.tm)), -F.S.sm * ((1-F.S.sp)*(F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm))+(1-F.S.tm)*F.S.kp), (F.S.hp*(1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*((F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))+F.S.hp*F.S.sm*(1-F.S.tm)))⟩ hν ?_
    have d01 : F.dep ⟨F.S.tp * ((1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*F.S.sm*(1-F.S.tm)), -F.S.sm * ((1-F.S.sp)*(F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm))+(1-F.S.tm)*F.S.kp), (F.S.hp*(1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*((F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))+F.S.hp*F.S.sm*(1-F.S.tm)))⟩ 0 = F.dep ⟨F.S.tp * ((1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*F.S.sm*(1-F.S.tm)), -F.S.sm * ((1-F.S.sp)*(F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm))+(1-F.S.tm)*F.S.kp), (F.S.hp*(1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*((F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))+F.S.hp*F.S.sm*(1-F.S.tm)))⟩ 1 := by
      refine F.deq P _ ?_
      simp only [Dd]; ring
    have d31 : F.dep ⟨F.S.tp * ((1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*F.S.sm*(1-F.S.tm)), -F.S.sm * ((1-F.S.sp)*(F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm))+(1-F.S.tm)*F.S.kp), (F.S.hp*(1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*((F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))+F.S.hp*F.S.sm*(1-F.S.tm)))⟩ 3 < F.dep ⟨F.S.tp * ((1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*F.S.sm*(1-F.S.tm)), -F.S.sm * ((1-F.S.sp)*(F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm))+(1-F.S.tm)*F.S.kp), (F.S.hp*(1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*((F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))+F.S.hp*F.S.sm*(1-F.S.tm)))⟩ 1 := by
      refine F.dlt P _ ?_
      have e : F.Dd B ⟨F.S.tp * ((1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*F.S.sm*(1-F.S.tm)), -F.S.sm * ((1-F.S.sp)*(F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm))+(1-F.S.tm)*F.S.kp), (F.S.hp*(1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*((F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))+F.S.hp*F.S.sm*(1-F.S.tm)))⟩ 1 - F.Dd B ⟨F.S.tp * ((1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*F.S.sm*(1-F.S.tm)), -F.S.sm * ((1-F.S.sp)*(F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm))+(1-F.S.tm)*F.S.kp), (F.S.hp*(1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*((F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))+F.S.hp*F.S.sm*(1-F.S.tm)))⟩ 3 =
          F.S.sm * (1-F.S.tm) * (F.S.hm * (1 - F.S.tp) + F.S.hp * (1-F.S.tm)) * (F.S.hp*(1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*((F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))+F.S.hp*F.S.sm*(1-F.S.tm))) := by
        simp only [Dd]; ring
      have := mul_pos (mul_pos (mul_pos sm ht) (by nlinarith : 0 < F.S.hm * (1 - F.S.tp) + F.S.hp * (1-F.S.tm))) hf5
      linarith
    have d53 : F.dep ⟨F.S.tp * ((1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*F.S.sm*(1-F.S.tm)), -F.S.sm * ((1-F.S.sp)*(F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm))+(1-F.S.tm)*F.S.kp), (F.S.hp*(1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*((F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))+F.S.hp*F.S.sm*(1-F.S.tm)))⟩ 5 < F.dep ⟨F.S.tp * ((1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*F.S.sm*(1-F.S.tm)), -F.S.sm * ((1-F.S.sp)*(F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm))+(1-F.S.tm)*F.S.kp), (F.S.hp*(1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*((F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))+F.S.hp*F.S.sm*(1-F.S.tm)))⟩ 3 := by
      refine F.dlt P _ ?_
      have e : F.Dd B ⟨F.S.tp * ((1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*F.S.sm*(1-F.S.tm)), -F.S.sm * ((1-F.S.sp)*(F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm))+(1-F.S.tm)*F.S.kp), (F.S.hp*(1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*((F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))+F.S.hp*F.S.sm*(1-F.S.tm)))⟩ 3 - F.Dd B ⟨F.S.tp * ((1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*F.S.sm*(1-F.S.tm)), -F.S.sm * ((1-F.S.sp)*(F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm))+(1-F.S.tm)*F.S.kp), (F.S.hp*(1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*((F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))+F.S.hp*F.S.sm*(1-F.S.tm)))⟩ 5 =
          F.S.sm * (1-F.S.tm) * (F.S.hm*F.S.tp-F.S.hm+F.S.hp*F.S.tm) * (F.S.hp*(1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*((F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))+F.S.hp*F.S.sm*(1-F.S.tm))) := by
        simp only [Dd]; ring
      have := mul_pos (mul_pos (mul_pos sm ht) hA) hf5
      linarith
    have d21 : F.dep ⟨F.S.tp * ((1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*F.S.sm*(1-F.S.tm)), -F.S.sm * ((1-F.S.sp)*(F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm))+(1-F.S.tm)*F.S.kp), (F.S.hp*(1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*((F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))+F.S.hp*F.S.sm*(1-F.S.tm)))⟩ 2 < F.dep ⟨F.S.tp * ((1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*F.S.sm*(1-F.S.tm)), -F.S.sm * ((1-F.S.sp)*(F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm))+(1-F.S.tm)*F.S.kp), (F.S.hp*(1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*((F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))+F.S.hp*F.S.sm*(1-F.S.tm)))⟩ 1 := by
      refine F.dlt P _ ?_
      have hP2 : 0 < F.S.hm * F.S.hp * F.S.sm ^ 2 * F.S.tp * (1-F.S.tm) * (1 - F.S.sp) +
          F.S.sp * (F.S.hp * F.S.sm * (1-F.S.tm) + (F.S.hm+F.S.km*F.S.tm-F.S.km)) * (F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm)) := by
        have h1 := mul_pos (mul_pos (mul_pos (mul_pos hm hp) (pow_pos sm 2)) tp) ht
        have h3 := mul_pos sp (mul_pos (add_pos (mul_pos (mul_pos hp sm) ht) hden) lroof)
        have h4 := mul_pos h1 hs
        linarith
      have e : F.Dd B ⟨F.S.tp * ((1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*F.S.sm*(1-F.S.tm)), -F.S.sm * ((1-F.S.sp)*(F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm))+(1-F.S.tm)*F.S.kp), (F.S.hp*(1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*((F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))+F.S.hp*F.S.sm*(1-F.S.tm)))⟩ 1 - F.Dd B ⟨F.S.tp * ((1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*F.S.sm*(1-F.S.tm)), -F.S.sm * ((1-F.S.sp)*(F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm))+(1-F.S.tm)*F.S.kp), (F.S.hp*(1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*((F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))+F.S.hp*F.S.sm*(1-F.S.tm)))⟩ 2 =
          (F.S.hp*(1-F.S.sp)-F.S.kp*(1-F.S.tp)) * (F.S.hm * F.S.hp * F.S.sm ^ 2 * F.S.tp * (1-F.S.tm) * (1 - F.S.sp) +
            F.S.sp * (F.S.hp * F.S.sm * (1-F.S.tm) + (F.S.hm+F.S.km*F.S.tm-F.S.km)) * (F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm))) +
          (F.S.kp-F.S.hp*(1-F.S.sp)) * F.S.sp * (F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm)) * ((1 - F.S.tp) * (F.S.hm+F.S.km*F.S.tm-F.S.km) + F.S.hp * F.S.sm * (1-F.S.tm)) +
          F.S.sm * (1-F.S.tm) * ((F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))+F.S.hp*F.S.sm*(1-F.S.tm)) * (F.S.kp-F.S.hp*(1-F.S.sp)) * (F.S.hp*(1-F.S.sp)-F.S.kp*(1-F.S.tp)) + F.S.hp * F.S.sp * F.S.sm * ((1-F.S.sp)*(F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm))+(1-F.S.tm)*F.S.kp) * (B - (F.S.hm+F.S.km*F.S.tm-F.S.km)) := by
        simp only [Dd]; ring
      have t1 := mul_pos roof hP2
      have t2 : 0 ≤ (F.S.kp-F.S.hp*(1-F.S.sp)) * F.S.sp * (F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm)) * ((1 - F.S.tp) * (F.S.hm+F.S.km*F.S.tm-F.S.km) + F.S.hp * F.S.sm * (1-F.S.tm)) :=
        mul_nonneg (mul_nonneg (mul_nonneg hF sp.le) lroof.le)
          (add_pos (mul_pos ht' hden) (mul_pos (mul_pos hp sm) ht)).le
      have t3 : 0 ≤ F.S.sm * (1-F.S.tm) * ((F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))+F.S.hp*F.S.sm*(1-F.S.tm)) * (F.S.kp-F.S.hp*(1-F.S.sp)) * (F.S.hp*(1-F.S.sp)-F.S.kp*(1-F.S.tp)) :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_pos sm ht).le hW.le) hF) roof.le
      have t4 : 0 ≤ F.S.hp * F.S.sp * F.S.sm * ((1-F.S.sp)*(F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm))+(1-F.S.tm)*F.S.kp) * (B - (F.S.hm+F.S.km*F.S.tm-F.S.km)) :=
        mul_nonneg (mul_pos (mul_pos (mul_pos hp sp) sm) hR1).le (by linarith)
      linarith
    exact robUni5_L7 d01 d31 d53 d21
  have fB : F.S.tp * ((1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*F.S.sm*(1-F.S.tm)) * -(F.S.hp * F.S.sp) + -F.S.sm * ((1-F.S.sp)*(F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm))+(1-F.S.tm)*F.S.kp) * -(F.S.kp * F.S.tp) + (F.S.hp*(1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*((F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))+F.S.hp*F.S.sm*(1-F.S.tm))) * (F.S.sp * F.S.tp) =
      F.S.kp * F.S.tp * (F.S.sm*((F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm))+F.S.kp*(1-F.S.tm))-F.S.sp*(F.S.hm+F.S.km*F.S.tm-F.S.km)) := by ring
  have fC : F.S.tp * ((1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*F.S.sm*(1-F.S.tm)) * 0 + -F.S.sm * ((1-F.S.sp)*(F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm))+(1-F.S.tm)*F.S.kp) * -(F.S.hm*F.S.tp+F.S.hp*F.S.tm) + (F.S.hp*(1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*((F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))+F.S.hp*F.S.sm*(1-F.S.tm))) * 0 = F.S.sm * (F.S.hm*F.S.tp+F.S.hp*F.S.tm) * ((1-F.S.sp)*(F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm))+(1-F.S.tm)*F.S.kp) := by ring
  have fD : F.S.tp * ((1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*F.S.sm*(1-F.S.tm)) * -(F.S.hm * F.S.sm) + -F.S.sm * ((1-F.S.sp)*(F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm))+(1-F.S.tm)*F.S.kp) * -(F.S.km * F.S.tm) + (F.S.hp*(1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*((F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))+F.S.hp*F.S.sm*(1-F.S.tm))) * -(F.S.sm * F.S.tm) =
      -(F.S.hm * F.S.sm * (((1-F.S.sp)*(F.S.hm*F.S.tp+F.S.hp*F.S.tm)-F.S.kp*F.S.tm)-F.S.tp*(F.S.km*(1-F.S.sp)-F.S.kp*F.S.sm))) := by ring
  have fE : F.S.tp * ((1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*F.S.sm*(1-F.S.tm)) * F.S.hp + -F.S.sm * ((1-F.S.sp)*(F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm))+(1-F.S.tm)*F.S.kp) * F.S.hp + (F.S.hp*(1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*((F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))+F.S.hp*F.S.sm*(1-F.S.tm))) * (1 - F.S.tp) = -((F.S.hp*(1-F.S.sp)-F.S.kp*(1-F.S.tp)) * (F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))) := by ring
  have fG : F.S.tp * ((1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*F.S.sm*(1-F.S.tm)) * F.S.km + -F.S.sm * ((1-F.S.sp)*(F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm))+(1-F.S.tm)*F.S.kp) * F.S.km + (F.S.hp*(1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*((F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))+F.S.hp*F.S.sm*(1-F.S.tm))) * (F.S.sm - 1) = -((F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm)) * ((1-F.S.sm*F.S.tp)*(F.S.kp-F.S.hp*(1-F.S.sp))+(1-F.S.sp)*F.S.tp*(F.S.km-F.S.hp*F.S.sm))) := by ring
  have fH : F.S.tp * ((1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*F.S.sm*(1-F.S.tm)) * -F.S.kp + -F.S.sm * ((1-F.S.sp)*(F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm))+(1-F.S.tm)*F.S.kp) * 0 + (F.S.hp*(1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*((F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))+F.S.hp*F.S.sm*(1-F.S.tm))) * 0 = -(F.S.kp * F.S.tp * ((1-F.S.sp)*(F.S.hm+F.S.km*F.S.tm-F.S.km)+F.S.kp*F.S.sm*(1-F.S.tm))) := by ring
  rcases lt_or_gt_of_ne hν with hneg | hpos
  · refine h20s_I_LAF' FF hx ?_ ?_ ?_ ?_ ?_ ?_ hU
    · rw [hc]; refine (F.nrm_B FF).fneg' hneg ?_
      rw [fB]; exact mul_pos (mul_pos kp tp) hf2
    · rw [hc]; refine (F.nrm_C FF).fneg' hneg ?_
      rw [fC]; exact mul_pos (mul_pos sm hc0) hR1
    · rw [hc]; refine (F.nrm_D FF).fpos' hneg ?_
      rw [fD]; exact neg_neg_of_pos (mul_pos (mul_pos hm sm) hVM)
    · rw [hc]; refine (F.nrm_E FF).fpos' hneg ?_
      rw [fE]; exact neg_neg_of_pos (mul_pos roof hQ)
    · rw [hc]; refine (F.nrm_G FF).fpos' hneg ?_
      rw [fG]; exact neg_neg_of_pos (mul_pos lroof hf3)
    · rw [hc]; refine (F.nrm_H FF).fpos' hneg ?_
      rw [fH]; exact neg_neg_of_pos (mul_pos (mul_pos kp tp) hY1)
  · refine h20s_I_LAF FF hx ?_ ?_ ?_ ?_ ?_ ?_ hU
    · rw [hc]; refine (F.nrm_B FF).fpos hpos ?_
      rw [fB]; exact mul_pos (mul_pos kp tp) hf2
    · rw [hc]; refine (F.nrm_C FF).fpos hpos ?_
      rw [fC]; exact mul_pos (mul_pos sm hc0) hR1
    · rw [hc]; refine (F.nrm_D FF).fneg hpos ?_
      rw [fD]; exact neg_neg_of_pos (mul_pos (mul_pos hm sm) hVM)
    · rw [hc]; refine (F.nrm_E FF).fneg hpos ?_
      rw [fE]; exact neg_neg_of_pos (mul_pos roof hQ)
    · rw [hc]; refine (F.nrm_G FF).fneg hpos ?_
      rw [fG]; exact neg_neg_of_pos (mul_pos lroof hf3)
    · rw [hc]; refine (F.nrm_H FF).fneg hpos ?_
      rw [fH]; exact neg_neg_of_pos (mul_pos (mul_pos kp tp) hY1)

end Frame20
end Minimality.CaseC20

end

section
--PREFIX=S.

/-!
# G5a: pure shape algebra for leaves L9 and L10 (no frame)

For a `Shape20` `S`: signs of `D16`, `P1`, `LF`, `LE`, `LA`, `B16` in the region
`K >= 0`, `Vq <= 0`, `VM <= 0` (COVER section 5).
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset

namespace Minimality.CaseC20
namespace Shape20
variable (S : Shape20)

lemma roofP : 0 < (S.hp*(1-S.sp)-S.kp*(1-S.tp)) := by linarith [S.roof_p']
lemma lroofP : 0 < (S.km*(1-S.tm)-S.hm*(1-S.sm)) := by linarith [S.roof_m']

/-- `D16 = km tm - hm sm > 0` when `A > 0`, `K >= 0`, `Vq <= 0`, `VM <= 0`. -/
lemma alg_D16 (hA : 0 < (S.hm*S.tp-S.hm+S.hp*S.tm)) (hK : 0 ≤ (S.km-S.hm)) (hV : ((1-S.sp)*(S.hm*S.tp+S.hp*S.tm)-S.kp*S.tm) ≤ 0) (hVM : (((1-S.sp)*(S.hm*S.tp+S.hp*S.tm)-S.kp*S.tm)-S.tp*(S.km*(1-S.sp)-S.kp*S.sm)) ≤ 0) : 0 < (S.km*S.tm-S.hm*S.sm) := by
  by_contra hD
  push Not at hD
  have tp := S.tp_pos; have tm := S.tm_pos; have hm := S.hm_pos; have sm := S.sm_pos
  have hs := S.sp1; have ht' := S.tp1; have roof := S.roofP
  have hts : S.tm ≤ S.sm := by
    have : S.hm * S.tm ≤ S.hm * S.sm := by nlinarith [mul_nonneg hK tm.le]
    exact le_of_mul_le_mul_left this hm
  have hP1 : (S.km*S.tm-S.sm*(S.hm*S.tp+S.hp*S.tm)) < 0 := by
    have : 0 < S.sm * (S.hm*S.tp-S.hm+S.hp*S.tm) := mul_pos sm hA
    nlinarith
  rcases le_or_gt S.tm (S.tp * S.sm) with h1 | h1
  · have e : S.tm * (((1-S.sp)*(S.hm*S.tp+S.hp*S.tm)-S.kp*S.tm)-S.tp*(S.km*(1-S.sp)-S.kp*S.sm)) = ((1-S.sp)*(S.hm*S.tp+S.hp*S.tm)-S.kp*S.tm) * (S.tm - S.tp * S.sm) - S.tp * (1 - S.sp) * (S.km*S.tm-S.sm*(S.hm*S.tp+S.hp*S.tm)) := by ring
    have a1 : 0 ≤ ((1-S.sp)*(S.hm*S.tp+S.hp*S.tm)-S.kp*S.tm) * (S.tm - S.tp * S.sm) := mul_nonneg_of_nonpos_of_nonpos hV (by linarith)
    have a2 : 0 < S.tp * (1 - S.sp) * (-(S.km*S.tm-S.sm*(S.hm*S.tp+S.hp*S.tm))) := mul_pos (mul_pos tp hs) (by linarith)
    have a3 : S.tm * (((1-S.sp)*(S.hm*S.tp+S.hp*S.tm)-S.kp*S.tm)-S.tp*(S.km*(1-S.sp)-S.kp*S.sm)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos tm.le hVM
    nlinarith
  · have e : (1 - S.tp) * (S.tm * (((1-S.sp)*(S.hm*S.tp+S.hp*S.tm)-S.kp*S.tm)-S.tp*(S.km*(1-S.sp)-S.kp*S.sm))) = S.tm * (S.hp*(1-S.sp)-S.kp*(1-S.tp)) * (S.tm - S.tp * S.sm) +
        S.tp * (1 - S.sp) * ((S.hm*S.tp-S.hm+S.hp*S.tm) * (S.sm - S.tm) - (1 - S.tp) * (S.km*S.tm-S.hm*S.sm)) := by ring
    have a1 : 0 < S.tm * (S.hp*(1-S.sp)-S.kp*(1-S.tp)) * (S.tm - S.tp * S.sm) := mul_pos (mul_pos tm roof) (by linarith)
    have a2 : 0 ≤ S.tp * (1 - S.sp) * ((S.hm*S.tp-S.hm+S.hp*S.tm) * (S.sm - S.tm) - (1 - S.tp) * (S.km*S.tm-S.hm*S.sm)) := by
      refine mul_nonneg (mul_pos tp hs).le ?_
      nlinarith [mul_nonneg hA.le (sub_nonneg.2 hts), mul_nonneg ht'.le (neg_nonneg.2 hD)]
    have a3 : (1 - S.tp) * (S.tm * (((1-S.sp)*(S.hm*S.tp+S.hp*S.tm)-S.kp*S.tm)-S.tp*(S.km*(1-S.sp)-S.kp*S.sm))) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos ht'.le (mul_nonpos_of_nonneg_of_nonpos tm.le hVM)
    linarith

/-- `P1 >= 0` when `Q >= 0`, `Vq <= 0`, `VM <= 0`. -/
lemma alg_P1 (hQ : 0 ≤ (S.km*(1-S.tm)-S.hm*(1-S.sm*S.tp)-S.hp*S.sm*(1-S.tm))) (hV : ((1-S.sp)*(S.hm*S.tp+S.hp*S.tm)-S.kp*S.tm) ≤ 0) (hVM : (((1-S.sp)*(S.hm*S.tp+S.hp*S.tm)-S.kp*S.tm)-S.tp*(S.km*(1-S.sp)-S.kp*S.sm)) ≤ 0) : 0 ≤ (S.km*S.tm-S.sm*(S.hm*S.tp+S.hp*S.tm)) := by
  have tp := S.tp_pos; have tm := S.tm_pos; have hm := S.hm_pos; have sm := S.sm_pos
  have hs := S.sp1; have ht := S.tm1
  rcases le_or_gt (S.tp * S.sm) S.tm with h1 | h1
  · have e : (1-S.tm) * (S.km*S.tm-S.sm*(S.hm*S.tp+S.hp*S.tm)) = S.tm * (S.km*(1-S.tm)-S.hm*(1-S.sm*S.tp)-S.hp*S.sm*(1-S.tm)) + S.hm * (S.tm - S.sm * S.tp) := by ring
    have : 0 ≤ (1-S.tm) * (S.km*S.tm-S.sm*(S.hm*S.tp+S.hp*S.tm)) := by
      rw [e]; nlinarith [mul_nonneg tm.le hQ, mul_nonneg hm.le (sub_nonneg.2 h1)]
    by_contra hc
    push Not at hc
    nlinarith [mul_pos ht (neg_pos.2 hc)]
  · have e : S.tm * (((1-S.sp)*(S.hm*S.tp+S.hp*S.tm)-S.kp*S.tm)-S.tp*(S.km*(1-S.sp)-S.kp*S.sm)) = ((1-S.sp)*(S.hm*S.tp+S.hp*S.tm)-S.kp*S.tm) * (S.tm - S.tp * S.sm) - S.tp * (1 - S.sp) * (S.km*S.tm-S.sm*(S.hm*S.tp+S.hp*S.tm)) := by ring
    by_contra hc
    push Not at hc
    have a1 : 0 ≤ ((1-S.sp)*(S.hm*S.tp+S.hp*S.tm)-S.kp*S.tm) * (S.tm - S.tp * S.sm) := mul_nonneg_of_nonpos_of_nonpos hV (by linarith)
    have a2 : 0 < S.tp * (1 - S.sp) * (-(S.km*S.tm-S.sm*(S.hm*S.tp+S.hp*S.tm))) := mul_pos (mul_pos tp hs) (by linarith)
    have a3 : S.tm * (((1-S.sp)*(S.hm*S.tp+S.hp*S.tm)-S.kp*S.tm)-S.tp*(S.km*(1-S.sp)-S.kp*S.sm)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos tm.le hVM
    nlinarith

/-- `LF = sp P1 - sm Vq > 0` off the stratum `Z` (`Vq = P1 = 0`). -/
lemma alg_LF (hP : 0 ≤ (S.km*S.tm-S.sm*(S.hm*S.tp+S.hp*S.tm))) (hV : ((1-S.sp)*(S.hm*S.tp+S.hp*S.tm)-S.kp*S.tm) ≤ 0) (hZ : ¬ (((1-S.sp)*(S.hm*S.tp+S.hp*S.tm)-S.kp*S.tm) = 0 ∧ (S.km*S.tm-S.sm*(S.hm*S.tp+S.hp*S.tm)) = 0)) : 0 < (S.tm*(S.km*S.sp+S.kp*S.sm)-S.sm*(S.hm*S.tp+S.hp*S.tm)) := by
  have sp := S.sp_pos; have sm := S.sm_pos
  have e : (S.tm*(S.km*S.sp+S.kp*S.sm)-S.sm*(S.hm*S.tp+S.hp*S.tm)) = S.sp * (S.km*S.tm-S.sm*(S.hm*S.tp+S.hp*S.tm)) - S.sm * ((1-S.sp)*(S.hm*S.tp+S.hp*S.tm)-S.kp*S.tm) := by ring
  rw [e]
  by_contra hc
  push Not at hc
  apply hZ
  have a1 := mul_nonneg sp.le hP
  have a2 : 0 ≤ -(S.sm * ((1-S.sp)*(S.hm*S.tp+S.hp*S.tm)-S.kp*S.tm)) := by nlinarith
  have h1 : S.sp * (S.km*S.tm-S.sm*(S.hm*S.tp+S.hp*S.tm)) = 0 := by linarith
  have h2 : S.sm * ((1-S.sp)*(S.hm*S.tp+S.hp*S.tm)-S.kp*S.tm) = 0 := by linarith
  exact ⟨(mul_eq_zero.1 h2).resolve_left sm.ne', (mul_eq_zero.1 h1).resolve_left sp.ne'⟩

/-- `LE > 0` for `P1 >= 0`, `A > 0`. -/
lemma alg_LE (hP : 0 ≤ (S.km*S.tm-S.sm*(S.hm*S.tp+S.hp*S.tm))) (hA : 0 < (S.hm*S.tp-S.hm+S.hp*S.tm)) : 0 < (S.hp*S.sp*(S.km*S.tm-S.sm*(S.hm*S.tp+S.hp*S.tm))+S.sm*S.tp*S.kp*(S.hm*S.tp-S.hm+S.hp*S.tm)) := by
  have tp := S.tp_pos; have sm := S.sm_pos; have sp := S.sp_pos; have hp := S.hp_pos
  have kp := S.kp_pos
  have := mul_nonneg (mul_pos hp sp).le hP
  have := mul_pos (mul_pos (mul_pos sm tp) kp) hA
  linarith

/-- `LA > 0` for `Q >= 0`, `E0 > 0`, `P1 >= 0`, `Vq <= 0`, `LF > 0`. -/
lemma alg_LA (hQ : 0 ≤ (S.km*(1-S.tm)-S.hm*(1-S.sm*S.tp)-S.hp*S.sm*(1-S.tm))) (hE0 : 0 < (S.hm*S.tp-S.hp*(1-S.tm))) (hP : 0 ≤ (S.km*S.tm-S.sm*(S.hm*S.tp+S.hp*S.tm))) (hV : ((1-S.sp)*(S.hm*S.tp+S.hp*S.tm)-S.kp*S.tm) ≤ 0) (hLF : 0 < (S.tm*(S.km*S.sp+S.kp*S.sm)-S.sm*(S.hm*S.tp+S.hp*S.tm))) :
    0 < (S.tp*(S.km*S.sp+S.kp*S.sm)-S.sp*(S.hm*S.tp+S.hp*S.tm)) := by
  have tp := S.tp_pos; have tm := S.tm_pos; have hm := S.hm_pos; have sm := S.sm_pos
  have sp := S.sp_pos; have hp := S.hp_pos; have kp := S.kp_pos
  have hs := S.sp1; have ht := S.tm1
  have e : S.tm * (S.tp*(S.km*S.sp+S.kp*S.sm)-S.sp*(S.hm*S.tp+S.hp*S.tm)) = S.tp * (S.tm*(S.km*S.sp+S.kp*S.sm)-S.sm*(S.hm*S.tp+S.hp*S.tm)) - (S.hm*S.tp+S.hp*S.tm) * (S.sp*S.tm-S.sm*S.tp) := by ring
  have hc0 : 0 < (S.hm*S.tp+S.hp*S.tm) := by positivity
  suffices h : 0 < S.tm * (S.tp*(S.km*S.sp+S.kp*S.sm)-S.sp*(S.hm*S.tp+S.hp*S.tm)) from Frame20.pos_of_mul_pos' tm h
  rw [e]
  rcases le_or_gt (S.sp*S.tm-S.sm*S.tp) 0 with hD | hD
  · nlinarith [mul_pos tp hLF, mul_nonneg hc0.le (neg_nonneg.2 hD)]
  · -- `Dl > 0`: `c0 Dl < sp tp P1`
    have e2 : (1-S.tm) * (S.km*S.tm-S.sm*(S.hm*S.tp+S.hp*S.tm)) = S.tm * (S.km*(1-S.tm)-S.hm*(1-S.sm*S.tp)-S.hp*S.sm*(1-S.tm)) + S.hm * (S.tm - S.sm * S.tp) := by ring
    have h1 : S.hm * (S.tm - S.sm * S.tp) ≤ (1-S.tm) * (S.km*S.tm-S.sm*(S.hm*S.tp+S.hp*S.tm)) := by
      rw [e2]; nlinarith [mul_nonneg tm.le hQ]
    have h2 : (S.hm*S.tp+S.hp*S.tm) * (1-S.tm) < S.hm * S.tp := by
      nlinarith [mul_pos tm hE0]
    have h3 : (S.sp*S.tm-S.sm*S.tp) ≤ S.sp * (S.tm - S.sm * S.tp) := by
      nlinarith [mul_pos sm tp, mul_pos (mul_pos sm tp) hs]
    have h4 : (1-S.tm) * ((S.hm*S.tp+S.hp*S.tm) * (S.sp*S.tm-S.sm*S.tp)) < (1-S.tm) * (S.sp * S.tp * (S.km*S.tm-S.sm*(S.hm*S.tp+S.hp*S.tm))) := by
      have a1 : (S.hm*S.tp+S.hp*S.tm) * (1-S.tm) * (S.sp*S.tm-S.sm*S.tp) < S.hm * S.tp * (S.sp*S.tm-S.sm*S.tp) := mul_lt_mul_of_pos_right h2 hD
      have a2 : S.tp * S.hm * (S.sp*S.tm-S.sm*S.tp) ≤ S.tp * S.hm * (S.sp * (S.tm - S.sm * S.tp)) :=
        mul_le_mul_of_nonneg_left h3 (mul_pos tp hm).le
      have a3 : S.sp * S.tp * (S.hm * (S.tm - S.sm * S.tp)) ≤ S.sp * S.tp * ((1-S.tm) * (S.km*S.tm-S.sm*(S.hm*S.tp+S.hp*S.tm))) :=
        mul_le_mul_of_nonneg_left h1 (mul_pos sp tp).le
      nlinarith
    have h5 : (S.hm*S.tp+S.hp*S.tm) * (S.sp*S.tm-S.sm*S.tp) < S.sp * S.tp * (S.km*S.tm-S.sm*(S.hm*S.tp+S.hp*S.tm)) := lt_of_mul_lt_mul_left h4 ht.le
    nlinarith [mul_nonneg sm.le (neg_nonneg.2 hV), mul_nonneg tp.le (mul_nonneg sm.le (neg_nonneg.2 hV))]

/-- `B16 = hp sp - kp tp > 0` from `LG <= 0`, `D16 > 0`, `E0 > 0` (L10). -/
lemma alg_B16 (hD : 0 < (S.km*S.tm-S.hm*S.sm)) (hE0 : 0 < (S.hm*S.tp-S.hp*(1-S.tm))) (hLG : (S.tp*(S.km*S.tm-S.hm*S.sm)*(S.km*S.sp+S.kp*S.sm)-(S.hp*S.km*S.sp*S.tm-S.hm*S.kp*S.sm*S.tp)) ≤ 0) : 0 < (S.hp*S.sp-S.kp*S.tp) := by
  have tp := S.tp_pos; have tm := S.tm_pos; have hm := S.hm_pos; have sm := S.sm_pos
  have sp := S.sp_pos; have hp := S.hp_pos; have kp := S.kp_pos; have km := S.km_pos
  have hs' := S.sm1; have ht := S.tm1; have lroof := S.lroofP
  have hX : 0 < (S.km*S.tm+S.hm*(1-S.sm)) := by
    have := mul_pos km tm; have := mul_pos hm hs'; linarith
  have hkm : 0 < S.km * S.tp - S.hp * (1 - S.sm) := by
    have h1 : S.hm * (S.hp * (1 - S.sm)) < S.hm * (S.km * S.tp) := by
      nlinarith [mul_pos hp lroof, mul_pos km (mul_pos tm hE0), mul_pos km hE0]
    exact Frame20.pos_of_mul_pos' hm (by linarith)
  have e : (S.tp*(S.km*S.tm-S.hm*S.sm)*(S.km*S.sp+S.kp*S.sm)-(S.hp*S.km*S.sp*S.tm-S.hm*S.kp*S.sm*S.tp)) = S.sp * (S.km*S.tm-S.hm*S.sm) * (S.km * S.tp - S.hp * (1 - S.sm)) - S.sm * (S.km*S.tm+S.hm*(1-S.sm)) * (S.hp*S.sp-S.kp*S.tp) := by ring
  by_contra hc
  push Not at hc
  have a1 : 0 < S.sp * (S.km*S.tm-S.hm*S.sm) * (S.km * S.tp - S.hp * (1 - S.sm)) := mul_pos (mul_pos sp hD) hkm
  have a2 : 0 ≤ -(S.sm * (S.km*S.tm+S.hm*(1-S.sm)) * (S.hp*S.sp-S.kp*S.tp)) := by
    have := mul_pos sm hX
    nlinarith
  linarith

end Shape20
end Minimality.CaseC20

end

section
--PREFIX=F.S.

/-!
# G5: leaf L9 of I_MC, line view `LBD:2546[B^D^]`

Hypotheses: `Q >= 0`, `A > 0`, `K >= 0`, `Vq <= 0`, `VM <= 0`, not on the stratum `Z` (`Vq = P1 = 0`),
`LG > 0`, and the depth of `x6` or the `z`-component along the view does not both vanish
(`not (lam = 0 and a12 wx + a22 wy = 0)`: the excluded special position L9').
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.H20S

/-- Robust unimodality of the 4-cycle `(2,5,4,6)` of the chord depths: `z5 = 0`, `z6 = g2`,
`z2 = sp g2 + kp g3`, `z4 = sm g2 - km g3`, with `(g2, g3) != 0`. -/
theorem robUni4_L9 {z : ZMod 4 → ℝ} {sp sm kp km g3 : ℝ} (hsp : 0 < sp) (hsp1 : sp < 1)
    (hsm : 0 < sm) (hsm1 : sm < 1) (hkp : 0 < kp) (hkm : 0 < km)
    (h0 : z 0 = sp * z 3 + kp * g3) (h1 : z 1 = 0) (h2 : z 2 = sm * z 3 - km * g3)
    (hne : z 3 ≠ 0 ∨ g3 ≠ 0) : RobUni z := by
  have key : ¬ ((0 ≤ z 0 ∧ 0 ≤ z 2 ∧ z 3 ≤ z 0 ∧ z 3 ≤ z 2) ∨
      (z 0 ≤ 0 ∧ z 0 ≤ z 3 ∧ z 2 ≤ 0 ∧ z 2 ≤ z 3)) := by
    rintro (⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩)
    · rw [h0] at a1 a3; rw [h2] at a2 a4
      have b1 : 0 ≤ (km * sp + kp * sm) * z 3 := by
        nlinarith [mul_nonneg hkm.le a1, mul_nonneg hkp.le a2]
      have b2 : (km * (sp - 1) + kp * (sm - 1)) * z 3 ≥ 0 := by
        nlinarith [mul_nonneg hkm.le (sub_nonneg.2 a3), mul_nonneg hkp.le (sub_nonneg.2 a4)]
      have c1 : 0 ≤ z 3 := by
        by_contra hc; push Not at hc
        nlinarith [mul_pos (add_pos (mul_pos hkm hsp) (mul_pos hkp hsm)) (neg_pos.2 hc)]
      have c2 : z 3 ≤ 0 := by
        by_contra hc; push Not at hc
        nlinarith [mul_pos (show 0 < km * (1 - sp) + kp * (1 - sm) by nlinarith [mul_pos hkm (sub_pos.2 hsp1), mul_pos hkp (sub_pos.2 hsm1)]) hc]
      have c3 : z 3 = 0 := le_antisymm c2 c1
      rw [c3] at a1 a2
      have : g3 = 0 := by nlinarith
      rcases hne with h | h
      · exact h c3
      · exact h this
    · rw [h0] at a1 a2; rw [h2] at a3 a4
      have b1 : (km * sp + kp * sm) * z 3 ≤ 0 := by
        nlinarith [mul_nonneg hkm.le (neg_nonneg.2 a1), mul_nonneg hkp.le (neg_nonneg.2 a3)]
      have b2 : (km * (sp - 1) + kp * (sm - 1)) * z 3 ≤ 0 := by
        nlinarith [mul_nonneg hkm.le (sub_nonneg.2 a2), mul_nonneg hkp.le (sub_nonneg.2 a4)]
      have c1 : z 3 ≤ 0 := by
        by_contra hc; push Not at hc
        nlinarith [mul_pos (add_pos (mul_pos hkm hsp) (mul_pos hkp hsm)) hc]
      have c2 : 0 ≤ z 3 := by
        by_contra hc; push Not at hc
        nlinarith [mul_pos (show 0 < km * (1 - sp) + kp * (1 - sm) by nlinarith [mul_pos hkm (sub_pos.2 hsp1), mul_pos hkp (sub_pos.2 hsm1)]) (neg_pos.2 hc)]
      have c3 : z 3 = 0 := le_antisymm c1 c2
      rw [c3] at a1 a3
      have : g3 = 0 := by nlinarith
      rcases hne with h | h
      · exact h c3
      · exact h this
  refine robUni4 ?_ ?_
  · rintro ⟨a1, a2, a3, a4⟩
    exact key (Or.inl ⟨by rw [h1] at a1; exact a1, by rw [h1] at a2; exact a2, a3, a4⟩)
  · rintro ⟨a1, a2, a3, a4⟩
    exact key (Or.inr ⟨by rw [h1] at a1; exact a1, a2, by rw [h1] at a3; exact a3, a4⟩)

end Minimality.H20S

namespace Minimality.CaseC20
namespace Frame20
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

set_option maxHeartbeats 1600000 in
/-- **I_MC leaf L9**: in the region `Q >= 0`, `A > 0`, `K >= 0`, `Vq <= 0`, `VM <= 0`, off the stratum
`Z` (`Vq = 0 = P1`), with `LG > 0` (and not the special position `lam = 0`, `a12 wx + a22 wy = 0`),
the point set is Rupert, by the line leaf `LBD:2546[B^D^]` (view `N_B x N_D`, either orientation;
facings `hm sm LA`, `sm sp c0^2`, `LE`, `kp tp LF`, `LG` up, `-kp tm tp kap` down). -/
theorem imc_L9 (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hI : F.IMC) (hQ : 0 ≤ (F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))) (hA : 0 < (F.S.hm*F.S.tp-F.S.hm+F.S.hp*F.S.tm)) (hK : 0 ≤ (F.S.km-F.S.hm)) (hV : ((1-F.S.sp)*(F.S.hm*F.S.tp+F.S.hp*F.S.tm)-F.S.kp*F.S.tm) ≤ 0) (hVM : (((1-F.S.sp)*(F.S.hm*F.S.tp+F.S.hp*F.S.tm)-F.S.kp*F.S.tm)-F.S.tp*(F.S.km*(1-F.S.sp)-F.S.kp*F.S.sm)) ≤ 0)
    (hZ : ¬ (((1-F.S.sp)*(F.S.hm*F.S.tp+F.S.hp*F.S.tm)-F.S.kp*F.S.tm) = 0 ∧ (F.S.km*F.S.tm-F.S.sm*(F.S.hm*F.S.tp+F.S.hp*F.S.tm)) = 0)) (hLG : 0 < (F.S.tp*(F.S.km*F.S.tm-F.S.hm*F.S.sm)*(F.S.km*F.S.sp+F.S.kp*F.S.sm)-(F.S.hp*F.S.km*F.S.sp*F.S.tm-F.S.hm*F.S.kp*F.S.sm*F.S.tp)))
    (hne : ¬ ((F.S.hp*F.S.km*F.S.sp*F.S.tm-F.S.hm*F.S.kp*F.S.sm*F.S.tp) = 0 ∧ F.a12 * (F.S.tm * F.S.tp * (F.S.km*F.S.sp+F.S.kp*F.S.sm)) + F.a22 * (-F.S.sm * F.S.sp * (F.S.hm*F.S.tp+F.S.hp*F.S.tm)) = 0)) :
    IsRupert (Finset.univ.image x) := by
  set FF := h20s_fac hR with hFF
  obtain ⟨r, B, P⟩ := F.par hI
  have hden := P.hden
  have ht := F.one_sub_tm_pos; have hs := F.one_sub_sp_pos; have hs' := F.one_sub_sm_pos
  have tp := F.S.tp_pos; have tm := F.S.tm_pos; have hm := F.S.hm_pos; have hp := F.S.hp_pos
  have km := F.S.km_pos; have sm := F.S.sm_pos; have kp := F.S.kp_pos; have sp := F.S.sp_pos
  have hc0 : 0 < (F.S.hm*F.S.tp+F.S.hp*F.S.tm) := by positivity
  have hkap : 0 < (F.S.km*F.S.sp+F.S.kp*F.S.sm) := by positivity
  have hE0 : 0 < (F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm)) := by
    have e : F.S.sm * (F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm)) = (F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm)) + (F.S.hm+F.S.km*F.S.tm-F.S.km) := by ring
    have : 0 < F.S.sm * (F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm)) := by rw [e]; linarith
    exact pos_of_mul_pos' sm this
  have hP1 := F.S.alg_P1 hQ hV hVM
  have hLF := F.S.alg_LF hP1 hV hZ
  have hLE := F.S.alg_LE hP1 hA
  have hLA := F.S.alg_LA hQ hE0 hP1 hV hLF
  obtain ⟨ν, hν, hc⟩ := F.line_view FF 1 3 (F.nrm_B FF) (F.nrm_D FF) (κ := 1)
    (wx := F.S.tm * F.S.tp * (F.S.km*F.S.sp+F.S.kp*F.S.sm)) (wy := -F.S.sm * F.S.sp * (F.S.hm*F.S.tp+F.S.hp*F.S.tm)) (wz := (F.S.hp*F.S.km*F.S.sp*F.S.tm-F.S.hm*F.S.kp*F.S.sm*F.S.tp)) one_ne_zero
    (Or.inl (mul_pos (mul_pos tm tp) hkap).ne') (by ring) (by ring) (by ring)
  have hU : RobUni (fun a : ZMod 4 => ⟪x (h20s_LBD.c a), cross (FF.N 1) (FF.N 3)⟫) := by
    rw [hc]
    refine F.robUni_line _ ⟨F.S.tm * F.S.tp * (F.S.km*F.S.sp+F.S.kp*F.S.sm), -F.S.sm * F.S.sp * (F.S.hm*F.S.tp+F.S.hp*F.S.tm), (F.S.hp*F.S.km*F.S.sp*F.S.tm-F.S.hm*F.S.kp*F.S.sm*F.S.tp)⟩ hν ?_
    have hg := F.g_pos
    have d2 := F.dep_2 ⟨F.S.tm * F.S.tp * (F.S.km*F.S.sp+F.S.kp*F.S.sm), -F.S.sm * F.S.sp * (F.S.hm*F.S.tp+F.S.hp*F.S.tm), (F.S.hp*F.S.km*F.S.sp*F.S.tm-F.S.hm*F.S.kp*F.S.sm*F.S.tp)⟩
    have d4 := F.dep_4 ⟨F.S.tm * F.S.tp * (F.S.km*F.S.sp+F.S.kp*F.S.sm), -F.S.sm * F.S.sp * (F.S.hm*F.S.tp+F.S.hp*F.S.tm), (F.S.hp*F.S.km*F.S.sp*F.S.tm-F.S.hm*F.S.kp*F.S.sm*F.S.tp)⟩
    have d5 := F.dep_5 ⟨F.S.tm * F.S.tp * (F.S.km*F.S.sp+F.S.kp*F.S.sm), -F.S.sm * F.S.sp * (F.S.hm*F.S.tp+F.S.hp*F.S.tm), (F.S.hp*F.S.km*F.S.sp*F.S.tm-F.S.hm*F.S.kp*F.S.sm*F.S.tp)⟩
    have d6 := F.dep_6 ⟨F.S.tm * F.S.tp * (F.S.km*F.S.sp+F.S.kp*F.S.sm), -F.S.sm * F.S.sp * (F.S.hm*F.S.tp+F.S.hp*F.S.tm), (F.S.hp*F.S.km*F.S.sp*F.S.tm-F.S.hm*F.S.kp*F.S.sm*F.S.tp)⟩
    refine robUni4_L9 (g3 := F.gg * (F.S.hp*F.S.km*F.S.sp*F.S.tm-F.S.hm*F.S.kp*F.S.sm*F.S.tp)) F.S.sp_pos F.S.sp_lt F.S.sm_pos F.S.sm_lt
      F.S.kp_pos F.S.km_pos ?_ ?_ ?_ ?_
    · show F.dep _ 2 = F.S.sp * F.dep _ 6 + F.S.kp * (F.gg * (F.S.hp*F.S.km*F.S.sp*F.S.tm-F.S.hm*F.S.kp*F.S.sm*F.S.tp))
      rw [d2, d6]; ring
    · exact d5
    · show F.dep _ 4 = F.S.sm * F.dep _ 6 - F.S.km * (F.gg * (F.S.hp*F.S.km*F.S.sp*F.S.tm-F.S.hm*F.S.kp*F.S.sm*F.S.tp))
      rw [d4, d6]; ring
    · show F.dep _ 6 ≠ 0 ∨ F.gg * (F.S.hp*F.S.km*F.S.sp*F.S.tm-F.S.hm*F.S.kp*F.S.sm*F.S.tp) ≠ 0
      by_contra hcon
      push Not at hcon
      apply hne
      refine ⟨?_, ?_⟩
      · exact (mul_eq_zero.1 hcon.2).resolve_left hg.ne'
      · rw [d6] at hcon; exact hcon.1
  have fA : F.S.tm * F.S.tp * (F.S.km*F.S.sp+F.S.kp*F.S.sm) * (F.S.hm * F.S.sm) + -F.S.sm * F.S.sp * (F.S.hm*F.S.tp+F.S.hp*F.S.tm) * (F.S.hm+F.S.km*F.S.tm-F.S.km) + (F.S.hp*F.S.km*F.S.sp*F.S.tm-F.S.hm*F.S.kp*F.S.sm*F.S.tp) * -(F.S.sm * (1-F.S.tm)) =
      F.S.hm * F.S.sm * (F.S.tp*(F.S.km*F.S.sp+F.S.kp*F.S.sm)-F.S.sp*(F.S.hm*F.S.tp+F.S.hp*F.S.tm)) := by ring
  have fC : F.S.tm * F.S.tp * (F.S.km*F.S.sp+F.S.kp*F.S.sm) * 0 + -F.S.sm * F.S.sp * (F.S.hm*F.S.tp+F.S.hp*F.S.tm) * -(F.S.hm*F.S.tp+F.S.hp*F.S.tm) + (F.S.hp*F.S.km*F.S.sp*F.S.tm-F.S.hm*F.S.kp*F.S.sm*F.S.tp) * 0 = F.S.sm * F.S.sp * (F.S.hm*F.S.tp+F.S.hp*F.S.tm) * (F.S.hm*F.S.tp+F.S.hp*F.S.tm) := by ring
  have fE : F.S.tm * F.S.tp * (F.S.km*F.S.sp+F.S.kp*F.S.sm) * F.S.hp + -F.S.sm * F.S.sp * (F.S.hm*F.S.tp+F.S.hp*F.S.tm) * F.S.hp + (F.S.hp*F.S.km*F.S.sp*F.S.tm-F.S.hm*F.S.kp*F.S.sm*F.S.tp) * (1 - F.S.tp) = (F.S.hp*F.S.sp*(F.S.km*F.S.tm-F.S.sm*(F.S.hm*F.S.tp+F.S.hp*F.S.tm))+F.S.sm*F.S.tp*F.S.kp*(F.S.hm*F.S.tp-F.S.hm+F.S.hp*F.S.tm)) := by ring
  have fF : F.S.tm * F.S.tp * (F.S.km*F.S.sp+F.S.kp*F.S.sm) * (F.S.kp-F.S.hp*(1-F.S.sp)) + -F.S.sm * F.S.sp * (F.S.hm*F.S.tp+F.S.hp*F.S.tm) * (F.S.kp * F.S.tp) + (F.S.hp*F.S.km*F.S.sp*F.S.tm-F.S.hm*F.S.kp*F.S.sm*F.S.tp) * (F.S.tp * (1 - F.S.sp)) =
      F.S.kp * F.S.tp * (F.S.tm*(F.S.km*F.S.sp+F.S.kp*F.S.sm)-F.S.sm*(F.S.hm*F.S.tp+F.S.hp*F.S.tm)) := by ring
  have fG : F.S.tm * F.S.tp * (F.S.km*F.S.sp+F.S.kp*F.S.sm) * F.S.km + -F.S.sm * F.S.sp * (F.S.hm*F.S.tp+F.S.hp*F.S.tm) * F.S.km + (F.S.hp*F.S.km*F.S.sp*F.S.tm-F.S.hm*F.S.kp*F.S.sm*F.S.tp) * (F.S.sm - 1) = (F.S.tp*(F.S.km*F.S.tm-F.S.hm*F.S.sm)*(F.S.km*F.S.sp+F.S.kp*F.S.sm)-(F.S.hp*F.S.km*F.S.sp*F.S.tm-F.S.hm*F.S.kp*F.S.sm*F.S.tp)) := by ring
  have fH : F.S.tm * F.S.tp * (F.S.km*F.S.sp+F.S.kp*F.S.sm) * -F.S.kp + -F.S.sm * F.S.sp * (F.S.hm*F.S.tp+F.S.hp*F.S.tm) * 0 + (F.S.hp*F.S.km*F.S.sp*F.S.tm-F.S.hm*F.S.kp*F.S.sm*F.S.tp) * 0 =
      -(F.S.kp * F.S.tm * F.S.tp * (F.S.km*F.S.sp+F.S.kp*F.S.sm)) := by ring
  have pA := mul_pos (mul_pos hm sm) hLA
  have pC := mul_pos (mul_pos (mul_pos sm sp) hc0) hc0
  have pF := mul_pos (mul_pos kp tp) hLF
  have pH := mul_pos (mul_pos (mul_pos kp tm) tp) hkap
  rcases lt_or_gt_of_ne hν with hneg | hpos
  · refine h20s_I_LBD' FF hx ?_ ?_ ?_ ?_ ?_ ?_ hU
    · rw [hc]; refine (F.nrm_A FF).fneg' hneg ?_; rw [fA]; exact pA
    · rw [hc]; refine (F.nrm_C FF).fneg' hneg ?_; rw [fC]; exact pC
    · rw [hc]; refine (F.nrm_E FF).fneg' hneg ?_; rw [fE]; exact hLE
    · rw [hc]; refine (F.nrm_F FF).fneg' hneg ?_; rw [fF]; exact pF
    · rw [hc]; refine (F.nrm_G FF).fneg' hneg ?_; rw [fG]; exact hLG
    · rw [hc]; refine (F.nrm_H FF).fpos' hneg ?_; rw [fH]; linarith
  · refine h20s_I_LBD FF hx ?_ ?_ ?_ ?_ ?_ ?_ hU
    · rw [hc]; refine (F.nrm_A FF).fpos hpos ?_; rw [fA]; exact pA
    · rw [hc]; refine (F.nrm_C FF).fpos hpos ?_; rw [fC]; exact pC
    · rw [hc]; refine (F.nrm_E FF).fpos hpos ?_; rw [fE]; exact hLE
    · rw [hc]; refine (F.nrm_F FF).fpos hpos ?_; rw [fF]; exact pF
    · rw [hc]; refine (F.nrm_G FF).fpos hpos ?_; rw [fG]; exact hLG
    · rw [hc]; refine (F.nrm_H FF).fneg hpos ?_; rw [fH]; linarith

end Frame20
end Minimality.CaseC20

end

section
--PREFIX=F.S.

/-!
# G6: leaf L10 of I_MC, new segment cell `s16:0145[E^G^]` (view `x6 - x1`)
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality
namespace H20S
open Minimality.H21

/-- I_MC, `s16:0145[E^G^]`: view `x6 - x1`, up `B E F G H`, down `A C D`, cycle `0,1,4,5`. -/
def h20s_s16 : S0xSeg 7 8 4 where
  i := 1
  j := 6
  pat := ![false, true, false, false, true, true, true, true]
  c := ![0, 1, 4, 5]

theorem h20s_s16_good : h20s_s16.Good h20s_S := by decide

variable {x : Fin 7 → ℝ³}

/-- I_MC, `s16:0145[E^G^]`: literals `B+ D-`. -/
theorem h20s_I_s16 (F : S0xFac 8 h20s_S x) (hx : Function.Injective x)
    (hB : 0 < F.f 1 (x 6) - F.f 1 (x 1)) (hD : F.f 3 (x 6) - F.f 3 (x 1) < 0)
    (hU : RobUni (fun a : ZMod 4 => ⟪x (h20s_s16.c a), x 6 - x 1⟫)) :
    IsRupert (univ.image x) :=
  s0x_seg_rupert F hx h20s_s16 h20s_s16_good ⟨by h20s_lits, hU⟩

end H20S
end Minimality

namespace Minimality.CaseC20
namespace Frame20
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- **I_MC leaf L10**: in the region `Q >= 0`, `A > 0`, `K >= 0`, `Vq <= 0`, `VM <= 0` with `LG <= 0`
the point set is Rupert, by the new segment leaf `s16:0145[E^G^]` (view `x6 - x1`; literals
`B+` is `B16 > 0`, `D-` is `-D16 < 0`; depths `z1 < z0 < 0 = z5`, valid for any `a22 >= a12`). -/
theorem imc_L10 (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hI : F.IMC) (hQ : 0 ≤ (F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))) (hA : 0 < (F.S.hm*F.S.tp-F.S.hm+F.S.hp*F.S.tm)) (hK : 0 ≤ (F.S.km-F.S.hm)) (hV : ((1-F.S.sp)*(F.S.hm*F.S.tp+F.S.hp*F.S.tm)-F.S.kp*F.S.tm) ≤ 0) (hVM : (((1-F.S.sp)*(F.S.hm*F.S.tp+F.S.hp*F.S.tm)-F.S.kp*F.S.tm)-F.S.tp*(F.S.km*(1-F.S.sp)-F.S.kp*F.S.sm)) ≤ 0)
    (hLG : (F.S.tp*(F.S.km*F.S.tm-F.S.hm*F.S.sm)*(F.S.km*F.S.sp+F.S.kp*F.S.sm)-(F.S.hp*F.S.km*F.S.sp*F.S.tm-F.S.hm*F.S.kp*F.S.sm*F.S.tp)) ≤ 0) : IsRupert (Finset.univ.image x) := by
  set FF := h20s_fac hR with hFF
  obtain ⟨r, B, P⟩ := F.par hI
  have hden := P.hden
  have ht := F.one_sub_tm_pos; have ht' := F.one_sub_tp_pos
  have tp := F.S.tp_pos; have tm := F.S.tm_pos; have hm := F.S.hm_pos; have hp := F.S.hp_pos
  have sm := F.S.sm_pos; have lroof := F.lroof_pos
  have hE0 : 0 < (F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm)) := by
    have e : F.S.sm * (F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm)) = (F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm)) + (F.S.hm+F.S.km*F.S.tm-F.S.km) := by ring
    have : 0 < F.S.sm * (F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm)) := by rw [e]; linarith
    exact pos_of_mul_pos' sm this
  have hD := F.S.alg_D16 hA hK hV hVM
  have hB16 := F.S.alg_B16 hD hE0 hLG
  have hq := IVT.seg_vec F 1 6 ⟨-1, 1, 0⟩ (by rw [F.ptC_1, F.ptC_6]; simp [C3.sub])
  refine h20s_I_s16 FF hx ?_ ?_ ?_
  · refine (F.nrm_B FF).seg_pos hq ?_
    simp only; linarith
  · refine (F.nrm_D FF).seg_neg hq ?_
    simp only; linarith
  · rw [hq]
    refine F.robUni_of_dep _ _ (robUni4 ?_ ?_)
    · rintro ⟨a1, a2, a3, a4⟩
      have key : F.dep ⟨-1, 1, 0⟩ 0 < F.dep ⟨-1, 1, 0⟩ 5 := by
        refine F.dlt P _ ?_
        have e : F.Dd B ⟨-1, 1, 0⟩ 5 - F.Dd B ⟨-1, 1, 0⟩ 0 = F.S.hp * F.S.tp * (F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm)) := by
          simp only [Dd]; ring
        have := mul_pos (mul_pos hp tp) lroof
        linarith
      exact absurd a3 (not_le.2 key)
    · rintro ⟨a1, a2, a3, a4⟩
      have key : F.dep ⟨-1, 1, 0⟩ 1 < F.dep ⟨-1, 1, 0⟩ 0 := by
        refine F.dlt P _ ?_
        have e : F.Dd B ⟨-1, 1, 0⟩ 0 - F.Dd B ⟨-1, 1, 0⟩ 1 = F.S.hp * (1 - F.S.tp) * (F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm)) := by
          simp only [Dd]; ring
        have := mul_pos (mul_pos hp ht') lroof
        linarith
      exact absurd a1 (not_le.2 key)

end Frame20
end Minimality.CaseC20

end

section
--PREFIX=F.S.

/-!
# G7: leaves L4 and L5 of I_MC, new segment cells `s13:25346[AvCv]` and `s15:01346[C^]`
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality
namespace H20S
open Minimality.H21

/-- I_MC, `s13:25346[AvCv]`: view `x3 - x1`, up `D H`, down `A B C E F G`, cycle `2,5,3,4,6`
(`A`, `C` are edge-on). -/
def h20s_s13 : S0xSeg 7 8 5 where
  i := 1
  j := 3
  pat := ![false, false, false, true, false, false, false, true]
  c := ![2, 5, 3, 4, 6]

/-- I_MC, `s15:01346[C^]`: view `x1 - x5`, up `A E G`, down `B C D F H`, cycle `0,1,3,4,6`
(`C` is edge-on). -/
def h20s_s15 : S0xSeg 7 8 5 where
  i := 5
  j := 1
  pat := ![true, false, false, false, true, false, true, false]
  c := ![0, 1, 3, 4, 6]

theorem h20s_s13_good : h20s_s13.Good h20s_S := by decide
theorem h20s_s15_good : h20s_s15.Good h20s_S := by decide

variable {x : Fin 7 → ℝ³}

/-- I_MC, `s13:25346[AvCv]`: literals `B- F- H+`. -/
theorem h20s_I_s13 (F : S0xFac 8 h20s_S x) (hx : Function.Injective x)
    (hB : F.f 1 (x 3) - F.f 1 (x 1) < 0) (hF : F.f 5 (x 3) - F.f 5 (x 1) < 0)
    (hH : 0 < F.f 7 (x 3) - F.f 7 (x 1))
    (hU : RobUni (fun a : ZMod 5 => ⟪x (h20s_s13.c a), x 3 - x 1⟫)) :
    IsRupert (univ.image x) :=
  s0x_seg_rupert F hx h20s_s13 h20s_s13_good ⟨by h20s_lits, hU⟩

/-- I_MC, `s15:01346[C^]`: literal `F-`. -/
theorem h20s_I_s15 (F : S0xFac 8 h20s_S x) (hx : Function.Injective x)
    (hF : F.f 5 (x 1) - F.f 5 (x 5) < 0)
    (hU : RobUni (fun a : ZMod 5 => ⟪x (h20s_s15.c a), x 1 - x 5⟫)) :
    IsRupert (univ.image x) :=
  s0x_seg_rupert F hx h20s_s15 h20s_s15_good ⟨by h20s_lits, hU⟩

end H20S
end Minimality

namespace Minimality.CaseC20
namespace Frame20
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- Wrapper: `<=` between true depths from `<=` between polynomial depths. -/
lemma dle {r B : ℝ} (P : F.Par r B) (q : C3) {i j : Fin 7} (h : F.Dd B q i ≤ F.Dd B q j) :
    F.dep q i ≤ F.dep q j := by
  rcases h.lt_or_eq with h | h
  · exact (F.dlt P q h).le
  · exact (F.deq P q h).le

set_option maxHeartbeats 1600000 in
/-- **I_MC leaf L4**: for `A >= 0`, `Q >= 0`, `K < 0` the point set is Rupert, by the new segment
leaf `s13:25346[AvCv]` (view `x3 - x1 = (-t, 0, -hm)`; literals `B-: -sp E0`, `F-: -R1`,
`H+: kp t`; order `z5 >= z3 > z4 > z6`, `z5 > z2`). -/
theorem imc_L4 (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hI : F.IMC) (hA : 0 ≤ (F.S.hm*F.S.tp-F.S.hm+F.S.hp*F.S.tm)) (hQ : 0 ≤ (F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))) (hK : (F.S.km-F.S.hm) < 0) : IsRupert (Finset.univ.image x) := by
  set FF := h20s_fac hR with hFF
  obtain ⟨r, B, P⟩ := F.par hI
  have hden := P.hden
  have ht := F.one_sub_tm_pos; have hs := F.one_sub_sp_pos; have hs' := F.one_sub_sm_pos
  have ht' := F.one_sub_tp_pos
  have tp := F.S.tp_pos; have tm := F.S.tm_pos; have hm := F.S.hm_pos; have hp := F.S.hp_pos
  have km := F.S.km_pos; have sm := F.S.sm_pos; have kp := F.S.kp_pos; have sp := F.S.sp_pos
  have hE0 : 0 < (F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm)) := by
    have e : F.S.sm * (F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm)) = (F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm)) + (F.S.hm+F.S.km*F.S.tm-F.S.km) := by ring
    have : 0 < F.S.sm * (F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm)) := by rw [e]; linarith
    exact pos_of_mul_pos' sm this
  have hR1 : 0 < ((1-F.S.sp)*(F.S.hm*F.S.tp-F.S.hp*(1-F.S.tm))+(1-F.S.tm)*F.S.kp) := by
    have := mul_pos hs hE0; have := mul_pos ht kp; linarith
  have hq := IVT.seg_vec F 1 3 ⟨-(1-F.S.tm), 0, -F.S.hm⟩ (by rw [F.ptC_1, F.ptC_3]; simp [C3.sub])
  refine h20s_I_s13 FF hx ?_ ?_ ?_ ?_
  · refine (F.nrm_B FF).seg_neg hq ?_
    simp only
    nlinarith [mul_pos sp hE0]
  · refine (F.nrm_F FF).seg_neg hq ?_
    simp only
    nlinarith [hR1]
  · refine (F.nrm_H FF).seg_pos hq ?_
    simp only
    nlinarith [mul_pos kp ht]
  · rw [hq]
    refine F.robUni_of_dep _ _ (robUni5_L4 ?_ ?_ ?_ ?_)
    · show F.dep ⟨-(1-F.S.tm), 0, -F.S.hm⟩ 3 ≤ F.dep ⟨-(1-F.S.tm), 0, -F.S.hm⟩ 5
      refine F.dle P _ ?_
      have e : F.Dd B ⟨-(1-F.S.tm), 0, -F.S.hm⟩ 5 - F.Dd B ⟨-(1-F.S.tm), 0, -F.S.hm⟩ 3 = F.S.sm * F.S.hm * (1-F.S.tm) * (F.S.hm*F.S.tp-F.S.hm+F.S.hp*F.S.tm) := by
        simp only [Dd]; ring
      have := mul_nonneg (mul_pos (mul_pos sm hm) ht).le hA
      linarith
    · show F.dep ⟨-(1-F.S.tm), 0, -F.S.hm⟩ 4 < F.dep ⟨-(1-F.S.tm), 0, -F.S.hm⟩ 3
      refine F.dlt P _ ?_
      have e : F.Dd B ⟨-(1-F.S.tm), 0, -F.S.hm⟩ 3 - F.Dd B ⟨-(1-F.S.tm), 0, -F.S.hm⟩ 4 =
          F.S.sm * (F.S.hm - F.S.km) * (1-F.S.tm) * (F.S.hm * (1 - F.S.tp) + F.S.hp * (1-F.S.tm)) := by
        simp only [Dd]; ring
      have h1 : 0 < F.S.hm - F.S.km := by linarith
      have h2 : 0 < F.S.hm * (1 - F.S.tp) + F.S.hp * (1-F.S.tm) := by
        have := mul_pos hm ht'; have := mul_pos hp ht; linarith
      have := mul_pos (mul_pos (mul_pos sm h1) ht) h2
      linarith
    · show F.dep ⟨-(1-F.S.tm), 0, -F.S.hm⟩ 6 < F.dep ⟨-(1-F.S.tm), 0, -F.S.hm⟩ 4
      refine F.dlt P _ ?_
      have e : F.Dd B ⟨-(1-F.S.tm), 0, -F.S.hm⟩ 4 - F.Dd B ⟨-(1-F.S.tm), 0, -F.S.hm⟩ 6 =
          (1-F.S.tm) * (F.S.hp * (1 - F.S.sm) * (F.S.hm+F.S.km*F.S.tm-F.S.km) + F.S.hm * F.S.km * F.S.sm * (1 - F.S.tp)) := by
        simp only [Dd]; ring
      have h1 : 0 < F.S.hp * (1 - F.S.sm) * (F.S.hm+F.S.km*F.S.tm-F.S.km) := mul_pos (mul_pos hp hs') hden
      have h2 : 0 < F.S.hm * F.S.km * F.S.sm * (1 - F.S.tp) := mul_pos (mul_pos (mul_pos hm km) sm) ht'
      have := mul_pos ht (add_pos h1 h2)
      linarith
    · show F.dep ⟨-(1-F.S.tm), 0, -F.S.hm⟩ 2 < F.dep ⟨-(1-F.S.tm), 0, -F.S.hm⟩ 5
      refine F.dlt P _ ?_
      have e : F.Dd B ⟨-(1-F.S.tm), 0, -F.S.hm⟩ 5 - F.Dd B ⟨-(1-F.S.tm), 0, -F.S.hm⟩ 2 =
          (1-F.S.tm) * (F.S.hp * F.S.sp * (F.S.hm+F.S.km*F.S.tm-F.S.km) + F.S.hm * F.S.kp * F.S.sm * (1 - F.S.tp)) := by
        simp only [Dd]; ring
      have h1 : 0 < F.S.hp * F.S.sp * (F.S.hm+F.S.km*F.S.tm-F.S.km) := mul_pos (mul_pos hp sp) hden
      have h2 : 0 < F.S.hm * F.S.kp * F.S.sm * (1 - F.S.tp) := mul_pos (mul_pos (mul_pos hm kp) sm) ht'
      have := mul_pos ht (add_pos h1 h2)
      linarith

/-- **I_MC leaf L5**: for `Q >= 0`, `K >= 0`, `F15 < 0` the point set is Rupert, by the new segment
leaf `s15:01346[C^]` (view `x1 - x5 = (1, 0, 0)`; the one literal `F-` is `F15 < 0`; order
`z1 > z0 > z6 > z4`, `z1 > z3 >= z4`). -/
theorem imc_L5 (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hI : F.IMC) (hQ : 0 ≤ (F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))) (hK : 0 ≤ (F.S.km-F.S.hm)) (hF : (F.S.kp-F.S.hp*(1-F.S.sp)) < 0) : IsRupert (Finset.univ.image x) := by
  set FF := h20s_fac hR with hFF
  obtain ⟨r, B, P⟩ := F.par hI
  have hden := P.hden
  have ht := F.one_sub_tm_pos; have hs := F.one_sub_sp_pos; have hs' := F.one_sub_sm_pos
  have ht' := F.one_sub_tp_pos
  have tp := F.S.tp_pos; have tm := F.S.tm_pos; have hm := F.S.hm_pos; have hp := F.S.hp_pos
  have km := F.S.km_pos; have sm := F.S.sm_pos; have kp := F.S.kp_pos; have sp := F.S.sp_pos
  have hW : 0 < ((F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))+F.S.hp*F.S.sm*(1-F.S.tm)) := by
    have : 0 < F.S.hp * F.S.sm * (1-F.S.tm) := mul_pos (mul_pos hp sm) ht
    linarith
  have hq := IVT.seg_vec F 5 1 ⟨1, 0, 0⟩ (by rw [F.ptC_5, F.ptC_1]; simp [C3.sub])
  refine h20s_I_s15 FF hx ?_ ?_
  · refine (F.nrm_F FF).seg_neg hq ?_
    simp only; linarith
  · rw [hq]
    refine F.robUni_of_dep _ _ (robUni5_L5 ?_ ?_ ?_ ?_ ?_)
    · show F.dep ⟨1, 0, 0⟩ 0 < F.dep ⟨1, 0, 0⟩ 1
      refine F.dlt P _ ?_
      have e : F.Dd B ⟨1, 0, 0⟩ 1 - F.Dd B ⟨1, 0, 0⟩ 0 = F.S.hp * F.S.sm * F.S.hm * (1 - F.S.tp) := by
        simp only [Dd]; ring
      have := mul_pos (mul_pos (mul_pos hp sm) hm) ht'
      linarith
    · show F.dep ⟨1, 0, 0⟩ 6 < F.dep ⟨1, 0, 0⟩ 0
      refine F.dlt P _ ?_
      have e : F.Dd B ⟨1, 0, 0⟩ 0 - F.Dd B ⟨1, 0, 0⟩ 6 = F.S.hp * ((F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))+F.S.hp*F.S.sm*(1-F.S.tm)) := by
        simp only [Dd]; ring
      have := mul_pos hp hW
      linarith
    · show F.dep ⟨1, 0, 0⟩ 4 < F.dep ⟨1, 0, 0⟩ 6
      refine F.dlt P _ ?_
      have e : F.Dd B ⟨1, 0, 0⟩ 6 - F.Dd B ⟨1, 0, 0⟩ 4 = F.S.hp * (F.S.hm+F.S.km*F.S.tm-F.S.km) * (1 - F.S.sm) := by
        simp only [Dd]; ring
      have := mul_pos (mul_pos hp hden) hs'
      linarith
    · show F.dep ⟨1, 0, 0⟩ 3 < F.dep ⟨1, 0, 0⟩ 1
      refine F.dlt P _ ?_
      have e : F.Dd B ⟨1, 0, 0⟩ 1 - F.Dd B ⟨1, 0, 0⟩ 3 = F.S.hp * F.S.sm * F.S.hm * (1-F.S.tm) := by
        simp only [Dd]; ring
      have := mul_pos (mul_pos (mul_pos hp sm) hm) ht
      linarith
    · show F.dep ⟨1, 0, 0⟩ 4 ≤ F.dep ⟨1, 0, 0⟩ 3
      refine F.dle P _ ?_
      have e : F.Dd B ⟨1, 0, 0⟩ 3 - F.Dd B ⟨1, 0, 0⟩ 4 = F.S.hp * F.S.sm * (F.S.km-F.S.hm) * (1-F.S.tm) := by
        simp only [Dd]; ring
      have := mul_nonneg (mul_pos (mul_pos hp sm) ht).le hK
      nlinarith

end Frame20
end Minimality.CaseC20

end

