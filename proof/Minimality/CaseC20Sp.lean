module

public import Minimality.CaseC20Final

@[expose] public section

/-!
# Type 20, acute case (c): the reduced special set

`CaseC20Special'` is `CaseC20Special` with the 8 disjuncts n1, n3, n17, n18, n19, n23, n24, n25 removed
(ported from `nopert229/out/bottleneck/sp20`); `Frame20.isRupert_of_not_special'` is Rupert off it.
-/


namespace Minimality.CaseC20
open Finset Filter Minimality.CaseC09 Minimality.CaseC18
open scoped RealInnerProductSpace Topology


theorem xX_cyc_c (S : Shape20) (hA3 : 0 ≤ S.hm*S.sm*S.tp - S.hm + S.hp*S.sm*S.tm - S.hp*S.sm - S.km*S.tm + S.km) (hBm : 0 < -S.hm*S.tp + S.hm - S.hp*S.tm) (hCm : 0 ≤ S.hp*S.sm + S.km*S.tp - S.km) :
    Cyc5 1 S.u_xX S.w_xX (⟨1, 0, 0⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, 0, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨0, 1, 0⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos (mul_pos S.sm_pos S.hp_pos) S.hm_pos), (mul_pos (mul_pos S.sm_pos S.hm_pos) hBm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos (mul_pos (mul_pos htp1 S.sp_pos) S.hm_pos) rm), (mul_pos (mul_pos (mul_pos htm1 S.sp_pos) S.hp_pos) rm), (mul_pos (mul_pos (mul_pos htm1 S.sm_pos) S.hp_pos) S.kp_pos), (mul_pos (mul_pos (mul_pos htm1 S.sm_pos) S.kp_pos) hBm), (mul_pos (mul_pos (mul_pos hsp1 S.sm_pos) S.hp_pos) S.hm_pos), (mul_pos (mul_pos (mul_pos hsp1 S.sm_pos) S.hm_pos) hBm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos S.hp_pos rm), (mul_pos rm hBm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos (mul_pos (mul_pos htp1 S.sp_pos) S.hm_pos) S.hm_pos), (mul_pos (mul_pos (mul_pos S.tm_pos S.sp_pos) S.hp_pos) rm), (mul_pos (mul_pos (mul_pos S.tm_pos S.sm_pos) S.hp_pos) S.kp_pos), (mul_pos (mul_pos (mul_pos S.tm_pos S.sm_pos) S.kp_pos) hBm), (mul_nonneg (mul_nonneg (mul_nonneg (htm1).le (S.sp_pos).le) (S.hm_pos).le) hCm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos (mul_pos htp1 S.hm_pos) S.hm_pos), (mul_pos (mul_pos S.tm_pos S.hp_pos) rm), (mul_nonneg (mul_nonneg (htm1).le (S.hm_pos).le) hCm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos (mul_pos S.sm_pos S.hp_pos) S.hm_pos), (mul_pos (mul_pos S.sm_pos S.hm_pos) hBm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos (mul_pos htp1 S.hm_pos) S.kp_pos), (mul_nonneg (mul_nonneg (htm1).le (S.kp_pos).le) hCm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos (mul_pos S.sp_pos S.hp_pos) rm), (mul_pos (mul_pos S.sm_pos S.hp_pos) S.kp_pos), (mul_pos (mul_pos S.sm_pos S.kp_pos) hBm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos (mul_pos (mul_pos htp1 S.sp_pos) S.hm_pos) S.hm_pos), (mul_pos (mul_pos (mul_pos S.tm_pos S.sp_pos) S.hp_pos) rm), (mul_pos (mul_pos (mul_pos S.tm_pos S.sm_pos) S.hp_pos) S.kp_pos), (mul_pos (mul_pos (mul_pos S.tm_pos S.sm_pos) S.kp_pos) hBm), (mul_nonneg (mul_nonneg (mul_nonneg (htm1).le (S.sp_pos).le) (S.hm_pos).le) hCm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos rp rm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos (mul_pos S.tm_pos rp) rm), (mul_pos (mul_pos (mul_pos htp1 htm1) S.hm_pos) S.kp_pos), (mul_pos (mul_pos (mul_pos htp1 hsp1) S.hm_pos) S.hm_pos), (mul_nonneg (mul_nonneg (mul_nonneg (htm1).le (htm1).le) (S.kp_pos).le) hCm), (mul_nonneg (mul_nonneg (mul_nonneg (htm1).le (hsp1).le) (S.hm_pos).le) hCm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos (mul_pos htp1 S.hm_pos) S.kp_pos), (mul_nonneg (mul_nonneg (htm1).le (S.kp_pos).le) hCm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos S.hp_pos rm), (mul_pos rm hBm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos S.hp_pos rm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos rp rm)])⟩

theorem xX_rest0_c (S : Shape20) (hA3 : 0 ≤ S.hm*S.sm*S.tp - S.hm + S.hp*S.sm*S.tm - S.hp*S.sm - S.km*S.tm + S.km) (hBm : 0 < -S.hm*S.tp + S.hm - S.hp*S.tm) (hCm : 0 ≤ S.hp*S.sm + S.km*S.tp - S.km) :
    Rest5 1 S.u_xX S.w_xX (⟨1, 0, 0⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, 0, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨0, 1, 0⟩ ⟨S.tp, 0, S.hp⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos (mul_pos S.sm_pos S.hp_pos) S.hp_pos), (mul_pos (mul_pos S.sm_pos S.hp_pos) hBm), (mul_pos (mul_pos S.sm_pos hBm) hBm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_nonneg hA3 (hBm).le), (mul_pos (mul_pos htp1 S.hm_pos) S.hm_pos), (mul_pos (mul_pos S.tm_pos S.hp_pos) rm), (mul_nonneg (mul_nonneg (htm1).le (S.hm_pos).le) hCm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos (mul_pos htp1 S.hm_pos) S.kp_pos), (mul_nonneg (mul_nonneg (htp1).le (S.kp_pos).le) hA3), (mul_nonneg (mul_nonneg (htm1).le (S.kp_pos).le) hCm), (mul_nonneg (mul_nonneg (S.sp_pos).le (S.hp_pos).le) hA3)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; exact (hA3.lt_or_eq.elim (fun h => Or.inl (by linarith [mul_pos rp h])) (fun h => Or.inr ⟨by first | linear_combination (-(S.hp * (1 - S.sp) - S.kp * (1 - S.tp))) * h | linear_combination (S.hp * (1 - S.sp) - S.kp * (1 - S.tp)) * h, by linarith [mul_pos hsp1 S.tp_pos]⟩))),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; right; refine ⟨by ring, ?_⟩; linarith [htp1])⟩

theorem xX_rest4_c (S : Shape20) (hA3 : 0 ≤ S.hm*S.sm*S.tp - S.hm + S.hp*S.sm*S.tm - S.hp*S.sm - S.km*S.tm + S.km) (hBm : 0 < -S.hm*S.tp + S.hm - S.hp*S.tm) (hCm : 0 ≤ S.hp*S.sm + S.km*S.tp - S.km) :
    Rest5 1 S.u_xX S.w_xX (⟨1, 0, 0⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, 0, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; right; refine ⟨by ring, ?_⟩; linarith [(mul_pos htm1 S.sm_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos (mul_pos S.sm_pos S.hm_pos) hBm), (mul_nonneg (mul_nonneg (S.sm_pos).le (S.hm_pos).le) hCm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos (mul_pos (mul_pos htp1 S.sp_pos) S.hm_pos) S.km_pos), (mul_pos (mul_pos (mul_pos htp1 S.sm_pos) S.hm_pos) S.kp_pos), (mul_nonneg (mul_nonneg (mul_nonneg (htm1).le (S.sp_pos).le) (S.km_pos).le) hCm), (mul_nonneg (mul_nonneg (mul_nonneg (htm1).le (S.sm_pos).le) (S.kp_pos).le) hCm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos (mul_pos (mul_pos htp1 hsp1) S.hm_pos) S.km_pos), (mul_pos (mul_pos (mul_pos htp1 hsm1) S.hm_pos) S.kp_pos), (mul_nonneg (mul_nonneg (mul_nonneg (htm1).le (hsp1).le) (S.km_pos).le) hCm), (mul_nonneg (mul_nonneg (mul_nonneg (htm1).le (hsm1).le) (S.kp_pos).le) hCm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos (mul_pos htp1 S.km_pos) rm), (mul_pos (mul_pos hsm1 S.hp_pos) rm)])⟩

theorem Frame20.xX_c {x : Fin 7 → ℝ³} (F : Frame20 x) (hA3 : 0 ≤ F.S.hm*F.S.sm*F.S.tp - F.S.hm + F.S.hp*F.S.sm*F.S.tm - F.S.hp*F.S.sm - F.S.km*F.S.tm + F.S.km) (hBm : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hCm : 0 ≤ F.S.hp*F.S.sm + F.S.km*F.S.tp - F.S.km)
    (h0 : F.dep F.S.u_xX 1 < F.dep F.S.u_xX 6 ∨ F.dep F.S.u_xX 1 < F.dep F.S.u_xX 3 ∨ F.dep F.S.u_xX 5 < F.dep F.S.u_xX 3 ∨ F.dep F.S.u_xX 5 < F.dep F.S.u_xX 2) (h1 : F.dep F.S.u_xX 3 < F.dep F.S.u_xX 1 ∨ F.dep F.S.u_xX 3 < F.dep F.S.u_xX 5 ∨ F.dep F.S.u_xX 2 < F.dep F.S.u_xX 5 ∨ F.dep F.S.u_xX 2 < F.dep F.S.u_xX 6) (h2 : F.dep F.S.u_xX 5 < F.dep F.S.u_xX 3 ∨ F.dep F.S.u_xX 5 < F.dep F.S.u_xX 2 ∨ F.dep F.S.u_xX 6 < F.dep F.S.u_xX 2 ∨ F.dep F.S.u_xX 6 < F.dep F.S.u_xX 1) (h3 : F.dep F.S.u_xX 2 < F.dep F.S.u_xX 5 ∨ F.dep F.S.u_xX 2 < F.dep F.S.u_xX 6 ∨ F.dep F.S.u_xX 1 < F.dep F.S.u_xX 6 ∨ F.dep F.S.u_xX 1 < F.dep F.S.u_xX 3) (h4 : F.dep F.S.u_xX 6 < F.dep F.S.u_xX 2 ∨ F.dep F.S.u_xX 6 < F.dep F.S.u_xX 1 ∨ F.dep F.S.u_xX 3 < F.dep F.S.u_xX 1 ∨ F.dep F.S.u_xX 3 < F.dep F.S.u_xX 5) :
    IsRupert (Finset.univ.image x) := by
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  refine F.toFrame7.rim5p 1 3 5 2 6 _ _ _ _ _ (F.ptC_1) (F.ptC_3) (F.ptC_5) (F.ptC_2) (F.ptC_6) 1 (Or.inl rfl) F.S.u_xX F.S.w_xX (Or.inl (by simp only [Shape20.u_xX]; intro h0; linarith [(mul_pos htp1 F.S.hm_pos), (mul_nonneg (htm1).le hCm), h0]))
    (xX_cyc_c F.S hA3 hBm hCm) ?_ ?_ ?_ ?_ ?_ ?_
  · intro j' h0 h1 h2 h3 h4
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [F.ptC_0]; exact xX_rest0_c F.S hA3 hBm hCm
    · exact absurd rfl h0
    · exact absurd rfl h3
    · exact absurd rfl h1
    · rw [F.ptC_4]; exact xX_rest4_c F.S hA3 hBm hCm
    · exact absurd rfl h2
    · exact absurd rfl h4
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using h0
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using h1
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using h2
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using h3
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using h4


/-- the tilt of the closed yY test: e3 -/
def Shape20.w_yY3 (_ : Shape20) : C3 := ⟨0, 0, 1⟩

theorem yY_cyc_c (S : Shape20) (hA2 : 0 < S.hm*S.sm*S.tp + S.hp*S.sm*S.tm - S.km*S.tm) (hA3 : 0 ≤ -S.hm*S.sm*S.tp + S.hm - S.hp*S.sm*S.tm + S.hp*S.sm + S.km*S.tm - S.km) :
    Cyc5 1 S.u_yY S.w_yY3 (⟨1, 0, 0⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY3]; left; linarith [rp]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY3]; left; linarith [S.hp_pos]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY3]; left; linarith [(mul_pos htp1 S.hm_pos), (mul_pos htm1 S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY3]; left; linarith [(mul_pos S.tp_pos S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY3]; left; linarith [(mul_pos S.tm_pos rp), (mul_pos (mul_pos S.tp_pos htm1) S.kp_pos), (mul_pos (mul_pos S.tp_pos hsp1) S.hm_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY3]; left; linarith [rp]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY3]; left; linarith [(mul_pos S.tm_pos S.kp_pos), (mul_pos (mul_pos S.tp_pos S.sp_pos) S.hm_pos), (mul_pos (mul_pos S.tm_pos S.sp_pos) S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY3]; left; linarith [S.kp_pos, (mul_pos S.sp_pos S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY3]; left; linarith [(mul_pos S.tp_pos S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY3]; left; linarith [S.hm_pos]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY3]; left; linarith [(mul_pos S.tp_pos S.hm_pos), (mul_pos S.tm_pos S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY3]; left; linarith [(mul_pos S.tm_pos S.kp_pos), (mul_pos (mul_pos S.tp_pos S.sp_pos) S.hm_pos), (mul_pos (mul_pos S.tm_pos S.sp_pos) S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY3]; left; linarith [(mul_pos htp1 S.hm_pos), (mul_pos htm1 S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY3]; left; linarith [(mul_pos htp1 S.hm_pos), (mul_pos htm1 S.kp_pos), (mul_pos (mul_pos S.tp_pos hsp1) S.hm_pos), (mul_pos (mul_pos htm1 S.sp_pos) S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY3]; left; linarith [S.hm_pos])⟩

theorem yY_rest0_c (S : Shape20) (hA2 : 0 < S.hm*S.sm*S.tp + S.hp*S.sm*S.tm - S.km*S.tm) (hA3 : 0 ≤ -S.hm*S.sm*S.tp + S.hm - S.hp*S.sm*S.tm + S.hp*S.sm + S.km*S.tm - S.km) :
    Rest5 1 S.u_yY S.w_yY3 (⟨1, 0, 0⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨S.tp, 0, S.hp⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY3]; right; refine ⟨by ring, ?_⟩; linarith [S.hp_pos]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY3]; right; refine ⟨by ring, ?_⟩; linarith [(mul_pos hsp1 S.tp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY3]; left; linarith [(mul_pos S.tp_pos S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY3]; left; linarith [(mul_pos S.tp_pos S.hm_pos), (mul_pos S.tm_pos S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY3]; left; linarith [(mul_pos htp1 S.hm_pos), (mul_pos htm1 S.hp_pos)])⟩

theorem yY_rest4_c (S : Shape20) (hA2 : 0 < S.hm*S.sm*S.tp + S.hp*S.sm*S.tm - S.km*S.tm) (hA3 : 0 ≤ -S.hm*S.sm*S.tp + S.hm - S.hp*S.sm*S.tm + S.hp*S.sm + S.km*S.tm - S.km) :
    Rest5 1 S.u_yY S.w_yY3 (⟨1, 0, 0⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨0, S.sm, -S.km⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY3]; left; linarith [(mul_pos htp1 S.km_pos), (mul_pos hsm1 S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY3]; left; linarith [(mul_pos (mul_pos S.tp_pos hsp1) S.km_pos), (mul_pos (mul_pos S.tp_pos hsm1) S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY3]; left; linarith [(mul_pos (mul_pos S.tp_pos S.sp_pos) S.km_pos), (mul_pos (mul_pos S.tp_pos S.sm_pos) S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY3]; left; linarith [hA2]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY3]; exact (hA3.lt_or_eq.elim (fun h => Or.inl (by linarith)) (fun h => Or.inr ⟨by linarith, by linarith [mul_pos htm1 S.sm_pos]⟩)))⟩

theorem Frame20.yY_c {x : Fin 7 → ℝ³} (F : Frame20 x) (hA2 : 0 < F.S.hm*F.S.sm*F.S.tp + F.S.hp*F.S.sm*F.S.tm - F.S.km*F.S.tm) (hA3 : 0 ≤ -F.S.hm*F.S.sm*F.S.tp + F.S.hm - F.S.hp*F.S.sm*F.S.tm + F.S.hp*F.S.sm + F.S.km*F.S.tm - F.S.km)
    (h0 : F.dep F.S.u_yY 1 < F.dep F.S.u_yY 3 ∨ F.dep F.S.u_yY 1 < F.dep F.S.u_yY 6 ∨ F.dep F.S.u_yY 2 < F.dep F.S.u_yY 6 ∨ F.dep F.S.u_yY 2 < F.dep F.S.u_yY 5) (h1 : F.dep F.S.u_yY 6 < F.dep F.S.u_yY 1 ∨ F.dep F.S.u_yY 6 < F.dep F.S.u_yY 2 ∨ F.dep F.S.u_yY 5 < F.dep F.S.u_yY 2 ∨ F.dep F.S.u_yY 5 < F.dep F.S.u_yY 3) (h2 : F.dep F.S.u_yY 2 < F.dep F.S.u_yY 6 ∨ F.dep F.S.u_yY 2 < F.dep F.S.u_yY 5 ∨ F.dep F.S.u_yY 3 < F.dep F.S.u_yY 5 ∨ F.dep F.S.u_yY 3 < F.dep F.S.u_yY 1) (h3 : F.dep F.S.u_yY 5 < F.dep F.S.u_yY 2 ∨ F.dep F.S.u_yY 5 < F.dep F.S.u_yY 3 ∨ F.dep F.S.u_yY 1 < F.dep F.S.u_yY 3 ∨ F.dep F.S.u_yY 1 < F.dep F.S.u_yY 6) (h4 : F.dep F.S.u_yY 3 < F.dep F.S.u_yY 5 ∨ F.dep F.S.u_yY 3 < F.dep F.S.u_yY 1 ∨ F.dep F.S.u_yY 6 < F.dep F.S.u_yY 1 ∨ F.dep F.S.u_yY 6 < F.dep F.S.u_yY 2) :
    IsRupert (Finset.univ.image x) := by
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  refine F.toFrame7.rim5p 1 6 2 5 3 _ _ _ _ _ (F.ptC_1) (F.ptC_6) (F.ptC_2) (F.ptC_5) (F.ptC_3) 1 (Or.inl rfl) F.S.u_yY F.S.w_yY3 (Or.inl (by simp only [Shape20.u_yY]; intro h0; linarith [F.S.tp_pos, h0]))
    (yY_cyc_c F.S hA2 hA3) ?_ ?_ ?_ ?_ ?_ ?_
  · intro j' h0 h1 h2 h3 h4
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [F.ptC_0]; exact yY_rest0_c F.S hA2 hA3
    · exact absurd rfl h0
    · exact absurd rfl h2
    · exact absurd rfl h4
    · rw [F.ptC_4]; exact yY_rest4_c F.S hA2 hA3
    · exact absurd rfl h3
    · exact absurd rfl h1
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using h0
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using h1
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using h2
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using h3
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using h4


theorem vRa4_cyc_c (S : Shape20) (hW : 0 < -S.hp*S.sp + S.hp - S.kp) (hQ : 0 < S.hm*S.sp*S.tp - S.hm*S.tp + S.hp*S.sp*S.tm - S.hp*S.sp - S.hp*S.tm + S.hp + S.kp*S.tm - S.kp) (hD : 0 ≤ -S.hp*S.sm*S.sp + S.hp*S.sm + S.hp*S.sp - S.hp - S.km*S.sp*S.tp + S.km*S.tp - S.kp*S.sm + S.kp) :
    Cyc4 (-1) S.u_vRa4 S.w_vRa4 (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨1, 0, 0⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; left; linarith [hD, (mul_pos hsm1 rp)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; left; linarith [rp]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; exact (hD.lt_or_eq.elim (fun h => Or.inl (by linarith)) (fun h => Or.inr ⟨by linarith, pos_of_pos_mul hsp1 (by linarith [mul_pos hsm1 hkp, mul_pos hkm hsp1])⟩))),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; left; linarith [hD, (mul_pos hsm1 rp)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; left; linarith [(mul_pos S.sm_pos rp)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; exact (hD.lt_or_eq.elim (fun h => Or.inl (by linarith)) (fun h => Or.inr ⟨by linarith, pos_of_pos_mul hsp1 (by linarith [mul_pos hsm1 hkp, mul_pos hkm hsp1])⟩))),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; left; linarith [rp]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; left; linarith [(mul_pos S.sm_pos rp)])⟩

theorem vRa4_rest5_c (S : Shape20) (hW : 0 < -S.hp*S.sp + S.hp - S.kp) (hQ : 0 < S.hm*S.sp*S.tp - S.hm*S.tp + S.hp*S.sp*S.tm - S.hp*S.sp - S.hp*S.tm + S.hp + S.kp*S.tm - S.kp) (hD : 0 ≤ -S.hp*S.sm*S.sp + S.hp*S.sm + S.hp*S.sp - S.hp - S.km*S.sp*S.tp + S.km*S.tp - S.kp*S.sm + S.kp) :
    Rest4 (-1) S.u_vRa4 S.w_vRa4 (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨1, 0, 0⟩ ⟨0, 0, 0⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; left; linarith [(mul_pos S.tp_pos S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; left; linarith [(mul_pos (mul_pos S.tp_pos hsp1) S.km_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; left; linarith [(mul_pos S.sm_pos hW)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; right; refine ⟨by ring, ?_⟩; linarith [S.hp_pos])⟩

theorem vRa4_rest3_c (S : Shape20) (hW : 0 < -S.hp*S.sp + S.hp - S.kp) (hQ : 0 < S.hm*S.sp*S.tp - S.hm*S.tp + S.hp*S.sp*S.tm - S.hp*S.sp - S.hp*S.tm + S.hp + S.kp*S.tm - S.kp) (hD : 0 ≤ -S.hp*S.sm*S.sp + S.hp*S.sm + S.hp*S.sp - S.hp - S.km*S.sp*S.tp + S.km*S.tp - S.kp*S.sm + S.kp) :
    Rest4 (-1) S.u_vRa4 S.w_vRa4 (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨1, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; left; linarith [(mul_pos S.tp_pos S.kp_pos), (mul_pos S.tm_pos hW), (mul_pos (mul_pos S.tp_pos hsp1) S.hm_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; left; linarith [(mul_nonneg (S.tm_pos).le hD), (mul_pos (mul_pos S.tp_pos hsp1) rm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; left; linarith [(mul_pos S.sm_pos hQ)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; right; refine ⟨by ring, ?_⟩; linarith [(mul_pos htp1 S.hm_pos), (mul_pos htm1 S.hp_pos)])⟩

theorem vRa4_rest2_c (S : Shape20) (hW : 0 < -S.hp*S.sp + S.hp - S.kp) (hQ : 0 < S.hm*S.sp*S.tp - S.hm*S.tp + S.hp*S.sp*S.tm - S.hp*S.sp - S.hp*S.tm + S.hp + S.kp*S.tm - S.kp) (hD : 0 ≤ -S.hp*S.sm*S.sp + S.hp*S.sm + S.hp*S.sp - S.hp - S.km*S.sp*S.tp + S.km*S.tp - S.kp*S.sm + S.kp) :
    Rest4 (-1) S.u_vRa4 S.w_vRa4 (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨1, 0, 0⟩ ⟨0, S.sp, S.kp⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; right; refine ⟨by ring, ?_⟩; linarith [(mul_pos S.tp_pos S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; left; linarith [(mul_nonneg (hsp1).le hD), (mul_pos (mul_pos hsp1 hsm1) rp)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; left; linarith [(mul_nonneg (S.sp_pos).le hD), (mul_pos (mul_pos hsp1 S.sm_pos) rp)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; left; linarith [(mul_pos S.sp_pos rp)])⟩

theorem Frame20.vRa4_cD {x : Fin 7 → ℝ³} (F : Frame20 x) (hW : 0 < -F.S.hp*F.S.sp + F.S.hp - F.S.kp) (hQ : 0 < F.S.hm*F.S.sp*F.S.tp - F.S.hm*F.S.tp + F.S.hp*F.S.sp*F.S.tm - F.S.hp*F.S.sp - F.S.hp*F.S.tm + F.S.hp + F.S.kp*F.S.tm - F.S.kp) (hD : 0 ≤ -F.S.hp*F.S.sm*F.S.sp + F.S.hp*F.S.sm + F.S.hp*F.S.sp - F.S.hp - F.S.km*F.S.sp*F.S.tp + F.S.km*F.S.tp - F.S.kp*F.S.sm + F.S.kp)
    (hA : F.dep F.S.u_vRa4 0 < F.dep F.S.u_vRa4 6 ∨ F.dep F.S.u_vRa4 0 < F.dep F.S.u_vRa4 1 ∨ F.dep F.S.u_vRa4 4 < F.dep F.S.u_vRa4 6 ∨ F.dep F.S.u_vRa4 4 < F.dep F.S.u_vRa4 1) (hB : F.dep F.S.u_vRa4 6 < F.dep F.S.u_vRa4 0 ∨ F.dep F.S.u_vRa4 1 < F.dep F.S.u_vRa4 0 ∨ F.dep F.S.u_vRa4 6 < F.dep F.S.u_vRa4 4 ∨ F.dep F.S.u_vRa4 1 < F.dep F.S.u_vRa4 4) :
    IsRupert (Finset.univ.image x) := by
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  refine F.toFrame7.rim4 0 6 4 1 _ _ _ _ (F.ptC_0) (F.ptC_6) (F.ptC_4) (F.ptC_1) (-1) (Or.inr rfl) F.S.u_vRa4 F.S.w_vRa4 (Or.inl (by simp only [Shape20.u_vRa4]; intro h0; linarith [(mul_pos F.S.tp_pos hsp1), h0]))
    (vRa4_cyc_c F.S hW hQ hD) ?_ ?_ ?_
  · intro j' h0 h1 h2 h3
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · exact absurd rfl h3
    · rw [F.ptC_2]; exact vRa4_rest2_c F.S hW hQ hD
    · rw [F.ptC_3]; exact vRa4_rest3_c F.S hW hQ hD
    · exact absurd rfl h2
    · rw [F.ptC_5]; exact vRa4_rest5_c F.S hW hQ hD
    · exact absurd rfl h1
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using hA
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using hB




theorem Frame20.vRa4_c {x : Fin 7 → ℝ³} (F : Frame20 x) (hW : 0 ≤ -F.S.hp*F.S.sp + F.S.hp - F.S.kp) (hQ : 0 < F.S.hm*F.S.sp*F.S.tp - F.S.hm*F.S.tp + F.S.hp*F.S.sp*F.S.tm - F.S.hp*F.S.sp - F.S.hp*F.S.tm + F.S.hp + F.S.kp*F.S.tm - F.S.kp) (hD : 0 ≤ -F.S.hp*F.S.sm*F.S.sp + F.S.hp*F.S.sm + F.S.hp*F.S.sp - F.S.hp - F.S.km*F.S.sp*F.S.tp + F.S.km*F.S.tp - F.S.kp*F.S.sm + F.S.kp)
    (hA : F.dep F.S.u_vRa4 0 < F.dep F.S.u_vRa4 6 ∨ F.dep F.S.u_vRa4 0 < F.dep F.S.u_vRa4 1 ∨ F.dep F.S.u_vRa4 4 < F.dep F.S.u_vRa4 6 ∨ F.dep F.S.u_vRa4 4 < F.dep F.S.u_vRa4 1) (hB : F.dep F.S.u_vRa4 6 < F.dep F.S.u_vRa4 0 ∨ F.dep F.S.u_vRa4 1 < F.dep F.S.u_vRa4 0 ∨ F.dep F.S.u_vRa4 6 < F.dep F.S.u_vRa4 4 ∨ F.dep F.S.u_vRa4 1 < F.dep F.S.u_vRa4 4) :
    IsRupert (Finset.univ.image x) := by
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hW' : 0 < (-F.S.hp*F.S.sp + F.S.hp - F.S.kp) := pos_of_pos_mul htm1 (by linarith [mul_pos (mul_pos F.S.hm_pos F.S.tp_pos) hsp1])
  exact F.vRa4_cD hW' hQ hD hA hB

theorem Frame20.vRv_c {x : Fin 7 → ℝ³} (F : Frame20 x) (hW : 0 ≤ F.S.hp*F.S.sp - F.S.hp + F.S.kp) (hV : 0 < F.S.hm*F.S.sp*F.S.tp - F.S.hm*F.S.tp + F.S.hp*F.S.sp*F.S.tm - F.S.hp*F.S.tm + F.S.kp*F.S.tm)
    (hA : F.dep F.S.u_vRv 0 < F.dep F.S.u_vRv 6 ∨ F.dep F.S.u_vRv 0 < F.dep F.S.u_vRv 5 ∨ F.dep F.S.u_vRv 4 < F.dep F.S.u_vRv 6 ∨ F.dep F.S.u_vRv 4 < F.dep F.S.u_vRv 5) (hB : F.dep F.S.u_vRv 6 < F.dep F.S.u_vRv 0 ∨ F.dep F.S.u_vRv 5 < F.dep F.S.u_vRv 0 ∨ F.dep F.S.u_vRv 6 < F.dep F.S.u_vRv 4 ∨ F.dep F.S.u_vRv 5 < F.dep F.S.u_vRv 4) :
    IsRupert (Finset.univ.image x) := by
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hW' : 0 < (F.S.hp*F.S.sp - F.S.hp + F.S.kp) := pos_of_pos_mul F.S.tm_pos (by linarith [mul_pos (mul_pos F.S.hm_pos F.S.tp_pos) hsp1])
  exact F.vRv hW' hV hA hB





set_option maxHeartbeats 1600000 in
theorem Frame20.ra4_A_cc {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hW : 0 ≤ -F.S.hp*F.S.sp + F.S.hp - F.S.kp) (hQ : 0 < F.S.hm*F.S.sp*F.S.tp - F.S.hm*F.S.tp + F.S.hp*F.S.sp*F.S.tm - F.S.hp*F.S.sp - F.S.hp*F.S.tm + F.S.hp + F.S.kp*F.S.tm - F.S.kp) (hD : 0 ≤ -F.S.hp*F.S.sm*F.S.sp + F.S.hp*F.S.sm + F.S.hp*F.S.sp - F.S.hp - F.S.km*F.S.sp*F.S.tp + F.S.km*F.S.tp - F.S.kp*F.S.sm + F.S.kp) (hA1 : 0 < F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm)   :
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
  · exact F.vRa4_c (by linarith only [hW]) (by linarith only [hQ]) (by linarith only [hD]) o0.1 o0.2
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
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_4, F.ptC_5, F.ptC_6, Shape20.u_vRa4, Shape20.u_tA] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n1_3), mul_nonneg (hsm1).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.hp_pos F.S.km_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_4, F.ptC_5, F.ptC_6, Shape20.u_vRa4, Shape20.u_tA] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(sub_nonneg.2 n0_2), mul_nonneg (hsp1).le (sub_nonneg.2 n1_1), mul_pos ((mul_pos htp1 hsp1)) hga, mul_pos ((mul_pos F.S.hp_pos F.S.kp_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_4, F.ptC_5, F.ptC_6, Shape20.u_vRa4, Shape20.u_tA] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(sub_nonneg.2 n1_4), mul_pos ((mul_pos htp1 F.S.sm_pos)) hga, mul_pos ((mul_pos F.S.hp_pos F.S.km_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_4, F.ptC_5, F.ptC_6, Shape20.u_vRa4, Shape20.u_tA] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg ((mul_pos F.S.tp_pos htp1)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos htp1 htp1)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos F.S.tp_pos hsp1)).le (sub_nonneg.2 n1_1), mul_pos ((mul_pos F.S.hp_pos hQ)) hde, mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.hp_pos) F.S.kp_pos)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le hW) (hA1).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (htm1).le hW) (hA1).le) (hde).le), mul_pos ((mul_pos (mul_pos F.S.sm_pos F.S.hm_pos) rp)) hde, mul_pos ((mul_pos (mul_pos hsm1 F.S.hm_pos) rp)) hde]


set_option maxHeartbeats 1600000 in
theorem Frame20.ra4_Y_cc {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hW : 0 ≤ -F.S.hp*F.S.sp + F.S.hp - F.S.kp) (hQ : 0 < F.S.hm*F.S.sp*F.S.tp - F.S.hm*F.S.tp + F.S.hp*F.S.sp*F.S.tm - F.S.hp*F.S.sp - F.S.hp*F.S.tm + F.S.hp + F.S.kp*F.S.tm - F.S.kp) (hD : 0 ≤ -F.S.hp*F.S.sm*F.S.sp + F.S.hp*F.S.sm + F.S.hp*F.S.sp - F.S.hp - F.S.km*F.S.sp*F.S.tp + F.S.km*F.S.tp - F.S.kp*F.S.sm + F.S.kp) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hCm : 0 ≤ F.S.hp*F.S.sm + F.S.km*F.S.tp - F.S.km) (hA3h : 0 ≤ -F.S.hm*F.S.sm*F.S.tp + F.S.hm - F.S.hp*F.S.sm*F.S.tm + F.S.hp*F.S.sm + F.S.km*F.S.tm - F.S.km)   :
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
  · exact F.vRa4_c (by linarith only [hW]) (by linarith only [hQ]) (by linarith only [hD]) o0.1 o0.2
  by_cases o1 : (F.dep F.S.u_yY 1 < F.dep F.S.u_yY 3 ∨ F.dep F.S.u_yY 1 < F.dep F.S.u_yY 6 ∨ F.dep F.S.u_yY 2 < F.dep F.S.u_yY 6 ∨ F.dep F.S.u_yY 2 < F.dep F.S.u_yY 5) ∧ (F.dep F.S.u_yY 6 < F.dep F.S.u_yY 1 ∨ F.dep F.S.u_yY 6 < F.dep F.S.u_yY 2 ∨ F.dep F.S.u_yY 5 < F.dep F.S.u_yY 2 ∨ F.dep F.S.u_yY 5 < F.dep F.S.u_yY 3) ∧ (F.dep F.S.u_yY 2 < F.dep F.S.u_yY 6 ∨ F.dep F.S.u_yY 2 < F.dep F.S.u_yY 5 ∨ F.dep F.S.u_yY 3 < F.dep F.S.u_yY 5 ∨ F.dep F.S.u_yY 3 < F.dep F.S.u_yY 1) ∧ (F.dep F.S.u_yY 5 < F.dep F.S.u_yY 2 ∨ F.dep F.S.u_yY 5 < F.dep F.S.u_yY 3 ∨ F.dep F.S.u_yY 1 < F.dep F.S.u_yY 3 ∨ F.dep F.S.u_yY 1 < F.dep F.S.u_yY 6) ∧ (F.dep F.S.u_yY 3 < F.dep F.S.u_yY 5 ∨ F.dep F.S.u_yY 3 < F.dep F.S.u_yY 1 ∨ F.dep F.S.u_yY 6 < F.dep F.S.u_yY 1 ∨ F.dep F.S.u_yY 6 < F.dep F.S.u_yY 2)
  · exact F.yY_c (by refine pos_of_pos_mul htp1 ?_; linarith only [(mul_nonneg (F.S.tm_pos).le hCm), (mul_pos (mul_pos F.S.tp_pos F.S.sm_pos) hA1r)]) (by linarith only [hA3h]) o1.1 o1.2.1 o1.2.2.1 o1.2.2.2.1 o1.2.2.2.2
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 | n1 | n1 | n1
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tp_pos hsp1)) hal, mul_pos ((mul_pos (mul_pos F.S.tp_pos hsp1) hsm1)) hga, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le (F.S.km_pos).le) hW) (hde).le), mul_pos ((mul_pos (mul_pos htp1 F.S.km_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos F.S.tm_pos F.S.km_pos) rp)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le hD) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (htm1).le hD) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (hsm1).le hW) (hA1r).le) (hde).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n1_1), (sub_nonneg.2 n1_2), mul_pos ((mul_pos F.S.tp_pos F.S.sp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.tm_pos)) hbe, mul_pos ((mul_pos F.S.tm_pos htm1)) hbe, mul_pos ((mul_pos htm1 htm1)) hbe, mul_pos ((mul_pos htp1 hsp1)) hga, mul_pos ((mul_pos F.S.hp_pos F.S.kp_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.hp_pos F.S.hm_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg ((mul_pos F.S.hp_pos F.S.km_pos)).le (sub_nonneg.2 n0_2), mul_nonneg ((mul_pos F.S.km_pos hA1r)).le (sub_nonneg.2 n0_2), mul_nonneg ((mul_pos F.S.hp_pos F.S.hp_pos)).le (sub_nonneg.2 n0_4), mul_nonneg ((mul_pos F.S.hp_pos hA1r)).le (sub_nonneg.2 n0_4), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le (F.S.kp_pos).le) hA3h) (hal).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le hW) hA3h) (hal).le), (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le (F.S.hp_pos).le) hD) (hal).le), (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le (rm).le) hD) (hal).le), (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le hD) (hA1r).le) (hal).le), (mul_nonneg (mul_nonneg (mul_nonneg (htm1).le hD) hCm) (hal).le), mul_pos ((mul_pos (mul_pos hsm1 F.S.hp_pos) rp)) hal, mul_pos ((mul_pos (mul_pos hsm1 rp) rm)) hal, mul_pos ((mul_pos (mul_pos hsm1 rp) hA1r)) hal, (mul_nonneg (mul_nonneg (mul_nonneg (hsm1).le (hQ).le) hCm) (hal).le), (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le (F.S.hp_pos).le) hD) (hga).le), (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le hD) (hA1r).le) (hga).le), mul_pos ((mul_pos (mul_pos hsm1 F.S.hp_pos) rp)) hga, mul_pos ((mul_pos (mul_pos hsm1 rp) hA1r)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.sp_pos hsp1)) hbe, mul_pos ((mul_pos hsp1 hsp1)) hbe, mul_pos ((mul_pos htp1 hsp1)) hga, mul_pos ((mul_pos F.S.hp_pos F.S.kp_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg ((mul_pos F.S.tp_pos htm1)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos htp1 htm1)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos F.S.tp_pos hsp1)).le (sub_nonneg.2 n1_1), mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.kp_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos htp1 F.S.kp_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) hQ)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sm_pos).le hW) (hQ).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (hsm1).le hW) (hQ).le) (hde).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n1_1), (mul_nonneg hA3h (sub_nonneg.2 n1_1)), mul_pos ((mul_pos F.S.tp_pos F.S.kp_pos)) hal, mul_pos ((mul_pos F.S.tp_pos F.S.km_pos)) hal, (mul_nonneg (mul_nonneg (F.S.tp_pos).le hA3h) (hal).le), mul_pos ((mul_pos F.S.tp_pos rp)) hbe, (mul_nonneg (mul_nonneg (F.S.tp_pos).le hD) (hbe).le), mul_pos ((mul_pos htp1 F.S.kp_pos)) hbe, mul_pos ((mul_pos htp1 F.S.km_pos)) hbe, mul_pos ((mul_pos htp1 rp)) hbe, (mul_nonneg (mul_nonneg (htp1).le hD) (hbe).le), mul_pos ((mul_pos F.S.tm_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, (mul_nonneg (mul_nonneg (F.S.sp_pos).le hCm) (hbe).le), mul_pos ((mul_pos F.S.sm_pos F.S.kp_pos)) hbe, mul_pos ((mul_pos F.S.sm_pos hA1r)) hbe, mul_pos ((mul_pos hsm1 F.S.hm_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.hp_pos F.S.hm_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg ((mul_pos htm1 F.S.sm_pos)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos htm1 hsm1)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos F.S.tp_pos hsp1)).le (sub_nonneg.2 n1_3), mul_pos ((mul_pos (mul_pos htp1 F.S.km_pos) hQ)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sm_pos).le (hQ).le) hCm) (hde).le), mul_pos ((mul_pos (mul_pos hsm1 F.S.hp_pos) hQ)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (hsm1).le (hQ).le) hCm) (hde).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_3), (mul_nonneg hW (sub_nonneg.2 n1_3)), (mul_nonneg hD (sub_nonneg.2 n1_3)), mul_pos ((mul_pos F.S.tp_pos F.S.kp_pos)) hal, (mul_nonneg (mul_nonneg (F.S.tp_pos).le hW) (hal).le), (mul_nonneg (mul_nonneg (F.S.tp_pos).le hD) (hal).le), mul_pos ((mul_pos hsp1 F.S.km_pos)) hbe, (mul_nonneg (mul_nonneg (hsp1).le hCm) (hbe).le), mul_pos ((mul_pos hsm1 F.S.kp_pos)) hbe]


set_option maxHeartbeats 1600000 in
theorem Frame20.ra4_X_cc {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hW : 0 ≤ -F.S.hp*F.S.sp + F.S.hp - F.S.kp) (hQ : 0 < F.S.hm*F.S.sp*F.S.tp - F.S.hm*F.S.tp + F.S.hp*F.S.sp*F.S.tm - F.S.hp*F.S.sp - F.S.hp*F.S.tm + F.S.hp + F.S.kp*F.S.tm - F.S.kp) (hD : 0 ≤ -F.S.hp*F.S.sm*F.S.sp + F.S.hp*F.S.sm + F.S.hp*F.S.sp - F.S.hp - F.S.km*F.S.sp*F.S.tp + F.S.km*F.S.tp - F.S.kp*F.S.sm + F.S.kp) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hCm : 0 ≤ F.S.hp*F.S.sm + F.S.km*F.S.tp - F.S.km) (hA3 : 0 ≤ F.S.hm*F.S.sm*F.S.tp - F.S.hm + F.S.hp*F.S.sm*F.S.tm - F.S.hp*F.S.sm - F.S.km*F.S.tm + F.S.km)   :
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
  · exact F.vRa4_c (by linarith only [hW]) (by linarith only [hQ]) (by linarith only [hD]) o0.1 o0.2
  by_cases o1 : (F.dep F.S.u_xX 1 < F.dep F.S.u_xX 6 ∨ F.dep F.S.u_xX 1 < F.dep F.S.u_xX 3 ∨ F.dep F.S.u_xX 5 < F.dep F.S.u_xX 3 ∨ F.dep F.S.u_xX 5 < F.dep F.S.u_xX 2) ∧ (F.dep F.S.u_xX 3 < F.dep F.S.u_xX 1 ∨ F.dep F.S.u_xX 3 < F.dep F.S.u_xX 5 ∨ F.dep F.S.u_xX 2 < F.dep F.S.u_xX 5 ∨ F.dep F.S.u_xX 2 < F.dep F.S.u_xX 6) ∧ (F.dep F.S.u_xX 5 < F.dep F.S.u_xX 3 ∨ F.dep F.S.u_xX 5 < F.dep F.S.u_xX 2 ∨ F.dep F.S.u_xX 6 < F.dep F.S.u_xX 2 ∨ F.dep F.S.u_xX 6 < F.dep F.S.u_xX 1) ∧ (F.dep F.S.u_xX 2 < F.dep F.S.u_xX 5 ∨ F.dep F.S.u_xX 2 < F.dep F.S.u_xX 6 ∨ F.dep F.S.u_xX 1 < F.dep F.S.u_xX 6 ∨ F.dep F.S.u_xX 1 < F.dep F.S.u_xX 3) ∧ (F.dep F.S.u_xX 6 < F.dep F.S.u_xX 2 ∨ F.dep F.S.u_xX 6 < F.dep F.S.u_xX 1 ∨ F.dep F.S.u_xX 3 < F.dep F.S.u_xX 1 ∨ F.dep F.S.u_xX 3 < F.dep F.S.u_xX 5)
  · exact F.xX_c (by linarith only [hA3]) (by linarith only [hA1r]) (by linarith only [hCm]) o1.1 o1.2.1 o1.2.2.1 o1.2.2.2.1 o1.2.2.2.2
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 | n1 | n1 | n1
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n1_1), mul_nonneg (hsp1).le (sub_nonneg.2 n1_1), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, (mul_nonneg (mul_nonneg (htm1).le hCm) (hal).le), mul_pos ((mul_pos htp1 rm)) hbe, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hbe, (mul_nonneg (mul_nonneg (htm1).le hCm) (hbe).le), mul_pos ((mul_pos F.S.sm_pos hA1r)) hbe, mul_pos ((mul_pos hsm1 hA1r)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg ((mul_pos F.S.tm_pos htm1)).le (sub_nonneg.2 n0_4), mul_nonneg ((mul_pos F.S.tm_pos F.S.sp_pos)).le (sub_nonneg.2 n0_4), mul_nonneg ((mul_pos F.S.tm_pos hsp1)).le (sub_nonneg.2 n0_4), mul_nonneg ((mul_pos htm1 htm1)).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.tm_pos) hsp1)) hal, mul_pos ((mul_pos (mul_pos F.S.tp_pos htm1) hsp1)) hal, mul_pos ((mul_pos (mul_pos F.S.tp_pos hsp1) hsm1)) hga, (mul_nonneg (mul_nonneg (hQ).le hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le (F.S.hm_pos).le) hD) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le (rm).le) hW) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le (F.S.km_pos).le) hW) (hde).le), mul_pos ((mul_pos (mul_pos F.S.sm_pos F.S.hm_pos) rp)) hde, mul_pos ((mul_pos (mul_pos F.S.sm_pos F.S.km_pos) hQ)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sm_pos).le hW) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (hsm1).le (F.S.hm_pos).le) hW) (hde).le), mul_pos ((mul_pos (mul_pos hsm1 F.S.km_pos) hQ)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (hsm1).le hW) hA3) (hde).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(sub_nonneg.2 n0_4), mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.sp_pos) hsp1)) hal, mul_pos ((mul_pos (mul_pos F.S.tp_pos hsp1) hsp1)) hal, mul_pos ((mul_pos (mul_pos F.S.tp_pos hsp1) hsm1)) hga, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le (F.S.hm_pos).le) hD) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le hW) (hQ).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le hW) hD) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le hW) hA3) (hde).le), mul_pos ((mul_pos (mul_pos htp1 rm) hQ)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le hW) (hQ).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le hW) hD) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le hW) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le (F.S.kp_pos).le) hD) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le (F.S.km_pos).le) hW) (hde).le), mul_pos ((mul_pos (mul_pos F.S.tm_pos F.S.km_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos F.S.tm_pos rp) rm)) hde, mul_pos ((mul_pos (mul_pos htm1 F.S.km_pos) hQ)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (htm1).le hD) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.hm_pos).le) hD) (hde).le), mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.km_pos) hQ)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (hQ).le) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le hD) (hA1r).le) (hde).le), mul_pos ((mul_pos (mul_pos F.S.sm_pos F.S.hm_pos) rp)) hde, mul_pos ((mul_pos (mul_pos F.S.sm_pos F.S.kp_pos) hQ)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (hsm1).le (F.S.hm_pos).le) hW) (hde).le), mul_pos ((mul_pos (mul_pos hsm1 hQ) hA1r)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(sub_nonneg.2 n1_3), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, (mul_nonneg (mul_nonneg (htm1).le hCm) (hal).le), mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsp1 hA1r)) hal, mul_pos ((mul_pos htp1 rm)) hbe, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hbe, (mul_nonneg (mul_nonneg (htm1).le hCm) (hbe).le), mul_pos ((mul_pos F.S.sm_pos hA1r)) hbe, mul_pos ((mul_pos hsm1 hA1r)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg ((mul_pos F.S.tp_pos F.S.sp_pos)).le (sub_nonneg.2 n0_4), mul_nonneg ((mul_pos htp1 F.S.sp_pos)).le (sub_nonneg.2 n0_4), mul_nonneg ((mul_pos F.S.sp_pos hsp1)).le (sub_nonneg.2 n0_4), mul_nonneg ((mul_pos hsp1 hsp1)).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.tm_pos) hsp1)) hal, mul_pos ((mul_pos (mul_pos F.S.tp_pos htm1) hsp1)) hal, mul_pos ((mul_pos (mul_pos F.S.tp_pos hsp1) hsm1)) hga, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le (F.S.km_pos).le) hW) (hde).le), mul_pos ((mul_pos (mul_pos htp1 F.S.km_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos F.S.tm_pos F.S.km_pos) rp)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le hD) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (htm1).le hD) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (hsm1).le hW) (hA1r).le) (hde).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n1_1), mul_nonneg (hsp1).le (sub_nonneg.2 n1_1), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, (mul_nonneg (mul_nonneg (htm1).le hCm) (hal).le), mul_pos ((mul_pos htp1 rm)) hbe, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hbe, (mul_nonneg (mul_nonneg (htm1).le hCm) (hbe).le), mul_pos ((mul_pos F.S.sm_pos hA1r)) hbe, mul_pos ((mul_pos hsm1 hA1r)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg ((mul_pos F.S.tm_pos F.S.sm_pos)).le (sub_nonneg.2 n1_4), mul_nonneg ((mul_pos htm1 F.S.sm_pos)).le (sub_nonneg.2 n1_4), mul_nonneg ((mul_pos F.S.sm_pos hsm1)).le (sub_nonneg.2 n1_4), mul_nonneg ((mul_pos hsm1 hsm1)).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.tm_pos) rp)) hbe, mul_pos ((mul_pos (mul_pos F.S.tp_pos hsp1) hA1r)) hbe, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le (hsp1).le) hCm) (hbe).le), mul_pos ((mul_pos (mul_pos htp1 F.S.tm_pos) rp)) hbe, (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le (F.S.tm_pos).le) hD) (hbe).le), (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le (htm1).le) hD) (hbe).le), mul_pos ((mul_pos (mul_pos htp1 F.S.sm_pos) F.S.kp_pos)) hbe, mul_pos ((mul_pos (mul_pos htp1 F.S.sm_pos) hQ)) hbe, mul_pos ((mul_pos (mul_pos htp1 hsm1) hQ)) hbe, mul_pos ((mul_pos (mul_pos hsp1 F.S.sm_pos) hA1r)) hbe, (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le (hsp1).le) hA3) (hga).le), mul_pos ((mul_pos (mul_pos htp1 F.S.sm_pos) F.S.kp_pos)) hga, mul_pos ((mul_pos (mul_pos htp1 F.S.sm_pos) hQ)) hga, mul_pos ((mul_pos (mul_pos F.S.tm_pos F.S.sm_pos) rp)) hga, mul_pos ((mul_pos (mul_pos hsp1 F.S.sm_pos) hA1r)) hga, mul_pos ((mul_pos (mul_pos F.S.hp_pos F.S.kp_pos) rm)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg ((mul_pos F.S.tm_pos hA1r)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos htp1 F.S.tm_pos) rm)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos F.S.tm_pos F.S.tm_pos) F.S.hp_pos)).le (sub_nonneg.2 n0_1), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le (htm1).le) hCm) (sub_nonneg.2 n0_1)), (mul_nonneg (mul_nonneg (F.S.tm_pos).le hA3) (sub_nonneg.2 n0_2)), mul_nonneg ((mul_pos F.S.tp_pos hsp1)).le (sub_nonneg.2 n1_1), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le (F.S.hm_pos).le) (rp).le) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le (F.S.hm_pos).le) hW) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le (F.S.hm_pos).le) hD) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le (F.S.hm_pos).le) hD) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le (F.S.kp_pos).le) (hA1r).le) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le (F.S.hp_pos).le) (F.S.hp_pos).le) hW) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le (F.S.hp_pos).le) (F.S.hp_pos).le) hD) (hde).le), mul_pos ((mul_pos (mul_pos (mul_pos F.S.tm_pos F.S.hp_pos) F.S.hm_pos) F.S.kp_pos)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.tm_pos F.S.hp_pos) F.S.kp_pos) hA1r)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.tm_pos F.S.hp_pos) F.S.km_pos) hQ)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le (F.S.hp_pos).le) (rp).le) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le (F.S.hp_pos).le) hD) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le (F.S.hp_pos).le) hD) hCm) (hde).le), mul_pos ((mul_pos (mul_pos (mul_pos F.S.tm_pos F.S.hm_pos) F.S.km_pos) rp)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le (F.S.kp_pos).le) (F.S.km_pos).le) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le (F.S.kp_pos).le) hCm) hA3) (hde).le), mul_pos ((mul_pos (mul_pos (mul_pos F.S.tm_pos F.S.km_pos) rp) hA1r)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le (F.S.km_pos).le) hW) hA3) (hde).le), mul_pos ((mul_pos (mul_pos (mul_pos F.S.tm_pos F.S.km_pos) hQ) hA1r)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le (F.S.km_pos).le) (hQ).le) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (htm1).le (F.S.hm_pos).le) (F.S.kp_pos).le) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (htm1).le (F.S.kp_pos).le) (hA1r).le) hCm) (hde).le), mul_pos ((mul_pos (mul_pos (mul_pos F.S.sp_pos F.S.kp_pos) hA1r) hA1r)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.kp_pos).le) (hA1r).le) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le hW) (hA1r).le) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (hQ).le) (hA1r).le) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le hD) (hA1r).le) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le hD) (hA1r).le) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le hD) (hA1r).le) hA3) (hde).le), mul_pos ((mul_pos (mul_pos (mul_pos hsp1 F.S.kp_pos) hA1r) hA1r)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le (F.S.kp_pos).le) (hA1r).le) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le hW) (hA1r).le) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le (hQ).le) (hA1r).le) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le hD) (hA1r).le) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le hD) (hA1r).le) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le hD) (hA1r).le) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sm_pos).le (F.S.kp_pos).le) (hA1r).le) hA3) (hde).le), mul_pos ((mul_pos (mul_pos (mul_pos F.S.sm_pos hQ) hA1r) hA1r)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sm_pos).le (hQ).le) (hA1r).le) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hsm1).le (F.S.hm_pos).le) (F.S.kp_pos).le) hA3) (hde).le), mul_pos ((mul_pos (mul_pos (mul_pos hsm1 F.S.hm_pos) rp) hA1r)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hsm1).le (F.S.hm_pos).le) (rp).le) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hsm1).le (F.S.hm_pos).le) hW) hA3) (hde).le), mul_pos ((mul_pos (mul_pos (mul_pos hsm1 F.S.hm_pos) hQ) hA1r)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hsm1).le (F.S.hm_pos).le) (hQ).le) hCm) (hde).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(sub_nonneg.2 n1_3), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, (mul_nonneg (mul_nonneg (htm1).le hCm) (hal).le), mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsp1 hA1r)) hal, mul_pos ((mul_pos htp1 rm)) hbe, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hbe, (mul_nonneg (mul_nonneg (htm1).le hCm) (hbe).le), mul_pos ((mul_pos F.S.sm_pos hA1r)) hbe, mul_pos ((mul_pos hsm1 hA1r)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(mul_nonneg (mul_nonneg (htm1).le hCm) (sub_nonneg.2 n0_1)), mul_nonneg ((mul_pos hsm1 hA1r)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos htp1 F.S.tm_pos) rm)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos htp1 htm1) rm)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos F.S.tm_pos hsm1) F.S.hp_pos)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos htm1 F.S.sm_pos) hA1r)).le (sub_nonneg.2 n0_1), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le (htm1).le) hA3) (sub_nonneg.2 n0_2)), (mul_nonneg (mul_nonneg (mul_nonneg (htm1).le (htm1).le) hA3) (sub_nonneg.2 n0_2)), mul_nonneg ((mul_pos F.S.tp_pos hsp1)).le (sub_nonneg.2 n1_3), mul_pos ((mul_pos (mul_pos F.S.hp_pos rm) hQ)) hde]


set_option maxHeartbeats 1600000 in
theorem Frame20.om4ap_cc {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1R : 0 < F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) (hVpR : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVWR : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hKb : 0 ≤ F.S.hm + F.S.km*F.S.tm - F.S.km) (hss : 0 < F.S.sm - F.S.sp) (hnu : 0 < (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) :
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
  · exact rupert_of_r (F.rFrame.vN4_any (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVpR]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVWR]) o2.1 o2.2)
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
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga, mul_pos ((mul_pos hsm1 F.S.hm_pos)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_4)), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos htp1 rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hVpR).le (sub_nonneg.2 n0_4), mul_nonneg (hVWR).le (sub_nonneg.2 n1_4), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos htp1 rm)) hga, mul_pos ((mul_pos hsm1 hVWR)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(sub_nonneg.2 n0_3), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n1_4), hnu, mul_pos ((mul_pos htp1 F.S.tm_pos)) hal, mul_pos ((mul_pos F.S.tm_pos hsm1)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n0_1), mul_nonneg (htm1).le (sub_nonneg.2 n0_3), mul_pos F.S.sp_pos hnu, mul_pos hsm1 hnu, mul_pos hss hnu]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n2_4), mul_nonneg (htm1).le (sub_nonneg.2 n2_4), mul_pos F.S.tp_pos hnu, mul_pos htp1 hnu]


set_option maxHeartbeats 1600000 in
theorem Frame20.om4an_cc {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1R : 0 < F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) (hVpR : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVWR : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hKb : 0 ≤ F.S.hm + F.S.km*F.S.tm - F.S.km) (hss : 0 < F.S.sm - F.S.sp) (hnu : 0 < (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) :
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
  · exact rupert_of_r (F.rFrame.vN4_any (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVpR]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVWR]) o2.1 o2.2)
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
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga, mul_pos ((mul_pos hsm1 F.S.hm_pos)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (htp1).le (sub_nonneg.2 n0_1), (sub_nonneg.2 n0_2), mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n0_3), mul_nonneg (htp1).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n1_3), mul_pos F.S.sp_pos hnu, mul_pos hsm1 hnu, mul_pos hss hnu, mul_pos ((mul_pos htp1 htp1)) hal, mul_pos ((mul_pos htp1 htm1)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_2), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n1_3), mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hVpR).le (sub_nonneg.2 n0_4), mul_nonneg (hVWR).le (sub_nonneg.2 n1_4), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos ((mul_pos htp1 rm)) hga, mul_pos ((mul_pos hsm1 hVWR)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (htp1).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n1_4), mul_nonneg (htp1).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.sm_pos hsm1)) hga, mul_pos ((mul_pos hsm1 hsm1)) hga, mul_pos ((mul_pos F.S.hp_pos F.S.km_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(sub_nonneg.2 n2_4), mul_pos F.S.sp_pos hnu, mul_pos hsm1 hnu, mul_pos hss hnu]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg ((mul_pos htm1 F.S.sp_pos)).le (sub_nonneg.2 n1_1), mul_nonneg ((mul_pos htm1 hss)).le (sub_nonneg.2 n1_1), mul_nonneg ((mul_pos F.S.tp_pos hsm1)).le (sub_nonneg.2 n2_2), mul_nonneg ((mul_pos htp1 hsm1)).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos (mul_pos F.S.tm_pos rm) hA1R)) hde, mul_pos ((mul_pos (mul_pos htm1 rm) hA1R)) hde, mul_pos ((mul_pos (mul_pos hsm1 F.S.kp_pos) rm)) hde, mul_pos ((mul_pos (mul_pos hsm1 F.S.km_pos) rm)) hde, mul_pos ((mul_pos (mul_pos F.S.km_pos rm) hss)) hde]


set_option maxHeartbeats 1600000 in
theorem Frame20.om4az1_cc {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1R : 0 < F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) (hVpR : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVWR : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hKb : 0 ≤ F.S.hm + F.S.km*F.S.tm - F.S.km) (hss : 0 < F.S.sm - F.S.sp) (hnu1 : 0 ≤ (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) (hnu2 : 0 ≤ (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) (hl : 0 < (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) + (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg) :
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
  · exact rupert_of_r (F.rFrame.vN4_any (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVpR]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVWR]) o2.1 o2.2)
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
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga, mul_pos ((mul_pos hsm1 F.S.hm_pos)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga, mul_pos ((mul_pos hsm1 F.S.hm_pos)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(sub_nonneg.2 n0_3), mul_nonneg (htm1).le (sub_nonneg.2 n0_4), (sub_nonneg.2 n1_4), (sub_nonneg.2 n2_4), mul_pos ((mul_pos htp1 F.S.tm_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hsm1)) hga, mul_pos ((mul_pos hsm1 hsm1)) hga, mul_pos ((mul_pos hsm1 hss)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_4), mul_nonneg (hVWR).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos hsm1 hVpR)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n2_4), mul_nonneg (hsm1).le (sub_nonneg.2 n2_4), mul_nonneg (hss).le (sub_nonneg.2 n2_4), mul_pos F.S.tm_pos hl]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.sm_pos).le hnu1, mul_nonneg (hsm1).le hnu1, mul_pos F.S.tm_pos hl]


set_option maxHeartbeats 1600000 in
theorem Frame20.om4az2_cc {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1R : 0 < F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) (hVpR : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVWR : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hKb : 0 ≤ F.S.hm + F.S.km*F.S.tm - F.S.km) (hss : 0 < F.S.sm - F.S.sp) (hnu1 : 0 ≤ (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) (hnu2 : 0 ≤ (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) (hl : 0 < (-F.S.tm*F.S.tp + F.S.tm + F.S.tp - 1) * (F.a11 - F.a12) + (-F.S.tm*F.S.tp + F.S.tm + F.S.tp - 1) * F.a12 + (F.S.hm*F.S.hp) * F.gg) :
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
  · exact rupert_of_r (F.rFrame.vN4_any (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVpR]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVWR]) o2.1 o2.2)
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
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga, mul_pos ((mul_pos hsm1 F.S.hm_pos)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga, mul_pos ((mul_pos hsm1 F.S.hm_pos)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_4), mul_pos F.S.hm_pos hl, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos hsm1 F.S.hm_pos)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_3), mul_nonneg (hVpR).le (sub_nonneg.2 n1_4), (mul_nonneg hKb (sub_nonneg.2 n1_4)), mul_pos hVpR hl, (mul_nonneg hKb (hl).le), mul_pos ((mul_pos htp1 hVWR)) hal, mul_pos ((mul_pos hsm1 hVpR)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_1), mul_pos hVpR hl, (mul_nonneg hKb (hl).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_1), mul_pos F.S.hm_pos hl]


set_option maxHeartbeats 1600000 in
theorem Frame20.om4bp_cc {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1R : 0 < F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) (hVR : 0 < F.S.hm*F.S.sp + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) (hKb : 0 ≤ F.S.hm + F.S.km*F.S.tm - F.S.km) (hnu : 0 < (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg)   :
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
  · exact rupert_of_r (F.rFrame.vRv_c (by simp only [rFrame_S, Shape20.swap]; linarith only [hKb]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVR]) o2.1 o2.2)
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
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos F.S.tm_pos rm)) hga, mul_pos ((mul_pos htm1 rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_4)), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos htp1 rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos F.S.tm_pos rm)) hga, mul_pos ((mul_pos htm1 rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n0_1), mul_nonneg (htm1).le (sub_nonneg.2 n0_3), mul_pos F.S.tm_pos hnu, mul_pos htm1 hnu]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos F.S.tp_pos rm)) hga, mul_pos ((mul_pos htp1 rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]


set_option maxHeartbeats 1600000 in
theorem Frame20.om4bn_cc {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1R : 0 < F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) (hVR : 0 < F.S.hm*F.S.sp + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) (hKb : 0 ≤ F.S.hm + F.S.km*F.S.tm - F.S.km) (hnu : 0 < (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg)   :
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
  · exact rupert_of_r (F.rFrame.vRv_c (by simp only [rFrame_S, Shape20.swap]; linarith only [hKb]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVR]) o2.1 o2.2)
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
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga, mul_pos ((mul_pos hsm1 F.S.hm_pos)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), (mul_nonneg hKb (sub_nonneg.2 n1_3)), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_4)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_3), mul_pos ((mul_pos htp1 rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(sub_nonneg.2 n0_4), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n1_4), mul_nonneg (htm1).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.tm_pos hsm1)) hga, mul_pos ((mul_pos htm1 hsm1)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n2_3), mul_nonneg (htp1).le (sub_nonneg.2 n2_3), mul_pos F.S.sm_pos hnu, mul_pos hsm1 hnu]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_1)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos F.S.sm_pos rm)) hbe, mul_pos ((mul_pos F.S.sm_pos rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]


set_option maxHeartbeats 1600000 in
theorem Frame20.om4bz1_cc {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1R : 0 < F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) (hVR : 0 < F.S.hm*F.S.sp + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) (hKb : 0 ≤ F.S.hm + F.S.km*F.S.tm - F.S.km) (hnu1 : 0 ≤ (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) (hnu2 : 0 ≤ (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) (hl : 0 < (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) + (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg)   :
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
  · exact rupert_of_r (F.rFrame.vRv_c (by simp only [rFrame_S, Shape20.swap]; linarith only [hKb]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVR]) o2.1 o2.2)
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
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n0_1), mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n0_2), mul_nonneg (hsm1).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n1_3), mul_nonneg (hsm1).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n2_3), mul_nonneg (hsm1).le (sub_nonneg.2 n2_3), mul_pos F.S.sp_pos hl, mul_pos hsp1 hl]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), (mul_nonneg hKb (sub_nonneg.2 n1_3)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos hA1r)) hal, mul_pos ((mul_pos htm1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos rm)) hga, mul_pos ((mul_pos htm1 rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n0_4), mul_nonneg (hsp1).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n1_4), mul_nonneg (hsp1).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.sm_pos hsm1)) hga, mul_pos ((mul_pos hsm1 hsm1)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_nonneg (F.S.km_pos).le hnu1, mul_pos ((mul_pos F.S.tm_pos rm)) hga, mul_pos ((mul_pos htm1 rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n2_3), mul_nonneg (htp1).le (sub_nonneg.2 n2_3), mul_pos F.S.tm_pos hl]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_1)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos F.S.sm_pos rm)) hbe, mul_pos ((mul_pos F.S.sm_pos rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]


set_option maxHeartbeats 1600000 in
theorem Frame20.om4bz2_cc {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1R : 0 < F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) (hVR : 0 < F.S.hm*F.S.sp + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) (hKb : 0 ≤ F.S.hm + F.S.km*F.S.tm - F.S.km) (hnu1 : 0 ≤ (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) (hnu2 : 0 ≤ (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) (hl : 0 < (-F.S.tm*F.S.tp + F.S.tm + F.S.tp - 1) * (F.a11 - F.a12) + (-F.S.tm*F.S.tp + F.S.tm + F.S.tp - 1) * F.a12 + (F.S.hm*F.S.hp) * F.gg)   :
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
  · exact rupert_of_r (F.rFrame.vRv_c (by simp only [rFrame_S, Shape20.swap]; linarith only [hKb]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVR]) o2.1 o2.2)
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
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga, mul_pos ((mul_pos hsm1 F.S.hm_pos)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n0_3)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.km_pos).le hnu2, mul_pos F.S.km_pos hl, (mul_nonneg hKb (hl).le), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos hA1r)) hal, mul_pos ((mul_pos htm1 hA1r)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n1_4), mul_nonneg (hsm1).le (sub_nonneg.2 n1_4), mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n2_4), mul_nonneg (htp1).le (sub_nonneg.2 n2_4), hl, mul_pos F.S.tm_pos hl, mul_pos ((mul_pos F.S.tp_pos htp1)) hal, mul_pos ((mul_pos htp1 htp1)) hal, mul_pos ((mul_pos F.S.tp_pos htm1)) hga, mul_pos ((mul_pos htp1 htm1)) hga, mul_pos ((mul_pos F.S.tm_pos hsm1)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n0_1), mul_nonneg (htm1).le (sub_nonneg.2 n0_1), mul_pos F.S.sm_pos hl, mul_pos hsm1 hl]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n0_3)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), (mul_nonneg hKb (hl).le), (mul_nonneg (mul_nonneg (htp1).le hKb) (hal).le), mul_pos ((mul_pos F.S.tp_pos rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]


set_option maxHeartbeats 1600000 in
theorem Frame20.om4cp_cc {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1Rr : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVpR : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVWR : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hKb : 0 ≤ F.S.hm + F.S.km*F.S.tm - F.S.km) (hss : 0 < F.S.sm - F.S.sp) (hnu : 0 < (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg)  :
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
  · exact rupert_of_r (F.rFrame.tANR_any (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1Rr]) o1.1 o1.2)
  by_cases o2 : (F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 6 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 6) ∧ (F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 4 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 4)
  · exact rupert_of_r (F.rFrame.vN4_any (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVpR]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVWR]) o2.1 o2.2)
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
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_4), mul_nonneg (hVpR).le (sub_nonneg.2 n1_1), (mul_nonneg hKb (sub_nonneg.2 n1_2)), mul_nonneg (hVpR).le (sub_nonneg.2 n1_4), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_2), mul_nonneg (hA1Rr).le (sub_nonneg.2 n2_2), mul_nonneg (rm).le (sub_nonneg.2 n3_1), mul_nonneg (hVWR).le (sub_nonneg.2 n3_1), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos hsm1 rm)) hbe, mul_pos ((mul_pos hsm1 hVpR)) hbe, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hbe).le), mul_pos ((mul_pos rm hss)) hbe, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_2), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), (mul_nonneg hKb (sub_nonneg.2 n1_2)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n1_3), (mul_nonneg hKb (sub_nonneg.2 n1_3)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_2), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_3), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos rm hss)) hbe, mul_pos ((mul_pos rm hss)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sm_pos hA1Rr)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_3)), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_3)), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [(sub_nonneg.2 n0_3), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n1_3), mul_pos F.S.tm_pos hnu, mul_pos htm1 hnu, mul_pos ((mul_pos htp1 F.S.tm_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n3_1), mul_pos ((mul_pos hsm1 F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hsm1 F.S.km_pos)) hga, mul_pos ((mul_pos hsm1 hA1Rr)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n0_1), mul_nonneg (htm1).le (sub_nonneg.2 n0_3), mul_pos F.S.sm_pos hnu, mul_pos hsm1 hnu]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n3_1), mul_pos ((mul_pos hsm1 F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hsm1 F.S.km_pos)) hga, mul_pos ((mul_pos hsm1 hA1Rr)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n2_4), mul_pos hVpR hnu, (mul_nonneg hKb (hnu).le)]


set_option maxHeartbeats 1600000 in
theorem Frame20.om4cz1_cc {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1Rr : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVpR : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVWR : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hKb : 0 ≤ F.S.hm + F.S.km*F.S.tm - F.S.km) (hss : 0 < F.S.sm - F.S.sp) (hnu1 : 0 ≤ (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) (hnu2 : 0 ≤ (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) (hl : 0 < (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) + (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg)  :
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
  · exact rupert_of_r (F.rFrame.tANR_any (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1Rr]) o1.1 o1.2)
  by_cases o2 : (F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 6 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 6) ∧ (F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 4 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 4)
  · exact rupert_of_r (F.rFrame.vN4_any (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVpR]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVWR]) o2.1 o2.2)
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
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sp_pos hA1Rr)) hbe, mul_pos ((mul_pos hsp1 hA1Rr)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sp_pos hA1Rr)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hA1Rr hss)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_nonneg (hVpR).le (sub_nonneg.2 n0_2), mul_nonneg (hVWR).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n3_4), mul_nonneg (hVpR).le (sub_nonneg.2 n3_4), mul_nonneg (F.S.km_pos).le hnu1, mul_pos F.S.km_pos hl, mul_pos hVpR hl, (mul_nonneg hKb (hl).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (hVWR).le (sub_nonneg.2 n0_3), mul_nonneg (hVWR).le (sub_nonneg.2 n1_4), mul_nonneg (hVWR).le (sub_nonneg.2 n3_1), mul_pos hVpR hl, (mul_nonneg hKb (hl).le), mul_pos ((mul_pos hsm1 hVWR)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n3_1), mul_pos ((mul_pos hsm1 F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hsm1 F.S.km_pos)) hga, mul_pos ((mul_pos hsm1 hA1Rr)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (hA1r).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_nonneg (hA1r).le (sub_nonneg.2 n1_3), mul_pos hA1r hl, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sm_pos hA1Rr)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [(sub_nonneg.2 n0_3), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n2_4), mul_nonneg (htp1).le (sub_nonneg.2 n2_4), mul_pos ((mul_pos htp1 F.S.tm_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos hsm1 hVpR)) hbe, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hbe).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [(sub_nonneg.2 n0_3), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.tm_pos).le hnu1, mul_nonneg (htm1).le hnu1, mul_pos ((mul_pos htp1 F.S.tm_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sp_pos hA1Rr)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hA1Rr hss)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n2_4), mul_nonneg (hsm1).le (sub_nonneg.2 n2_4), mul_nonneg (hss).le (sub_nonneg.2 n2_4), mul_pos F.S.tm_pos hl]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVpR).le (sub_nonneg.2 n1_2), (mul_nonneg hKb (sub_nonneg.2 n1_2)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_2), mul_nonneg (hA1Rr).le (sub_nonneg.2 n2_2), mul_nonneg (rm).le (sub_nonneg.2 n3_1), mul_nonneg (hVWR).le (sub_nonneg.2 n3_1), mul_pos ((mul_pos hsm1 rm)) hbe, mul_pos ((mul_pos hsm1 hVpR)) hbe, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hbe).le), mul_pos ((mul_pos rm hss)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_2)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_1), mul_pos ((mul_pos rm hss)) hbe, mul_pos ((mul_pos rm hss)) hga]


set_option maxHeartbeats 1600000 in
theorem Frame20.om4cz2_cc {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1Rr : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVpR : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVWR : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hKb : 0 ≤ F.S.hm + F.S.km*F.S.tm - F.S.km) (hss : 0 < F.S.sm - F.S.sp) (hnu1 : 0 ≤ (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) (hnu2 : 0 ≤ (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) (hl : 0 < (-F.S.tm*F.S.tp + F.S.tm + F.S.tp - 1) * (F.a11 - F.a12) + (-F.S.tm*F.S.tp + F.S.tm + F.S.tp - 1) * F.a12 + (F.S.hm*F.S.hp) * F.gg)  :
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
  · exact rupert_of_r (F.rFrame.tANR_any (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1Rr]) o1.1 o1.2)
  by_cases o2 : (F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 6 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 6) ∧ (F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 4 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 4)
  · exact rupert_of_r (F.rFrame.vN4_any (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVpR]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVWR]) o2.1 o2.2)
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
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_3), mul_nonneg (hVWR).le (sub_nonneg.2 n1_3), mul_pos F.S.km_pos hl, mul_pos hVpR hl, (mul_nonneg hKb (hl).le), mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_3), mul_nonneg (hVpR).le (sub_nonneg.2 n1_3), (mul_nonneg hKb (sub_nonneg.2 n1_3)), mul_pos F.S.km_pos hl, mul_pos hVWR hl, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_3), mul_nonneg (hVWR).le (sub_nonneg.2 n1_3), mul_pos F.S.km_pos hl, mul_pos hVpR hl, (mul_nonneg hKb (hl).le), mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos hA1r)) hal, mul_pos ((mul_pos htm1 hA1r)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_3), mul_pos F.S.hm_pos hl, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.tp_pos hA1Rr)) hbe, mul_pos ((mul_pos htp1 hA1Rr)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_1), mul_pos hVpR hl, (mul_nonneg hKb (hl).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n3_4), mul_nonneg (hVpR).le (sub_nonneg.2 n3_4), mul_pos F.S.km_pos hl, mul_pos hVpR hl, (mul_nonneg hKb (hl).le), mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n0_1), mul_pos hsm1 hl, mul_pos hss hl]


set_option maxHeartbeats 1600000 in
theorem Frame20.om4cnop_cc {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1Rr : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVpR : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVWR : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hKb : 0 ≤ F.S.hm + F.S.km*F.S.tm - F.S.km) (hss : 0 < F.S.sm - F.S.sp) (hnu : 0 < (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) (hom : 0 < (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg)  :
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
  · exact rupert_of_r (F.rFrame.tANR_any (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1Rr]) o1.1 o1.2)
  by_cases o2 : (F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 6 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 6) ∧ (F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 4 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 4)
  · exact rupert_of_r (F.rFrame.vN4_any (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVpR]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVWR]) o2.1 o2.2)
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
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_pos F.S.hm_pos hom, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_pos F.S.hm_pos hom, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_2), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n1_4), mul_nonneg (hVpR).le (sub_nonneg.2 n1_4), (mul_nonneg hKb (sub_nonneg.2 n1_4)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n3_1), mul_nonneg (hVWR).le (sub_nonneg.2 n3_1), mul_pos F.S.km_pos hnu, mul_pos F.S.hm_pos hom, mul_pos hVpR hom, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos hsm1 F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hVWR)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_pos F.S.hm_pos hom, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [(sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos hsm1)) hbe, mul_pos ((mul_pos hsm1 hsm1)) hbe, mul_pos ((mul_pos hsm1 hss)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n2_4), mul_pos hVpR hnu, (mul_nonneg hKb (hnu).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_4), mul_pos hVpR hom, (mul_nonneg hKb (hom).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [(sub_nonneg.2 n0_4), mul_pos F.S.tp_pos hom, mul_pos htp1 hom]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_4), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_1), mul_pos F.S.kp_pos hom, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sp_pos hA1Rr)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hA1Rr hss)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_4), mul_pos hVpR hom, (mul_nonneg hKb (hom).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n1_1), mul_nonneg (hsm1).le (sub_nonneg.2 n1_2), mul_nonneg (hsm1).le (sub_nonneg.2 n3_1), (sub_nonneg.2 n3_2), mul_pos ((mul_pos hsm1 hsm1)) hbe, mul_pos ((mul_pos hsm1 hsm1)) hga, mul_pos ((mul_pos F.S.km_pos F.S.km_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVpR).le (sub_nonneg.2 n0_4), (mul_nonneg hKb (sub_nonneg.2 n1_1)), (mul_nonneg hKb (sub_nonneg.2 n1_4)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_1), mul_pos hVWR hom, mul_pos ((mul_pos rm hss)) hbe, mul_pos ((mul_pos rm hss)) hga]


set_option maxHeartbeats 1600000 in
theorem Frame20.om4cnom_cc {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1Rr : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVpR : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVWR : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hKb : 0 ≤ F.S.hm + F.S.km*F.S.tm - F.S.km) (hss : 0 < F.S.sm - F.S.sp) (hnu : 0 < (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) (hom : 0 < (-F.S.sm*F.S.tp + F.S.sm + F.S.tp - 1) * F.a12 + (F.S.hp*F.S.km) * F.gg)  :
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
  · exact rupert_of_r (F.rFrame.tANR_any (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1Rr]) o1.1 o1.2)
  by_cases o2 : (F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 6 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 6) ∧ (F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 4 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 4)
  · exact rupert_of_r (F.rFrame.vN4_any (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVpR]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVWR]) o2.1 o2.2)
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
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_2), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hom, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_2), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hom, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hnu, (mul_nonneg hKb (hom).le), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_nonneg (hVWR).le (sub_nonneg.2 n1_4), (mul_nonneg hKb (sub_nonneg.2 n3_1)), mul_nonneg (hVpR).le (sub_nonneg.2 n3_3), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hbe).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos hVpR hom, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n2_4), mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.tp_pos hnu, mul_pos htp1 hnu, mul_pos hss hnu]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sp_pos hA1Rr)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hA1Rr hss)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n1_3), mul_pos F.S.sp_pos hom, mul_pos hss hom]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n1_4), mul_nonneg (hVWR).le (sub_nonneg.2 n3_1), mul_nonneg (hVWR).le (sub_nonneg.2 n3_4), mul_pos ((mul_pos hsm1 hVpR)) hbe, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hbe).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n2_4), mul_pos hsm1 hnu, mul_pos hss hnu]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n3_1), mul_pos ((mul_pos hsm1 F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hsm1 F.S.km_pos)) hga, mul_pos ((mul_pos hsm1 hA1Rr)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_2)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_1), mul_pos ((mul_pos rm hss)) hbe, mul_pos ((mul_pos rm hss)) hga]


set_option maxHeartbeats 1600000 in
theorem Frame20.om4cnoz1_cc {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1Rr : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVpR : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVWR : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hKb : 0 ≤ F.S.hm + F.S.km*F.S.tm - F.S.km) (hss : 0 < F.S.sm - F.S.sp) (hnu : 0 < (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) (hom1 : 0 ≤ (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) (hom2 : 0 ≤ (-F.S.sm*F.S.tp + F.S.sm + F.S.tp - 1) * F.a12 + (F.S.hp*F.S.km) * F.gg) (hl2 : 0 < (F.S.hp*F.S.sp) * (F.a22 - F.a12) + (F.S.hp*F.S.sp - F.S.hp - F.S.kp*F.S.tp + F.S.kp) * F.a12)  :
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
  · exact rupert_of_r (F.rFrame.tANR_any (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1Rr]) o1.1 o1.2)
  by_cases o2 : (F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 6 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 6) ∧ (F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 4 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 4)
  · exact rupert_of_r (F.rFrame.vN4_any (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVpR]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVWR]) o2.1 o2.2)
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
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hnu, (mul_nonneg hKb hom2), mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_2), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hnu, mul_nonneg (F.S.km_pos).le hom2, (mul_nonneg hKb hom2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), (mul_nonneg hKb (sub_nonneg.2 n1_2)), (mul_nonneg hKb (sub_nonneg.2 n1_3)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_2), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_3), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos rm hss)) hbe, mul_pos ((mul_pos rm hss)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sp_pos hA1Rr)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hA1Rr hss)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [(sub_nonneg.2 n2_4), mul_pos F.S.sm_pos hnu, mul_pos hsm1 hnu]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sp_pos hA1Rr)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hA1Rr hss)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n3_3), mul_pos hsm1 hl2]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.tm_pos hA1Rr)) hbe, mul_pos ((mul_pos htm1 hA1Rr)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n2_4), mul_pos hVpR hnu, (mul_nonneg hKb (hnu).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sp_pos hA1Rr)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hA1Rr hss)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_2)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_1), mul_pos ((mul_pos rm hss)) hbe, mul_pos ((mul_pos rm hss)) hga]


set_option maxHeartbeats 1600000 in
theorem Frame20.om4cnoz2_cc {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1Rr : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVpR : 0 < -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hVWR : 0 < -F.S.hm*F.S.sp + F.S.hm - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp + F.S.km*F.S.tm - F.S.km - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) (hKb : 0 ≤ F.S.hm + F.S.km*F.S.tm - F.S.km) (hss : 0 < F.S.sm - F.S.sp) (hnu : 0 < (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) (hom1 : 0 ≤ (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) (hom2 : 0 ≤ (-F.S.sm*F.S.tp + F.S.sm + F.S.tp - 1) * F.a12 + (F.S.hp*F.S.km) * F.gg) (hl2 : 0 < (-F.S.hp*F.S.sp) * (F.a22 - F.a12) + (-F.S.hp*F.S.sp + F.S.hp + F.S.kp*F.S.tp - F.S.kp) * F.a12)  :
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
  · exact rupert_of_r (F.rFrame.tANR_any (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1Rr]) o1.1 o1.2)
  by_cases o2 : (F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 0 < F.rFrame.dep F.rFrame.S.u_vN4 6 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 3 ∨ F.rFrame.dep F.rFrame.S.u_vN4 4 < F.rFrame.dep F.rFrame.S.u_vN4 6) ∧ (F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 0 ∨ F.rFrame.dep F.rFrame.S.u_vN4 3 < F.rFrame.dep F.rFrame.S.u_vN4 4 ∨ F.rFrame.dep F.rFrame.S.u_vN4 6 < F.rFrame.dep F.rFrame.S.u_vN4 4)
  · exact rupert_of_r (F.rFrame.vN4_any (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVpR]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVWR]) o2.1 o2.2)
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
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hnu, (mul_nonneg hKb hom2), mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_2), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hnu, mul_nonneg (F.S.km_pos).le hom2, (mul_nonneg hKb hom2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), (mul_nonneg hKb (sub_nonneg.2 n3_4)), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), (mul_nonneg hKb (sub_nonneg.2 n1_2)), (mul_nonneg hKb (sub_nonneg.2 n1_3)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_2), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_3), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos rm hss)) hbe, mul_pos ((mul_pos rm hss)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sp_pos hA1Rr)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hA1Rr hss)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n2_4), mul_pos hsm1 hnu, mul_pos hss hnu]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sp_pos hA1Rr)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hA1Rr hss)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n1_4), mul_pos hsm1 hl2]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n3_1), mul_pos ((mul_pos hsm1 F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hsm1 F.S.km_pos)) hga, mul_pos ((mul_pos hsm1 hA1Rr)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n2_4), mul_nonneg (htp1).le (sub_nonneg.2 n2_4), mul_pos F.S.sp_pos hnu, mul_pos hsm1 hnu, mul_pos hss hnu]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sp_pos hA1Rr)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hA1Rr hss)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_2)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_1), mul_pos ((mul_pos rm hss)) hbe, mul_pos ((mul_pos rm hss)) hga]


set_option maxHeartbeats 1600000 in
theorem Frame20.om4dp_cc {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1Rr : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVR : 0 < F.S.hm*F.S.sp + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) (hKb : 0 ≤ F.S.hm + F.S.km*F.S.tm - F.S.km) (hnu : 0 < (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) :
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
  · exact rupert_of_r (F.rFrame.tANR_any (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1Rr]) o1.1 o1.2)
  by_cases o2 : (F.rFrame.dep F.rFrame.S.u_vRv 0 < F.rFrame.dep F.rFrame.S.u_vRv 6 ∨ F.rFrame.dep F.rFrame.S.u_vRv 0 < F.rFrame.dep F.rFrame.S.u_vRv 5 ∨ F.rFrame.dep F.rFrame.S.u_vRv 4 < F.rFrame.dep F.rFrame.S.u_vRv 6 ∨ F.rFrame.dep F.rFrame.S.u_vRv 4 < F.rFrame.dep F.rFrame.S.u_vRv 5) ∧ (F.rFrame.dep F.rFrame.S.u_vRv 6 < F.rFrame.dep F.rFrame.S.u_vRv 0 ∨ F.rFrame.dep F.rFrame.S.u_vRv 5 < F.rFrame.dep F.rFrame.S.u_vRv 0 ∨ F.rFrame.dep F.rFrame.S.u_vRv 6 < F.rFrame.dep F.rFrame.S.u_vRv 4 ∨ F.rFrame.dep F.rFrame.S.u_vRv 5 < F.rFrame.dep F.rFrame.S.u_vRv 4)
  · exact rupert_of_r (F.rFrame.vRv_c (by simp only [rFrame_S, Shape20.swap]; linarith only [hKb]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVR]) o2.1 o2.2)
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
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos F.S.tm_pos rm)) hga, mul_pos ((mul_pos htm1 rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos F.S.tp_pos rm)) hga, mul_pos ((mul_pos htp1 rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n3_1), mul_pos ((mul_pos hsm1 F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hsm1 F.S.km_pos)) hga, mul_pos ((mul_pos hsm1 hA1Rr)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n3_1), mul_pos ((mul_pos hsm1 F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hsm1 F.S.km_pos)) hga, mul_pos ((mul_pos hsm1 hA1Rr)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos F.S.tm_pos rm)) hga, mul_pos ((mul_pos htm1 rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos F.S.tm_pos rm)) hga, mul_pos ((mul_pos htm1 rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_2)), mul_nonneg (rm).le (sub_nonneg.2 n1_4), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_nonneg (rm).le (sub_nonneg.2 n3_1), (mul_nonneg hKb (sub_nonneg.2 n3_1)), mul_nonneg (rm).le (sub_nonneg.2 n3_4), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos F.S.tp_pos rm)) hbe, mul_pos ((mul_pos htp1 rm)) hbe, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hbe).le), mul_pos ((mul_pos F.S.sm_pos rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_1)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos F.S.sm_pos rm)) hbe, mul_pos ((mul_pos F.S.sm_pos rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]


set_option maxHeartbeats 1600000 in
theorem Frame20.om4dn_cc {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1Rr : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVR : 0 < F.S.hm*F.S.sp + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) (hKb : 0 ≤ F.S.hm + F.S.km*F.S.tm - F.S.km) (hnu : 0 < (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) :
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
  · exact rupert_of_r (F.rFrame.tANR_any (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1Rr]) o1.1 o1.2)
  by_cases o2 : (F.rFrame.dep F.rFrame.S.u_vRv 0 < F.rFrame.dep F.rFrame.S.u_vRv 6 ∨ F.rFrame.dep F.rFrame.S.u_vRv 0 < F.rFrame.dep F.rFrame.S.u_vRv 5 ∨ F.rFrame.dep F.rFrame.S.u_vRv 4 < F.rFrame.dep F.rFrame.S.u_vRv 6 ∨ F.rFrame.dep F.rFrame.S.u_vRv 4 < F.rFrame.dep F.rFrame.S.u_vRv 5) ∧ (F.rFrame.dep F.rFrame.S.u_vRv 6 < F.rFrame.dep F.rFrame.S.u_vRv 0 ∨ F.rFrame.dep F.rFrame.S.u_vRv 5 < F.rFrame.dep F.rFrame.S.u_vRv 0 ∨ F.rFrame.dep F.rFrame.S.u_vRv 6 < F.rFrame.dep F.rFrame.S.u_vRv 4 ∨ F.rFrame.dep F.rFrame.S.u_vRv 5 < F.rFrame.dep F.rFrame.S.u_vRv 4)
  · exact rupert_of_r (F.rFrame.vRv_c (by simp only [rFrame_S, Shape20.swap]; linarith only [hKb]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVR]) o2.1 o2.2)
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
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_2), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n3_4), (mul_nonneg hKb (sub_nonneg.2 n3_4)), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos rm)) hga, mul_pos ((mul_pos htm1 rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), (mul_nonneg hKb (sub_nonneg.2 n1_3)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos ((mul_pos htp1 F.S.hm_pos)) hal, mul_pos ((mul_pos F.S.sp_pos rm)) hga, mul_pos ((mul_pos hsp1 rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.tp_pos hA1Rr)) hbe, mul_pos ((mul_pos htp1 hA1Rr)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hA1Rr).le (sub_nonneg.2 n2_4), mul_pos hA1Rr hnu, mul_pos ((mul_pos F.S.sp_pos rm)) hga, mul_pos ((mul_pos hsm1 hVR)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (hA1Rr).le (sub_nonneg.2 n2_4), mul_pos hA1Rr hnu, mul_pos ((mul_pos F.S.sp_pos rm)) hga, mul_pos ((mul_pos hsm1 hVR)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [(sub_nonneg.2 n2_3), mul_pos F.S.sp_pos hnu, mul_pos hsp1 hnu]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_2)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_2), (mul_nonneg hKb (sub_nonneg.2 n3_1)), mul_pos ((mul_pos F.S.sm_pos rm)) hbe, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hbe).le), mul_pos ((mul_pos F.S.sm_pos rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]


set_option maxHeartbeats 1600000 in
theorem Frame20.om4dz1_cc {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1Rr : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVR : 0 < F.S.hm*F.S.sp + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) (hKb : 0 ≤ F.S.hm + F.S.km*F.S.tm - F.S.km) (hnu1 : 0 ≤ (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) (hnu2 : 0 ≤ (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) (hl : 0 < (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) + (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg) :
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
  · exact rupert_of_r (F.rFrame.tANR_any (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1Rr]) o1.1 o1.2)
  by_cases o2 : (F.rFrame.dep F.rFrame.S.u_vRv 0 < F.rFrame.dep F.rFrame.S.u_vRv 6 ∨ F.rFrame.dep F.rFrame.S.u_vRv 0 < F.rFrame.dep F.rFrame.S.u_vRv 5 ∨ F.rFrame.dep F.rFrame.S.u_vRv 4 < F.rFrame.dep F.rFrame.S.u_vRv 6 ∨ F.rFrame.dep F.rFrame.S.u_vRv 4 < F.rFrame.dep F.rFrame.S.u_vRv 5) ∧ (F.rFrame.dep F.rFrame.S.u_vRv 6 < F.rFrame.dep F.rFrame.S.u_vRv 0 ∨ F.rFrame.dep F.rFrame.S.u_vRv 5 < F.rFrame.dep F.rFrame.S.u_vRv 0 ∨ F.rFrame.dep F.rFrame.S.u_vRv 6 < F.rFrame.dep F.rFrame.S.u_vRv 4 ∨ F.rFrame.dep F.rFrame.S.u_vRv 5 < F.rFrame.dep F.rFrame.S.u_vRv 4)
  · exact rupert_of_r (F.rFrame.vRv_c (by simp only [rFrame_S, Shape20.swap]; linarith only [hKb]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVR]) o2.1 o2.2)
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
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (hA1r).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_nonneg (hA1r).le (sub_nonneg.2 n3_4), mul_pos hA1r hl, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (hA1r).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_nonneg (hA1r).le (sub_nonneg.2 n3_4), (mul_nonneg hKb (sub_nonneg.2 n3_4)), mul_pos hA1r hl, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos rm)) hga, mul_pos ((mul_pos htm1 rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_nonneg (rm).le (sub_nonneg.2 n0_2), mul_nonneg (rm).le (sub_nonneg.2 n0_3), (mul_nonneg hKb (sub_nonneg.2 n1_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_4), mul_nonneg (rm).le (sub_nonneg.2 n1_4), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n3_1), mul_nonneg (rm).le (sub_nonneg.2 n3_1), (mul_nonneg hKb (sub_nonneg.2 n3_3)), mul_nonneg (F.S.km_pos).le hnu1, mul_pos F.S.km_pos hl, mul_pos rm hl, (mul_nonneg (mul_nonneg (htp1).le hKb) (hal).le), mul_pos ((mul_pos F.S.tp_pos rm)) hbe, mul_pos ((mul_pos htp1 rm)) hbe, mul_pos ((mul_pos hsm1 F.S.hm_pos)) hbe, mul_pos ((mul_pos F.S.sm_pos rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_nonneg (hA1r).le (sub_nonneg.2 n0_3), mul_nonneg (hA1r).le (sub_nonneg.2 n1_3), mul_pos hA1r hl, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.tm_pos hA1Rr)) hbe, mul_pos ((mul_pos htm1 hA1Rr)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_2)), mul_nonneg (rm).le (sub_nonneg.2 n1_4), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_2), mul_nonneg (rm).le (sub_nonneg.2 n3_1), (mul_nonneg hKb (sub_nonneg.2 n3_1)), mul_nonneg (rm).le (sub_nonneg.2 n3_4), mul_pos ((mul_pos F.S.tp_pos rm)) hbe, mul_pos ((mul_pos htp1 rm)) hbe, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hbe).le), mul_pos ((mul_pos F.S.sm_pos rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]


set_option maxHeartbeats 1600000 in
theorem Frame20.om4dz2_cc {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hA1Rr : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hVR : 0 < F.S.hm*F.S.sp + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) (hKb : 0 ≤ F.S.hm + F.S.km*F.S.tm - F.S.km) (hnu1 : 0 ≤ (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) (hnu2 : 0 ≤ (F.S.sm*F.S.tm*F.S.tp - F.S.sm*F.S.tm - F.S.sm*F.S.tp + F.S.sm) * F.a12 + (-F.S.hm*F.S.hp - F.S.hp*F.S.km*F.S.tm + F.S.hp*F.S.km) * F.gg) (hl : 0 < (-F.S.tm*F.S.tp + F.S.tm + F.S.tp - 1) * (F.a11 - F.a12) + (-F.S.tm*F.S.tp + F.S.tm + F.S.tp - 1) * F.a12 + (F.S.hm*F.S.hp) * F.gg) :
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
  · exact rupert_of_r (F.rFrame.tANR_any (hx.comp rperm_bijective.1) (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1Rr]) o1.1 o1.2)
  by_cases o2 : (F.rFrame.dep F.rFrame.S.u_vRv 0 < F.rFrame.dep F.rFrame.S.u_vRv 6 ∨ F.rFrame.dep F.rFrame.S.u_vRv 0 < F.rFrame.dep F.rFrame.S.u_vRv 5 ∨ F.rFrame.dep F.rFrame.S.u_vRv 4 < F.rFrame.dep F.rFrame.S.u_vRv 6 ∨ F.rFrame.dep F.rFrame.S.u_vRv 4 < F.rFrame.dep F.rFrame.S.u_vRv 5) ∧ (F.rFrame.dep F.rFrame.S.u_vRv 6 < F.rFrame.dep F.rFrame.S.u_vRv 0 ∨ F.rFrame.dep F.rFrame.S.u_vRv 5 < F.rFrame.dep F.rFrame.S.u_vRv 0 ∨ F.rFrame.dep F.rFrame.S.u_vRv 6 < F.rFrame.dep F.rFrame.S.u_vRv 4 ∨ F.rFrame.dep F.rFrame.S.u_vRv 5 < F.rFrame.dep F.rFrame.S.u_vRv 4)
  · exact rupert_of_r (F.rFrame.vRv_c (by simp only [rFrame_S, Shape20.swap]; linarith only [hKb]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hVR]) o2.1 o2.2)
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
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_nonneg (F.S.km_pos).le hnu1, mul_pos ((mul_pos F.S.tm_pos rm)) hga, mul_pos ((mul_pos htm1 rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), (mul_nonneg hKb (sub_nonneg.2 n1_3)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos rm)) hga, mul_pos ((mul_pos htm1 rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_3), mul_pos F.S.hm_pos hl, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n0_3)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.km_pos hl, (mul_nonneg hKb (hl).le), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos hA1r)) hal, mul_pos ((mul_pos htm1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos rm)) hga, mul_pos ((mul_pos htm1 rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n3_3), mul_nonneg (F.S.km_pos).le hnu1, mul_pos F.S.hm_pos hl, mul_pos ((mul_pos htp1 F.S.km_pos)) hal, (mul_nonneg (mul_nonneg (htp1).le hKb) (hal).le), mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos F.S.tp_pos rm)) hga, mul_pos ((mul_pos hsm1 F.S.km_pos)) hga, mul_pos ((mul_pos hsm1 hA1Rr)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]


set_option maxHeartbeats 1600000 in
theorem Frame20.ra4_A_R_cc {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hW : 0 ≤ -F.S.hm - F.S.km*F.S.tm + F.S.km) (hQ : 0 < F.S.hm*F.S.sp - F.S.hm + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp - F.S.km*F.S.tm + F.S.km + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) (hD : 0 ≤ -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.sm*F.S.tm + F.S.hp*F.S.sm - F.S.km*F.S.tm*F.S.tp + F.S.km*F.S.tm + F.S.km*F.S.tp - F.S.km) (hA1 : 0 < F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp)   :
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
  · exact rupert_of_r (F.rFrame.vRa4_c (by simp only [rFrame_S, Shape20.swap]; linarith only [hW]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hQ]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hD]) o0.1 o0.2)
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
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_tA] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n1_3), mul_nonneg (htp1).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.hp_pos F.S.km_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_tA] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_4), (mul_nonneg hW (sub_nonneg.2 n1_3)), mul_pos ((mul_pos F.S.sm_pos F.S.hm_pos)) hbe, (mul_nonneg (mul_nonneg (F.S.sm_pos).le hW) (hbe).le), mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_tA] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.tp_pos hsm1)) hga, mul_pos ((mul_pos F.S.hp_pos F.S.km_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_tA] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg ((mul_pos F.S.sm_pos hsm1)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos hsm1 hsm1)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos htm1 F.S.sm_pos)).le (sub_nonneg.2 n1_1), mul_pos ((mul_pos F.S.km_pos hQ)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le hW) (hA1).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le hW) (hA1).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.kp_pos).le) hW) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le (F.S.kp_pos).le) hW) (hde).le), mul_pos ((mul_pos (mul_pos F.S.sm_pos F.S.hm_pos) F.S.kp_pos)) hde, mul_pos ((mul_pos (mul_pos F.S.sm_pos F.S.hm_pos) F.S.km_pos)) hde]


set_option maxHeartbeats 1600000 in
theorem Frame20.ra4_Y_R_cc {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hW : 0 ≤ -F.S.hm - F.S.km*F.S.tm + F.S.km) (hQ : 0 < F.S.hm*F.S.sp - F.S.hm + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp - F.S.km*F.S.tm + F.S.km + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) (hD : 0 ≤ -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.sm*F.S.tm + F.S.hp*F.S.sm - F.S.km*F.S.tm*F.S.tp + F.S.km*F.S.tm + F.S.km*F.S.tp - F.S.km) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hCm : 0 ≤ F.S.hp*F.S.sm - F.S.hp + F.S.km*F.S.tp) (hA3h : 0 ≤ F.S.hp*F.S.sp - F.S.hp - F.S.km*F.S.sp*F.S.tp + F.S.km*F.S.tp - F.S.kp*F.S.sm*F.S.tp + F.S.kp)   :
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
  · exact rupert_of_r (F.rFrame.vRa4_c (by simp only [rFrame_S, Shape20.swap]; linarith only [hW]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hQ]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hD]) o0.1 o0.2)
  by_cases o1 : (F.rFrame.dep F.rFrame.S.u_yY 1 < F.rFrame.dep F.rFrame.S.u_yY 3 ∨ F.rFrame.dep F.rFrame.S.u_yY 1 < F.rFrame.dep F.rFrame.S.u_yY 6 ∨ F.rFrame.dep F.rFrame.S.u_yY 2 < F.rFrame.dep F.rFrame.S.u_yY 6 ∨ F.rFrame.dep F.rFrame.S.u_yY 2 < F.rFrame.dep F.rFrame.S.u_yY 5) ∧ (F.rFrame.dep F.rFrame.S.u_yY 6 < F.rFrame.dep F.rFrame.S.u_yY 1 ∨ F.rFrame.dep F.rFrame.S.u_yY 6 < F.rFrame.dep F.rFrame.S.u_yY 2 ∨ F.rFrame.dep F.rFrame.S.u_yY 5 < F.rFrame.dep F.rFrame.S.u_yY 2 ∨ F.rFrame.dep F.rFrame.S.u_yY 5 < F.rFrame.dep F.rFrame.S.u_yY 3) ∧ (F.rFrame.dep F.rFrame.S.u_yY 2 < F.rFrame.dep F.rFrame.S.u_yY 6 ∨ F.rFrame.dep F.rFrame.S.u_yY 2 < F.rFrame.dep F.rFrame.S.u_yY 5 ∨ F.rFrame.dep F.rFrame.S.u_yY 3 < F.rFrame.dep F.rFrame.S.u_yY 5 ∨ F.rFrame.dep F.rFrame.S.u_yY 3 < F.rFrame.dep F.rFrame.S.u_yY 1) ∧ (F.rFrame.dep F.rFrame.S.u_yY 5 < F.rFrame.dep F.rFrame.S.u_yY 2 ∨ F.rFrame.dep F.rFrame.S.u_yY 5 < F.rFrame.dep F.rFrame.S.u_yY 3 ∨ F.rFrame.dep F.rFrame.S.u_yY 1 < F.rFrame.dep F.rFrame.S.u_yY 3 ∨ F.rFrame.dep F.rFrame.S.u_yY 1 < F.rFrame.dep F.rFrame.S.u_yY 6) ∧ (F.rFrame.dep F.rFrame.S.u_yY 3 < F.rFrame.dep F.rFrame.S.u_yY 5 ∨ F.rFrame.dep F.rFrame.S.u_yY 3 < F.rFrame.dep F.rFrame.S.u_yY 1 ∨ F.rFrame.dep F.rFrame.S.u_yY 6 < F.rFrame.dep F.rFrame.S.u_yY 1 ∨ F.rFrame.dep F.rFrame.S.u_yY 6 < F.rFrame.dep F.rFrame.S.u_yY 2)
  · exact rupert_of_r (F.rFrame.yY_c (by simp only [rFrame_S, Shape20.swap]; refine pos_of_pos_mul hsm1 ?_; linarith only [(mul_nonneg (F.S.sp_pos).le hCm), (mul_pos (mul_pos F.S.tp_pos F.S.sm_pos) hA1r)]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hA3h]) o1.1 o1.2.1 o1.2.2.1 o1.2.2.2.1 o1.2.2.2.2)
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 | n1 | n1 | n1
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg ((mul_pos F.S.tp_pos F.S.sp_pos)).le (sub_nonneg.2 n0_3), mul_nonneg ((mul_pos F.S.tp_pos hsp1)).le (sub_nonneg.2 n0_3), mul_nonneg (htp1).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos (mul_pos htp1 htm1) F.S.sm_pos)) hbe, mul_pos ((mul_pos (mul_pos htp1 htm1) F.S.sm_pos)) hga, mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.hp_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos htp1 F.S.hp_pos) hQ)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le (F.S.kp_pos).le) hW) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le hW) (hA1r).le) (hde).le), mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) rm)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.hp_pos).le) hW) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le hD) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le hD) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sm_pos).le (F.S.hp_pos).le) hW) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sm_pos).le (F.S.kp_pos).le) hD) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (hsm1).le (rp).le) hW) (hde).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n1_1), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_1), mul_nonneg (hA1r).le (sub_nonneg.2 n1_1), (mul_nonneg hA3h (sub_nonneg.2 n1_1)), mul_pos ((mul_pos F.S.tp_pos F.S.hm_pos)) hal, mul_pos ((mul_pos F.S.tp_pos hQ)) hal, (mul_nonneg (mul_nonneg (F.S.tp_pos).le hD) (hal).le), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 F.S.kp_pos)) hal, mul_pos ((mul_pos htp1 hQ)) hal, (mul_nonneg (mul_nonneg (htp1).le hD) (hal).le), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos hA1r)) hal, (mul_nonneg (mul_nonneg (F.S.tm_pos).le hCm) (hal).le), mul_pos ((mul_pos htm1 F.S.kp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos F.S.hp_pos)) hal, mul_pos ((mul_pos hsp1 F.S.hm_pos)) hal, mul_pos ((mul_pos hsm1 F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sm_pos F.S.hp_pos)) hbe, mul_pos ((mul_pos F.S.sm_pos F.S.hm_pos)) hbe, mul_pos ((mul_pos F.S.sm_pos hA1r)) hbe, (mul_nonneg (mul_nonneg (F.S.sm_pos).le hA3h) (hbe).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.kp_pos F.S.km_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n0_4), mul_nonneg ((mul_pos F.S.tm_pos F.S.sm_pos)).le (sub_nonneg.2 n0_4), mul_nonneg ((mul_pos F.S.tm_pos hsm1)).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos (mul_pos htm1 F.S.sp_pos) F.S.sm_pos)) hbe, mul_pos ((mul_pos (mul_pos htm1 hsp1) F.S.sm_pos)) hbe, mul_pos ((mul_pos (mul_pos htp1 htm1) F.S.sm_pos)) hga, (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le (F.S.kp_pos).le) hW) (hde).le), mul_pos ((mul_pos (mul_pos htp1 F.S.kp_pos) hQ)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le hW) (hA1r).le) (hde).le), mul_pos ((mul_pos (mul_pos htp1 hQ) hA1r)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le hD) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (htm1).le hD) (hA1r).le) (hde).le), mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) rm)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.hp_pos).le) hW) (hde).le), mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos rp) rm)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le hD) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sm_pos).le (F.S.hp_pos).le) hW) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sm_pos).le (F.S.kp_pos).le) hD) (hde).le), mul_pos ((mul_pos (mul_pos F.S.sm_pos rp) hQ)) hde, mul_pos ((mul_pos (mul_pos hsm1 rp) hQ)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.tm_pos htm1)) hal, mul_pos ((mul_pos htm1 htm1)) hal, mul_pos ((mul_pos htm1 hsm1)) hga, mul_pos ((mul_pos F.S.hm_pos F.S.km_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg ((mul_pos F.S.tp_pos hsp1)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos htp1 hsp1)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos htm1 F.S.sm_pos)).le (sub_nonneg.2 n1_1), mul_pos ((mul_pos (mul_pos F.S.tm_pos F.S.km_pos) hQ)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le hW) (hQ).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (htm1).le hW) (hQ).le) (hde).le), mul_pos ((mul_pos (mul_pos F.S.sm_pos F.S.hm_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos hsm1 F.S.hm_pos) hQ)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n1_1), (sub_nonneg.2 n1_2), mul_pos ((mul_pos F.S.sp_pos F.S.sp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hsp1)) hal, mul_pos ((mul_pos hsp1 hsp1)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.sm_pos)) hbe, mul_pos ((mul_pos htm1 hsm1)) hga, mul_pos ((mul_pos F.S.hm_pos F.S.km_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.kp_pos F.S.km_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg ((mul_pos F.S.sp_pos hsp1)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos hsp1 hsp1)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos htm1 F.S.sm_pos)).le (sub_nonneg.2 n1_3), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le (hQ).le) hCm) (hde).le), mul_pos ((mul_pos (mul_pos htp1 F.S.km_pos) hQ)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le (hQ).le) hCm) (hde).le), mul_pos ((mul_pos (mul_pos hsm1 F.S.hp_pos) hQ)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_3), (mul_nonneg hW (sub_nonneg.2 n1_3)), mul_nonneg (hA1r).le (sub_nonneg.2 n1_3), mul_pos ((mul_pos F.S.tp_pos hQ)) hal, mul_pos ((mul_pos htp1 hQ)) hal, mul_pos ((mul_pos F.S.tm_pos hA1r)) hal, mul_pos ((mul_pos htm1 F.S.kp_pos)) hal, mul_pos ((mul_pos hsp1 F.S.hm_pos)) hal, mul_pos ((mul_pos F.S.sm_pos F.S.hm_pos)) hbe, (mul_nonneg (mul_nonneg (F.S.sm_pos).le hW) (hbe).le), mul_pos ((mul_pos F.S.sm_pos hA1r)) hbe]


set_option maxHeartbeats 1600000 in
theorem Frame20.ra4_X_R_cc {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hW : 0 ≤ -F.S.hm - F.S.km*F.S.tm + F.S.km) (hQ : 0 < F.S.hm*F.S.sp - F.S.hm + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp - F.S.km*F.S.tm + F.S.km + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) (hD : 0 ≤ -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.sm*F.S.tm + F.S.hp*F.S.sm - F.S.km*F.S.tm*F.S.tp + F.S.km*F.S.tm + F.S.km*F.S.tp - F.S.km) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hCm : 0 ≤ F.S.hp*F.S.sm - F.S.hp + F.S.km*F.S.tp) (hA3 : 0 ≤ -F.S.hp*F.S.sp + F.S.hp + F.S.km*F.S.sp*F.S.tp - F.S.km*F.S.tp + F.S.kp*F.S.sm*F.S.tp - F.S.kp)   :
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
  · exact rupert_of_r (F.rFrame.vRa4_c (by simp only [rFrame_S, Shape20.swap]; linarith only [hW]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hQ]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hD]) o0.1 o0.2)
  by_cases o1 : (F.rFrame.dep F.rFrame.S.u_xX 1 < F.rFrame.dep F.rFrame.S.u_xX 6 ∨ F.rFrame.dep F.rFrame.S.u_xX 1 < F.rFrame.dep F.rFrame.S.u_xX 3 ∨ F.rFrame.dep F.rFrame.S.u_xX 5 < F.rFrame.dep F.rFrame.S.u_xX 3 ∨ F.rFrame.dep F.rFrame.S.u_xX 5 < F.rFrame.dep F.rFrame.S.u_xX 2) ∧ (F.rFrame.dep F.rFrame.S.u_xX 3 < F.rFrame.dep F.rFrame.S.u_xX 1 ∨ F.rFrame.dep F.rFrame.S.u_xX 3 < F.rFrame.dep F.rFrame.S.u_xX 5 ∨ F.rFrame.dep F.rFrame.S.u_xX 2 < F.rFrame.dep F.rFrame.S.u_xX 5 ∨ F.rFrame.dep F.rFrame.S.u_xX 2 < F.rFrame.dep F.rFrame.S.u_xX 6) ∧ (F.rFrame.dep F.rFrame.S.u_xX 5 < F.rFrame.dep F.rFrame.S.u_xX 3 ∨ F.rFrame.dep F.rFrame.S.u_xX 5 < F.rFrame.dep F.rFrame.S.u_xX 2 ∨ F.rFrame.dep F.rFrame.S.u_xX 6 < F.rFrame.dep F.rFrame.S.u_xX 2 ∨ F.rFrame.dep F.rFrame.S.u_xX 6 < F.rFrame.dep F.rFrame.S.u_xX 1) ∧ (F.rFrame.dep F.rFrame.S.u_xX 2 < F.rFrame.dep F.rFrame.S.u_xX 5 ∨ F.rFrame.dep F.rFrame.S.u_xX 2 < F.rFrame.dep F.rFrame.S.u_xX 6 ∨ F.rFrame.dep F.rFrame.S.u_xX 1 < F.rFrame.dep F.rFrame.S.u_xX 6 ∨ F.rFrame.dep F.rFrame.S.u_xX 1 < F.rFrame.dep F.rFrame.S.u_xX 3) ∧ (F.rFrame.dep F.rFrame.S.u_xX 6 < F.rFrame.dep F.rFrame.S.u_xX 2 ∨ F.rFrame.dep F.rFrame.S.u_xX 6 < F.rFrame.dep F.rFrame.S.u_xX 1 ∨ F.rFrame.dep F.rFrame.S.u_xX 3 < F.rFrame.dep F.rFrame.S.u_xX 1 ∨ F.rFrame.dep F.rFrame.S.u_xX 3 < F.rFrame.dep F.rFrame.S.u_xX 5)
  · exact rupert_of_r (F.rFrame.xX_c (by simp only [rFrame_S, Shape20.swap]; linarith only [hA3]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hA1r]) (by simp only [rFrame_S, Shape20.swap]; linarith only [hCm]) o1.1 o1.2.1 o1.2.2.1 o1.2.2.2.1 o1.2.2.2.2)
  exfalso
  simp only [not_and_or, not_or, not_lt] at o0
  simp only [not_and_or, not_or, not_lt] at o1
  rcases o0 with n0 | n0 <;>
    rcases o1 with n1 | n1 | n1 | n1 | n1
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(sub_nonneg.2 n1_1), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, (mul_nonneg (mul_nonneg (F.S.tp_pos).le hCm) (hal).le), (mul_nonneg (mul_nonneg (htp1).le hCm) (hal).le), mul_pos ((mul_pos hsm1 F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos htm1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, (mul_nonneg (mul_nonneg (hsp1).le hCm) (hbe).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(sub_nonneg.2 n0_4), mul_pos ((mul_pos (mul_pos F.S.tp_pos htm1) F.S.sm_pos)) hbe, mul_pos ((mul_pos (mul_pos htp1 htm1) F.S.sm_pos)) hbe, mul_pos ((mul_pos (mul_pos htp1 htm1) F.S.sm_pos)) hga, mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.hm_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.kp_pos) rm)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le hW) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le (hQ).le) hD) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le (F.S.kp_pos).le) hW) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le hW) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le (hQ).le) hD) (hde).le), mul_pos ((mul_pos (mul_pos F.S.tm_pos F.S.hp_pos) hQ)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le hW) (hQ).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le (hQ).le) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (htm1).le hW) (hQ).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.hp_pos).le) hW) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.km_pos).le) hD) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sm_pos).le (F.S.kp_pos).le) hD) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sm_pos).le hD) (hA1r).le) (hde).le), mul_pos ((mul_pos (mul_pos hsm1 F.S.hp_pos) hQ)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (hsm1).le hD) (hA1r).le) (hde).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(sub_nonneg.2 n0_4), mul_pos ((mul_pos (mul_pos F.S.tp_pos htm1) F.S.sm_pos)) hbe, mul_pos ((mul_pos (mul_pos htp1 htm1) F.S.sm_pos)) hbe, mul_pos ((mul_pos (mul_pos htp1 htm1) F.S.sm_pos)) hga, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le hW) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le hW) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le (F.S.kp_pos).le) hW) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le hW) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le hW) hA3) (hde).le), mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) rm)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.hp_pos).le) hW) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le hW) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le hD) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le hW) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le hD) (hA1r).le) (hde).le), mul_pos ((mul_pos (mul_pos hsm1 F.S.hp_pos) hQ)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(sub_nonneg.2 n1_3), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, (mul_nonneg (mul_nonneg (F.S.tp_pos).le hCm) (hal).le), (mul_nonneg (mul_nonneg (htp1).le hCm) (hal).le), mul_pos ((mul_pos hsm1 F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos htm1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, (mul_nonneg (mul_nonneg (hsp1).le hCm) (hbe).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(sub_nonneg.2 n0_4), mul_pos ((mul_pos htm1 F.S.sm_pos)) hbe, mul_pos ((mul_pos (mul_pos htp1 htm1) F.S.sm_pos)) hga, (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le (F.S.kp_pos).le) hW) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.hp_pos).le) hW) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.km_pos).le) hW) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.km_pos).le) hD) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le hW) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le hW) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le hD) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le hW) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le hW) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le hW) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le hD) (hA1r).le) (hde).le), mul_pos ((mul_pos (mul_pos hsm1 F.S.hp_pos) hQ)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(sub_nonneg.2 n1_1), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, (mul_nonneg (mul_nonneg (F.S.tp_pos).le hCm) (hal).le), (mul_nonneg (mul_nonneg (htp1).le hCm) (hal).le), mul_pos ((mul_pos hsm1 F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos htm1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, (mul_nonneg (mul_nonneg (hsp1).le hCm) (hbe).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg ((mul_pos F.S.tp_pos F.S.km_pos)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos F.S.tp_pos hA1r)).le (sub_nonneg.2 n0_1), (mul_nonneg (mul_nonneg (F.S.tp_pos).le hA3) (sub_nonneg.2 n0_2)), (mul_nonneg (mul_nonneg (htp1).le hA3) (sub_nonneg.2 n0_2)), mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos (mul_pos F.S.tp_pos htm1) F.S.kp_pos)) hal, mul_pos ((mul_pos (mul_pos F.S.tp_pos htm1) hA1r)) hal, mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.sm_pos) F.S.hm_pos)) hal, mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.sm_pos) hQ)) hal, mul_pos ((mul_pos (mul_pos htp1 htm1) hA1r)) hal, mul_pos ((mul_pos (mul_pos htp1 F.S.sp_pos) F.S.hm_pos)) hal, mul_pos ((mul_pos (mul_pos htp1 F.S.sp_pos) rm)) hal, (mul_nonneg (mul_nonneg (mul_nonneg (htm1).le (hsp1).le) hCm) (hal).le), (mul_nonneg (mul_nonneg (mul_nonneg (htm1).le (hsm1).le) hA3) (hal).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.sp_pos).le) hW) (hal).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (hsp1).le) hW) (hal).le), mul_pos ((mul_pos (mul_pos F.S.sp_pos hsm1) F.S.hm_pos)) hal, mul_pos ((mul_pos (mul_pos htp1 F.S.sp_pos) rm)) hbe, mul_pos ((mul_pos (mul_pos htm1 F.S.sm_pos) hA1r)) hbe, (mul_nonneg (mul_nonneg (mul_nonneg (htm1).le (F.S.sm_pos).le) hCm) (hbe).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (hsm1).le) hD) (hbe).le), mul_pos ((mul_pos (mul_pos F.S.km_pos rp) rm)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [mul_nonneg ((mul_pos (mul_pos F.S.tp_pos F.S.sp_pos) F.S.km_pos)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos F.S.tp_pos F.S.sp_pos) hA1r)).le (sub_nonneg.2 n0_1), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le (F.S.sp_pos).le) hA3) (sub_nonneg.2 n0_2)), (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le (F.S.sp_pos).le) hA3) (sub_nonneg.2 n0_2)), mul_nonneg ((mul_pos htm1 F.S.sm_pos)).le (sub_nonneg.2 n1_1), mul_pos ((mul_pos (mul_pos (mul_pos htp1 F.S.kp_pos) F.S.km_pos) hQ)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le (F.S.kp_pos).le) (F.S.km_pos).le) hD) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le (F.S.hm_pos).le) (hA1r).le) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (htm1).le (F.S.hm_pos).le) (hA1r).le) hA3) (hde).le), mul_pos ((mul_pos (mul_pos (mul_pos htm1 F.S.km_pos) hA1r) hA1r)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) F.S.hp_pos) rm)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) F.S.km_pos) hQ)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.hp_pos).le) hW) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.hp_pos).le) hW) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.hp_pos).le) hD) (hA1r).le) (hde).le), mul_pos ((mul_pos (mul_pos (mul_pos F.S.sp_pos F.S.hm_pos) F.S.kp_pos) F.S.km_pos)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.sp_pos F.S.hm_pos) F.S.km_pos) hA1r)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.hm_pos).le) (F.S.km_pos).le) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.kp_pos).le) hW) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.kp_pos).le) hD) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.km_pos).le) hW) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le (F.S.hp_pos).le) hD) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le (F.S.hm_pos).le) (F.S.kp_pos).le) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le (F.S.kp_pos).le) hW) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le (F.S.kp_pos).le) hD) hCm) (hde).le), mul_pos ((mul_pos (mul_pos (mul_pos F.S.sm_pos F.S.hm_pos) F.S.kp_pos) hA1r)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sm_pos).le (F.S.hm_pos).le) (F.S.kp_pos).le) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sm_pos).le (F.S.kp_pos).le) hW) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sm_pos).le (F.S.kp_pos).le) hW) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hsm1).le (F.S.kp_pos).le) hW) hA3) (hde).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(sub_nonneg.2 n1_3), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, (mul_nonneg (mul_nonneg (F.S.tp_pos).le hCm) (hal).le), (mul_nonneg (mul_nonneg (htp1).le hCm) (hal).le), mul_pos ((mul_pos hsm1 F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos htm1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, (mul_nonneg (mul_nonneg (hsp1).le hCm) (hbe).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    linarith only [(mul_nonneg (mul_nonneg (hsp1).le hCm) (sub_nonneg.2 n0_1)), mul_nonneg ((mul_pos (mul_pos F.S.tp_pos hsp1) hA1r)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos htp1 F.S.sp_pos) F.S.km_pos)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos htp1 F.S.sp_pos) hA1r)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos htp1 hsp1) hA1r)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos F.S.sm_pos hsm1) rp)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos hsm1 hsm1) rp)).le (sub_nonneg.2 n0_1), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (hsp1).le) hA3) (sub_nonneg.2 n0_2)), (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le (hsp1).le) hA3) (sub_nonneg.2 n0_2)), mul_nonneg ((mul_pos htm1 F.S.sm_pos)).le (sub_nonneg.2 n1_3), mul_pos ((mul_pos (mul_pos F.S.km_pos rp) hQ)) hde]


set_option maxHeartbeats 1600000 in
theorem Frame20.om4ap_R_cc {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hA1R : 0 < F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) (hVpR : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm - F.S.kp*F.S.tm) (hVWR : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.sp + F.S.hp*F.S.tm - F.S.hp - F.S.kp*F.S.tm + F.S.kp) (hKb : 0 ≤ F.S.hp*F.S.sp - F.S.hp + F.S.kp) (hss : 0 < -F.S.tm + F.S.tp) (hnu : 0 < (-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 + (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg) :
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
  · exact F.vN4_any hx (by linarith only [hVpR]) (by linarith only [hVWR]) o2.1 o2.2
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
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hA1r hss)) hbe, mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hA1r hss)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hVpR)) hbe, mul_pos ((mul_pos hA1r hss)) hbe, mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hA1r hss)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_4)), mul_pos F.S.hp_pos hnu, (mul_nonneg (mul_nonneg (htp1).le hKb) (hga).le), mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(sub_nonneg.2 n0_3), mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n1_4), hnu, mul_pos ((mul_pos F.S.sp_pos hsm1)) hbe, mul_pos ((mul_pos htp1 F.S.sp_pos)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hsp1).le (sub_nonneg.2 n0_3), mul_pos htp1 hnu, mul_pos F.S.tm_pos hnu, mul_pos hss hnu]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n2_4), mul_pos hVpR hnu, (mul_nonneg hKb (hnu).le)]


set_option maxHeartbeats 1600000 in
theorem Frame20.om4an_R_cc {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hA1R : 0 < F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) (hVpR : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm - F.S.kp*F.S.tm) (hVWR : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.sp + F.S.hp*F.S.tm - F.S.hp - F.S.kp*F.S.tm + F.S.kp) (hKb : 0 ≤ F.S.hp*F.S.sp - F.S.hp + F.S.kp) (hss : 0 < -F.S.tm + F.S.tp) (hnu : 0 < (F.S.sm*F.S.sp*F.S.tp - F.S.sm*F.S.tp - F.S.sp*F.S.tp + F.S.tp) * F.a12 + (-F.S.hp*F.S.km*F.S.sp + F.S.hp*F.S.km - F.S.km*F.S.kp) * F.gg) :
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
  · exact F.vN4_any hx (by linarith only [hVpR]) (by linarith only [hVWR]) o2.1 o2.2
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
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hVpR)) hbe, mul_pos ((mul_pos htp1 F.S.kp_pos)) hga, mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hA1r hss)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hA1r hss)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hA1r hss)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hVpR).le (sub_nonneg.2 n0_4), mul_nonneg (hVWR).le (sub_nonneg.2 n1_4), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_4), mul_pos ((mul_pos htp1 hVpR)) hga, (mul_nonneg (mul_nonneg (htp1).le hKb) (hga).le), mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n0_4), mul_nonneg (htp1).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n1_4), mul_nonneg (htp1).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos htp1 F.S.sp_pos)) hga, mul_pos ((mul_pos htp1 hsp1)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n2_4), mul_nonneg (hsm1).le (sub_nonneg.2 n2_4), mul_pos htp1 hnu, mul_pos F.S.tm_pos hnu, mul_pos hss hnu]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg ((mul_pos F.S.tm_pos hsp1)).le (sub_nonneg.2 n1_1), mul_nonneg ((mul_pos hsp1 hss)).le (sub_nonneg.2 n1_1), mul_nonneg ((mul_pos htp1 F.S.sm_pos)).le (sub_nonneg.2 n2_2), mul_nonneg ((mul_pos htp1 hsm1)).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos (mul_pos htp1 F.S.hp_pos) rp)) hde, mul_pos ((mul_pos (mul_pos htp1 F.S.hm_pos) rp)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos rp) hA1R)) hde, mul_pos ((mul_pos (mul_pos hsp1 rp) hA1R)) hde, mul_pos ((mul_pos (mul_pos F.S.hp_pos rp) hss)) hde]


set_option maxHeartbeats 1600000 in
theorem Frame20.om4az1_R_cc {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hA1R : 0 < F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) (hVpR : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm - F.S.kp*F.S.tm) (hVWR : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.sp + F.S.hp*F.S.tm - F.S.hp - F.S.kp*F.S.tm + F.S.kp) (hKb : 0 ≤ F.S.hp*F.S.sp - F.S.hp + F.S.kp) (hss : 0 < -F.S.tm + F.S.tp) (hnu1 : 0 ≤ (-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 + (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg) (hnu2 : 0 ≤ (F.S.sm*F.S.sp*F.S.tp - F.S.sm*F.S.tp - F.S.sp*F.S.tp + F.S.tp) * F.a12 + (-F.S.hp*F.S.km*F.S.sp + F.S.hp*F.S.km - F.S.km*F.S.kp) * F.gg) (hl : 0 < (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * (F.a22 - F.a12) + (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * F.a12 + (-F.S.km*F.S.kp) * F.gg) :
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
  · exact F.vN4_any hx (by linarith only [hVpR]) (by linarith only [hVWR]) o2.1 o2.2
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
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hA1r hss)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hA1r hss)) hbe, mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hA1r hss)) hbe, mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hVpR).le (sub_nonneg.2 n0_4), mul_nonneg (hVWR).le (sub_nonneg.2 n1_4), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_4), mul_pos ((mul_pos htp1 hVWR)) hga, mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_4)), mul_nonneg (F.S.hp_pos).le hnu1, (mul_nonneg (mul_nonneg (htp1).le hKb) (hga).le), mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n2_4), mul_nonneg (htm1).le (sub_nonneg.2 n2_4), mul_nonneg (hss).le hnu2, mul_pos F.S.sp_pos hl]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.sm_pos).le hnu1, mul_nonneg (hsm1).le hnu1, mul_pos F.S.sp_pos hl]


set_option maxHeartbeats 1600000 in
theorem Frame20.om4az2_R_cc {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hA1R : 0 < F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) (hVpR : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm - F.S.kp*F.S.tm) (hVWR : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.sp + F.S.hp*F.S.tm - F.S.hp - F.S.kp*F.S.tm + F.S.kp) (hKb : 0 ≤ F.S.hp*F.S.sp - F.S.hp + F.S.kp) (hss : 0 < -F.S.tm + F.S.tp) (hnu1 : 0 ≤ (-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 + (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg) (hnu2 : 0 ≤ (F.S.sm*F.S.sp*F.S.tp - F.S.sm*F.S.tp - F.S.sp*F.S.tp + F.S.tp) * F.a12 + (-F.S.hp*F.S.km*F.S.sp + F.S.hp*F.S.km - F.S.km*F.S.kp) * F.gg) (hl : 0 < (-F.S.sm*F.S.sp + F.S.sm + F.S.sp - 1) * (F.a22 - F.a12) + (-F.S.sm*F.S.sp + F.S.sm + F.S.sp - 1) * F.a12 + (F.S.km*F.S.kp) * F.gg) :
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
  · exact F.vN4_any hx (by linarith only [hVpR]) (by linarith only [hVWR]) o2.1 o2.2
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
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_4), mul_pos F.S.hp_pos hl, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hVpR)) hbe, mul_pos ((mul_pos hA1r hss)) hbe, mul_pos ((mul_pos htp1 F.S.kp_pos)) hga, mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_4), mul_pos F.S.hp_pos hl, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hVpR)) hbe, mul_pos ((mul_pos hA1r hss)) hbe, mul_pos ((mul_pos htp1 F.S.kp_pos)) hga, mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.hp_pos hl, mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hA1r hss)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (rm).le (sub_nonneg.2 n0_3), mul_nonneg (rm).le (sub_nonneg.2 n1_4), mul_pos rm hl, mul_pos ((mul_pos hsm1 rm)) hbe, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (rm).le (sub_nonneg.2 n0_3), mul_nonneg (rm).le (sub_nonneg.2 n1_4), mul_pos rm hl, mul_pos ((mul_pos hsm1 rm)) hbe, mul_pos ((mul_pos htp1 rm)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_1), mul_pos hVpR hl, (mul_nonneg hKb (hl).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hA1R).le (sub_nonneg.2 n0_1), mul_pos hA1R hl]


set_option maxHeartbeats 1600000 in
theorem Frame20.om4bp_R_cc {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hA1R : 0 < F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) (hVR : 0 < F.S.hm*F.S.sp*F.S.tp - F.S.hm*F.S.tp + F.S.hp*F.S.sp*F.S.tm - F.S.hp*F.S.tm + F.S.kp*F.S.tm) (hKb : 0 ≤ F.S.hp*F.S.sp - F.S.hp + F.S.kp) (hnu : 0 < (-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 + (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg)   :
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
  · exact F.vRv_c (by linarith only [hKb]) (by linarith only [hVR]) o2.1 o2.2
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
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.hp_pos hnu, mul_pos ((mul_pos F.S.tp_pos rp)) hga, mul_pos ((mul_pos htp1 rp)) hga, (mul_nonneg (mul_nonneg (htp1).le hKb) (hga).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_4)), mul_pos F.S.hp_pos hnu, (mul_nonneg (mul_nonneg (htp1).le hKb) (hga).le), mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.hp_pos hnu, mul_pos ((mul_pos F.S.tp_pos rp)) hga, mul_pos ((mul_pos htp1 rp)) hga, (mul_nonneg (mul_nonneg (htp1).le hKb) (hga).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hsp1).le (sub_nonneg.2 n0_3), mul_pos F.S.sp_pos hnu, mul_pos hsp1 hnu]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_1)), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos F.S.tp_pos rp)) hal, mul_pos ((mul_pos F.S.tp_pos rp)) hga, (mul_nonneg (mul_nonneg (htp1).le hKb) (hga).le)]


set_option maxHeartbeats 1600000 in
theorem Frame20.om4bn_R_cc {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hA1R : 0 < F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) (hVR : 0 < F.S.hm*F.S.sp*F.S.tp - F.S.hm*F.S.tp + F.S.hp*F.S.sp*F.S.tm - F.S.hp*F.S.tm + F.S.kp*F.S.tm) (hKb : 0 ≤ F.S.hp*F.S.sp - F.S.hp + F.S.kp) (hnu : 0 < (F.S.sm*F.S.sp*F.S.tp - F.S.sm*F.S.tp - F.S.sp*F.S.tp + F.S.tp) * F.a12 + (-F.S.hp*F.S.km*F.S.sp + F.S.hp*F.S.km - F.S.km*F.S.kp) * F.gg)   :
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
  · exact F.vRv_c (by linarith only [hKb]) (by linarith only [hVR]) o2.1 o2.2
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
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos htp1 F.S.kp_pos)) hga, mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(sub_nonneg.2 n0_4), mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n1_4), mul_nonneg (htp1).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.tp_pos htp1)) hga, mul_pos ((mul_pos htp1 htp1)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n1_4), mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n2_4), mul_nonneg (hsp1).le (sub_nonneg.2 n2_4), mul_pos ((mul_pos hsp1 F.S.sm_pos)) hga, mul_pos ((mul_pos F.S.kp_pos F.S.km_pos)) hde]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(sub_nonneg.2 n2_3), mul_pos F.S.sp_pos hnu, mul_pos hsp1 hnu]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_1)), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos F.S.tp_pos rp)) hal, mul_pos ((mul_pos F.S.tp_pos rp)) hga, (mul_nonneg (mul_nonneg (htp1).le hKb) (hga).le)]


set_option maxHeartbeats 1600000 in
theorem Frame20.om4bz1_R_cc {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hA1R : 0 < F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) (hVR : 0 < F.S.hm*F.S.sp*F.S.tp - F.S.hm*F.S.tp + F.S.hp*F.S.sp*F.S.tm - F.S.hp*F.S.tm + F.S.kp*F.S.tm) (hKb : 0 ≤ F.S.hp*F.S.sp - F.S.hp + F.S.kp) (hnu1 : 0 ≤ (-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 + (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg) (hnu2 : 0 ≤ (F.S.sm*F.S.sp*F.S.tp - F.S.sm*F.S.tp - F.S.sp*F.S.tp + F.S.tp) * F.a12 + (-F.S.hp*F.S.km*F.S.sp + F.S.hp*F.S.km - F.S.km*F.S.kp) * F.gg) (hl : 0 < (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * (F.a22 - F.a12) + (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * F.a12 + (-F.S.km*F.S.kp) * F.gg)   :
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
  · exact F.vRv_c (by linarith only [hKb]) (by linarith only [hVR]) o2.1 o2.2
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
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sm_pos hA1r)) hbe, mul_pos ((mul_pos hsm1 hA1r)) hbe, mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hsp1).le (sub_nonneg.2 n0_1), mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n0_2), mul_nonneg (hsp1).le (sub_nonneg.2 n0_4), (sub_nonneg.2 n2_4), mul_pos ((mul_pos F.S.sm_pos hsm1)) hbe, mul_pos ((mul_pos hsm1 hsm1)) hbe, mul_pos ((mul_pos F.S.tp_pos hsp1)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_4)), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_3), (mul_nonneg (mul_nonneg (htp1).le hKb) (hga).le), mul_pos ((mul_pos hsm1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_4), mul_nonneg (F.S.hp_pos).le hnu1, mul_pos ((mul_pos F.S.tp_pos rp)) hga, mul_pos ((mul_pos htp1 rp)) hga, (mul_nonneg (mul_nonneg (htp1).le hKb) (hga).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n2_3), mul_nonneg (hsm1).le (sub_nonneg.2 n2_3), mul_pos F.S.sp_pos hl]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_1)), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos F.S.tp_pos rp)) hal, mul_pos ((mul_pos F.S.tp_pos rp)) hga, (mul_nonneg (mul_nonneg (htp1).le hKb) (hga).le)]


set_option maxHeartbeats 1600000 in
theorem Frame20.om4bz2_R_cc {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x)
    (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (hA1r : 0 < -F.S.km*F.S.sp - F.S.kp*F.S.sm + F.S.kp) (hA1R : 0 < F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) (hVR : 0 < F.S.hm*F.S.sp*F.S.tp - F.S.hm*F.S.tp + F.S.hp*F.S.sp*F.S.tm - F.S.hp*F.S.tm + F.S.kp*F.S.tm) (hKb : 0 ≤ F.S.hp*F.S.sp - F.S.hp + F.S.kp) (hnu1 : 0 ≤ (-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 + (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg) (hnu2 : 0 ≤ (F.S.sm*F.S.sp*F.S.tp - F.S.sm*F.S.tp - F.S.sp*F.S.tp + F.S.tp) * F.a12 + (-F.S.hp*F.S.km*F.S.sp + F.S.hp*F.S.km - F.S.km*F.S.kp) * F.gg) (hl : 0 < (-F.S.sm*F.S.sp + F.S.sm + F.S.sp - 1) * (F.a22 - F.a12) + (-F.S.sm*F.S.sp + F.S.sm + F.S.sp - 1) * F.a12 + (F.S.km*F.S.kp) * F.gg)   :
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
  · exact F.vRv_c (by linarith only [hKb]) (by linarith only [hVR]) o2.1 o2.2
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
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_1)), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos F.S.tp_pos rp)) hal, mul_pos ((mul_pos F.S.tp_pos rp)) hga, (mul_nonneg (mul_nonneg (htp1).le hKb) (hga).le)]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [mul_nonneg (rp).le (sub_nonneg.2 n0_3), mul_nonneg (rp).le (sub_nonneg.2 n1_4), mul_pos rp hl, mul_pos ((mul_pos hsm1 rp)) hbe, mul_pos ((mul_pos htp1 rp)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n0_3)), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_4), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_3), mul_pos F.S.hp_pos hl, (mul_nonneg hKb (hl).le), mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos htm1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos htp1 F.S.kp_pos)) hga]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(sub_nonneg.2 n0_1), mul_pos F.S.tm_pos hl, mul_pos htm1 hl]
  · obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    linarith only [(mul_nonneg hKb (sub_nonneg.2 n0_3)), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_4), (mul_nonneg hKb (hl).le), (mul_nonneg (mul_nonneg (hsm1).le hKb) (hbe).le), (mul_nonneg (mul_nonneg (htp1).le hKb) (hga).le), mul_pos ((mul_pos F.S.sm_pos rp)) hga]



def CaseC20Special' (x : Fin 7 → ℝ³) : Prop :=
  ∃ F : Frame20 x,
    (F.a12 = F.a11) ∨
    (F.a12 = F.a22) ∨
    (-F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm - F.S.kp*F.S.tm = 0) ∨
    (-F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm = 0) ∨
    (F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm = 0) ∨
    (F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp = 0) ∨
    ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.km*F.S.tm) * (F.a11 - F.a12) + (-F.S.hm*F.S.sm + F.S.hm + F.S.km*F.S.tm - F.S.km) * F.a12 = 0) ∨
    ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.hp*F.S.sp) * (F.a22 - F.a12) + (F.S.hp*F.S.sp - F.S.hp - F.S.kp*F.S.tp + F.S.kp) * F.a12 = 0) ∨
    ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) + (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg = 0) ∨
    ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) + (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg = 0) ∨
    ((-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 + (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg = 0 ∧ (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * (F.a22 - F.a12) + (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * F.a12 + (-F.S.km*F.S.kp) * F.gg = 0) ∨
    ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) + (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg = 0) ∨
    ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.hp*F.S.sp) * (F.a22 - F.a12) + (F.S.hp*F.S.sp - F.S.hp - F.S.kp*F.S.tp + F.S.kp) * F.a12 = 0) ∨
    ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) + (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg = 0) ∨
    (F.S.hm*F.S.sp - F.S.hm + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp - F.S.km*F.S.tm + F.S.km + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm = 0) ∨
    ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.hp*F.S.sp) * (F.a22 - F.a12) + (F.S.hp*F.S.sp - F.S.hp - F.S.kp*F.S.tp + F.S.kp) * F.a12 = 0) ∨
    ((-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 + (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg = 0 ∧ (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * (F.a22 - F.a12) + (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * F.a12 + (-F.S.km*F.S.kp) * F.gg = 0) ∨
    (F.S.hm*F.S.sp*F.S.tp - F.S.hm*F.S.tp + F.S.hp*F.S.sp*F.S.tm - F.S.hp*F.S.sp - F.S.hp*F.S.tm + F.S.hp + F.S.kp*F.S.tm - F.S.kp = 0) ∨
    ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.km*F.S.tm) * (F.a11 - F.a12) + (-F.S.hm*F.S.sm + F.S.hm + F.S.km*F.S.tm - F.S.km) * F.a12 = 0)

set_option maxHeartbeats 1600000 in
theorem Frame20.isRupert_of_not_special' {x : Fin 7 → ℝ³} (F : Frame20 x)
    (hx : Function.Injective x) (h : ¬ CaseC20Special' x) :
    IsRupert (Finset.univ.image x) := by
  have hF : ¬ ((F.a12 = F.a11) ∨
    (F.a12 = F.a22) ∨
    (-F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm - F.S.kp*F.S.tm = 0) ∨
    (-F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm = 0) ∨
    (F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm = 0) ∨
    (F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp = 0) ∨
    ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.km*F.S.tm) * (F.a11 - F.a12) + (-F.S.hm*F.S.sm + F.S.hm + F.S.km*F.S.tm - F.S.km) * F.a12 = 0) ∨
    ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.hp*F.S.sp) * (F.a22 - F.a12) + (F.S.hp*F.S.sp - F.S.hp - F.S.kp*F.S.tp + F.S.kp) * F.a12 = 0) ∨
    ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) + (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg = 0) ∨
    ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) + (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg = 0) ∨
    ((-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 + (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg = 0 ∧ (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * (F.a22 - F.a12) + (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * F.a12 + (-F.S.km*F.S.kp) * F.gg = 0) ∨
    ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) + (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg = 0) ∨
    ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.hp*F.S.sp) * (F.a22 - F.a12) + (F.S.hp*F.S.sp - F.S.hp - F.S.kp*F.S.tp + F.S.kp) * F.a12 = 0) ∨
    ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) + (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg = 0) ∨
    (F.S.hm*F.S.sp - F.S.hm + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp - F.S.km*F.S.tm + F.S.km + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm = 0) ∨
    ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.hp*F.S.sp) * (F.a22 - F.a12) + (F.S.hp*F.S.sp - F.S.hp - F.S.kp*F.S.tp + F.S.kp) * F.a12 = 0) ∨
    ((-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 + (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg = 0 ∧ (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * (F.a22 - F.a12) + (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * F.a12 + (-F.S.km*F.S.kp) * F.gg = 0) ∨
    (F.S.hm*F.S.sp*F.S.tp - F.S.hm*F.S.tp + F.S.hp*F.S.sp*F.S.tm - F.S.hp*F.S.sp - F.S.hp*F.S.tm + F.S.hp + F.S.kp*F.S.tm - F.S.kp = 0) ∨
    ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.km*F.S.tm) * (F.a11 - F.a12) + (-F.S.hm*F.S.sm + F.S.hm + F.S.km*F.S.tm - F.S.km) * F.a12 = 0)) := fun hs => h ⟨F, hs⟩
  simp only [not_or] at hF
  obtain ⟨m1, m2, n2, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n20, n21, n22⟩ := hF
  have hα : F.a12 < F.a11 := lt_of_le_of_ne F.A12_le_A11 m1
  have hβ : F.a12 < F.a22 := lt_of_le_of_ne F.A12_le_A22 m2
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  rcases le_or_gt (-F.S.hp*F.S.sp + F.S.hp - F.S.kp) 0 with c1 | c1
  · have c1p : 0 ≤ -(-F.S.hp*F.S.sp + F.S.hp - F.S.kp) := neg_nonneg.2 c1
    rcases lt_or_gt_of_ne n2 with c2 | c2
    · have c2p : 0 < -(-F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm - F.S.kp*F.S.tm) := neg_pos.2 c2
      rcases le_or_gt (-F.S.hm - F.S.km*F.S.tm + F.S.km) 0 with c3 | c3
      · have c3p : 0 ≤ -(-F.S.hm - F.S.km*F.S.tm + F.S.km) := neg_nonneg.2 c3
        rcases lt_or_gt_of_ne n4 with c4 | c4
        · have c4p : 0 < -(-F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) := neg_pos.2 c4
          rcases lt_or_gt_of_ne n5 with c5 | c5
          · have c5p : 0 < -(F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) := neg_pos.2 c5
            rcases lt_or_gt_of_ne n6 with c6 | c6
            · have c6p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c6
              rcases le_or_gt 0 (F.S.tm - F.S.tp) with c7 | c7
              · rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c8 | c8 | c8
                · exact Frame20.om1n F hx hα hβ (by linarith only [c5p]) (by linarith only [c7]) (by linarith only [(neg_pos.2 c8)])
                · rcases lt_or_gt_of_ne (fun hl => n7 ⟨c8, hl⟩) with c9 | c9
                  · exact Frame20.om1z2 F hx hα hβ (by linarith only [c5p]) (by linarith only [c7]) (by linarith only [c8, (neg_pos.2 c9)]) (by linarith only [c8, (neg_pos.2 c9)]) (by linarith only [c8, (neg_pos.2 c9)])
                  · exact Frame20.om1z1 F hx hα hβ (by linarith only [c5p]) (by linarith only [c7]) (by linarith only [c8, c9]) (by linarith only [c8, c9]) (by linarith only [c8, c9])
                · exact Frame20.om1p F hx hα hβ (by linarith only [c5p]) (by linarith only [c7]) (by linarith only [c8])
              · have c7p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c7]
                rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c10 | c10
                · rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c11 | c11 | c11
                  · exact Frame20.om1n_R F hx hα hβ (by linarith only [c6p]) (by linarith only [c10]) (by linarith only [(neg_pos.2 c11)])
                  · rcases lt_or_gt_of_ne (fun hl => n8 ⟨c11, hl⟩) with c12 | c12
                    · exact Frame20.om1z2_R F hx hα hβ (by linarith only [c6p]) (by linarith only [c10]) (by linarith only [c11, (neg_pos.2 c12)]) (by linarith only [c11, (neg_pos.2 c12)]) (by linarith only [c11, (neg_pos.2 c12)])
                    · exact Frame20.om1z1_R F hx hα hβ (by linarith only [c6p]) (by linarith only [c10]) (by linarith only [c11, c12]) (by linarith only [c11, c12]) (by linarith only [c11, c12])
                  · exact Frame20.om1p_R F hx hα hβ (by linarith only [c6p]) (by linarith only [c10]) (by linarith only [c11])
                · have c10p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c10]
                  rcases lt_trichotomy ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) 0 with c13 | c13 | c13
                  · exact Frame20.om4dn_cc F hx hα hβ (by linarith only [c5p]) (by linarith only [c6p]) (by linarith only [c4p]) (by linarith only [c3p]) (by linarith only [(neg_pos.2 c13)])
                  · rcases lt_or_gt_of_ne (fun hl => n9 ⟨c13, hl⟩) with c14 | c14
                    · exact Frame20.om4dz2_cc F hx hα hβ (by linarith only [c5p]) (by linarith only [c6p]) (by linarith only [c4p]) (by linarith only [c3p]) (by linarith only [c13, (neg_pos.2 c14)]) (by linarith only [c13, (neg_pos.2 c14)]) (by linarith only [c13, (neg_pos.2 c14)])
                    · exact Frame20.om4dz1_cc F hx hα hβ (by linarith only [c5p]) (by linarith only [c6p]) (by linarith only [c4p]) (by linarith only [c3p]) (by linarith only [c13, c14]) (by linarith only [c13, c14]) (by linarith only [c13, c14])
                  · exact Frame20.om4dp_cc F hx hα hβ (by linarith only [c5p]) (by linarith only [c6p]) (by linarith only [c4p]) (by linarith only [c3p]) (by linarith only [c13])
            · rcases le_or_gt 0 (F.S.tm - F.S.tp) with c15 | c15
              · rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c16 | c16 | c16
                · exact Frame20.om1n F hx hα hβ (by linarith only [c5p]) (by linarith only [c15]) (by linarith only [(neg_pos.2 c16)])
                · rcases lt_or_gt_of_ne (fun hl => n7 ⟨c16, hl⟩) with c17 | c17
                  · exact Frame20.om1z2 F hx hα hβ (by linarith only [c5p]) (by linarith only [c15]) (by linarith only [c16, (neg_pos.2 c17)]) (by linarith only [c16, (neg_pos.2 c17)]) (by linarith only [c16, (neg_pos.2 c17)])
                  · exact Frame20.om1z1 F hx hα hβ (by linarith only [c5p]) (by linarith only [c15]) (by linarith only [c16, c17]) (by linarith only [c16, c17]) (by linarith only [c16, c17])
                · exact Frame20.om1p F hx hα hβ (by linarith only [c5p]) (by linarith only [c15]) (by linarith only [c16])
              · have c15p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c15]
                rcases lt_trichotomy ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) 0 with c18 | c18 | c18
                · exact Frame20.om4bn_cc F hx hα hβ (by linarith only [c5p]) (by linarith only [c6]) (by linarith only [c4p]) (by linarith only [c3p]) (by linarith only [(neg_pos.2 c18)])
                · rcases lt_or_gt_of_ne (fun hl => n10 ⟨c18, hl⟩) with c19 | c19
                  · exact Frame20.om4bz2_cc F hx hα hβ (by linarith only [c5p]) (by linarith only [c6]) (by linarith only [c4p]) (by linarith only [c3p]) (by linarith only [c18, (neg_pos.2 c19)]) (by linarith only [c18, (neg_pos.2 c19)]) (by linarith only [c18, (neg_pos.2 c19)])
                  · exact Frame20.om4bz1_cc F hx hα hβ (by linarith only [c5p]) (by linarith only [c6]) (by linarith only [c4p]) (by linarith only [c3p]) (by linarith only [c18, c19]) (by linarith only [c18, c19]) (by linarith only [c18, c19])
                · exact Frame20.om4bp_cc F hx hα hβ (by linarith only [c5p]) (by linarith only [c6]) (by linarith only [c4p]) (by linarith only [c3p]) (by linarith only [c18])
          · rcases lt_or_gt_of_ne n6 with c20 | c20
            · have c20p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c20
              rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c21 | c21
              · rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c22 | c22 | c22
                · exact Frame20.om1n_R F hx hα hβ (by linarith only [c20p]) (by linarith only [c21]) (by linarith only [(neg_pos.2 c22)])
                · rcases lt_or_gt_of_ne (fun hl => n8 ⟨c22, hl⟩) with c23 | c23
                  · exact Frame20.om1z2_R F hx hα hβ (by linarith only [c20p]) (by linarith only [c21]) (by linarith only [c22, (neg_pos.2 c23)]) (by linarith only [c22, (neg_pos.2 c23)]) (by linarith only [c22, (neg_pos.2 c23)])
                  · exact Frame20.om1z1_R F hx hα hβ (by linarith only [c20p]) (by linarith only [c21]) (by linarith only [c22, c23]) (by linarith only [c22, c23]) (by linarith only [c22, c23])
                · exact Frame20.om1p_R F hx hα hβ (by linarith only [c20p]) (by linarith only [c21]) (by linarith only [c22])
              · have c21p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c21]
                rcases lt_trichotomy ((-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 + (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg) 0 with c24 | c24 | c24
                · exact Frame20.om4bn_R_cc F hx hα hβ (by linarith only [c20p]) (by linarith only [c5]) (by linarith only [c2p]) (by linarith only [c1p]) (by linarith only [(neg_pos.2 c24)])
                · rcases lt_or_gt_of_ne (fun hl => n11 ⟨c24, hl⟩) with c25 | c25
                  · exact Frame20.om4bz2_R_cc F hx hα hβ (by linarith only [c20p]) (by linarith only [c5]) (by linarith only [c2p]) (by linarith only [c1p]) (by linarith only [c24, (neg_pos.2 c25)]) (by linarith only [c24, (neg_pos.2 c25)]) (by linarith only [c24, (neg_pos.2 c25)])
                  · exact Frame20.om4bz1_R_cc F hx hα hβ (by linarith only [c20p]) (by linarith only [c5]) (by linarith only [c2p]) (by linarith only [c1p]) (by linarith only [c24, c25]) (by linarith only [c24, c25]) (by linarith only [c24, c25])
                · exact Frame20.om4bp_R_cc F hx hα hβ (by linarith only [c20p]) (by linarith only [c5]) (by linarith only [c2p]) (by linarith only [c1p]) (by linarith only [c24])
            · rcases le_or_gt 0 (F.S.hm*F.S.sm*F.S.tp - F.S.hm + F.S.hp*F.S.sm*F.S.tm - F.S.hp*F.S.sm - F.S.km*F.S.tm + F.S.km) with c26 | c26
              · rcases lt_or_ge 0 ((F.S.sm^2 - F.S.sm) * (F.a22 - F.a12) + (F.S.sm^2 - 2*F.S.sm + 1) * F.a12 + (F.S.km^2) * F.gg) with c27 | c27
                · exact Frame20.famA1_R F hx hα hβ (by linarith only [c20]) (by refine pos_of_pos_mul rm ?_; linarith only [(mul_pos F.S.kp_pos rm), (mul_nonneg (c20).le c26), (mul_pos (mul_pos htp1 F.S.km_pos) c4p), (mul_pos (mul_pos hsm1 F.S.hp_pos) c4p)]) (by refine pos_of_pos_mul htm1 ?_; linarith only [(mul_nonneg (hsp1).le c26), (mul_nonneg (mul_nonneg (by first | exact le_of_lt (htp1) | exact (htp1)) (by first | exact le_of_lt (hsp1) | exact (hsp1))) c3p), (mul_nonneg (mul_nonneg (by first | exact le_of_lt (htm1) | exact (htm1)) (by first | exact le_of_lt (hsm1) | exact (hsm1))) c1p), (mul_pos (mul_pos (mul_pos F.S.tp_pos hsp1) hsm1) F.S.hm_pos), (mul_pos (mul_pos (mul_pos htp1 htm1) F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c27])
                · exact Frame20.famA2_R F hx hα hβ (by linarith only [c20]) (by refine pos_of_pos_mul rm ?_; linarith only [(mul_pos F.S.kp_pos rm), (mul_nonneg (c20).le c26), (mul_pos (mul_pos htp1 F.S.km_pos) c4p), (mul_pos (mul_pos hsm1 F.S.hp_pos) c4p)]) (by refine pos_of_pos_mul htm1 ?_; linarith only [(mul_nonneg (hsp1).le c26), (mul_nonneg (mul_nonneg (by first | exact le_of_lt (htp1) | exact (htp1)) (by first | exact le_of_lt (hsp1) | exact (hsp1))) c3p), (mul_nonneg (mul_nonneg (by first | exact le_of_lt (htm1) | exact (htm1)) (by first | exact le_of_lt (hsm1) | exact (hsm1))) c1p), (mul_pos (mul_pos (mul_pos F.S.tp_pos hsp1) hsm1) F.S.hm_pos), (mul_pos (mul_pos (mul_pos htp1 htm1) F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c27])
              · have c26p : 0 < -(F.S.hm*F.S.sm*F.S.tp - F.S.hm + F.S.hp*F.S.sm*F.S.tm - F.S.hp*F.S.sm - F.S.km*F.S.tm + F.S.km) := by linarith only [c26]
                rcases le_or_gt 0 (-F.S.hp*F.S.sp + F.S.hp + F.S.km*F.S.sp*F.S.tp - F.S.km*F.S.tp + F.S.kp*F.S.sm*F.S.tp - F.S.kp) with c28 | c28
                · rcases lt_or_ge 0 ((F.S.tp^2 - F.S.tp) * (F.a11 - F.a12) + (F.S.tp^2 - 2*F.S.tp + 1) * F.a12 + (F.S.hp^2) * F.gg) with c29 | c29
                  · exact Frame20.famA1 F hx hα hβ (by linarith only [c5]) (by refine pos_of_pos_mul rp ?_; linarith only [(mul_nonneg (c5).le c28), (mul_pos (mul_pos htp1 F.S.km_pos) c2p), (mul_pos (mul_pos F.S.sm_pos F.S.hm_pos) rp), (mul_nonneg (mul_nonneg (by first | exact le_of_lt (hsm1) | exact (hsm1)) c1p) (by first | exact le_of_lt (c5) | exact (c5)))]) (by linarith only [c26p]) (by linarith only [c29])
                  · exact Frame20.famA2 F hx hα hβ (by linarith only [c5]) (by refine pos_of_pos_mul rp ?_; linarith only [(mul_nonneg (c5).le c28), (mul_pos (mul_pos htp1 F.S.km_pos) c2p), (mul_pos (mul_pos F.S.sm_pos F.S.hm_pos) rp), (mul_nonneg (mul_nonneg (by first | exact le_of_lt (hsm1) | exact (hsm1)) c1p) (by first | exact le_of_lt (c5) | exact (c5)))]) (by linarith only [c26p]) (by linarith only [c29])
                · have c28p : 0 < -(-F.S.hp*F.S.sp + F.S.hp + F.S.km*F.S.sp*F.S.tp - F.S.km*F.S.tp + F.S.kp*F.S.sm*F.S.tp - F.S.kp) := by linarith only [c28]
                  rcases le_or_gt 0 (-F.S.hm*F.S.sm*F.S.tp - F.S.hp*F.S.sm*F.S.tm + F.S.km*F.S.tm) with c30 | c30
                  · rcases le_or_gt 0 (F.S.hp*F.S.sp - F.S.km*F.S.sp*F.S.tp - F.S.kp*F.S.sm*F.S.tp) with c31 | c31
                    · exact Frame20.famE F hx hα hβ (by linarith only [c5]) (by linarith only [c20]) (by linarith only [c30]) (by linarith only [c31])
                    · have c31p : 0 < -(F.S.hp*F.S.sp - F.S.km*F.S.sp*F.S.tp - F.S.kp*F.S.sm*F.S.tp) := by linarith only [c31]
                      rcases lt_or_ge 0 ((F.S.sm^2 - F.S.sm) * (F.a22 - F.a12) + (F.S.sm^2 - 2*F.S.sm + 1) * F.a12 + (F.S.km^2) * F.gg) with c32 | c32
                      · exact Frame20.famA1_R F hx hα hβ (by linarith only [c20]) (by linarith only [c31p]) (by linarith only [c28p]) (by linarith only [c32])
                      · exact Frame20.famA2_R F hx hα hβ (by linarith only [c20]) (by linarith only [c31p]) (by linarith only [c28p]) (by linarith only [c32])
                  · have c30p : 0 < -(-F.S.hm*F.S.sm*F.S.tp - F.S.hp*F.S.sm*F.S.tm + F.S.km*F.S.tm) := by linarith only [c30]
                    rcases lt_or_ge 0 ((F.S.tp^2 - F.S.tp) * (F.a11 - F.a12) + (F.S.tp^2 - 2*F.S.tp + 1) * F.a12 + (F.S.hp^2) * F.gg) with c33 | c33
                    · exact Frame20.famA1 F hx hα hβ (by linarith only [c5]) (by linarith only [c30p]) (by linarith only [c26p]) (by linarith only [c33])
                    · exact Frame20.famA2 F hx hα hβ (by linarith only [c5]) (by linarith only [c30p]) (by linarith only [c26p]) (by linarith only [c33])
        · rcases lt_or_gt_of_ne n5 with c34 | c34
          · have c34p : 0 < -(F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) := neg_pos.2 c34
            rcases lt_or_gt_of_ne n6 with c35 | c35
            · have c35p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c35
              rcases le_or_gt 0 (F.S.tm - F.S.tp) with c36 | c36
              · rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c37 | c37 | c37
                · exact Frame20.om1n F hx hα hβ (by linarith only [c34p]) (by linarith only [c36]) (by linarith only [(neg_pos.2 c37)])
                · rcases lt_or_gt_of_ne (fun hl => n7 ⟨c37, hl⟩) with c38 | c38
                  · exact Frame20.om1z2 F hx hα hβ (by linarith only [c34p]) (by linarith only [c36]) (by linarith only [c37, (neg_pos.2 c38)]) (by linarith only [c37, (neg_pos.2 c38)]) (by linarith only [c37, (neg_pos.2 c38)])
                  · exact Frame20.om1z1 F hx hα hβ (by linarith only [c34p]) (by linarith only [c36]) (by linarith only [c37, c38]) (by linarith only [c37, c38]) (by linarith only [c37, c38])
                · exact Frame20.om1p F hx hα hβ (by linarith only [c34p]) (by linarith only [c36]) (by linarith only [c37])
              · have c36p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c36]
                rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c39 | c39
                · rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c40 | c40 | c40
                  · exact Frame20.om1n_R F hx hα hβ (by linarith only [c35p]) (by linarith only [c39]) (by linarith only [(neg_pos.2 c40)])
                  · rcases lt_or_gt_of_ne (fun hl => n8 ⟨c40, hl⟩) with c41 | c41
                    · exact Frame20.om1z2_R F hx hα hβ (by linarith only [c35p]) (by linarith only [c39]) (by linarith only [c40, (neg_pos.2 c41)]) (by linarith only [c40, (neg_pos.2 c41)]) (by linarith only [c40, (neg_pos.2 c41)])
                    · exact Frame20.om1z1_R F hx hα hβ (by linarith only [c35p]) (by linarith only [c39]) (by linarith only [c40, c41]) (by linarith only [c40, c41]) (by linarith only [c40, c41])
                  · exact Frame20.om1p_R F hx hα hβ (by linarith only [c35p]) (by linarith only [c39]) (by linarith only [c40])
                · have c39p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c39]
                  rcases lt_trichotomy ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) 0 with c42 | c42 | c42
                  · rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c43 | c43 | c43
                    · exact Frame20.om4cnom_cc F hx hα hβ (by linarith only [c34p]) (by linarith only [c35p]) (by linarith only [c4]) (by linarith only [(mul_nonneg (by first | exact le_of_lt (hsp1) | exact (hsp1)) c3p), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c3p]) (by linarith only [c39p]) (by linarith only [(neg_pos.2 c42), (neg_pos.2 c43)]) (by linarith only [(neg_pos.2 c42), (neg_pos.2 c43)])
                    · rcases lt_or_gt_of_ne (fun hl => n13 ⟨c43, hl⟩) with c44 | c44
                      · exact Frame20.om4cnoz2_cc F hx hα hβ (by linarith only [c34p]) (by linarith only [c35p]) (by linarith only [c4]) (by linarith only [(mul_nonneg (by first | exact le_of_lt (hsp1) | exact (hsp1)) c3p), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c3p]) (by linarith only [c39p]) (by linarith only [(neg_pos.2 c42), c43, (neg_pos.2 c44)]) (by linarith only [(neg_pos.2 c42), c43, (neg_pos.2 c44)]) (by linarith only [(neg_pos.2 c42), c43, (neg_pos.2 c44)]) (by linarith only [(neg_pos.2 c42), c43, (neg_pos.2 c44)])
                      · exact Frame20.om4cnoz1_cc F hx hα hβ (by linarith only [c34p]) (by linarith only [c35p]) (by linarith only [c4]) (by linarith only [(mul_nonneg (by first | exact le_of_lt (hsp1) | exact (hsp1)) c3p), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c3p]) (by linarith only [c39p]) (by linarith only [(neg_pos.2 c42), c43, c44]) (by linarith only [(neg_pos.2 c42), c43, c44]) (by linarith only [(neg_pos.2 c42), c43, c44]) (by linarith only [(neg_pos.2 c42), c43, c44])
                    · exact Frame20.om4cnop_cc F hx hα hβ (by linarith only [c34p]) (by linarith only [c35p]) (by linarith only [c4]) (by linarith only [(mul_nonneg (by first | exact le_of_lt (hsp1) | exact (hsp1)) c3p), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c3p]) (by linarith only [c39p]) (by linarith only [(neg_pos.2 c42), c43]) (by linarith only [(neg_pos.2 c42), c43])
                  · rcases lt_or_gt_of_ne (fun hl => n12 ⟨c42, hl⟩) with c45 | c45
                    · exact Frame20.om4cz2_cc F hx hα hβ (by linarith only [c34p]) (by linarith only [c35p]) (by linarith only [c4]) (by linarith only [(mul_nonneg (by first | exact le_of_lt (hsp1) | exact (hsp1)) c3p), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c3p]) (by linarith only [c39p]) (by linarith only [c42, (neg_pos.2 c45)]) (by linarith only [c42, (neg_pos.2 c45)]) (by linarith only [c42, (neg_pos.2 c45)])
                    · exact Frame20.om4cz1_cc F hx hα hβ (by linarith only [c34p]) (by linarith only [c35p]) (by linarith only [c4]) (by linarith only [(mul_nonneg (by first | exact le_of_lt (hsp1) | exact (hsp1)) c3p), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c3p]) (by linarith only [c39p]) (by linarith only [c42, c45]) (by linarith only [c42, c45]) (by linarith only [c42, c45])
                  · exact Frame20.om4cp_cc F hx hα hβ (by linarith only [c34p]) (by linarith only [c35p]) (by linarith only [c4]) (by linarith only [(mul_nonneg (by first | exact le_of_lt (hsp1) | exact (hsp1)) c3p), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c3p]) (by linarith only [c39p]) (by linarith only [c42])
            · rcases le_or_gt 0 (F.S.tm - F.S.tp) with c46 | c46
              · rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c47 | c47 | c47
                · exact Frame20.om1n F hx hα hβ (by linarith only [c34p]) (by linarith only [c46]) (by linarith only [(neg_pos.2 c47)])
                · rcases lt_or_gt_of_ne (fun hl => n7 ⟨c47, hl⟩) with c48 | c48
                  · exact Frame20.om1z2 F hx hα hβ (by linarith only [c34p]) (by linarith only [c46]) (by linarith only [c47, (neg_pos.2 c48)]) (by linarith only [c47, (neg_pos.2 c48)]) (by linarith only [c47, (neg_pos.2 c48)])
                  · exact Frame20.om1z1 F hx hα hβ (by linarith only [c34p]) (by linarith only [c46]) (by linarith only [c47, c48]) (by linarith only [c47, c48]) (by linarith only [c47, c48])
                · exact Frame20.om1p F hx hα hβ (by linarith only [c34p]) (by linarith only [c46]) (by linarith only [c47])
              · have c46p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c46]
                rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c49 | c49
                · exact Frame20.om2b_R F hx hα hβ (by linarith only [c35]) (by linarith only [c4]) (by linarith only [c3p, c4]) (by linarith only [c49]) (by linarith only [c3p])
                · have c49p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c49]
                  rcases lt_trichotomy ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) 0 with c50 | c50 | c50
                  · exact Frame20.om4an_cc F hx hα hβ (by linarith only [c34p]) (by linarith only [c35]) (by linarith only [c4]) (by linarith only [c3p, c4]) (by linarith only [c3p]) (by linarith only [c49p]) (by linarith only [(neg_pos.2 c50)])
                  · rcases lt_or_gt_of_ne (fun hl => n14 ⟨c50, hl⟩) with c51 | c51
                    · exact Frame20.om4az2_cc F hx hα hβ (by linarith only [c34p]) (by linarith only [c35]) (by linarith only [c4]) (by linarith only [c3p, c4]) (by linarith only [c3p]) (by linarith only [c49p]) (by linarith only [c50, (neg_pos.2 c51)]) (by linarith only [c50, (neg_pos.2 c51)]) (by linarith only [c50, (neg_pos.2 c51)])
                    · exact Frame20.om4az1_cc F hx hα hβ (by linarith only [c34p]) (by linarith only [c35]) (by linarith only [c4]) (by linarith only [c3p, c4]) (by linarith only [c3p]) (by linarith only [c49p]) (by linarith only [c50, c51]) (by linarith only [c50, c51]) (by linarith only [c50, c51])
                  · exact Frame20.om4ap_cc F hx hα hβ (by linarith only [c34p]) (by linarith only [c35]) (by linarith only [c4]) (by linarith only [c3p, c4]) (by linarith only [c3p]) (by linarith only [c49p]) (by linarith only [c50])
          · rcases lt_or_gt_of_ne n6 with c52 | c52
            · have c52p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c52
              rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c53 | c53
              · rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c54 | c54 | c54
                · exact Frame20.om1n_R F hx hα hβ (by linarith only [c52p]) (by linarith only [c53]) (by linarith only [(neg_pos.2 c54)])
                · rcases lt_or_gt_of_ne (fun hl => n8 ⟨c54, hl⟩) with c55 | c55
                  · exact Frame20.om1z2_R F hx hα hβ (by linarith only [c52p]) (by linarith only [c53]) (by linarith only [c54, (neg_pos.2 c55)]) (by linarith only [c54, (neg_pos.2 c55)]) (by linarith only [c54, (neg_pos.2 c55)])
                  · exact Frame20.om1z1_R F hx hα hβ (by linarith only [c52p]) (by linarith only [c53]) (by linarith only [c54, c55]) (by linarith only [c54, c55]) (by linarith only [c54, c55])
                · exact Frame20.om1p_R F hx hα hβ (by linarith only [c52p]) (by linarith only [c53]) (by linarith only [c54])
              · have c53p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c53]
                rcases lt_trichotomy ((-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 + (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg) 0 with c56 | c56 | c56
                · exact Frame20.om4bn_R_cc F hx hα hβ (by linarith only [c52p]) (by linarith only [c34]) (by linarith only [c2p]) (by linarith only [c1p]) (by linarith only [(neg_pos.2 c56)])
                · rcases lt_or_gt_of_ne (fun hl => n11 ⟨c56, hl⟩) with c57 | c57
                  · exact Frame20.om4bz2_R_cc F hx hα hβ (by linarith only [c52p]) (by linarith only [c34]) (by linarith only [c2p]) (by linarith only [c1p]) (by linarith only [c56, (neg_pos.2 c57)]) (by linarith only [c56, (neg_pos.2 c57)]) (by linarith only [c56, (neg_pos.2 c57)])
                  · exact Frame20.om4bz1_R_cc F hx hα hβ (by linarith only [c52p]) (by linarith only [c34]) (by linarith only [c2p]) (by linarith only [c1p]) (by linarith only [c56, c57]) (by linarith only [c56, c57]) (by linarith only [c56, c57])
                · exact Frame20.om4bp_R_cc F hx hα hβ (by linarith only [c52p]) (by linarith only [c34]) (by linarith only [c2p]) (by linarith only [c1p]) (by linarith only [c56])
            · rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c58 | c58
              · exact Frame20.om2b_R F hx hα hβ (by linarith only [c52]) (by linarith only [c4]) (by linarith only [(mul_nonneg (by first | exact le_of_lt (hsp1) | exact (hsp1)) c3p), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c58]) (by linarith only [c3p])
              · have c58p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c58]
                rcases le_or_gt 0 (F.S.hm*F.S.sm*F.S.tp - F.S.hm + F.S.hp*F.S.sm*F.S.tm - F.S.hp*F.S.sm - F.S.km*F.S.tm + F.S.km) with c59 | c59
                · rcases lt_or_ge 0 ((F.S.sm^2 - F.S.sm) * (F.a22 - F.a12) + (F.S.sm^2 - 2*F.S.sm + 1) * F.a12 + (F.S.km^2) * F.gg) with c60 | c60
                  · exact Frame20.famA1_R F hx hα hβ (by linarith only [c52]) (by refine pos_of_pos_mul rm ?_; linarith only [(mul_nonneg (F.S.kp_pos).le c59), (mul_nonneg (c52).le c59), (mul_nonneg (mul_nonneg (by first | exact le_of_lt (htp1) | exact (htp1)) (by first | exact le_of_lt (F.S.kp_pos) | exact (F.S.kp_pos))) c3p), (mul_nonneg (mul_nonneg (by first | exact le_of_lt (htp1) | exact (htp1)) c3p) (by first | exact le_of_lt (c52) | exact (c52))), (mul_nonneg (mul_nonneg (by first | exact le_of_lt (F.S.sp_pos) | exact (F.S.sp_pos)) (by first | exact le_of_lt (F.S.hp_pos) | exact (F.S.hp_pos))) c3p), (mul_pos (mul_pos F.S.sm_pos F.S.hp_pos) c4)]) (by refine pos_of_pos_mul rm ?_; linarith only [(mul_nonneg (mul_nonneg (by first | exact le_of_lt (htp1) | exact (htp1)) (by first | exact le_of_lt (F.S.km_pos) | exact (F.S.km_pos))) c3p), (mul_pos (mul_pos htp1 F.S.km_pos) c4), (mul_nonneg (mul_nonneg (hsp1).le (F.S.km_pos).le) c59), (mul_pos (mul_pos hsm1 rp) rm), (mul_nonneg (mul_nonneg (by first | exact le_of_lt (hsm1) | exact (hsm1)) (by first | exact le_of_lt (rp) | exact (rp))) c3p), (mul_nonneg (mul_nonneg (by first | exact le_of_lt (hsm1) | exact (hsm1)) (by first | exact le_of_lt (rm) | exact (rm))) c1p)]) (by linarith only [c60])
                  · exact Frame20.famA2_R F hx hα hβ (by linarith only [c52]) (by refine pos_of_pos_mul rm ?_; linarith only [(mul_nonneg (F.S.kp_pos).le c59), (mul_nonneg (c52).le c59), (mul_nonneg (mul_nonneg (by first | exact le_of_lt (htp1) | exact (htp1)) (by first | exact le_of_lt (F.S.kp_pos) | exact (F.S.kp_pos))) c3p), (mul_nonneg (mul_nonneg (by first | exact le_of_lt (htp1) | exact (htp1)) c3p) (by first | exact le_of_lt (c52) | exact (c52))), (mul_nonneg (mul_nonneg (by first | exact le_of_lt (F.S.sp_pos) | exact (F.S.sp_pos)) (by first | exact le_of_lt (F.S.hp_pos) | exact (F.S.hp_pos))) c3p), (mul_pos (mul_pos F.S.sm_pos F.S.hp_pos) c4)]) (by refine pos_of_pos_mul rm ?_; linarith only [(mul_nonneg (mul_nonneg (by first | exact le_of_lt (htp1) | exact (htp1)) (by first | exact le_of_lt (F.S.km_pos) | exact (F.S.km_pos))) c3p), (mul_pos (mul_pos htp1 F.S.km_pos) c4), (mul_nonneg (mul_nonneg (hsp1).le (F.S.km_pos).le) c59), (mul_pos (mul_pos hsm1 rp) rm), (mul_nonneg (mul_nonneg (by first | exact le_of_lt (hsm1) | exact (hsm1)) (by first | exact le_of_lt (rp) | exact (rp))) c3p), (mul_nonneg (mul_nonneg (by first | exact le_of_lt (hsm1) | exact (hsm1)) (by first | exact le_of_lt (rm) | exact (rm))) c1p)]) (by linarith only [c60])
                · have c59p : 0 < -(F.S.hm*F.S.sm*F.S.tp - F.S.hm + F.S.hp*F.S.sm*F.S.tm - F.S.hp*F.S.sm - F.S.km*F.S.tm + F.S.km) := by linarith only [c59]
                  rcases le_or_gt 0 (-F.S.hp*F.S.sp + F.S.hp + F.S.km*F.S.sp*F.S.tp - F.S.km*F.S.tp + F.S.kp*F.S.sm*F.S.tp - F.S.kp) with c61 | c61
                  · rcases lt_or_ge 0 ((F.S.tp^2 - F.S.tp) * (F.a11 - F.a12) + (F.S.tp^2 - 2*F.S.tp + 1) * F.a12 + (F.S.hp^2) * F.gg) with c62 | c62
                    · exact Frame20.famA1 F hx hα hβ (by linarith only [c34]) (by refine pos_of_pos_mul rp ?_; linarith only [(mul_nonneg (c34).le c61), (mul_pos (mul_pos htp1 F.S.km_pos) c2p), (mul_pos (mul_pos F.S.sm_pos F.S.hm_pos) rp), (mul_nonneg (mul_nonneg (by first | exact le_of_lt (hsm1) | exact (hsm1)) c1p) (by first | exact le_of_lt (c34) | exact (c34)))]) (by linarith only [c59p]) (by linarith only [c62])
                    · exact Frame20.famA2 F hx hα hβ (by linarith only [c34]) (by refine pos_of_pos_mul rp ?_; linarith only [(mul_nonneg (c34).le c61), (mul_pos (mul_pos htp1 F.S.km_pos) c2p), (mul_pos (mul_pos F.S.sm_pos F.S.hm_pos) rp), (mul_nonneg (mul_nonneg (by first | exact le_of_lt (hsm1) | exact (hsm1)) c1p) (by first | exact le_of_lt (c34) | exact (c34)))]) (by linarith only [c59p]) (by linarith only [c62])
                  · have c61p : 0 < -(-F.S.hp*F.S.sp + F.S.hp + F.S.km*F.S.sp*F.S.tp - F.S.km*F.S.tp + F.S.kp*F.S.sm*F.S.tp - F.S.kp) := by linarith only [c61]
                    rcases le_or_gt 0 (-F.S.hm*F.S.sm*F.S.tp - F.S.hp*F.S.sm*F.S.tm + F.S.km*F.S.tm) with c63 | c63
                    · rcases le_or_gt 0 (F.S.hp*F.S.sp - F.S.km*F.S.sp*F.S.tp - F.S.kp*F.S.sm*F.S.tp) with c64 | c64
                      · exact Frame20.famE F hx hα hβ (by linarith only [c34]) (by linarith only [c52]) (by linarith only [c63]) (by linarith only [c64])
                      · have c64p : 0 < -(F.S.hp*F.S.sp - F.S.km*F.S.sp*F.S.tp - F.S.kp*F.S.sm*F.S.tp) := by linarith only [c64]
                        rcases lt_or_ge 0 ((F.S.sm^2 - F.S.sm) * (F.a22 - F.a12) + (F.S.sm^2 - 2*F.S.sm + 1) * F.a12 + (F.S.km^2) * F.gg) with c65 | c65
                        · exact Frame20.famA1_R F hx hα hβ (by linarith only [c52]) (by linarith only [c64p]) (by linarith only [c61p]) (by linarith only [c65])
                        · exact Frame20.famA2_R F hx hα hβ (by linarith only [c52]) (by linarith only [c64p]) (by linarith only [c61p]) (by linarith only [c65])
                    · have c63p : 0 < -(-F.S.hm*F.S.sm*F.S.tp - F.S.hp*F.S.sm*F.S.tm + F.S.km*F.S.tm) := by linarith only [c63]
                      rcases lt_or_ge 0 ((F.S.tp^2 - F.S.tp) * (F.a11 - F.a12) + (F.S.tp^2 - 2*F.S.tp + 1) * F.a12 + (F.S.hp^2) * F.gg) with c66 | c66
                      · exact Frame20.famA1 F hx hα hβ (by linarith only [c34]) (by linarith only [c63p]) (by linarith only [c59p]) (by linarith only [c66])
                      · exact Frame20.famA2 F hx hα hβ (by linarith only [c34]) (by linarith only [c63p]) (by linarith only [c59p]) (by linarith only [c66])
      · rcases lt_or_gt_of_ne n15 with c67 | c67
        · have c67p : 0 < -(F.S.hm*F.S.sp - F.S.hm + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp - F.S.km*F.S.tm + F.S.km + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) := neg_pos.2 c67
          rcases lt_or_gt_of_ne n5 with c68 | c68
          · have c68p : 0 < -(F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) := neg_pos.2 c68
            rcases lt_or_gt_of_ne n6 with c69 | c69
            · have c69p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c69
              rcases le_or_gt 0 (F.S.tm - F.S.tp) with c70 | c70
              · rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c71 | c71 | c71
                · exact Frame20.om1n F hx hα hβ (by linarith only [c68p]) (by linarith only [c70]) (by linarith only [(neg_pos.2 c71)])
                · rcases lt_or_gt_of_ne (fun hl => n7 ⟨c71, hl⟩) with c72 | c72
                  · exact Frame20.om1z2 F hx hα hβ (by linarith only [c68p]) (by linarith only [c70]) (by linarith only [c71, (neg_pos.2 c72)]) (by linarith only [c71, (neg_pos.2 c72)]) (by linarith only [c71, (neg_pos.2 c72)])
                  · exact Frame20.om1z1 F hx hα hβ (by linarith only [c68p]) (by linarith only [c70]) (by linarith only [c71, c72]) (by linarith only [c71, c72]) (by linarith only [c71, c72])
                · exact Frame20.om1p F hx hα hβ (by linarith only [c68p]) (by linarith only [c70]) (by linarith only [c71])
              · have c70p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c70]
                rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c73 | c73
                · rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c74 | c74 | c74
                  · exact Frame20.om1n_R F hx hα hβ (by linarith only [c69p]) (by linarith only [c73]) (by linarith only [(neg_pos.2 c74)])
                  · rcases lt_or_gt_of_ne (fun hl => n8 ⟨c74, hl⟩) with c75 | c75
                    · exact Frame20.om1z2_R F hx hα hβ (by linarith only [c69p]) (by linarith only [c73]) (by linarith only [c74, (neg_pos.2 c75)]) (by linarith only [c74, (neg_pos.2 c75)]) (by linarith only [c74, (neg_pos.2 c75)])
                    · exact Frame20.om1z1_R F hx hα hβ (by linarith only [c69p]) (by linarith only [c73]) (by linarith only [c74, c75]) (by linarith only [c74, c75]) (by linarith only [c74, c75])
                  · exact Frame20.om1p_R F hx hα hβ (by linarith only [c69p]) (by linarith only [c73]) (by linarith only [c74])
                · have c73p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c73]
                  rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c76 | c76 | c76
                  · exact Frame20.om3n_R F hx hα hβ (by linarith only [c69p]) (by linarith only [c3, c67p]) (by linarith only [c67p]) (by linarith only [c3]) (by linarith only [(neg_pos.2 c76)])
                  · rcases lt_or_gt_of_ne (fun hl => n16 ⟨c76, hl⟩) with c77 | c77
                    · exact Frame20.om3z2_R F hx hα hβ (by linarith only [c69p]) (by linarith only [c3, c67p]) (by linarith only [c67p]) (by linarith only [c3]) (by linarith only [c76, (neg_pos.2 c77)]) (by linarith only [c76, (neg_pos.2 c77)]) (by linarith only [c76, (neg_pos.2 c77)])
                    · exact Frame20.om3z1_R F hx hα hβ (by linarith only [c69p]) (by linarith only [c3, c67p]) (by linarith only [c67p]) (by linarith only [c3]) (by linarith only [c76, c77]) (by linarith only [c76, c77]) (by linarith only [c76, c77])
                  · exact Frame20.om3p_R F hx hα hβ (by linarith only [c69p]) (by linarith only [c3, c67p]) (by linarith only [c67p]) (by linarith only [c3]) (by linarith only [c76])
            · rcases le_or_gt 0 (F.S.tm - F.S.tp) with c78 | c78
              · rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c79 | c79 | c79
                · exact Frame20.om1n F hx hα hβ (by linarith only [c68p]) (by linarith only [c78]) (by linarith only [(neg_pos.2 c79)])
                · rcases lt_or_gt_of_ne (fun hl => n7 ⟨c79, hl⟩) with c80 | c80
                  · exact Frame20.om1z2 F hx hα hβ (by linarith only [c68p]) (by linarith only [c78]) (by linarith only [c79, (neg_pos.2 c80)]) (by linarith only [c79, (neg_pos.2 c80)]) (by linarith only [c79, (neg_pos.2 c80)])
                  · exact Frame20.om1z1 F hx hα hβ (by linarith only [c68p]) (by linarith only [c78]) (by linarith only [c79, c80]) (by linarith only [c79, c80]) (by linarith only [c79, c80])
                · exact Frame20.om1p F hx hα hβ (by linarith only [c68p]) (by linarith only [c78]) (by linarith only [c79])
              · have c78p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c78]
                exact Frame20.om2a_R F hx hα hβ (by linarith only [c69]) (by linarith only [(mul_pos F.S.sp_pos c3), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c67p]) (by linarith only [c3])
          · rcases lt_or_gt_of_ne n6 with c81 | c81
            · have c81p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c81
              rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c82 | c82
              · rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c83 | c83 | c83
                · exact Frame20.om1n_R F hx hα hβ (by linarith only [c81p]) (by linarith only [c82]) (by linarith only [(neg_pos.2 c83)])
                · rcases lt_or_gt_of_ne (fun hl => n8 ⟨c83, hl⟩) with c84 | c84
                  · exact Frame20.om1z2_R F hx hα hβ (by linarith only [c81p]) (by linarith only [c82]) (by linarith only [c83, (neg_pos.2 c84)]) (by linarith only [c83, (neg_pos.2 c84)]) (by linarith only [c83, (neg_pos.2 c84)])
                  · exact Frame20.om1z1_R F hx hα hβ (by linarith only [c81p]) (by linarith only [c82]) (by linarith only [c83, c84]) (by linarith only [c83, c84]) (by linarith only [c83, c84])
                · exact Frame20.om1p_R F hx hα hβ (by linarith only [c81p]) (by linarith only [c82]) (by linarith only [c83])
              · have c82p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c82]
                rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c85 | c85 | c85
                · exact Frame20.om3n_R F hx hα hβ (by linarith only [c81p]) (by linarith only [c3, c67p]) (by linarith only [c67p]) (by linarith only [c3]) (by linarith only [(neg_pos.2 c85)])
                · rcases lt_or_gt_of_ne (fun hl => n16 ⟨c85, hl⟩) with c86 | c86
                  · exact Frame20.om3z2_R F hx hα hβ (by linarith only [c81p]) (by linarith only [c3, c67p]) (by linarith only [c67p]) (by linarith only [c3]) (by linarith only [c85, (neg_pos.2 c86)]) (by linarith only [c85, (neg_pos.2 c86)]) (by linarith only [c85, (neg_pos.2 c86)])
                  · exact Frame20.om3z1_R F hx hα hβ (by linarith only [c81p]) (by linarith only [c3, c67p]) (by linarith only [c67p]) (by linarith only [c3]) (by linarith only [c85, c86]) (by linarith only [c85, c86]) (by linarith only [c85, c86])
                · exact Frame20.om3p_R F hx hα hβ (by linarith only [c81p]) (by linarith only [c3, c67p]) (by linarith only [c67p]) (by linarith only [c3]) (by linarith only [c85])
            · exact Frame20.om2a_R F hx hα hβ (by linarith only [c81]) (by linarith only [(mul_pos F.S.sp_pos c3), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c67p]) (by linarith only [c3])
        · rcases lt_or_ge (-F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.sm*F.S.tm + F.S.hp*F.S.sm - F.S.km*F.S.tm*F.S.tp + F.S.km*F.S.tm + F.S.km*F.S.tp - F.S.km) 0 with c87 | c87
          · have c87p : 0 < -(-F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.sm*F.S.tm + F.S.hp*F.S.sm - F.S.km*F.S.tm*F.S.tp + F.S.km*F.S.tm + F.S.km*F.S.tp - F.S.km) := neg_pos.2 c87
            exact rupert_of_r (F.rFrame.vTri (by simp only [rFrame_S, Shape20.swap]; exact (by linarith only [c3])) (by simp only [rFrame_S, Shape20.swap]; exact (by linarith only [c67])) (by simp only [rFrame_S, Shape20.swap]; exact (by linarith only [c87p])))
          · rcases lt_or_gt_of_ne n6 with c88 | c88
            · have c88p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c88
              rcases le_or_gt (-F.S.hp*F.S.sm + F.S.hp - F.S.km*F.S.tp) 0 with c89 | c89
              · have c89p : 0 ≤ -(-F.S.hp*F.S.sm + F.S.hp - F.S.km*F.S.tp) := neg_nonneg.2 c89
                rcases le_or_gt (F.S.hp*F.S.sp - F.S.hp - F.S.km*F.S.sp*F.S.tp + F.S.km*F.S.tp - F.S.kp*F.S.sm*F.S.tp + F.S.kp) 0 with c90 | c90
                · have c90p : 0 ≤ -(F.S.hp*F.S.sp - F.S.hp - F.S.km*F.S.sp*F.S.tp + F.S.km*F.S.tp - F.S.kp*F.S.sm*F.S.tp + F.S.kp) := neg_nonneg.2 c90
                  exact Frame20.ra4_X_R_cc F hx hα hβ (by linarith only [c3]) (by linarith only [c67]) (by linarith only [c87]) (by linarith only [c88p]) (by linarith only [c89p]) (by linarith only [c90p])
                · exact Frame20.ra4_Y_R_cc F hx hα hβ (by linarith only [c3]) (by linarith only [c67]) (by linarith only [c87]) (by linarith only [c88p]) (by linarith only [c89p]) (by linarith only [c90])
              · exact Frame20.ra4_tBR_R F hx hα hβ (by linarith only [c88p]) (by linarith only [c89])
            · exact Frame20.ra4_A_R_cc F hx hα hβ (by linarith only [c3]) (by linarith only [c67]) (by linarith only [c87]) (by linarith only [c88])
    · rcases le_or_gt (-F.S.hm - F.S.km*F.S.tm + F.S.km) 0 with c91 | c91
      · have c91p : 0 ≤ -(-F.S.hm - F.S.km*F.S.tm + F.S.km) := neg_nonneg.2 c91
        rcases lt_or_gt_of_ne n4 with c92 | c92
        · have c92p : 0 < -(-F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) := neg_pos.2 c92
          rcases lt_or_gt_of_ne n5 with c93 | c93
          · have c93p : 0 < -(F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) := neg_pos.2 c93
            rcases lt_or_gt_of_ne n6 with c94 | c94
            · have c94p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c94
              rcases le_or_gt 0 (F.S.tm - F.S.tp) with c95 | c95
              · rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c96 | c96 | c96
                · exact Frame20.om1n F hx hα hβ (by linarith only [c93p]) (by linarith only [c95]) (by linarith only [(neg_pos.2 c96)])
                · rcases lt_or_gt_of_ne (fun hl => n7 ⟨c96, hl⟩) with c97 | c97
                  · exact Frame20.om1z2 F hx hα hβ (by linarith only [c93p]) (by linarith only [c95]) (by linarith only [c96, (neg_pos.2 c97)]) (by linarith only [c96, (neg_pos.2 c97)]) (by linarith only [c96, (neg_pos.2 c97)])
                  · exact Frame20.om1z1 F hx hα hβ (by linarith only [c93p]) (by linarith only [c95]) (by linarith only [c96, c97]) (by linarith only [c96, c97]) (by linarith only [c96, c97])
                · exact Frame20.om1p F hx hα hβ (by linarith only [c93p]) (by linarith only [c95]) (by linarith only [c96])
              · have c95p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c95]
                rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c98 | c98
                · rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c99 | c99 | c99
                  · exact Frame20.om1n_R F hx hα hβ (by linarith only [c94p]) (by linarith only [c98]) (by linarith only [(neg_pos.2 c99)])
                  · rcases lt_or_gt_of_ne (fun hl => n8 ⟨c99, hl⟩) with c100 | c100
                    · exact Frame20.om1z2_R F hx hα hβ (by linarith only [c94p]) (by linarith only [c98]) (by linarith only [c99, (neg_pos.2 c100)]) (by linarith only [c99, (neg_pos.2 c100)]) (by linarith only [c99, (neg_pos.2 c100)])
                    · exact Frame20.om1z1_R F hx hα hβ (by linarith only [c94p]) (by linarith only [c98]) (by linarith only [c99, c100]) (by linarith only [c99, c100]) (by linarith only [c99, c100])
                  · exact Frame20.om1p_R F hx hα hβ (by linarith only [c94p]) (by linarith only [c98]) (by linarith only [c99])
                · have c98p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c98]
                  rcases lt_trichotomy ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) 0 with c101 | c101 | c101
                  · exact Frame20.om4dn_cc F hx hα hβ (by linarith only [c93p]) (by linarith only [c94p]) (by linarith only [c92p]) (by linarith only [c91p]) (by linarith only [(neg_pos.2 c101)])
                  · rcases lt_or_gt_of_ne (fun hl => n9 ⟨c101, hl⟩) with c102 | c102
                    · exact Frame20.om4dz2_cc F hx hα hβ (by linarith only [c93p]) (by linarith only [c94p]) (by linarith only [c92p]) (by linarith only [c91p]) (by linarith only [c101, (neg_pos.2 c102)]) (by linarith only [c101, (neg_pos.2 c102)]) (by linarith only [c101, (neg_pos.2 c102)])
                    · exact Frame20.om4dz1_cc F hx hα hβ (by linarith only [c93p]) (by linarith only [c94p]) (by linarith only [c92p]) (by linarith only [c91p]) (by linarith only [c101, c102]) (by linarith only [c101, c102]) (by linarith only [c101, c102])
                  · exact Frame20.om4dp_cc F hx hα hβ (by linarith only [c93p]) (by linarith only [c94p]) (by linarith only [c92p]) (by linarith only [c91p]) (by linarith only [c101])
            · rcases le_or_gt 0 (F.S.tm - F.S.tp) with c103 | c103
              · rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c104 | c104 | c104
                · exact Frame20.om1n F hx hα hβ (by linarith only [c93p]) (by linarith only [c103]) (by linarith only [(neg_pos.2 c104)])
                · rcases lt_or_gt_of_ne (fun hl => n7 ⟨c104, hl⟩) with c105 | c105
                  · exact Frame20.om1z2 F hx hα hβ (by linarith only [c93p]) (by linarith only [c103]) (by linarith only [c104, (neg_pos.2 c105)]) (by linarith only [c104, (neg_pos.2 c105)]) (by linarith only [c104, (neg_pos.2 c105)])
                  · exact Frame20.om1z1 F hx hα hβ (by linarith only [c93p]) (by linarith only [c103]) (by linarith only [c104, c105]) (by linarith only [c104, c105]) (by linarith only [c104, c105])
                · exact Frame20.om1p F hx hα hβ (by linarith only [c93p]) (by linarith only [c103]) (by linarith only [c104])
              · have c103p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c103]
                rcases lt_trichotomy ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) 0 with c106 | c106 | c106
                · exact Frame20.om4bn_cc F hx hα hβ (by linarith only [c93p]) (by linarith only [c94]) (by linarith only [c92p]) (by linarith only [c91p]) (by linarith only [(neg_pos.2 c106)])
                · rcases lt_or_gt_of_ne (fun hl => n10 ⟨c106, hl⟩) with c107 | c107
                  · exact Frame20.om4bz2_cc F hx hα hβ (by linarith only [c93p]) (by linarith only [c94]) (by linarith only [c92p]) (by linarith only [c91p]) (by linarith only [c106, (neg_pos.2 c107)]) (by linarith only [c106, (neg_pos.2 c107)]) (by linarith only [c106, (neg_pos.2 c107)])
                  · exact Frame20.om4bz1_cc F hx hα hβ (by linarith only [c93p]) (by linarith only [c94]) (by linarith only [c92p]) (by linarith only [c91p]) (by linarith only [c106, c107]) (by linarith only [c106, c107]) (by linarith only [c106, c107])
                · exact Frame20.om4bp_cc F hx hα hβ (by linarith only [c93p]) (by linarith only [c94]) (by linarith only [c92p]) (by linarith only [c91p]) (by linarith only [c106])
          · rcases lt_or_gt_of_ne n6 with c108 | c108
            · have c108p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c108
              rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c109 | c109
              · rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c110 | c110 | c110
                · exact Frame20.om1n_R F hx hα hβ (by linarith only [c108p]) (by linarith only [c109]) (by linarith only [(neg_pos.2 c110)])
                · rcases lt_or_gt_of_ne (fun hl => n8 ⟨c110, hl⟩) with c111 | c111
                  · exact Frame20.om1z2_R F hx hα hβ (by linarith only [c108p]) (by linarith only [c109]) (by linarith only [c110, (neg_pos.2 c111)]) (by linarith only [c110, (neg_pos.2 c111)]) (by linarith only [c110, (neg_pos.2 c111)])
                  · exact Frame20.om1z1_R F hx hα hβ (by linarith only [c108p]) (by linarith only [c109]) (by linarith only [c110, c111]) (by linarith only [c110, c111]) (by linarith only [c110, c111])
                · exact Frame20.om1p_R F hx hα hβ (by linarith only [c108p]) (by linarith only [c109]) (by linarith only [c110])
              · have c109p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c109]
                rcases le_or_gt 0 (F.S.tm - F.S.tp) with c112 | c112
                · exact Frame20.om2b F hx hα hβ (by linarith only [c93]) (by linarith only [c2]) (by linarith only [c1p, c2]) (by linarith only [c112]) (by linarith only [c1p])
                · have c112p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c112]
                  rcases lt_trichotomy ((-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 + (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg) 0 with c113 | c113 | c113
                  · exact Frame20.om4an_R_cc F hx hα hβ (by linarith only [c108p]) (by linarith only [c93]) (by linarith only [c2]) (by linarith only [(mul_nonneg (by first | exact le_of_lt (htm1) | exact (htm1)) c1p), (mul_pos (mul_pos F.S.tp_pos hsp1) F.S.hm_pos)]) (by linarith only [c1p]) (by linarith only [c112p]) (by linarith only [(neg_pos.2 c113)])
                  · rcases lt_or_gt_of_ne (fun hl => n20 ⟨c113, hl⟩) with c114 | c114
                    · exact Frame20.om4az2_R_cc F hx hα hβ (by linarith only [c108p]) (by linarith only [c93]) (by linarith only [c2]) (by linarith only [(mul_nonneg (by first | exact le_of_lt (htm1) | exact (htm1)) c1p), (mul_pos (mul_pos F.S.tp_pos hsp1) F.S.hm_pos)]) (by linarith only [c1p]) (by linarith only [c112p]) (by linarith only [c113, (neg_pos.2 c114)]) (by linarith only [c113, (neg_pos.2 c114)]) (by linarith only [c113, (neg_pos.2 c114)])
                    · exact Frame20.om4az1_R_cc F hx hα hβ (by linarith only [c108p]) (by linarith only [c93]) (by linarith only [c2]) (by linarith only [(mul_nonneg (by first | exact le_of_lt (htm1) | exact (htm1)) c1p), (mul_pos (mul_pos F.S.tp_pos hsp1) F.S.hm_pos)]) (by linarith only [c1p]) (by linarith only [c112p]) (by linarith only [c113, c114]) (by linarith only [c113, c114]) (by linarith only [c113, c114])
                  · exact Frame20.om4ap_R_cc F hx hα hβ (by linarith only [c108p]) (by linarith only [c93]) (by linarith only [c2]) (by linarith only [(mul_nonneg (by first | exact le_of_lt (htm1) | exact (htm1)) c1p), (mul_pos (mul_pos F.S.tp_pos hsp1) F.S.hm_pos)]) (by linarith only [c1p]) (by linarith only [c112p]) (by linarith only [c113])
            · rcases le_or_gt 0 (F.S.tm - F.S.tp) with c115 | c115
              · exact Frame20.om2b F hx hα hβ (by linarith only [c93]) (by linarith only [c2]) (by linarith only [c1p, c2]) (by linarith only [c115]) (by linarith only [c1p])
              · have c115p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c115]
                rcases le_or_gt 0 (F.S.hm*F.S.sm*F.S.tp - F.S.hm + F.S.hp*F.S.sm*F.S.tm - F.S.hp*F.S.sm - F.S.km*F.S.tm + F.S.km) with c116 | c116
                · rcases lt_or_ge 0 ((F.S.sm^2 - F.S.sm) * (F.a22 - F.a12) + (F.S.sm^2 - 2*F.S.sm + 1) * F.a12 + (F.S.km^2) * F.gg) with c117 | c117
                  · exact Frame20.famA1_R F hx hα hβ (by linarith only [c108]) (by refine pos_of_pos_mul rm ?_; linarith only [(mul_pos F.S.kp_pos rm), (mul_nonneg (c108).le c116), (mul_pos (mul_pos htp1 F.S.km_pos) c92p), (mul_pos (mul_pos hsm1 F.S.hp_pos) c92p)]) (by refine pos_of_pos_mul htm1 ?_; linarith only [(mul_nonneg (by first | exact le_of_lt (htp1) | exact (htp1)) c1p), (mul_pos htp1 c2), (mul_nonneg (mul_nonneg (F.S.tp_pos).le (hsp1).le) c116), (mul_nonneg (mul_nonneg (by first | exact le_of_lt (F.S.tp_pos) | exact (F.S.tp_pos)) (by first | exact le_of_lt (hsm1) | exact (hsm1))) c1p), (mul_pos (mul_pos F.S.tp_pos hsm1) c2)]) (by linarith only [c117])
                  · exact Frame20.famA2_R F hx hα hβ (by linarith only [c108]) (by refine pos_of_pos_mul rm ?_; linarith only [(mul_pos F.S.kp_pos rm), (mul_nonneg (c108).le c116), (mul_pos (mul_pos htp1 F.S.km_pos) c92p), (mul_pos (mul_pos hsm1 F.S.hp_pos) c92p)]) (by refine pos_of_pos_mul htm1 ?_; linarith only [(mul_nonneg (by first | exact le_of_lt (htp1) | exact (htp1)) c1p), (mul_pos htp1 c2), (mul_nonneg (mul_nonneg (F.S.tp_pos).le (hsp1).le) c116), (mul_nonneg (mul_nonneg (by first | exact le_of_lt (F.S.tp_pos) | exact (F.S.tp_pos)) (by first | exact le_of_lt (hsm1) | exact (hsm1))) c1p), (mul_pos (mul_pos F.S.tp_pos hsm1) c2)]) (by linarith only [c117])
                · have c116p : 0 < -(F.S.hm*F.S.sm*F.S.tp - F.S.hm + F.S.hp*F.S.sm*F.S.tm - F.S.hp*F.S.sm - F.S.km*F.S.tm + F.S.km) := by linarith only [c116]
                  rcases le_or_gt 0 (-F.S.hp*F.S.sp + F.S.hp + F.S.km*F.S.sp*F.S.tp - F.S.km*F.S.tp + F.S.kp*F.S.sm*F.S.tp - F.S.kp) with c118 | c118
                  · rcases lt_or_ge 0 ((F.S.tp^2 - F.S.tp) * (F.a11 - F.a12) + (F.S.tp^2 - 2*F.S.tp + 1) * F.a12 + (F.S.hp^2) * F.gg) with c119 | c119
                    · exact Frame20.famA1 F hx hα hβ (by linarith only [c93]) (by refine pos_of_pos_mul rp ?_; linarith only [(mul_nonneg (F.S.hm_pos).le c118), (mul_nonneg (c93).le c118), (mul_pos (mul_pos F.S.tp_pos F.S.km_pos) c2), (mul_nonneg (mul_nonneg (by first | exact le_of_lt (F.S.tm_pos) | exact (F.S.tm_pos)) (by first | exact le_of_lt (F.S.km_pos) | exact (F.S.km_pos))) c1p), (mul_nonneg (mul_nonneg (by first | exact le_of_lt (hsm1) | exact (hsm1)) (by first | exact le_of_lt (F.S.hm_pos) | exact (F.S.hm_pos))) c1p), (mul_nonneg (mul_nonneg (by first | exact le_of_lt (hsm1) | exact (hsm1)) c1p) (by first | exact le_of_lt (c93) | exact (c93)))]) (by linarith only [c116p]) (by linarith only [c119])
                    · exact Frame20.famA2 F hx hα hβ (by linarith only [c93]) (by refine pos_of_pos_mul rp ?_; linarith only [(mul_nonneg (F.S.hm_pos).le c118), (mul_nonneg (c93).le c118), (mul_pos (mul_pos F.S.tp_pos F.S.km_pos) c2), (mul_nonneg (mul_nonneg (by first | exact le_of_lt (F.S.tm_pos) | exact (F.S.tm_pos)) (by first | exact le_of_lt (F.S.km_pos) | exact (F.S.km_pos))) c1p), (mul_nonneg (mul_nonneg (by first | exact le_of_lt (hsm1) | exact (hsm1)) (by first | exact le_of_lt (F.S.hm_pos) | exact (F.S.hm_pos))) c1p), (mul_nonneg (mul_nonneg (by first | exact le_of_lt (hsm1) | exact (hsm1)) c1p) (by first | exact le_of_lt (c93) | exact (c93)))]) (by linarith only [c116p]) (by linarith only [c119])
                  · have c118p : 0 < -(-F.S.hp*F.S.sp + F.S.hp + F.S.km*F.S.sp*F.S.tp - F.S.km*F.S.tp + F.S.kp*F.S.sm*F.S.tp - F.S.kp) := by linarith only [c118]
                    rcases le_or_gt 0 (-F.S.hm*F.S.sm*F.S.tp - F.S.hp*F.S.sm*F.S.tm + F.S.km*F.S.tm) with c120 | c120
                    · rcases le_or_gt 0 (F.S.hp*F.S.sp - F.S.km*F.S.sp*F.S.tp - F.S.kp*F.S.sm*F.S.tp) with c121 | c121
                      · exact Frame20.famE F hx hα hβ (by linarith only [c93]) (by linarith only [c108]) (by linarith only [c120]) (by linarith only [c121])
                      · have c121p : 0 < -(F.S.hp*F.S.sp - F.S.km*F.S.sp*F.S.tp - F.S.kp*F.S.sm*F.S.tp) := by linarith only [c121]
                        rcases lt_or_ge 0 ((F.S.sm^2 - F.S.sm) * (F.a22 - F.a12) + (F.S.sm^2 - 2*F.S.sm + 1) * F.a12 + (F.S.km^2) * F.gg) with c122 | c122
                        · exact Frame20.famA1_R F hx hα hβ (by linarith only [c108]) (by linarith only [c121p]) (by linarith only [c118p]) (by linarith only [c122])
                        · exact Frame20.famA2_R F hx hα hβ (by linarith only [c108]) (by linarith only [c121p]) (by linarith only [c118p]) (by linarith only [c122])
                    · have c120p : 0 < -(-F.S.hm*F.S.sm*F.S.tp - F.S.hp*F.S.sm*F.S.tm + F.S.km*F.S.tm) := by linarith only [c120]
                      rcases lt_or_ge 0 ((F.S.tp^2 - F.S.tp) * (F.a11 - F.a12) + (F.S.tp^2 - 2*F.S.tp + 1) * F.a12 + (F.S.hp^2) * F.gg) with c123 | c123
                      · exact Frame20.famA1 F hx hα hβ (by linarith only [c93]) (by linarith only [c120p]) (by linarith only [c116p]) (by linarith only [c123])
                      · exact Frame20.famA2 F hx hα hβ (by linarith only [c93]) (by linarith only [c120p]) (by linarith only [c116p]) (by linarith only [c123])
        · rcases lt_or_gt_of_ne n5 with c124 | c124
          · have c124p : 0 < -(F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) := neg_pos.2 c124
            rcases lt_or_gt_of_ne n6 with c125 | c125
            · have c125p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c125
              rcases le_or_gt 0 (F.S.tm - F.S.tp) with c126 | c126
              · rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c127 | c127 | c127
                · exact Frame20.om1n F hx hα hβ (by linarith only [c124p]) (by linarith only [c126]) (by linarith only [(neg_pos.2 c127)])
                · rcases lt_or_gt_of_ne (fun hl => n7 ⟨c127, hl⟩) with c128 | c128
                  · exact Frame20.om1z2 F hx hα hβ (by linarith only [c124p]) (by linarith only [c126]) (by linarith only [c127, (neg_pos.2 c128)]) (by linarith only [c127, (neg_pos.2 c128)]) (by linarith only [c127, (neg_pos.2 c128)])
                  · exact Frame20.om1z1 F hx hα hβ (by linarith only [c124p]) (by linarith only [c126]) (by linarith only [c127, c128]) (by linarith only [c127, c128]) (by linarith only [c127, c128])
                · exact Frame20.om1p F hx hα hβ (by linarith only [c124p]) (by linarith only [c126]) (by linarith only [c127])
              · have c126p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c126]
                rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c129 | c129
                · rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c130 | c130 | c130
                  · exact Frame20.om1n_R F hx hα hβ (by linarith only [c125p]) (by linarith only [c129]) (by linarith only [(neg_pos.2 c130)])
                  · rcases lt_or_gt_of_ne (fun hl => n8 ⟨c130, hl⟩) with c131 | c131
                    · exact Frame20.om1z2_R F hx hα hβ (by linarith only [c125p]) (by linarith only [c129]) (by linarith only [c130, (neg_pos.2 c131)]) (by linarith only [c130, (neg_pos.2 c131)]) (by linarith only [c130, (neg_pos.2 c131)])
                    · exact Frame20.om1z1_R F hx hα hβ (by linarith only [c125p]) (by linarith only [c129]) (by linarith only [c130, c131]) (by linarith only [c130, c131]) (by linarith only [c130, c131])
                  · exact Frame20.om1p_R F hx hα hβ (by linarith only [c125p]) (by linarith only [c129]) (by linarith only [c130])
                · have c129p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c129]
                  rcases lt_trichotomy ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) 0 with c132 | c132 | c132
                  · rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c133 | c133 | c133
                    · exact Frame20.om4cnom_cc F hx hα hβ (by linarith only [c124p]) (by linarith only [c125p]) (by linarith only [c92]) (by linarith only [c91p, c92]) (by linarith only [c91p]) (by linarith only [c129p]) (by linarith only [(neg_pos.2 c132), (neg_pos.2 c133)]) (by linarith only [(neg_pos.2 c132), (neg_pos.2 c133)])
                    · rcases lt_or_gt_of_ne (fun hl => n13 ⟨c133, hl⟩) with c134 | c134
                      · exact Frame20.om4cnoz2_cc F hx hα hβ (by linarith only [c124p]) (by linarith only [c125p]) (by linarith only [c92]) (by linarith only [c91p, c92]) (by linarith only [c91p]) (by linarith only [c129p]) (by linarith only [(neg_pos.2 c132), c133, (neg_pos.2 c134)]) (by linarith only [(neg_pos.2 c132), c133, (neg_pos.2 c134)]) (by linarith only [(neg_pos.2 c132), c133, (neg_pos.2 c134)]) (by linarith only [(neg_pos.2 c132), c133, (neg_pos.2 c134)])
                      · exact Frame20.om4cnoz1_cc F hx hα hβ (by linarith only [c124p]) (by linarith only [c125p]) (by linarith only [c92]) (by linarith only [c91p, c92]) (by linarith only [c91p]) (by linarith only [c129p]) (by linarith only [(neg_pos.2 c132), c133, c134]) (by linarith only [(neg_pos.2 c132), c133, c134]) (by linarith only [(neg_pos.2 c132), c133, c134]) (by linarith only [(neg_pos.2 c132), c133, c134])
                    · exact Frame20.om4cnop_cc F hx hα hβ (by linarith only [c124p]) (by linarith only [c125p]) (by linarith only [c92]) (by linarith only [c91p, c92]) (by linarith only [c91p]) (by linarith only [c129p]) (by linarith only [(neg_pos.2 c132), c133]) (by linarith only [(neg_pos.2 c132), c133])
                  · rcases lt_or_gt_of_ne (fun hl => n12 ⟨c132, hl⟩) with c135 | c135
                    · exact Frame20.om4cz2_cc F hx hα hβ (by linarith only [c124p]) (by linarith only [c125p]) (by linarith only [c92]) (by linarith only [c91p, c92]) (by linarith only [c91p]) (by linarith only [c129p]) (by linarith only [c132, (neg_pos.2 c135)]) (by linarith only [c132, (neg_pos.2 c135)]) (by linarith only [c132, (neg_pos.2 c135)])
                    · exact Frame20.om4cz1_cc F hx hα hβ (by linarith only [c124p]) (by linarith only [c125p]) (by linarith only [c92]) (by linarith only [c91p, c92]) (by linarith only [c91p]) (by linarith only [c129p]) (by linarith only [c132, c135]) (by linarith only [c132, c135]) (by linarith only [c132, c135])
                  · exact Frame20.om4cp_cc F hx hα hβ (by linarith only [c124p]) (by linarith only [c125p]) (by linarith only [c92]) (by linarith only [c91p, c92]) (by linarith only [c91p]) (by linarith only [c129p]) (by linarith only [c132])
            · rcases le_or_gt 0 (F.S.tm - F.S.tp) with c136 | c136
              · rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c137 | c137 | c137
                · exact Frame20.om1n F hx hα hβ (by linarith only [c124p]) (by linarith only [c136]) (by linarith only [(neg_pos.2 c137)])
                · rcases lt_or_gt_of_ne (fun hl => n7 ⟨c137, hl⟩) with c138 | c138
                  · exact Frame20.om1z2 F hx hα hβ (by linarith only [c124p]) (by linarith only [c136]) (by linarith only [c137, (neg_pos.2 c138)]) (by linarith only [c137, (neg_pos.2 c138)]) (by linarith only [c137, (neg_pos.2 c138)])
                  · exact Frame20.om1z1 F hx hα hβ (by linarith only [c124p]) (by linarith only [c136]) (by linarith only [c137, c138]) (by linarith only [c137, c138]) (by linarith only [c137, c138])
                · exact Frame20.om1p F hx hα hβ (by linarith only [c124p]) (by linarith only [c136]) (by linarith only [c137])
              · have c136p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c136]
                rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c139 | c139
                · exact Frame20.om2b_R F hx hα hβ (by linarith only [c125]) (by linarith only [c92]) (by linarith only [(mul_nonneg (by first | exact le_of_lt (hsp1) | exact (hsp1)) c91p), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c139]) (by linarith only [c91p])
                · have c139p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c139]
                  rcases lt_trichotomy ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) 0 with c140 | c140 | c140
                  · exact Frame20.om4an_cc F hx hα hβ (by linarith only [c124p]) (by linarith only [c125]) (by linarith only [c92]) (by linarith only [c91p, c92]) (by linarith only [c91p]) (by linarith only [c139p]) (by linarith only [(neg_pos.2 c140)])
                  · rcases lt_or_gt_of_ne (fun hl => n14 ⟨c140, hl⟩) with c141 | c141
                    · exact Frame20.om4az2_cc F hx hα hβ (by linarith only [c124p]) (by linarith only [c125]) (by linarith only [c92]) (by linarith only [c91p, c92]) (by linarith only [c91p]) (by linarith only [c139p]) (by linarith only [c140, (neg_pos.2 c141)]) (by linarith only [c140, (neg_pos.2 c141)]) (by linarith only [c140, (neg_pos.2 c141)])
                    · exact Frame20.om4az1_cc F hx hα hβ (by linarith only [c124p]) (by linarith only [c125]) (by linarith only [c92]) (by linarith only [c91p, c92]) (by linarith only [c91p]) (by linarith only [c139p]) (by linarith only [c140, c141]) (by linarith only [c140, c141]) (by linarith only [c140, c141])
                  · exact Frame20.om4ap_cc F hx hα hβ (by linarith only [c124p]) (by linarith only [c125]) (by linarith only [c92]) (by linarith only [c91p, c92]) (by linarith only [c91p]) (by linarith only [c139p]) (by linarith only [c140])
          · rcases lt_or_gt_of_ne n6 with c142 | c142
            · have c142p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c142
              rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c143 | c143
              · rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c144 | c144 | c144
                · exact Frame20.om1n_R F hx hα hβ (by linarith only [c142p]) (by linarith only [c143]) (by linarith only [(neg_pos.2 c144)])
                · rcases lt_or_gt_of_ne (fun hl => n8 ⟨c144, hl⟩) with c145 | c145
                  · exact Frame20.om1z2_R F hx hα hβ (by linarith only [c142p]) (by linarith only [c143]) (by linarith only [c144, (neg_pos.2 c145)]) (by linarith only [c144, (neg_pos.2 c145)]) (by linarith only [c144, (neg_pos.2 c145)])
                  · exact Frame20.om1z1_R F hx hα hβ (by linarith only [c142p]) (by linarith only [c143]) (by linarith only [c144, c145]) (by linarith only [c144, c145]) (by linarith only [c144, c145])
                · exact Frame20.om1p_R F hx hα hβ (by linarith only [c142p]) (by linarith only [c143]) (by linarith only [c144])
              · have c143p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c143]
                rcases le_or_gt 0 (F.S.tm - F.S.tp) with c146 | c146
                · exact Frame20.om2b F hx hα hβ (by linarith only [c124]) (by linarith only [c2]) (by linarith only [(mul_nonneg (by first | exact le_of_lt (htm1) | exact (htm1)) c1p), (mul_pos (mul_pos F.S.tp_pos hsp1) F.S.hm_pos)]) (by linarith only [c146]) (by linarith only [c1p])
                · have c146p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c146]
                  rcases lt_trichotomy ((-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 + (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg) 0 with c147 | c147 | c147
                  · exact Frame20.om4an_R_cc F hx hα hβ (by linarith only [c142p]) (by linarith only [c124]) (by linarith only [c2]) (by linarith only [c1p, c2]) (by linarith only [c1p]) (by linarith only [c146p]) (by linarith only [(neg_pos.2 c147)])
                  · rcases lt_or_gt_of_ne (fun hl => n20 ⟨c147, hl⟩) with c148 | c148
                    · exact Frame20.om4az2_R_cc F hx hα hβ (by linarith only [c142p]) (by linarith only [c124]) (by linarith only [c2]) (by linarith only [c1p, c2]) (by linarith only [c1p]) (by linarith only [c146p]) (by linarith only [c147, (neg_pos.2 c148)]) (by linarith only [c147, (neg_pos.2 c148)]) (by linarith only [c147, (neg_pos.2 c148)])
                    · exact Frame20.om4az1_R_cc F hx hα hβ (by linarith only [c142p]) (by linarith only [c124]) (by linarith only [c2]) (by linarith only [c1p, c2]) (by linarith only [c1p]) (by linarith only [c146p]) (by linarith only [c147, c148]) (by linarith only [c147, c148]) (by linarith only [c147, c148])
                  · exact Frame20.om4ap_R_cc F hx hα hβ (by linarith only [c142p]) (by linarith only [c124]) (by linarith only [c2]) (by linarith only [c1p, c2]) (by linarith only [c1p]) (by linarith only [c146p]) (by linarith only [c147])
            · rcases le_or_gt 0 (F.S.tm - F.S.tp) with c149 | c149
              · exact Frame20.om2b F hx hα hβ (by linarith only [c124]) (by linarith only [c2]) (by linarith only [c1p, c2]) (by linarith only [c149]) (by linarith only [c1p])
              · have c149p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c149]
                rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c150 | c150
                · exact Frame20.om2b_R F hx hα hβ (by linarith only [c142]) (by linarith only [c92]) (by linarith only [(mul_nonneg (by first | exact le_of_lt (hsp1) | exact (hsp1)) c91p), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c150]) (by linarith only [c91p])
                · have c150p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c150]
                  rcases le_or_gt 0 (F.S.hm*F.S.sm*F.S.tp - F.S.hm + F.S.hp*F.S.sm*F.S.tm - F.S.hp*F.S.sm - F.S.km*F.S.tm + F.S.km) with c151 | c151
                  · rcases lt_or_ge 0 ((F.S.sm^2 - F.S.sm) * (F.a22 - F.a12) + (F.S.sm^2 - 2*F.S.sm + 1) * F.a12 + (F.S.km^2) * F.gg) with c152 | c152
                    · exact Frame20.famA1_R F hx hα hβ (by linarith only [c142]) (by refine pos_of_pos_mul rm ?_; linarith only [(mul_nonneg (mul_nonneg (by first | exact le_of_lt (htp1) | exact (htp1)) (by first | exact le_of_lt (F.S.kp_pos) | exact (F.S.kp_pos))) c91p), (mul_nonneg (mul_nonneg (by first | exact le_of_lt (htp1) | exact (htp1)) c91p) (by first | exact le_of_lt (c142) | exact (c142))), (mul_nonneg (mul_nonneg (by first | exact le_of_lt (F.S.sp_pos) | exact (F.S.sp_pos)) (by first | exact le_of_lt (F.S.hp_pos) | exact (F.S.hp_pos))) c91p), (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.km_pos).le) c151), (mul_pos (mul_pos F.S.sm_pos F.S.hp_pos) c92), (mul_nonneg (mul_nonneg (F.S.sm_pos).le (F.S.kp_pos).le) c151)]) (by refine pos_of_pos_mul htm1 ?_; linarith only [(mul_nonneg (by first | exact le_of_lt (htp1) | exact (htp1)) c1p), (mul_pos hsm1 c2), (mul_nonneg (mul_nonneg (F.S.tp_pos).le (hsp1).le) c151), (mul_nonneg (mul_nonneg (by first | exact le_of_lt (F.S.tp_pos) | exact (F.S.tp_pos)) (by first | exact le_of_lt (hsm1) | exact (hsm1))) c1p), (mul_pos (mul_pos htp1 F.S.sm_pos) c2)]) (by linarith only [c152])
                    · exact Frame20.famA2_R F hx hα hβ (by linarith only [c142]) (by refine pos_of_pos_mul rm ?_; linarith only [(mul_nonneg (mul_nonneg (by first | exact le_of_lt (htp1) | exact (htp1)) (by first | exact le_of_lt (F.S.kp_pos) | exact (F.S.kp_pos))) c91p), (mul_nonneg (mul_nonneg (by first | exact le_of_lt (htp1) | exact (htp1)) c91p) (by first | exact le_of_lt (c142) | exact (c142))), (mul_nonneg (mul_nonneg (by first | exact le_of_lt (F.S.sp_pos) | exact (F.S.sp_pos)) (by first | exact le_of_lt (F.S.hp_pos) | exact (F.S.hp_pos))) c91p), (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.km_pos).le) c151), (mul_pos (mul_pos F.S.sm_pos F.S.hp_pos) c92), (mul_nonneg (mul_nonneg (F.S.sm_pos).le (F.S.kp_pos).le) c151)]) (by refine pos_of_pos_mul htm1 ?_; linarith only [(mul_nonneg (by first | exact le_of_lt (htp1) | exact (htp1)) c1p), (mul_pos hsm1 c2), (mul_nonneg (mul_nonneg (F.S.tp_pos).le (hsp1).le) c151), (mul_nonneg (mul_nonneg (by first | exact le_of_lt (F.S.tp_pos) | exact (F.S.tp_pos)) (by first | exact le_of_lt (hsm1) | exact (hsm1))) c1p), (mul_pos (mul_pos htp1 F.S.sm_pos) c2)]) (by linarith only [c152])
                  · have c151p : 0 < -(F.S.hm*F.S.sm*F.S.tp - F.S.hm + F.S.hp*F.S.sm*F.S.tm - F.S.hp*F.S.sm - F.S.km*F.S.tm + F.S.km) := by linarith only [c151]
                    rcases le_or_gt 0 (-F.S.hp*F.S.sp + F.S.hp + F.S.km*F.S.sp*F.S.tp - F.S.km*F.S.tp + F.S.kp*F.S.sm*F.S.tp - F.S.kp) with c153 | c153
                    · rcases lt_or_ge 0 ((F.S.tp^2 - F.S.tp) * (F.a11 - F.a12) + (F.S.tp^2 - 2*F.S.tp + 1) * F.a12 + (F.S.hp^2) * F.gg) with c154 | c154
                      · exact Frame20.famA1 F hx hα hβ (by linarith only [c124]) (by refine pos_of_pos_mul rp ?_; linarith only [(mul_nonneg (F.S.hm_pos).le c153), (mul_nonneg (c124).le c153), (mul_pos (mul_pos F.S.tp_pos F.S.km_pos) c2), (mul_nonneg (mul_nonneg (by first | exact le_of_lt (F.S.tm_pos) | exact (F.S.tm_pos)) (by first | exact le_of_lt (F.S.km_pos) | exact (F.S.km_pos))) c1p), (mul_nonneg (mul_nonneg (by first | exact le_of_lt (hsm1) | exact (hsm1)) (by first | exact le_of_lt (F.S.hm_pos) | exact (F.S.hm_pos))) c1p), (mul_nonneg (mul_nonneg (by first | exact le_of_lt (hsm1) | exact (hsm1)) c1p) (by first | exact le_of_lt (c124) | exact (c124)))]) (by linarith only [c151p]) (by linarith only [c154])
                      · exact Frame20.famA2 F hx hα hβ (by linarith only [c124]) (by refine pos_of_pos_mul rp ?_; linarith only [(mul_nonneg (F.S.hm_pos).le c153), (mul_nonneg (c124).le c153), (mul_pos (mul_pos F.S.tp_pos F.S.km_pos) c2), (mul_nonneg (mul_nonneg (by first | exact le_of_lt (F.S.tm_pos) | exact (F.S.tm_pos)) (by first | exact le_of_lt (F.S.km_pos) | exact (F.S.km_pos))) c1p), (mul_nonneg (mul_nonneg (by first | exact le_of_lt (hsm1) | exact (hsm1)) (by first | exact le_of_lt (F.S.hm_pos) | exact (F.S.hm_pos))) c1p), (mul_nonneg (mul_nonneg (by first | exact le_of_lt (hsm1) | exact (hsm1)) c1p) (by first | exact le_of_lt (c124) | exact (c124)))]) (by linarith only [c151p]) (by linarith only [c154])
                    · have c153p : 0 < -(-F.S.hp*F.S.sp + F.S.hp + F.S.km*F.S.sp*F.S.tp - F.S.km*F.S.tp + F.S.kp*F.S.sm*F.S.tp - F.S.kp) := by linarith only [c153]
                      rcases le_or_gt 0 (-F.S.hm*F.S.sm*F.S.tp - F.S.hp*F.S.sm*F.S.tm + F.S.km*F.S.tm) with c155 | c155
                      · rcases le_or_gt 0 (F.S.hp*F.S.sp - F.S.km*F.S.sp*F.S.tp - F.S.kp*F.S.sm*F.S.tp) with c156 | c156
                        · exact Frame20.famE F hx hα hβ (by linarith only [c124]) (by linarith only [c142]) (by linarith only [c155]) (by linarith only [c156])
                        · have c156p : 0 < -(F.S.hp*F.S.sp - F.S.km*F.S.sp*F.S.tp - F.S.kp*F.S.sm*F.S.tp) := by linarith only [c156]
                          rcases lt_or_ge 0 ((F.S.sm^2 - F.S.sm) * (F.a22 - F.a12) + (F.S.sm^2 - 2*F.S.sm + 1) * F.a12 + (F.S.km^2) * F.gg) with c157 | c157
                          · exact Frame20.famA1_R F hx hα hβ (by linarith only [c142]) (by linarith only [c156p]) (by linarith only [c153p]) (by linarith only [c157])
                          · exact Frame20.famA2_R F hx hα hβ (by linarith only [c142]) (by linarith only [c156p]) (by linarith only [c153p]) (by linarith only [c157])
                      · have c155p : 0 < -(-F.S.hm*F.S.sm*F.S.tp - F.S.hp*F.S.sm*F.S.tm + F.S.km*F.S.tm) := by linarith only [c155]
                        rcases lt_or_ge 0 ((F.S.tp^2 - F.S.tp) * (F.a11 - F.a12) + (F.S.tp^2 - 2*F.S.tp + 1) * F.a12 + (F.S.hp^2) * F.gg) with c158 | c158
                        · exact Frame20.famA1 F hx hα hβ (by linarith only [c124]) (by linarith only [c155p]) (by linarith only [c151p]) (by linarith only [c158])
                        · exact Frame20.famA2 F hx hα hβ (by linarith only [c124]) (by linarith only [c155p]) (by linarith only [c151p]) (by linarith only [c158])
      · rcases lt_or_gt_of_ne n15 with c159 | c159
        · have c159p : 0 < -(F.S.hm*F.S.sp - F.S.hm + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp - F.S.km*F.S.tm + F.S.km + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) := neg_pos.2 c159
          rcases lt_or_gt_of_ne n5 with c160 | c160
          · have c160p : 0 < -(F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) := neg_pos.2 c160
            rcases lt_or_gt_of_ne n6 with c161 | c161
            · have c161p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c161
              rcases le_or_gt 0 (F.S.tm - F.S.tp) with c162 | c162
              · rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c163 | c163 | c163
                · exact Frame20.om1n F hx hα hβ (by linarith only [c160p]) (by linarith only [c162]) (by linarith only [(neg_pos.2 c163)])
                · rcases lt_or_gt_of_ne (fun hl => n7 ⟨c163, hl⟩) with c164 | c164
                  · exact Frame20.om1z2 F hx hα hβ (by linarith only [c160p]) (by linarith only [c162]) (by linarith only [c163, (neg_pos.2 c164)]) (by linarith only [c163, (neg_pos.2 c164)]) (by linarith only [c163, (neg_pos.2 c164)])
                  · exact Frame20.om1z1 F hx hα hβ (by linarith only [c160p]) (by linarith only [c162]) (by linarith only [c163, c164]) (by linarith only [c163, c164]) (by linarith only [c163, c164])
                · exact Frame20.om1p F hx hα hβ (by linarith only [c160p]) (by linarith only [c162]) (by linarith only [c163])
              · have c162p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c162]
                rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c165 | c165
                · rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c166 | c166 | c166
                  · exact Frame20.om1n_R F hx hα hβ (by linarith only [c161p]) (by linarith only [c165]) (by linarith only [(neg_pos.2 c166)])
                  · rcases lt_or_gt_of_ne (fun hl => n8 ⟨c166, hl⟩) with c167 | c167
                    · exact Frame20.om1z2_R F hx hα hβ (by linarith only [c161p]) (by linarith only [c165]) (by linarith only [c166, (neg_pos.2 c167)]) (by linarith only [c166, (neg_pos.2 c167)]) (by linarith only [c166, (neg_pos.2 c167)])
                    · exact Frame20.om1z1_R F hx hα hβ (by linarith only [c161p]) (by linarith only [c165]) (by linarith only [c166, c167]) (by linarith only [c166, c167]) (by linarith only [c166, c167])
                  · exact Frame20.om1p_R F hx hα hβ (by linarith only [c161p]) (by linarith only [c165]) (by linarith only [c166])
                · have c165p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c165]
                  rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c168 | c168 | c168
                  · exact Frame20.om3n_R F hx hα hβ (by linarith only [c161p]) (by linarith only [(mul_pos F.S.sp_pos c91), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c159p]) (by linarith only [c91]) (by linarith only [(neg_pos.2 c168)])
                  · rcases lt_or_gt_of_ne (fun hl => n16 ⟨c168, hl⟩) with c169 | c169
                    · exact Frame20.om3z2_R F hx hα hβ (by linarith only [c161p]) (by linarith only [(mul_pos F.S.sp_pos c91), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c159p]) (by linarith only [c91]) (by linarith only [c168, (neg_pos.2 c169)]) (by linarith only [c168, (neg_pos.2 c169)]) (by linarith only [c168, (neg_pos.2 c169)])
                    · exact Frame20.om3z1_R F hx hα hβ (by linarith only [c161p]) (by linarith only [(mul_pos F.S.sp_pos c91), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c159p]) (by linarith only [c91]) (by linarith only [c168, c169]) (by linarith only [c168, c169]) (by linarith only [c168, c169])
                  · exact Frame20.om3p_R F hx hα hβ (by linarith only [c161p]) (by linarith only [(mul_pos F.S.sp_pos c91), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c159p]) (by linarith only [c91]) (by linarith only [c168])
            · rcases le_or_gt 0 (F.S.tm - F.S.tp) with c170 | c170
              · rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c171 | c171 | c171
                · exact Frame20.om1n F hx hα hβ (by linarith only [c160p]) (by linarith only [c170]) (by linarith only [(neg_pos.2 c171)])
                · rcases lt_or_gt_of_ne (fun hl => n7 ⟨c171, hl⟩) with c172 | c172
                  · exact Frame20.om1z2 F hx hα hβ (by linarith only [c160p]) (by linarith only [c170]) (by linarith only [c171, (neg_pos.2 c172)]) (by linarith only [c171, (neg_pos.2 c172)]) (by linarith only [c171, (neg_pos.2 c172)])
                  · exact Frame20.om1z1 F hx hα hβ (by linarith only [c160p]) (by linarith only [c170]) (by linarith only [c171, c172]) (by linarith only [c171, c172]) (by linarith only [c171, c172])
                · exact Frame20.om1p F hx hα hβ (by linarith only [c160p]) (by linarith only [c170]) (by linarith only [c171])
              · have c170p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c170]
                exact Frame20.om2a_R F hx hα hβ (by linarith only [c161]) (by linarith only [(mul_pos F.S.sp_pos c91), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c159p]) (by linarith only [c91])
          · rcases lt_or_gt_of_ne n6 with c173 | c173
            · have c173p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c173
              rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c174 | c174
              · rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c175 | c175 | c175
                · exact Frame20.om1n_R F hx hα hβ (by linarith only [c173p]) (by linarith only [c174]) (by linarith only [(neg_pos.2 c175)])
                · rcases lt_or_gt_of_ne (fun hl => n8 ⟨c175, hl⟩) with c176 | c176
                  · exact Frame20.om1z2_R F hx hα hβ (by linarith only [c173p]) (by linarith only [c174]) (by linarith only [c175, (neg_pos.2 c176)]) (by linarith only [c175, (neg_pos.2 c176)]) (by linarith only [c175, (neg_pos.2 c176)])
                  · exact Frame20.om1z1_R F hx hα hβ (by linarith only [c173p]) (by linarith only [c174]) (by linarith only [c175, c176]) (by linarith only [c175, c176]) (by linarith only [c175, c176])
                · exact Frame20.om1p_R F hx hα hβ (by linarith only [c173p]) (by linarith only [c174]) (by linarith only [c175])
              · have c174p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c174]
                rcases le_or_gt 0 (F.S.tm - F.S.tp) with c177 | c177
                · exact Frame20.om2b F hx hα hβ (by linarith only [c160]) (by linarith only [c2]) (by linarith only [c1p, c2]) (by linarith only [c177]) (by linarith only [c1p])
                · have c177p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c177]
                  rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c178 | c178 | c178
                  · exact Frame20.om3n_R F hx hα hβ (by linarith only [c173p]) (by linarith only [(mul_pos F.S.sp_pos c91), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c159p]) (by linarith only [c91]) (by linarith only [(neg_pos.2 c178)])
                  · rcases lt_or_gt_of_ne (fun hl => n16 ⟨c178, hl⟩) with c179 | c179
                    · exact Frame20.om3z2_R F hx hα hβ (by linarith only [c173p]) (by linarith only [(mul_pos F.S.sp_pos c91), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c159p]) (by linarith only [c91]) (by linarith only [c178, (neg_pos.2 c179)]) (by linarith only [c178, (neg_pos.2 c179)]) (by linarith only [c178, (neg_pos.2 c179)])
                    · exact Frame20.om3z1_R F hx hα hβ (by linarith only [c173p]) (by linarith only [(mul_pos F.S.sp_pos c91), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c159p]) (by linarith only [c91]) (by linarith only [c178, c179]) (by linarith only [c178, c179]) (by linarith only [c178, c179])
                  · exact Frame20.om3p_R F hx hα hβ (by linarith only [c173p]) (by linarith only [(mul_pos F.S.sp_pos c91), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c159p]) (by linarith only [c91]) (by linarith only [c178])
            · rcases le_or_gt 0 (F.S.tm - F.S.tp) with c180 | c180
              · exact Frame20.om2b F hx hα hβ (by linarith only [c160]) (by linarith only [c2]) (by linarith only [(mul_nonneg (by first | exact le_of_lt (htm1) | exact (htm1)) c1p), (mul_pos (mul_pos F.S.tp_pos hsp1) F.S.hm_pos)]) (by linarith only [c180]) (by linarith only [c1p])
              · have c180p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c180]
                exact Frame20.om2a_R F hx hα hβ (by linarith only [c173]) (by linarith only [(mul_pos F.S.sp_pos c91), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c159p]) (by linarith only [c91])
        · rcases lt_or_ge (-F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.sm*F.S.tm + F.S.hp*F.S.sm - F.S.km*F.S.tm*F.S.tp + F.S.km*F.S.tm + F.S.km*F.S.tp - F.S.km) 0 with c181 | c181
          · have c181p : 0 < -(-F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.sm*F.S.tm + F.S.hp*F.S.sm - F.S.km*F.S.tm*F.S.tp + F.S.km*F.S.tm + F.S.km*F.S.tp - F.S.km) := neg_pos.2 c181
            exact rupert_of_r (F.rFrame.vTri (by simp only [rFrame_S, Shape20.swap]; exact (by linarith only [c91])) (by simp only [rFrame_S, Shape20.swap]; exact (by linarith only [c159])) (by simp only [rFrame_S, Shape20.swap]; exact (by linarith only [c181p])))
          · rcases lt_or_gt_of_ne n6 with c182 | c182
            · have c182p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c182
              rcases le_or_gt (-F.S.hp*F.S.sm + F.S.hp - F.S.km*F.S.tp) 0 with c183 | c183
              · have c183p : 0 ≤ -(-F.S.hp*F.S.sm + F.S.hp - F.S.km*F.S.tp) := neg_nonneg.2 c183
                rcases le_or_gt (F.S.hp*F.S.sp - F.S.hp - F.S.km*F.S.sp*F.S.tp + F.S.km*F.S.tp - F.S.kp*F.S.sm*F.S.tp + F.S.kp) 0 with c184 | c184
                · have c184p : 0 ≤ -(F.S.hp*F.S.sp - F.S.hp - F.S.km*F.S.sp*F.S.tp + F.S.km*F.S.tp - F.S.kp*F.S.sm*F.S.tp + F.S.kp) := neg_nonneg.2 c184
                  exact Frame20.ra4_X_R_cc F hx hα hβ (by linarith only [c91]) (by linarith only [c159]) (by linarith only [c181]) (by linarith only [c182p]) (by linarith only [c183p]) (by linarith only [c184p])
                · exact Frame20.ra4_Y_R_cc F hx hα hβ (by linarith only [c91]) (by linarith only [c159]) (by linarith only [c181]) (by linarith only [c182p]) (by linarith only [c183p]) (by linarith only [c184])
              · exact Frame20.ra4_tBR_R F hx hα hβ (by linarith only [c182p]) (by linarith only [c183])
            · exact Frame20.ra4_A_R_cc F hx hα hβ (by linarith only [c91]) (by linarith only [c159]) (by linarith only [c181]) (by linarith only [c182])
  · rcases lt_or_gt_of_ne n21 with c185 | c185
    · have c185p : 0 < -(F.S.hm*F.S.sp*F.S.tp - F.S.hm*F.S.tp + F.S.hp*F.S.sp*F.S.tm - F.S.hp*F.S.sp - F.S.hp*F.S.tm + F.S.hp + F.S.kp*F.S.tm - F.S.kp) := neg_pos.2 c185
      rcases le_or_gt (-F.S.hm - F.S.km*F.S.tm + F.S.km) 0 with c186 | c186
      · have c186p : 0 ≤ -(-F.S.hm - F.S.km*F.S.tm + F.S.km) := neg_nonneg.2 c186
        rcases lt_or_gt_of_ne n4 with c187 | c187
        · have c187p : 0 < -(-F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) := neg_pos.2 c187
          rcases lt_or_gt_of_ne n5 with c188 | c188
          · have c188p : 0 < -(F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) := neg_pos.2 c188
            rcases lt_or_gt_of_ne n6 with c189 | c189
            · have c189p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c189
              rcases le_or_gt 0 (F.S.tm - F.S.tp) with c190 | c190
              · rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c191 | c191 | c191
                · exact Frame20.om1n F hx hα hβ (by linarith only [c188p]) (by linarith only [c190]) (by linarith only [(neg_pos.2 c191)])
                · rcases lt_or_gt_of_ne (fun hl => n7 ⟨c191, hl⟩) with c192 | c192
                  · exact Frame20.om1z2 F hx hα hβ (by linarith only [c188p]) (by linarith only [c190]) (by linarith only [c191, (neg_pos.2 c192)]) (by linarith only [c191, (neg_pos.2 c192)]) (by linarith only [c191, (neg_pos.2 c192)])
                  · exact Frame20.om1z1 F hx hα hβ (by linarith only [c188p]) (by linarith only [c190]) (by linarith only [c191, c192]) (by linarith only [c191, c192]) (by linarith only [c191, c192])
                · exact Frame20.om1p F hx hα hβ (by linarith only [c188p]) (by linarith only [c190]) (by linarith only [c191])
              · have c190p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c190]
                rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c193 | c193
                · rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c194 | c194 | c194
                  · exact Frame20.om1n_R F hx hα hβ (by linarith only [c189p]) (by linarith only [c193]) (by linarith only [(neg_pos.2 c194)])
                  · rcases lt_or_gt_of_ne (fun hl => n8 ⟨c194, hl⟩) with c195 | c195
                    · exact Frame20.om1z2_R F hx hα hβ (by linarith only [c189p]) (by linarith only [c193]) (by linarith only [c194, (neg_pos.2 c195)]) (by linarith only [c194, (neg_pos.2 c195)]) (by linarith only [c194, (neg_pos.2 c195)])
                    · exact Frame20.om1z1_R F hx hα hβ (by linarith only [c189p]) (by linarith only [c193]) (by linarith only [c194, c195]) (by linarith only [c194, c195]) (by linarith only [c194, c195])
                  · exact Frame20.om1p_R F hx hα hβ (by linarith only [c189p]) (by linarith only [c193]) (by linarith only [c194])
                · have c193p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c193]
                  rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c196 | c196 | c196
                  · exact Frame20.om3n F hx hα hβ (by linarith only [c188p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [(neg_pos.2 c196)])
                  · rcases lt_or_gt_of_ne (fun hl => n22 ⟨c196, hl⟩) with c197 | c197
                    · exact Frame20.om3z2 F hx hα hβ (by linarith only [c188p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [c196, (neg_pos.2 c197)]) (by linarith only [c196, (neg_pos.2 c197)]) (by linarith only [c196, (neg_pos.2 c197)])
                    · exact Frame20.om3z1 F hx hα hβ (by linarith only [c188p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [c196, c197]) (by linarith only [c196, c197]) (by linarith only [c196, c197])
                  · exact Frame20.om3p F hx hα hβ (by linarith only [c188p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [c196])
            · rcases le_or_gt 0 (F.S.tm - F.S.tp) with c198 | c198
              · rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c199 | c199 | c199
                · exact Frame20.om1n F hx hα hβ (by linarith only [c188p]) (by linarith only [c198]) (by linarith only [(neg_pos.2 c199)])
                · rcases lt_or_gt_of_ne (fun hl => n7 ⟨c199, hl⟩) with c200 | c200
                  · exact Frame20.om1z2 F hx hα hβ (by linarith only [c188p]) (by linarith only [c198]) (by linarith only [c199, (neg_pos.2 c200)]) (by linarith only [c199, (neg_pos.2 c200)]) (by linarith only [c199, (neg_pos.2 c200)])
                  · exact Frame20.om1z1 F hx hα hβ (by linarith only [c188p]) (by linarith only [c198]) (by linarith only [c199, c200]) (by linarith only [c199, c200]) (by linarith only [c199, c200])
                · exact Frame20.om1p F hx hα hβ (by linarith only [c188p]) (by linarith only [c198]) (by linarith only [c199])
              · have c198p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c198]
                rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c201 | c201 | c201
                · exact Frame20.om3n F hx hα hβ (by linarith only [c188p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [(neg_pos.2 c201)])
                · rcases lt_or_gt_of_ne (fun hl => n22 ⟨c201, hl⟩) with c202 | c202
                  · exact Frame20.om3z2 F hx hα hβ (by linarith only [c188p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [c201, (neg_pos.2 c202)]) (by linarith only [c201, (neg_pos.2 c202)]) (by linarith only [c201, (neg_pos.2 c202)])
                  · exact Frame20.om3z1 F hx hα hβ (by linarith only [c188p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [c201, c202]) (by linarith only [c201, c202]) (by linarith only [c201, c202])
                · exact Frame20.om3p F hx hα hβ (by linarith only [c188p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [c201])
          · rcases lt_or_gt_of_ne n6 with c203 | c203
            · have c203p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c203
              rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c204 | c204
              · rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c205 | c205 | c205
                · exact Frame20.om1n_R F hx hα hβ (by linarith only [c203p]) (by linarith only [c204]) (by linarith only [(neg_pos.2 c205)])
                · rcases lt_or_gt_of_ne (fun hl => n8 ⟨c205, hl⟩) with c206 | c206
                  · exact Frame20.om1z2_R F hx hα hβ (by linarith only [c203p]) (by linarith only [c204]) (by linarith only [c205, (neg_pos.2 c206)]) (by linarith only [c205, (neg_pos.2 c206)]) (by linarith only [c205, (neg_pos.2 c206)])
                  · exact Frame20.om1z1_R F hx hα hβ (by linarith only [c203p]) (by linarith only [c204]) (by linarith only [c205, c206]) (by linarith only [c205, c206]) (by linarith only [c205, c206])
                · exact Frame20.om1p_R F hx hα hβ (by linarith only [c203p]) (by linarith only [c204]) (by linarith only [c205])
              · have c204p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c204]
                exact Frame20.om2a F hx hα hβ (by linarith only [c188]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1])
            · exact Frame20.om2a F hx hα hβ (by linarith only [c188]) (by linarith only [(mul_pos F.S.tm_pos c1), (mul_pos (mul_pos F.S.tp_pos hsp1) F.S.hm_pos)]) (by linarith only [c185p]) (by linarith only [c1])
        · rcases lt_or_gt_of_ne n5 with c207 | c207
          · have c207p : 0 < -(F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) := neg_pos.2 c207
            rcases lt_or_gt_of_ne n6 with c208 | c208
            · have c208p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c208
              rcases le_or_gt 0 (F.S.tm - F.S.tp) with c209 | c209
              · rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c210 | c210 | c210
                · exact Frame20.om1n F hx hα hβ (by linarith only [c207p]) (by linarith only [c209]) (by linarith only [(neg_pos.2 c210)])
                · rcases lt_or_gt_of_ne (fun hl => n7 ⟨c210, hl⟩) with c211 | c211
                  · exact Frame20.om1z2 F hx hα hβ (by linarith only [c207p]) (by linarith only [c209]) (by linarith only [c210, (neg_pos.2 c211)]) (by linarith only [c210, (neg_pos.2 c211)]) (by linarith only [c210, (neg_pos.2 c211)])
                  · exact Frame20.om1z1 F hx hα hβ (by linarith only [c207p]) (by linarith only [c209]) (by linarith only [c210, c211]) (by linarith only [c210, c211]) (by linarith only [c210, c211])
                · exact Frame20.om1p F hx hα hβ (by linarith only [c207p]) (by linarith only [c209]) (by linarith only [c210])
              · have c209p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c209]
                rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c212 | c212
                · rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c213 | c213 | c213
                  · exact Frame20.om1n_R F hx hα hβ (by linarith only [c208p]) (by linarith only [c212]) (by linarith only [(neg_pos.2 c213)])
                  · rcases lt_or_gt_of_ne (fun hl => n8 ⟨c213, hl⟩) with c214 | c214
                    · exact Frame20.om1z2_R F hx hα hβ (by linarith only [c208p]) (by linarith only [c212]) (by linarith only [c213, (neg_pos.2 c214)]) (by linarith only [c213, (neg_pos.2 c214)]) (by linarith only [c213, (neg_pos.2 c214)])
                    · exact Frame20.om1z1_R F hx hα hβ (by linarith only [c208p]) (by linarith only [c212]) (by linarith only [c213, c214]) (by linarith only [c213, c214]) (by linarith only [c213, c214])
                  · exact Frame20.om1p_R F hx hα hβ (by linarith only [c208p]) (by linarith only [c212]) (by linarith only [c213])
                · have c212p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c212]
                  rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c215 | c215 | c215
                  · exact Frame20.om3n F hx hα hβ (by linarith only [c207p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [(neg_pos.2 c215)])
                  · rcases lt_or_gt_of_ne (fun hl => n22 ⟨c215, hl⟩) with c216 | c216
                    · exact Frame20.om3z2 F hx hα hβ (by linarith only [c207p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [c215, (neg_pos.2 c216)]) (by linarith only [c215, (neg_pos.2 c216)]) (by linarith only [c215, (neg_pos.2 c216)])
                    · exact Frame20.om3z1 F hx hα hβ (by linarith only [c207p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [c215, c216]) (by linarith only [c215, c216]) (by linarith only [c215, c216])
                  · exact Frame20.om3p F hx hα hβ (by linarith only [c207p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [c215])
            · rcases le_or_gt 0 (F.S.tm - F.S.tp) with c217 | c217
              · rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c218 | c218 | c218
                · exact Frame20.om1n F hx hα hβ (by linarith only [c207p]) (by linarith only [c217]) (by linarith only [(neg_pos.2 c218)])
                · rcases lt_or_gt_of_ne (fun hl => n7 ⟨c218, hl⟩) with c219 | c219
                  · exact Frame20.om1z2 F hx hα hβ (by linarith only [c207p]) (by linarith only [c217]) (by linarith only [c218, (neg_pos.2 c219)]) (by linarith only [c218, (neg_pos.2 c219)]) (by linarith only [c218, (neg_pos.2 c219)])
                  · exact Frame20.om1z1 F hx hα hβ (by linarith only [c207p]) (by linarith only [c217]) (by linarith only [c218, c219]) (by linarith only [c218, c219]) (by linarith only [c218, c219])
                · exact Frame20.om1p F hx hα hβ (by linarith only [c207p]) (by linarith only [c217]) (by linarith only [c218])
              · have c217p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c217]
                rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c220 | c220 | c220
                · exact Frame20.om3n F hx hα hβ (by linarith only [c207p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [(neg_pos.2 c220)])
                · rcases lt_or_gt_of_ne (fun hl => n22 ⟨c220, hl⟩) with c221 | c221
                  · exact Frame20.om3z2 F hx hα hβ (by linarith only [c207p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [c220, (neg_pos.2 c221)]) (by linarith only [c220, (neg_pos.2 c221)]) (by linarith only [c220, (neg_pos.2 c221)])
                  · exact Frame20.om3z1 F hx hα hβ (by linarith only [c207p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [c220, c221]) (by linarith only [c220, c221]) (by linarith only [c220, c221])
                · exact Frame20.om3p F hx hα hβ (by linarith only [c207p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [c220])
          · rcases lt_or_gt_of_ne n6 with c222 | c222
            · have c222p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c222
              rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c223 | c223
              · rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c224 | c224 | c224
                · exact Frame20.om1n_R F hx hα hβ (by linarith only [c222p]) (by linarith only [c223]) (by linarith only [(neg_pos.2 c224)])
                · rcases lt_or_gt_of_ne (fun hl => n8 ⟨c224, hl⟩) with c225 | c225
                  · exact Frame20.om1z2_R F hx hα hβ (by linarith only [c222p]) (by linarith only [c223]) (by linarith only [c224, (neg_pos.2 c225)]) (by linarith only [c224, (neg_pos.2 c225)]) (by linarith only [c224, (neg_pos.2 c225)])
                  · exact Frame20.om1z1_R F hx hα hβ (by linarith only [c222p]) (by linarith only [c223]) (by linarith only [c224, c225]) (by linarith only [c224, c225]) (by linarith only [c224, c225])
                · exact Frame20.om1p_R F hx hα hβ (by linarith only [c222p]) (by linarith only [c223]) (by linarith only [c224])
              · have c223p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c223]
                exact Frame20.om2a F hx hα hβ (by linarith only [c207]) (by linarith only [(mul_pos F.S.tm_pos c1), (mul_pos (mul_pos F.S.tp_pos hsp1) F.S.hm_pos)]) (by linarith only [c185p]) (by linarith only [c1])
            · exact Frame20.om2a F hx hα hβ (by linarith only [c207]) (by linarith only [(mul_pos F.S.tm_pos c1), (mul_pos (mul_pos F.S.tp_pos hsp1) F.S.hm_pos)]) (by linarith only [c185p]) (by linarith only [c1])
      · rcases lt_or_gt_of_ne n15 with c226 | c226
        · have c226p : 0 < -(F.S.hm*F.S.sp - F.S.hm + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp - F.S.km*F.S.tm + F.S.km + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) := neg_pos.2 c226
          rcases lt_or_gt_of_ne n5 with c227 | c227
          · have c227p : 0 < -(F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) := neg_pos.2 c227
            rcases lt_or_gt_of_ne n6 with c228 | c228
            · have c228p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c228
              rcases le_or_gt 0 (F.S.tm - F.S.tp) with c229 | c229
              · rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c230 | c230 | c230
                · exact Frame20.om1n F hx hα hβ (by linarith only [c227p]) (by linarith only [c229]) (by linarith only [(neg_pos.2 c230)])
                · rcases lt_or_gt_of_ne (fun hl => n7 ⟨c230, hl⟩) with c231 | c231
                  · exact Frame20.om1z2 F hx hα hβ (by linarith only [c227p]) (by linarith only [c229]) (by linarith only [c230, (neg_pos.2 c231)]) (by linarith only [c230, (neg_pos.2 c231)]) (by linarith only [c230, (neg_pos.2 c231)])
                  · exact Frame20.om1z1 F hx hα hβ (by linarith only [c227p]) (by linarith only [c229]) (by linarith only [c230, c231]) (by linarith only [c230, c231]) (by linarith only [c230, c231])
                · exact Frame20.om1p F hx hα hβ (by linarith only [c227p]) (by linarith only [c229]) (by linarith only [c230])
              · have c229p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c229]
                rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c232 | c232
                · rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c233 | c233 | c233
                  · exact Frame20.om1n_R F hx hα hβ (by linarith only [c228p]) (by linarith only [c232]) (by linarith only [(neg_pos.2 c233)])
                  · rcases lt_or_gt_of_ne (fun hl => n8 ⟨c233, hl⟩) with c234 | c234
                    · exact Frame20.om1z2_R F hx hα hβ (by linarith only [c228p]) (by linarith only [c232]) (by linarith only [c233, (neg_pos.2 c234)]) (by linarith only [c233, (neg_pos.2 c234)]) (by linarith only [c233, (neg_pos.2 c234)])
                    · exact Frame20.om1z1_R F hx hα hβ (by linarith only [c228p]) (by linarith only [c232]) (by linarith only [c233, c234]) (by linarith only [c233, c234]) (by linarith only [c233, c234])
                  · exact Frame20.om1p_R F hx hα hβ (by linarith only [c228p]) (by linarith only [c232]) (by linarith only [c233])
                · have c232p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c232]
                  rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c235 | c235 | c235
                  · exact Frame20.om3n F hx hα hβ (by linarith only [c227p]) (by linarith only [(mul_pos F.S.tm_pos c1), (mul_pos (mul_pos F.S.tp_pos hsp1) F.S.hm_pos)]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [(neg_pos.2 c235)])
                  · rcases lt_or_gt_of_ne (fun hl => n22 ⟨c235, hl⟩) with c236 | c236
                    · exact Frame20.om3z2 F hx hα hβ (by linarith only [c227p]) (by linarith only [(mul_pos F.S.tm_pos c1), (mul_pos (mul_pos F.S.tp_pos hsp1) F.S.hm_pos)]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [c235, (neg_pos.2 c236)]) (by linarith only [c235, (neg_pos.2 c236)]) (by linarith only [c235, (neg_pos.2 c236)])
                    · exact Frame20.om3z1 F hx hα hβ (by linarith only [c227p]) (by linarith only [(mul_pos F.S.tm_pos c1), (mul_pos (mul_pos F.S.tp_pos hsp1) F.S.hm_pos)]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [c235, c236]) (by linarith only [c235, c236]) (by linarith only [c235, c236])
                  · exact Frame20.om3p F hx hα hβ (by linarith only [c227p]) (by linarith only [(mul_pos F.S.tm_pos c1), (mul_pos (mul_pos F.S.tp_pos hsp1) F.S.hm_pos)]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [c235])
            · rcases le_or_gt 0 (F.S.tm - F.S.tp) with c237 | c237
              · rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c238 | c238 | c238
                · exact Frame20.om1n F hx hα hβ (by linarith only [c227p]) (by linarith only [c237]) (by linarith only [(neg_pos.2 c238)])
                · rcases lt_or_gt_of_ne (fun hl => n7 ⟨c238, hl⟩) with c239 | c239
                  · exact Frame20.om1z2 F hx hα hβ (by linarith only [c227p]) (by linarith only [c237]) (by linarith only [c238, (neg_pos.2 c239)]) (by linarith only [c238, (neg_pos.2 c239)]) (by linarith only [c238, (neg_pos.2 c239)])
                  · exact Frame20.om1z1 F hx hα hβ (by linarith only [c227p]) (by linarith only [c237]) (by linarith only [c238, c239]) (by linarith only [c238, c239]) (by linarith only [c238, c239])
                · exact Frame20.om1p F hx hα hβ (by linarith only [c227p]) (by linarith only [c237]) (by linarith only [c238])
              · have c237p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c237]
                rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c240 | c240 | c240
                · exact Frame20.om3n F hx hα hβ (by linarith only [c227p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [(neg_pos.2 c240)])
                · rcases lt_or_gt_of_ne (fun hl => n22 ⟨c240, hl⟩) with c241 | c241
                  · exact Frame20.om3z2 F hx hα hβ (by linarith only [c227p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [c240, (neg_pos.2 c241)]) (by linarith only [c240, (neg_pos.2 c241)]) (by linarith only [c240, (neg_pos.2 c241)])
                  · exact Frame20.om3z1 F hx hα hβ (by linarith only [c227p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [c240, c241]) (by linarith only [c240, c241]) (by linarith only [c240, c241])
                · exact Frame20.om3p F hx hα hβ (by linarith only [c227p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [c240])
          · rcases lt_or_gt_of_ne n6 with c242 | c242
            · have c242p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c242
              rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c243 | c243
              · rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c244 | c244 | c244
                · exact Frame20.om1n_R F hx hα hβ (by linarith only [c242p]) (by linarith only [c243]) (by linarith only [(neg_pos.2 c244)])
                · rcases lt_or_gt_of_ne (fun hl => n8 ⟨c244, hl⟩) with c245 | c245
                  · exact Frame20.om1z2_R F hx hα hβ (by linarith only [c242p]) (by linarith only [c243]) (by linarith only [c244, (neg_pos.2 c245)]) (by linarith only [c244, (neg_pos.2 c245)]) (by linarith only [c244, (neg_pos.2 c245)])
                  · exact Frame20.om1z1_R F hx hα hβ (by linarith only [c242p]) (by linarith only [c243]) (by linarith only [c244, c245]) (by linarith only [c244, c245]) (by linarith only [c244, c245])
                · exact Frame20.om1p_R F hx hα hβ (by linarith only [c242p]) (by linarith only [c243]) (by linarith only [c244])
              · have c243p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c243]
                exact Frame20.om2a F hx hα hβ (by linarith only [c227]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1])
            · exact Frame20.om2a F hx hα hβ (by linarith only [c227]) (by linarith only [(mul_pos F.S.tm_pos c1), (mul_pos (mul_pos F.S.tp_pos hsp1) F.S.hm_pos)]) (by linarith only [c185p]) (by linarith only [c1])
        · rcases lt_or_ge (-F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.sm*F.S.tm + F.S.hp*F.S.sm - F.S.km*F.S.tm*F.S.tp + F.S.km*F.S.tm + F.S.km*F.S.tp - F.S.km) 0 with c246 | c246
          · have c246p : 0 < -(-F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.sm*F.S.tm + F.S.hp*F.S.sm - F.S.km*F.S.tm*F.S.tp + F.S.km*F.S.tm + F.S.km*F.S.tp - F.S.km) := neg_pos.2 c246
            exact rupert_of_r (F.rFrame.vTri (by simp only [rFrame_S, Shape20.swap]; exact (by linarith only [c186])) (by simp only [rFrame_S, Shape20.swap]; exact (by linarith only [c226])) (by simp only [rFrame_S, Shape20.swap]; exact (by linarith only [c246p])))
          · rcases lt_or_gt_of_ne n6 with c247 | c247
            · have c247p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c247
              rcases le_or_gt (-F.S.hp*F.S.sm + F.S.hp - F.S.km*F.S.tp) 0 with c248 | c248
              · have c248p : 0 ≤ -(-F.S.hp*F.S.sm + F.S.hp - F.S.km*F.S.tp) := neg_nonneg.2 c248
                rcases le_or_gt (F.S.hp*F.S.sp - F.S.hp - F.S.km*F.S.sp*F.S.tp + F.S.km*F.S.tp - F.S.kp*F.S.sm*F.S.tp + F.S.kp) 0 with c249 | c249
                · have c249p : 0 ≤ -(F.S.hp*F.S.sp - F.S.hp - F.S.km*F.S.sp*F.S.tp + F.S.km*F.S.tp - F.S.kp*F.S.sm*F.S.tp + F.S.kp) := neg_nonneg.2 c249
                  exact Frame20.ra4_X_R_cc F hx hα hβ (by linarith only [c186]) (by linarith only [c226]) (by linarith only [c246]) (by linarith only [c247p]) (by linarith only [c248p]) (by linarith only [c249p])
                · exact Frame20.ra4_Y_R_cc F hx hα hβ (by linarith only [c186]) (by linarith only [c226]) (by linarith only [c246]) (by linarith only [c247p]) (by linarith only [c248p]) (by linarith only [c249])
              · exact Frame20.ra4_tBR_R F hx hα hβ (by linarith only [c247p]) (by linarith only [c248])
            · exact Frame20.ra4_A_R_cc F hx hα hβ (by linarith only [c186]) (by linarith only [c226]) (by linarith only [c246]) (by linarith only [c247])
    · rcases lt_or_ge (-F.S.hp*F.S.sm*F.S.sp + F.S.hp*F.S.sm + F.S.hp*F.S.sp - F.S.hp - F.S.km*F.S.sp*F.S.tp + F.S.km*F.S.tp - F.S.kp*F.S.sm + F.S.kp) 0 with c250 | c250
      · have c250p : 0 < -(-F.S.hp*F.S.sm*F.S.sp + F.S.hp*F.S.sm + F.S.hp*F.S.sp - F.S.hp - F.S.km*F.S.sp*F.S.tp + F.S.km*F.S.tp - F.S.kp*F.S.sm + F.S.kp) := neg_pos.2 c250
        exact F.vTri (by linarith only [c1]) (by linarith only [c185]) (by linarith only [c250p])
      · rcases lt_or_gt_of_ne n5 with c251 | c251
        · have c251p : 0 < -(F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) := neg_pos.2 c251
          rcases le_or_gt (-F.S.hp*F.S.sm - F.S.km*F.S.tp + F.S.km) 0 with c252 | c252
          · have c252p : 0 ≤ -(-F.S.hp*F.S.sm - F.S.km*F.S.tp + F.S.km) := neg_nonneg.2 c252
            rcases le_or_gt (-F.S.hm*F.S.sm*F.S.tp + F.S.hm - F.S.hp*F.S.sm*F.S.tm + F.S.hp*F.S.sm + F.S.km*F.S.tm - F.S.km) 0 with c253 | c253
            · have c253p : 0 ≤ -(-F.S.hm*F.S.sm*F.S.tp + F.S.hm - F.S.hp*F.S.sm*F.S.tm + F.S.hp*F.S.sm + F.S.km*F.S.tm - F.S.km) := neg_nonneg.2 c253
              exact Frame20.ra4_X_cc F hx hα hβ (by linarith only [c1]) (by linarith only [c185]) (by linarith only [c250]) (by linarith only [c251p]) (by linarith only [c252p]) (by linarith only [c253p])
            · exact Frame20.ra4_Y_cc F hx hα hβ (by linarith only [c1]) (by linarith only [c185]) (by linarith only [c250]) (by linarith only [c251p]) (by linarith only [c252p]) (by linarith only [c253])
          · exact Frame20.ra4_tBR F hx hα hβ (by linarith only [c251p]) (by linarith only [c252])
        · exact Frame20.ra4_A_cc F hx hα hβ (by linarith only [c1]) (by linarith only [c185]) (by linarith only [c250]) (by linarith only [c251])


end Minimality.CaseC20
