module

public import Minimality.CaseC20Bridge
public import Minimality.CaseC20ST
public import Minimality.CaseC20NR
public import Minimality.CaseC20Tests
public import Minimality.CaseC20TestsNR
public import Minimality.CaseC20VSlide
public import Minimality.CaseC20Step4

@[expose] public section

/-!
# Type 20, acute case (c): the non-strict (`_cc`) covering lemmas

The `ra4_*_cc`, `om4*_cc` theorems (and `_R_cc` images) of Theorem 27.79: the same covering
lemmas as in `CaseC20Leaves`, with `0 ≤` in place of `0 <` in some sign hypotheses.  The strict
versions in `CaseC20Leaves` are one-line corollaries.  (Moved out of `CaseC20Sp` unchanged.)
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
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_4, F.ptC_5, F.ptC_6, Shape20.u_vRa4, Shape20.u_tA] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
  · linarith only [mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n1_3), mul_nonneg (hsm1).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.hp_pos F.S.km_pos)) hde]
  · linarith only [(sub_nonneg.2 n0_2), mul_nonneg (hsp1).le (sub_nonneg.2 n1_1), mul_pos ((mul_pos htp1 hsp1)) hga, mul_pos ((mul_pos F.S.hp_pos F.S.kp_pos)) hde]
  · linarith only [(sub_nonneg.2 n1_4), mul_pos ((mul_pos htp1 F.S.sm_pos)) hga, mul_pos ((mul_pos F.S.hp_pos F.S.km_pos)) hde]
  · linarith only [mul_nonneg ((mul_pos F.S.tp_pos htp1)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos htp1 htp1)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos F.S.tp_pos hsp1)).le (sub_nonneg.2 n1_1), mul_pos ((mul_pos F.S.hp_pos hQ)) hde, mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.hp_pos) F.S.kp_pos)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le hW) (hA1).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (htm1).le hW) (hA1).le) (hde).le), mul_pos ((mul_pos (mul_pos F.S.sm_pos F.S.hm_pos) rp)) hde, mul_pos ((mul_pos (mul_pos hsm1 F.S.hm_pos) rp)) hde]


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
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
  · linarith only [(sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tp_pos hsp1)) hal, mul_pos ((mul_pos (mul_pos F.S.tp_pos hsp1) hsm1)) hga, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le (F.S.km_pos).le) hW) (hde).le), mul_pos ((mul_pos (mul_pos htp1 F.S.km_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos F.S.tm_pos F.S.km_pos) rp)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le hD) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (htm1).le hD) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (hsm1).le hW) (hA1r).le) (hde).le)]
  · linarith only [mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n1_1), (sub_nonneg.2 n1_2), mul_pos ((mul_pos F.S.tp_pos F.S.sp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.tm_pos)) hbe, mul_pos ((mul_pos F.S.tm_pos htm1)) hbe, mul_pos ((mul_pos htm1 htm1)) hbe, mul_pos ((mul_pos htp1 hsp1)) hga, mul_pos ((mul_pos F.S.hp_pos F.S.kp_pos)) hde]
  · linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.hp_pos F.S.hm_pos)) hde]
  · linarith only [mul_nonneg ((mul_pos F.S.hp_pos F.S.km_pos)).le (sub_nonneg.2 n0_2), mul_nonneg ((mul_pos F.S.km_pos hA1r)).le (sub_nonneg.2 n0_2), mul_nonneg ((mul_pos F.S.hp_pos F.S.hp_pos)).le (sub_nonneg.2 n0_4), mul_nonneg ((mul_pos F.S.hp_pos hA1r)).le (sub_nonneg.2 n0_4), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le (F.S.kp_pos).le) hA3h) (hal).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le hW) hA3h) (hal).le), (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le (F.S.hp_pos).le) hD) (hal).le), (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le (rm).le) hD) (hal).le), (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le hD) (hA1r).le) (hal).le), (mul_nonneg (mul_nonneg (mul_nonneg (htm1).le hD) hCm) (hal).le), mul_pos ((mul_pos (mul_pos hsm1 F.S.hp_pos) rp)) hal, mul_pos ((mul_pos (mul_pos hsm1 rp) rm)) hal, mul_pos ((mul_pos (mul_pos hsm1 rp) hA1r)) hal, (mul_nonneg (mul_nonneg (mul_nonneg (hsm1).le (hQ).le) hCm) (hal).le), (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le (F.S.hp_pos).le) hD) (hga).le), (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le hD) (hA1r).le) (hga).le), mul_pos ((mul_pos (mul_pos hsm1 F.S.hp_pos) rp)) hga, mul_pos ((mul_pos (mul_pos hsm1 rp) hA1r)) hga]
  · linarith only [(sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.sp_pos hsp1)) hbe, mul_pos ((mul_pos hsp1 hsp1)) hbe, mul_pos ((mul_pos htp1 hsp1)) hga, mul_pos ((mul_pos F.S.hp_pos F.S.kp_pos)) hde]
  · linarith only [mul_nonneg ((mul_pos F.S.tp_pos htm1)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos htp1 htm1)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos F.S.tp_pos hsp1)).le (sub_nonneg.2 n1_1), mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.kp_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos htp1 F.S.kp_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) hQ)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sm_pos).le hW) (hQ).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (hsm1).le hW) (hQ).le) (hde).le)]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n1_1), (mul_nonneg hA3h (sub_nonneg.2 n1_1)), mul_pos ((mul_pos F.S.tp_pos F.S.kp_pos)) hal, mul_pos ((mul_pos F.S.tp_pos F.S.km_pos)) hal, (mul_nonneg (mul_nonneg (F.S.tp_pos).le hA3h) (hal).le), mul_pos ((mul_pos F.S.tp_pos rp)) hbe, (mul_nonneg (mul_nonneg (F.S.tp_pos).le hD) (hbe).le), mul_pos ((mul_pos htp1 F.S.kp_pos)) hbe, mul_pos ((mul_pos htp1 F.S.km_pos)) hbe, mul_pos ((mul_pos htp1 rp)) hbe, (mul_nonneg (mul_nonneg (htp1).le hD) (hbe).le), mul_pos ((mul_pos F.S.tm_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, (mul_nonneg (mul_nonneg (F.S.sp_pos).le hCm) (hbe).le), mul_pos ((mul_pos F.S.sm_pos F.S.kp_pos)) hbe, mul_pos ((mul_pos F.S.sm_pos hA1r)) hbe, mul_pos ((mul_pos hsm1 F.S.hm_pos)) hbe]
  · linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.hp_pos F.S.hm_pos)) hde]
  · linarith only [mul_nonneg ((mul_pos htm1 F.S.sm_pos)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos htm1 hsm1)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos F.S.tp_pos hsp1)).le (sub_nonneg.2 n1_3), mul_pos ((mul_pos (mul_pos htp1 F.S.km_pos) hQ)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sm_pos).le (hQ).le) hCm) (hde).le), mul_pos ((mul_pos (mul_pos hsm1 F.S.hp_pos) hQ)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (hsm1).le (hQ).le) hCm) (hde).le)]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_3), (mul_nonneg hW (sub_nonneg.2 n1_3)), (mul_nonneg hD (sub_nonneg.2 n1_3)), mul_pos ((mul_pos F.S.tp_pos F.S.kp_pos)) hal, (mul_nonneg (mul_nonneg (F.S.tp_pos).le hW) (hal).le), (mul_nonneg (mul_nonneg (F.S.tp_pos).le hD) (hal).le), mul_pos ((mul_pos hsp1 F.S.km_pos)) hbe, (mul_nonneg (mul_nonneg (hsp1).le hCm) (hbe).le), mul_pos ((mul_pos hsm1 F.S.kp_pos)) hbe]


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
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
  · linarith only [mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n1_1), mul_nonneg (hsp1).le (sub_nonneg.2 n1_1), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, (mul_nonneg (mul_nonneg (htm1).le hCm) (hal).le), mul_pos ((mul_pos htp1 rm)) hbe, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hbe, (mul_nonneg (mul_nonneg (htm1).le hCm) (hbe).le), mul_pos ((mul_pos F.S.sm_pos hA1r)) hbe, mul_pos ((mul_pos hsm1 hA1r)) hbe]
  · linarith only [mul_nonneg ((mul_pos F.S.tm_pos htm1)).le (sub_nonneg.2 n0_4), mul_nonneg ((mul_pos F.S.tm_pos F.S.sp_pos)).le (sub_nonneg.2 n0_4), mul_nonneg ((mul_pos F.S.tm_pos hsp1)).le (sub_nonneg.2 n0_4), mul_nonneg ((mul_pos htm1 htm1)).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.tm_pos) hsp1)) hal, mul_pos ((mul_pos (mul_pos F.S.tp_pos htm1) hsp1)) hal, mul_pos ((mul_pos (mul_pos F.S.tp_pos hsp1) hsm1)) hga, (mul_nonneg (mul_nonneg (hQ).le hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le (F.S.hm_pos).le) hD) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le (rm).le) hW) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le (F.S.km_pos).le) hW) (hde).le), mul_pos ((mul_pos (mul_pos F.S.sm_pos F.S.hm_pos) rp)) hde, mul_pos ((mul_pos (mul_pos F.S.sm_pos F.S.km_pos) hQ)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sm_pos).le hW) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (hsm1).le (F.S.hm_pos).le) hW) (hde).le), mul_pos ((mul_pos (mul_pos hsm1 F.S.km_pos) hQ)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (hsm1).le hW) hA3) (hde).le)]
  · linarith only [(sub_nonneg.2 n0_4), mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.sp_pos) hsp1)) hal, mul_pos ((mul_pos (mul_pos F.S.tp_pos hsp1) hsp1)) hal, mul_pos ((mul_pos (mul_pos F.S.tp_pos hsp1) hsm1)) hga, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le (F.S.hm_pos).le) hD) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le hW) (hQ).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le hW) hD) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le hW) hA3) (hde).le), mul_pos ((mul_pos (mul_pos htp1 rm) hQ)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le hW) (hQ).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le hW) hD) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le hW) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le (F.S.kp_pos).le) hD) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le (F.S.km_pos).le) hW) (hde).le), mul_pos ((mul_pos (mul_pos F.S.tm_pos F.S.km_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos F.S.tm_pos rp) rm)) hde, mul_pos ((mul_pos (mul_pos htm1 F.S.km_pos) hQ)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (htm1).le hD) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.hm_pos).le) hD) (hde).le), mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.km_pos) hQ)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (hQ).le) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le hD) (hA1r).le) (hde).le), mul_pos ((mul_pos (mul_pos F.S.sm_pos F.S.hm_pos) rp)) hde, mul_pos ((mul_pos (mul_pos F.S.sm_pos F.S.kp_pos) hQ)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (hsm1).le (F.S.hm_pos).le) hW) (hde).le), mul_pos ((mul_pos (mul_pos hsm1 hQ) hA1r)) hde]
  · linarith only [(sub_nonneg.2 n1_3), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, (mul_nonneg (mul_nonneg (htm1).le hCm) (hal).le), mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsp1 hA1r)) hal, mul_pos ((mul_pos htp1 rm)) hbe, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hbe, (mul_nonneg (mul_nonneg (htm1).le hCm) (hbe).le), mul_pos ((mul_pos F.S.sm_pos hA1r)) hbe, mul_pos ((mul_pos hsm1 hA1r)) hbe]
  · linarith only [mul_nonneg ((mul_pos F.S.tp_pos F.S.sp_pos)).le (sub_nonneg.2 n0_4), mul_nonneg ((mul_pos htp1 F.S.sp_pos)).le (sub_nonneg.2 n0_4), mul_nonneg ((mul_pos F.S.sp_pos hsp1)).le (sub_nonneg.2 n0_4), mul_nonneg ((mul_pos hsp1 hsp1)).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.tm_pos) hsp1)) hal, mul_pos ((mul_pos (mul_pos F.S.tp_pos htm1) hsp1)) hal, mul_pos ((mul_pos (mul_pos F.S.tp_pos hsp1) hsm1)) hga, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le (F.S.km_pos).le) hW) (hde).le), mul_pos ((mul_pos (mul_pos htp1 F.S.km_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos F.S.tm_pos F.S.km_pos) rp)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le hD) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (htm1).le hD) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (hsm1).le hW) (hA1r).le) (hde).le)]
  · linarith only [mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n1_1), mul_nonneg (hsp1).le (sub_nonneg.2 n1_1), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, (mul_nonneg (mul_nonneg (htm1).le hCm) (hal).le), mul_pos ((mul_pos htp1 rm)) hbe, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hbe, (mul_nonneg (mul_nonneg (htm1).le hCm) (hbe).le), mul_pos ((mul_pos F.S.sm_pos hA1r)) hbe, mul_pos ((mul_pos hsm1 hA1r)) hbe]
  · linarith only [mul_nonneg ((mul_pos F.S.tm_pos F.S.sm_pos)).le (sub_nonneg.2 n1_4), mul_nonneg ((mul_pos htm1 F.S.sm_pos)).le (sub_nonneg.2 n1_4), mul_nonneg ((mul_pos F.S.sm_pos hsm1)).le (sub_nonneg.2 n1_4), mul_nonneg ((mul_pos hsm1 hsm1)).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.tm_pos) rp)) hbe, mul_pos ((mul_pos (mul_pos F.S.tp_pos hsp1) hA1r)) hbe, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le (hsp1).le) hCm) (hbe).le), mul_pos ((mul_pos (mul_pos htp1 F.S.tm_pos) rp)) hbe, (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le (F.S.tm_pos).le) hD) (hbe).le), (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le (htm1).le) hD) (hbe).le), mul_pos ((mul_pos (mul_pos htp1 F.S.sm_pos) F.S.kp_pos)) hbe, mul_pos ((mul_pos (mul_pos htp1 F.S.sm_pos) hQ)) hbe, mul_pos ((mul_pos (mul_pos htp1 hsm1) hQ)) hbe, mul_pos ((mul_pos (mul_pos hsp1 F.S.sm_pos) hA1r)) hbe, (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le (hsp1).le) hA3) (hga).le), mul_pos ((mul_pos (mul_pos htp1 F.S.sm_pos) F.S.kp_pos)) hga, mul_pos ((mul_pos (mul_pos htp1 F.S.sm_pos) hQ)) hga, mul_pos ((mul_pos (mul_pos F.S.tm_pos F.S.sm_pos) rp)) hga, mul_pos ((mul_pos (mul_pos hsp1 F.S.sm_pos) hA1r)) hga, mul_pos ((mul_pos (mul_pos F.S.hp_pos F.S.kp_pos) rm)) hde]
  · linarith only [mul_nonneg ((mul_pos F.S.tm_pos hA1r)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos htp1 F.S.tm_pos) rm)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos F.S.tm_pos F.S.tm_pos) F.S.hp_pos)).le (sub_nonneg.2 n0_1), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le (htm1).le) hCm) (sub_nonneg.2 n0_1)), (mul_nonneg (mul_nonneg (F.S.tm_pos).le hA3) (sub_nonneg.2 n0_2)), mul_nonneg ((mul_pos F.S.tp_pos hsp1)).le (sub_nonneg.2 n1_1), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le (F.S.hm_pos).le) (rp).le) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le (F.S.hm_pos).le) hW) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le (F.S.hm_pos).le) hD) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le (F.S.hm_pos).le) hD) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le (F.S.kp_pos).le) (hA1r).le) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le (F.S.hp_pos).le) (F.S.hp_pos).le) hW) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le (F.S.hp_pos).le) (F.S.hp_pos).le) hD) (hde).le), mul_pos ((mul_pos (mul_pos (mul_pos F.S.tm_pos F.S.hp_pos) F.S.hm_pos) F.S.kp_pos)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.tm_pos F.S.hp_pos) F.S.kp_pos) hA1r)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.tm_pos F.S.hp_pos) F.S.km_pos) hQ)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le (F.S.hp_pos).le) (rp).le) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le (F.S.hp_pos).le) hD) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le (F.S.hp_pos).le) hD) hCm) (hde).le), mul_pos ((mul_pos (mul_pos (mul_pos F.S.tm_pos F.S.hm_pos) F.S.km_pos) rp)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le (F.S.kp_pos).le) (F.S.km_pos).le) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le (F.S.kp_pos).le) hCm) hA3) (hde).le), mul_pos ((mul_pos (mul_pos (mul_pos F.S.tm_pos F.S.km_pos) rp) hA1r)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le (F.S.km_pos).le) hW) hA3) (hde).le), mul_pos ((mul_pos (mul_pos (mul_pos F.S.tm_pos F.S.km_pos) hQ) hA1r)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le (F.S.km_pos).le) (hQ).le) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (htm1).le (F.S.hm_pos).le) (F.S.kp_pos).le) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (htm1).le (F.S.kp_pos).le) (hA1r).le) hCm) (hde).le), mul_pos ((mul_pos (mul_pos (mul_pos F.S.sp_pos F.S.kp_pos) hA1r) hA1r)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.kp_pos).le) (hA1r).le) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le hW) (hA1r).le) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (hQ).le) (hA1r).le) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le hD) (hA1r).le) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le hD) (hA1r).le) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le hD) (hA1r).le) hA3) (hde).le), mul_pos ((mul_pos (mul_pos (mul_pos hsp1 F.S.kp_pos) hA1r) hA1r)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le (F.S.kp_pos).le) (hA1r).le) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le hW) (hA1r).le) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le (hQ).le) (hA1r).le) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le hD) (hA1r).le) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le hD) (hA1r).le) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le hD) (hA1r).le) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sm_pos).le (F.S.kp_pos).le) (hA1r).le) hA3) (hde).le), mul_pos ((mul_pos (mul_pos (mul_pos F.S.sm_pos hQ) hA1r) hA1r)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sm_pos).le (hQ).le) (hA1r).le) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hsm1).le (F.S.hm_pos).le) (F.S.kp_pos).le) hA3) (hde).le), mul_pos ((mul_pos (mul_pos (mul_pos hsm1 F.S.hm_pos) rp) hA1r)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hsm1).le (F.S.hm_pos).le) (rp).le) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hsm1).le (F.S.hm_pos).le) hW) hA3) (hde).le), mul_pos ((mul_pos (mul_pos (mul_pos hsm1 F.S.hm_pos) hQ) hA1r)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hsm1).le (F.S.hm_pos).le) (hQ).le) hCm) (hde).le)]
  · linarith only [(sub_nonneg.2 n1_3), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, (mul_nonneg (mul_nonneg (htm1).le hCm) (hal).le), mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsp1 hA1r)) hal, mul_pos ((mul_pos htp1 rm)) hbe, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hbe, (mul_nonneg (mul_nonneg (htm1).le hCm) (hbe).le), mul_pos ((mul_pos F.S.sm_pos hA1r)) hbe, mul_pos ((mul_pos hsm1 hA1r)) hbe]
  · linarith only [(mul_nonneg (mul_nonneg (htm1).le hCm) (sub_nonneg.2 n0_1)), mul_nonneg ((mul_pos hsm1 hA1r)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos htp1 F.S.tm_pos) rm)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos htp1 htm1) rm)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos F.S.tm_pos hsm1) F.S.hp_pos)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos htm1 F.S.sm_pos) hA1r)).le (sub_nonneg.2 n0_1), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le (htm1).le) hA3) (sub_nonneg.2 n0_2)), (mul_nonneg (mul_nonneg (mul_nonneg (htm1).le (htm1).le) hA3) (sub_nonneg.2 n0_2)), mul_nonneg ((mul_pos F.S.tp_pos hsp1)).le (sub_nonneg.2 n1_3), mul_pos ((mul_pos (mul_pos F.S.hp_pos rm) hQ)) hde]


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
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga, mul_pos ((mul_pos hsm1 F.S.hm_pos)) hga]
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_4)), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos htp1 rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [mul_nonneg (hVpR).le (sub_nonneg.2 n0_4), mul_nonneg (hVWR).le (sub_nonneg.2 n1_4), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos htp1 rm)) hga, mul_pos ((mul_pos hsm1 hVWR)) hga]
  · linarith only [(sub_nonneg.2 n0_3), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n1_4), hnu, mul_pos ((mul_pos htp1 F.S.tm_pos)) hal, mul_pos ((mul_pos F.S.tm_pos hsm1)) hga]
  · linarith only [mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n0_1), mul_nonneg (htm1).le (sub_nonneg.2 n0_3), mul_pos F.S.sp_pos hnu, mul_pos hsm1 hnu, mul_pos hss hnu]
  · linarith only [mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n2_4), mul_nonneg (htm1).le (sub_nonneg.2 n2_4), mul_pos F.S.tp_pos hnu, mul_pos htp1 hnu]


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
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga, mul_pos ((mul_pos hsm1 F.S.hm_pos)) hga]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [mul_nonneg (htp1).le (sub_nonneg.2 n0_1), (sub_nonneg.2 n0_2), mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n0_3), mul_nonneg (htp1).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n1_3), mul_pos F.S.sp_pos hnu, mul_pos hsm1 hnu, mul_pos hss hnu, mul_pos ((mul_pos htp1 htp1)) hal, mul_pos ((mul_pos htp1 htm1)) hal]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_2), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n1_3), mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [mul_nonneg (hVpR).le (sub_nonneg.2 n0_4), mul_nonneg (hVWR).le (sub_nonneg.2 n1_4), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos ((mul_pos htp1 rm)) hga, mul_pos ((mul_pos hsm1 hVWR)) hga]
  · linarith only [mul_nonneg (htp1).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n1_4), mul_nonneg (htp1).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.sm_pos hsm1)) hga, mul_pos ((mul_pos hsm1 hsm1)) hga, mul_pos ((mul_pos F.S.hp_pos F.S.km_pos)) hde]
  · linarith only [(sub_nonneg.2 n2_4), mul_pos F.S.sp_pos hnu, mul_pos hsm1 hnu, mul_pos hss hnu]
  · linarith only [mul_nonneg ((mul_pos htm1 F.S.sp_pos)).le (sub_nonneg.2 n1_1), mul_nonneg ((mul_pos htm1 hss)).le (sub_nonneg.2 n1_1), mul_nonneg ((mul_pos F.S.tp_pos hsm1)).le (sub_nonneg.2 n2_2), mul_nonneg ((mul_pos htp1 hsm1)).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos (mul_pos F.S.tm_pos rm) hA1R)) hde, mul_pos ((mul_pos (mul_pos htm1 rm) hA1R)) hde, mul_pos ((mul_pos (mul_pos hsm1 F.S.kp_pos) rm)) hde, mul_pos ((mul_pos (mul_pos hsm1 F.S.km_pos) rm)) hde, mul_pos ((mul_pos (mul_pos F.S.km_pos rm) hss)) hde]


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
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga, mul_pos ((mul_pos hsm1 F.S.hm_pos)) hga]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga, mul_pos ((mul_pos hsm1 F.S.hm_pos)) hga]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [(sub_nonneg.2 n0_3), mul_nonneg (htm1).le (sub_nonneg.2 n0_4), (sub_nonneg.2 n1_4), (sub_nonneg.2 n2_4), mul_pos ((mul_pos htp1 F.S.tm_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hsm1)) hga, mul_pos ((mul_pos hsm1 hsm1)) hga, mul_pos ((mul_pos hsm1 hss)) hga]
  · linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_4), mul_nonneg (hVWR).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos hsm1 hVpR)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n2_4), mul_nonneg (hsm1).le (sub_nonneg.2 n2_4), mul_nonneg (hss).le (sub_nonneg.2 n2_4), mul_pos F.S.tm_pos hl]
  · linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.sm_pos).le hnu1, mul_nonneg (hsm1).le hnu1, mul_pos F.S.tm_pos hl]


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
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga, mul_pos ((mul_pos hsm1 F.S.hm_pos)) hga]
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga, mul_pos ((mul_pos hsm1 F.S.hm_pos)) hga]
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_4), mul_pos F.S.hm_pos hl, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos hsm1 F.S.hm_pos)) hga]
  · linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_3), mul_nonneg (hVpR).le (sub_nonneg.2 n1_4), (mul_nonneg hKb (sub_nonneg.2 n1_4)), mul_pos hVpR hl, (mul_nonneg hKb (hl).le), mul_pos ((mul_pos htp1 hVWR)) hal, mul_pos ((mul_pos hsm1 hVpR)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_1), mul_pos hVpR hl, (mul_nonneg hKb (hl).le)]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_1), mul_pos F.S.hm_pos hl]


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
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos F.S.tm_pos rm)) hga, mul_pos ((mul_pos htm1 rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_4)), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos htp1 rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos F.S.tm_pos rm)) hga, mul_pos ((mul_pos htm1 rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · linarith only [mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n0_1), mul_nonneg (htm1).le (sub_nonneg.2 n0_3), mul_pos F.S.tm_pos hnu, mul_pos htm1 hnu]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos F.S.tp_pos rm)) hga, mul_pos ((mul_pos htp1 rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]


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
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga, mul_pos ((mul_pos hsm1 F.S.hm_pos)) hga]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), (mul_nonneg hKb (sub_nonneg.2 n1_3)), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_4)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_3), mul_pos ((mul_pos htp1 rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · linarith only [(sub_nonneg.2 n0_4), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n1_4), mul_nonneg (htm1).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.tm_pos hsm1)) hga, mul_pos ((mul_pos htm1 hsm1)) hga]
  · linarith only [mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n2_3), mul_nonneg (htp1).le (sub_nonneg.2 n2_3), mul_pos F.S.sm_pos hnu, mul_pos hsm1 hnu]
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_1)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos F.S.sm_pos rm)) hbe, mul_pos ((mul_pos F.S.sm_pos rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]


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
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n0_1), mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n0_2), mul_nonneg (hsm1).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n1_3), mul_nonneg (hsm1).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n2_3), mul_nonneg (hsm1).le (sub_nonneg.2 n2_3), mul_pos F.S.sp_pos hl, mul_pos hsp1 hl]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), (mul_nonneg hKb (sub_nonneg.2 n1_3)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos hA1r)) hal, mul_pos ((mul_pos htm1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos rm)) hga, mul_pos ((mul_pos htm1 rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · linarith only [mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n0_4), mul_nonneg (hsp1).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n1_4), mul_nonneg (hsp1).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.sm_pos hsm1)) hga, mul_pos ((mul_pos hsm1 hsm1)) hga]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_nonneg (F.S.km_pos).le hnu1, mul_pos ((mul_pos F.S.tm_pos rm)) hga, mul_pos ((mul_pos htm1 rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n2_3), mul_nonneg (htp1).le (sub_nonneg.2 n2_3), mul_pos F.S.tm_pos hl]
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_1)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos F.S.sm_pos rm)) hbe, mul_pos ((mul_pos F.S.sm_pos rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]


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
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga, mul_pos ((mul_pos hsm1 F.S.hm_pos)) hga]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n0_3)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.km_pos).le hnu2, mul_pos F.S.km_pos hl, (mul_nonneg hKb (hl).le), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos hA1r)) hal, mul_pos ((mul_pos htm1 hA1r)) hal]
  · linarith only [mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n1_4), mul_nonneg (hsm1).le (sub_nonneg.2 n1_4), mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n2_4), mul_nonneg (htp1).le (sub_nonneg.2 n2_4), hl, mul_pos F.S.tm_pos hl, mul_pos ((mul_pos F.S.tp_pos htp1)) hal, mul_pos ((mul_pos htp1 htp1)) hal, mul_pos ((mul_pos F.S.tp_pos htm1)) hga, mul_pos ((mul_pos htp1 htm1)) hga, mul_pos ((mul_pos F.S.tm_pos hsm1)) hga]
  · linarith only [mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n0_1), mul_nonneg (htm1).le (sub_nonneg.2 n0_1), mul_pos F.S.sm_pos hl, mul_pos hsm1 hl]
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n0_3)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), (mul_nonneg hKb (hl).le), (mul_nonneg (mul_nonneg (htp1).le hKb) (hal).le), mul_pos ((mul_pos F.S.tp_pos rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]


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
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_4), mul_nonneg (hVpR).le (sub_nonneg.2 n1_1), (mul_nonneg hKb (sub_nonneg.2 n1_2)), mul_nonneg (hVpR).le (sub_nonneg.2 n1_4), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_2), mul_nonneg (hA1Rr).le (sub_nonneg.2 n2_2), mul_nonneg (rm).le (sub_nonneg.2 n3_1), mul_nonneg (hVWR).le (sub_nonneg.2 n3_1), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos hsm1 rm)) hbe, mul_pos ((mul_pos hsm1 hVpR)) hbe, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hbe).le), mul_pos ((mul_pos rm hss)) hbe, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_2), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), (mul_nonneg hKb (sub_nonneg.2 n1_2)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n1_3), (mul_nonneg hKb (sub_nonneg.2 n1_3)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_2), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_3), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos rm hss)) hbe, mul_pos ((mul_pos rm hss)) hga]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sm_pos hA1Rr)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe]
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_3)), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_3)), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [(sub_nonneg.2 n0_3), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n1_3), mul_pos F.S.tm_pos hnu, mul_pos htm1 hnu, mul_pos ((mul_pos htp1 F.S.tm_pos)) hal]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n3_1), mul_pos ((mul_pos hsm1 F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hsm1 F.S.km_pos)) hga, mul_pos ((mul_pos hsm1 hA1Rr)) hga]
  · linarith only [mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n0_1), mul_nonneg (htm1).le (sub_nonneg.2 n0_3), mul_pos F.S.sm_pos hnu, mul_pos hsm1 hnu]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n3_1), mul_pos ((mul_pos hsm1 F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hsm1 F.S.km_pos)) hga, mul_pos ((mul_pos hsm1 hA1Rr)) hga]
  · linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n2_4), mul_pos hVpR hnu, (mul_nonneg hKb (hnu).le)]


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
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sp_pos hA1Rr)) hbe, mul_pos ((mul_pos hsp1 hA1Rr)) hbe]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sp_pos hA1Rr)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hA1Rr hss)) hbe]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_nonneg (hVpR).le (sub_nonneg.2 n0_2), mul_nonneg (hVWR).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n3_4), mul_nonneg (hVpR).le (sub_nonneg.2 n3_4), mul_nonneg (F.S.km_pos).le hnu1, mul_pos F.S.km_pos hl, mul_pos hVpR hl, (mul_nonneg hKb (hl).le)]
  · linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (hVWR).le (sub_nonneg.2 n0_3), mul_nonneg (hVWR).le (sub_nonneg.2 n1_4), mul_nonneg (hVWR).le (sub_nonneg.2 n3_1), mul_pos hVpR hl, (mul_nonneg hKb (hl).le), mul_pos ((mul_pos hsm1 hVWR)) hbe]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n3_1), mul_pos ((mul_pos hsm1 F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hsm1 F.S.km_pos)) hga, mul_pos ((mul_pos hsm1 hA1Rr)) hga]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (hA1r).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_nonneg (hA1r).le (sub_nonneg.2 n1_3), mul_pos hA1r hl, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sm_pos hA1Rr)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe]
  · linarith only [(sub_nonneg.2 n0_3), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n2_4), mul_nonneg (htp1).le (sub_nonneg.2 n2_4), mul_pos ((mul_pos htp1 F.S.tm_pos)) hal]
  · linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos hsm1 hVpR)) hbe, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hbe).le)]
  · linarith only [(sub_nonneg.2 n0_3), mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.tm_pos).le hnu1, mul_nonneg (htm1).le hnu1, mul_pos ((mul_pos htp1 F.S.tm_pos)) hal]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sp_pos hA1Rr)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hA1Rr hss)) hbe]
  · linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n2_4), mul_nonneg (hsm1).le (sub_nonneg.2 n2_4), mul_nonneg (hss).le (sub_nonneg.2 n2_4), mul_pos F.S.tm_pos hl]
  · linarith only [mul_nonneg (hVpR).le (sub_nonneg.2 n1_2), (mul_nonneg hKb (sub_nonneg.2 n1_2)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_2), mul_nonneg (hA1Rr).le (sub_nonneg.2 n2_2), mul_nonneg (rm).le (sub_nonneg.2 n3_1), mul_nonneg (hVWR).le (sub_nonneg.2 n3_1), mul_pos ((mul_pos hsm1 rm)) hbe, mul_pos ((mul_pos hsm1 hVpR)) hbe, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hbe).le), mul_pos ((mul_pos rm hss)) hbe]
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_2)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_1), mul_pos ((mul_pos rm hss)) hbe, mul_pos ((mul_pos rm hss)) hga]


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
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_3), mul_nonneg (hVWR).le (sub_nonneg.2 n1_3), mul_pos F.S.km_pos hl, mul_pos hVpR hl, (mul_nonneg hKb (hl).le), mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_3), mul_nonneg (hVpR).le (sub_nonneg.2 n1_3), (mul_nonneg hKb (sub_nonneg.2 n1_3)), mul_pos F.S.km_pos hl, mul_pos hVWR hl, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_3), mul_nonneg (hVWR).le (sub_nonneg.2 n1_3), mul_pos F.S.km_pos hl, mul_pos hVpR hl, (mul_nonneg hKb (hl).le), mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos hA1r)) hal, mul_pos ((mul_pos htm1 hA1r)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_3), mul_pos F.S.hm_pos hl, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.tp_pos hA1Rr)) hbe, mul_pos ((mul_pos htp1 hA1Rr)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_1), mul_pos hVpR hl, (mul_nonneg hKb (hl).le)]
  · linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n3_4), mul_nonneg (hVpR).le (sub_nonneg.2 n3_4), mul_pos F.S.km_pos hl, mul_pos hVpR hl, (mul_nonneg hKb (hl).le), mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n0_1), mul_pos hsm1 hl, mul_pos hss hl]


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
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_pos F.S.hm_pos hom, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_pos F.S.hm_pos hom, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_2), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n1_4), mul_nonneg (hVpR).le (sub_nonneg.2 n1_4), (mul_nonneg hKb (sub_nonneg.2 n1_4)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n3_1), mul_nonneg (hVWR).le (sub_nonneg.2 n3_1), mul_pos F.S.km_pos hnu, mul_pos F.S.hm_pos hom, mul_pos hVpR hom, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos hsm1 F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hVWR)) hbe]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_pos F.S.hm_pos hom, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · linarith only [(sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos hsm1)) hbe, mul_pos ((mul_pos hsm1 hsm1)) hbe, mul_pos ((mul_pos hsm1 hss)) hbe]
  · linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n2_4), mul_pos hVpR hnu, (mul_nonneg hKb (hnu).le)]
  · linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_4), mul_pos hVpR hom, (mul_nonneg hKb (hom).le)]
  · linarith only [(sub_nonneg.2 n0_4), mul_pos F.S.tp_pos hom, mul_pos htp1 hom]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_4), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_1), mul_pos F.S.kp_pos hom, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sp_pos hA1Rr)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hA1Rr hss)) hbe]
  · linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_4), mul_pos hVpR hom, (mul_nonneg hKb (hom).le)]
  · linarith only [mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n1_1), mul_nonneg (hsm1).le (sub_nonneg.2 n1_2), mul_nonneg (hsm1).le (sub_nonneg.2 n3_1), (sub_nonneg.2 n3_2), mul_pos ((mul_pos hsm1 hsm1)) hbe, mul_pos ((mul_pos hsm1 hsm1)) hga, mul_pos ((mul_pos F.S.km_pos F.S.km_pos)) hde]
  · linarith only [mul_nonneg (hVpR).le (sub_nonneg.2 n0_4), (mul_nonneg hKb (sub_nonneg.2 n1_1)), (mul_nonneg hKb (sub_nonneg.2 n1_4)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_1), mul_pos hVWR hom, mul_pos ((mul_pos rm hss)) hbe, mul_pos ((mul_pos rm hss)) hga]


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
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_2), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hom, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_2), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hom, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hnu, (mul_nonneg hKb (hom).le), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_nonneg (hVWR).le (sub_nonneg.2 n1_4), (mul_nonneg hKb (sub_nonneg.2 n3_1)), mul_nonneg (hVpR).le (sub_nonneg.2 n3_3), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hbe).le)]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos hVpR hom, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n2_4), mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.tp_pos hnu, mul_pos htp1 hnu, mul_pos hss hnu]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sp_pos hA1Rr)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hA1Rr hss)) hbe]
  · linarith only [mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n1_3), mul_pos F.S.sp_pos hom, mul_pos hss hom]
  · linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n1_4), mul_nonneg (hVWR).le (sub_nonneg.2 n3_1), mul_nonneg (hVWR).le (sub_nonneg.2 n3_4), mul_pos ((mul_pos hsm1 hVpR)) hbe, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hbe).le)]
  · linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n2_4), mul_pos hsm1 hnu, mul_pos hss hnu]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n3_1), mul_pos ((mul_pos hsm1 F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hsm1 F.S.km_pos)) hga, mul_pos ((mul_pos hsm1 hA1Rr)) hga]
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_2)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_1), mul_pos ((mul_pos rm hss)) hbe, mul_pos ((mul_pos rm hss)) hga]


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
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hnu, (mul_nonneg hKb hom2), mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_2), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hnu, mul_nonneg (F.S.km_pos).le hom2, (mul_nonneg hKb hom2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), (mul_nonneg hKb (sub_nonneg.2 n1_2)), (mul_nonneg hKb (sub_nonneg.2 n1_3)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_2), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_3), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos rm hss)) hbe, mul_pos ((mul_pos rm hss)) hga]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sp_pos hA1Rr)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hA1Rr hss)) hbe]
  · linarith only [(sub_nonneg.2 n2_4), mul_pos F.S.sm_pos hnu, mul_pos hsm1 hnu]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sp_pos hA1Rr)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hA1Rr hss)) hbe]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n3_3), mul_pos hsm1 hl2]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.tm_pos hA1Rr)) hbe, mul_pos ((mul_pos htm1 hA1Rr)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n2_4), mul_pos hVpR hnu, (mul_nonneg hKb (hnu).le)]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sp_pos hA1Rr)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hA1Rr hss)) hbe]
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_2)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_1), mul_pos ((mul_pos rm hss)) hbe, mul_pos ((mul_pos rm hss)) hga]


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
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vN4, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hnu, (mul_nonneg hKb hom2), mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_2), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hnu, mul_nonneg (F.S.km_pos).le hom2, (mul_nonneg hKb hom2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), (mul_nonneg hKb (sub_nonneg.2 n3_4)), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos htp1 hVpR)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), (mul_nonneg hKb (sub_nonneg.2 n1_2)), (mul_nonneg hKb (sub_nonneg.2 n1_3)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_2), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_3), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hA1r)) hal, mul_pos ((mul_pos hsm1 hA1r)) hal, mul_pos ((mul_pos hA1r hss)) hal, mul_pos ((mul_pos rm hss)) hbe, mul_pos ((mul_pos rm hss)) hga]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sp_pos hA1Rr)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hA1Rr hss)) hbe]
  · linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n2_4), mul_pos hsm1 hnu, mul_pos hss hnu]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sp_pos hA1Rr)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hA1Rr hss)) hbe]
  · linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n1_4), mul_pos hsm1 hl2]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n3_1), mul_pos ((mul_pos hsm1 F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hsm1 F.S.km_pos)) hga, mul_pos ((mul_pos hsm1 hA1Rr)) hga]
  · linarith only [mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n2_4), mul_nonneg (htp1).le (sub_nonneg.2 n2_4), mul_pos F.S.sp_pos hnu, mul_pos hsm1 hnu, mul_pos hss hnu]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sp_pos hA1Rr)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hA1Rr hss)) hbe]
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_2)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_1), mul_pos ((mul_pos rm hss)) hbe, mul_pos ((mul_pos rm hss)) hga]


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
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos F.S.tm_pos rm)) hga, mul_pos ((mul_pos htm1 rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos F.S.tp_pos rm)) hga, mul_pos ((mul_pos htp1 rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n3_1), mul_pos ((mul_pos hsm1 F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hsm1 F.S.km_pos)) hga, mul_pos ((mul_pos hsm1 hA1Rr)) hga]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n3_1), mul_pos ((mul_pos hsm1 F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos hsm1 F.S.km_pos)) hga, mul_pos ((mul_pos hsm1 hA1Rr)) hga]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos F.S.tm_pos rm)) hga, mul_pos ((mul_pos htm1 rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos F.S.tm_pos rm)) hga, mul_pos ((mul_pos htm1 rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_2)), mul_nonneg (rm).le (sub_nonneg.2 n1_4), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_nonneg (rm).le (sub_nonneg.2 n3_1), (mul_nonneg hKb (sub_nonneg.2 n3_1)), mul_nonneg (rm).le (sub_nonneg.2 n3_4), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos F.S.tp_pos rm)) hbe, mul_pos ((mul_pos htp1 rm)) hbe, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hbe).le), mul_pos ((mul_pos F.S.sm_pos rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_1)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.km_pos hnu, mul_pos ((mul_pos F.S.sm_pos rm)) hbe, mul_pos ((mul_pos F.S.sm_pos rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]


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
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_2), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n3_4), (mul_nonneg hKb (sub_nonneg.2 n3_4)), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos rm)) hga, mul_pos ((mul_pos htm1 rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), (mul_nonneg hKb (sub_nonneg.2 n1_3)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos ((mul_pos htp1 F.S.hm_pos)) hal, mul_pos ((mul_pos F.S.sp_pos rm)) hga, mul_pos ((mul_pos hsp1 rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.tp_pos hA1Rr)) hbe, mul_pos ((mul_pos htp1 hA1Rr)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · linarith only [mul_nonneg (hA1Rr).le (sub_nonneg.2 n2_4), mul_pos hA1Rr hnu, mul_pos ((mul_pos F.S.sp_pos rm)) hga, mul_pos ((mul_pos hsm1 hVR)) hga]
  · linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · linarith only [mul_nonneg (hA1Rr).le (sub_nonneg.2 n2_4), mul_pos hA1Rr hnu, mul_pos ((mul_pos F.S.sp_pos rm)) hga, mul_pos ((mul_pos hsm1 hVR)) hga]
  · linarith only [(sub_nonneg.2 n2_3), mul_pos F.S.sp_pos hnu, mul_pos hsp1 hnu]
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_2)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_2), (mul_nonneg hKb (sub_nonneg.2 n3_1)), mul_pos ((mul_pos F.S.sm_pos rm)) hbe, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hbe).le), mul_pos ((mul_pos F.S.sm_pos rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]


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
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (hA1r).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_nonneg (hA1r).le (sub_nonneg.2 n3_4), mul_pos hA1r hl, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (hA1r).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_nonneg (hA1r).le (sub_nonneg.2 n3_4), (mul_nonneg hKb (sub_nonneg.2 n3_4)), mul_pos hA1r hl, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos rm)) hga, mul_pos ((mul_pos htm1 rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_nonneg (rm).le (sub_nonneg.2 n0_2), mul_nonneg (rm).le (sub_nonneg.2 n0_3), (mul_nonneg hKb (sub_nonneg.2 n1_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_4), mul_nonneg (rm).le (sub_nonneg.2 n1_4), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_2), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n3_1), mul_nonneg (rm).le (sub_nonneg.2 n3_1), (mul_nonneg hKb (sub_nonneg.2 n3_3)), mul_nonneg (F.S.km_pos).le hnu1, mul_pos F.S.km_pos hl, mul_pos rm hl, (mul_nonneg (mul_nonneg (htp1).le hKb) (hal).le), mul_pos ((mul_pos F.S.tp_pos rm)) hbe, mul_pos ((mul_pos htp1 rm)) hbe, mul_pos ((mul_pos hsm1 F.S.hm_pos)) hbe, mul_pos ((mul_pos F.S.sm_pos rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_nonneg (hA1r).le (sub_nonneg.2 n0_3), mul_nonneg (hA1r).le (sub_nonneg.2 n1_3), mul_pos hA1r hl, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_pos ((mul_pos F.S.tm_pos hA1Rr)) hbe, mul_pos ((mul_pos htm1 hA1Rr)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_2)), mul_nonneg (rm).le (sub_nonneg.2 n1_4), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_2), mul_nonneg (rm).le (sub_nonneg.2 n3_1), (mul_nonneg hKb (sub_nonneg.2 n3_1)), mul_nonneg (rm).le (sub_nonneg.2 n3_4), mul_pos ((mul_pos F.S.tp_pos rm)) hbe, mul_pos ((mul_pos htp1 rm)) hbe, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hbe).le), mul_pos ((mul_pos F.S.sm_pos rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]


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
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    obtain ⟨n3_1, n3_2, n3_3, n3_4⟩ := n3
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_tP, Shape20.u_tANR, Shape20.u_vRv, Shape20.u_tP] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4 n3_1 n3_2 n3_3 n3_4
  · linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_nonneg (F.S.km_pos).le hnu1, mul_pos ((mul_pos F.S.tm_pos rm)) hga, mul_pos ((mul_pos htm1 rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_4), (mul_nonneg hKb (sub_nonneg.2 n1_3)), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.km_pos hl, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos rm)) hga, mul_pos ((mul_pos htm1 rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_3), mul_pos F.S.hm_pos hl, mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal]
  · linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n0_3)), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.km_pos hl, (mul_nonneg hKb (hl).le), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos hA1r)) hal, mul_pos ((mul_pos htm1 hA1r)) hal, mul_pos ((mul_pos F.S.tm_pos rm)) hga, mul_pos ((mul_pos htm1 rm)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_1), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n2_4), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n3_2), mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n3_3), mul_nonneg (F.S.km_pos).le hnu1, mul_pos F.S.hm_pos hl, mul_pos ((mul_pos htp1 F.S.km_pos)) hal, (mul_nonneg (mul_nonneg (htp1).le hKb) (hal).le), mul_pos ((mul_pos hsm1 hA1Rr)) hbe, mul_pos ((mul_pos F.S.tp_pos rm)) hga, mul_pos ((mul_pos hsm1 F.S.km_pos)) hga, mul_pos ((mul_pos hsm1 hA1Rr)) hga, (mul_nonneg (mul_nonneg (hsm1).le hKb) (hga).le)]
  · linarith only [mul_pos ((mul_pos F.S.kp_pos rm)) hal, mul_pos ((mul_pos F.S.km_pos hVR)) hal, (mul_nonneg (mul_nonneg (hA1Rr).le hKb) (hal).le)]


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
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_tA] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
  · linarith only [mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n1_3), mul_nonneg (htp1).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.hp_pos F.S.km_pos)) hde]
  · linarith only [mul_nonneg (F.S.km_pos).le (sub_nonneg.2 n0_4), (mul_nonneg hW (sub_nonneg.2 n1_3)), mul_pos ((mul_pos F.S.sm_pos F.S.hm_pos)) hbe, (mul_nonneg (mul_nonneg (F.S.sm_pos).le hW) (hbe).le), mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [(sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.tp_pos hsm1)) hga, mul_pos ((mul_pos F.S.hp_pos F.S.km_pos)) hde]
  · linarith only [mul_nonneg ((mul_pos F.S.sm_pos hsm1)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos hsm1 hsm1)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos htm1 F.S.sm_pos)).le (sub_nonneg.2 n1_1), mul_pos ((mul_pos F.S.km_pos hQ)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le hW) (hA1).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le hW) (hA1).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.kp_pos).le) hW) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le (F.S.kp_pos).le) hW) (hde).le), mul_pos ((mul_pos (mul_pos F.S.sm_pos F.S.hm_pos) F.S.kp_pos)) hde, mul_pos ((mul_pos (mul_pos F.S.sm_pos F.S.hm_pos) F.S.km_pos)) hde]


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
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_yY] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
  · linarith only [mul_nonneg ((mul_pos F.S.tp_pos F.S.sp_pos)).le (sub_nonneg.2 n0_3), mul_nonneg ((mul_pos F.S.tp_pos hsp1)).le (sub_nonneg.2 n0_3), mul_nonneg (htp1).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos (mul_pos htp1 htm1) F.S.sm_pos)) hbe, mul_pos ((mul_pos (mul_pos htp1 htm1) F.S.sm_pos)) hga, mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.hp_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos htp1 F.S.hp_pos) hQ)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le (F.S.kp_pos).le) hW) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le hW) (hA1r).le) (hde).le), mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) rm)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.hp_pos).le) hW) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le hD) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le hD) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sm_pos).le (F.S.hp_pos).le) hW) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sm_pos).le (F.S.kp_pos).le) hD) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (hsm1).le (rp).le) hW) (hde).le)]
  · linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n1_1), mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_1), mul_nonneg (hA1r).le (sub_nonneg.2 n1_1), (mul_nonneg hA3h (sub_nonneg.2 n1_1)), mul_pos ((mul_pos F.S.tp_pos F.S.hm_pos)) hal, mul_pos ((mul_pos F.S.tp_pos hQ)) hal, (mul_nonneg (mul_nonneg (F.S.tp_pos).le hD) (hal).le), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, mul_pos ((mul_pos htp1 F.S.kp_pos)) hal, mul_pos ((mul_pos htp1 hQ)) hal, (mul_nonneg (mul_nonneg (htp1).le hD) (hal).le), mul_pos ((mul_pos F.S.tm_pos F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos hA1r)) hal, (mul_nonneg (mul_nonneg (F.S.tm_pos).le hCm) (hal).le), mul_pos ((mul_pos htm1 F.S.kp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos F.S.hp_pos)) hal, mul_pos ((mul_pos hsp1 F.S.hm_pos)) hal, mul_pos ((mul_pos hsm1 F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.sm_pos F.S.hp_pos)) hbe, mul_pos ((mul_pos F.S.sm_pos F.S.hm_pos)) hbe, mul_pos ((mul_pos F.S.sm_pos hA1r)) hbe, (mul_nonneg (mul_nonneg (F.S.sm_pos).le hA3h) (hbe).le)]
  · linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.kp_pos F.S.km_pos)) hde]
  · linarith only [mul_nonneg (htm1).le (sub_nonneg.2 n0_4), mul_nonneg ((mul_pos F.S.tm_pos F.S.sm_pos)).le (sub_nonneg.2 n0_4), mul_nonneg ((mul_pos F.S.tm_pos hsm1)).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos (mul_pos htm1 F.S.sp_pos) F.S.sm_pos)) hbe, mul_pos ((mul_pos (mul_pos htm1 hsp1) F.S.sm_pos)) hbe, mul_pos ((mul_pos (mul_pos htp1 htm1) F.S.sm_pos)) hga, (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le (F.S.kp_pos).le) hW) (hde).le), mul_pos ((mul_pos (mul_pos htp1 F.S.kp_pos) hQ)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le hW) (hA1r).le) (hde).le), mul_pos ((mul_pos (mul_pos htp1 hQ) hA1r)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le hD) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (htm1).le hD) (hA1r).le) (hde).le), mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) rm)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.hp_pos).le) hW) (hde).le), mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos rp) rm)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le hD) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sm_pos).le (F.S.hp_pos).le) hW) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sm_pos).le (F.S.kp_pos).le) hD) (hde).le), mul_pos ((mul_pos (mul_pos F.S.sm_pos rp) hQ)) hde, mul_pos ((mul_pos (mul_pos hsm1 rp) hQ)) hde]
  · linarith only [(sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.tm_pos htm1)) hal, mul_pos ((mul_pos htm1 htm1)) hal, mul_pos ((mul_pos htm1 hsm1)) hga, mul_pos ((mul_pos F.S.hm_pos F.S.km_pos)) hde]
  · linarith only [mul_nonneg ((mul_pos F.S.tp_pos hsp1)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos htp1 hsp1)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos htm1 F.S.sm_pos)).le (sub_nonneg.2 n1_1), mul_pos ((mul_pos (mul_pos F.S.tm_pos F.S.km_pos) hQ)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le hW) (hQ).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (htm1).le hW) (hQ).le) (hde).le), mul_pos ((mul_pos (mul_pos F.S.sm_pos F.S.hm_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos hsm1 F.S.hm_pos) hQ)) hde]
  · linarith only [mul_nonneg (F.S.tm_pos).le (sub_nonneg.2 n1_1), (sub_nonneg.2 n1_2), mul_pos ((mul_pos F.S.sp_pos F.S.sp_pos)) hal, mul_pos ((mul_pos F.S.sp_pos hsp1)) hal, mul_pos ((mul_pos hsp1 hsp1)) hal, mul_pos ((mul_pos F.S.tm_pos F.S.sm_pos)) hbe, mul_pos ((mul_pos htm1 hsm1)) hga, mul_pos ((mul_pos F.S.hm_pos F.S.km_pos)) hde]
  · linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n1_3), mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.kp_pos F.S.km_pos)) hde]
  · linarith only [mul_nonneg ((mul_pos F.S.sp_pos hsp1)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos hsp1 hsp1)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos htm1 F.S.sm_pos)).le (sub_nonneg.2 n1_3), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le (hQ).le) hCm) (hde).le), mul_pos ((mul_pos (mul_pos htp1 F.S.km_pos) hQ)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le (hQ).le) hCm) (hde).le), mul_pos ((mul_pos (mul_pos hsm1 F.S.hp_pos) hQ)) hde]
  · linarith only [mul_nonneg (F.S.hm_pos).le (sub_nonneg.2 n1_3), (mul_nonneg hW (sub_nonneg.2 n1_3)), mul_nonneg (hA1r).le (sub_nonneg.2 n1_3), mul_pos ((mul_pos F.S.tp_pos hQ)) hal, mul_pos ((mul_pos htp1 hQ)) hal, mul_pos ((mul_pos F.S.tm_pos hA1r)) hal, mul_pos ((mul_pos htm1 F.S.kp_pos)) hal, mul_pos ((mul_pos hsp1 F.S.hm_pos)) hal, mul_pos ((mul_pos F.S.sm_pos F.S.hm_pos)) hbe, (mul_nonneg (mul_nonneg (F.S.sm_pos).le hW) (hbe).le), mul_pos ((mul_pos F.S.sm_pos hA1r)) hbe]


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
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_0, rperm_1, rperm_2, rperm_3, rperm_4, rperm_5, rperm_6, Shape20.u_vRa4, Shape20.u_xX] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4
  · linarith only [(sub_nonneg.2 n1_1), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, (mul_nonneg (mul_nonneg (F.S.tp_pos).le hCm) (hal).le), (mul_nonneg (mul_nonneg (htp1).le hCm) (hal).le), mul_pos ((mul_pos hsm1 F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos htm1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, (mul_nonneg (mul_nonneg (hsp1).le hCm) (hbe).le)]
  · linarith only [(sub_nonneg.2 n0_4), mul_pos ((mul_pos (mul_pos F.S.tp_pos htm1) F.S.sm_pos)) hbe, mul_pos ((mul_pos (mul_pos htp1 htm1) F.S.sm_pos)) hbe, mul_pos ((mul_pos (mul_pos htp1 htm1) F.S.sm_pos)) hga, mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.hm_pos) hQ)) hde, mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.kp_pos) rm)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le hW) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le (hQ).le) hD) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le (F.S.kp_pos).le) hW) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le hW) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le (hQ).le) hD) (hde).le), mul_pos ((mul_pos (mul_pos F.S.tm_pos F.S.hp_pos) hQ)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le hW) (hQ).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le (hQ).le) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (htm1).le hW) (hQ).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.hp_pos).le) hW) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.km_pos).le) hD) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sm_pos).le (F.S.kp_pos).le) hD) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sm_pos).le hD) (hA1r).le) (hde).le), mul_pos ((mul_pos (mul_pos hsm1 F.S.hp_pos) hQ)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (hsm1).le hD) (hA1r).le) (hde).le)]
  · linarith only [(sub_nonneg.2 n0_4), mul_pos ((mul_pos (mul_pos F.S.tp_pos htm1) F.S.sm_pos)) hbe, mul_pos ((mul_pos (mul_pos htp1 htm1) F.S.sm_pos)) hbe, mul_pos ((mul_pos (mul_pos htp1 htm1) F.S.sm_pos)) hga, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le hW) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le hW) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le (F.S.kp_pos).le) hW) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le hW) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le hW) hA3) (hde).le), mul_pos ((mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) rm)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.hp_pos).le) hW) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le hW) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le hD) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le hW) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le hD) (hA1r).le) (hde).le), mul_pos ((mul_pos (mul_pos hsm1 F.S.hp_pos) hQ)) hde]
  · linarith only [(sub_nonneg.2 n1_3), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, (mul_nonneg (mul_nonneg (F.S.tp_pos).le hCm) (hal).le), (mul_nonneg (mul_nonneg (htp1).le hCm) (hal).le), mul_pos ((mul_pos hsm1 F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos htm1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, (mul_nonneg (mul_nonneg (hsp1).le hCm) (hbe).le)]
  · linarith only [(sub_nonneg.2 n0_4), mul_pos ((mul_pos htm1 F.S.sm_pos)) hbe, mul_pos ((mul_pos (mul_pos htp1 htm1) F.S.sm_pos)) hga, (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le (F.S.kp_pos).le) hW) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.hp_pos).le) hW) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.km_pos).le) hW) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.km_pos).le) hD) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le hW) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le hW) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le hD) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le hW) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le hW) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le hW) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le hD) (hA1r).le) (hde).le), mul_pos ((mul_pos (mul_pos hsm1 F.S.hp_pos) hQ)) hde]
  · linarith only [(sub_nonneg.2 n1_1), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, (mul_nonneg (mul_nonneg (F.S.tp_pos).le hCm) (hal).le), (mul_nonneg (mul_nonneg (htp1).le hCm) (hal).le), mul_pos ((mul_pos hsm1 F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos htm1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, (mul_nonneg (mul_nonneg (hsp1).le hCm) (hbe).le)]
  · linarith only [mul_nonneg ((mul_pos F.S.tp_pos F.S.km_pos)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos F.S.tp_pos hA1r)).le (sub_nonneg.2 n0_1), (mul_nonneg (mul_nonneg (F.S.tp_pos).le hA3) (sub_nonneg.2 n0_2)), (mul_nonneg (mul_nonneg (htp1).le hA3) (sub_nonneg.2 n0_2)), mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos (mul_pos F.S.tp_pos htm1) F.S.kp_pos)) hal, mul_pos ((mul_pos (mul_pos F.S.tp_pos htm1) hA1r)) hal, mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.sm_pos) F.S.hm_pos)) hal, mul_pos ((mul_pos (mul_pos F.S.tp_pos F.S.sm_pos) hQ)) hal, mul_pos ((mul_pos (mul_pos htp1 htm1) hA1r)) hal, mul_pos ((mul_pos (mul_pos htp1 F.S.sp_pos) F.S.hm_pos)) hal, mul_pos ((mul_pos (mul_pos htp1 F.S.sp_pos) rm)) hal, (mul_nonneg (mul_nonneg (mul_nonneg (htm1).le (hsp1).le) hCm) (hal).le), (mul_nonneg (mul_nonneg (mul_nonneg (htm1).le (hsm1).le) hA3) (hal).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.sp_pos).le) hW) (hal).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (hsp1).le) hW) (hal).le), mul_pos ((mul_pos (mul_pos F.S.sp_pos hsm1) F.S.hm_pos)) hal, mul_pos ((mul_pos (mul_pos htp1 F.S.sp_pos) rm)) hbe, mul_pos ((mul_pos (mul_pos htm1 F.S.sm_pos) hA1r)) hbe, (mul_nonneg (mul_nonneg (mul_nonneg (htm1).le (F.S.sm_pos).le) hCm) (hbe).le), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (hsm1).le) hD) (hbe).le), mul_pos ((mul_pos (mul_pos F.S.km_pos rp) rm)) hde]
  · linarith only [mul_nonneg ((mul_pos (mul_pos F.S.tp_pos F.S.sp_pos) F.S.km_pos)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos F.S.tp_pos F.S.sp_pos) hA1r)).le (sub_nonneg.2 n0_1), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tp_pos).le (F.S.sp_pos).le) hA3) (sub_nonneg.2 n0_2)), (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le (F.S.sp_pos).le) hA3) (sub_nonneg.2 n0_2)), mul_nonneg ((mul_pos htm1 F.S.sm_pos)).le (sub_nonneg.2 n1_1), mul_pos ((mul_pos (mul_pos (mul_pos htp1 F.S.kp_pos) F.S.km_pos) hQ)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (htp1).le (F.S.kp_pos).le) (F.S.km_pos).le) hD) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.tm_pos).le (F.S.hm_pos).le) (hA1r).le) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (htm1).le (F.S.hm_pos).le) (hA1r).le) hA3) (hde).le), mul_pos ((mul_pos (mul_pos (mul_pos htm1 F.S.km_pos) hA1r) hA1r)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) F.S.hp_pos) rm)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) F.S.km_pos) hQ)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.hp_pos).le) hW) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.hp_pos).le) hW) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.hp_pos).le) hD) (hA1r).le) (hde).le), mul_pos ((mul_pos (mul_pos (mul_pos F.S.sp_pos F.S.hm_pos) F.S.kp_pos) F.S.km_pos)) hde, mul_pos ((mul_pos (mul_pos (mul_pos F.S.sp_pos F.S.hm_pos) F.S.km_pos) hA1r)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.hm_pos).le) (F.S.km_pos).le) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.kp_pos).le) hW) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.kp_pos).le) hD) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.km_pos).le) hW) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le (F.S.hp_pos).le) hD) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le (F.S.hm_pos).le) (F.S.kp_pos).le) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le (F.S.kp_pos).le) hW) hCm) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le (F.S.kp_pos).le) hD) hCm) (hde).le), mul_pos ((mul_pos (mul_pos (mul_pos F.S.sm_pos F.S.hm_pos) F.S.kp_pos) hA1r)) hde, (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sm_pos).le (F.S.hm_pos).le) (F.S.kp_pos).le) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sm_pos).le (F.S.kp_pos).le) hW) (hA1r).le) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sm_pos).le (F.S.kp_pos).le) hW) hA3) (hde).le), (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hsm1).le (F.S.kp_pos).le) hW) hA3) (hde).le)]
  · linarith only [(sub_nonneg.2 n1_3), mul_pos ((mul_pos F.S.tp_pos hA1r)) hal, (mul_nonneg (mul_nonneg (F.S.tp_pos).le hCm) (hal).le), (mul_nonneg (mul_nonneg (htp1).le hCm) (hal).le), mul_pos ((mul_pos hsm1 F.S.hp_pos)) hal, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos htm1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, (mul_nonneg (mul_nonneg (hsp1).le hCm) (hbe).le)]
  · linarith only [(mul_nonneg (mul_nonneg (hsp1).le hCm) (sub_nonneg.2 n0_1)), mul_nonneg ((mul_pos (mul_pos F.S.tp_pos hsp1) hA1r)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos htp1 F.S.sp_pos) F.S.km_pos)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos htp1 F.S.sp_pos) hA1r)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos htp1 hsp1) hA1r)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos F.S.sm_pos hsm1) rp)).le (sub_nonneg.2 n0_1), mul_nonneg ((mul_pos (mul_pos hsm1 hsm1) rp)).le (sub_nonneg.2 n0_1), (mul_nonneg (mul_nonneg (mul_nonneg (F.S.sp_pos).le (hsp1).le) hA3) (sub_nonneg.2 n0_2)), (mul_nonneg (mul_nonneg (mul_nonneg (hsp1).le (hsp1).le) hA3) (sub_nonneg.2 n0_2)), mul_nonneg ((mul_pos htm1 F.S.sm_pos)).le (sub_nonneg.2 n1_3), mul_pos ((mul_pos (mul_pos F.S.km_pos rp) hQ)) hde]


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
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
  · linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hA1r hss)) hbe, mul_pos ((mul_pos hsm1 rp)) hga]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hA1r hss)) hbe]
  · linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hVpR)) hbe, mul_pos ((mul_pos hA1r hss)) hbe, mul_pos ((mul_pos hsm1 rp)) hga]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hA1r hss)) hbe]
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_4)), mul_pos F.S.hp_pos hnu, (mul_nonneg (mul_nonneg (htp1).le hKb) (hga).le), mul_pos ((mul_pos hsm1 rp)) hga]
  · linarith only [(sub_nonneg.2 n0_3), mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n1_4), hnu, mul_pos ((mul_pos F.S.sp_pos hsm1)) hbe, mul_pos ((mul_pos htp1 F.S.sp_pos)) hga]
  · linarith only [mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hsp1).le (sub_nonneg.2 n0_3), mul_pos htp1 hnu, mul_pos F.S.tm_pos hnu, mul_pos hss hnu]
  · linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n2_4), mul_pos hVpR hnu, (mul_nonneg hKb (hnu).le)]


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
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
  · linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hVpR)) hbe, mul_pos ((mul_pos htp1 F.S.kp_pos)) hga, mul_pos ((mul_pos hsm1 rp)) hga]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hA1r hss)) hbe]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hA1r hss)) hbe]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hA1r hss)) hbe]
  · linarith only [mul_nonneg (hVpR).le (sub_nonneg.2 n0_4), mul_nonneg (hVWR).le (sub_nonneg.2 n1_4), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_4), mul_pos ((mul_pos htp1 hVpR)) hga, (mul_nonneg (mul_nonneg (htp1).le hKb) (hga).le), mul_pos ((mul_pos hsm1 rp)) hga]
  · linarith only [mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n0_4), mul_nonneg (htp1).le (sub_nonneg.2 n0_4), mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n1_4), mul_nonneg (htp1).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos htp1 F.S.sp_pos)) hga, mul_pos ((mul_pos htp1 hsp1)) hga]
  · linarith only [mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n2_4), mul_nonneg (hsm1).le (sub_nonneg.2 n2_4), mul_pos htp1 hnu, mul_pos F.S.tm_pos hnu, mul_pos hss hnu]
  · linarith only [mul_nonneg ((mul_pos F.S.tm_pos hsp1)).le (sub_nonneg.2 n1_1), mul_nonneg ((mul_pos hsp1 hss)).le (sub_nonneg.2 n1_1), mul_nonneg ((mul_pos htp1 F.S.sm_pos)).le (sub_nonneg.2 n2_2), mul_nonneg ((mul_pos htp1 hsm1)).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos (mul_pos htp1 F.S.hp_pos) rp)) hde, mul_pos ((mul_pos (mul_pos htp1 F.S.hm_pos) rp)) hde, mul_pos ((mul_pos (mul_pos F.S.sp_pos rp) hA1R)) hde, mul_pos ((mul_pos (mul_pos hsp1 rp) hA1R)) hde, mul_pos ((mul_pos (mul_pos F.S.hp_pos rp) hss)) hde]


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
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hA1r hss)) hbe]
  · linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hA1r hss)) hbe, mul_pos ((mul_pos hsm1 rp)) hga]
  · linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hA1r hss)) hbe, mul_pos ((mul_pos hsm1 rp)) hga]
  · linarith only [mul_nonneg (hVpR).le (sub_nonneg.2 n0_4), mul_nonneg (hVWR).le (sub_nonneg.2 n1_4), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_4), mul_pos ((mul_pos htp1 hVWR)) hga, mul_pos ((mul_pos hsm1 rp)) hga]
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_4)), mul_nonneg (F.S.hp_pos).le hnu1, (mul_nonneg (mul_nonneg (htp1).le hKb) (hga).le), mul_pos ((mul_pos hsm1 rp)) hga]
  · linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n2_4), mul_nonneg (htm1).le (sub_nonneg.2 n2_4), mul_nonneg (hss).le hnu2, mul_pos F.S.sp_pos hl]
  · linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.sm_pos).le hnu1, mul_nonneg (hsm1).le hnu1, mul_pos F.S.sp_pos hl]


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
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vN4] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
  · linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_4), mul_pos F.S.hp_pos hl, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hVpR)) hbe, mul_pos ((mul_pos hA1r hss)) hbe, mul_pos ((mul_pos htp1 F.S.kp_pos)) hga, mul_pos ((mul_pos hsm1 rp)) hga]
  · linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_2), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_4), mul_pos F.S.hp_pos hl, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 hVpR)) hbe, mul_pos ((mul_pos hA1r hss)) hbe, mul_pos ((mul_pos htp1 F.S.kp_pos)) hga, mul_pos ((mul_pos hsm1 rp)) hga]
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_4), mul_pos F.S.hp_pos hl, mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 rp)) hga]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hA1r hss)) hbe]
  · linarith only [mul_nonneg (rm).le (sub_nonneg.2 n0_3), mul_nonneg (rm).le (sub_nonneg.2 n1_4), mul_pos rm hl, mul_pos ((mul_pos hsm1 rm)) hbe, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [mul_nonneg (rm).le (sub_nonneg.2 n0_3), mul_nonneg (rm).le (sub_nonneg.2 n1_4), mul_pos rm hl, mul_pos ((mul_pos hsm1 rm)) hbe, mul_pos ((mul_pos htp1 rm)) hga]
  · linarith only [mul_nonneg (hVWR).le (sub_nonneg.2 n0_1), mul_pos hVpR hl, (mul_nonneg hKb (hl).le)]
  · linarith only [mul_nonneg (hA1R).le (sub_nonneg.2 n0_1), mul_pos hA1R hl]


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
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.hp_pos hnu, mul_pos ((mul_pos F.S.tp_pos rp)) hga, mul_pos ((mul_pos htp1 rp)) hga, (mul_nonneg (mul_nonneg (htp1).le hKb) (hga).le)]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_4)), mul_pos F.S.hp_pos hnu, (mul_nonneg (mul_nonneg (htp1).le hKb) (hga).le), mul_pos ((mul_pos hsm1 rp)) hga]
  · linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_4), mul_pos F.S.hp_pos hnu, mul_pos ((mul_pos F.S.tp_pos rp)) hga, mul_pos ((mul_pos htp1 rp)) hga, (mul_nonneg (mul_nonneg (htp1).le hKb) (hga).le)]
  · linarith only [mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hsp1).le (sub_nonneg.2 n0_3), mul_pos F.S.sp_pos hnu, mul_pos hsp1 hnu]
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_1)), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos F.S.tp_pos rp)) hal, mul_pos ((mul_pos F.S.tp_pos rp)) hga, (mul_nonneg (mul_nonneg (htp1).le hKb) (hga).le)]


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
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
  · linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos htp1 F.S.kp_pos)) hga, mul_pos ((mul_pos hsm1 rp)) hga]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 rp)) hga]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · linarith only [(sub_nonneg.2 n0_4), mul_nonneg (F.S.tp_pos).le (sub_nonneg.2 n1_4), mul_nonneg (htp1).le (sub_nonneg.2 n1_4), mul_pos ((mul_pos F.S.tp_pos htp1)) hga, mul_pos ((mul_pos htp1 htp1)) hga]
  · linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n1_4), mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n2_4), mul_nonneg (hsp1).le (sub_nonneg.2 n2_4), mul_pos ((mul_pos hsp1 F.S.sm_pos)) hga, mul_pos ((mul_pos F.S.kp_pos F.S.km_pos)) hde]
  · linarith only [(sub_nonneg.2 n2_3), mul_pos F.S.sp_pos hnu, mul_pos hsp1 hnu]
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_1)), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos F.S.tp_pos rp)) hal, mul_pos ((mul_pos F.S.tp_pos rp)) hga, (mul_nonneg (mul_nonneg (htp1).le hKb) (hga).le)]


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
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
  · linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos hsm1 rp)) hga]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n0_1), (mul_nonneg hKb (sub_nonneg.2 n0_2)), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_4), mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos F.S.sm_pos hA1r)) hbe, mul_pos ((mul_pos hsm1 hA1r)) hbe, mul_pos ((mul_pos hsm1 rp)) hga]
  · linarith only [mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n0_1), mul_nonneg (hsp1).le (sub_nonneg.2 n0_1), mul_nonneg (F.S.sp_pos).le (sub_nonneg.2 n0_2), mul_nonneg (hsp1).le (sub_nonneg.2 n0_4), (sub_nonneg.2 n2_4), mul_pos ((mul_pos F.S.sm_pos hsm1)) hbe, mul_pos ((mul_pos hsm1 hsm1)) hbe, mul_pos ((mul_pos F.S.tp_pos hsp1)) hga]
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_4)), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_3), (mul_nonneg (mul_nonneg (htp1).le hKb) (hga).le), mul_pos ((mul_pos hsm1 rp)) hga]
  · linarith only [mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_4), mul_nonneg (F.S.hp_pos).le hnu1, mul_pos ((mul_pos F.S.tp_pos rp)) hga, mul_pos ((mul_pos htp1 rp)) hga, (mul_nonneg (mul_nonneg (htp1).le hKb) (hga).le)]
  · linarith only [mul_nonneg (hsp1).le (sub_nonneg.2 n0_3), mul_nonneg (F.S.sm_pos).le (sub_nonneg.2 n2_3), mul_nonneg (hsm1).le (sub_nonneg.2 n2_3), mul_pos F.S.sp_pos hl]
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_1)), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos F.S.tp_pos rp)) hal, mul_pos ((mul_pos F.S.tp_pos rp)) hga, (mul_nonneg (mul_nonneg (htp1).le hKb) (hga).le)]


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
  all_goals
    obtain ⟨n0_1, n0_2, n0_3, n0_4⟩ := n0
    obtain ⟨n1_1, n1_2, n1_3, n1_4⟩ := n1
    obtain ⟨n2_1, n2_2, n2_3, n2_4⟩ := n2
    try simp only [rFrame_dep] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
    simp only [C3.rimg, rFrame_S, Shape20.swap, Frame20.dep, Frame20.GG_eq, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_4, F.ptC_5, F.ptC_6, rperm_1, rperm_3, rperm_4, rperm_6, Shape20.u_tP, Shape20.u_tA, Shape20.u_vRv] at n0_1 n0_2 n0_3 n0_4 n1_1 n1_2 n1_3 n1_4 n2_1 n2_2 n2_3 n2_4
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · linarith only [mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n0_2), mul_pos ((mul_pos F.S.tp_pos hA1r)) hbe, mul_pos ((mul_pos htp1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe]
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n1_1)), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_2), mul_pos ((mul_pos F.S.tp_pos rp)) hal, mul_pos ((mul_pos F.S.tp_pos rp)) hga, (mul_nonneg (mul_nonneg (htp1).le hKb) (hga).le)]
  · linarith only [mul_nonneg (rp).le (sub_nonneg.2 n0_3), mul_nonneg (rp).le (sub_nonneg.2 n1_4), mul_pos rp hl, mul_pos ((mul_pos hsm1 rp)) hbe, mul_pos ((mul_pos htp1 rp)) hga]
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n0_3)), mul_nonneg (F.S.kp_pos).le (sub_nonneg.2 n1_4), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_3), mul_pos F.S.hp_pos hl, (mul_nonneg hKb (hl).le), mul_pos ((mul_pos F.S.tm_pos hA1r)) hbe, mul_pos ((mul_pos htm1 hA1r)) hbe, mul_pos ((mul_pos F.S.sp_pos F.S.km_pos)) hbe, mul_pos ((mul_pos htp1 F.S.kp_pos)) hga]
  · linarith only [(sub_nonneg.2 n0_1), mul_pos F.S.tm_pos hl, mul_pos htm1 hl]
  · linarith only [(mul_nonneg hKb (sub_nonneg.2 n0_3)), mul_nonneg (F.S.hp_pos).le (sub_nonneg.2 n2_4), (mul_nonneg hKb (hl).le), (mul_nonneg (mul_nonneg (hsm1).le hKb) (hbe).le), (mul_nonneg (mul_nonneg (htp1).le hKb) (hga).le), mul_pos ((mul_pos F.S.sm_pos rp)) hga]

end Minimality.CaseC20

