module

public import Minimality.CaseC20Bridge
public import Minimality.CaseC20ST
public import Minimality.CaseC20NR

@[expose] public section

/-!
# Type 20, acute case (c): the non-realizable tests

* `vN4` : `V` of class `N4` (rim `(m1+, m1-, m2-, xb)`), at its own view, through the vertex bridge
  `Frame7.vertex4` (Theorem 18.1 in its tie form): the `v`, `xa`, `m2+` project onto the sides, the
  rim is robustly unimodal, and `V`'s closing has no horizontal double normal at the view (`hnd`).
* `tANR` : `T_A = 0135/016-1` for `b+ < a-` (non-realizable: the far end of `0135` from the line
  `m1+ xa` is `m1-`).  Along the circle of `0135` (the slide `u + η (0, 0, -1)`, `η → 0+`) the face
  `0135` stays edge-on with `v` and `xa` over the open chord `(m1+, m1-)`, and the rim
  `(m1+, xb, m2-, m1-)` keeps its tests; the set is Rupert if the rim is robustly unimodal at `u` and
  the closing has no horizontal double normal at the slid views for arbitrarily small `η`
  (`∃ᶠ η in 𝓝[>] 0`, the persistent double normals of `FEWER-FACES-PROOFS.md` 27.71 Step 2 and 4).
-/

namespace Minimality.CaseC20

open Finset Filter Minimality.CaseC09 Minimality.CaseC18
open scoped RealInnerProductSpace Topology

namespace Shape20
variable (S : Shape20)

/-- the view of `vN4` -/
def u_vN4 : C3 := ⟨-S.sp*S.tp + S.tp, 0, -S.hp*S.sp + S.hp - S.kp⟩

end Shape20

theorem vN4_pcyc (S : Shape20) (hV : 0 < -S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.tm - S.kp*S.tm) (hVW : 0 < -S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.sp + S.hp*S.tm - S.hp - S.kp*S.tm + S.kp) :
    PCyc4 1 S.u_vN4 (⟨S.tp, 0, S.hp⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [PS, Dc, C3.sub, Shape20.u_vN4]; linarith [(mul_pos S.sm_pos rp), (mul_pos S.sm_pos hVW)]),
    (by simp only [PS, Dc, C3.sub, Shape20.u_vN4]; linarith [hV, (mul_pos S.tp_pos S.kp_pos)]),
    (by simp only [PS, Dc, C3.sub, Shape20.u_vN4]; refine pos_of_pos_mul htm1 ?_; linarith [(mul_pos (mul_pos S.tp_pos hsp1) rm), (mul_pos (mul_pos S.tm_pos hsm1) hVW)]),
    (by simp only [PS, Dc, C3.sub, Shape20.u_vN4]; linarith [(mul_pos S.sm_pos rp), (mul_pos S.sm_pos hVW)]),
    (by simp only [PS, Dc, C3.sub, Shape20.u_vN4]; linarith [(mul_pos (mul_pos S.tp_pos hsp1) S.km_pos), (mul_pos (mul_pos S.tp_pos hsm1) S.kp_pos)]),
    (by simp only [PS, Dc, C3.sub, Shape20.u_vN4]; refine pos_of_pos_mul htm1 ?_; linarith [(mul_pos (mul_pos S.tp_pos hsp1) rm), (mul_pos (mul_pos S.tm_pos hsm1) hVW)]),
    (by simp only [PS, Dc, C3.sub, Shape20.u_vN4]; linarith [hV, (mul_pos S.tp_pos S.kp_pos)]),
    (by simp only [PS, Dc, C3.sub, Shape20.u_vN4]; linarith [(mul_pos (mul_pos S.tp_pos hsp1) S.km_pos), (mul_pos (mul_pos S.tp_pos hsm1) S.kp_pos)])⟩

theorem vN4_mid5 (S : Shape20) (hV : 0 < -S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.tm - S.kp*S.tm) (hVW : 0 < -S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.sp + S.hp*S.tm - S.hp - S.kp*S.tm + S.kp) :
    ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      (⟨0, 0, 0⟩ : C3).x = (⟨S.tp, 0, S.hp⟩ : C3).x + s * ((⟨S.tm, 0, -S.hm⟩ : C3).x - (⟨S.tp, 0, S.hp⟩ : C3).x) + δ * S.u_vN4.x ∧
      (⟨0, 0, 0⟩ : C3).y = (⟨S.tp, 0, S.hp⟩ : C3).y + s * ((⟨S.tm, 0, -S.hm⟩ : C3).y - (⟨S.tp, 0, S.hp⟩ : C3).y) + δ * S.u_vN4.y ∧
      (⟨0, 0, 0⟩ : C3).z = (⟨S.tp, 0, S.hp⟩ : C3).z + s * ((⟨S.tm, 0, -S.hm⟩ : C3).z - (⟨S.tp, 0, S.hp⟩ : C3).z) + δ * S.u_vN4.z := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  have hD : 0 < -S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.tm - S.kp*S.tm + S.kp*S.tp := by linarith [hV, (mul_pos S.tp_pos S.kp_pos)]
  have hD0 : -S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.tm - S.kp*S.tm + S.kp*S.tp ≠ 0 := hD.ne'
  have hN : 0 < S.kp*S.tp := by linarith [(mul_pos S.tp_pos S.kp_pos)]
  have hDN : 0 < -S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.tm - S.kp*S.tm := by linarith [hV]
  have hd : 0 < S.hm*S.tp + S.hp*S.tm := by linarith [(mul_pos S.tp_pos S.hm_pos), (mul_pos S.tm_pos S.hp_pos)]
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = (S.kp*S.tp) / (-S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.tm - S.kp*S.tm + S.kp*S.tp) := ⟨_, rfl⟩
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = (-S.hm*S.tp - S.hp*S.tm) / (-S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.tm - S.kp*S.tm + S.kp*S.tp) := ⟨_, rfl⟩
  have hs : s * (-S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.tm - S.kp*S.tm + S.kp*S.tp) = S.kp*S.tp := by rw [hsdef]; exact div_mul_cancel₀ _ hD0
  have hδ : δ * (-S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.tm - S.kp*S.tm + S.kp*S.tp) = -S.hm*S.tp - S.hp*S.tm := by rw [hδdef]; exact div_mul_cancel₀ _ hD0
  refine ⟨s, δ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsdef]; exact div_pos hN hD
  · rw [hsdef, div_lt_one hD]; linarith
  · intro h0
    have h1 : S.hm*S.tp + S.hp*S.tm = 0 := by
      have : δ * (-S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.tm - S.kp*S.tm + S.kp*S.tp) = 0 := by rw [h0]; ring
      linarith
    linarith
  · have h : ((⟨0, 0, 0⟩ : C3).x - ((⟨S.tp, 0, S.hp⟩ : C3).x + s * ((⟨S.tm, 0, -S.hm⟩ : C3).x - (⟨S.tp, 0, S.hp⟩ : C3).x) + δ * (S.u_vN4).x)) * (-S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.tm - S.kp*S.tm + S.kp*S.tp) = 0 := by
      simp only [Shape20.u_vN4]
      linear_combination (-(S.tm - S.tp)) * hs + (-(-S.sp*S.tp + S.tp)) * hδ
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hD0)
  · have h : ((⟨0, 0, 0⟩ : C3).y - ((⟨S.tp, 0, S.hp⟩ : C3).y + s * ((⟨S.tm, 0, -S.hm⟩ : C3).y - (⟨S.tp, 0, S.hp⟩ : C3).y) + δ * (S.u_vN4).y)) * (-S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.tm - S.kp*S.tm + S.kp*S.tp) = 0 := by
      simp only [Shape20.u_vN4]
      linear_combination (-(0)) * hs + (-(0)) * hδ
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hD0)
  · have h : ((⟨0, 0, 0⟩ : C3).z - ((⟨S.tp, 0, S.hp⟩ : C3).z + s * ((⟨S.tm, 0, -S.hm⟩ : C3).z - (⟨S.tp, 0, S.hp⟩ : C3).z) + δ * (S.u_vN4).z)) * (-S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.tm - S.kp*S.tm + S.kp*S.tp) = 0 := by
      simp only [Shape20.u_vN4]
      linear_combination (-(-S.hm - S.hp)) * hs + (-(-S.hp*S.sp + S.hp - S.kp)) * hδ
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hD0)

theorem vN4_mid1 (S : Shape20) (hV : 0 < -S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.tm - S.kp*S.tm) (hVW : 0 < -S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.sp + S.hp*S.tm - S.hp - S.kp*S.tm + S.kp) :
    ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      (⟨1, 0, 0⟩ : C3).x = (⟨S.tp, 0, S.hp⟩ : C3).x + s * ((⟨S.tm, 0, -S.hm⟩ : C3).x - (⟨S.tp, 0, S.hp⟩ : C3).x) + δ * S.u_vN4.x ∧
      (⟨1, 0, 0⟩ : C3).y = (⟨S.tp, 0, S.hp⟩ : C3).y + s * ((⟨S.tm, 0, -S.hm⟩ : C3).y - (⟨S.tp, 0, S.hp⟩ : C3).y) + δ * S.u_vN4.y ∧
      (⟨1, 0, 0⟩ : C3).z = (⟨S.tp, 0, S.hp⟩ : C3).z + s * ((⟨S.tm, 0, -S.hm⟩ : C3).z - (⟨S.tp, 0, S.hp⟩ : C3).z) + δ * S.u_vN4.z := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  have hD : 0 < -S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.tm - S.kp*S.tm + S.kp*S.tp := by linarith [hV, (mul_pos S.tp_pos S.kp_pos)]
  have hD0 : -S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.tm - S.kp*S.tm + S.kp*S.tp ≠ 0 := hD.ne'
  have hN : 0 < -S.hp*S.sp + S.hp + S.kp*S.tp - S.kp := by linarith [rp]
  have hDN : 0 < -S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.sp + S.hp*S.tm - S.hp - S.kp*S.tm + S.kp := by linarith [hVW]
  have hd : 0 < -S.hm*S.tp + S.hm - S.hp*S.tm + S.hp := by linarith [(mul_pos htp1 S.hm_pos), (mul_pos htm1 S.hp_pos)]
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = (-S.hp*S.sp + S.hp + S.kp*S.tp - S.kp) / (-S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.tm - S.kp*S.tm + S.kp*S.tp) := ⟨_, rfl⟩
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = (-S.hm*S.tp + S.hm - S.hp*S.tm + S.hp) / (-S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.tm - S.kp*S.tm + S.kp*S.tp) := ⟨_, rfl⟩
  have hs : s * (-S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.tm - S.kp*S.tm + S.kp*S.tp) = -S.hp*S.sp + S.hp + S.kp*S.tp - S.kp := by rw [hsdef]; exact div_mul_cancel₀ _ hD0
  have hδ : δ * (-S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.tm - S.kp*S.tm + S.kp*S.tp) = -S.hm*S.tp + S.hm - S.hp*S.tm + S.hp := by rw [hδdef]; exact div_mul_cancel₀ _ hD0
  refine ⟨s, δ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsdef]; exact div_pos hN hD
  · rw [hsdef, div_lt_one hD]; linarith
  · intro h0
    have h1 : -S.hm*S.tp + S.hm - S.hp*S.tm + S.hp = 0 := by
      have : δ * (-S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.tm - S.kp*S.tm + S.kp*S.tp) = 0 := by rw [h0]; ring
      linarith
    linarith
  · have h : ((⟨1, 0, 0⟩ : C3).x - ((⟨S.tp, 0, S.hp⟩ : C3).x + s * ((⟨S.tm, 0, -S.hm⟩ : C3).x - (⟨S.tp, 0, S.hp⟩ : C3).x) + δ * (S.u_vN4).x)) * (-S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.tm - S.kp*S.tm + S.kp*S.tp) = 0 := by
      simp only [Shape20.u_vN4]
      linear_combination (-(S.tm - S.tp)) * hs + (-(-S.sp*S.tp + S.tp)) * hδ
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hD0)
  · have h : ((⟨1, 0, 0⟩ : C3).y - ((⟨S.tp, 0, S.hp⟩ : C3).y + s * ((⟨S.tm, 0, -S.hm⟩ : C3).y - (⟨S.tp, 0, S.hp⟩ : C3).y) + δ * (S.u_vN4).y)) * (-S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.tm - S.kp*S.tm + S.kp*S.tp) = 0 := by
      simp only [Shape20.u_vN4]
      linear_combination (-(0)) * hs + (-(0)) * hδ
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hD0)
  · have h : ((⟨1, 0, 0⟩ : C3).z - ((⟨S.tp, 0, S.hp⟩ : C3).z + s * ((⟨S.tm, 0, -S.hm⟩ : C3).z - (⟨S.tp, 0, S.hp⟩ : C3).z) + δ * (S.u_vN4).z)) * (-S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.tm - S.kp*S.tm + S.kp*S.tp) = 0 := by
      simp only [Shape20.u_vN4]
      linear_combination (-(-S.hm - S.hp)) * hs + (-(-S.hp*S.sp + S.hp - S.kp)) * hδ
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hD0)

namespace Shape20
variable (S : Shape20)

/-- the view of `tANR` (the slide starts here) -/
def u_tANR : C3 := ⟨S.tp - 1, 0, S.hp⟩

end Shape20

theorem tANR_pcyc (S : Shape20) (hA1 : 0 < -S.hm*S.tp + S.hm - S.hp*S.tm) :
    PCyc4 1 S.u_tANR (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨S.tm, 0, -S.hm⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [PS, Dc, C3.sub, Shape20.u_tANR]; linarith [(mul_pos htp1 S.km_pos), (mul_pos hsm1 S.hp_pos)]),
    (by simp only [PS, Dc, C3.sub, Shape20.u_tANR]; linarith [S.hp_pos, hA1]),
    (by simp only [PS, Dc, C3.sub, Shape20.u_tANR]; linarith [(mul_pos htp1 rm), (mul_pos (mul_pos htp1 S.tm_pos) S.km_pos), (mul_pos (mul_pos S.tm_pos hsm1) S.hp_pos)]),
    (by simp only [PS, Dc, C3.sub, Shape20.u_tANR]; linarith [(mul_pos htp1 S.km_pos), (mul_pos hsm1 S.hp_pos)]),
    (by simp only [PS, Dc, C3.sub, Shape20.u_tANR]; linarith [(mul_pos S.sm_pos S.hp_pos), (mul_pos S.sm_pos hA1)]),
    (by simp only [PS, Dc, C3.sub, Shape20.u_tANR]; linarith [(mul_pos htp1 rm), (mul_pos (mul_pos htp1 S.tm_pos) S.km_pos), (mul_pos (mul_pos S.tm_pos hsm1) S.hp_pos)]),
    (by simp only [PS, Dc, C3.sub, Shape20.u_tANR]; linarith [S.hp_pos, hA1]),
    (by simp only [PS, Dc, C3.sub, Shape20.u_tANR]; linarith [(mul_pos S.sm_pos S.hp_pos), (mul_pos S.sm_pos hA1)])⟩

theorem tANR_prest2 (S : Shape20) (hA1 : 0 < -S.hm*S.tp + S.hm - S.hp*S.tm) :
    PRest4 1 S.u_tANR (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨S.tm, 0, -S.hm⟩ ⟨0, S.sp, S.kp⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [PS, Dc, C3.sub, Shape20.u_tANR]; linarith [rp]),
    (by simp only [PS, Dc, C3.sub, Shape20.u_tANR]; linarith [(mul_pos (mul_pos htp1 hsp1) S.km_pos), (mul_pos (mul_pos htp1 hsm1) S.kp_pos)]),
    (by simp only [PS, Dc, C3.sub, Shape20.u_tANR]; linarith [(mul_pos (mul_pos htp1 S.sp_pos) rm), (mul_pos (mul_pos htp1 S.sm_pos) S.kp_pos), (mul_pos (mul_pos hsp1 S.sm_pos) hA1), (mul_pos (mul_pos (mul_pos htp1 S.tm_pos) S.sp_pos) S.km_pos), (mul_pos (mul_pos (mul_pos S.tm_pos S.sp_pos) hsm1) S.hp_pos)]),
    (by simp only [PS, Dc, C3.sub, Shape20.u_tANR]; linarith [(mul_pos (mul_pos htp1 S.sp_pos) S.hm_pos), (mul_pos (mul_pos htm1 S.sp_pos) S.hp_pos)])⟩

theorem tANR_mid5 (S : Shape20) (hA1 : 0 < -S.hm*S.tp + S.hm - S.hp*S.tm) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      (⟨0, 0, 0⟩ : C3).x = (⟨S.tm, 0, -S.hm⟩ : C3).x + s * ((⟨S.tp, 0, S.hp⟩ : C3).x - (⟨S.tm, 0, -S.hm⟩ : C3).x) + δ * (C3.slide S.u_tANR ⟨0, 0, -1⟩ η).x ∧
      (⟨0, 0, 0⟩ : C3).y = (⟨S.tm, 0, -S.hm⟩ : C3).y + s * ((⟨S.tp, 0, S.hp⟩ : C3).y - (⟨S.tm, 0, -S.hm⟩ : C3).y) + δ * (C3.slide S.u_tANR ⟨0, 0, -1⟩ η).y ∧
      (⟨0, 0, 0⟩ : C3).z = (⟨S.tm, 0, -S.hm⟩ : C3).z + s * ((⟨S.tp, 0, S.hp⟩ : C3).z - (⟨S.tm, 0, -S.hm⟩ : C3).z) + δ * (C3.slide S.u_tANR ⟨0, 0, -1⟩ η).z := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  filter_upwards [eventually_pos_affine (A := -S.hm*S.tp + S.hm - S.hp*S.tm + S.hp) (B := S.tm - S.tp) (Or.inl (by linarith [S.hp_pos, hA1])),
    eventually_pos_affine (A := -S.hm*S.tp + S.hm - S.hp*S.tm) (B := S.tm) (Or.inl (by linarith [hA1])),
    eventually_pos_affine (A := S.hp) (B := -S.tp) (Or.inl (by linarith [S.hp_pos])),
    eventually_pos_affine (A := S.hm*S.tp + S.hp*S.tm) (B := 0) (Or.inl (by linarith [(mul_pos S.tp_pos S.hm_pos), (mul_pos S.tm_pos S.hp_pos)]))] with η hD hN hDN hd
  have hD0 : (-S.hm*S.tp + S.hm - S.hp*S.tm + S.hp + η * (S.tm - S.tp)) ≠ 0 := hD.ne'
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = ((-S.hm*S.tp + S.hm - S.hp*S.tm + η * (S.tm))) / ((-S.hm*S.tp + S.hm - S.hp*S.tm + S.hp + η * (S.tm - S.tp))) := ⟨_, rfl⟩
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = (S.hm*S.tp + S.hp*S.tm) / ((-S.hm*S.tp + S.hm - S.hp*S.tm + S.hp + η * (S.tm - S.tp))) := ⟨_, rfl⟩
  have hs : s * ((-S.hm*S.tp + S.hm - S.hp*S.tm + S.hp + η * (S.tm - S.tp))) = (-S.hm*S.tp + S.hm - S.hp*S.tm + η * (S.tm)) := by rw [hsdef]; exact div_mul_cancel₀ _ hD0
  have hδ : δ * ((-S.hm*S.tp + S.hm - S.hp*S.tm + S.hp + η * (S.tm - S.tp))) = S.hm*S.tp + S.hp*S.tm := by rw [hδdef]; exact div_mul_cancel₀ _ hD0
  refine ⟨s, δ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsdef]; exact div_pos (by linarith) hD
  · rw [hsdef, div_lt_one hD]; linarith
  · intro h0
    have h1 : S.hm*S.tp + S.hp*S.tm = 0 := by
      have : δ * ((-S.hm*S.tp + S.hm - S.hp*S.tm + S.hp + η * (S.tm - S.tp))) = 0 := by rw [h0]; ring
      linarith
    linarith
  · have h : ((⟨0, 0, 0⟩ : C3).x - ((⟨S.tm, 0, -S.hm⟩ : C3).x + s * ((⟨S.tp, 0, S.hp⟩ : C3).x - (⟨S.tm, 0, -S.hm⟩ : C3).x) + δ * (C3.slide S.u_tANR ⟨0, 0, -1⟩ η).x)) * ((-S.hm*S.tp + S.hm - S.hp*S.tm + S.hp + η * (S.tm - S.tp))) = 0 := by
      simp only [C3.slide, Shape20.u_tANR]
      linear_combination (-(-S.tm + S.tp)) * hs + (-(S.tp - 1)) * hδ
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hD0)
  · have h : ((⟨0, 0, 0⟩ : C3).y - ((⟨S.tm, 0, -S.hm⟩ : C3).y + s * ((⟨S.tp, 0, S.hp⟩ : C3).y - (⟨S.tm, 0, -S.hm⟩ : C3).y) + δ * (C3.slide S.u_tANR ⟨0, 0, -1⟩ η).y)) * ((-S.hm*S.tp + S.hm - S.hp*S.tm + S.hp + η * (S.tm - S.tp))) = 0 := by
      simp only [C3.slide, Shape20.u_tANR]
      linear_combination (-(0)) * hs + (-(0)) * hδ
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hD0)
  · have h : ((⟨0, 0, 0⟩ : C3).z - ((⟨S.tm, 0, -S.hm⟩ : C3).z + s * ((⟨S.tp, 0, S.hp⟩ : C3).z - (⟨S.tm, 0, -S.hm⟩ : C3).z) + δ * (C3.slide S.u_tANR ⟨0, 0, -1⟩ η).z)) * ((-S.hm*S.tp + S.hm - S.hp*S.tm + S.hp + η * (S.tm - S.tp))) = 0 := by
      simp only [C3.slide, Shape20.u_tANR]
      linear_combination (-(S.hm + S.hp)) * hs + (-(-η + S.hp)) * hδ
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hD0)

theorem tANR_mid1 (S : Shape20) (hA1 : 0 < -S.hm*S.tp + S.hm - S.hp*S.tm) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      (⟨1, 0, 0⟩ : C3).x = (⟨S.tm, 0, -S.hm⟩ : C3).x + s * ((⟨S.tp, 0, S.hp⟩ : C3).x - (⟨S.tm, 0, -S.hm⟩ : C3).x) + δ * (C3.slide S.u_tANR ⟨0, 0, -1⟩ η).x ∧
      (⟨1, 0, 0⟩ : C3).y = (⟨S.tm, 0, -S.hm⟩ : C3).y + s * ((⟨S.tp, 0, S.hp⟩ : C3).y - (⟨S.tm, 0, -S.hm⟩ : C3).y) + δ * (C3.slide S.u_tANR ⟨0, 0, -1⟩ η).y ∧
      (⟨1, 0, 0⟩ : C3).z = (⟨S.tm, 0, -S.hm⟩ : C3).z + s * ((⟨S.tp, 0, S.hp⟩ : C3).z - (⟨S.tm, 0, -S.hm⟩ : C3).z) + δ * (C3.slide S.u_tANR ⟨0, 0, -1⟩ η).z := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  filter_upwards [eventually_pos_affine (A := -S.hm*S.tp + S.hm - S.hp*S.tm + S.hp) (B := S.tm - S.tp) (Or.inl (by linarith [S.hp_pos, hA1])),
    eventually_pos_affine (A := -S.hm*S.tp + S.hm - S.hp*S.tm + S.hp) (B := S.tm - 1) (Or.inl (by linarith [S.hp_pos, hA1])),
    eventually_pos_affine (A := 0) (B := -S.tp + 1) (Or.inr ⟨rfl, by linarith [htp1]⟩),
    eventually_pos_affine (A := -S.hm*S.tp + S.hm - S.hp*S.tm + S.hp) (B := 0) (Or.inl (by linarith [S.hp_pos, hA1]))] with η hD hN hDN hd
  have hD0 : (-S.hm*S.tp + S.hm - S.hp*S.tm + S.hp + η * (S.tm - S.tp)) ≠ 0 := hD.ne'
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = ((-S.hm*S.tp + S.hm - S.hp*S.tm + S.hp + η * (S.tm - 1))) / ((-S.hm*S.tp + S.hm - S.hp*S.tm + S.hp + η * (S.tm - S.tp))) := ⟨_, rfl⟩
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = (S.hm*S.tp - S.hm + S.hp*S.tm - S.hp) / ((-S.hm*S.tp + S.hm - S.hp*S.tm + S.hp + η * (S.tm - S.tp))) := ⟨_, rfl⟩
  have hs : s * ((-S.hm*S.tp + S.hm - S.hp*S.tm + S.hp + η * (S.tm - S.tp))) = (-S.hm*S.tp + S.hm - S.hp*S.tm + S.hp + η * (S.tm - 1)) := by rw [hsdef]; exact div_mul_cancel₀ _ hD0
  have hδ : δ * ((-S.hm*S.tp + S.hm - S.hp*S.tm + S.hp + η * (S.tm - S.tp))) = S.hm*S.tp - S.hm + S.hp*S.tm - S.hp := by rw [hδdef]; exact div_mul_cancel₀ _ hD0
  refine ⟨s, δ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsdef]; exact div_pos (by linarith) hD
  · rw [hsdef, div_lt_one hD]; linarith
  · intro h0
    have h1 : -S.hm*S.tp + S.hm - S.hp*S.tm + S.hp = 0 := by
      have : δ * ((-S.hm*S.tp + S.hm - S.hp*S.tm + S.hp + η * (S.tm - S.tp))) = 0 := by rw [h0]; ring
      linarith
    linarith
  · have h : ((⟨1, 0, 0⟩ : C3).x - ((⟨S.tm, 0, -S.hm⟩ : C3).x + s * ((⟨S.tp, 0, S.hp⟩ : C3).x - (⟨S.tm, 0, -S.hm⟩ : C3).x) + δ * (C3.slide S.u_tANR ⟨0, 0, -1⟩ η).x)) * ((-S.hm*S.tp + S.hm - S.hp*S.tm + S.hp + η * (S.tm - S.tp))) = 0 := by
      simp only [C3.slide, Shape20.u_tANR]
      linear_combination (-(-S.tm + S.tp)) * hs + (-(S.tp - 1)) * hδ
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hD0)
  · have h : ((⟨1, 0, 0⟩ : C3).y - ((⟨S.tm, 0, -S.hm⟩ : C3).y + s * ((⟨S.tp, 0, S.hp⟩ : C3).y - (⟨S.tm, 0, -S.hm⟩ : C3).y) + δ * (C3.slide S.u_tANR ⟨0, 0, -1⟩ η).y)) * ((-S.hm*S.tp + S.hm - S.hp*S.tm + S.hp + η * (S.tm - S.tp))) = 0 := by
      simp only [C3.slide, Shape20.u_tANR]
      linear_combination (-(0)) * hs + (-(0)) * hδ
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hD0)
  · have h : ((⟨1, 0, 0⟩ : C3).z - ((⟨S.tm, 0, -S.hm⟩ : C3).z + s * ((⟨S.tp, 0, S.hp⟩ : C3).z - (⟨S.tm, 0, -S.hm⟩ : C3).z) + δ * (C3.slide S.u_tANR ⟨0, 0, -1⟩ η).z)) * ((-S.hm*S.tp + S.hm - S.hp*S.tm + S.hp + η * (S.tm - S.tp))) = 0 := by
      simp only [C3.slide, Shape20.u_tANR]
      linear_combination (-(S.hm + S.hp)) * hs + (-(-η + S.hp)) * hδ
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hD0)

end Minimality.CaseC20

end
