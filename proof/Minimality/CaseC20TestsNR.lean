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

theorem vN4_mid2 (S : Shape20) (hV : 0 < -S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.tm - S.kp*S.tm) (hVW : 0 < -S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.sp + S.hp*S.tm - S.hp - S.kp*S.tm + S.kp) :
    ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      (⟨0, S.sp, S.kp⟩ : C3).x = (⟨0, 1, 0⟩ : C3).x + s * ((⟨S.tp, 0, S.hp⟩ : C3).x - (⟨0, 1, 0⟩ : C3).x) + δ * S.u_vN4.x ∧
      (⟨0, S.sp, S.kp⟩ : C3).y = (⟨0, 1, 0⟩ : C3).y + s * ((⟨S.tp, 0, S.hp⟩ : C3).y - (⟨0, 1, 0⟩ : C3).y) + δ * S.u_vN4.y ∧
      (⟨0, S.sp, S.kp⟩ : C3).z = (⟨0, 1, 0⟩ : C3).z + s * ((⟨S.tp, 0, S.hp⟩ : C3).z - (⟨0, 1, 0⟩ : C3).z) + δ * S.u_vN4.z := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  have hD : 0 < S.kp*S.tp := by linarith [(mul_pos S.tp_pos S.kp_pos)]
  have hD0 : S.kp*S.tp ≠ 0 := hD.ne'
  have hN : 0 < -S.kp*S.sp*S.tp + S.kp*S.tp := by linarith [(mul_pos (mul_pos S.tp_pos hsp1) S.kp_pos)]
  have hDN : 0 < S.kp*S.sp*S.tp := by linarith [(mul_pos (mul_pos S.tp_pos S.sp_pos) S.kp_pos)]
  have hd : 0 < S.kp*S.tp := by linarith [(mul_pos S.tp_pos S.kp_pos)]
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = (-S.kp*S.sp*S.tp + S.kp*S.tp) / (S.kp*S.tp) := ⟨_, rfl⟩
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = (-S.kp*S.tp) / (S.kp*S.tp) := ⟨_, rfl⟩
  have hs : s * (S.kp*S.tp) = -S.kp*S.sp*S.tp + S.kp*S.tp := by rw [hsdef]; exact div_mul_cancel₀ _ hD0
  have hδ : δ * (S.kp*S.tp) = -S.kp*S.tp := by rw [hδdef]; exact div_mul_cancel₀ _ hD0
  refine ⟨s, δ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsdef]; exact div_pos hN hD
  · rw [hsdef, div_lt_one hD]; linarith
  · intro h0
    have h1 : S.kp*S.tp = 0 := by
      have : δ * (S.kp*S.tp) = 0 := by rw [h0]; ring
      linarith
    linarith
  · have h : ((⟨0, S.sp, S.kp⟩ : C3).x - ((⟨0, 1, 0⟩ : C3).x + s * ((⟨S.tp, 0, S.hp⟩ : C3).x - (⟨0, 1, 0⟩ : C3).x) + δ * (S.u_vN4).x)) * (S.kp*S.tp) = 0 := by
      simp only [Shape20.u_vN4]
      linear_combination (-(S.tp)) * hs + (-(-S.sp*S.tp + S.tp)) * hδ
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hD0)
  · have h : ((⟨0, S.sp, S.kp⟩ : C3).y - ((⟨0, 1, 0⟩ : C3).y + s * ((⟨S.tp, 0, S.hp⟩ : C3).y - (⟨0, 1, 0⟩ : C3).y) + δ * (S.u_vN4).y)) * (S.kp*S.tp) = 0 := by
      simp only [Shape20.u_vN4]
      linear_combination (-(-1)) * hs + (-(0)) * hδ
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hD0)
  · have h : ((⟨0, S.sp, S.kp⟩ : C3).z - ((⟨0, 1, 0⟩ : C3).z + s * ((⟨S.tp, 0, S.hp⟩ : C3).z - (⟨0, 1, 0⟩ : C3).z) + δ * (S.u_vN4).z)) * (S.kp*S.tp) = 0 := by
      simp only [Shape20.u_vN4]
      linear_combination (-(S.hp)) * hs + (-(-S.hp*S.sp + S.hp - S.kp)) * hδ
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hD0)

/-- `V` of class `N4` (non-realizable): Rupert if its rim is robustly unimodal and it has no horizontal double normal at its view. -/
theorem Frame20.vN4 {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x) (hV : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm - F.S.kp*F.S.tm) (hVW : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.sp + F.S.hp*F.S.tm - F.S.hp - F.S.kp*F.S.tm + F.S.kp)
    (hA : F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 3 ∨ F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 6 ∨ F.dep F.S.u_vN4 4 < F.dep F.S.u_vN4 3 ∨ F.dep F.S.u_vN4 4 < F.dep F.S.u_vN4 6) (hB : F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 0 ∨ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 0 ∨ F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 4 ∨ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 4)
    (hnd : NoHDNAt (Finset.univ.image x) (F.toFrame7.fvC F.S.u_vN4)) :
    IsRupert (Finset.univ.image x) := by
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  have hz : IsRobustUnimodal (quad (F.toFrame7.GG (F.toFrame7.ptC 0) F.S.u_vN4) (F.toFrame7.GG (F.toFrame7.ptC 3) F.S.u_vN4)
      (F.toFrame7.GG (F.toFrame7.ptC 4) F.S.u_vN4) (F.toFrame7.GG (F.toFrame7.ptC 6) F.S.u_vN4)) :=
    robust_quad_of_nws (by simpa only [Frame20.dep] using hA) (by simpa only [Frame20.dep] using hB)
  refine F.toFrame7.vertex4 hx 0 3 4 6 _ _ _ _ (F.ptC_0) (F.ptC_3) (F.ptC_4) (F.ptC_6) ({5, 1, 2} : Finset (Fin 7)) ?_ 1 (Or.inl rfl) F.S.u_vN4 (Or.inl (by simp only [Shape20.u_vN4]; intro h0; linarith [(mul_pos F.S.tp_pos hsp1), h0])) (vN4_pcyc F.S hV hVW) ?_ ?_ hnd ?_
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl <;> decide
  · intro j' hjM h0 h1 h2 h3
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · exact absurd (by simp) hjM
    · exact absurd (by simp) hjM
    · exact absurd rfl h1
    · exact absurd rfl h2
    · exact absurd (by simp) hjM
    · exact absurd rfl h3
  · simpa only [F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using hz
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
    rcases hm with rfl | rfl | rfl
    · obtain ⟨s, δ, hs0, hs1, hδ, ex, ey, ez⟩ := vN4_mid5 F.S hV hVW
      refine ⟨0, s, δ, hs0, hs1, hδ, ?_, ?_, ?_⟩ <;>
        simp only [b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3, F.ptC_5, F.ptC_0, F.ptC_3, Shape20.u_vN4] at ex ey ez ⊢ <;>
        linarith
    · obtain ⟨s, δ, hs0, hs1, hδ, ex, ey, ez⟩ := vN4_mid1 F.S hV hVW
      refine ⟨0, s, δ, hs0, hs1, hδ, ?_, ?_, ?_⟩ <;>
        simp only [b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3, F.ptC_1, F.ptC_0, F.ptC_3, Shape20.u_vN4] at ex ey ez ⊢ <;>
        linarith
    · obtain ⟨s, δ, hs0, hs1, hδ, ex, ey, ez⟩ := vN4_mid2 F.S hV hVW
      refine ⟨3, s, δ, hs0, hs1, hδ, ?_, ?_, ?_⟩ <;>
        simp only [b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3, F.ptC_2, F.ptC_6, F.ptC_0, Shape20.u_vN4] at ex ey ez ⊢ <;>
        linarith

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

/-- `T_A` for `b+ < a-` (non-realizable), along the slide of the circle of the face `0135`. -/
theorem Frame20.tANR {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x) (hA1 : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm)
    (hA : F.dep F.S.u_tANR 0 < F.dep F.S.u_tANR 6 ∨ F.dep F.S.u_tANR 0 < F.dep F.S.u_tANR 3 ∨ F.dep F.S.u_tANR 4 < F.dep F.S.u_tANR 6 ∨ F.dep F.S.u_tANR 4 < F.dep F.S.u_tANR 3) (hB : F.dep F.S.u_tANR 6 < F.dep F.S.u_tANR 0 ∨ F.dep F.S.u_tANR 3 < F.dep F.S.u_tANR 0 ∨ F.dep F.S.u_tANR 6 < F.dep F.S.u_tANR 4 ∨ F.dep F.S.u_tANR 3 < F.dep F.S.u_tANR 4)
    (hnd : ∃ᶠ η in 𝓝[>] (0 : ℝ), NoHDNAt (Finset.univ.image x) (F.toFrame7.fvC (C3.slide F.S.u_tANR ⟨0, 0, -1⟩ η))) :
    IsRupert (Finset.univ.image x) := by
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  have hcev := (tANR_pcyc F.S hA1).ev ⟨0, 0, -1⟩
  have hrev2 := (tANR_prest2 F.S hA1).ev ⟨0, 0, -1⟩
  have hmev5 := tANR_mid5 F.S hA1
  have hmev1 := tANR_mid1 F.S hA1
  have hzev : ∀ᶠ η in 𝓝[>] (0 : ℝ), IsRobustUnimodal (quad (F.dep (C3.slide F.S.u_tANR ⟨0, 0, -1⟩ η) 0) (F.dep (C3.slide F.S.u_tANR ⟨0, 0, -1⟩ η) 6) (F.dep (C3.slide F.S.u_tANR ⟨0, 0, -1⟩ η) 4) (F.dep (C3.slide F.S.u_tANR ⟨0, 0, -1⟩ η) 3)) := by
    have h0 := Q4_ev_strict (z := quad (F.dep F.S.u_tANR 0) (F.dep F.S.u_tANR 6) (F.dep F.S.u_tANR 4) (F.dep F.S.u_tANR 3)) (w := quad (F.dep ⟨0, 0, -1⟩ 0) (F.dep ⟨0, 0, -1⟩ 6) (F.dep ⟨0, 0, -1⟩ 4) (F.dep ⟨0, 0, -1⟩ 3))
      (by simpa only [quad_0, quad_1, quad_2, quad_3] using hA)
      (by simpa only [quad_0, quad_1, quad_2, quad_3] using hB)
    filter_upwards [h0] with η hη
    obtain ⟨hA', hB'⟩ := hη
    simp only [quad_0, quad_1, quad_2, quad_3] at hA' hB'
    simp only [Frame20.dep_slide]
    exact robust_quad_of_nws hA' hB'
  obtain ⟨η, hnd', hc, hr2, hm5, hm1, hz⟩ := (hnd.and_eventually ((hcev).and ((hrev2).and ((hmev5).and ((hmev1).and (hzev)))))).exists
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  refine F.toFrame7.vertex4 hx 0 6 4 3 _ _ _ _ (F.ptC_0) (F.ptC_6) (F.ptC_4) (F.ptC_3) ({5, 1} : Finset (Fin 7)) ?_ 1 (Or.inl rfl) (C3.slide F.S.u_tANR ⟨0, 0, -1⟩ η) ?_ hc ?_ ?_ hnd' ?_
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl <;> decide
  · exact (Or.inl (by simp only [C3.slide, Shape20.u_tANR]; intro h0; linarith [htp1, h0]))
  · intro j' hjM h0 h1 h2 h3
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · exact absurd (by simp) hjM
    · rw [F.ptC_2]; exact hr2
    · exact absurd rfl h3
    · exact absurd rfl h2
    · exact absurd (by simp) hjM
    · exact absurd rfl h1
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using hz
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · obtain ⟨s, δ, hs0, hs1, hδ, ex, ey, ez⟩ := hm5
      refine ⟨3, s, δ, hs0, hs1, hδ, ?_, ?_, ?_⟩ <;>
        simp only [b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3, F.ptC_5, F.ptC_3, F.ptC_0] at ex ey ez ⊢ <;>
        linarith
    · obtain ⟨s, δ, hs0, hs1, hδ, ex, ey, ez⟩ := hm1
      refine ⟨3, s, δ, hs0, hs1, hδ, ?_, ?_, ?_⟩ <;>
        simp only [b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3, F.ptC_1, F.ptC_3, F.ptC_0] at ex ey ez ⊢ <;>
        linarith

end Minimality.CaseC20

end
