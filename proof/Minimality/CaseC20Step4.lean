module

public import Minimality.CaseC18Step4
public import Minimality.CaseC20VSlide

@[expose] public section

/-!
# Type 20: Theorem 27.41 / 27.71 Step 4 (`V` and `T_A` on the hyperplane `ClassH`)

`FEWER-FACES-PROOFS.md` Theorem 27.41 Step 4 and Theorem 27.71 Step 4.  The summary is at the end.

Dictionary type 18 -> type 20 for `V` (frame coordinates are literally the same points):
`xa 3 -> 1, xb 4 -> 6, m1+ 0 -> 0, m1- 6 -> 3, m2+ 1 -> 2, m2- 2 -> 4, v 5 -> 5`;
`Shape20.u_vN4` is `Shape18.uV`, so `dV j` becomes `F.dep F.S.u_vN4 j'`.

* `V` (view `u_vN4`): `Delta = (m1+, m2+, xb) = 026`, slide `u + eta eD`, `eD = m1+ - xb`; removed set `{m2+}` (2);
  slide rim = pentagon `pent 0 5 3 4 6 = (m1+, v, m1-, m2-, xb)`; rest point `xa` (1).
* `T_A` (view `u_tANR = m1+ - xa`): the triangle `016 = (m1+, xa, xb)` contains the view, slide
  `u + eta eT`, `eT = xb - m1+` (the sign that hides `xa`: `xa = (1-eta) m1+ + eta xb - u_eta`);
  removed set `{xa}` (1); slide rim = pentagon `pent 0 6 4 3 5 = (m1+, xb, m2-, m1-, v)` (the reverse of V's,
  as `tANR`'s `quad 0 6 4 3` is the reverse of `quad 0 3 4 6`); rest point `m2+` (2).
-/

namespace Minimality.CaseC20

open Finset Filter Minimality.CaseC09 Minimality.CaseC18
open scoped RealInnerProductSpace Topology

/-! ### Shape-level data -/

namespace Shape20
variable (S : Shape20)

/-- `V`'s positivity quantity (`Vp` of type 18): the hypothesis `hV` of `vN4_slide`. -/
noncomputable def Vq : ℝ :=
  -S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.tm - S.kp*S.tm

/-- `Vp - Wp`: the hypothesis `hVW` of `vN4_slide`. -/
noncomputable def VWq : ℝ :=
  -S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.sp + S.hp*S.tm - S.hp - S.kp*S.tm + S.kp

/-- `-D2p` of type 18 (`D2p < 0`, the pentagon rim `N4`).  In type 20 it is automatic from `hV`, `hVW` and
the lower roof: `(1 - tm) D2n = tp (1 - sp) (km (1 - tm) - hm (1 - sm)) + tm (1 - sm) VWq`. -/
noncomputable def D2n : ℝ :=
  -S.hm * S.sm * S.sp * S.tp - S.hp * S.sm * S.sp * S.tm + S.hm * S.sm * S.tp + S.hm * S.sp * S.tp +
    S.hp * S.sm * S.tm + S.hp * S.sp * S.tm - S.km * S.sp * S.tp - S.kp * S.sm * S.tm -
    S.hm * S.tp - S.hp * S.tm + S.km * S.tp + S.kp * S.tm

/-- `V`'s slide direction on `Delta = 026`'s circle: `m1+ - xb` (as `Shape18.eD`). -/
def eD : C3 := ⟨S.tp, -1, S.hp⟩

/-- `T_A`'s slide direction on `016`'s circle: `xb - m1+` (hides `xa` exactly). -/
def eT : C3 := ⟨-S.tp, 1, -S.hp⟩

theorem D2n_pos (hV : 0 < S.Vq) (hVW : 0 < S.VWq) : 0 < S.D2n := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  have key : (1 - S.tm) * S.D2n = S.tp * (1 - S.sp) * (S.km * (1 - S.tm) - S.hm * (1 - S.sm)) +
      S.tm * (1 - S.sm) * S.VWq := by
    unfold D2n VWq; ring
  have : 0 < (1 - S.tm) * S.D2n := by
    rw [key]
    have := mul_pos (mul_pos htp hsp1) rm
    have := mul_pos (mul_pos htm hsm1) hVW
    linarith
  exact pos_of_mul_pos_right this htm1.le

/-- **V, pentagon `(m1+, v, m1-, m2-, xb)` along `eD`**: all 15 tests are strict for small `eta > 0`
(copy of `Shape18.N4D_cyc_ev_S`; `hD2` is `D2n_pos`). -/
theorem N4D_cyc_ev_S (hV : 0 < S.Vq) (hVW : 0 < S.VWq) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      PS 1 (C3.slide S.u_vN4 S.eD η)
        ((pent (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩
            (i + 1)).sub
          (pent (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ i))
        ((pent (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ j).sub
          (pent (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ i)) := by
  have htp := S.tp_pos; have htp1 := S.tp_lt; have htm := S.tm_pos; have htm1 := S.tm_lt
  have hsp := S.sp_pos; have hsp1 := S.sp_lt; have hsm := S.sm_pos; have hsm1 := S.sm_lt
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have hV' : 0 < (1 - S.sp) * (S.hp * S.tm + S.hm * S.tp) - S.kp * S.tm := by
    have := hV; unfold Shape20.Vq at this; linarith
  have hD2 : 0 < -S.hm * S.sm * S.sp * S.tp - S.hp * S.sm * S.sp * S.tm + S.hm * S.sm * S.tp + S.hm * S.sp * S.tp + S.hp * S.sm * S.tm + S.hp * S.sp * S.tm - S.km * S.sp * S.tp - S.kp * S.sm * S.tm - S.hm * S.tp - S.hp * S.tm + S.km * S.tp + S.kp * S.tm := by
    have := S.D2n_pos hV hVW; unfold Shape20.D2n at this; linarith
  have hsp' : 0 < 1 - S.sp := sub_pos.2 hsp1
  have hsm' : 0 < 1 - S.sm := sub_pos.2 hsm1
  have f1 : 0 < S.sm * S.tp * S.kp := by positivity
  have f2 : 0 < S.tp * S.kp := by positivity
  have f3 : 0 < S.sm * ((1 - S.sp) * (S.hp * S.tm + S.hm * S.tp) - S.kp * S.tm) := by positivity
  have f5 : 0 < ((1 - S.sp) * (S.hp * S.tm + S.hm * S.tp) - S.kp * S.tm) + S.kp * S.tp := by
    have := mul_pos hkp htp; linarith
  have f4 : 0 < S.sm * (((1 - S.sp) * (S.hp * S.tm + S.hm * S.tp) - S.kp * S.tm) + S.kp * S.tp) :=
    mul_pos hsm f5
  have f6 : 0 < S.tp * (S.km * (1 - S.sp) + S.kp * (1 - S.sm)) := by positivity
  have f7 : 0 < S.km * S.tp * (1 - S.sp) := by positivity
  have f8 : 0 < S.hp * S.tm + S.hm * S.tp := by positivity
  refine eventually_forall_cycle fun i j h1 h2 => ?_
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    apply PS_ev'
    simp only [b0, b1, b2, b3, b4, pent_0, pent_1, pent_2, pent_3, pent_4, Dc, C3.sub,
      Shape20.u_vN4, Shape20.eD]
    first
    | (left; linarith [f1, f2, f3, f4, f5, f6, f7, hD2])
    | (right; exact ⟨by ring, by linarith [f8]⟩)

/-- Splitting `xa` over the chord at `u_vN4` (copy of `Shape18.Dc_xa_split`). -/
theorem Dc_xa_split (E Q : C3) (s δ : ℝ)
    (e1 : 1 = S.tp + s * (S.tm - S.tp) + δ * S.u_vN4.x)
    (e2 : 0 = S.hp + s * (-S.hm - S.hp) + δ * S.u_vN4.z) :
    Dc E ((⟨1, 0, 0⟩ : C3).sub Q) S.u_vN4 =
      (1 - s) * Dc E ((⟨S.tp, 0, S.hp⟩ : C3).sub Q) S.u_vN4 +
        s * Dc E ((⟨S.tm, 0, -S.hm⟩ : C3).sub Q) S.u_vN4 := by
  simp only [Shape20.u_vN4] at e1 e2
  simp only [Dc, C3.sub, Shape20.u_vN4]
  linear_combination (-E.y * (-S.hp * S.sp + S.hp - S.kp)) * e1 +
    (E.y * (-S.sp * S.tp + S.tp)) * e2

/-- **V, rest point `xa`** (copy of `N4D_rest_ev_S`). -/
theorem N4D_rest_ev_S (hV : 0 < S.Vq) (hVW : 0 < S.VWq) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ i : ZMod 5,
      PS 1 (C3.slide S.u_vN4 S.eD η)
        ((pent (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩
            (i + 1)).sub
          (pent (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ i))
        ((⟨1, 0, 0⟩ : C3).sub
          (pent (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ i)) := by
  have htp := S.tp_pos; have htp1 := S.tp_lt; have htm := S.tm_pos; have htm1 := S.tm_lt
  have hsp := S.sp_pos; have hsp1 := S.sp_lt; have hsm := S.sm_pos; have hsm1 := S.sm_lt
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have hV' : 0 < (1 - S.sp) * (S.hp * S.tm + S.hm * S.tp) - S.kp * S.tm := by
    have := hV; unfold Shape20.Vq at this; linarith
  have hD2 : 0 < -S.hm * S.sm * S.sp * S.tp - S.hp * S.sm * S.sp * S.tm + S.hm * S.sm * S.tp + S.hm * S.sp * S.tp + S.hp * S.sm * S.tm + S.hp * S.sp * S.tm - S.km * S.sp * S.tp - S.kp * S.sm * S.tm - S.hm * S.tp - S.hp * S.tm + S.km * S.tp + S.kp * S.tm := by
    have := S.D2n_pos hV hVW; unfold Shape20.D2n at this; linarith
  have hsp' : 0 < 1 - S.sp := sub_pos.2 hsp1
  have hsm' : 0 < 1 - S.sm := sub_pos.2 hsm1
  have f5 : 0 < ((1 - S.sp) * (S.hp * S.tm + S.hm * S.tp) - S.kp * S.tm) + S.kp * S.tp := by
    have := mul_pos hkp htp; linarith
  have f4 : 0 < S.sm * (((1 - S.sp) * (S.hp * S.tm + S.hm * S.tp) - S.kp * S.tm) + S.kp * S.tp) :=
    mul_pos hsm f5
  have f6 : 0 < S.tp * (S.km * (1 - S.sp) + S.kp * (1 - S.sm)) := by positivity
  obtain ⟨s, δ, hs0, hs1, -, e1, -, e2⟩ := vN4_mid1 S hV hVW
  have hs1' : 0 < 1 - s := sub_pos.2 hs1
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  refine eventually_all.2 fun i => ?_
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
  · apply PS_ev'
    simp only [b0, pent_0, pent_1]
    right
    exact ⟨by simp only [Dc, C3.sub, Shape20.u_vN4]; ring,
      by simp only [Dc, C3.sub, Shape20.eD]; linarith⟩
  · apply PS_ev'
    simp only [b1, pent_1, pent_2]
    right
    exact ⟨by simp only [Dc, C3.sub, Shape20.u_vN4]; ring,
      by simp only [Dc, C3.sub, Shape20.eD]; linarith⟩
  · apply PS_ev'
    simp only [b2, pent_2, pent_3]
    left
    rw [S.Dc_xa_split _ _ s δ e1 e2]
    simp only [Dc, C3.sub, Shape20.u_vN4]
    nlinarith [mul_pos hs1' f4]
  · apply PS_ev'
    simp only [b3, pent_3, pent_4]
    left
    rw [S.Dc_xa_split _ _ s δ e1 e2]
    simp only [Dc, C3.sub, Shape20.u_vN4]
    nlinarith [mul_pos hs1' f6, mul_pos hs0 hD2]
  · apply PS_ev'
    simp only [b4, pent_4, pent_0]
    left
    rw [S.Dc_xa_split _ _ s δ e1 e2]
    simp only [Dc, C3.sub, Shape20.u_vN4]
    nlinarith [mul_pos hs0 f5]

/-- **T_A, pentagon `(m1+, xb, m2-, m1-, v)` along `eT`** (view `u_tANR`): all 15 tests are positive at `eta = 0`
except `([m1-, v], m1+)` and `([v, m1+], m1-)` (F1 edge-on), whose `eta`-derivative is `hm tp + hp tm > 0`. -/
theorem TA_cyc_ev_S (hA1 : 0 < -S.hm*S.tp + S.hm - S.hp*S.tm) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      PS 1 (C3.slide S.u_tANR S.eT η)
        ((pent (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨S.tm, 0, -S.hm⟩ ⟨0, 0, 0⟩
            (i + 1)).sub
          (pent (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨S.tm, 0, -S.hm⟩ ⟨0, 0, 0⟩ i))
        ((pent (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨S.tm, 0, -S.hm⟩ ⟨0, 0, 0⟩ j).sub
          (pent (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨S.tm, 0, -S.hm⟩ ⟨0, 0, 0⟩ i)) := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  have f1 : 0 < S.hp * (1 - S.sm) := by positivity
  have f2 : 0 < S.km * (1 - S.tp) := by positivity
  have f3 : 0 < S.hm * (1 - S.tp) := by positivity
  have f4 : 0 < S.hp * (1 - S.tm) := by positivity
  have f5 : 0 < S.hm * S.sm * (1 - S.tp) := by positivity
  have f6 : 0 < S.hp * S.sm * (1 - S.tm) := by positivity
  have f7 : 0 < (1 - S.tp) * (S.km * S.tm) := by positivity
  have f8 : 0 < (1 - S.tp) * (S.km * (1 - S.tm) - S.hm * (1 - S.sm)) := mul_pos htp1 rm
  have f9 : 0 < S.hp * S.tm * (1 - S.sm) := by positivity
  have f10 : 0 < S.sm * (-S.hm*S.tp + S.hm - S.hp*S.tm) := mul_pos hsm hA1
  have f11 : 0 < S.hp * S.sm := by positivity
  have f12 : 0 < S.km * (1 - S.tp) := f2
  have f13 : 0 < S.hm * S.tp + S.hp * S.tm := by positivity
  refine eventually_forall_cycle fun i j h1 h2 => ?_
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    apply PS_ev'
    simp only [b0, b1, b2, b3, b4, pent_0, pent_1, pent_2, pent_3, pent_4, Dc, C3.sub,
      Shape20.u_tANR, Shape20.eT]
    first
    | (left; linarith [f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, hA1, hhp])
    | (right; exact ⟨by ring, by linarith [f13]⟩)

/-- **T_A, rest point `m2+`** against the pentagon sides: all five tests are strict at `eta = 0`. -/
theorem TA_rest_ev_S (hA1 : 0 < -S.hm*S.tp + S.hm - S.hp*S.tm) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ i : ZMod 5,
      PS 1 (C3.slide S.u_tANR S.eT η)
        ((pent (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨S.tm, 0, -S.hm⟩ ⟨0, 0, 0⟩
            (i + 1)).sub
          (pent (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨S.tm, 0, -S.hm⟩ ⟨0, 0, 0⟩ i))
        ((⟨0, S.sp, S.kp⟩ : C3).sub
          (pent (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨S.tm, 0, -S.hm⟩ ⟨0, 0, 0⟩ i)) := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  refine eventually_all.2 fun i => ?_
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
  · apply PS_ev'
    simp only [b0, pent_0, pent_1, Dc, C3.sub, Shape20.u_tANR]
    left; linarith [rp]
  · apply PS_ev'
    simp only [b1, pent_1, pent_2, Dc, C3.sub, Shape20.u_tANR]
    left
    linarith [(mul_pos (mul_pos htp1 hsp1) S.km_pos), (mul_pos (mul_pos htp1 hsm1) S.kp_pos)]
  · apply PS_ev'
    simp only [b2, pent_2, pent_3, Dc, C3.sub, Shape20.u_tANR]
    left
    linarith [(mul_pos (mul_pos htp1 S.sp_pos) rm), (mul_pos (mul_pos htp1 S.sm_pos) S.kp_pos),
      (mul_pos (mul_pos hsp1 S.sm_pos) hA1), (mul_pos (mul_pos (mul_pos htp1 S.tm_pos) S.sp_pos) S.km_pos),
      (mul_pos (mul_pos (mul_pos S.tm_pos S.sp_pos) hsm1) S.hp_pos)]
  · apply PS_ev'
    simp only [b3, pent_3, pent_4, Dc, C3.sub, Shape20.u_tANR]
    left
    linarith [mul_pos hsp hA1]
  · apply PS_ev'
    simp only [b4, pent_4, pent_0, Dc, C3.sub, Shape20.u_tANR]
    left
    linarith [mul_pos hhp hsp]

end Shape20

theorem four_V {d0 d3 d4 d6 : ℝ} (hA : d0 < d3 ∨ d0 < d6 ∨ d4 < d3 ∨ d4 < d6)
    (hB : d3 < d0 ∨ d6 < d0 ∨ d3 < d4 ∨ d6 < d4) (e0 : d0 = d6) (e6 : d6 = d3) : False := by
  rcases hA with h | h | h | h <;> rcases hB with h' | h' | h' | h' <;> linarith

theorem four_T {d0 d3 d4 d6 : ℝ} (hA : d0 < d6 ∨ d0 < d3 ∨ d4 < d6 ∨ d4 < d3)
    (hB : d6 < d0 ∨ d3 < d0 ∨ d6 < d4 ∨ d3 < d4) (e0 : d0 = d6) (e3 : d6 = d3) : False := by
  rcases hA with h | h | h | h <;> rcases hB with h' | h' | h' | h' <;> linarith

/-! ### Frame-level statements -/

namespace Frame20
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- The depth along `V`'s view (type 18's `dV`). -/
@[reducible] noncomputable def dV (j : Fin 7) : ℝ := F.dep F.S.u_vN4 j

/-- The depth along `T_A`'s view. -/
@[reducible] noncomputable def dT (j : Fin 7) : ℝ := F.dep F.S.u_tANR j

lemma dV_0 : F.dV 0 = F.a11 * (F.S.tp * (-F.S.sp * F.S.tp + F.S.tp)) +
    F.gg * (F.S.hp * (-F.S.hp * F.S.sp + F.S.hp - F.S.kp)) := by
  simp only [dV, dep, ptC_0, GG_eq, Shape20.u_vN4]; ring
lemma dV_3 : F.dV 3 = F.a11 * (F.S.tm * (-F.S.sp * F.S.tp + F.S.tp)) +
    F.gg * (-F.S.hm * (-F.S.hp * F.S.sp + F.S.hp - F.S.kp)) := by
  simp only [dV, dep, ptC_3, GG_eq, Shape20.u_vN4]; ring
lemma dV_4 : F.dV 4 = F.a12 * (F.S.sm * (-F.S.sp * F.S.tp + F.S.tp)) +
    F.gg * (-F.S.km * (-F.S.hp * F.S.sp + F.S.hp - F.S.kp)) := by
  simp only [dV, dep, ptC_4, GG_eq, Shape20.u_vN4]; ring
lemma dV_6 : F.dV 6 = F.a12 * (-F.S.sp * F.S.tp + F.S.tp) := by
  simp only [dV, dep, ptC_6, GG_eq, Shape20.u_vN4]; ring

lemma dT_0 : F.dT 0 = F.a11 * (F.S.tp * (F.S.tp - 1)) + F.gg * (F.S.hp * F.S.hp) := by
  simp only [dT, dep, ptC_0, GG_eq, Shape20.u_tANR]; ring
lemma dT_3 : F.dT 3 = F.a11 * (F.S.tm * (F.S.tp - 1)) + F.gg * (-F.S.hm * F.S.hp) := by
  simp only [dT, dep, ptC_3, GG_eq, Shape20.u_tANR]; ring
lemma dT_4 : F.dT 4 = F.a12 * (F.S.sm * (F.S.tp - 1)) + F.gg * (-F.S.km * F.S.hp) := by
  simp only [dT, dep, ptC_4, GG_eq, Shape20.u_tANR]; ring
lemma dT_6 : F.dT 6 = F.a12 * (F.S.tp - 1) := by
  simp only [dT, dep, ptC_6, GG_eq, Shape20.u_tANR]; ring
lemma dT_5 : F.dT 5 = 0 := by
  simp only [dT, dep, ptC_5, GG_eq, Shape20.u_tANR]; ring

/-- `m2+` (vertex 2) is hidden exactly on `V`'s slide. -/
theorem mid_m2p_D :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      (F.toFrame7.ptC 2).x = (F.toFrame7.ptC 6).x +
        s * ((F.toFrame7.ptC 0).x - (F.toFrame7.ptC 6).x) + δ * (C3.slide F.S.u_vN4 F.S.eD η).x ∧
      (F.toFrame7.ptC 2).y = (F.toFrame7.ptC 6).y +
        s * ((F.toFrame7.ptC 0).y - (F.toFrame7.ptC 6).y) + δ * (C3.slide F.S.u_vN4 F.S.eD η).y ∧
      (F.toFrame7.ptC 2).z = (F.toFrame7.ptC 6).z +
        s * ((F.toFrame7.ptC 0).z - (F.toFrame7.ptC 6).z) + δ * (C3.slide F.S.u_vN4 F.S.eD η).z := by
  have hsp := F.S.sp_pos; have hsp1 := F.S.sp_lt
  filter_upwards [Ioo_mem_nhdsGT hsp] with η hη
  refine ⟨1 - F.S.sp + η, -1, by linarith [hη.1, hη.2], by linarith [hη.1, hη.2], by norm_num,
    ?_, ?_, ?_⟩ <;>
  · simp only [F.ptC_2, F.ptC_6, F.ptC_0, C3.slide, Shape20.u_vN4, Shape20.eD]
    ring

/-- `xa` (vertex 1) is hidden exactly on `T_A`'s slide: `xa = m1+ + eta (xb - m1+) - u_eta`. -/
theorem mid_xa_T :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      (F.toFrame7.ptC 1).x = (F.toFrame7.ptC 0).x +
        s * ((F.toFrame7.ptC 6).x - (F.toFrame7.ptC 0).x) + δ * (C3.slide F.S.u_tANR F.S.eT η).x ∧
      (F.toFrame7.ptC 1).y = (F.toFrame7.ptC 0).y +
        s * ((F.toFrame7.ptC 6).y - (F.toFrame7.ptC 0).y) + δ * (C3.slide F.S.u_tANR F.S.eT η).y ∧
      (F.toFrame7.ptC 1).z = (F.toFrame7.ptC 0).z +
        s * ((F.toFrame7.ptC 6).z - (F.toFrame7.ptC 0).z) + δ * (C3.slide F.S.u_tANR F.S.eT η).z := by
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with η hη
  refine ⟨η, -1, hη.1, hη.2, by norm_num, ?_, ?_, ?_⟩ <;>
  · simp only [F.ptC_1, F.ptC_6, F.ptC_0, C3.slide, Shape20.u_tANR, Shape20.eT]
    ring

/-- **Depth order at `u_vN4` on `ClassH`** (copy of `Frame18.classH_depth_trichotomy`): with
`B = A11 tp (1 - sp)(tp - tm) + g (hp + hm)(hp (1 - sp) - kp)`,
`(hp + hm)(dep 0 - dep 6) = hp B`, `(hp + hm)(dep 6 - dep 3) = hm B`. -/
theorem classH_depth_trichotomy_V (hH : F.ClassH) :
    (F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 6 ∧ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 0) ∨
      (F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 6 ∧ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 3) ∨
      (F.dep F.S.u_vN4 0 = F.dep F.S.u_vN4 6 ∧ F.dep F.S.u_vN4 6 = F.dep F.S.u_vN4 3) := by
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos
  have hux : 0 < F.S.tp * (1 - F.S.sp) := mul_pos F.S.tp_pos (sub_pos.2 F.S.sp_lt)
  set B : ℝ := F.a11 * (F.S.tp * (1 - F.S.sp)) * (F.S.tp - F.S.tm) +
    F.gg * (F.S.hp + F.S.hm) * (F.S.hp * (1 - F.S.sp) - F.S.kp) with hB
  have hH' : F.a12 * (F.S.hp + F.S.hm) = F.a11 * (F.S.tp * F.S.hm + F.S.tm * F.S.hp) := hH
  have e1 : (F.S.hp + F.S.hm) * (F.dV 0 - F.dV 6) = F.S.hp * B := by
    rw [F.dV_0, F.dV_6, hB]
    linear_combination (-(F.S.tp * (1 - F.S.sp))) * hH'
  have e2 : (F.S.hp + F.S.hm) * (F.dV 6 - F.dV 3) = F.S.hm * B := by
    rw [F.dV_3, F.dV_6, hB]
    linear_combination (F.S.tp * (1 - F.S.sp)) * hH'
  have hs : 0 < F.S.hp + F.S.hm := by linarith
  rcases lt_trichotomy B 0 with h | h | h
  · right; left
    have a1 : F.dV 0 - F.dV 6 < 0 := by
      by_contra hh; push Not at hh
      nlinarith [mul_nonneg hs.le hh, mul_pos hhp (neg_pos.2 h)]
    have a2 : F.dV 6 - F.dV 3 < 0 := by
      by_contra hh; push Not at hh
      nlinarith [mul_nonneg hs.le hh, mul_pos hhm (neg_pos.2 h)]
    constructor <;> linarith
  · right; right
    rw [h] at e1 e2
    have a1 : F.dV 0 - F.dV 6 = 0 := by
      have := mul_eq_zero.mp (by linarith : (F.S.hp + F.S.hm) * (F.dV 0 - F.dV 6) = 0)
      rcases this with h' | h'
      · linarith
      · exact h'
    have a2 : F.dV 6 - F.dV 3 = 0 := by
      have := mul_eq_zero.mp (by linarith : (F.S.hp + F.S.hm) * (F.dV 6 - F.dV 3) = 0)
      rcases this with h' | h'
      · linarith
      · exact h'
    constructor <;> linarith
  · left
    have a1 : 0 < F.dV 0 - F.dV 6 := by
      by_contra hh; push Not at hh
      nlinarith [mul_nonneg hs.le (neg_nonneg.2 hh), mul_pos hhp h]
    have a2 : 0 < F.dV 6 - F.dV 3 := by
      by_contra hh; push Not at hh
      nlinarith [mul_nonneg hs.le (neg_nonneg.2 hh), mul_pos hhm h]
    constructor <;> linarith

/-- **Depth order at `u_tANR` on `ClassH`.**  With `B_T = A11 (tp - 1)(tp - tm) + g hp (hp + hm) = dep 0 - dep 3`:
`(hp + hm)(dep 0 - dep 6) = hp B_T` and `(hp + hm)(dep 6 - dep 3) = hm B_T`. -/
theorem classH_depth_trichotomy_T (hH : F.ClassH) :
    (F.dep F.S.u_tANR 3 < F.dep F.S.u_tANR 6 ∧ F.dep F.S.u_tANR 6 < F.dep F.S.u_tANR 0) ∨
      (F.dep F.S.u_tANR 0 < F.dep F.S.u_tANR 6 ∧ F.dep F.S.u_tANR 6 < F.dep F.S.u_tANR 3) ∨
      (F.dep F.S.u_tANR 0 = F.dep F.S.u_tANR 6 ∧ F.dep F.S.u_tANR 6 = F.dep F.S.u_tANR 3) := by
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos
  set B : ℝ := F.a11 * ((F.S.tp - 1) * (F.S.tp - F.S.tm)) + F.gg * (F.S.hp * (F.S.hp + F.S.hm)) with hB
  have hH' : F.a12 * (F.S.hp + F.S.hm) = F.a11 * (F.S.tp * F.S.hm + F.S.tm * F.S.hp) := hH
  have e1 : (F.S.hp + F.S.hm) * (F.dT 0 - F.dT 6) = F.S.hp * B := by
    rw [F.dT_0, F.dT_6, hB]
    linear_combination (-(F.S.tp - 1)) * hH'
  have e2 : (F.S.hp + F.S.hm) * (F.dT 6 - F.dT 3) = F.S.hm * B := by
    rw [F.dT_3, F.dT_6, hB]
    linear_combination (F.S.tp - 1) * hH'
  have hs : 0 < F.S.hp + F.S.hm := by linarith
  rcases lt_trichotomy B 0 with h | h | h
  · right; left
    have a1 : F.dT 0 - F.dT 6 < 0 := by
      by_contra hh; push Not at hh
      nlinarith [mul_nonneg hs.le hh, mul_pos hhp (neg_pos.2 h)]
    have a2 : F.dT 6 - F.dT 3 < 0 := by
      by_contra hh; push Not at hh
      nlinarith [mul_nonneg hs.le hh, mul_pos hhm (neg_pos.2 h)]
    constructor <;> linarith
  · right; right
    rw [h] at e1 e2
    have a1 : F.dT 0 - F.dT 6 = 0 := by
      have := mul_eq_zero.mp (by linarith : (F.S.hp + F.S.hm) * (F.dT 0 - F.dT 6) = 0)
      rcases this with h' | h'
      · linarith
      · exact h'
    have a2 : F.dT 6 - F.dT 3 = 0 := by
      have := mul_eq_zero.mp (by linarith : (F.S.hp + F.S.hm) * (F.dT 6 - F.dT 3) = 0)
      rcases this with h' | h'
      · linarith
      · exact h'
    constructor <;> linarith
  · left
    have a1 : 0 < F.dT 0 - F.dT 6 := by
      by_contra hh; push Not at hh
      nlinarith [mul_nonneg hs.le (neg_nonneg.2 hh), mul_pos hhp h]
    have a2 : 0 < F.dT 6 - F.dT 3 := by
      by_contra hh; push Not at hh
      nlinarith [mul_nonneg hs.le (neg_nonneg.2 hh), mul_pos hhm h]
    constructor <;> linarith

/-- **V: the depth-separated pair of the pentagon at `u_vN4` with nonzero torque** (copy of
`Frame18.N4D_pair`).  `hA`, `hB` exclude the level chord `B = 0`. -/
theorem N4D_pair_V (hH : F.ClassH) (hV : 0 < F.S.Vq)
    (hA : F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 3 ∨ F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 6 ∨
      F.dep F.S.u_vN4 4 < F.dep F.S.u_vN4 3 ∨ F.dep F.S.u_vN4 4 < F.dep F.S.u_vN4 6)
    (hB : F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 0 ∨ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 0 ∨
      F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 4 ∨ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 4) :
    ∃ a c : ZMod 5, DepthSepAt (fun i => x (pent 0 5 3 4 6 i)) (F.toFrame7.fvC F.S.u_vN4) a c ∧
      ⟪x (pent 0 5 3 4 6 (a + 1)) - x (pent 0 5 3 4 6 a), F.toFrame7.fvC F.S.u_vN4⟫ ≠ 0 ∧
      torque3 (fun i => x (pent 0 5 3 4 6 i)) (F.toFrame7.fvC F.S.u_vN4) a c ≠ 0 := by
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos
  have hsp1 := F.S.sp_lt; have hsm := F.S.sm_pos; have hsm1 := F.S.sm_lt
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have hgg := F.g_pos
  have hA12 : 0 < F.a12 := F.A12_pos
  have hsp' : 0 < 1 - F.S.sp := sub_pos.2 hsp1
  have hsm' : 0 < 1 - F.S.sm := sub_pos.2 hsm1
  have hV' : 0 < (1 - F.S.sp) * (F.S.hp * F.S.tm + F.S.hm * F.S.tp) - F.S.kp * F.S.tm := by
    have := hV; unfold Shape20.Vq at this; linarith
  have hux : 0 < F.S.tp * (1 - F.S.sp) := mul_pos htp hsp'
  have hd4 : 0 < F.dV 6 := by
    rw [F.dV_6, show -F.S.sp * F.S.tp + F.S.tp = F.S.tp * (1 - F.S.sp) by ring]
    exact mul_pos F.A12_pos hux
  have d5 : F.dV 5 = 0 := by simp only [dV, Frame20.dep, ptC_5, GG_eq, Shape20.u_vN4]; ring
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  have hT : 0 < F.S.tp * F.S.kp := mul_pos htp hkp
  have hVV : 0 < ((1 - F.S.sp) * (F.S.hp * F.S.tm + F.S.hm * F.S.tp) - F.S.kp * F.S.tm) := hV'
  rcases F.classH_depth_trichotomy_V hH with ⟨h6, h0⟩ | ⟨h0, h6⟩ | ⟨e0, e6⟩
  · -- `dV 3 < dV 6 < dV 0`: `a = m1+`, `c = xb`
    have h2 : F.dV 4 < F.dV 6 := by
      rcases hA with h | h | h | h <;> first | linarith | skip
    have hv : ((0 : ZMod 5) - 4).val = 1 := by decide
    have hden : F.toFrame7.GG ((F.toFrame7.ptC (pent 0 5 3 4 6 (0 + 1))).sub
        (F.toFrame7.ptC (pent 0 5 3 4 6 0))) F.S.u_vN4 ≠ 0 := by
      have : F.toFrame7.GG ((F.toFrame7.ptC (pent 0 5 3 4 6 (0 + 1))).sub
          (F.toFrame7.ptC (pent 0 5 3 4 6 0))) F.S.u_vN4 = F.dV 5 - F.dV 0 := by
        simp only [b0, pent_0, pent_1, dV, Frame20.dep, C3.sub, Shape20.u_vN4, F.ptC_0, F.ptC_5, GG_eq]; ring
      rw [this]; linarith
    refine ⟨0, 4, F.toFrame7.depthSepAt_of_frame (pent 0 5 3 4 6) F.S.u_vN4 0 4 ?_ ?_, ?_, ?_⟩
    · intro j hj
      rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl
      · simp only [b0, pent_0, pent_1, pent_4, F.ptC_0, F.ptC_5, F.ptC_6, Dc, C3.sub,
          Shape20.u_vN4]
        nlinarith [mul_pos hT hT]
      · simp only [b0, pent_0, pent_1, pent_4, F.ptC_0, F.ptC_5, F.ptC_6, Dc, C3.sub,
          Shape20.u_vN4]
        nlinarith [mul_pos hT hT]
      · simp only [b0, pent_0, pent_1, pent_2, pent_4, F.ptC_0, F.ptC_5, F.ptC_3, F.ptC_6, Dc,
          C3.sub, Shape20.u_vN4]
        nlinarith [mul_pos hT hT]
      · simp only [b0, pent_0, pent_1, pent_3, pent_4, F.ptC_0, F.ptC_5, F.ptC_4, F.ptC_6, Dc,
          C3.sub, Shape20.u_vN4]
        nlinarith [mul_pos (mul_pos hsm' hT) hT]
      · exact absurd rfl hj
    · left
      refine ⟨fun s hs hs1 => ?_, fun s hs1 hs2 => ?_⟩
      · have : s = 1 := by rw [hv] at hs1; omega
        subst this
        have e : (4 : ZMod 5) + ((1 : ℕ) : ZMod 5) = 0 := by decide
        simp only [e, pent_0, pent_4, dV, Frame20.dep, F.ptC_0, F.ptC_6] at h0 ⊢
        exact h0
      · rw [hv] at hs1
        interval_cases s
        · have e : (4 : ZMod 5) + ((2 : ℕ) : ZMod 5) = 1 := by decide
          simp only [e, pent_1, pent_4, dV, Frame20.dep, F.ptC_5, F.ptC_6] at d5 hd4 ⊢
          linarith
        · have e : (4 : ZMod 5) + ((3 : ℕ) : ZMod 5) = 2 := by decide
          simp only [e, pent_2, pent_4, dV, Frame20.dep, F.ptC_3, F.ptC_6] at h6 ⊢
          linarith
        · have e : (4 : ZMod 5) + ((4 : ℕ) : ZMod 5) = 3 := by decide
          simp only [e, pent_3, pent_4, dV, Frame20.dep, F.ptC_4, F.ptC_6] at h2 ⊢
          linarith
    · rw [F.toFrame7.x_sub, F.toFrame7.inner_fvC]; exact hden
    · rw [F.toFrame7.torque3_frame]
      have key : (F.toFrame7.GG ((F.toFrame7.ptC (pent 0 5 3 4 6 4)).sub
            (F.toFrame7.ptC (pent 0 5 3 4 6 0)))
            ((F.toFrame7.ptC (pent 0 5 3 4 6 (0 + 1))).sub (F.toFrame7.ptC (pent 0 5 3 4 6 0))) -
          (F.toFrame7.GG ((F.toFrame7.ptC (pent 0 5 3 4 6 4)).sub
            (F.toFrame7.ptC (pent 0 5 3 4 6 0))) F.S.u_vN4 /
            F.toFrame7.GG ((F.toFrame7.ptC (pent 0 5 3 4 6 (0 + 1))).sub
              (F.toFrame7.ptC (pent 0 5 3 4 6 0))) F.S.u_vN4) *
            F.toFrame7.GG ((F.toFrame7.ptC (pent 0 5 3 4 6 (0 + 1))).sub
              (F.toFrame7.ptC (pent 0 5 3 4 6 0)))
              ((F.toFrame7.ptC (pent 0 5 3 4 6 (0 + 1))).sub (F.toFrame7.ptC (pent 0 5 3 4 6 0)))) *
          F.toFrame7.GG ((F.toFrame7.ptC (pent 0 5 3 4 6 (0 + 1))).sub
            (F.toFrame7.ptC (pent 0 5 3 4 6 0))) F.S.u_vN4 =
          -(F.a12 * F.gg * F.S.hp * F.S.tp * F.S.kp) := by
        field_simp
        simp only [b0, pent_0, pent_1, pent_4, F.ptC_0, F.ptC_5, F.ptC_6, GG_eq, C3.sub,
          Shape20.u_vN4]
        ring
      intro h
      rw [h, zero_mul] at key
      have : 0 < F.a12 * F.gg * F.S.hp * F.S.tp * F.S.kp := by
        positivity
      linarith
  · -- `dV 0 < dV 6 < dV 3`: `a = v`, `c = xb`
    have h2 : F.dV 6 < F.dV 4 := by
      rcases hB with h | h | h | h <;> first | linarith | skip
    have hv : ((1 : ZMod 5) - 4).val = 2 := by decide
    have hden : F.toFrame7.GG ((F.toFrame7.ptC (pent 0 5 3 4 6 (1 + 1))).sub
        (F.toFrame7.ptC (pent 0 5 3 4 6 1))) F.S.u_vN4 ≠ 0 := by
      have : F.toFrame7.GG ((F.toFrame7.ptC (pent 0 5 3 4 6 (1 + 1))).sub
          (F.toFrame7.ptC (pent 0 5 3 4 6 1))) F.S.u_vN4 = F.dV 3 - F.dV 5 := by
        simp only [b1, pent_1, pent_2, dV, Frame20.dep, C3.sub, Shape20.u_vN4, F.ptC_3, F.ptC_5, GG_eq]; ring
      rw [this]; linarith
    refine ⟨1, 4, F.toFrame7.depthSepAt_of_frame (pent 0 5 3 4 6) F.S.u_vN4 1 4 ?_ ?_, ?_, ?_⟩
    · intro j hj
      rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl
      · simp only [b1, pent_0, pent_1, pent_2, pent_4, F.ptC_0, F.ptC_5, F.ptC_3, F.ptC_6, Dc,
          C3.sub, Shape20.u_vN4]
        nlinarith [mul_pos hVV hVV]
      · simp only [b1, pent_1, pent_2, pent_4, F.ptC_5, F.ptC_3, F.ptC_6, Dc, C3.sub,
          Shape20.u_vN4]
        nlinarith [mul_pos hVV hVV]
      · simp only [b1, pent_1, pent_2, pent_4, F.ptC_5, F.ptC_3, F.ptC_6, Dc, C3.sub,
          Shape20.u_vN4]
        nlinarith [mul_pos hVV hVV]
      · simp only [b1, pent_1, pent_2, pent_3, pent_4, F.ptC_5, F.ptC_3, F.ptC_4, F.ptC_6, Dc,
          C3.sub, Shape20.u_vN4]
        nlinarith [mul_pos (mul_pos hsm' hVV) hVV]
      · exact absurd rfl hj
    · right
      refine ⟨fun s hs hs1 => ?_, fun s hs1 hs2 => ?_⟩
      · rw [hv] at hs1
        interval_cases s
        · have e : (4 : ZMod 5) + ((1 : ℕ) : ZMod 5) = 0 := by decide
          simp only [e, pent_0, pent_4, dV, Frame20.dep, F.ptC_0, F.ptC_6] at h0 ⊢
          exact h0
        · have e : (4 : ZMod 5) + ((2 : ℕ) : ZMod 5) = 1 := by decide
          simp only [e, pent_1, pent_4, dV, Frame20.dep, F.ptC_5, F.ptC_6] at d5 hd4 ⊢
          linarith
      · rw [hv] at hs1
        interval_cases s
        · have e : (4 : ZMod 5) + ((3 : ℕ) : ZMod 5) = 2 := by decide
          simp only [e, pent_2, pent_4, dV, Frame20.dep, F.ptC_3, F.ptC_6] at h6 ⊢
          exact h6
        · have e : (4 : ZMod 5) + ((4 : ℕ) : ZMod 5) = 3 := by decide
          simp only [e, pent_3, pent_4, dV, Frame20.dep, F.ptC_4, F.ptC_6] at h2 ⊢
          exact h2
    · rw [F.toFrame7.x_sub, F.toFrame7.inner_fvC]; exact hden
    · rw [F.toFrame7.torque3_frame]
      have key : (F.toFrame7.GG ((F.toFrame7.ptC (pent 0 5 3 4 6 4)).sub
            (F.toFrame7.ptC (pent 0 5 3 4 6 1)))
            ((F.toFrame7.ptC (pent 0 5 3 4 6 (1 + 1))).sub (F.toFrame7.ptC (pent 0 5 3 4 6 1))) -
          (F.toFrame7.GG ((F.toFrame7.ptC (pent 0 5 3 4 6 4)).sub
            (F.toFrame7.ptC (pent 0 5 3 4 6 1))) F.S.u_vN4 /
            F.toFrame7.GG ((F.toFrame7.ptC (pent 0 5 3 4 6 (1 + 1))).sub
              (F.toFrame7.ptC (pent 0 5 3 4 6 1))) F.S.u_vN4) *
            F.toFrame7.GG ((F.toFrame7.ptC (pent 0 5 3 4 6 (1 + 1))).sub
              (F.toFrame7.ptC (pent 0 5 3 4 6 1)))
              ((F.toFrame7.ptC (pent 0 5 3 4 6 (1 + 1))).sub (F.toFrame7.ptC (pent 0 5 3 4 6 1)))) *
          F.toFrame7.GG ((F.toFrame7.ptC (pent 0 5 3 4 6 (1 + 1))).sub
            (F.toFrame7.ptC (pent 0 5 3 4 6 1))) F.S.u_vN4 =
          -(F.a12 * F.gg * F.S.hm * ((1 - F.S.sp) * (F.S.hp * F.S.tm + F.S.hm * F.S.tp) -
            F.S.kp * F.S.tm)) := by
        field_simp
        simp only [b1, pent_1, pent_2, pent_4, F.ptC_5, F.ptC_3, F.ptC_6, GG_eq, C3.sub,
          Shape20.u_vN4]
        ring
      intro h
      rw [h, zero_mul] at key
      have : 0 < F.a12 * F.gg * F.S.hm * ((1 - F.S.sp) * (F.S.hp * F.S.tm + F.S.hm * F.S.tp) -
          F.S.kp * F.S.tm) := by
        positivity
      linarith
  · exact (four_V hA hB e0 e6).elim

/-- **T_A: the depth-separated pair of the pentagon `(m1+, xb, m2-, m1-, v)` at `u_tANR` with nonzero torque**
(Theorem 27.71 Step 4).  `dep 5 = 0 > dep 6 = A12 (tp - 1)`, `c = xb` (index 1).
* `dep 3 < dep 6 < dep 0`: `e = [m1-, v]` (`a = 3`);
* `dep 0 < dep 6 < dep 3`: `e = [v, m1+]` (`a = 4`);
* the equal case contradicts `hA /\ hB`.
The torque satisfies `torque * G(d, u) = A12 g hm (-hm tp + hm - hp tm)` resp. `A12 g hp^2`. -/
theorem TA_pair (hH : F.ClassH) (hA1 : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm)
    (hA : F.dep F.S.u_tANR 0 < F.dep F.S.u_tANR 6 ∨ F.dep F.S.u_tANR 0 < F.dep F.S.u_tANR 3 ∨
      F.dep F.S.u_tANR 4 < F.dep F.S.u_tANR 6 ∨ F.dep F.S.u_tANR 4 < F.dep F.S.u_tANR 3)
    (hB : F.dep F.S.u_tANR 6 < F.dep F.S.u_tANR 0 ∨ F.dep F.S.u_tANR 3 < F.dep F.S.u_tANR 0 ∨
      F.dep F.S.u_tANR 6 < F.dep F.S.u_tANR 4 ∨ F.dep F.S.u_tANR 3 < F.dep F.S.u_tANR 4) :
    ∃ a c : ZMod 5, DepthSepAt (fun i => x (pent 0 6 4 3 5 i)) (F.toFrame7.fvC F.S.u_tANR) a c ∧
      ⟪x (pent 0 6 4 3 5 (a + 1)) - x (pent 0 6 4 3 5 a), F.toFrame7.fvC F.S.u_tANR⟫ ≠ 0 ∧
      torque3 (fun i => x (pent 0 6 4 3 5 i)) (F.toFrame7.fvC F.S.u_tANR) a c ≠ 0 := by
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkm := F.S.km_pos
  have hgg := F.g_pos
  have hA12 : 0 < F.a12 := F.A12_pos
  have hsm' : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have hd6 : F.dT 6 < 0 := by
    rw [F.dT_6]; nlinarith [mul_pos hA12 (sub_pos.2 F.S.tp_lt)]
  have d5 : F.dT 5 = 0 := F.dT_5
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  have hAA := mul_pos hA1 hA1
  have hAs := mul_pos (mul_pos hsm' hA1) hA1
  have hPP := mul_pos hhp hhp
  have hPs := mul_pos (mul_pos hsm' hhp) hhp
  rcases F.classH_depth_trichotomy_T hH with ⟨h3, h0⟩ | ⟨h0, h3⟩ | ⟨e0, e3⟩
  · -- `dT 3 < dT 6 < dT 0`: `e = [m1-, v]` (`a = 3`), `c = xb` (index 1)
    have h4 : F.dT 4 < F.dT 6 := by
      rcases hA with h | h | h | h <;> first | linarith | skip
    have hv : ((3 : ZMod 5) - 1).val = 2 := by decide
    have hden : F.toFrame7.GG ((F.toFrame7.ptC (pent 0 6 4 3 5 (3 + 1))).sub
        (F.toFrame7.ptC (pent 0 6 4 3 5 3))) F.S.u_tANR ≠ 0 := by
      have : F.toFrame7.GG ((F.toFrame7.ptC (pent 0 6 4 3 5 (3 + 1))).sub
          (F.toFrame7.ptC (pent 0 6 4 3 5 3))) F.S.u_tANR = F.dT 5 - F.dT 3 := by
        simp only [b3, pent_3, pent_4, dT, dep, C3.sub, Shape20.u_tANR, F.ptC_3, F.ptC_5, GG_eq]; ring
      rw [this]; linarith
    refine ⟨3, 1, F.toFrame7.depthSepAt_of_frame (pent 0 6 4 3 5) F.S.u_tANR 3 1 ?_ ?_, ?_, ?_⟩
    · intro j hj
      rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl
      · simp only [b3, pent_0, pent_1, pent_3, pent_4, F.ptC_0, F.ptC_3, F.ptC_5, F.ptC_6, Dc,
          C3.sub, Shape20.u_tANR]
        nlinarith [hAA]
      · exact absurd rfl hj
      · simp only [b3, pent_1, pent_2, pent_3, pent_4, F.ptC_4, F.ptC_3, F.ptC_5, F.ptC_6, Dc,
          C3.sub, Shape20.u_tANR]
        nlinarith [hAs]
      · simp only [b3, pent_1, pent_3, pent_4, F.ptC_3, F.ptC_5, F.ptC_6, Dc,
          C3.sub, Shape20.u_tANR]
        nlinarith [hAA]
      · simp only [b3, pent_1, pent_3, pent_4, F.ptC_3, F.ptC_5, F.ptC_6, Dc,
          C3.sub, Shape20.u_tANR]
        nlinarith [hAA]
    · right
      refine ⟨fun s hs hs1 => ?_, fun s hs1 hs2 => ?_⟩
      · rw [hv] at hs1
        interval_cases s
        · have e : (1 : ZMod 5) + ((1 : ℕ) : ZMod 5) = 2 := by decide
          simp only [e, pent_2, pent_1, dT, dep, F.ptC_4, F.ptC_6] at h4 ⊢
          exact h4
        · have e : (1 : ZMod 5) + ((2 : ℕ) : ZMod 5) = 3 := by decide
          simp only [e, pent_3, pent_1, dT, dep, F.ptC_3, F.ptC_6] at h3 ⊢
          exact h3
      · rw [hv] at hs1
        interval_cases s
        · have e : (1 : ZMod 5) + ((3 : ℕ) : ZMod 5) = 4 := by decide
          simp only [e, pent_4, pent_1, dT, dep, F.ptC_5, F.ptC_6] at d5 hd6 ⊢
          linarith
        · have e : (1 : ZMod 5) + ((4 : ℕ) : ZMod 5) = 0 := by decide
          simp only [e, pent_0, pent_1, dT, dep, F.ptC_0, F.ptC_6] at h0 ⊢
          exact h0
    · rw [F.toFrame7.x_sub, F.toFrame7.inner_fvC]; exact hden
    · rw [F.toFrame7.torque3_frame]
      have key : (F.toFrame7.GG ((F.toFrame7.ptC (pent 0 6 4 3 5 1)).sub
            (F.toFrame7.ptC (pent 0 6 4 3 5 3)))
            ((F.toFrame7.ptC (pent 0 6 4 3 5 (3 + 1))).sub (F.toFrame7.ptC (pent 0 6 4 3 5 3))) -
          (F.toFrame7.GG ((F.toFrame7.ptC (pent 0 6 4 3 5 1)).sub
            (F.toFrame7.ptC (pent 0 6 4 3 5 3))) F.S.u_tANR /
            F.toFrame7.GG ((F.toFrame7.ptC (pent 0 6 4 3 5 (3 + 1))).sub
              (F.toFrame7.ptC (pent 0 6 4 3 5 3))) F.S.u_tANR) *
            F.toFrame7.GG ((F.toFrame7.ptC (pent 0 6 4 3 5 (3 + 1))).sub
              (F.toFrame7.ptC (pent 0 6 4 3 5 3)))
              ((F.toFrame7.ptC (pent 0 6 4 3 5 (3 + 1))).sub (F.toFrame7.ptC (pent 0 6 4 3 5 3)))) *
          F.toFrame7.GG ((F.toFrame7.ptC (pent 0 6 4 3 5 (3 + 1))).sub
            (F.toFrame7.ptC (pent 0 6 4 3 5 3))) F.S.u_tANR =
          F.a12 * F.gg * F.S.hm * (-F.S.hm * F.S.tp + F.S.hm - F.S.hp * F.S.tm) := by
        field_simp
        simp only [b3, pent_1, pent_3, pent_4, F.ptC_3, F.ptC_5, F.ptC_6, GG_eq, C3.sub,
          Shape20.u_tANR]
        ring
      intro h
      rw [h, zero_mul] at key
      have : 0 < F.a12 * F.gg * F.S.hm * (-F.S.hm * F.S.tp + F.S.hm - F.S.hp * F.S.tm) :=
        mul_pos (mul_pos (mul_pos hA12 hgg) hhm) hA1
      linarith
  · -- `dT 0 < dT 6 < dT 3`: `e = [v, m1+]` (`a = 4`)
    have h4 : F.dT 6 < F.dT 4 := by
      rcases hB with h | h | h | h <;> first | linarith | skip
    have hv : ((4 : ZMod 5) - 1).val = 3 := by decide
    have hden : F.toFrame7.GG ((F.toFrame7.ptC (pent 0 6 4 3 5 (4 + 1))).sub
        (F.toFrame7.ptC (pent 0 6 4 3 5 4))) F.S.u_tANR ≠ 0 := by
      have : F.toFrame7.GG ((F.toFrame7.ptC (pent 0 6 4 3 5 (4 + 1))).sub
          (F.toFrame7.ptC (pent 0 6 4 3 5 4))) F.S.u_tANR = F.dT 0 - F.dT 5 := by
        simp only [b4, pent_4, pent_0, dT, dep, C3.sub, Shape20.u_tANR, F.ptC_0, F.ptC_5, GG_eq]; ring
      rw [this]; linarith
    refine ⟨4, 1, F.toFrame7.depthSepAt_of_frame (pent 0 6 4 3 5) F.S.u_tANR 4 1 ?_ ?_, ?_, ?_⟩
    · intro j hj
      rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl
      · simp only [b4, pent_0, pent_1, pent_4, F.ptC_0, F.ptC_5, F.ptC_6, Dc,
          C3.sub, Shape20.u_tANR]
        nlinarith [hPP]
      · exact absurd rfl hj
      · simp only [b4, pent_0, pent_1, pent_2, pent_4, F.ptC_0, F.ptC_4, F.ptC_5, F.ptC_6, Dc,
          C3.sub, Shape20.u_tANR]
        nlinarith [hPs]
      · simp only [b4, pent_0, pent_1, pent_3, pent_4, F.ptC_0, F.ptC_3, F.ptC_5, F.ptC_6, Dc,
          C3.sub, Shape20.u_tANR]
        nlinarith [hPP]
      · simp only [b4, pent_0, pent_1, pent_4, F.ptC_0, F.ptC_5, F.ptC_6, Dc,
          C3.sub, Shape20.u_tANR]
        nlinarith [hPP]
    · left
      refine ⟨fun s hs hs1 => ?_, fun s hs1 hs2 => ?_⟩
      · rw [hv] at hs1
        interval_cases s
        · have e : (1 : ZMod 5) + ((1 : ℕ) : ZMod 5) = 2 := by decide
          simp only [e, pent_2, pent_1, dT, dep, F.ptC_4, F.ptC_6] at h4 ⊢
          exact h4
        · have e : (1 : ZMod 5) + ((2 : ℕ) : ZMod 5) = 3 := by decide
          simp only [e, pent_3, pent_1, dT, dep, F.ptC_3, F.ptC_6] at h3 ⊢
          exact h3
        · have e : (1 : ZMod 5) + ((3 : ℕ) : ZMod 5) = 4 := by decide
          simp only [e, pent_4, pent_1, dT, dep, F.ptC_5, F.ptC_6] at d5 hd6 ⊢
          linarith
      · rw [hv] at hs1
        interval_cases s
        have e : (1 : ZMod 5) + ((4 : ℕ) : ZMod 5) = 0 := by decide
        simp only [e, pent_0, pent_1, dT, dep, F.ptC_0, F.ptC_6] at h0 ⊢
        exact h0
    · rw [F.toFrame7.x_sub, F.toFrame7.inner_fvC]; exact hden
    · rw [F.toFrame7.torque3_frame]
      have key : (F.toFrame7.GG ((F.toFrame7.ptC (pent 0 6 4 3 5 1)).sub
            (F.toFrame7.ptC (pent 0 6 4 3 5 4)))
            ((F.toFrame7.ptC (pent 0 6 4 3 5 (4 + 1))).sub (F.toFrame7.ptC (pent 0 6 4 3 5 4))) -
          (F.toFrame7.GG ((F.toFrame7.ptC (pent 0 6 4 3 5 1)).sub
            (F.toFrame7.ptC (pent 0 6 4 3 5 4))) F.S.u_tANR /
            F.toFrame7.GG ((F.toFrame7.ptC (pent 0 6 4 3 5 (4 + 1))).sub
              (F.toFrame7.ptC (pent 0 6 4 3 5 4))) F.S.u_tANR) *
            F.toFrame7.GG ((F.toFrame7.ptC (pent 0 6 4 3 5 (4 + 1))).sub
              (F.toFrame7.ptC (pent 0 6 4 3 5 4)))
              ((F.toFrame7.ptC (pent 0 6 4 3 5 (4 + 1))).sub (F.toFrame7.ptC (pent 0 6 4 3 5 4)))) *
          F.toFrame7.GG ((F.toFrame7.ptC (pent 0 6 4 3 5 (4 + 1))).sub
            (F.toFrame7.ptC (pent 0 6 4 3 5 4))) F.S.u_tANR =
          F.a12 * F.gg * (F.S.hp * F.S.hp) := by
        field_simp
        simp only [b4, pent_0, pent_1, pent_4, F.ptC_0, F.ptC_5, F.ptC_6, GG_eq, C3.sub,
          Shape20.u_tANR]
        ring
      intro h
      rw [h, zero_mul] at key
      have : 0 < F.a12 * F.gg * (F.S.hp * F.S.hp) :=
        mul_pos (mul_pos hA12 hgg) (mul_pos hhp hhp)
      linarith
  · exact (four_T hA hB e0 e3).elim

/-- **`V` on `ClassH`** (Theorem 27.41 Step 4 for type 20): `vN4_slide` with `F.ClassH` instead of
`¬ F.ClassH`. -/
theorem vN4_classH (hx : Function.Injective x) (hV : 0 < F.S.Vq) (hVW : 0 < F.S.VWq)
    (hA : F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 3 ∨ F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 6 ∨
      F.dep F.S.u_vN4 4 < F.dep F.S.u_vN4 3 ∨ F.dep F.S.u_vN4 4 < F.dep F.S.u_vN4 6)
    (hB : F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 0 ∨ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 0 ∨
      F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 4 ∨ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 4)
    (hH : F.ClassH) : IsRupert (Finset.univ.image x) := by
  have htp := F.S.tp_pos; have hsp1 := F.S.sp_lt
  have ux : 0 < -F.S.sp * F.S.tp + F.S.tp := by nlinarith [mul_pos htp (sub_pos.2 hsp1)]
  have efv : ∀ η : ℝ, F.toFrame7.fvC (C3.slide F.S.u_vN4 F.S.eD η) =
      F.toFrame7.fvC F.S.u_vN4 + η • F.toFrame7.fvC F.S.eD := by
    intro η; simp only [Frame7.fvC, C3.slide]; module
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  have hcomm : ∀ j : ZMod 5, F.toFrame7.ptC (pent 0 5 3 4 6 j) =
      pent (F.toFrame7.ptC 0) (F.toFrame7.ptC 5) (F.toFrame7.ptC 3) (F.toFrame7.ptC 4)
        (F.toFrame7.ptC 6) j := by
    intro j; rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;> rfl
  obtain ⟨a, c0, hds, hden, hτ⟩ := F.N4D_pair_V hH hV hA hB
  have hpos : ∀ᶠ η in 𝓝[>] (0 : ℝ), (0 : ℝ) < η := by
    filter_upwards [self_mem_nhdsWithin] with η hη using hη
  have hev := (eventually_depthSepAt (e := F.toFrame7.fvC F.S.eD) hds).and
    (eventually_torque3_ne_zero (fun i => x (pent 0 5 3 4 6 i)) (F.toFrame7.fvC F.S.u_vN4)
      (F.toFrame7.fvC F.S.eD) a c0 hden hτ)
  obtain ⟨η, hη0, hc, hr, hm, hds', -, hτ'⟩ :=
    (hpos.and ((F.S.N4D_cyc_ev_S hV hVW).and
      ((F.S.N4D_rest_ev_S hV hVW).and (F.mid_m2p_D.and hev)))).exists
  refine F.toFrame7.rupert_vertex_torque hx (k := 5) (by norm_num) (pent 0 5 3 4 6) {2} 1
    (Or.inl rfl) (C3.slide F.S.u_vN4 F.S.eD η)
    (Or.inl (ne_of_gt (by simp only [C3.slide, Shape20.u_vN4, Shape20.eD]; nlinarith [mul_pos hη0 htp]))) ?_ ?_ ?_
    (a := a) (c₀ := c0) ?_ ?_ ?_
  · intro m hm' i
    simp only [Finset.mem_singleton] at hm'
    subst hm'
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;> simp [pent_0, pent_1, pent_2, pent_3, pent_4]
  · intro i j h1 h2
    simp only [hcomm, F.ptC_0, F.ptC_5, F.ptC_3, F.ptC_4, F.ptC_6]; exact hc i j h1 h2
  · intro j' hj' hjc i
    simp only [Finset.mem_singleton] at hj'
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (by simp [pent_0]) (hjc 0)
    · simp only [hcomm, F.ptC_0, F.ptC_5, F.ptC_3, F.ptC_4, F.ptC_6, F.ptC_1]; exact hr i
    · exact absurd rfl hj'
    · exact absurd (by simp [pent_2]) (hjc 2)
    · exact absurd (by simp [pent_3]) (hjc 3)
    · exact absurd (by simp [pent_1]) (hjc 1)
    · exact absurd (by simp [pent_4]) (hjc 4)
  · rw [efv]; exact hds'
  · rw [efv]; exact hτ'
  · intro m hm'
    simp only [Finset.mem_singleton] at hm'
    subst hm'
    obtain ⟨s, δ, hs0, hs1, hδ, ex, ey, ez⟩ := hm
    refine ⟨4, s, δ, hs0, hs1, hδ, ?_, ?_, ?_⟩ <;>
      simp only [b4, pent_4, pent_0] <;> assumption

/-- **`T_A` on `ClassH`** (Theorem 27.71 Step 4): `tANR_slide` with `F.ClassH` instead of `¬ F.ClassH`. -/
theorem tANR_classH (hx : Function.Injective x)
    (hA1 : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm)
    (hA : F.dep F.S.u_tANR 0 < F.dep F.S.u_tANR 6 ∨ F.dep F.S.u_tANR 0 < F.dep F.S.u_tANR 3 ∨
      F.dep F.S.u_tANR 4 < F.dep F.S.u_tANR 6 ∨ F.dep F.S.u_tANR 4 < F.dep F.S.u_tANR 3)
    (hB : F.dep F.S.u_tANR 6 < F.dep F.S.u_tANR 0 ∨ F.dep F.S.u_tANR 3 < F.dep F.S.u_tANR 0 ∨
      F.dep F.S.u_tANR 6 < F.dep F.S.u_tANR 4 ∨ F.dep F.S.u_tANR 3 < F.dep F.S.u_tANR 4)
    (hH : F.ClassH) : IsRupert (Finset.univ.image x) := by
  have htp := F.S.tp_pos
  have efv : ∀ η : ℝ, F.toFrame7.fvC (C3.slide F.S.u_tANR F.S.eT η) =
      F.toFrame7.fvC F.S.u_tANR + η • F.toFrame7.fvC F.S.eT := by
    intro η; simp only [Frame7.fvC, C3.slide]; module
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  have hcomm : ∀ j : ZMod 5, F.toFrame7.ptC (pent 0 6 4 3 5 j) =
      pent (F.toFrame7.ptC 0) (F.toFrame7.ptC 6) (F.toFrame7.ptC 4) (F.toFrame7.ptC 3)
        (F.toFrame7.ptC 5) j := by
    intro j; rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;> rfl
  obtain ⟨a, c0, hds, hden, hτ⟩ := F.TA_pair hH hA1 hA hB
  have hpos : ∀ᶠ η in 𝓝[>] (0 : ℝ), (0 : ℝ) < η := by
    filter_upwards [self_mem_nhdsWithin] with η hη using hη
  have hev := (eventually_depthSepAt (e := F.toFrame7.fvC F.S.eT) hds).and
    (eventually_torque3_ne_zero (fun i => x (pent 0 6 4 3 5 i)) (F.toFrame7.fvC F.S.u_tANR)
      (F.toFrame7.fvC F.S.eT) a c0 hden hτ)
  obtain ⟨η, hη0, hc, hr, hm, hds', -, hτ'⟩ :=
    (hpos.and ((F.S.TA_cyc_ev_S hA1).and
      ((F.S.TA_rest_ev_S hA1).and (F.mid_xa_T.and hev)))).exists
  refine F.toFrame7.rupert_vertex_torque hx (k := 5) (by norm_num) (pent 0 6 4 3 5) {1} 1
    (Or.inl rfl) (C3.slide F.S.u_tANR F.S.eT η)
    (Or.inr (Or.inl (ne_of_gt (by simp only [C3.slide, Shape20.u_tANR, Shape20.eT]; linarith)))) ?_ ?_ ?_
    (a := a) (c₀ := c0) ?_ ?_ ?_
  · intro m hm' i
    simp only [Finset.mem_singleton] at hm'
    subst hm'
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;> simp [pent_0, pent_1, pent_2, pent_3, pent_4]
  · intro i j h1 h2
    simp only [hcomm, F.ptC_0, F.ptC_6, F.ptC_4, F.ptC_3, F.ptC_5]; exact hc i j h1 h2
  · intro j' hj' hjc i
    simp only [Finset.mem_singleton] at hj'
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (by simp [pent_0]) (hjc 0)
    · exact absurd rfl hj'
    · simp only [hcomm, F.ptC_0, F.ptC_6, F.ptC_4, F.ptC_3, F.ptC_5, F.ptC_2]; exact hr i
    · exact absurd (by simp [pent_3]) (hjc 3)
    · exact absurd (by simp [pent_2]) (hjc 2)
    · exact absurd (by simp [pent_4]) (hjc 4)
    · exact absurd (by simp [pent_1]) (hjc 1)
  · rw [efv]; exact hds'
  · rw [efv]; exact hτ'
  · intro m hm'
    simp only [Finset.mem_singleton] at hm'
    subst hm'
    obtain ⟨s, δ, hs0, hs1, hδ, ex, ey, ez⟩ := hm
    refine ⟨0, s, δ, hs0, hs1, hδ, ?_, ?_, ?_⟩ <;>
      simp only [b0, pent_0, pent_1] <;> assumption

/-- **`vN4_slide` without any `ClassH` hypothesis** (same hypotheses as `vN4_slide`, minus `hH`). -/
theorem vN4_any (hx : Function.Injective x)
    (hV : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm - F.S.kp*F.S.tm)
    (hVW : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.sp + F.S.hp*F.S.tm - F.S.hp - F.S.kp*F.S.tm + F.S.kp)
    (hA : F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 3 ∨ F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 6 ∨ F.dep F.S.u_vN4 4 < F.dep F.S.u_vN4 3 ∨ F.dep F.S.u_vN4 4 < F.dep F.S.u_vN4 6)
    (hB : F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 0 ∨ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 0 ∨ F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 4 ∨ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 4) :
    IsRupert (Finset.univ.image x) := by
  by_cases hH : F.ClassH
  · exact F.vN4_classH hx hV hVW hA hB hH
  · exact F.vN4_slide hx hV hVW hA hB hH

/-- **`tANR_slide` without any `ClassH` hypothesis.** -/
theorem tANR_any (hx : Function.Injective x)
    (hA1 : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm)
    (hA : F.dep F.S.u_tANR 0 < F.dep F.S.u_tANR 6 ∨ F.dep F.S.u_tANR 0 < F.dep F.S.u_tANR 3 ∨ F.dep F.S.u_tANR 4 < F.dep F.S.u_tANR 6 ∨ F.dep F.S.u_tANR 4 < F.dep F.S.u_tANR 3)
    (hB : F.dep F.S.u_tANR 6 < F.dep F.S.u_tANR 0 ∨ F.dep F.S.u_tANR 3 < F.dep F.S.u_tANR 0 ∨ F.dep F.S.u_tANR 6 < F.dep F.S.u_tANR 4 ∨ F.dep F.S.u_tANR 3 < F.dep F.S.u_tANR 4) :
    IsRupert (Finset.univ.image x) := by
  by_cases hH : F.ClassH
  · exact F.tANR_classH hx hA1 hA hB hH
  · exact F.tANR_slide hx hA1 hA hB hH

end Frame20

end Minimality.CaseC20

/-!
## Summary

* Everything generic comes from type 18: `torque3`, `isRupert_of_chordView_torque`, `Frame7.rupert_vertex_torque`,
  `depthSepAt_of_frame`, `torque3_frame`, `eventually_torque3_ne_zero`, `pent`, `PS_ev'`.  The `Shape18`/`Frame18`
  typed lemmas are copied for `Shape20`/`Frame20` (the lower roof differs); `D2p < 0` (pentagon rim) is automatic
  in type 20 (`D2n_pos`).
* `V` (`vN4_classH`): slide `eD = m1+ - xb` on `026`'s circle, rim `pent 0 5 3 4 6`, `m2+` hidden exactly.
* `T_A` (`tANR_classH`): slide `eT = xb - m1+` on `016`'s circle (`s = +1`), rim `pent 0 6 4 3 5`, `xa` hidden
  exactly; `dep 5 = 0 > dep 6 = A12 (tp - 1)` always; the pair is `xb` with `[m1-, v]` or `[v, m1+]` by the sign of
  `B_T`; the torque identities `A12 g hm A1`, `A12 g hp^2` do not need `ClassH`.
* Robust unimodality (`hA /\ hB`) excludes the level chord `dep 0 = dep 6 = dep 3`, so no special position is left:
  `vN4_any` and `tANR_any` have no `ClassH` hypothesis at all.
-/

end
