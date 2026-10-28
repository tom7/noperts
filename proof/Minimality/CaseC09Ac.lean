module

public import Minimality.CaseC09TS

@[expose] public section

/-!
# Type 09, acute case (c), `a+ = c+` (`FEWER-FACES-PROOFS.md` §39.2, Theorem 09.A)

At `a+ = c+` (`h+ s+ = k+ t+`) the vertex `m1+` lies over the open side `(m2+, v)` of the folded hull;
the triple `(m2+, m1+, v)` is collinear (`Dc = 0` in the screen), and the tilt decides.  The tests
`t31II`, `t31IB`, `t095_5` are re-proved with the strict hypothesis `H31` replaced by the equality
`h+ s+ = k+ t+` (new lemmas `*_eq`; the old lemmas are unchanged).  Then `CaseC09Special` loses its
disjunct `a+ = c+`.
-/

namespace Minimality.CaseC09

open Finset

section Ac
variable {tp hp tm hm sp kp sm km ds : ℝ}

theorem t31II_rest1_eq (hsp : 0 < sp) (hsp1 : sp < 1) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1) (hhm : 0 < hm)
    (roof : hp * (1 - sp) < kp * (1 - tp)) (H31 : hp * sp = kp * tp) :
    ∀ i : ZMod 4,
      ST 1 ⟨1, -1, 0⟩ ⟨-1, 0, 0⟩
        ((quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨0, sp, kp⟩ i))
        ((⟨tp, 0, hp⟩ : C3).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨0, sp, kp⟩ i)) := by
  have htm' : 0 < 1 - tm := by linarith
  have htp' : 0 < 1 - tp := by linarith
  have hsp' : 0 < 1 - sp := by linarith
  have a1 := mul_pos htm hkp
  have a2 := mul_pos hhm hsp
  have a3 := mul_pos htm' hkp
  have a4 := mul_pos hhm hsp'
  have a5 := mul_pos hsp hhm
  have a6 := mul_pos htm hhm
  have a7 := mul_pos hsp' hkp
  have a8 := mul_pos hsp hkp
  have a9 := mul_pos htp hhm
  have a10 := mul_pos htp' hhm
  have a11 := mul_pos hhp htm
  have a12 := mul_pos hhp htm'
  have a13 := sub_pos.2 roof
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith)
    | (right; refine ⟨by linarith, by nlinarith⟩)

theorem t31IB_cyc_eq (hsp : 0 < sp) (hsp1 : sp < 1) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hkp : 0 < kp) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km)
    (roof : hp * (1 - sp) < kp * (1 - tp)) (H31 : hp * sp = kp * tp) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨1, -1, 0⟩ ⟨1, 0, 0⟩
        ((quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ (i + 1)).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ i))
        ((quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ j).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ i)) := by
  have hsm' : 0 < 1 - sm := by linarith
  have hsp' : 0 < 1 - sp := by linarith
  have htp' : 0 < 1 - tp := by linarith
  have a1 := mul_pos hsm hkp
  have a2 := mul_pos hsp hkm
  have a3 := mul_pos hsm' hkp
  have a4 := mul_pos hsp' hkm
  have a5 := mul_pos hsm hkm
  have a6 := mul_pos hsp hkp
  have a7 := mul_pos hsm' hkm
  have a8 := mul_pos hsp' hkp
  have a9 := sub_pos.2 roof
  have a11 := mul_pos hsm hhp
  have a12 := mul_pos hkm htp
  have a13 := mul_pos hsm' hhp
  have a14 := mul_pos hkm htp'
  have a15 := mul_pos htp hkp
  have a16 := mul_pos htp' hkp
  have a17 := mul_pos hsp hhp
  have a18 := mul_pos hsp' hhp
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i j h1 h2
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith)
    | (right; refine ⟨by linarith, by nlinarith⟩)

theorem t31IB_rest3_eq (hsp : 0 < sp) (hsp1 : sp < 1) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hkp : 0 < kp) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km)
    (roof : hp * (1 - sp) < kp * (1 - tp)) (H31 : hp * sp = kp * tp) :
    ∀ i : ZMod 5,
      ST 1 ⟨1, -1, 0⟩ ⟨1, 0, 0⟩
        ((quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ (i + 1)).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ i))
        ((⟨1, 0, 0⟩ : C3).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ i)) := by
  have hsm' : 0 < 1 - sm := by linarith
  have hsp' : 0 < 1 - sp := by linarith
  have htp' : 0 < 1 - tp := by linarith
  have a1 := mul_pos hsm hkp
  have a2 := mul_pos hsp hkm
  have a3 := mul_pos hsm' hkp
  have a4 := mul_pos hsp' hkm
  have a5 := mul_pos hsm hkm
  have a6 := mul_pos hsp hkp
  have a7 := mul_pos hsm' hkm
  have a8 := mul_pos hsp' hkp
  have a9 := sub_pos.2 roof
  have a11 := mul_pos hsm hhp
  have a12 := mul_pos hkm htp
  have a13 := mul_pos hsm' hhp
  have a14 := mul_pos hkm htp'
  have a15 := mul_pos htp hkp
  have a16 := mul_pos htp' hkp
  have a17 := mul_pos hsp hhp
  have a18 := mul_pos hsp' hhp
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith)
    | (right; refine ⟨by linarith, by nlinarith⟩)

theorem t31IB_rest4_eq (hsp : 0 < sp) (hsp1 : sp < 1) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1) (hhm : 0 < hm) (hsm : 0 < sm) (hsm1 : sm < 1)
    (hkm : 0 < km) (hst : sm < tm) (Km : km * (1 - tm) = (1 - sm) * hm)
    (roof : hp * (1 - sp) < kp * (1 - tp)) (H31 : hp * sp = kp * tp) :
    ∀ i : ZMod 5,
      ST 1 ⟨1, -1, 0⟩ ⟨1, 0, 0⟩
        ((quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ (i + 1)).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ i))
        ((⟨tm, 0, -hm⟩ : C3).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ i)) := by
  have hsm' : 0 < 1 - sm := by linarith
  have hsp' : 0 < 1 - sp := by linarith
  have htm' : 0 < 1 - tm := by linarith
  have htp' : 0 < 1 - tp := by linarith
  have a1 := mul_pos hsm hkp
  have a2 := mul_pos hsp hkm
  have a3 := mul_pos hsm' hkp
  have a4 := mul_pos hsp' hkm
  have a5 := mul_pos hsm hkm
  have a6 := mul_pos hsp hkp
  have a7 := mul_pos htm hkm
  have a8 := mul_pos htm' hkm
  have a9 := mul_pos htm hkp
  have a10 := mul_pos htm' hkp
  have a11 := mul_pos hsm hhm
  have a12 := mul_pos (sub_pos.2 hst) hkm
  have a13 := mul_pos (sub_pos.2 hst) hhm
  have a14 := mul_pos (sub_pos.2 hst) hkp
  have a15 := sub_pos.2 roof
  have a17 := mul_pos htp hhm
  have a18 := mul_pos htp' hhm
  have a19 := mul_pos hsp hhm
  have a20 := mul_pos hsp' hhm
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith)
    | (right; refine ⟨by linarith, by nlinarith⟩)

theorem t095_cyc5_eq (hsp : 0 < sp) (hsp1 : sp < 1) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1) (hhm : 0 < hm)
    (roof : hp * (1 - sp) < kp * (1 - tp)) (H : hp * sp = kp * tp) (h1 : hm * ds < tm) (h2 : 1 - sp < kp * ds) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨1, -1, 0⟩ ⟨ds, 0, -1⟩
        ((quint (⟨0, 0, 0⟩ : C3) ⟨0, tm, -hm⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ (i + 1)).sub (quint (⟨0, 0, 0⟩ : C3) ⟨0, tm, -hm⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ i))
        ((quint (⟨0, 0, 0⟩ : C3) ⟨0, tm, -hm⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ j).sub (quint (⟨0, 0, 0⟩ : C3) ⟨0, tm, -hm⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ i)) := by
  have hsm' : 0 < 1 - tm := by linarith
  have hsp' : 0 < 1 - sp := by linarith
  have htp' : 0 < 1 - tp := by linarith
  have a1 := mul_pos htm hkp
  have a2 := mul_pos hsp hhm
  have a3 := mul_pos hsm' hkp
  have a4 := mul_pos hsp' hhm
  have a5 := mul_pos htm hhm
  have a6 := mul_pos hsp hkp
  have a7 := mul_pos hsm' hhm
  have a8 := mul_pos hsp' hkp
  have a9 := sub_pos.2 roof
  have a11 := mul_pos htm hhp
  have a12 := mul_pos hhm htp
  have a13 := mul_pos hsm' hhp
  have a14 := mul_pos hhm htp'
  have a15 := mul_pos htp hkp
  have a16 := mul_pos htp' hkp
  have a17 := mul_pos hsp hhp
  have a18 := mul_pos hsp' hhp
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i j h1 h2
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith)
    | (right; refine ⟨by linarith, by nlinarith⟩)

theorem t095_rest3_5_eq (hsp : 0 < sp) (hsp1 : sp < 1) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1) (hhm : 0 < hm)
    (roof : hp * (1 - sp) < kp * (1 - tp)) (H : hp * sp = kp * tp) (h1 : hm * ds < tm) (h2 : 1 - sp < kp * ds) :
    ∀ i : ZMod 5,
      ST 1 ⟨1, -1, 0⟩ ⟨ds, 0, -1⟩
        ((quint (⟨0, 0, 0⟩ : C3) ⟨0, tm, -hm⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ (i + 1)).sub (quint (⟨0, 0, 0⟩ : C3) ⟨0, tm, -hm⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ i))
        ((⟨1, 0, 0⟩ : C3).sub (quint (⟨0, 0, 0⟩ : C3) ⟨0, tm, -hm⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ i)) := by
  have hds : 0 < ds := by
    by_contra hn; push_neg at hn; nlinarith [mul_nonpos_of_nonneg_of_nonpos hkp.le hn]
  have hsm' : 0 < 1 - tm := by linarith
  have hsp' : 0 < 1 - sp := by linarith
  have htm' : 0 < 1 - tm := by linarith
  have htp' : 0 < 1 - tp := by linarith
  have a1 := mul_pos htm hkp
  have a2 := mul_pos hsp hhm
  have a3 := mul_pos hsm' hkp
  have a4 := mul_pos hsp' hhm
  have a5 := mul_pos htm hhm
  have a6 := mul_pos hsp hkp
  have a7 := mul_pos hsm' hhm
  have a8 := mul_pos hsp' hkp
  have a9 := sub_pos.2 roof
  have a11 := mul_pos htm hhp
  have a12 := mul_pos hhm htp
  have a13 := mul_pos hsm' hhp
  have a14 := mul_pos hhm htp'
  have a15 := mul_pos htp hkp
  have a16 := mul_pos htp' hkp
  have a17 := mul_pos hsp hhp
  have a18 := mul_pos hsp' hhp
  have c1 := sub_pos.2 h1
  have c2 := sub_pos.2 h2
  have c3 := mul_pos hds hhm
  have c4 := mul_pos hds hkp
  have c5 := mul_pos hds hsp
  have c6 := mul_pos hds htm
  have c7 := mul_pos hds hsp'
  have c8 := mul_pos hds hsm'
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith)
    | (right; refine ⟨by linarith, by nlinarith⟩)

theorem t095_rest4_5_eq (hsp : 0 < sp) (hsp1 : sp < 1) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1) (hhm : 0 < hm)
    (roof : hp * (1 - sp) < kp * (1 - tp)) (H : hp * sp = kp * tp) (h1 : hm * ds < tm) (h2 : 1 - sp < kp * ds) :
    ∀ i : ZMod 5,
      ST 1 ⟨1, -1, 0⟩ ⟨ds, 0, -1⟩
        ((quint (⟨0, 0, 0⟩ : C3) ⟨0, tm, -hm⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ (i + 1)).sub (quint (⟨0, 0, 0⟩ : C3) ⟨0, tm, -hm⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ i))
        ((⟨tm, 0, -hm⟩ : C3).sub (quint (⟨0, 0, 0⟩ : C3) ⟨0, tm, -hm⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ i)) := by
  have hds : 0 < ds := by
    by_contra hn; push_neg at hn; nlinarith [mul_nonpos_of_nonneg_of_nonpos hkp.le hn]
  have hsm' : 0 < 1 - tm := by linarith
  have hsp' : 0 < 1 - sp := by linarith
  have htm' : 0 < 1 - tm := by linarith
  have htp' : 0 < 1 - tp := by linarith
  have a1 := mul_pos htm hkp
  have a2 := mul_pos hsp hhm
  have a3 := mul_pos hsm' hkp
  have a4 := mul_pos hsp' hhm
  have a5 := mul_pos htm hhm
  have a6 := mul_pos hsp hkp
  have a7 := mul_pos hsm' hhm
  have a8 := mul_pos hsp' hkp
  have a9 := sub_pos.2 roof
  have a11 := mul_pos htm hhp
  have a12 := mul_pos hhm htp
  have a13 := mul_pos hsm' hhp
  have a14 := mul_pos hhm htp'
  have a15 := mul_pos htp hkp
  have a16 := mul_pos htp' hkp
  have a17 := mul_pos hsp hhp
  have a18 := mul_pos hsp' hhp
  have c1 := sub_pos.2 h1
  have c2 := sub_pos.2 h2
  have c3 := mul_pos hds hhm
  have c4 := mul_pos hds hkp
  have c5 := mul_pos hds hsp
  have c6 := mul_pos hds htm
  have c7 := mul_pos hds hsp'
  have c8 := mul_pos hds hsm'
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith)
    | (right; refine ⟨by linarith, by nlinarith⟩)


end Ac

namespace Frame09
variable {x : Fin 7 → ℝ³} (F : Frame09 x)

/-- At `a+ = c+`: `h+ s+ = k+ t+`. -/
lemma H31_eq (h : F.S.ap = F.S.cp) : F.S.hp * F.S.sp = F.S.kp * F.S.tp := by
  have e1 := F.S.ap_mul; have e2 := F.S.cp_mul
  rw [← e1, ← e2, h]; ring

/-- **09.A, case (i)** (`t- < s-`, `a+ = c+`): `t31II` with `m1+` over the open side `(m2+, v)`;
the triple `(m2+, m1+, v)` is collinear and the tilt `-e_x` decides (`t+ k+ > 0`). -/
theorem t31II_eq (hA1 : F.a12 ≤ F.a11) (hts : F.S.tm < F.S.sm) (hac : F.S.ap = F.S.cp) :
    IsRupert (Finset.univ.image x) := by
  have hsp := F.S.sp_pos; have hsp1 := F.S.sp_lt; have htp := F.S.tp_pos; have htp1 := F.S.tp_lt
  have hhp := F.S.hp_pos; have hkp := F.S.kp_pos; have htm := F.S.tm_pos; have htm1 := F.S.tm_lt
  have hhm := F.S.hm_pos; have hsm := F.S.sm_pos; have hsm1 := F.S.sm_lt; have hkm := F.S.km_pos
  have roof := F.roof'
  have H31 := F.H31_eq hac
  have Km := F.Km_eq
  obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ := F.ptC_pts
  refine F.rupert_rim4 0 4 3 2 ⟨0, 0, 0⟩ ⟨F.S.tm, 0, -F.S.hm⟩ ⟨1, 0, 0⟩ ⟨0, F.S.sp, F.S.kp⟩
    p0 p4 p3 p2 1 (Or.inl rfl) ⟨1, -1, 0⟩ ⟨-1, 0, 0⟩ (Or.inl one_ne_zero) ?_ ?_ ?_
  · exact t31II_cyc hsp hsp1 htp htp1 hhp hkp htm htm1 hhm
  · intro j' h0 h4 h3 h2 i
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · rw [p1]; exact t31II_rest1_eq hsp hsp1 htp htp1 hhp hkp htm htm1 hhm roof H31 i
    · exact absurd rfl h2
    · exact absurd rfl h3
    · exact absurd rfl h4
    · rw [p5]; exact t31II_rest5 hsp hsp1 htp htp1 hhp hkp htm htm1 hhm i
    · rw [p6]; exact t31II_rest6 hsp hsp1 htp htp1 hhp hkp htm htm1 hhm hsm hsm1 hkm hts Km i
  · set Pq : ZMod 4 → C3 := quad ⟨0, 0, 0⟩ ⟨F.S.tm, 0, -F.S.hm⟩ ⟨1, 0, 0⟩ ⟨0, F.S.sp, F.S.kp⟩
      with hPq
    set zz : ZMod 4 → ℝ := fun i => F.GG (Pq i) ⟨1, -1, 0⟩ with hzz
    set ww : ZMod 4 → ℝ := fun i => F.GG (Pq i) ⟨-1, 0, 0⟩ with hww
    have h11 : 0 < F.a11 := lt_of_lt_of_le F.A12_pos F.A12_le_A11
    rcases lt_or_eq_of_le hA1 with hlt | heq
    · have hd : 0 < F.a11 - F.a12 := sub_pos.2 hlt
      refine Q4_eventually (z := zz) (w := ww) (Or.inl (Or.inl ?_))
        (Or.inr (Or.inr (Or.inl (Or.inl ?_))))
      · simp only [hzz, hPq, GG, Gf, quad_0, quad_1]
        nlinarith [mul_pos htm hd]
      · simp only [hzz, hPq, GG, Gf, quad_1, quad_2]
        nlinarith [mul_pos (sub_pos.2 htm1) hd]
    · -- a right angle at `xa`: the ties are broken by the tilt `-u₁`
      have hz : F.a11 - F.a12 = 0 := by linarith
      refine Q4_eventually (z := zz) (w := ww) (Or.inr (Or.inr (Or.inl (Or.inr ⟨?_, ?_⟩))))
        (Or.inl (Or.inr ⟨?_, ?_⟩))
      · simp only [hzz, hPq, GG, Gf, quad_1, quad_2]
        linear_combination (1 - F.S.tm) * hz
      · simp only [hww, hPq, GG, Gf, quad_1, quad_2]
        nlinarith [mul_pos h11 (sub_pos.2 htm1)]
      · simp only [hzz, hPq, GG, Gf, quad_0, quad_1]
        linear_combination F.S.tm * hz
      · simp only [hww, hPq, GG, Gf, quad_0, quad_1]
        nlinarith [mul_pos h11 htm]



/-- **09.A, case (ii)** (`s- < t-`, `a+ = c+`): `t31IB` with `m1+` shown on the side `(m2+, v)`. -/
theorem t31IB_eq (hA1 : F.a12 ≤ F.a11) (hA2 : F.a12 < F.a22) (hst : F.S.sm < F.S.tm)
    (hac : F.S.ap = F.S.cp) : IsRupert (Finset.univ.image x) := by
  have hsp := F.S.sp_pos; have hsp1 := F.S.sp_lt; have htp := F.S.tp_pos; have htp1 := F.S.tp_lt
  have hhp := F.S.hp_pos; have hkp := F.S.kp_pos; have htm := F.S.tm_pos; have htm1 := F.S.tm_lt
  have hhm := F.S.hm_pos; have hsm := F.S.sm_pos; have hsm1 := F.S.sm_lt; have hkm := F.S.km_pos
  have roof := F.roof'
  have H31 := F.H31_eq hac
  have Km := F.Km_eq
  obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ := F.ptC_pts
  refine F.rupert_rim5 0 6 5 2 1 ⟨0, 0, 0⟩ ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨0, F.S.sp, F.S.kp⟩
    ⟨F.S.tp, 0, F.S.hp⟩ p0 p6 p5 p2 p1 1 (Or.inl rfl) ⟨1, -1, 0⟩ ⟨1, 0, 0⟩ (Or.inl one_ne_zero)
    ?_ ?_ ?_
  · exact t31IB_cyc_eq hsp hsp1 htp htp1 hhp hkp hsm hsm1 hkm roof H31
  · intro j' h0 h6 h5 h2 h1 i
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · exact absurd rfl h1
    · exact absurd rfl h2
    · rw [p3]; exact t31IB_rest3_eq hsp hsp1 htp htp1 hhp hkp hsm hsm1 hkm roof H31 i
    · rw [p4]; exact t31IB_rest4_eq hsp hsp1 htp htp1 hhp hkp htm htm1 hhm hsm hsm1 hkm hst Km
        roof H31 i
    · exact absurd rfl h5
    · exact absurd rfl h6
  · set Pq : ZMod 5 → C3 := quint ⟨0, 0, 0⟩ ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨0, F.S.sp, F.S.kp⟩
      ⟨F.S.tp, 0, F.S.hp⟩ with hPq
    set zz : ZMod 5 → ℝ := fun i => F.GG (Pq i) ⟨1, -1, 0⟩ with hzz
    set ww : ZMod 5 → ℝ := fun i => F.GG (Pq i) ⟨1, 0, 0⟩ with hww
    have hd1 : 0 ≤ F.a11 - F.a12 := sub_nonneg.2 hA1
    have h11 : 0 < F.a11 := lt_of_lt_of_le F.A12_pos F.A12_le_A11
    have hd2 : 0 < F.a22 - F.a12 := sub_pos.2 hA2
    refine Q5c_eventually (z := zz) (w := ww) (Or.inl ?_) (Or.inl ?_) (Or.inl ?_) (Or.inl ?_) ?_
    · simp only [hzz, hPq, GG, Gf, quint_0, quint_1]
      nlinarith [mul_pos hsm hd2]
    · simp only [hzz, hPq, GG, Gf, quint_1, quint_2]
      nlinarith [mul_pos (sub_pos.2 hsm1) hd2]
    · simp only [hzz, hPq, GG, Gf, quint_2, quint_3]
      nlinarith [mul_pos (sub_pos.2 hsp1) hd2]
    · simp only [hzz, hPq, GG, Gf, quint_3, quint_4]
      nlinarith [mul_pos hsp hd2, mul_nonneg htp.le hd1]
    · rcases lt_or_eq_of_le hA1 with hlt | heq
      · left
        simp only [hzz, hPq, GG, Gf, quint_0, quint_4]
        nlinarith [mul_pos htp (sub_pos.2 hlt)]
      · right
        have hz : F.a11 - F.a12 = 0 := by linarith
        constructor
        · simp only [hzz, hPq, GG, Gf, quint_0, quint_4]
          linear_combination (-F.S.tp) * hz
        · simp only [hww, hPq, GG, Gf, quint_0, quint_4]
          nlinarith [mul_pos h11 htp]


/-- **09.A, case (iii)** (`t- = s-`, `a- < d+`, `a+ = c+`): `t095_5` with `m1+` shown on the side. -/

theorem t095_5_eq (hA : F.a12 < F.a22) (hts : F.S.tm = F.S.sm) (hda : F.S.am < F.S.dp)
    (hac : F.S.ap = F.S.cp) : IsRupert (Finset.univ.image x) := by
  obtain ⟨ds, hd1, hd2⟩ := F.S.exists_ds hts hda
  have hkm := F.S.km_eq_hm_of_eq hts
  have hsp := F.S.sp_pos; have hsp1 := F.S.sp_lt; have htp := F.S.tp_pos; have htp1 := F.S.tp_lt
  have hhp := F.S.hp_pos; have hkp := F.S.kp_pos; have htm := F.S.tm_pos; have htm1 := F.S.tm_lt
  have hhm := F.S.hm_pos
  have roof := F.roof'
  have H31 := F.H31_eq hac
  obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ := F.ptC_pts
  rw [← hts, hkm] at p6
  refine F.rupert_rim5p 0 6 5 2 1 ⟨0, 0, 0⟩ ⟨0, F.S.tm, -F.S.hm⟩ ⟨0, 1, 0⟩ ⟨0, F.S.sp, F.S.kp⟩
    ⟨F.S.tp, 0, F.S.hp⟩ p0 p6 p5 p2 p1 1 (Or.inl rfl) ⟨1, -1, 0⟩ ⟨ds, 0, -1⟩
    (Or.inl one_ne_zero) ?_ ?_ ?_
  · exact t095_cyc5_eq hsp hsp1 htp htp1 hhp hkp htm htm1 hhm roof H31 hd1 hd2
  · intro j' h0 h6 h5 h2 h1 i
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · exact absurd rfl h1
    · exact absurd rfl h2
    · rw [p3]; exact t095_rest3_5_eq hsp hsp1 htp htp1 hhp hkp htm htm1 hhm roof H31 hd1 hd2 i
    · rw [p4]; exact t095_rest4_5_eq hsp hsp1 htp htp1 hhp hkp htm htm1 hhm roof H31 hd1 hd2 i
    · exact absurd rfl h5
    · exact absurd rfl h6
  · set Pq : ZMod 5 → C3 := quint ⟨0, 0, 0⟩ ⟨0, F.S.tm, -F.S.hm⟩ ⟨0, 1, 0⟩ ⟨0, F.S.sp, F.S.kp⟩
      ⟨F.S.tp, 0, F.S.hp⟩ with hPq
    set zz : ZMod 5 → ℝ := fun i => F.GG (Pq i) ⟨1, -1, 0⟩ with hzz
    set ww : ZMod 5 → ℝ := fun i => F.GG (Pq i) ⟨ds, 0, -1⟩ with hww
    have hd1' : 0 ≤ F.a11 - F.a12 := sub_nonneg.2 F.A12_le_A11
    have hd2' : 0 < F.a22 - F.a12 := sub_pos.2 hA
    -- strict witnesses (z = 0, -be t, -be, -be s+, al t+):
    --   h0: z2 < z1 (3rd alt)   h1: z1 < z0 (1st)   h2: z2 < z1 (1st)
    --   h3: z3 < z4 (2nd)       h4: z1 < z0 (3rd)
    refine Q5p_eventually (z := zz) (w := ww)
      (Or.inr (Or.inr (Or.inl (Or.inl ?_)))) (Or.inl (Or.inl ?_)) (Or.inl (Or.inl ?_))
      (Or.inr (Or.inl (Or.inl ?_))) (Or.inr (Or.inr (Or.inl (Or.inl ?_))))
    · simp only [hzz, hPq, GG, Gf, quint_1, quint_2]
      nlinarith [mul_pos (sub_pos.2 htm1) hd2']
    · simp only [hzz, hPq, GG, Gf, quint_0, quint_1]
      nlinarith [mul_pos htm hd2']
    · simp only [hzz, hPq, GG, Gf, quint_1, quint_2]
      nlinarith [mul_pos (sub_pos.2 htm1) hd2']
    · simp only [hzz, hPq, GG, Gf, quint_3, quint_4]
      nlinarith [mul_pos hsp hd2', mul_nonneg htp.le hd1']
    · simp only [hzz, hPq, GG, Gf, quint_0, quint_1]
      nlinarith [mul_pos htm hd2']


/-- Type 09, acute case (c), off the shrunken special set (`a+ = c+` is now handled: Theorem 09.A). -/
theorem isRupert_caseC' (hx : Function.Injective x) (hA : F.a12 < F.a22)
    (sp0 : F.S.tm ≠ F.S.sm ∨ F.S.am ≠ F.S.dp)
    (hc : ¬ (F.S.am = F.S.bp ∧ F.S.bp = F.S.sp * F.S.A2)) :
    IsRupert (Finset.univ.image x) := by
  by_cases hts : F.S.tm = F.S.sm
  · have hda : F.S.am ≠ F.S.dp := sp0.resolve_left (not_not.mpr hts)
    rcases lt_or_gt_of_ne hda with h | h
    · by_cases hac : F.S.ap = F.S.cp
      · exact F.t095_5_eq hA hts h hac
      · exact F.rupert_of_tm_eq_sm_gt hx hA hts h hac
    · exact F.rupert_of_tm_eq_sm_lt hx hA hts h
  · by_cases hac : F.S.ap = F.S.cp
    · rcases lt_or_gt_of_ne hts with h | h
      · exact F.t31II_eq F.A12_le_A11 h hac
      · exact F.t31IB_eq F.A12_le_A11 hA h hac
    · rcases F.rupert_or_27_48'' hx hA hts hac with h | ⟨a, b, c, d, e⟩
      · exact h
      · exact F.rupert_of_27_48_special a b c d e hc

end Frame09

/-- **The special positions of type 09's acute case (c)** (on `x`, for some frame): `t- = s-` with
`a- = d+` (the remaining part of 09.5), the right angle `A12 = A22` at `xb`, or the corner
`a- = b+ ∧ b+ = s+A2`.  (`a+ = c+` was removed by Theorem 09.A, §39.2; `t- = s-` with `a- ≠ d+`,
`c+ = b-`, `a- = d+`, `b+ = s+A2`, `a- = b+` alone by 09.5, 09.4, 09.1, 09.2, 09.3 and fix 1.) -/
def CaseC09Special (x : Fin 7 → ℝ³) : Prop :=
  ∃ F : Frame09 x, (F.S.tm = F.S.sm ∧ F.S.am = F.S.dp) ∨ F.a12 = F.a22 ∨
    (F.S.am = F.S.bp ∧ F.S.bp = F.S.sp * F.S.A2)

namespace Frame09

/-- Off the special positions, a type-09 frame (acute case (c)) is Rupert. -/
theorem isRupert_of_not_special {x : Fin 7 → ℝ³} (F : Frame09 x) (hx : Function.Injective x)
    (h : ¬ CaseC09Special x) : IsRupert (Finset.univ.image x) := by
  have hF : ¬ ((F.S.tm = F.S.sm ∧ F.S.am = F.S.dp) ∨ F.a12 = F.a22 ∨
      (F.S.am = F.S.bp ∧ F.S.bp = F.S.sp * F.S.A2)) := fun h' => h ⟨F, h'⟩
  simp only [not_or] at hF
  obtain ⟨n0, nA, n1⟩ := hF
  exact F.isRupert_caseC' hx (lt_of_le_of_ne F.A12_le_A22 nA) (not_and_or.mp n0) n1

end Frame09

end Minimality.CaseC09
