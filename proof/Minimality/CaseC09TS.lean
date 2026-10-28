module

public import Minimality.CaseC09Special

@[expose] public section

/-!
# Type 09, acute case (c), `t- = s-` with `d+ < a-` (`FEWER-FACES-PROOFS.md` §34.4.2, 09.5, part A)

Theorem 5 with `W` the quad `3456` (27.57) at `t- = s-`: the nine comparisons `t N < M` hold
(`Shape09.tm_N57_lt_M57` takes `t- ≤ s-`), and the quad is then solved by `w1 + w2` just below `M`.
-/

namespace Minimality.CaseC09

open Finset

/-- 09.5, case `d+ < a-`: `Q3456` at `t- = s-`. -/
theorem Shape09.q3456_of_eq (S : Shape09) (hts : S.tm = S.sm) (had : S.dp < S.am) : S.Q3456 := by
  have hkey := S.tm_N57_lt_M57 hts.le had
  have htm := S.tm_pos; have hM := S.M57_pos
  set M := S.M57
  set N := S.N57
  set ε := min (M / 4) ((M - S.tm * N) / 2) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (by linarith)
  have hε1 : ε ≤ M / 4 := min_le_left _ _
  have hε2 : ε ≤ (M - S.tm * N) / 2 := min_le_right _ _
  refine ⟨M - 2 * ε, ε, by linarith, hε0, by linarith, ?_⟩
  rw [← hts, ← add_div, lt_div_iff₀ htm]
  nlinarith

/-- **09.5, part A** (`t- = s-`, `d+ < a-`): Theorem 5 with `W = 3456` holds. -/
theorem Frame09.rupert_of_tm_eq_sm_lt {x : Fin 7 → ℝ³} (F : Frame09 x)
    (hx : Function.Injective x) (hA : F.a12 < F.a22) (hts : F.S.tm = F.S.sm)
    (hda : F.S.dp < F.S.am) : IsRupert (Finset.univ.image x) :=
  F.rupert_of_Q3456 hx (F.S.q3456_of_eq hts hda)

/-! ### Part B: `t- = s-` with `d+ > a-` (27.31's view with the doubles `xb`, `m2-` shown)

The view is `u = xa - xb = (1, -1, 0)` (frame coordinates), the tilt `d = (ds, 0, -1)` with
`a- ds < 1/t...`: precisely `hm * ds < tm` and `1 - sp < kp * ds` (the sides `v m2-`, `xb m2+` of
the folded hull; the side `m2- xb` then follows from `ds > 0`).  Such `ds` exists iff `a- < d+`.
At `t- = s-` we have `k- = h-`, `m1- = (t, 0, -h)`, `m2- = (0, t, -h)`, so `m1- = m2- + t u` and
`xa = xb + u` are doubles over the rim corners `m2-`, `xb`, and the three tests with `D0 = 0`
(`ST`'s second disjunct) read `n_e . d > 0` for the three sides.  Depths along `u`
(`al = A11 - A12 >= 0`, `be = A22 - A12 > 0`): `v = 0`, `m1+ = al t+`, `m2+ = -be s+`,
`xb = -be`, `m2- = -be t`.  The five-pairs condition `Q5p` (rim `(v, m2-, xb, m2+, m1+)`) and `Q4`
(rim `(v, m2-, xb, m2+)`) hold with strict inequalities that avoid the tie `v = m1+` at
`A12 = A11`, so no tilt-derivative case split is needed (unlike `t31IB`). -/

/-- `t- = s-` forces `k- = h-`. -/
theorem Shape09.km_eq_hm_of_eq (S : Shape09) (hts : S.tm = S.sm) : S.km = S.hm := by
  have e := S.km_eq; have e1 := S.bm_mul
  have h1 : 0 < 1 - S.tm := by linarith [S.tm_lt]
  rw [← hts] at e
  rw [e]; exact e1

/-- The tilt coordinate: exists iff `a- < d+` (`ds` between `(1 - s+)/k+ = 1/d+` and `t/h- = 1/a-`). -/
theorem Shape09.exists_ds (S : Shape09) (hts : S.tm = S.sm) (hda : S.am < S.dp) :
    ∃ ds : ℝ, S.hm * ds < S.tm ∧ 1 - S.sp < S.kp * ds := by
  have e1 := S.am_mul; have e2 := S.dp_mul
  have hhm := S.hm_pos; have hkp := S.kp_pos; have htm := S.tm_pos
  have hsp' : 0 < 1 - S.sp := by linarith [S.sp_lt]
  -- `(1 - sp)/kp < tm/hm`
  have key : (1 - S.sp) * S.hm < S.tm * S.kp := by
    have := mul_lt_mul_of_pos_right hda (mul_pos htm hsp')
    nlinarith
  refine ⟨((1 - S.sp) / S.kp + S.tm / S.hm) / 2, ?_, ?_⟩
  · have : (1 - S.sp) / S.kp < S.tm / S.hm := by
      rw [div_lt_div_iff₀ hkp hhm]; linarith
    have h3 : S.hm * (S.tm / S.hm) = S.tm := by field_simp
    have h4 : S.hm * ((1 - S.sp) / S.kp) < S.hm * (S.tm / S.hm) := mul_lt_mul_of_pos_left this hhm
    nlinarith
  · have : (1 - S.sp) / S.kp < S.tm / S.hm := by
      rw [div_lt_div_iff₀ hkp hhm]; linarith
    have h3 : S.kp * ((1 - S.sp) / S.kp) = 1 - S.sp := by field_simp
    have h4 : S.kp * ((1 - S.sp) / S.kp) < S.kp * (S.tm / S.hm) := mul_lt_mul_of_pos_left this hkp
    nlinarith

section T095
variable {tp hp tm hm sp kp ds : ℝ}

/-! The rim `(v, m2-, xb, m2+, m1+)` (`m1+` a corner, `c+ < a+`); the rest points are `xa`, `m1-`.
Template: `t31IB_cyc`, `t31IB_rest3`, `t31IB_rest4` (same points with `m2- = (0, tm, -hm)`; the cyclic
tests there should already be strict, `left`, hence independent of the tilt). -/

theorem t095_cyc5 (hsp : 0 < sp) (hsp1 : sp < 1) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1) (hhm : 0 < hm)
    (roof : hp * (1 - sp) < kp * (1 - tp)) (H : kp * tp < hp * sp) (h1 : hm * ds < tm) (h2 : 1 - sp < kp * ds) :
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
  have a10 := sub_pos.2 H
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
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem t095_rest3_5 (hsp : 0 < sp) (hsp1 : sp < 1) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1) (hhm : 0 < hm)
    (roof : hp * (1 - sp) < kp * (1 - tp)) (H : kp * tp < hp * sp) (h1 : hm * ds < tm) (h2 : 1 - sp < kp * ds) :
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
  have a10 := sub_pos.2 H
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
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem t095_rest4_5 (hsp : 0 < sp) (hsp1 : sp < 1) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1) (hhm : 0 < hm)
    (roof : hp * (1 - sp) < kp * (1 - tp)) (H : kp * tp < hp * sp) (h1 : hm * ds < tm) (h2 : 1 - sp < kp * ds) :
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
  have a10 := sub_pos.2 H
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
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem t095_cyc4 (hsp : 0 < sp) (hsp1 : sp < 1) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1) (hhm : 0 < hm)
    (roof : hp * (1 - sp) < kp * (1 - tp)) (H : hp * sp < kp * tp) (h1 : hm * ds < tm) (h2 : 1 - sp < kp * ds) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨1, -1, 0⟩ ⟨ds, 0, -1⟩
        ((quad (⟨0, 0, 0⟩ : C3) ⟨0, tm, -hm⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ (i + 1)).sub (quad (⟨0, 0, 0⟩ : C3) ⟨0, tm, -hm⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i))
        ((quad (⟨0, 0, 0⟩ : C3) ⟨0, tm, -hm⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ j).sub (quad (⟨0, 0, 0⟩ : C3) ⟨0, tm, -hm⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i)) := by
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
  have a10 := sub_pos.2 H
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
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i j h1' h2'
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1'
    | exact absurd (by decide) h2'
    | skip
  all_goals
    simp only [ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem t095_rest1_4 (hsp : 0 < sp) (hsp1 : sp < 1) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1) (hhm : 0 < hm)
    (roof : hp * (1 - sp) < kp * (1 - tp)) (H : hp * sp < kp * tp) (h1 : hm * ds < tm) (h2 : 1 - sp < kp * ds) :
    ∀ i : ZMod 4,
      ST 1 ⟨1, -1, 0⟩ ⟨ds, 0, -1⟩
        ((quad (⟨0, 0, 0⟩ : C3) ⟨0, tm, -hm⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ (i + 1)).sub (quad (⟨0, 0, 0⟩ : C3) ⟨0, tm, -hm⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i))
        ((⟨tp, 0, hp⟩ : C3).sub (quad (⟨0, 0, 0⟩ : C3) ⟨0, tm, -hm⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i)) := by
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
  have a10 := sub_pos.2 H
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
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem t095_rest3_4 (hsp : 0 < sp) (hsp1 : sp < 1) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1) (hhm : 0 < hm)
    (roof : hp * (1 - sp) < kp * (1 - tp)) (H : hp * sp < kp * tp) (h1 : hm * ds < tm) (h2 : 1 - sp < kp * ds) :
    ∀ i : ZMod 4,
      ST 1 ⟨1, -1, 0⟩ ⟨ds, 0, -1⟩
        ((quad (⟨0, 0, 0⟩ : C3) ⟨0, tm, -hm⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ (i + 1)).sub (quad (⟨0, 0, 0⟩ : C3) ⟨0, tm, -hm⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i))
        ((⟨1, 0, 0⟩ : C3).sub (quad (⟨0, 0, 0⟩ : C3) ⟨0, tm, -hm⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i)) := by
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
  have a10 := sub_pos.2 H
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
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem t095_rest4_4 (hsp : 0 < sp) (hsp1 : sp < 1) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1) (hhm : 0 < hm)
    (roof : hp * (1 - sp) < kp * (1 - tp)) (H : hp * sp < kp * tp) (h1 : hm * ds < tm) (h2 : 1 - sp < kp * ds) :
    ∀ i : ZMod 4,
      ST 1 ⟨1, -1, 0⟩ ⟨ds, 0, -1⟩
        ((quad (⟨0, 0, 0⟩ : C3) ⟨0, tm, -hm⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ (i + 1)).sub (quad (⟨0, 0, 0⟩ : C3) ⟨0, tm, -hm⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i))
        ((⟨tm, 0, -hm⟩ : C3).sub (quad (⟨0, 0, 0⟩ : C3) ⟨0, tm, -hm⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i)) := by
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
  have a10 := sub_pos.2 H
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
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)


end T095

namespace Frame09
variable {x : Fin 7 → ℝ³} (F : Frame09 x)

/-- **09.5, case `d+ > a-`, `m1+` interior** (`a+ < c+`): the sector rim `(v, m2-, xb, m2+)`. -/
theorem t095_4 (hA : F.a12 < F.a22) (hts : F.S.tm = F.S.sm) (hda : F.S.am < F.S.dp)
    (hac : F.S.ap < F.S.cp) : IsRupert (Finset.univ.image x) := by
  obtain ⟨ds, hd1, hd2⟩ := F.S.exists_ds hts hda
  have hkm := F.S.km_eq_hm_of_eq hts
  have hsp := F.S.sp_pos; have hsp1 := F.S.sp_lt; have htp := F.S.tp_pos; have htp1 := F.S.tp_lt
  have hhp := F.S.hp_pos; have hkp := F.S.kp_pos; have htm := F.S.tm_pos; have htm1 := F.S.tm_lt
  have hhm := F.S.hm_pos
  have roof := F.roof'
  have H31 := F.H31_of hac
  obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ := F.ptC_pts
  rw [← hts, hkm] at p6
  refine F.rupert_rim4 0 6 5 2 ⟨0, 0, 0⟩ ⟨0, F.S.tm, -F.S.hm⟩ ⟨0, 1, 0⟩ ⟨0, F.S.sp, F.S.kp⟩
    p0 p6 p5 p2 1 (Or.inl rfl) ⟨1, -1, 0⟩ ⟨ds, 0, -1⟩ (Or.inl one_ne_zero) ?_ ?_ ?_
  · exact t095_cyc4 hsp hsp1 htp htp1 hhp hkp htm htm1 hhm roof H31 hd1 hd2
  · intro j' h0 h6 h5 h2 i
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · rw [p1]; exact t095_rest1_4 hsp hsp1 htp htp1 hhp hkp htm htm1 hhm roof H31 hd1 hd2 i
    · exact absurd rfl h2
    · rw [p3]; exact t095_rest3_4 hsp hsp1 htp htp1 hhp hkp htm htm1 hhm roof H31 hd1 hd2 i
    · rw [p4]; exact t095_rest4_4 hsp hsp1 htp htp1 hhp hkp htm htm1 hhm roof H31 hd1 hd2 i
    · exact absurd rfl h5
    · exact absurd rfl h6
  · set Pq : ZMod 4 → C3 := quad ⟨0, 0, 0⟩ ⟨0, F.S.tm, -F.S.hm⟩ ⟨0, 1, 0⟩ ⟨0, F.S.sp, F.S.kp⟩
      with hPq
    set zz : ZMod 4 → ℝ := fun i => F.GG (Pq i) ⟨1, -1, 0⟩ with hzz
    set ww : ZMod 4 → ℝ := fun i => F.GG (Pq i) ⟨ds, 0, -1⟩ with hww
    have hd : 0 < F.a22 - F.a12 := sub_pos.2 hA
    refine Q4_eventually (z := zz) (w := ww) (Or.inr (Or.inr (Or.inl (Or.inl ?_))))
      (Or.inl (Or.inl ?_))
    · -- z 2 < z 1: `-be < -be t`
      simp only [hzz, hPq, GG, Gf, quad_1, quad_2]
      nlinarith [mul_pos (sub_pos.2 htm1) hd]
    · -- z 1 < z 0: `-be t < 0`
      simp only [hzz, hPq, GG, Gf, quad_0, quad_1]
      nlinarith [mul_pos htm hd]

/-- **09.5, case `d+ > a-`, `m1+` a corner** (`c+ < a+`, hence `t+ < s+`): the sector rim
`(v, m2-, xb, m2+, m1+)`, `Q5p` with all-strict witnesses (valid also at `A12 = A11`). -/
theorem t095_5 (hA : F.a12 < F.a22) (hts : F.S.tm = F.S.sm) (hda : F.S.am < F.S.dp)
    (hac : F.S.cp < F.S.ap) : IsRupert (Finset.univ.image x) := by
  obtain ⟨ds, hd1, hd2⟩ := F.S.exists_ds hts hda
  have hkm := F.S.km_eq_hm_of_eq hts
  have hsp := F.S.sp_pos; have hsp1 := F.S.sp_lt; have htp := F.S.tp_pos; have htp1 := F.S.tp_lt
  have hhp := F.S.hp_pos; have hkp := F.S.kp_pos; have htm := F.S.tm_pos; have htm1 := F.S.tm_lt
  have hhm := F.S.hm_pos
  have roof := F.roof'
  have H31 := F.H31'_of hac
  obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ := F.ptC_pts
  rw [← hts, hkm] at p6
  refine F.rupert_rim5p 0 6 5 2 1 ⟨0, 0, 0⟩ ⟨0, F.S.tm, -F.S.hm⟩ ⟨0, 1, 0⟩ ⟨0, F.S.sp, F.S.kp⟩
    ⟨F.S.tp, 0, F.S.hp⟩ p0 p6 p5 p2 p1 1 (Or.inl rfl) ⟨1, -1, 0⟩ ⟨ds, 0, -1⟩
    (Or.inl one_ne_zero) ?_ ?_ ?_
  · exact t095_cyc5 hsp hsp1 htp htp1 hhp hkp htm htm1 hhm roof H31 hd1 hd2
  · intro j' h0 h6 h5 h2 h1 i
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · exact absurd rfl h1
    · exact absurd rfl h2
    · rw [p3]; exact t095_rest3_5 hsp hsp1 htp htp1 hhp hkp htm htm1 hhm roof H31 hd1 hd2 i
    · rw [p4]; exact t095_rest4_5 hsp hsp1 htp htp1 hhp hkp htm htm1 hhm roof H31 hd1 hd2 i
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

/-- **09.5, case `t- = s-`, `d+ > a-`** (part B): Rupert, at every metric of `𝒞 ∪ 𝒞₁`
(`A12 < A22`, `A12 ≤ A11`), off `a+ = c+` (that case is not
a sector: `m1+` would lie on the side `(v, m2+)`).  Since `b+ < d+`, `c+ < a+` forces `t+ < s+`, so
`m1+` is a rim corner iff `c+ < a+`, and an interior point iff `a+ < c+`. -/
theorem rupert_of_tm_eq_sm_gt (hx : Function.Injective x) (hA : F.a12 < F.a22)
    (hts : F.S.tm = F.S.sm) (hda : F.S.am < F.S.dp) (hac : F.S.ap ≠ F.S.cp) :
    IsRupert (Finset.univ.image x) := by
  rcases lt_or_gt_of_ne hac with h | h
  · exact F.t095_4 hA hts hda h
  · exact F.t095_5 hA hts hda h

end Frame09

end Minimality.CaseC09
