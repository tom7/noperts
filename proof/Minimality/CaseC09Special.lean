module

public import Minimality.CaseC09Rims

@[expose] public section

/-!
# Type 09, acute case (c): removing special positions (`FEWER-FACES-PROOFS.md` §34.4.2)

The refereed proofs 09.1-09.4 and the
referee's fix 1 (the corner `a- = d+ ∧ b+ = s+A2`) shrink `CaseC09Special` to
`t- = s- ∨ A12 = A22 ∨ (a- = b+ ∧ b+ = s+A2)` (09.5 and the final definition are in
`CaseC09TS.lean`, which imports this file).

* 09.4 (`c+ = b-`): `Shape09.thm_27_58'`, the algebra of 27.58 with `c+ ≤ b-`.
* 09.1/09.2/09.3 (`a- = d+`, `b+ = s+A2`, `a- = b+`): the sector versions of the rim tests
  `rimT1`, `rimT2` (`rimT1_sector_dp`, `rimT1_sector_bp`, `rimT2_sector`), combined in
  `rupert_of_27_48_special` (including the corner, by the sum of the two failure inequalities).
* 09.5 (`t- = s-`) is in `CaseC09TS.lean`, (`CaseC09Special` and `isRupert_of_not_special` are in `CaseC09Ac.lean`).
-/

namespace Minimality.CaseC09

open Finset Filter
open scoped RealInnerProductSpace Topology

/-- **Theorem 27.58 with the special positions relaxed** (09.4, and the algebra of 09.1-09.3).
`c+ ≤ b-` replaces `c+ < b-`; `a- = d+`, `a- = b+` and `b+ = s+A2` are all allowed (for
`b+ > s+A2` and `a- ≤ b+`, `a- ≥ s+A2` Theorem 5 with `W = F1` applies, including `a- = b+`, 09.3).
The conclusion is the non-strict form of the five conditions of 27.48. -/
theorem Shape09.thm_27_58' (S : Shape09) (hts : S.tm < S.sm) (hca : S.cp < S.ap)
    (hcb : S.cp ≤ S.bm) (hAM : ¬ S.AM) (hT5 : ¬ S.T5F1) (hQ : ¬ S.Q3456) :
    S.bp ≤ S.am ∧ S.am ≤ S.dp ∧ S.cm < S.dp ∧ S.bp ≤ S.sp * S.A2 := by
  have had : S.am ≤ S.dp := by
    by_contra h
    exact hQ (S.q3456_of_lt hts (not_le.1 h))
  have hcmam := S.cm_lt_am hts
  have hcmd : S.cm < S.dp := hcmam.trans_le had
  have hspA : S.sp * S.A2 = S.kp + S.sp * S.cm := S.sp_A2
  have hbm := S.bm_pos; have hbp := S.bp_pos; have hkp := S.kp_pos
  have hsp := S.sp_pos; have hsp1 := S.sp_lt; have htm := S.tm_pos
  have hmm : S.bm * (1 - S.tm) = S.hm := S.bm_mul
  have hamm : S.am * S.tm = S.hm := S.am_mul
  have hAM3 : S.hm < S.kp * S.tm + S.dm * (1 - S.sp * S.tm) := by
    rw [S.dm_eq]
    nlinarith [mul_pos hkp htm, mul_pos (mul_pos hbm htm) (sub_pos.2 hsp1)]
  -- a case (III) contradiction when `b+ > s+A2` and `a- ≤ b+`
  have caseIII : S.am ≤ S.bp → S.sp * S.A2 < S.bp → False := by
    intro h h3
    have h2 : S.sp * S.A2 ≤ S.am := by
      by_contra hh
      rw [not_le] at hh
      refine hAM ⟨hcmd, ?_, hAM3⟩
      nlinarith [mul_lt_mul_of_pos_right hh htm, hspA]
    exact hT5 (S.t5_case_III hts hca hcb h h3 h2)
  refine ⟨?_, had, hcmd, ?_⟩
  · by_contra h
    rw [not_le] at h
    by_cases h3 : S.bp ≤ S.sp * S.A2
    · refine hAM ⟨hcmd, ?_, hAM3⟩
      nlinarith [mul_lt_mul_of_pos_right (h.trans_le h3) htm, hspA]
    · exact caseIII h.le (not_le.1 h3)
  · by_contra h3
    rw [not_le] at h3
    rcases le_or_gt S.am S.bp with h | h
    · exact caseIII h h3
    · exact hT5 (S.t5_case_I hts hca hcb h h3)

section T09S
variable {tp hp tm hm sp kp sm km : ℝ}

theorem t1_cycE (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1)
    (hhm : 0 < hm) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km)
    (H2 : hm * (1 - sp) = tm * kp) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST (-1) ⟨tm, 0, -hm⟩ ⟨0, 1, 0⟩
        ((t1P tm hm sp kp sm km (i + 1)).sub (t1P tm hm sp kp sm km i))
        ((t1P tm hm sp kp sm km j).sub (t1P tm hm sp kp sm km i)) := by
  have hsp' : 0 < 1 - sp := by linarith
  have hsm' : 0 < 1 - sm := by linarith
  have htm' : 0 < 1 - tm := by linarith
  have a1 := mul_pos hsp hhm
  have a2 := mul_pos htm hkp
  have a3 := mul_pos hsm hhm
  have a4 := mul_pos htm hkm
  have a5 := mul_pos (mul_pos htm hsp) hkm
  have a6 := mul_pos (mul_pos htm hsm) hkp
  have a7 := mul_pos hsm' hkp
  have a8 := mul_pos hsp' hkm
  have a9 := mul_pos htm (add_pos a7 a8)
  have a10 := mul_pos hsp (add_pos (mul_pos hsm' hhm) a4)
  have a12 := mul_pos hsm' hhm
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i j h1 h2
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [ST, Dc, C3.sub, t1P, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3,
      quint_4]
    first
    | (left; nlinarith)
    | (right; refine ⟨by nlinarith, by nlinarith⟩)

theorem t1_rest1E (hsp : 0 < sp) (hsp1 : sp < 1) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1) (hhm : 0 < hm) (hsm : 0 < sm) (hsm1 : sm < 1)
    (hkm : 0 < km) (H1 : hp * tm + hm * tp < hm) (H2 : hm * (1 - sp) = tm * kp) :
    ∀ i : ZMod 5,
      ST (-1) ⟨tm, 0, -hm⟩ ⟨0, 1, 0⟩
        ((t1P tm hm sp kp sm km (i + 1)).sub (t1P tm hm sp kp sm km i))
        ((⟨tp, 0, hp⟩ : C3).sub (t1P tm hm sp kp sm km i)) := by
  have hsp' : 0 < 1 - sp := by linarith
  have hsm' : 0 < 1 - sm := by linarith
  have htm' : 0 < 1 - tm := by linarith
  have htp' : 0 < 1 - tp := by linarith
  have q1 := sub_pos.2 H1
  have a1 := mul_pos hsp hhm
  have a2 := mul_pos htm hkp
  have a4 := mul_pos htm hkm
  have a9 := mul_pos hsp q1
  have a10 := mul_pos hsp' q1
  have a11 := mul_pos hsp' hhm
  have a12 := mul_pos htp hhm
  have a13 := mul_pos htm hhp
  have a14 := mul_pos hsm' (mul_pos htp hhm)
  have a15 := mul_pos hsm' (mul_pos htm hhp)
  have a16 := mul_pos hsm (mul_pos htp hhm)
  have a17 := mul_pos hsm (mul_pos htm hhp)
  have a18 := mul_pos hsm hhm
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, t1P, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3,
      quint_4]
    first
    | (left; nlinarith)
    | (right; refine ⟨by nlinarith, by nlinarith⟩)

theorem t2_rest1E (hsp : 0 < sp) (hsp1 : sp < 1) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1) (hhm : 0 < hm) (hsm : 0 < sm) (hsm1 : sm < 1)
    (hkm : 0 < km) (H3 : sm * hp = (km * sp + sm * kp) * (1 - tp)) :
    ∀ i : ZMod 4,
      ST (-1) ⟨0, sm, -km⟩ ⟨-1, 0, 0⟩
        ((t2P tm hm sp kp (i + 1)).sub (t2P tm hm sp kp i))
        ((⟨tp, 0, hp⟩ : C3).sub (t2P tm hm sp kp i)) := by
  have hsp' : 0 < 1 - sp := by linarith
  have hsm' : 0 < 1 - sm := by linarith
  have htm' : 0 < 1 - tm := by linarith
  have htp' : 0 < 1 - tp := by linarith
  have a1 := mul_pos hsm (mul_pos htp hhm)
  have a2 := mul_pos hsm (mul_pos htm hhp)
  have a3 := mul_pos hsm (mul_pos htp' hhm)
  have a4 := mul_pos hsm (mul_pos htm' hhp)
  have a5 := mul_pos hsm hhp
  have a6 := mul_pos hsm hhm
  have a7 := mul_pos hsp hkm
  have a8 := mul_pos hsm hkp
  have a9 := mul_pos htp (add_pos a7 a8)
  have a10 := mul_pos htp' (add_pos a7 a8)
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, t2P, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith)
    | (right; refine ⟨by nlinarith, by nlinarith⟩)

theorem t1_cycD (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1)
    (hhm : 0 < hm) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km)
    (H2 : hm * (1 - sp) < tm * kp) (dx : ℝ) (hl : -(tm * km) < dx * (sm * hm)) (hr : dx * (sp * hm) < tm * kp - hm) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST (-1) ⟨tm, 0, -hm⟩ ⟨dx, 1, 0⟩
        ((t1P tm hm sp kp sm km (i + 1)).sub (t1P tm hm sp kp sm km i))
        ((t1P tm hm sp kp sm km j).sub (t1P tm hm sp kp sm km i)) := by
  have hsp' : 0 < 1 - sp := by linarith
  have hsm' : 0 < 1 - sm := by linarith
  have htm' : 0 < 1 - tm := by linarith
  have q2 := sub_pos.2 H2
  have a1 := mul_pos hsp hhm
  have a2 := mul_pos htm hkp
  have a3 := mul_pos hsm hhm
  have a4 := mul_pos htm hkm
  have a5 := mul_pos (mul_pos htm hsp) hkm
  have a6 := mul_pos (mul_pos htm hsm) hkp
  have a7 := mul_pos hsm' hkp
  have a8 := mul_pos hsp' hkm
  have a9 := mul_pos htm (add_pos a7 a8)
  have a10 := mul_pos hsp (add_pos (mul_pos hsm' hhm) a4)
  have a11 := mul_pos hsm q2
  have a12 := mul_pos hsm' hhm
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i j h1 h2
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [ST, Dc, C3.sub, t1P, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3,
      quint_4]
    first
    | (left; nlinarith)
    | (right; refine ⟨by nlinarith, by nlinarith⟩)

theorem t1_rest0D (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1)
    (hhm : 0 < hm) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km) (dx : ℝ) (hl : -(tm * km) < dx * (sm * hm)) (hr : dx * (sp * hm) < tm * kp - hm) :
    ∀ i : ZMod 5,
      ST (-1) ⟨tm, 0, -hm⟩ ⟨dx, 1, 0⟩
        ((t1P tm hm sp kp sm km (i + 1)).sub (t1P tm hm sp kp sm km i))
        ((⟨0, 0, 0⟩ : C3).sub (t1P tm hm sp kp sm km i)) := by
  have hsp' : 0 < 1 - sp := by linarith
  have hsm' : 0 < 1 - sm := by linarith
  have htm' : 0 < 1 - tm := by linarith
  have a1 := mul_pos hsp hhm
  have a2 := mul_pos htm hkp
  have a3 := mul_pos hsm hhm
  have a4 := mul_pos htm hkm
  have a5 := mul_pos (mul_pos htm hsp) hkm
  have a6 := mul_pos (mul_pos htm hsm) hkp
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, t1P, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3,
      quint_4]
    first
    | (left; nlinarith)
    | (right; refine ⟨by nlinarith, by nlinarith⟩)

theorem t1_rest1D (hsp : 0 < sp) (hsp1 : sp < 1) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1) (hhm : 0 < hm) (hsm : 0 < sm) (hsm1 : sm < 1)
    (hkm : 0 < km) (H1 : hp * tm + hm * tp = hm) (H2 : hm * (1 - sp) < tm * kp) (dx : ℝ) (hl : -(tm * km) < dx * (sm * hm)) (hr : dx * (sp * hm) < tm * kp - hm) :
    ∀ i : ZMod 5,
      ST (-1) ⟨tm, 0, -hm⟩ ⟨dx, 1, 0⟩
        ((t1P tm hm sp kp sm km (i + 1)).sub (t1P tm hm sp kp sm km i))
        ((⟨tp, 0, hp⟩ : C3).sub (t1P tm hm sp kp sm km i)) := by
  have hsp' : 0 < 1 - sp := by linarith
  have hsm' : 0 < 1 - sm := by linarith
  have htm' : 0 < 1 - tm := by linarith
  have htp' : 0 < 1 - tp := by linarith
  have q2 := sub_pos.2 H2
  have a1 := mul_pos hsp hhm
  have a2 := mul_pos htm hkp
  have a4 := mul_pos htm hkm
  have a11 := mul_pos hsp' hhm
  have a12 := mul_pos htp hhm
  have a13 := mul_pos htm hhp
  have a14 := mul_pos hsm' (mul_pos htp hhm)
  have a15 := mul_pos hsm' (mul_pos htm hhp)
  have a16 := mul_pos hsm (mul_pos htp hhm)
  have a17 := mul_pos hsm (mul_pos htm hhp)
  have a18 := mul_pos hsm hhm
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, t1P, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3,
      quint_4]
    first
    | (left; nlinarith)
    | (right; refine ⟨by nlinarith, by nlinarith⟩)

end T09S

namespace Frame09

variable {x : Fin 7 → ℝ³} (F : Frame09 x)

/-- **09.1 `T1` sector at `a- = d+`**: `m2+` lies on the open segment `xa xb`; the sector at
`d = e_y` shows `m2+`.  Unimodal when `g h- k- > A12 t- (1 - s-)`. -/
theorem rimT1_sector_dp (hts : F.S.tm < F.S.sm) (H1 : F.S.bp < F.S.am)
    (H2 : F.S.am = F.S.dp)
    (hS : F.a12 * F.S.tm * (1 - F.S.sm) < F.gg * F.S.hm * F.S.km) :
    IsRupert (Finset.univ.image x) := by
  have H2e : F.S.hm * (1 - F.S.sp) = F.S.tm * F.S.kp := by
    have h1 := F.S.dp_mul; have h2 := F.S.am_mul
    rw [← h2, H2, ← h1]; ring
  have H1' := F.S.t48_T1_m1p_inside.2 H1
  have hsp := F.S.sp_pos; have hsp1 := F.S.sp_lt; have htp := F.S.tp_pos; have htp1 := F.S.tp_lt
  have hhp := F.S.hp_pos; have hkp := F.S.kp_pos; have htm := F.S.tm_pos; have htm1 := F.S.tm_lt
  have hhm := F.S.hm_pos; have hsm := F.S.sm_pos; have hsm1 := F.S.sm_lt; have hkm := F.S.km_pos
  have hA : 0 < F.a12 := F.A12_pos
  have hA11 : F.a12 ≤ F.a11 := F.A12_le_A11
  have hg : 0 < F.gg := F.g_pos
  obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ := F.ptC_pts
  refine F.rupert_rim5t 4 3 2 5 6 ⟨F.S.tm, 0, -F.S.hm⟩ ⟨1, 0, 0⟩ ⟨0, F.S.sp, F.S.kp⟩ ⟨0, 1, 0⟩
    ⟨0, F.S.sm, -F.S.km⟩ p4 p3 p2 p5 p6 (-1) (Or.inr rfl) ⟨F.S.tm, 0, -F.S.hm⟩ ⟨0, 1, 0⟩
    (Or.inl (ne_of_gt htm)) ?_ ?_ ?_
  · exact t1_cycE hsp hsp1 hkp htm htm1 hhm hsm hsm1 hkm H2e
  · intro j' h4 h3 h2 h5 h6 i
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [p0]; exact t1_rest0 hsp hsp1 hkp htm htm1 hhm hsm hsm1 hkm i
    · rw [p1]; exact t1_rest1E hsp hsp1 htp htp1 hhp hkp htm htm1 hhm hsm hsm1 hkm H1' H2e i
    · exact absurd rfl h2
    · exact absurd rfl h3
    · exact absurd rfl h4
    · exact absurd rfl h5
    · exact absurd rfl h6
  · set zz : ZMod 5 → ℝ := fun i => F.GG (t1P F.S.tm F.S.hm F.S.sp F.S.kp F.S.sm F.S.km i)
      ⟨F.S.tm, 0, -F.S.hm⟩ with hzz
    set ww : ZMod 5 → ℝ := fun i => F.GG (t1P F.S.tm F.S.hm F.S.sp F.S.kp F.S.sm F.S.km i)
      ⟨0, 1, 0⟩ with hww
    have e0 : zz 0 = F.a11 * F.S.tm * F.S.tm + F.gg * F.S.hm * F.S.hm := by
      simp only [hzz, t1P, GG, Gf, quint_0]; ring
    have e1 : zz 1 = F.a11 * F.S.tm := by
      simp only [hzz, t1P, GG, Gf, quint_1]; ring
    have e2 : zz 2 = F.a12 * F.S.tm * F.S.sp - F.gg * F.S.hm * F.S.kp := by
      simp only [hzz, t1P, GG, Gf, quint_2]; ring
    have e3 : zz 3 = F.a12 * F.S.tm := by
      simp only [hzz, t1P, GG, Gf, quint_3]; ring
    have e4 : zz 4 = F.a12 * F.S.tm * F.S.sm + F.gg * F.S.hm * F.S.km := by
      simp only [hzz, t1P, GG, Gf, quint_4]; ring
    have hz40 := t1_z4_lt_z0 (g := F.gg) hA hA11 htm htm1 hsm1 hts hhm F.Km_eq hS
    have m1 := mul_pos hA htm
    have m2 := mul_pos hg hhm
    have m3 := mul_pos m2 hkp
    have m4 := mul_pos m1 hsp
    have m5 := mul_nonneg m1.le (sub_nonneg.2 hA11)
    refine Q5t_eventually (z := zz) (w := ww) ?_ ?_ ?_ ?_
    · rw [e1, e2]; nlinarith [mul_pos m1 (sub_pos.2 hsp1), mul_le_mul_of_nonneg_left hA11 htm.le]
    · rw [e2, e3]; nlinarith [mul_pos m1 (sub_pos.2 hsp1)]
    · rw [e3, e4]; nlinarith
    · rw [e4, e0]; nlinarith

/-- **09.3 `T1` sector at `a- = b+`** (`b+ < s+A2`): `m1+` is a double over the corner `xa`;
the sector at `d = (d_x, 1, 0)`, `d_x` in an interval nonempty iff `a- < s+A2`. -/
theorem rimT1_sector_bp (hts : F.S.tm < F.S.sm) (H1 : F.S.am = F.S.bp)
    (H2 : F.S.am < F.S.dp) (H3 : F.S.bp < F.S.sp * F.S.A2)
    (hS : F.a12 * F.S.tm * (1 - F.S.sm) < F.gg * F.S.hm * F.S.km) :
    IsRupert (Finset.univ.image x) := by
  have H1e : F.S.hp * F.S.tm + F.S.hm * F.S.tp = F.S.hm := by
    have h1 := F.S.bp_mul; have h2 := F.S.am_mul
    rw [← h2, H1, ← h1]; ring
  have H2' := F.S.t48_T1_m2p_above.2 H2
  have H3' := F.S.t48_T2_m1p_below.2 (by rw [← F.S.sp_A2]; exact H3)
  have hsp := F.S.sp_pos; have hsp1 := F.S.sp_lt; have htp := F.S.tp_pos; have htp1 := F.S.tp_lt
  have hhp := F.S.hp_pos; have hkp := F.S.kp_pos; have htm := F.S.tm_pos; have htm1 := F.S.tm_lt
  have hhm := F.S.hm_pos; have hsm := F.S.sm_pos; have hsm1 := F.S.sm_lt; have hkm := F.S.km_pos
  obtain ⟨dx, hl, hr⟩ : ∃ dx : ℝ, -(F.S.tm * F.S.km) < dx * (F.S.sm * F.S.hm) ∧
      dx * (F.S.sp * F.S.hm) < F.S.tm * F.S.kp - F.S.hm := by
    have hsh := mul_pos hsm hhm
    have hph := mul_pos hsp hhm
    have key : -(F.S.tm * F.S.km) / (F.S.sm * F.S.hm) <
        (F.S.tm * F.S.kp - F.S.hm) / (F.S.sp * F.S.hm) := by
      rw [div_lt_div_iff₀ hsh hph]
      have h1 : F.S.hm * F.S.sm * (1 - F.S.tp) < F.S.tm * (F.S.km * F.S.sp + F.S.sm * F.S.kp) * (1 - F.S.tp) := by
        have := mul_lt_mul_of_pos_left H3' htm
        nlinarith [this, H1e]
      have h2 : F.S.hm * F.S.sm < F.S.tm * (F.S.km * F.S.sp + F.S.sm * F.S.kp) :=
        lt_of_mul_lt_mul_right h1 (sub_pos.2 htp1).le
      nlinarith [h2, mul_pos hsm hhm]
    obtain ⟨d, hd1, hd2⟩ := exists_between key
    refine ⟨d, ?_, ?_⟩
    · rwa [div_lt_iff₀ hsh] at hd1
    · rwa [lt_div_iff₀ hph] at hd2
  have hA : 0 < F.a12 := F.A12_pos
  have hA11 : F.a12 ≤ F.a11 := F.A12_le_A11
  have hg : 0 < F.gg := F.g_pos
  obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ := F.ptC_pts
  refine F.rupert_rim5t 4 3 2 5 6 ⟨F.S.tm, 0, -F.S.hm⟩ ⟨1, 0, 0⟩ ⟨0, F.S.sp, F.S.kp⟩ ⟨0, 1, 0⟩
    ⟨0, F.S.sm, -F.S.km⟩ p4 p3 p2 p5 p6 (-1) (Or.inr rfl) ⟨F.S.tm, 0, -F.S.hm⟩ ⟨dx, 1, 0⟩
    (Or.inl (ne_of_gt htm)) ?_ ?_ ?_
  · exact t1_cycD hsp hsp1 hkp htm htm1 hhm hsm hsm1 hkm H2' dx hl hr
  · intro j' h4 h3 h2 h5 h6 i
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [p0]; exact t1_rest0D hsp hsp1 hkp htm htm1 hhm hsm hsm1 hkm dx hl hr i
    · rw [p1]; exact t1_rest1D hsp hsp1 htp htp1 hhp hkp htm htm1 hhm hsm hsm1 hkm H1e H2' dx hl hr i
    · exact absurd rfl h2
    · exact absurd rfl h3
    · exact absurd rfl h4
    · exact absurd rfl h5
    · exact absurd rfl h6
  · clear hl hr H1e H2' H3' H1 H2 H3
    set zz : ZMod 5 → ℝ := fun i => F.GG (t1P F.S.tm F.S.hm F.S.sp F.S.kp F.S.sm F.S.km i)
      ⟨F.S.tm, 0, -F.S.hm⟩ with hzz
    set ww : ZMod 5 → ℝ := fun i => F.GG (t1P F.S.tm F.S.hm F.S.sp F.S.kp F.S.sm F.S.km i)
      ⟨dx, 1, 0⟩ with hww
    have e0 : zz 0 = F.a11 * F.S.tm * F.S.tm + F.gg * F.S.hm * F.S.hm := by
      simp only [hzz, t1P, GG, Gf, quint_0]; ring
    have e1 : zz 1 = F.a11 * F.S.tm := by
      simp only [hzz, t1P, GG, Gf, quint_1]; ring
    have e2 : zz 2 = F.a12 * F.S.tm * F.S.sp - F.gg * F.S.hm * F.S.kp := by
      simp only [hzz, t1P, GG, Gf, quint_2]; ring
    have e3 : zz 3 = F.a12 * F.S.tm := by
      simp only [hzz, t1P, GG, Gf, quint_3]; ring
    have e4 : zz 4 = F.a12 * F.S.tm * F.S.sm + F.gg * F.S.hm * F.S.km := by
      simp only [hzz, t1P, GG, Gf, quint_4]; ring
    have hz40 := t1_z4_lt_z0 (g := F.gg) hA hA11 htm htm1 hsm1 hts hhm F.Km_eq hS
    have m1 := mul_pos hA htm
    have m2 := mul_pos hg hhm
    have m3 := mul_pos m2 hkp
    have m4 := mul_pos m1 hsp
    have m5 := mul_nonneg m1.le (sub_nonneg.2 hA11)
    refine Q5t_eventually (z := zz) (w := ww) ?_ ?_ ?_ ?_
    · rw [e1, e2]; nlinarith [mul_pos m1 (sub_pos.2 hsp1), mul_le_mul_of_nonneg_left hA11 htm.le]
    · rw [e2, e3]; nlinarith [mul_pos m1 (sub_pos.2 hsp1)]
    · rw [e3, e4]; nlinarith
    · rw [e4, e0]; nlinarith

/-- **09.2 `T2` sector at `b+ = s+A2`**: `m1+` lies on the side `(m2+, xa)`; the sector at
`d = -e_x` hides `m1+`.  Unimodal when `g h- k- < A12 s- (1 - t-)`. -/
theorem rimT2_sector (H3 : F.S.bp = F.S.sp * F.S.A2) (H4 : F.S.cm < F.S.dp)
    (hS : F.gg * F.S.hm * F.S.km < F.a12 * F.S.sm * (1 - F.S.tm)) :
    IsRupert (Finset.univ.image x) := by
  have H3e : F.S.sm * F.S.hp = (F.S.km * F.S.sp + F.S.sm * F.S.kp) * (1 - F.S.tp) := by
    have h1 := F.S.bp_mul; have h2 := F.S.cm_mul
    have h3 : F.S.bp = F.S.kp + F.S.sp * F.S.cm := by rw [H3, F.S.sp_A2]
    rw [← h1, ← h2, h3]; ring
  have H4' := F.A1_of H4
  have hsp := F.S.sp_pos; have hsp1 := F.S.sp_lt; have htp := F.S.tp_pos; have htp1 := F.S.tp_lt
  have hhp := F.S.hp_pos; have hkp := F.S.kp_pos; have htm := F.S.tm_pos; have htm1 := F.S.tm_lt
  have hhm := F.S.hm_pos; have hsm := F.S.sm_pos; have hsm1 := F.S.sm_lt; have hkm := F.S.km_pos
  have hA : 0 < F.a12 := F.A12_pos
  have hg : 0 < F.gg := F.g_pos
  obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ := F.ptC_pts
  refine F.rupert_rim4 0 4 3 2 ⟨0, 0, 0⟩ ⟨F.S.tm, 0, -F.S.hm⟩ ⟨1, 0, 0⟩ ⟨0, F.S.sp, F.S.kp⟩
    p0 p4 p3 p2 (-1) (Or.inr rfl) ⟨0, F.S.sm, -F.S.km⟩ ⟨-1, 0, 0⟩
    (Or.inr (Or.inl (ne_of_gt hsm))) ?_ ?_ ?_
  · exact t2_cyc hsp hsp1 hkp htm htm1 hhm hsm hsm1 hkm
  · intro j' h0 h4 h3 h2 i
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · rw [p1]; exact t2_rest1E hsp hsp1 htp htp1 hhp hkp htm htm1 hhm hsm hsm1 hkm H3e i
    · exact absurd rfl h2
    · exact absurd rfl h3
    · exact absurd rfl h4
    · rw [p5]; exact t2_rest5 hsp hsp1 hkp htm htm1 hhm hsm hsm1 hkm H4' i
    · rw [p6]; exact t2_rest6 hsp hsp1 hkp htm htm1 hhm hsm hsm1 hkm i
  · set zz : ZMod 4 → ℝ := fun i => F.GG (t2P F.S.tm F.S.hm F.S.sp F.S.kp i)
      ⟨0, F.S.sm, -F.S.km⟩ with hzz
    set ww : ZMod 4 → ℝ := fun i => F.GG (t2P F.S.tm F.S.hm F.S.sp F.S.kp i)
      ⟨-1, 0, 0⟩ with hww
    have e0 : zz 0 = 0 := by
      simp only [hzz, t2P, GG, Gf, quad_0]; ring
    have e1 : zz 1 = F.a12 * F.S.tm * F.S.sm + F.gg * F.S.hm * F.S.km := by
      simp only [hzz, t2P, GG, Gf, quad_1]; ring
    have e2 : zz 2 = F.a12 * F.S.sm := by
      simp only [hzz, t2P, GG, Gf, quad_2]; ring
    have m1 := mul_pos (mul_pos hA htm) hsm
    have m2 := mul_pos (mul_pos hg hhm) hkm
    refine Q4_eventually (z := zz) (w := ww) (Or.inl (Or.inl ?_))
      (Or.inr (Or.inr (Or.inl (Or.inl ?_))))
    · rw [e0, e1]; linarith
    · rw [e1, e2]; nlinarith

/-- **09.1-09.3 and fix 1, combined**: under the non-strict conclusion of
`Shape09.thm_27_58'` and off the corner `a- = b+ ∧ b+ = s+A2`, one of the tests
(`rimT1`/`rimT1_sector_dp`/`rimT1_sector_bp`, `rimT2`/`rimT2_sector`) is unimodal, by
`t48_contra` (the failure inequalities sum to `A12 (t- - s-) ≥ 0`). -/
theorem rupert_of_27_48_special (hts : F.S.tm < F.S.sm) (h1 : F.S.bp ≤ F.S.am)
    (h2 : F.S.am ≤ F.S.dp) (h3 : F.S.cm < F.S.dp) (h4 : F.S.bp ≤ F.S.sp * F.S.A2)
    (hc : ¬ (F.S.am = F.S.bp ∧ F.S.bp = F.S.sp * F.S.A2)) :
    IsRupert (Finset.univ.image x) := by
  have hA : 0 < F.a12 := F.A12_pos
  have H4 := F.A1_of h3
  have T1 : F.a12 * F.S.tm * (1 - F.S.sm) < F.gg * F.S.hm * F.S.km →
      IsRupert (Finset.univ.image x) := by
    intro hS
    rcases h1.lt_or_eq with b | b
    · rcases h2.lt_or_eq with a | a
      · exact F.rimT1 hts (F.S.t48_T1_m1p_inside.2 b) (F.S.t48_T1_m2p_above.2 a) hS
      · exact F.rimT1_sector_dp hts b a hS
    · have a : F.S.am < F.S.dp := by
        refine lt_of_le_of_ne h2 (fun e => ?_)
        have := F.S.bp_lt_dp
        rw [b, e] at this
        exact lt_irrefl _ this
      have c : F.S.bp < F.S.sp * F.S.A2 :=
        lt_of_le_of_ne h4 (fun e => hc ⟨b.symm, e⟩)
      exact F.rimT1_sector_bp hts b.symm a c hS
  have T2 : F.gg * F.S.hm * F.S.km < F.a12 * F.S.sm * (1 - F.S.tm) →
      IsRupert (Finset.univ.image x) := by
    intro hS
    rcases h4.lt_or_eq with c | c
    · exact F.rimT2 (F.S.t48_T2_m1p_below.2 (by rw [← F.S.sp_A2]; exact c)) H4 hS
    · exact F.rimT2_sector c h3 hS
  by_cases hc1 : F.a12 * F.S.tm * (1 - F.S.sm) < F.gg * F.S.hm * F.S.km
  · exact T1 hc1
  · refine T2 ?_
    by_contra hn
    refine F.S.t48_contra hA hts (not_lt.mp hc1) ?_
    nlinarith [not_lt.mp hn]

/-- **`rupert_or_27_48'` with the special positions relaxed** (the flow of 27.58 with
`Shape09.thm_27_58'`): off `t- = s-` and `a+ = c+`, either `V` is Rupert or the non-strict
conditions of 27.48 hold. -/
theorem rupert_or_27_48'' (hx : Function.Injective x) (hA : F.a12 < F.a22)
    (sp0 : F.S.tm ≠ F.S.sm) (sp4 : F.S.ap ≠ F.S.cp) :
    IsRupert (Finset.univ.image x) ∨
      (F.S.tm < F.S.sm ∧ F.S.bp ≤ F.S.am ∧ F.S.am ≤ F.S.dp ∧ F.S.cm < F.S.dp ∧
        F.S.bp ≤ F.S.sp * F.S.A2) := by
  have T := F.tests09 hA
  by_cases hts : F.S.tm < F.S.sm
  swap
  · exact Or.inl (T.t31 sp0 sp4 (Or.inl hts))
  by_cases hca : F.S.cp < F.S.ap
  swap
  · exact Or.inl (T.t31 sp0 sp4 (Or.inr hca))
  by_cases hcb : F.S.cp ≤ F.S.bm
  swap
  · exact Or.inl (T.t32 (ne_of_gt (not_le.1 hcb)) (not_lt.2 (not_le.1 hcb).le))
  by_cases hAM : F.S.AM
  · exact Or.inl (T.am hAM)
  by_cases hT5 : F.S.T5F1
  · exact Or.inl (F.rupert_of_T5F1 hx hT5)
  by_cases hQ : F.S.Q3456
  · exact Or.inl (F.rupert_of_Q3456 hx hQ)
  obtain ⟨a, b, c, d⟩ := F.S.thm_27_58' hts hca hcb hAM hT5 hQ
  exact Or.inr ⟨hts, a, b, c, d⟩

end Frame09

end Minimality.CaseC09

end
