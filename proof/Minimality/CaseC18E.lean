module

public import Minimality.CaseC18M
public import Minimality.CaseC18Fo

@[expose] public section

/-!
# Type 18, acute case (c): PROOFS sections 37-38 (Theorems E, E2, W, C, R', F and E*)

All theorems are PROVED (no `sorry`), and so is the final assembly `CaseC18Special'.isRupert`:
type 18 has no special position left.  History and per-group notes: `nopert229/out/bottleneck/sp18d/handoff_lean.md`.
Paper: `FEWER-FACES-PROOFS.md` "## 37." (Theorems E, E1, E2, W, C, R', F) and "## 38." (E*);
the referee's fixes at the top of each section override the text.

Order of the case split on `CaseC18Special' x` (see `CaseC18Special'.isRupert` at the end):
* disjunct 1 (R1' residual): `thmF` (TF+), `thmFz` (TF-), else `thmRp`;
* disjunct 2 (`L_M'`): `thmE1` (`c- < d+`), `thmE2` (`c- = d+`, `s+ + s- != 1`), `thmW`
  (`Q`, off `E_W`), `thmEstar` (`E_W`);  disjunct 3: the same on `F.zFrame`;
* disjunct 4 (corner `Z`-image): `thmC` on `F.zFrame`;  disjunct 5 (corner): `thmC`.
-/

namespace Minimality.CaseC18

open Finset Filter Minimality.CaseC09
open scoped RealInnerProductSpace Topology

set_option maxHeartbeats 1000000 in
theorem rimH_cyc (tm hm tp hp sp kp d1 d3 : ℝ) (htm : 0 < tm) (hhm : 0 < hm) (htp : 0 < tp) (hhp : 0 < hp)
    (htp1 : tp < 1) (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (htm1 : tm < 1)
    (hroof : kp * (1 - tp) < hp * (1 - sp)) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨tp, -1, hp⟩ ⟨d1, 0, d3⟩
        ((quint (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ i))
        ((quint (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ j).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ i)) := by
  have a1 := sub_pos.2 htp1
  have a2 := sub_pos.2 hsp1
  have a3 := sub_pos.2 htm1
  have a4 := sub_pos.2 hroof
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i j h1 h2
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    left
    nlinarith [mul_pos htm hhm, mul_pos htm hhp, mul_pos hhm htp, mul_pos hhp a1, mul_pos hhm a1, mul_pos a1 hsp, mul_pos a2 hsp, mul_pos hhp hsp, mul_pos hhm hsp, mul_pos htp hkp, mul_pos a1 hkp, mul_pos htm hkp, mul_pos hsp hkp, mul_pos hhp htm, mul_pos a3 hhp, mul_pos a3 hkp, mul_pos htp hsp, mul_pos a4 htp, mul_pos a4 htm, mul_pos a4 a3, mul_pos a2 hhp, mul_pos a2 hkp, mul_pos a2 hhm]
set_option maxHeartbeats 1000000 in
theorem rimH_rest (tm hm tp hp sp kp sm km d1 d3 : ℝ) (htm : 0 < tm) (hhm : 0 < hm) (htp : 0 < tp) (hhp : 0 < hp)
    (htp1 : tp < 1) (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (htm1 : tm < 1)
    (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km)
    (hroof : kp * (1 - tp) < hp * (1 - sp)) (hroofm : km * (1 - tm) < hm * (1 - sm))
    (hc : tm * km < sm * (tm * hp + hm * tp))
    (hDa : 0 < -hp * d1 - (1 - tp) * d3)
    (hDb : 0 < -((kp - hp * (1 - sp)) * d1 + tp * (1 - sp) * d3)) (w : C3)
    (hw : w = ⟨0, 1, 0⟩ ∨ w = ⟨0, sm, -km⟩) :
    ∀ i : ZMod 5,
      ST 1 ⟨tp, -1, hp⟩ ⟨d1, 0, d3⟩
        ((quint (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ i))
        (w.sub (quint (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ i)) := by
  have a1 := sub_pos.2 htp1
  have a2 := sub_pos.2 hsp1
  have a3 := sub_pos.2 htm1
  have a4 := sub_pos.2 hroof
  have a5 := sub_pos.2 hsm1
  have a6 := sub_pos.2 hroofm
  have a7 := sub_pos.2 hc
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases hw with rfl | rfl <;>
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith [mul_pos htm hhm, mul_pos htm hhp, mul_pos hhm htp, mul_pos hhp a1, mul_pos hhm a1, mul_pos a1 hsp, mul_pos a2 hsp, mul_pos hhp hsp, mul_pos hhm hsp, mul_pos htp hkp, mul_pos a1 hkp, mul_pos htm hkp, mul_pos hsp hkp, mul_pos hhp htm, mul_pos a3 hhp, mul_pos a3 hkp, mul_pos htp hsp, mul_pos a4 htp, mul_pos a4 htm, mul_pos a4 a3, mul_pos a2 hhp, mul_pos a2 hkp, mul_pos a2 hhm, mul_pos a6 htp, mul_pos a6 hsp, mul_pos a6 hhp, mul_pos a7 hsp, mul_pos a7 htp, mul_pos a5 hhm, mul_pos a5 htm, mul_pos hsm hhp, mul_pos hkm htp, mul_pos hkm hsp, mul_pos a4 hsm, mul_pos a6 a1, mul_pos a7 a1])
    | (right; constructor
       · ring1
       · nlinarith [mul_pos a1 hDa, mul_pos a2 hDb, mul_pos htp hDa, hDa, hDb, mul_pos hsp hDa, mul_pos hsp hDb, mul_pos a2 hDa, mul_pos a1 hDb, mul_pos htp hDb])

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
theorem robust_cycH {a1 a2 a3 a4 : ℝ} (h1 : 0 < a1) (h2 : a1 < a2) (h4 : a4 < a3) :
    IsRobustUnimodal (k := 5) (fun i : ZMod 5 => ![0, a1, a2, a3, a4] i) := by
  have hB : ∀ B : ZMod 5, B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by decide
  refine ⟨?_, ?_, ?_⟩
  · intro B a b c d hab hbc hcd hdk
    interval_cases d <;> interval_cases c <;> (try omega) <;> interval_cases b <;> (try omega) <;> interval_cases a <;> (try omega) <;> rcases hB B with rfl | rfl | rfl | rfl | rfl <;> norm_num <;> intros <;> skip <;> linarith
  · intro i j l hij hjl hil e1 e2
    rcases hB i with rfl | rfl | rfl | rfl | rfl <;> rcases hB j with rfl | rfl | rfl | rfl | rfl <;> rcases hB l with rfl | rfl | rfl | rfl | rfl <;> simp at hij hjl hil <;> norm_num at e1 e2 <;> skip <;> linarith
  · intro B a b c d hab hbc hcd hdk e
    interval_cases d <;> interval_cases c <;> (try omega) <;> interval_cases b <;> (try omega) <;> interval_cases a <;> (try omega) <;> rcases hB B with rfl | rfl | rfl | rfl | rfl <;> norm_num at e ⊢ <;> intros <;> skip <;> constructor <;> intro hh <;> linarith


set_option maxHeartbeats 2000000 in
theorem rimE2a_cyc (tm hm tp hp sp kp sm km ap am d1 d3 : ℝ) (htm : 0 < tm) (htp : 0 < tp)
    (htp1 : tp < 1) (htm1 : tm < 1) (hsp : 0 < sp) (hsp1 : sp < 1) (hsm : 0 < sm) (hsm1 : sm < 1)
    (hap : 0 < ap) (ham : 0 < am)
    (hhp : hp = ap * tp) (hhm : hm = am * tm) (hkp : kp = (ap + am) * tp * (1 - sp))
    (hkm : km = sm * ((ap + am) * tp))
    (hr1 : am < (ap + am) * tp) (hr2 : sm * ((ap + am) * tp) * (1 - tm) < am * tm * (1 - sm))
    (hDe : am * d1 + d3 < 0) :
    ∀ i j : ZMod 6, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨tp, -1, hp⟩ ⟨d1, 0, d3⟩
        ((hex6 (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (hex6 (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ i))
        ((hex6 (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ j).sub
          (hex6 (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ i)) := by
  subst hhp hhm hkp hkm
  have a1 := sub_pos.2 htp1
  have a2 := sub_pos.2 hsp1
  have a3 := sub_pos.2 htm1
  have a5 := sub_pos.2 hsm1
  have a4 := sub_pos.2 hr1
  have a6 := sub_pos.2 hr2
  have a7 := neg_pos.2 hDe
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := zmod6_add_one
  intro i j h1 h2
  rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, b4, b5, hex6_0, hex6_1, hex6_2, hex6_3, hex6_4, hex6_5]
    first
    | (left; nlinarith [mul_pos htm hap, mul_pos htm ham, mul_pos htp hap, mul_pos htp ham, mul_pos hsp htp, mul_pos hsm htp, mul_pos a1 htm, mul_pos a2 htp, mul_pos a5 htp, mul_pos a4 htm, mul_pos a4 hsm, mul_pos a6 htp, mul_pos a6 hsp, mul_pos a3 htp, mul_pos a3 ham, mul_pos a3 hap])
    | (right; constructor
       · ring1
       · nlinarith [a7, mul_pos hsp a7, mul_pos hsm a7, mul_pos a2 a7, mul_pos htm a7, mul_pos htp a7, mul_pos a1 a7, mul_pos a3 a7, mul_pos a5 a7])

set_option maxHeartbeats 2000000 in
theorem rimE2a_rest (tm hm tp hp sp kp sm km ap am d1 d3 : ℝ)
    (htm : 0 < tm) (htp : 0 < tp)
    (htp1 : tp < 1) (htm1 : tm < 1) (hsp : 0 < sp) (hsp1 : sp < 1) (hsm : 0 < sm) (hsm1 : sm < 1)
    (hap : 0 < ap) (ham : 0 < am)
    (hhp : hp = ap * tp) (hhm : hm = am * tm) (hkp : kp = (ap + am) * tp * (1 - sp))
    (hkm : km = sm * ((ap + am) * tp))
    (hr1 : am < (ap + am) * tp) (hr2 : sm * ((ap + am) * tp) * (1 - tm) < am * tm * (1 - sm))
    (hDa : 0 < -(ap * tp) * d1 - (1 - tp) * d3) (hDe : am * d1 + d3 < 0) :
    ∀ i : ZMod 6,
      ST 1 ⟨tp, -1, hp⟩ ⟨d1, 0, d3⟩
        ((hex6 (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (hex6 (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ i))
        ((⟨0, 1, 0⟩ : C3).sub
          (hex6 (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ i)) := by
  subst hhp hhm hkp hkm
  have a1 := sub_pos.2 htp1
  have a2 := sub_pos.2 hsp1
  have a3 := sub_pos.2 htm1
  have a5 := sub_pos.2 hsm1
  have a4 := sub_pos.2 hr1
  have a6 := sub_pos.2 hr2
  have a7 := neg_pos.2 hDe
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := zmod6_add_one
  intro i
  rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, b4, b5, hex6_0, hex6_1, hex6_2, hex6_3, hex6_4, hex6_5]
    first
    | (left; nlinarith [mul_pos htm hap, mul_pos htm ham, mul_pos htp hap, mul_pos htp ham, mul_pos hsp htp, mul_pos hsm htp, mul_pos a1 htm, mul_pos a2 htp, mul_pos a5 htp, mul_pos a4 htm, mul_pos a4 hsm, mul_pos a6 htp, mul_pos a6 hsp, mul_pos a3 htp, mul_pos a3 ham, mul_pos a3 hap])
    | (right; constructor
       · ring1
       · nlinarith [mul_pos a1 hDa, mul_pos a2 hDa, mul_pos htp hDa, hDa, a7, mul_pos hsp a7, mul_pos hsm a7, mul_pos a2 a7, mul_pos htm a7, mul_pos htp a7, mul_pos a1 a7, mul_pos a3 a7, mul_pos a5 a7])

set_option maxHeartbeats 2000000 in
theorem rimE2b_cyc (tm hm tp hp sp kp sm km ap am d1 d3 : ℝ)
    (htm : 0 < tm) (htp : 0 < tp)
    (htp1 : tp < 1) (htm1 : tm < 1) (hsp : 0 < sp) (hsp1 : sp < 1) (hsm : 0 < sm) (hsm1 : sm < 1)
    (hap : 0 < ap) (ham : 0 < am)
    (hhp : hp = ap * tp) (hhm : hm = am * tm) (hkp : kp = (ap + am) * tp * (1 - sp))
    (hkm : km = sm * ((ap + am) * tp))
    (hr1 : am < (ap + am) * tp) (hr2 : sm * ((ap + am) * tp) * (1 - tm) < am * tm * (1 - sm))
    (hDa : -(ap * tp) * d1 - (1 - tp) * d3 < 0) (hDe : 0 < am * d1 + d3) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨tp, -1, hp⟩ ⟨d1, 0, d3⟩
        ((quint (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i))
        ((quint (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ j).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i)) := by
  subst hhp hhm hkp hkm
  have a1 := sub_pos.2 htp1
  have a2 := sub_pos.2 hsp1
  have a3 := sub_pos.2 htm1
  have a5 := sub_pos.2 hsm1
  have a4 := sub_pos.2 hr1
  have a6 := sub_pos.2 hr2
  have a7 : 0 < (ap * tp) * d1 + (1 - tp) * d3 := by linarith
  have a8 := hDe
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i j h1 h2
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith [mul_pos htm hap, mul_pos htm ham, mul_pos htp hap, mul_pos htp ham, mul_pos hsp htp, mul_pos hsm htp, mul_pos a1 htm, mul_pos a2 htp, mul_pos a5 htp, mul_pos a4 htm, mul_pos a4 hsm, mul_pos a6 htp, mul_pos a6 hsp, mul_pos a3 htp, mul_pos a3 ham, mul_pos a3 hap])
    | (right; constructor
       · ring1
       · nlinarith [mul_pos a1 a7, mul_pos a2 a7, mul_pos htp a7, a7, a8, mul_pos hsp a8, mul_pos hsm a8, mul_pos a2 a8, mul_pos htm a8, mul_pos htp a8, mul_pos a1 a8, mul_pos a3 a8, mul_pos a5 a8, mul_pos hap a8, mul_pos ham a8])

set_option maxHeartbeats 2000000 in
theorem rimE2b_rest (tm hm tp hp sp kp sm km ap am d1 d3 : ℝ)
    (htm : 0 < tm) (htp : 0 < tp)
    (htp1 : tp < 1) (htm1 : tm < 1) (hsp : 0 < sp) (hsp1 : sp < 1) (hsm : 0 < sm) (hsm1 : sm < 1)
    (hap : 0 < ap) (ham : 0 < am)
    (hhp : hp = ap * tp) (hhm : hm = am * tm) (hkp : kp = (ap + am) * tp * (1 - sp))
    (hkm : km = sm * ((ap + am) * tp))
    (hr1 : am < (ap + am) * tp) (hr2 : sm * ((ap + am) * tp) * (1 - tm) < am * tm * (1 - sm))
    (hDa : -(ap * tp) * d1 - (1 - tp) * d3 < 0) (hDe : 0 < am * d1 + d3) (w : C3)
    (hw : w = ⟨tp, 0, hp⟩ ∨ w = ⟨0, sm, -km⟩) :
    ∀ i : ZMod 5,
      ST 1 ⟨tp, -1, hp⟩ ⟨d1, 0, d3⟩
        ((quint (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i))
        (w.sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i)) := by
  subst hhp hhm hkp hkm
  have a1 := sub_pos.2 htp1
  have a2 := sub_pos.2 hsp1
  have a3 := sub_pos.2 htm1
  have a5 := sub_pos.2 hsm1
  have a4 := sub_pos.2 hr1
  have a6 := sub_pos.2 hr2
  have a7 : 0 < (ap * tp) * d1 + (1 - tp) * d3 := by linarith
  have a8 := hDe
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases hw with rfl | rfl <;>
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith [mul_pos htm hap, mul_pos htm ham, mul_pos htp hap, mul_pos htp ham, mul_pos hsp htp, mul_pos hsm htp, mul_pos a1 htm, mul_pos a2 htp, mul_pos a5 htp, mul_pos a4 htm, mul_pos a4 hsm, mul_pos a6 htp, mul_pos a6 hsp, mul_pos a3 htp, mul_pos a3 ham, mul_pos a3 hap])
    | (right; constructor
       · ring1
       · nlinarith [mul_pos a1 a7, mul_pos a2 a7, mul_pos htp a7, a7, a8, mul_pos hsp a8, mul_pos hsm a8, mul_pos a2 a8, mul_pos htm a8, mul_pos htp a8, mul_pos a1 a8, mul_pos a3 a8, mul_pos a5 a8, mul_pos hap a8, mul_pos ham a8])

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
theorem robust_cycE6 {b a1 a2 a3 a4 : ℝ} (hb : b < 0) (h1 : 0 < a1) (h2 : a1 < a2) (h4 : 0 < a4)
    (h5 : a4 < a3) :
    IsRobustUnimodal (k := 6) (fun i : ZMod 6 => ![0, b, a1, a2, a3, a4] i) := by
  have hB : ∀ B : ZMod 6, B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 ∨ B = 5 := by decide
  refine ⟨?_, ?_, ?_⟩
  · intro B a b c d hab hbc hcd hdk
    interval_cases d <;> interval_cases c <;> (try omega) <;> interval_cases b <;> (try omega) <;> interval_cases a <;> (try omega) <;> rcases hB B with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num <;> intros <;> skip <;> linarith
  · intro i j l hij hjl hil e1 e2
    rcases hB i with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hB j with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hB l with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hij hjl hil <;> norm_num at e1 e2 <;> skip <;> linarith
  · intro B a b c d hab hbc hcd hdk e
    interval_cases d <;> interval_cases c <;> (try omega) <;> interval_cases b <;> (try omega) <;> interval_cases a <;> (try omega) <;> rcases hB B with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num at e ⊢ <;> intros <;> skip <;> constructor <;> intro hh <;> linarith

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
theorem robust_cycE5 {a1 a2 b3 b4 : ℝ} (h1 : 0 < a1) (h2 : a1 < a2) (h3 : b3 < 0) (h4 : b4 < 0) :
    IsRobustUnimodal (k := 5) (fun i : ZMod 5 => ![0, a1, a2, b3, b4] i) := by
  have hB : ∀ B : ZMod 5, B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by decide
  refine ⟨?_, ?_, ?_⟩
  · intro B a b c d hab hbc hcd hdk
    interval_cases d <;> interval_cases c <;> (try omega) <;> interval_cases b <;> (try omega) <;> interval_cases a <;> (try omega) <;> rcases hB B with rfl | rfl | rfl | rfl | rfl <;> norm_num <;> intros <;> skip <;> linarith
  · intro i j l hij hjl hil e1 e2
    rcases hB i with rfl | rfl | rfl | rfl | rfl <;> rcases hB j with rfl | rfl | rfl | rfl | rfl <;> rcases hB l with rfl | rfl | rfl | rfl | rfl <;> simp at hij hjl hil <;> norm_num at e1 e2 <;> skip <;> linarith
  · intro B a b c d hab hbc hcd hdk e
    interval_cases d <;> interval_cases c <;> (try omega) <;> interval_cases b <;> (try omega) <;> interval_cases a <;> (try omega) <;> rcases hB B with rfl | rfl | rfl | rfl | rfl <;> norm_num at e ⊢ <;> intros <;> skip <;> constructor <;> intro hh <;> linarith

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
theorem robust_cycW1 {z0 z1 z2 z3 : ℝ} (h3 : 0 < z3) (h2 : z3 < z2) (h1 : z2 < z0) (h0 : z0 ≤ z1) :
    IsRobustUnimodal (k := 6) (fun i : ZMod 6 => ![z0, z1, z2, z3, 0, 0] i) := by
  have hB : ∀ B : ZMod 6, B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 ∨ B = 5 := by decide
  refine ⟨?_, ?_, ?_⟩
  · intro B a b c d hab hbc hcd hdk
    interval_cases d <;> interval_cases c <;> (try omega) <;> interval_cases b <;> (try omega) <;> interval_cases a <;> (try omega) <;> rcases hB B with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num <;> intros <;> skip <;> linarith
  · intro i j l hij hjl hil e1 e2
    rcases hB i with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hB j with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hB l with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hij hjl hil <;> norm_num at e1 e2 <;> skip <;> linarith
  · intro B a b c d hab hbc hcd hdk e
    interval_cases d <;> interval_cases c <;> (try omega) <;> interval_cases b <;> (try omega) <;> interval_cases a <;> (try omega) <;> rcases hB B with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num at e ⊢ <;> intros <;> skip <;> constructor <;> intro hh <;> linarith

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
theorem robust_cycW2 {z0 z2 z3 z4 : ℝ} (h3 : 0 < z3) (h4 : z4 < z3) (h2 : z3 < z2) (h1 : z2 < z0) :
    IsRobustUnimodal (k := 6) (fun i : ZMod 6 => ![z0, z0, z2, z3, z4, 0] i) := by
  have hB : ∀ B : ZMod 6, B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 ∨ B = 5 := by decide
  refine ⟨?_, ?_, ?_⟩
  · intro B a b c d hab hbc hcd hdk
    interval_cases d <;> interval_cases c <;> (try omega) <;> interval_cases b <;> (try omega) <;> interval_cases a <;> (try omega) <;> rcases hB B with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num <;> intros <;> skip <;> linarith
  · intro i j l hij hjl hil e1 e2
    rcases hB i with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hB j with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hB l with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hij hjl hil <;> norm_num at e1 e2 <;> skip <;> linarith
  · intro B a b c d hab hbc hcd hdk e
    interval_cases d <;> interval_cases c <;> (try omega) <;> interval_cases b <;> (try omega) <;> interval_cases a <;> (try omega) <;> rcases hB B with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num at e ⊢ <;> intros <;> skip <;> constructor <;> intro hh <;> linarith

set_option maxHeartbeats 4000000 in
theorem rimW1_cyc (tm hm tp hp sp kp sm km ap am d1 d3 : ℝ) (htm : 0 < tm) (htp : 0 < tp)
    (htp1 : tp < 1) (htm1 : tm < 1) (hsm : 0 < sm) (hsm1 : sm < 1)
    (hap : 0 < ap) (ham : 0 < am) (hs : sp + sm = 1)
    (hhp : hp = ap * tp) (hhm : hm = am * tm) (hkp : kp = (ap + am) * tp * (1 - sp))
    (hkm : km = sm * ((ap + am) * tp))
    (hr1 : am < (ap + am) * tp)
    (hd1 : d1 < 0) (hd3 : 0 < am * d1 + d3) :
    ∀ i j : ZMod 6, j ≠ i → j ≠ i + 1 →
      ST (-1) ⟨0, sm, -km⟩ ⟨d1, 0, d3⟩
        ((hex6 (⟨0, sm, -km⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ ⟨0, 0, 0⟩ (i + 1)).sub
          (hex6 (⟨0, sm, -km⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ ⟨0, 0, 0⟩ i))
        ((hex6 (⟨0, sm, -km⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ ⟨0, 0, 0⟩ j).sub
          (hex6 (⟨0, sm, -km⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ ⟨0, 0, 0⟩ i)) := by
  obtain rfl : sp = 1 - sm := by linarith
  subst hhp hhm hkp hkm
  have a1 := sub_pos.2 htp1
  have a3 := sub_pos.2 htm1
  have a5 := sub_pos.2 hsm1
  have a4 := sub_pos.2 hr1
  have a8 := neg_pos.2 hd1
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := zmod6_add_one
  intro i j h1 h2
  rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, b4, b5, hex6_0, hex6_1, hex6_2, hex6_3, hex6_4, hex6_5]
    first
    | (left; nlinarith [mul_pos (mul_pos hsm a3) (mul_pos hap htp), mul_pos (mul_pos hsm ham) (mul_pos htm a1), mul_pos htm hap, mul_pos htm ham, mul_pos htp hap, mul_pos htp ham, mul_pos hsm htp, mul_pos a1 htm, mul_pos a5 htp, mul_pos a4 htm, mul_pos a4 hsm, mul_pos a3 htp, mul_pos a3 ham, mul_pos a3 hap, mul_pos hsm a8, mul_pos hsm hd3, mul_pos htp hd3, mul_pos htm hd3])
    | (right; constructor
       · ring1
       · nlinarith [mul_pos hsm a8, mul_pos hsm hd3, mul_pos htp hd3, mul_pos htm hd3, mul_pos hsm htp, mul_pos htp a8, mul_pos htm a8, mul_pos a5 a8, mul_pos a5 hd3, mul_pos a1 hd3, mul_pos a3 hd3, mul_pos a1 a8, mul_pos a3 a8])

set_option maxHeartbeats 4000000 in
theorem rimW1_rest (tm hm tp hp sp kp sm km ap am d1 d3 : ℝ) (htm : 0 < tm) (htp : 0 < tp)
    (htp1 : tp < 1) (htm1 : tm < 1) (hsm : 0 < sm) (hsm1 : sm < 1)
    (hap : 0 < ap) (ham : 0 < am) (hs : sp + sm = 1)
    (hhp : hp = ap * tp) (hhm : hm = am * tm) (hkp : kp = (ap + am) * tp * (1 - sp))
    (hkm : km = sm * ((ap + am) * tp))
    (hr1 : am < (ap + am) * tp)
    (hd1 : d1 < 0) (hd3 : 0 < am * d1 + d3) :
    ∀ i : ZMod 6,
      ST (-1) ⟨0, sm, -km⟩ ⟨d1, 0, d3⟩
        ((hex6 (⟨0, sm, -km⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ ⟨0, 0, 0⟩ (i + 1)).sub
          (hex6 (⟨0, sm, -km⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ ⟨0, 0, 0⟩ i))
        ((⟨0, 1, 0⟩ : C3).sub
          (hex6 (⟨0, sm, -km⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ ⟨0, 0, 0⟩ i)) := by
  obtain rfl : sp = 1 - sm := by linarith
  subst hhp hhm hkp hkm
  have a1 := sub_pos.2 htp1
  have a3 := sub_pos.2 htm1
  have a5 := sub_pos.2 hsm1
  have a4 := sub_pos.2 hr1
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := zmod6_add_one
  have a8 := neg_pos.2 hd1
  intro i
  rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, b4, b5, hex6_0, hex6_1, hex6_2, hex6_3, hex6_4, hex6_5]
    first
    | (left; nlinarith [mul_pos (mul_pos hsm a3) (mul_pos hap htp), mul_pos (mul_pos hsm ham) (mul_pos htm a1), mul_pos htm hap, mul_pos htm ham, mul_pos htp hap, mul_pos htp ham, mul_pos hsm htp, mul_pos a1 htm, mul_pos a5 htp, mul_pos a4 htm, mul_pos a4 hsm, mul_pos a3 htp, mul_pos a3 ham, mul_pos a3 hap, mul_pos hsm a8, mul_pos hsm hd3, mul_pos htp hd3, mul_pos htm hd3])
    | (right; constructor
       · ring1
       · nlinarith [mul_pos hsm a8, mul_pos hsm hd3, mul_pos htp hd3, mul_pos htm hd3, mul_pos hsm htp, mul_pos htp a8, mul_pos htm a8, mul_pos a5 a8, mul_pos a5 hd3, mul_pos a1 hd3, mul_pos a3 hd3, mul_pos a1 a8, mul_pos a3 a8])

set_option maxHeartbeats 4000000 in
theorem rimW2_cyc (tm hm tp hp sp kp sm km ap am d1 d3 : ℝ) (htm : 0 < tm) (htp : 0 < tp)
    (htp1 : tp < 1) (htm1 : tm < 1) (hsm : 0 < sm) (hsm1 : sm < 1)
    (hap : 0 < ap) (ham : 0 < am) (hs : sp + sm = 1)
    (hhp : hp = ap * tp) (hhm : hm = am * tm) (hkp : kp = (ap + am) * tp * (1 - sp))
    (hkm : km = sm * ((ap + am) * tp))
    (hr1 : am < (ap + am) * tp)
    (hd1 : 0 < d1) (hd3 : 0 < am * d1 + d3) :
    ∀ i j : ZMod 6, j ≠ i → j ≠ i + 1 →
      ST (-1) ⟨0, sm, -km⟩ ⟨d1, 0, d3⟩
        ((hex6 (⟨0, 1, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (hex6 (⟨0, 1, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ i))
        ((hex6 (⟨0, 1, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ j).sub
          (hex6 (⟨0, 1, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ i)) := by
  obtain rfl : sp = 1 - sm := by linarith
  subst hhp hhm hkp hkm
  have a1 := sub_pos.2 htp1
  have a3 := sub_pos.2 htm1
  have a5 := sub_pos.2 hsm1
  have a4 := sub_pos.2 hr1
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := zmod6_add_one
  have a8 := hd1
  intro i j h1 h2
  rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, b4, b5, hex6_0, hex6_1, hex6_2, hex6_3, hex6_4, hex6_5]
    first
    | (left; nlinarith [mul_pos (mul_pos hsm a3) (mul_pos hap htp), mul_pos (mul_pos hsm ham) (mul_pos htm a1), mul_pos htm hap, mul_pos htm ham, mul_pos htp hap, mul_pos htp ham, mul_pos hsm htp, mul_pos a1 htm, mul_pos a5 htp, mul_pos a4 htm, mul_pos a4 hsm, mul_pos a3 htp, mul_pos a3 ham, mul_pos a3 hap, mul_pos hsm a8, mul_pos hsm hd3, mul_pos htp hd3, mul_pos htm hd3])
    | (right; constructor
       · ring1
       · nlinarith [mul_pos hsm a8, mul_pos hsm hd3, mul_pos htp hd3, mul_pos htm hd3, mul_pos hsm htp, mul_pos htp a8, mul_pos htm a8, mul_pos a5 a8, mul_pos a5 hd3, mul_pos a1 hd3, mul_pos a3 hd3, mul_pos a1 a8, mul_pos a3 a8])

set_option maxHeartbeats 4000000 in
theorem rimW2_rest (tm hm tp hp sp kp sm km ap am d1 d3 : ℝ) (htm : 0 < tm) (htp : 0 < tp)
    (htp1 : tp < 1) (htm1 : tm < 1) (hsm : 0 < sm) (hsm1 : sm < 1)
    (hap : 0 < ap) (ham : 0 < am) (hs : sp + sm = 1)
    (hhp : hp = ap * tp) (hhm : hm = am * tm) (hkp : kp = (ap + am) * tp * (1 - sp))
    (hkm : km = sm * ((ap + am) * tp))
    (hr1 : am < (ap + am) * tp)
    (hd1 : 0 < d1) (hd3 : 0 < am * d1 + d3) :
    ∀ i : ZMod 6,
      ST (-1) ⟨0, sm, -km⟩ ⟨d1, 0, d3⟩
        ((hex6 (⟨0, 1, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (hex6 (⟨0, 1, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ i))
        ((⟨0, 0, 0⟩ : C3).sub
          (hex6 (⟨0, 1, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ i)) := by
  obtain rfl : sp = 1 - sm := by linarith
  subst hhp hhm hkp hkm
  have a1 := sub_pos.2 htp1
  have a3 := sub_pos.2 htm1
  have a5 := sub_pos.2 hsm1
  have a4 := sub_pos.2 hr1
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := zmod6_add_one
  have a8 := hd1
  intro i
  rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, b4, b5, hex6_0, hex6_1, hex6_2, hex6_3, hex6_4, hex6_5]
    first
    | (left; nlinarith [mul_pos (mul_pos hsm a3) (mul_pos hap htp), mul_pos (mul_pos hsm ham) (mul_pos htm a1), mul_pos htm hap, mul_pos htm ham, mul_pos htp hap, mul_pos htp ham, mul_pos hsm htp, mul_pos a1 htm, mul_pos a5 htp, mul_pos a4 htm, mul_pos a4 hsm, mul_pos a3 htp, mul_pos a3 ham, mul_pos a3 hap, mul_pos hsm a8, mul_pos hsm hd3, mul_pos htp hd3, mul_pos htm hd3])
    | (right; constructor
       · ring1
       · nlinarith [mul_pos hsm a8, mul_pos hsm hd3, mul_pos htp hd3, mul_pos htm hd3, mul_pos hsm htp, mul_pos htp a8, mul_pos htm a8, mul_pos a5 a8, mul_pos a5 hd3, mul_pos a1 hd3, mul_pos a3 hd3, mul_pos a1 a8, mul_pos a3 a8])

/-! ### Group E-C support: pure-real lemmas for Theorem C (robust patterns, rim `(v,m2-,m1-,xa,m1+,m2+)`
at the view `u1`, tilt `(0,0,-1)`; `hp = a tp`, `hm = a (1-tm)`, `kp = a sp` are the corner relations) -/

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
theorem robust_cycC5 {a1 a2 a3 a4 : ℝ} (h2 : a1 < a2) (h4 : 0 < a4) (h5 : a4 < a3) :
    IsRobustUnimodal (k := 5) (fun i : ZMod 5 => ![0, a1, a2, a3, a4] i) := by
  have hB : ∀ B : ZMod 5, B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by decide
  refine ⟨?_, ?_, ?_⟩
  · intro B a b c d hab hbc hcd hdk
    interval_cases d <;> interval_cases c <;> (try omega) <;> interval_cases b <;> (try omega) <;> interval_cases a <;> (try omega) <;> rcases hB B with rfl | rfl | rfl | rfl | rfl <;> norm_num <;> intros <;> skip <;> linarith
  · intro i j l hij hjl hil e1 e2
    rcases hB i with rfl | rfl | rfl | rfl | rfl <;> rcases hB j with rfl | rfl | rfl | rfl | rfl <;> rcases hB l with rfl | rfl | rfl | rfl | rfl <;> simp at hij hjl hil <;> norm_num at e1 e2 <;> skip <;> linarith
  · intro B a b c d hab hbc hcd hdk e
    interval_cases d <;> interval_cases c <;> (try omega) <;> interval_cases b <;> (try omega) <;> interval_cases a <;> (try omega) <;> rcases hB B with rfl | rfl | rfl | rfl | rfl <;> norm_num at e ⊢ <;> intros <;> skip <;> constructor <;> intro hh <;> linarith

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
theorem robust_cycC6 {b a1 a2 a3 a4 : ℝ} (hb : b < 0) (h2 : a1 < a2) (h4 : 0 < a4)
    (h5 : a4 < a3) :
    IsRobustUnimodal (k := 6) (fun i : ZMod 6 => ![0, b, a1, a2, a3, a4] i) := by
  have hB : ∀ B : ZMod 6, B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 ∨ B = 5 := by decide
  refine ⟨?_, ?_, ?_⟩
  · intro B a b c d hab hbc hcd hdk
    interval_cases d <;> interval_cases c <;> (try omega) <;> interval_cases b <;> (try omega) <;> interval_cases a <;> (try omega) <;> rcases hB B with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num <;> intros <;> skip <;> linarith
  · intro i j l hij hjl hil e1 e2
    rcases hB i with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hB j with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hB l with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hij hjl hil <;> norm_num at e1 e2 <;> skip <;> linarith
  · intro B a b c d hab hbc hcd hdk e
    interval_cases d <;> interval_cases c <;> (try omega) <;> interval_cases b <;> (try omega) <;> interval_cases a <;> (try omega) <;> rcases hB B with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num at e ⊢ <;> intros <;> skip <;> constructor <;> intro hh <;> linarith

theorem Cq_pos (a tm tp sp sm km : ℝ) (ha : 0 < a) (htm : 0 < tm) (htp : 0 < tp) (hsp : 0 < sp)
    (hsm : 0 < sm) (hsm1 : sm < 1) (hc : sm * a * tp ≤ tm * km) (hr2 : km < a * (1 - sm)) :
    0 < a * (sp * tm + sp * tp - tp * sp * sm - sm * tp) + km * (tm - tp * sp) := by
  have hf : sm * tp < tm * (1 - sm) := by
    have h1 : tm * km < tm * (a * (1 - sm)) := mul_lt_mul_of_pos_left hr2 htm
    have : a * (sm * tp) < a * (tm * (1 - sm)) := by nlinarith
    exact lt_of_mul_lt_mul_left this ha.le
  have a5 := sub_pos.2 hsm1
  rcases le_total (tp * sp) tm with h | h
  · have : 0 < tm * (a * (sp * tm + sp * tp - tp * sp * sm - sm * tp) + km * (tm - tp * sp)) := by
      nlinarith [mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 hc), mul_pos ha htm, mul_pos (mul_pos ha hsp) (mul_pos htm htm), mul_pos (mul_pos ha hsp) (mul_pos htm htp), mul_pos (mul_pos ha hsp) (mul_pos htp htp), mul_pos (mul_pos ha hsp) (sub_pos.2 hf), mul_pos (mul_pos ha hsp) (mul_pos htm (mul_pos htp a5))]
    exact pos_of_mul_pos_right this htm.le
  · have : 0 < a * (sp * tm + sp * tp - tp * sp * sm - sm * tp) + km * (tm - tp * sp) := by
      nlinarith [mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 hr2.le), mul_pos ha hsp, mul_pos (mul_pos ha hsp) htm, mul_pos ha (sub_pos.2 hf), mul_pos (mul_pos ha htm) hsp]
    exact this

set_option maxHeartbeats 4000000 in
theorem rimC6_cyc (tm hm tp hp sp kp sm km a : ℝ) (htm : 0 < tm) (htp : 0 < tp)
    (htp1 : tp < 1) (htm1 : tm < 1) (hsp : 0 < sp) (hsp1 : sp < 1) (hsm : 0 < sm) (hsm1 : sm < 1)
    (ha : 0 < a) (hkm : 0 < km)
    (hhp : hp = a * tp) (hhm : hm = a * (1 - tm)) (hkp : kp = a * sp)
    (hroof : sp < tp) (hr2 : km < a * (1 - sm))
    (hc : sm * a * tp ≤ tm * km) :
    ∀ i j : ZMod 6, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨tp, -1, hp⟩ ⟨0, 0, -1⟩
        ((hex6 (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (hex6 (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ i))
        ((hex6 (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ j).sub
          (hex6 (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ i)) := by
  subst hhp hhm hkp
  have a1 := sub_pos.2 htp1
  have a2 := sub_pos.2 hsp1
  have a3 := sub_pos.2 htm1
  have a5 := sub_pos.2 hsm1
  have a4 := sub_pos.2 hroof
  have a6 := sub_pos.2 hr2
  have hQ := Cq_pos a tm tp sp sm km ha htm htp hsp hsm hsm1 hc hr2
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := zmod6_add_one
  intro i j h1 h2
  rcases hc.lt_or_eq with hc | hc <;>
  rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, b4, b5, hex6_0, hex6_1, hex6_2, hex6_3, hex6_4, hex6_5]
    first
    | (left; linarith [hQ])
    | (left; nlinarith [mul_pos ha htp, mul_pos ha hsp, mul_pos htp hsp, mul_pos a6 htp, mul_pos a6 hsp, mul_pos (mul_pos ha htp) a5, mul_pos hkm htp, mul_pos hkm hsp, mul_pos hkm a1, mul_pos (mul_pos ha htp) hsm, mul_pos (mul_pos ha htp) hsp, mul_pos (mul_pos ha hsp) hsm, mul_pos (mul_pos ha hsp) a3, mul_pos (mul_pos ha a3) hsm, mul_pos (mul_pos ha a3) htp, mul_pos (mul_pos ha a3) a1, mul_pos (mul_pos ha a3) a5, mul_pos (mul_pos ha htm) a1, mul_pos (mul_pos ha htm) a5, mul_pos (mul_pos ha htm) hsm, mul_pos (mul_pos ha a4) htm, mul_pos (mul_pos ha a4) hsm, mul_pos ha a4, mul_pos hkm htm, mul_pos hkm hsm, mul_pos (mul_pos hkm htm) a1, mul_pos hkm a5, mul_pos (mul_pos hkm htp) a5, mul_pos (mul_pos hkm hsm) htp])
    | (right; constructor
       · nlinarith [hc]
       · nlinarith [mul_pos ha htp, mul_pos ha hsp, mul_pos ha hsm, mul_pos ha htm, mul_pos ha a1, mul_pos ha a2, mul_pos ha a3, mul_pos ha a5, mul_pos ha hkm])

set_option maxHeartbeats 4000000 in
theorem rimC6_rest (tm hm tp hp sp kp sm km a : ℝ) (htm : 0 < tm) (htp : 0 < tp)
    (htp1 : tp < 1) (htm1 : tm < 1) (hsp : 0 < sp) (hsp1 : sp < 1) (hsm : 0 < sm) (hsm1 : sm < 1)
    (ha : 0 < a) (hkm : 0 < km)
    (hhp : hp = a * tp) (hhm : hm = a * (1 - tm)) (hkp : kp = a * sp)
    (hroof : sp < tp) (hr2 : km < a * (1 - sm))
    (hc : sm * a * tp ≤ tm * km) :
    ∀ i : ZMod 6,
      ST 1 ⟨tp, -1, hp⟩ ⟨0, 0, -1⟩
        ((hex6 (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (hex6 (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ i))
        ((⟨0, 1, 0⟩ : C3).sub
          (hex6 (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ i)) := by
  subst hhp hhm hkp
  have a1 := sub_pos.2 htp1
  have a2 := sub_pos.2 hsp1
  have a3 := sub_pos.2 htm1
  have a5 := sub_pos.2 hsm1
  have a4 := sub_pos.2 hroof
  have a6 := sub_pos.2 hr2
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := zmod6_add_one
  intro i
  rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, b4, b5, hex6_0, hex6_1, hex6_2, hex6_3, hex6_4, hex6_5]
    first
    | (left; nlinarith [mul_pos ha htp, mul_pos ha hsp, mul_pos htp hsp, mul_pos a6 htp, mul_pos a6 hsp, mul_pos (mul_pos ha htp) a5, mul_pos hkm htp, mul_pos hkm hsp, mul_pos hkm a1, mul_pos (mul_pos ha htp) hsm, mul_pos (mul_pos ha htp) hsp, mul_pos (mul_pos ha hsp) hsm, mul_pos (mul_pos ha hsp) a3, mul_pos (mul_pos ha a3) hsm, mul_pos (mul_pos ha a3) htp, mul_pos (mul_pos ha a3) a1, mul_pos (mul_pos ha a3) a5, mul_pos (mul_pos ha htm) a1, mul_pos (mul_pos ha htm) a5, mul_pos (mul_pos ha htm) hsm, mul_pos (mul_pos ha a4) htm, mul_pos (mul_pos ha a4) hsm, mul_pos ha a4, mul_pos hkm htm, mul_pos hkm hsm, mul_pos (mul_pos hkm htm) a1, mul_pos hkm a5, mul_pos (mul_pos hkm htp) a5, mul_pos (mul_pos hkm hsm) htp, mul_pos (mul_pos ha htp) a2, mul_pos (mul_pos ha hsp) a2, mul_pos (mul_pos ha hsp) htp])
    | (right; constructor
       · ring1
       · nlinarith [mul_pos a1 a2, mul_pos htp a2, a1, a2, htp, mul_pos htp a1, mul_pos ha a1, mul_pos ha a2, mul_pos ha htp, mul_pos ha hsp, mul_pos hsp a1, mul_pos hsp a2])

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
theorem robust_cycCT {R Z2 T Z1 : ℝ} (hZ1 : Z1 < T) (hR : T < R) (hZ2 : T < Z2) :
    IsRobustUnimodal (k := 5) (fun i : ZMod 5 => ![R, Z2, T, Z1, T] i) := by
  have hB : ∀ B : ZMod 5, B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by decide
  refine ⟨?_, ?_, ?_⟩
  · intro B a b c d hab hbc hcd hdk
    interval_cases d <;> interval_cases c <;> (try omega) <;> interval_cases b <;> (try omega) <;> interval_cases a <;> (try omega) <;> rcases hB B with rfl | rfl | rfl | rfl | rfl <;> norm_num <;> intros <;> skip <;> linarith
  · intro i j l hij hjl hil e1 e2
    rcases hB i with rfl | rfl | rfl | rfl | rfl <;> rcases hB j with rfl | rfl | rfl | rfl | rfl <;> rcases hB l with rfl | rfl | rfl | rfl | rfl <;> simp at hij hjl hil <;> norm_num at e1 e2 <;> skip <;> linarith
  · intro B a b c d hab hbc hcd hdk e
    interval_cases d <;> interval_cases c <;> (try omega) <;> interval_cases b <;> (try omega) <;> interval_cases a <;> (try omega) <;> rcases hB B with rfl | rfl | rfl | rfl | rfl <;> norm_num at e ⊢ <;> intros <;> skip <;> constructor <;> intro hh <;> linarith

set_option maxHeartbeats 1000000 in
theorem rimBe_rest (S : Shape18) (P q : ℝ) (hP : P < 0) (hV1 : S.sm * S.hm * q + S.tm * S.km * P < 0)
    (hQ : 0 < q + P) (hE : S.hm * (1 - S.tp) = S.tm * S.hp)
    (hV : S.tm * S.kp < S.hm * (1 - S.sp)) (w : C3)
    (hw : w = ⟨0, S.sp, S.kp⟩ ∨ w = ⟨1, 0, 0⟩ ∨ w = ⟨S.tm, 0, -S.hm⟩) :
    ∀ i : ZMod 4,
      ST 1 ⟨S.tm, 0, -S.hm⟩ ⟨q, P, 0⟩
        ((quad (⟨0, 0, 0⟩ : C3) ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨S.tp, 0, S.hp⟩ (i + 1)).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨S.tp, 0, S.hp⟩ i))
        (w.sub (quad (⟨0, 0, 0⟩ : C3) ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨S.tp, 0, S.hp⟩ i)) := by
  have a1 := S.hp_pos
  have a2 := S.hm_pos
  have a3 := S.tm_pos
  have a4 := S.km_pos
  have a5 := S.sm_pos
  have a6 := S.tp_pos
  have a7 := mul_pos S.tm_pos S.km_pos
  have a9 := mul_pos S.tm_pos S.hp_pos
  have a10 := mul_pos S.hm_pos S.tp_pos
  have a11 := sub_pos.2 S.sm_lt
  have a12 := sub_pos.2 S.sp_lt
  have a13 := S.kp_pos
  have a14 := sub_pos.2 hV
  have a15 := S.sp_pos
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases hw with rfl | rfl | rfl <;>
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith [mul_pos a11 a7, mul_pos a11 a9, mul_pos a11 a10, mul_pos a5 a9, mul_pos a5 a7, mul_pos a3 a13, mul_pos a5 (mul_pos a3 a13), mul_pos a7 a15, mul_pos a14 a3, mul_pos a14 a15, mul_pos a14 a6, hE])
    | (right; refine ⟨by first | ring1 | linear_combination hE | linear_combination (-1 : ℝ) * hE, by nlinarith [mul_pos a1 (neg_pos.2 hP), mul_pos a9 (neg_pos.2 hP), mul_pos a2 (neg_pos.2 hP), mul_pos a10 (neg_pos.2 hP), mul_pos a7 (neg_pos.2 hP), mul_pos a1 hQ, mul_pos a2 hQ, mul_pos a9 hQ, mul_pos a10 hQ, mul_pos a6 hQ, mul_pos a3 hQ]⟩)

namespace Shape18
variable (S : Shape18)

/-- The upper roof `d+ < b+` cleared: `kp (1 - tp) < hp (1 - sp)`. -/
theorem roof_p_poly : S.kp * (1 - S.tp) < S.hp * (1 - S.sp) := by
  have h1 := S.dp_mul
  have h2 := S.bp_mul
  have h3 := S.dp_lt_bp
  have a : 0 < 1 - S.tp := by linarith [S.tp_lt]
  have b : 0 < 1 - S.sp := by linarith [S.sp_lt]
  have := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right h3 a) b
  nlinarith

/-- The lower roof `d- < b-` cleared: `km (1 - tm) < hm (1 - sm)`. -/
theorem roof_m_poly : S.km * (1 - S.tm) < S.hm * (1 - S.sm) := by
  have h1 := S.dm_mul
  have h2 := S.bm_mul
  have h3 := S.dm_lt_bm
  have a : 0 < 1 - S.tm := by linarith [S.tm_lt]
  have b : 0 < 1 - S.sm := by linarith [S.sm_lt]
  have := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right h3 a) b
  nlinarith

/-- `c- < A1 tp` cleared: `tm km < sm (tm hp + hm tp)`. -/
theorem hc_of_lt (h : S.cm < S.A1 * S.tp) : S.tm * S.km < S.sm * (S.tm * S.hp + S.hm * S.tp) := by
  have h1 := S.cm_mul
  have h2 := S.H_eq
  have := mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right h S.sm_pos) S.tm_pos
  have h3 : S.sm * (S.tm * S.hp + S.hm * S.tp) = S.tm * (S.A1 * S.tp * S.sm) := by
    linear_combination S.sm * h2
  have h4 : S.tm * S.km = S.tm * (S.cm * S.sm) := by rw [h1]
  linarith

end Shape18

/-- The tilt of sector `Q_H`: `D1a = D1b' = 1`. -/
theorem exists_tiltH (tp hp sp kp : ℝ) (htp1 : tp < 1) (hsp1 : sp < 1)
    (hroof : kp * (1 - tp) < hp * (1 - sp)) :
    ∃ d1 d3 : ℝ, 0 < -hp * d1 - (1 - tp) * d3 ∧
      0 < -((kp - hp * (1 - sp)) * d1 + tp * (1 - sp) * d3) := by
  have hdet : 0 < hp * (1 - sp) - (1 - tp) * kp := by nlinarith
  have hne := hdet.ne'
  refine ⟨((1 - tp) - tp * (1 - sp)) / (hp * (1 - sp) - (1 - tp) * kp),
    ((kp - hp * (1 - sp)) - hp) / (hp * (1 - sp) - (1 - tp) * kp), ?_, ?_⟩
  · have : -hp * (((1 - tp) - tp * (1 - sp)) / (hp * (1 - sp) - (1 - tp) * kp)) -
        (1 - tp) * (((kp - hp * (1 - sp)) - hp) / (hp * (1 - sp) - (1 - tp) * kp)) = 1 := by
      rw [show -hp * (((1 - tp) - tp * (1 - sp)) / (hp * (1 - sp) - (1 - tp) * kp)) -
        (1 - tp) * (((kp - hp * (1 - sp)) - hp) / (hp * (1 - sp) - (1 - tp) * kp)) = (-hp * ((1 - tp) - tp * (1 - sp)) - (1 - tp) * ((kp - hp * (1 - sp)) - hp)) / (hp * (1 - sp) - (1 - tp) * kp) by ring,
        show -hp * ((1 - tp) - tp * (1 - sp)) - (1 - tp) * ((kp - hp * (1 - sp)) - hp) = (hp * (1 - sp) - (1 - tp) * kp) by ring, div_self hne]
    rw [this]; exact one_pos
  · have : -((kp - hp * (1 - sp)) * (((1 - tp) - tp * (1 - sp)) / (hp * (1 - sp) - (1 - tp) * kp)) +
        tp * (1 - sp) * (((kp - hp * (1 - sp)) - hp) / (hp * (1 - sp) - (1 - tp) * kp))) = 1 := by
      rw [show -((kp - hp * (1 - sp)) * (((1 - tp) - tp * (1 - sp)) / (hp * (1 - sp) - (1 - tp) * kp)) +
        tp * (1 - sp) * (((kp - hp * (1 - sp)) - hp) / (hp * (1 - sp) - (1 - tp) * kp))) = (-((kp - hp * (1 - sp)) * ((1 - tp) - tp * (1 - sp)) + tp * (1 - sp) * ((kp - hp * (1 - sp)) - hp))) / (hp * (1 - sp) - (1 - tp) * kp) by ring,
        show -((kp - hp * (1 - sp)) * ((1 - tp) - tp * (1 - sp)) + tp * (1 - sp) * ((kp - hp * (1 - sp)) - hp)) = (hp * (1 - sp) - (1 - tp) * kp) by ring, div_self hne]
    rw [this]; exact one_pos


/-! ### Group E-F: Theorem F (view `u' = (-(β+D), D, b+ β)`, normalised by `1/D`; PROOFS 37.4) -/

/-- The F view (normalised): screen `(x + (1+ρ) y, z - ρ b y)`. -/
def uF (ρ b : ℝ) : C3 := ⟨-(1 + ρ), 1, ρ * b⟩
def scF (ρ b : ℝ) (p : C3) : ℝ × ℝ := (p.x + (1 + ρ) * p.y, p.z - ρ * b * p.y)
def crF (p q : ℝ × ℝ) : ℝ := p.1 * q.2 - p.2 * q.1

theorem Dc_uF (ρ b : ℝ) (a c : C3) : Dc a c (uF ρ b) = - crF (scF ρ b a) (scF ρ b c) := by
  simp only [Dc, uF, scF, crF]; ring

theorem rimA_cyc (tp tm hm sp kp sm km ρ b : ℝ) (d : C3) (htp : 0 < tp) (htp1 : tp < 1) (htm : 0 < tm)
    (htm1 : tm < 1) (hb : 0 < b) (hρ : 0 < ρ) (hhm : 0 < hm) (hbm : b * tm ≤ hm) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      ST (-1) (uF ρ b) d
        (((quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨0, 1, 0⟩ ⟨tp, 0, b * (1 - tp)⟩) (i + 1)).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨0, 1, 0⟩ ⟨tp, 0, b * (1 - tp)⟩ i))
        (((quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨0, 1, 0⟩ ⟨tp, 0, b * (1 - tp)⟩) j).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨0, 1, 0⟩ ⟨tp, 0, b * (1 - tp)⟩ i)) := by
  have a1 := sub_pos.2 htp1
  have a2 := sub_pos.2 htm1
  have f1 : 0 < hm * (1 + ρ) - ρ * b * tm := by
    nlinarith [mul_nonneg (sub_nonneg.2 hbm) hρ.le, mul_pos hb htm]
  have f2 : 0 < tm * (b * (1 - tp)) + hm * tp := by positivity
  have f3 : 0 < (1 + ρ - tp) * (hm + b * (1 - tm)) := by
    apply mul_pos (by linarith) (by nlinarith)
  have f4 : 0 < ρ * b * tp + (1 + ρ) * (b * (1 - tp)) := by positivity
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i j h1 h2
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [CaseC09.ST, Dc_uF, crF, scF, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    left
    nlinarith [f1, f2, f3, f4]

theorem rimA_restW (tp tm hm sp kp ρ b : ℝ) (d : C3) (htp : 0 < tp) (htp1 : tp < 1) (htm : 0 < tm)
    (htm1 : tm < 1) (hb : 0 < b) (hρ : 0 < ρ) (hhm : 0 < hm) (hbm : b * tm ≤ hm)
    (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (hroof : kp < b * (1 - sp))
    (HW : 0 < b * (1 - tp) * sp * (1 + ρ) - tp * kp + tp * sp * (ρ * b)) :
    ∀ i : ZMod 4,
      ST (-1) (uF ρ b) d
        (((quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨0, 1, 0⟩ ⟨tp, 0, b * (1 - tp)⟩) (i + 1)).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨0, 1, 0⟩ ⟨tp, 0, b * (1 - tp)⟩ i))
        ((⟨0, sp, kp⟩ : C3).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨0, 1, 0⟩ ⟨tp, 0, b * (1 - tp)⟩ i)) := by
  have a1 := sub_pos.2 htp1
  have a2 := sub_pos.2 htm1
  have a3 := sub_pos.2 hsp1
  have f1 : 0 < hm * (1 + ρ) - ρ * b * tm := by
    nlinarith [mul_nonneg (sub_nonneg.2 hbm) hρ.le, mul_pos hb htm]
  have g1 : 0 < sp * (hm * (1 + ρ) - ρ * b * tm) + tm * kp := by positivity
  have g2 : 0 < (1 + ρ - tm) * kp + (1 - sp) * (hm * (1 + ρ) - ρ * b * tm) := by
    have : 0 < 1 + ρ - tm := by linarith
    positivity
  have g3 : 0 < (1 + ρ - tp) * (b * (1 - sp) - kp) := by
    apply mul_pos (by linarith) (by linarith)
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc_uF, crF, scF, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    left
    nlinarith [g1, g2, g3, HW]

theorem rimA_restN (tp tm hm sm km ρ b : ℝ) (d : C3) (htp : 0 < tp) (htp1 : tp < 1) (htm : 0 < tm)
    (htm1 : tm < 1) (hb : 0 < b) (hρ : 0 < ρ) (hhm : 0 < hm) (hbm : b * tm ≤ hm)
    (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km)
    (HN1 : 0 < -(tm * km) - tm * sm * (ρ * b) + hm * sm * (1 + ρ))
    (HN2 : 0 < (1 + ρ - tm) * (-km - sm * (ρ * b) + hm) - (-(ρ * b) + hm) * (sm * (1 + ρ) - tm)) :
    ∀ i : ZMod 4,
      ST (-1) (uF ρ b) d
        (((quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨0, 1, 0⟩ ⟨tp, 0, b * (1 - tp)⟩) (i + 1)).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨0, 1, 0⟩ ⟨tp, 0, b * (1 - tp)⟩ i))
        ((⟨0, sm, -km⟩ : C3).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨0, 1, 0⟩ ⟨tp, 0, b * (1 - tp)⟩ i)) := by
  have a1 := sub_pos.2 htp1
  have a3 := sub_pos.2 hsm1
  have g3 : 0 < (1 + ρ - tp) * (km + b * (1 - sm)) := by
    apply mul_pos (by linarith) (by positivity)
  have g4 : 0 < tp * km + tp * sm * (ρ * b) + b * (1 - tp) * sm * (1 + ρ) := by positivity
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc_uF, crF, scF, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    left
    nlinarith [g3, g4, HN1, HN2]

theorem rimA_restA (tp tm hm ρ b : ℝ) (htp : 0 < tp) (htp1 : tp < 1) (htm : 0 < tm)
    (htm1 : tm < 1) (hb : 0 < b) (hρ : 0 < ρ) (hhm : 0 < hm) :
    ∀ i : ZMod 4,
      ST (-1) (uF ρ b) ⟨0, 0, -1⟩
        (((quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨0, 1, 0⟩ ⟨tp, 0, b * (1 - tp)⟩) (i + 1)).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨0, 1, 0⟩ ⟨tp, 0, b * (1 - tp)⟩ i))
        ((⟨1, 0, 0⟩ : C3).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨0, 1, 0⟩ ⟨tp, 0, b * (1 - tp)⟩ i)) := by
  have a1 := sub_pos.2 htp1
  have a2 := sub_pos.2 htm1
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, Dc_uF, crF, scF, C3.sub, uF, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith [mul_pos hρ hhm, mul_pos hρ (mul_pos hb a2), mul_pos hb a1, hhm])
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem robust_smul_pos {k : ℕ} {z : ZMod k → ℝ} (hz : IsRobustUnimodal z) {c : ℝ} (hc : 0 < c) :
    IsRobustUnimodal (fun i => c * z i) := by
  have key : ∀ a b : ℝ, c * a < c * b ↔ a < b :=
    fun a b => ⟨fun h => lt_of_mul_lt_mul_left h hc.le, fun h => mul_lt_mul_of_pos_left h hc⟩
  exact
  { noPeaks := fun B a' b c' d hab hbc hcd hdk h => hz.noPeaks B a' b c' d hab hbc hcd hdk (by
      simp only [key] at h; exact h)
    noTriple := fun i j l hij hjl hil e1 e2 => hz.noTriple i j l hij hjl hil
      (mul_left_cancel₀ hc.ne' e1) (mul_left_cancel₀ hc.ne' e2)
    noLevelRun := fun B a' b c' d hab hbc hcd hdk e => by
      have := hz.noLevelRun B a' b c' d hab hbc hcd hdk (mul_left_cancel₀ hc.ne' e)
      simp only [key]; exact this }



/-! ### Group E-F2: rims B, C, D and the lexicographic tilt `d = (-1,-1,-λ)` -/

def dF (lam : ℝ) : C3 := ⟨-1, -1, -lam⟩
/-- Screen orientation of the triple `P Q S` (counterclockwise > 0). -/
def Ot (ρ b : ℝ) (P Q S : C3) : ℝ := crF (scF ρ b (Q.sub P)) (scF ρ b (S.sub P))
/-- The tilt functional of the triple. -/
def Tt (lam : ℝ) (P Q S : C3) : ℝ := - Dc (Q.sub P) (S.sub P) (dF lam)
/-- Lexicographic positivity of the triple. -/
def Lx (ρ b lam : ℝ) (P Q S : C3) : Prop := 0 ≤ Ot ρ b P Q S ∧ (Ot ρ b P Q S = 0 → 0 < Tt lam P Q S)

theorem ST_of_Lx {ρ b lam : ℝ} {P Q S : C3} (h : Lx ρ b lam P Q S) :
    CaseC09.ST (-1) (uF ρ b) (dF lam) (Q.sub P) (S.sub P) := by
  have e1 : (-1 : ℝ) * Dc (Q.sub P) (S.sub P) (uF ρ b) = Ot ρ b P Q S := by
    rw [Dc_uF]; simp only [Ot]; ring
  have e2 : (-1 : ℝ) * Dc (Q.sub P) (S.sub P) (dF lam) = Tt lam P Q S := by
    simp only [Tt]; ring
  unfold CaseC09.ST
  rw [e1, e2]
  have e3 : Dc (Q.sub P) (S.sub P) (uF ρ b) = - Ot ρ b P Q S := by
    rw [Dc_uF]; simp only [Ot]
  rw [e3]
  rcases h.1.lt_or_eq with h1 | h1
  · exact Or.inl h1
  · exact Or.inr ⟨by rw [← h1]; simp, h.2 h1.symm⟩

theorem Lx_rot {ρ b lam : ℝ} {P Q S : C3} (h : Lx ρ b lam P Q S) : Lx ρ b lam Q S P := by
  have e1 : Ot ρ b Q S P = Ot ρ b P Q S := by
    simp only [Ot, crF, scF, C3.sub]; ring
  have e2 : Tt lam Q S P = Tt lam P Q S := by
    simp only [Tt, Dc, dF, C3.sub]; ring
  unfold Lx; rw [e1, e2]; exact h

theorem Lx_of_pos {ρ b lam : ℝ} {P Q S : C3} (h : 0 < Ot ρ b P Q S) : Lx ρ b lam P Q S :=
  ⟨h.le, fun e => absurd e h.ne'⟩

theorem Ot_swap (ρ b : ℝ) (P Q S : C3) : Ot ρ b P S Q = - Ot ρ b P Q S := by
  simp only [Ot, crF, scF, C3.sub]; ring

def pV : C3 := ⟨0, 0, 0⟩
def pM (tm hm : ℝ) : C3 := ⟨tm, 0, -hm⟩
def pB : C3 := ⟨0, 1, 0⟩
def pU (tp b : ℝ) : C3 := ⟨tp, 0, b * (1 - tp)⟩
def pW (sp kp : ℝ) : C3 := ⟨0, sp, kp⟩
def pN (sm km : ℝ) : C3 := ⟨0, sm, -km⟩
def pA : C3 := ⟨1, 0, 0⟩

structure FPar (tp tm hm sp kp sm km ρ b lam : ℝ) : Prop where
  tp_pos : 0 < tp
  tp_lt : tp < 1
  tm_pos : 0 < tm
  tm_lt : tm < 1
  b_pos : 0 < b
  ρ_pos : 0 < ρ
  hm_pos : 0 < hm
  hbm : b * tm ≤ hm
  sp_pos : 0 < sp
  sp_lt : sp < 1
  kp_pos : 0 < kp
  roofp : kp < b * (1 - sp)
  sm_pos : 0 < sm
  sm_lt : sm < 1
  km_pos : 0 < km
  roofm : km * (1 - tm) < hm * (1 - sm)
  lam_pos : 0 < lam
  lam_lt : lam * tp * sp < b * (1 - tp) * sp + tp * kp

set_option hygiene false in
macro "fpre" H:ident : tactic => `(tactic| (
  obtain ⟨htp, htp1, htm, htm1, hb, hρ, hhm, hbm, hsp, hsp1, hkp, hroofp, hsm, hsm1, hkm, hroofm, hl, hlW⟩ := $H
  have a1 : 0 < 1 - tp := sub_pos.2 htp1
  have a2 : 0 < 1 - tm := sub_pos.2 htm1
  have a3 : 0 < 1 - sp := sub_pos.2 hsp1
  have a4 : 0 < 1 - sm := sub_pos.2 hsm1
  have r1 : 0 < 1 + ρ - tp := by linarith
  have r2 : 0 < 1 + ρ - tm := by linarith
  have r3 : 0 < b * (1 - sp) - kp := by linarith
  have f1 : 0 < hm * (1 + ρ) - ρ * b * tm := by
    nlinarith [mul_nonneg hρ.le (sub_nonneg.2 hbm)]
  skip))

section
variable {tp tm hm sp kp sm km ρ b lam : ℝ}

theorem lx_VMB (H : FPar tp tm hm sp kp sm km ρ b lam) : Lx ρ b lam pV (pM tm hm) pB := by
  fpre H
  refine Lx_of_pos ?_
  have e : Ot ρ b pV (pM tm hm) pB = hm * (1 + ρ) - ρ * b * tm := by
    simp only [Ot, crF, scF, C3.sub, pV, pM, pB]; ring
  rw [e]; exact f1

theorem lx_VMU (H : FPar tp tm hm sp kp sm km ρ b lam) : Lx ρ b lam pV (pM tm hm) (pU tp b) := by
  fpre H
  refine Lx_of_pos ?_
  have e : Ot ρ b pV (pM tm hm) (pU tp b) = hm * tp + tm * (b * (1 - tp)) := by
    simp only [Ot, crF, scF, C3.sub, pV, pM, pU]; ring
  rw [e]; positivity

theorem lx_VMW (H : FPar tp tm hm sp kp sm km ρ b lam) : Lx ρ b lam pV (pM tm hm) (pW sp kp) := by
  fpre H
  refine Lx_of_pos ?_
  have e : Ot ρ b pV (pM tm hm) (pW sp kp) = sp * (hm * (1 + ρ) - ρ * b * tm) + tm * kp := by
    simp only [Ot, crF, scF, C3.sub, pV, pM, pW]; ring
  rw [e]; positivity

end

section
variable {tp tm hm sp kp sm km ρ b lam : ℝ}

theorem lx_VMA (H : FPar tp tm hm sp kp sm km ρ b lam) : Lx ρ b lam pV (pM tm hm) pA := by
  fpre H
  refine Lx_of_pos ?_
  have e : Ot ρ b pV (pM tm hm) pA = hm := by
    simp only [Ot, crF, scF, C3.sub, pA, pM, pV]; ring
  rw [e]; positivity

theorem lx_VBU (H : FPar tp tm hm sp kp sm km ρ b lam) : Lx ρ b lam pV pB (pU tp b) := by
  fpre H
  refine Lx_of_pos ?_
  have e : Ot ρ b pV pB (pU tp b) = (1 + ρ) * (b * (1 - tp)) + ρ * b * tp := by
    simp only [Ot, crF, scF, C3.sub, pB, pU, pV]; ring
  rw [e]; positivity

theorem lx_VBW (H : FPar tp tm hm sp kp sm km ρ b lam) : Lx ρ b lam pV pB (pW sp kp) := by
  fpre H
  refine Lx_of_pos ?_
  have e : Ot ρ b pV pB (pW sp kp) = (1 + ρ) * kp := by
    simp only [Ot, crF, scF, C3.sub, pB, pV, pW]; ring
  rw [e]; positivity

theorem lx_VBA (H : FPar tp tm hm sp kp sm km ρ b lam) : Lx ρ b lam pV pB pA := by
  fpre H
  refine Lx_of_pos ?_
  have e : Ot ρ b pV pB pA = ρ * b := by
    simp only [Ot, crF, scF, C3.sub, pA, pB, pV]; ring
  rw [e]; positivity

theorem lx_VNB (H : FPar tp tm hm sp kp sm km ρ b lam) : Lx ρ b lam pV (pN sm km) pB := by
  fpre H
  refine Lx_of_pos ?_
  have e : Ot ρ b pV (pN sm km) pB = (1 + ρ) * km := by
    simp only [Ot, crF, scF, C3.sub, pB, pN, pV]; ring
  rw [e]; positivity

theorem lx_VNA (H : FPar tp tm hm sp kp sm km ρ b lam) : Lx ρ b lam pV (pN sm km) pA := by
  fpre H
  refine Lx_of_pos ?_
  have e : Ot ρ b pV (pN sm km) pA = km + ρ * b * sm := by
    simp only [Ot, crF, scF, C3.sub, pA, pN, pV]; ring
  rw [e]; positivity

theorem lx_VNU (H : FPar tp tm hm sp kp sm km ρ b lam) : Lx ρ b lam pV (pN sm km) (pU tp b) := by
  fpre H
  refine Lx_of_pos ?_
  have e : Ot ρ b pV (pN sm km) (pU tp b) = (1 + ρ) * (b * (1 - tp)) * sm + tp * km + ρ * b * tp * sm := by
    simp only [Ot, crF, scF, C3.sub, pN, pU, pV]; ring
  rw [e]; positivity

theorem lx_VNW (H : FPar tp tm hm sp kp sm km ρ b lam) : Lx ρ b lam pV (pN sm km) (pW sp kp) := by
  fpre H
  refine Lx_of_pos ?_
  have e : Ot ρ b pV (pN sm km) (pW sp kp) = (1 + ρ) * (sp * km + kp * sm) := by
    simp only [Ot, crF, scF, C3.sub, pN, pV, pW]; ring
  rw [e]; positivity

theorem lx_VAU (H : FPar tp tm hm sp kp sm km ρ b lam) : Lx ρ b lam pV pA (pU tp b) := by
  fpre H
  refine Lx_of_pos ?_
  have e : Ot ρ b pV pA (pU tp b) = b * (1 - tp) := by
    simp only [Ot, crF, scF, C3.sub, pA, pU, pV]; ring
  rw [e]; positivity

theorem lx_NBU (H : FPar tp tm hm sp kp sm km ρ b lam) : Lx ρ b lam (pN sm km) pB (pU tp b) := by
  fpre H
  refine Lx_of_pos ?_
  have e : Ot ρ b (pN sm km) pB (pU tp b) = km * (1 + ρ - tp) + (1 - sm) * ((1 + ρ) * (b * (1 - tp)) + ρ * b * tp) := by
    simp only [Ot, crF, scF, C3.sub, pB, pN, pU]; ring
  rw [e]; positivity

theorem lx_MBU (H : FPar tp tm hm sp kp sm km ρ b lam) : Lx ρ b lam (pM tm hm) pB (pU tp b) := by
  fpre H
  refine Lx_of_pos ?_
  have e : Ot ρ b (pM tm hm) pB (pU tp b) = (1 + ρ - tp) * (hm + b * (1 - tm)) := by
    simp only [Ot, crF, scF, C3.sub, pB, pM, pU]; ring
  rw [e]; positivity

theorem lx_BUW (H : FPar tp tm hm sp kp sm km ρ b lam) : Lx ρ b lam pB (pU tp b) (pW sp kp) := by
  fpre H
  refine Lx_of_pos ?_
  have e : Ot ρ b pB (pU tp b) (pW sp kp) = (1 + ρ - tp) * (b * (1 - sp) - kp) := by
    simp only [Ot, crF, scF, C3.sub, pB, pU, pW]; ring
  rw [e]; positivity

theorem lx_NBW (H : FPar tp tm hm sp kp sm km ρ b lam) : Lx ρ b lam (pN sm km) pB (pW sp kp) := by
  fpre H
  refine Lx_of_pos ?_
  have e : Ot ρ b (pN sm km) pB (pW sp kp) = (1 + ρ) * (km * (1 - sp) + kp * (1 - sm)) := by
    simp only [Ot, crF, scF, C3.sub, pB, pN, pW]; ring
  rw [e]; positivity

theorem lx_NBA (H : FPar tp tm hm sp kp sm km ρ b lam) : Lx ρ b lam (pN sm km) pB pA := by
  fpre H
  refine Lx_of_pos ?_
  have e : Ot ρ b (pN sm km) pB pA = ρ * km + ρ * b * (1 - sm) := by
    simp only [Ot, crF, scF, C3.sub, pA, pB, pN]; ring
  rw [e]; positivity

theorem lx_MBW (H : FPar tp tm hm sp kp sm km ρ b lam) : Lx ρ b lam (pM tm hm) pB (pW sp kp) := by
  fpre H
  refine Lx_of_pos ?_
  have e : Ot ρ b (pM tm hm) pB (pW sp kp) = (1 - sp) * (hm * (1 + ρ) - ρ * b * tm) + kp * (1 + ρ - tm) := by
    simp only [Ot, crF, scF, C3.sub, pB, pM, pW]; ring
  rw [e]; positivity

theorem lx_MBA (H : FPar tp tm hm sp kp sm km ρ b lam) : Lx ρ b lam (pM tm hm) pB pA := by
  fpre H
  refine Lx_of_pos ?_
  have e : Ot ρ b (pM tm hm) pB pA = ρ * hm + ρ * b * (1 - tm) := by
    simp only [Ot, crF, scF, C3.sub, pA, pB, pM]; ring
  rw [e]; positivity

end

section
variable {tp tm hm sp kp sm km ρ b lam : ℝ}

theorem lx_VMN_of (H : FPar tp tm hm sp kp sm km ρ b lam)
    (h : 0 ≤ Ot ρ b pV (pM tm hm) (pN sm km)) : Lx ρ b lam pV (pM tm hm) (pN sm km) := by
  fpre H
  refine ⟨h, fun _ => ?_⟩
  have e : Tt lam pV (pM tm hm) (pN sm km) = hm * sm + tm * km + lam * tm * sm := by
    simp only [Tt, Dc, dF, C3.sub, pV, pM, pN]; ring
  rw [e]; positivity

theorem lx_VNM_of (H : FPar tp tm hm sp kp sm km ρ b lam)
    (h : Ot ρ b pV (pM tm hm) (pN sm km) < 0) : Lx ρ b lam pV (pN sm km) (pM tm hm) := by
  refine Lx_of_pos ?_
  rw [Ot_swap]; linarith

theorem lx_UVW_of (H : FPar tp tm hm sp kp sm km ρ b lam)
    (h : 0 ≤ Ot ρ b (pU tp b) pV (pW sp kp)) : Lx ρ b lam (pU tp b) pV (pW sp kp) := by
  fpre H
  refine ⟨h, fun _ => ?_⟩
  have e : Tt lam (pU tp b) pV (pW sp kp) = b * (1 - tp) * sp + tp * kp - lam * tp * sp := by
    simp only [Tt, Dc, dF, C3.sub, pV, pU, pW]; ring
  rw [e]; linarith

theorem lx_BUA (H : FPar tp tm hm sp kp sm km ρ b lam) : Lx ρ b lam pB (pU tp b) pA := by
  fpre H
  refine ⟨le_of_eq ?_, fun _ => ?_⟩
  · simp only [Ot, crF, scF, C3.sub, pB, pU, pA]; ring
  · have e : Tt lam pB (pU tp b) pA = 2 * (b * (1 - tp)) + lam * (1 - tp) := by
      simp only [Tt, Dc, dF, C3.sub, pB, pU, pA]; ring
    rw [e]; positivity

/-- The key relation between the orientation numbers `x = O(v,m1-,m2-)`, `z = O(m1-,xb,m2-)`. -/
theorem star_rel (tm hm sm km ρ b : ℝ) :
    km * ((1 + ρ) * sm - tm) = Ot ρ b pV (pM tm hm) (pN sm km) * (1 - sm) -
      sm * Ot ρ b (pM tm hm) pB (pN sm km) := by
  simp only [Ot, crF, scF, C3.sub, pV, pM, pB, pN]; ring

theorem star_U (tp tm hm sm km ρ b : ℝ) :
    (1 + ρ) * Ot ρ b (pM tm hm) (pN sm km) (pU tp b) =
      (1 + ρ - tp) * (Ot ρ b pV (pM tm hm) (pN sm km) + b * ((1 + ρ) * sm - tm)) -
        tp * Ot ρ b (pM tm hm) pB (pN sm km) := by
  simp only [Ot, crF, scF, C3.sub, pV, pM, pB, pN, pU]; ring

theorem star_W (tm hm sp kp sm km ρ b : ℝ) :
    Ot ρ b (pM tm hm) (pN sm km) (pW sp kp) =
      Ot ρ b pV (pM tm hm) (pN sm km) * (1 - sp) - sp * Ot ρ b (pM tm hm) pB (pN sm km) +
        kp * ((1 + ρ) * sm - tm) := by
  simp only [Ot, crF, scF, C3.sub, pV, pM, pB, pN, pW]; ring

theorem star_A (tm hm sm km ρ b : ℝ) :
    (1 + ρ) * Ot ρ b (pM tm hm) (pN sm km) pA =
      ρ * Ot ρ b pV (pM tm hm) (pN sm km) - Ot ρ b (pM tm hm) pB (pN sm km) +
        ρ * b * ((1 + ρ) * sm - tm) := by
  simp only [Ot, crF, scF, C3.sub, pV, pM, pB, pN, pA]; ring

end

theorem Ot_swap12 (ρ b : ℝ) (P Q S : C3) : Ot ρ b Q P S = - Ot ρ b P Q S := by
  simp only [Ot, crF, scF, C3.sub]; ring

theorem star_y (tm hm sm km ρ b : ℝ) :
    Ot ρ b (pM tm hm) (pN sm km) pB =
      Ot ρ b pV (pM tm hm) (pN sm km) + (1 + ρ) * (km - hm) + ρ * b * tm := by
  simp only [Ot, crF, scF, C3.sub, pV, pM, pB, pN]; ring

section
variable {tp tm hm sp kp sm km ρ b lam : ℝ}

theorem starD (H : FPar tp tm hm sp kp sm km ρ b lam)
    (hx : Ot ρ b pV (pM tm hm) (pN sm km) < 0) (hz : 0 ≤ Ot ρ b (pM tm hm) pB (pN sm km)) :
    Lx ρ b lam (pN sm km) (pM tm hm) (pU tp b) ∧ Lx ρ b lam (pN sm km) (pM tm hm) (pW sp kp) ∧
      Lx ρ b lam (pN sm km) (pM tm hm) pA := by
  fpre H
  have rel := star_rel tm hm sm km ρ b
  have hΔ : (1 + ρ) * sm - tm < 0 := by
    by_contra hcon
    have hcon := not_lt.1 hcon
    nlinarith [mul_nonneg hkm.le hcon, mul_pos (neg_pos.2 hx) a4, mul_nonneg hsm.le hz]
  have hR : 0 < 1 + ρ := by linarith
  refine ⟨Lx_of_pos ?_, Lx_of_pos ?_, Lx_of_pos ?_⟩
  · refine lt_of_mul_lt_mul_left (a := 1 + ρ) ?_ hR.le
    rw [mul_zero, Ot_swap12, mul_neg, star_U]
    nlinarith [mul_pos r1 (neg_pos.2 hx), mul_pos r1 (mul_pos hb (neg_pos.2 hΔ)), mul_nonneg htp.le hz]
  · rw [Ot_swap12, star_W]
    nlinarith [mul_pos a3 (neg_pos.2 hx), mul_pos hkp (neg_pos.2 hΔ), mul_nonneg hsp.le hz]
  · refine lt_of_mul_lt_mul_left (a := 1 + ρ) ?_ hR.le
    rw [mul_zero, Ot_swap12, mul_neg, star_A]
    nlinarith [mul_pos hρ (neg_pos.2 hx), mul_pos hρ (mul_pos hb (neg_pos.2 hΔ))]

theorem starC (H : FPar tp tm hm sp kp sm km ρ b lam)
    (hx : Lx ρ b lam pV (pM tm hm) (pN sm km)) (hy : Lx ρ b lam (pM tm hm) (pN sm km) pB) :
    Lx ρ b lam (pM tm hm) (pN sm km) (pU tp b) ∧ Lx ρ b lam (pM tm hm) (pN sm km) (pW sp kp) ∧
      Lx ρ b lam (pM tm hm) (pN sm km) pA := by
  fpre H
  obtain ⟨hx0, -⟩ := hx
  obtain ⟨hy0, hyT⟩ := hy
  have hz : Ot ρ b (pM tm hm) pB (pN sm km) = - Ot ρ b (pM tm hm) (pN sm km) pB := Ot_swap ρ b _ _ _
  have rel := star_rel tm hm sm km ρ b
  rw [hz] at rel
  have hR : 0 < 1 + ρ := by linarith
  by_cases hD : 0 < (1 + ρ) * sm - tm
  · refine ⟨Lx_of_pos ?_, Lx_of_pos ?_, Lx_of_pos ?_⟩
    · refine lt_of_mul_lt_mul_left (a := 1 + ρ) ?_ hR.le
      rw [mul_zero, star_U, hz]
      nlinarith [mul_nonneg r1.le hx0, mul_pos r1 (mul_pos hb hD), mul_nonneg htp.le hy0]
    · rw [star_W, hz]
      nlinarith [mul_nonneg a3.le hx0, mul_pos hkp hD, mul_nonneg hsp.le hy0]
    · refine lt_of_mul_lt_mul_left (a := 1 + ρ) ?_ hR.le
      rw [mul_zero, star_A, hz]
      nlinarith [mul_nonneg hρ.le hx0, mul_pos hρ (mul_pos hb hD)]
  · have hD0 : (1 + ρ) * sm - tm = 0 := by
      have h1 : km * ((1 + ρ) * sm - tm) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hkm.le (not_lt.1 hD)
      have h2 : 0 ≤ km * ((1 + ρ) * sm - tm) := by
        rw [rel]; nlinarith [mul_nonneg hx0 a4.le, mul_nonneg hsm.le hy0]
      exact (mul_eq_zero.1 (le_antisymm h1 h2)).resolve_left hkm.ne'
    rw [hD0, mul_zero] at rel
    have hx00 : Ot ρ b pV (pM tm hm) (pN sm km) = 0 := by
      have : Ot ρ b pV (pM tm hm) (pN sm km) * (1 - sm) = 0 := by
        nlinarith [mul_nonneg hx0 a4.le, mul_nonneg hsm.le hy0]
      exact (mul_eq_zero.1 this).resolve_right a4.ne'
    have hy00 : Ot ρ b (pM tm hm) (pN sm km) pB = 0 := by
      have : sm * Ot ρ b (pM tm hm) (pN sm km) pB = 0 := by
        nlinarith [mul_nonneg hx0 a4.le, mul_nonneg hsm.le hy0]
      exact (mul_eq_zero.1 this).resolve_left hsm.ne'
    have hT := hyT hy00
    have hz0 : Ot ρ b (pM tm hm) pB (pN sm km) = 0 := by rw [hz, hy00]; simp
    have htm' : tm = (1 + ρ) * sm := by linarith
    have hy' := star_y tm hm sm km ρ b
    rw [hy00, hx00] at hy'
    have hhm' : hm = km + ρ * b * sm := by
      have : (1 + ρ) * (hm - km) = (1 + ρ) * (ρ * b * sm) := by
        rw [htm'] at hy'; nlinarith
      have := mul_left_cancel₀ hR.ne' this
      linarith
    have eU := star_U tp tm hm sm km ρ b
    have eW := star_W tm hm sp kp sm km ρ b
    have eA := star_A tm hm sm km ρ b
    rw [hx00, hz0, hD0] at eU eW eA
    have oU : Ot ρ b (pM tm hm) (pN sm km) (pU tp b) = 0 := by
      have : (1 + ρ) * Ot ρ b (pM tm hm) (pN sm km) (pU tp b) = 0 := by rw [eU]; ring
      exact (mul_eq_zero.1 this).resolve_left hR.ne'
    have oW : Ot ρ b (pM tm hm) (pN sm km) (pW sp kp) = 0 := by rw [eW]; ring
    have oA : Ot ρ b (pM tm hm) (pN sm km) pA = 0 := by
      have : (1 + ρ) * Ot ρ b (pM tm hm) (pN sm km) pA = 0 := by rw [eA]; ring
      exact (mul_eq_zero.1 this).resolve_left hR.ne'
    clear eU eW eA rel hz hy' hD hD0 hz0
    subst htm' hhm'
    refine ⟨⟨oU.ge, fun _ => ?_⟩, ⟨oW.ge, fun _ => ?_⟩, ⟨oA.ge, fun _ => ?_⟩⟩
    · have e : Tt lam (pM ((1 + ρ) * sm) (km + ρ * b * sm)) (pN sm km) (pU tp b) =
          Tt lam (pM ((1 + ρ) * sm) (km + ρ * b * sm)) (pN sm km) pB +
            sm * (ρ * b * (1 + tp) + lam * (1 + ρ - tp) + b * (1 - tp) * (2 + ρ)) := by
        simp only [Tt, Dc, dF, C3.sub, pM, pN, pU, pB]; ring
      rw [e]; positivity
    · have e : Tt lam (pM ((1 + ρ) * sm) (km + ρ * b * sm)) (pN sm km) (pW sp kp) =
          Tt lam (pM ((1 + ρ) * sm) (km + ρ * b * sm)) (pN sm km) pB +
            sm * (ρ * b * (1 - sp) + lam * (1 + ρ) * (1 - sp) + kp * (2 + ρ)) := by
        simp only [Tt, Dc, dF, C3.sub, pM, pN, pW, pB]; ring
      rw [e]; positivity
    · have e : Tt lam (pM ((1 + ρ) * sm) (km + ρ * b * sm)) (pN sm km) pA =
          Tt lam (pM ((1 + ρ) * sm) (km + ρ * b * sm)) (pN sm km) pB +
            sm * (2 * (ρ * b) + lam * ρ) := by
        simp only [Tt, Dc, dF, C3.sub, pM, pN, pA, pB]; ring
      rw [e]; positivity

end

section
variable {tp tm hm sp kp sm km ρ b lam : ℝ}

theorem rimFA_cyc (H : FPar tp tm hm sp kp sm km ρ b lam) (hx : Lx ρ b lam pV (pM tm hm) (pN sm km)) (hz : Lx ρ b lam (pM tm hm) pB (pN sm km))
    (hw : Lx ρ b lam (pU tp b) pV (pW sp kp)) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      CaseC09.ST (-1) (uF ρ b) (dF lam) (((quad pV (pM tm hm) pB (pU tp b)) (i + 1)).sub ((quad pV (pM tm hm) pB (pU tp b)) i))
        (((quad pV (pM tm hm) pB (pU tp b)) j).sub ((quad pV (pM tm hm) pB (pU tp b)) i)) := by
  have := lx_VMB H
  have := lx_VMU H
  have := lx_VMW H
  have := lx_VMA H
  have := lx_VBU H
  have := lx_VBW H
  have := lx_VBA H
  have := lx_VNA H
  have := lx_VNB H
  have := lx_VNU H
  have := lx_VNW H
  have := lx_VAU H
  have := lx_NBU H
  have := lx_MBU H
  have := lx_BUW H
  have := lx_NBW H
  have := lx_NBA H
  have := lx_MBW H
  have := lx_MBA H
  have := lx_BUA H
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i j h1 h2
  apply ST_of_Lx
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals simp only [b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
  all_goals
    first
    | assumption
    | (apply Lx_rot; assumption)
    | (apply Lx_rot; apply Lx_rot; assumption)

theorem rimFA_restW (H : FPar tp tm hm sp kp sm km ρ b lam) (hx : Lx ρ b lam pV (pM tm hm) (pN sm km)) (hz : Lx ρ b lam (pM tm hm) pB (pN sm km))
    (hw : Lx ρ b lam (pU tp b) pV (pW sp kp)) :
    ∀ i : ZMod 4,
      CaseC09.ST (-1) (uF ρ b) (dF lam) (((quad pV (pM tm hm) pB (pU tp b)) (i + 1)).sub ((quad pV (pM tm hm) pB (pU tp b)) i))
        ((pW sp kp).sub ((quad pV (pM tm hm) pB (pU tp b)) i)) := by
  have := lx_VMB H
  have := lx_VMU H
  have := lx_VMW H
  have := lx_VMA H
  have := lx_VBU H
  have := lx_VBW H
  have := lx_VBA H
  have := lx_VNA H
  have := lx_VNB H
  have := lx_VNU H
  have := lx_VNW H
  have := lx_VAU H
  have := lx_NBU H
  have := lx_MBU H
  have := lx_BUW H
  have := lx_NBW H
  have := lx_NBA H
  have := lx_MBW H
  have := lx_MBA H
  have := lx_BUA H
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  apply ST_of_Lx
  rcases zmod4_cases i with rfl | rfl | rfl | rfl
  all_goals simp only [b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
  all_goals
    first
    | assumption
    | (apply Lx_rot; assumption)
    | (apply Lx_rot; apply Lx_rot; assumption)

theorem rimFA_restN (H : FPar tp tm hm sp kp sm km ρ b lam) (hx : Lx ρ b lam pV (pM tm hm) (pN sm km)) (hz : Lx ρ b lam (pM tm hm) pB (pN sm km))
    (hw : Lx ρ b lam (pU tp b) pV (pW sp kp)) :
    ∀ i : ZMod 4,
      CaseC09.ST (-1) (uF ρ b) (dF lam) (((quad pV (pM tm hm) pB (pU tp b)) (i + 1)).sub ((quad pV (pM tm hm) pB (pU tp b)) i))
        ((pN sm km).sub ((quad pV (pM tm hm) pB (pU tp b)) i)) := by
  have := lx_VMB H
  have := lx_VMU H
  have := lx_VMW H
  have := lx_VMA H
  have := lx_VBU H
  have := lx_VBW H
  have := lx_VBA H
  have := lx_VNA H
  have := lx_VNB H
  have := lx_VNU H
  have := lx_VNW H
  have := lx_VAU H
  have := lx_NBU H
  have := lx_MBU H
  have := lx_BUW H
  have := lx_NBW H
  have := lx_NBA H
  have := lx_MBW H
  have := lx_MBA H
  have := lx_BUA H
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  apply ST_of_Lx
  rcases zmod4_cases i with rfl | rfl | rfl | rfl
  all_goals simp only [b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
  all_goals
    first
    | assumption
    | (apply Lx_rot; assumption)
    | (apply Lx_rot; apply Lx_rot; assumption)

theorem rimFA_restA (H : FPar tp tm hm sp kp sm km ρ b lam) (hx : Lx ρ b lam pV (pM tm hm) (pN sm km)) (hz : Lx ρ b lam (pM tm hm) pB (pN sm km))
    (hw : Lx ρ b lam (pU tp b) pV (pW sp kp)) :
    ∀ i : ZMod 4,
      CaseC09.ST (-1) (uF ρ b) (dF lam) (((quad pV (pM tm hm) pB (pU tp b)) (i + 1)).sub ((quad pV (pM tm hm) pB (pU tp b)) i))
        (pA.sub ((quad pV (pM tm hm) pB (pU tp b)) i)) := by
  have := lx_VMB H
  have := lx_VMU H
  have := lx_VMW H
  have := lx_VMA H
  have := lx_VBU H
  have := lx_VBW H
  have := lx_VBA H
  have := lx_VNA H
  have := lx_VNB H
  have := lx_VNU H
  have := lx_VNW H
  have := lx_VAU H
  have := lx_NBU H
  have := lx_MBU H
  have := lx_BUW H
  have := lx_NBW H
  have := lx_NBA H
  have := lx_MBW H
  have := lx_MBA H
  have := lx_BUA H
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  apply ST_of_Lx
  rcases zmod4_cases i with rfl | rfl | rfl | rfl
  all_goals simp only [b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
  all_goals
    first
    | assumption
    | (apply Lx_rot; assumption)
    | (apply Lx_rot; apply Lx_rot; assumption)

theorem rimFB_cyc (H : FPar tp tm hm sp kp sm km ρ b lam) (hx : Ot ρ b pV (pM tm hm) (pN sm km) < 0) (hz : Lx ρ b lam (pN sm km) pB (pM tm hm))
    (hw : Lx ρ b lam (pU tp b) pV (pW sp kp)) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      CaseC09.ST (-1) (uF ρ b) (dF lam) (((quad pV (pN sm km) pB (pU tp b)) (i + 1)).sub ((quad pV (pN sm km) pB (pU tp b)) i))
        (((quad pV (pN sm km) pB (pU tp b)) j).sub ((quad pV (pN sm km) pB (pU tp b)) i)) := by
  have hxN := lx_VNM_of H hx
  have := lx_VMB H
  have := lx_VMU H
  have := lx_VMW H
  have := lx_VMA H
  have := lx_VBU H
  have := lx_VBW H
  have := lx_VBA H
  have := lx_VNA H
  have := lx_VNB H
  have := lx_VNU H
  have := lx_VNW H
  have := lx_VAU H
  have := lx_NBU H
  have := lx_MBU H
  have := lx_BUW H
  have := lx_NBW H
  have := lx_NBA H
  have := lx_MBW H
  have := lx_MBA H
  have := lx_BUA H
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i j h1 h2
  apply ST_of_Lx
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals simp only [b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
  all_goals
    first
    | assumption
    | (apply Lx_rot; assumption)
    | (apply Lx_rot; apply Lx_rot; assumption)

theorem rimFB_restW (H : FPar tp tm hm sp kp sm km ρ b lam) (hx : Ot ρ b pV (pM tm hm) (pN sm km) < 0) (hz : Lx ρ b lam (pN sm km) pB (pM tm hm))
    (hw : Lx ρ b lam (pU tp b) pV (pW sp kp)) :
    ∀ i : ZMod 4,
      CaseC09.ST (-1) (uF ρ b) (dF lam) (((quad pV (pN sm km) pB (pU tp b)) (i + 1)).sub ((quad pV (pN sm km) pB (pU tp b)) i))
        ((pW sp kp).sub ((quad pV (pN sm km) pB (pU tp b)) i)) := by
  have hxN := lx_VNM_of H hx
  have := lx_VMB H
  have := lx_VMU H
  have := lx_VMW H
  have := lx_VMA H
  have := lx_VBU H
  have := lx_VBW H
  have := lx_VBA H
  have := lx_VNA H
  have := lx_VNB H
  have := lx_VNU H
  have := lx_VNW H
  have := lx_VAU H
  have := lx_NBU H
  have := lx_MBU H
  have := lx_BUW H
  have := lx_NBW H
  have := lx_NBA H
  have := lx_MBW H
  have := lx_MBA H
  have := lx_BUA H
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  apply ST_of_Lx
  rcases zmod4_cases i with rfl | rfl | rfl | rfl
  all_goals simp only [b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
  all_goals
    first
    | assumption
    | (apply Lx_rot; assumption)
    | (apply Lx_rot; apply Lx_rot; assumption)

theorem rimFB_restM (H : FPar tp tm hm sp kp sm km ρ b lam) (hx : Ot ρ b pV (pM tm hm) (pN sm km) < 0) (hz : Lx ρ b lam (pN sm km) pB (pM tm hm))
    (hw : Lx ρ b lam (pU tp b) pV (pW sp kp)) :
    ∀ i : ZMod 4,
      CaseC09.ST (-1) (uF ρ b) (dF lam) (((quad pV (pN sm km) pB (pU tp b)) (i + 1)).sub ((quad pV (pN sm km) pB (pU tp b)) i))
        ((pM tm hm).sub ((quad pV (pN sm km) pB (pU tp b)) i)) := by
  have hxN := lx_VNM_of H hx
  have := lx_VMB H
  have := lx_VMU H
  have := lx_VMW H
  have := lx_VMA H
  have := lx_VBU H
  have := lx_VBW H
  have := lx_VBA H
  have := lx_VNA H
  have := lx_VNB H
  have := lx_VNU H
  have := lx_VNW H
  have := lx_VAU H
  have := lx_NBU H
  have := lx_MBU H
  have := lx_BUW H
  have := lx_NBW H
  have := lx_NBA H
  have := lx_MBW H
  have := lx_MBA H
  have := lx_BUA H
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  apply ST_of_Lx
  rcases zmod4_cases i with rfl | rfl | rfl | rfl
  all_goals simp only [b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
  all_goals
    first
    | assumption
    | (apply Lx_rot; assumption)
    | (apply Lx_rot; apply Lx_rot; assumption)

theorem rimFB_restA (H : FPar tp tm hm sp kp sm km ρ b lam) (hx : Ot ρ b pV (pM tm hm) (pN sm km) < 0) (hz : Lx ρ b lam (pN sm km) pB (pM tm hm))
    (hw : Lx ρ b lam (pU tp b) pV (pW sp kp)) :
    ∀ i : ZMod 4,
      CaseC09.ST (-1) (uF ρ b) (dF lam) (((quad pV (pN sm km) pB (pU tp b)) (i + 1)).sub ((quad pV (pN sm km) pB (pU tp b)) i))
        (pA.sub ((quad pV (pN sm km) pB (pU tp b)) i)) := by
  have hxN := lx_VNM_of H hx
  have := lx_VMB H
  have := lx_VMU H
  have := lx_VMW H
  have := lx_VMA H
  have := lx_VBU H
  have := lx_VBW H
  have := lx_VBA H
  have := lx_VNA H
  have := lx_VNB H
  have := lx_VNU H
  have := lx_VNW H
  have := lx_VAU H
  have := lx_NBU H
  have := lx_MBU H
  have := lx_BUW H
  have := lx_NBW H
  have := lx_NBA H
  have := lx_MBW H
  have := lx_MBA H
  have := lx_BUA H
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  apply ST_of_Lx
  rcases zmod4_cases i with rfl | rfl | rfl | rfl
  all_goals simp only [b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
  all_goals
    first
    | assumption
    | (apply Lx_rot; assumption)
    | (apply Lx_rot; apply Lx_rot; assumption)

theorem rimFC_cyc (H : FPar tp tm hm sp kp sm km ρ b lam) (hx : Lx ρ b lam pV (pM tm hm) (pN sm km)) (hz : Lx ρ b lam (pM tm hm) (pN sm km) pB)
    (hw : Lx ρ b lam (pU tp b) pV (pW sp kp)) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      CaseC09.ST (-1) (uF ρ b) (dF lam) (((quint pV (pM tm hm) (pN sm km) pB (pU tp b)) (i + 1)).sub ((quint pV (pM tm hm) (pN sm km) pB (pU tp b)) i))
        (((quint pV (pM tm hm) (pN sm km) pB (pU tp b)) j).sub ((quint pV (pM tm hm) (pN sm km) pB (pU tp b)) i)) := by
  obtain ⟨sU, sW, sA⟩ := starC H hx hz
  have := lx_VMB H
  have := lx_VMU H
  have := lx_VMW H
  have := lx_VMA H
  have := lx_VBU H
  have := lx_VBW H
  have := lx_VBA H
  have := lx_VNA H
  have := lx_VNB H
  have := lx_VNU H
  have := lx_VNW H
  have := lx_VAU H
  have := lx_NBU H
  have := lx_MBU H
  have := lx_BUW H
  have := lx_NBW H
  have := lx_NBA H
  have := lx_MBW H
  have := lx_MBA H
  have := lx_BUA H
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i j h1 h2
  apply ST_of_Lx
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals simp only [b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
  all_goals
    first
    | assumption
    | (apply Lx_rot; assumption)
    | (apply Lx_rot; apply Lx_rot; assumption)

theorem rimFC_restW (H : FPar tp tm hm sp kp sm km ρ b lam) (hx : Lx ρ b lam pV (pM tm hm) (pN sm km)) (hz : Lx ρ b lam (pM tm hm) (pN sm km) pB)
    (hw : Lx ρ b lam (pU tp b) pV (pW sp kp)) :
    ∀ i : ZMod 5,
      CaseC09.ST (-1) (uF ρ b) (dF lam) (((quint pV (pM tm hm) (pN sm km) pB (pU tp b)) (i + 1)).sub ((quint pV (pM tm hm) (pN sm km) pB (pU tp b)) i))
        ((pW sp kp).sub ((quint pV (pM tm hm) (pN sm km) pB (pU tp b)) i)) := by
  obtain ⟨sU, sW, sA⟩ := starC H hx hz
  have := lx_VMB H
  have := lx_VMU H
  have := lx_VMW H
  have := lx_VMA H
  have := lx_VBU H
  have := lx_VBW H
  have := lx_VBA H
  have := lx_VNA H
  have := lx_VNB H
  have := lx_VNU H
  have := lx_VNW H
  have := lx_VAU H
  have := lx_NBU H
  have := lx_MBU H
  have := lx_BUW H
  have := lx_NBW H
  have := lx_NBA H
  have := lx_MBW H
  have := lx_MBA H
  have := lx_BUA H
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  apply ST_of_Lx
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
  all_goals
    first
    | assumption
    | (apply Lx_rot; assumption)
    | (apply Lx_rot; apply Lx_rot; assumption)

theorem rimFC_restA (H : FPar tp tm hm sp kp sm km ρ b lam) (hx : Lx ρ b lam pV (pM tm hm) (pN sm km)) (hz : Lx ρ b lam (pM tm hm) (pN sm km) pB)
    (hw : Lx ρ b lam (pU tp b) pV (pW sp kp)) :
    ∀ i : ZMod 5,
      CaseC09.ST (-1) (uF ρ b) (dF lam) (((quint pV (pM tm hm) (pN sm km) pB (pU tp b)) (i + 1)).sub ((quint pV (pM tm hm) (pN sm km) pB (pU tp b)) i))
        (pA.sub ((quint pV (pM tm hm) (pN sm km) pB (pU tp b)) i)) := by
  obtain ⟨sU, sW, sA⟩ := starC H hx hz
  have := lx_VMB H
  have := lx_VMU H
  have := lx_VMW H
  have := lx_VMA H
  have := lx_VBU H
  have := lx_VBW H
  have := lx_VBA H
  have := lx_VNA H
  have := lx_VNB H
  have := lx_VNU H
  have := lx_VNW H
  have := lx_VAU H
  have := lx_NBU H
  have := lx_MBU H
  have := lx_BUW H
  have := lx_NBW H
  have := lx_NBA H
  have := lx_MBW H
  have := lx_MBA H
  have := lx_BUA H
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  apply ST_of_Lx
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
  all_goals
    first
    | assumption
    | (apply Lx_rot; assumption)
    | (apply Lx_rot; apply Lx_rot; assumption)

theorem rimFD_cyc (H : FPar tp tm hm sp kp sm km ρ b lam) (hx : Ot ρ b pV (pM tm hm) (pN sm km) < 0) (hz : Lx ρ b lam (pM tm hm) pB (pN sm km))
    (hw : Lx ρ b lam (pU tp b) pV (pW sp kp)) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      CaseC09.ST (-1) (uF ρ b) (dF lam) (((quint pV (pN sm km) (pM tm hm) pB (pU tp b)) (i + 1)).sub ((quint pV (pN sm km) (pM tm hm) pB (pU tp b)) i))
        (((quint pV (pN sm km) (pM tm hm) pB (pU tp b)) j).sub ((quint pV (pN sm km) (pM tm hm) pB (pU tp b)) i)) := by
  have hxN := lx_VNM_of H hx
  obtain ⟨sU, sW, sA⟩ := starD H hx hz.1
  have := lx_VMB H
  have := lx_VMU H
  have := lx_VMW H
  have := lx_VMA H
  have := lx_VBU H
  have := lx_VBW H
  have := lx_VBA H
  have := lx_VNA H
  have := lx_VNB H
  have := lx_VNU H
  have := lx_VNW H
  have := lx_VAU H
  have := lx_NBU H
  have := lx_MBU H
  have := lx_BUW H
  have := lx_NBW H
  have := lx_NBA H
  have := lx_MBW H
  have := lx_MBA H
  have := lx_BUA H
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i j h1 h2
  apply ST_of_Lx
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals simp only [b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
  all_goals
    first
    | assumption
    | (apply Lx_rot; assumption)
    | (apply Lx_rot; apply Lx_rot; assumption)

theorem rimFD_restW (H : FPar tp tm hm sp kp sm km ρ b lam) (hx : Ot ρ b pV (pM tm hm) (pN sm km) < 0) (hz : Lx ρ b lam (pM tm hm) pB (pN sm km))
    (hw : Lx ρ b lam (pU tp b) pV (pW sp kp)) :
    ∀ i : ZMod 5,
      CaseC09.ST (-1) (uF ρ b) (dF lam) (((quint pV (pN sm km) (pM tm hm) pB (pU tp b)) (i + 1)).sub ((quint pV (pN sm km) (pM tm hm) pB (pU tp b)) i))
        ((pW sp kp).sub ((quint pV (pN sm km) (pM tm hm) pB (pU tp b)) i)) := by
  have hxN := lx_VNM_of H hx
  obtain ⟨sU, sW, sA⟩ := starD H hx hz.1
  have := lx_VMB H
  have := lx_VMU H
  have := lx_VMW H
  have := lx_VMA H
  have := lx_VBU H
  have := lx_VBW H
  have := lx_VBA H
  have := lx_VNA H
  have := lx_VNB H
  have := lx_VNU H
  have := lx_VNW H
  have := lx_VAU H
  have := lx_NBU H
  have := lx_MBU H
  have := lx_BUW H
  have := lx_NBW H
  have := lx_NBA H
  have := lx_MBW H
  have := lx_MBA H
  have := lx_BUA H
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  apply ST_of_Lx
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
  all_goals
    first
    | assumption
    | (apply Lx_rot; assumption)
    | (apply Lx_rot; apply Lx_rot; assumption)

theorem rimFD_restA (H : FPar tp tm hm sp kp sm km ρ b lam) (hx : Ot ρ b pV (pM tm hm) (pN sm km) < 0) (hz : Lx ρ b lam (pM tm hm) pB (pN sm km))
    (hw : Lx ρ b lam (pU tp b) pV (pW sp kp)) :
    ∀ i : ZMod 5,
      CaseC09.ST (-1) (uF ρ b) (dF lam) (((quint pV (pN sm km) (pM tm hm) pB (pU tp b)) (i + 1)).sub ((quint pV (pN sm km) (pM tm hm) pB (pU tp b)) i))
        (pA.sub ((quint pV (pN sm km) (pM tm hm) pB (pU tp b)) i)) := by
  have hxN := lx_VNM_of H hx
  obtain ⟨sU, sW, sA⟩ := starD H hx hz.1
  have := lx_VMB H
  have := lx_VMU H
  have := lx_VMW H
  have := lx_VMA H
  have := lx_VBU H
  have := lx_VBW H
  have := lx_VBA H
  have := lx_VNA H
  have := lx_VNB H
  have := lx_VNU H
  have := lx_VNW H
  have := lx_VAU H
  have := lx_NBU H
  have := lx_MBU H
  have := lx_BUW H
  have := lx_NBW H
  have := lx_NBA H
  have := lx_MBW H
  have := lx_MBA H
  have := lx_BUA H
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  apply ST_of_Lx
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
  all_goals
    first
    | assumption
    | (apply Lx_rot; assumption)
    | (apply Lx_rot; apply Lx_rot; assumption)

end

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
theorem robust_cycF5 {a c m : ℝ} (ha : a < 0) (hc : c < m) (hm : 0 < m) :
    IsRobustUnimodal (k := 5) (fun i : ZMod 5 => ![0, a, c, m, m] i) := by
  have hB : ∀ B : ZMod 5, B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by decide
  refine ⟨?_, ?_, ?_⟩
  · intro B a b c d hab hbc hcd hdk
    interval_cases d <;> interval_cases c <;> (try omega) <;> interval_cases b <;> (try omega) <;> interval_cases a <;> (try omega) <;> rcases hB B with rfl | rfl | rfl | rfl | rfl <;> norm_num <;> intros <;> skip <;> linarith
  · intro i j l hij hjl hil e1 e2
    rcases hB i with rfl | rfl | rfl | rfl | rfl <;> rcases hB j with rfl | rfl | rfl | rfl | rfl <;> rcases hB l with rfl | rfl | rfl | rfl | rfl <;> simp at hij hjl hil <;> norm_num at e1 e2 <;> skip <;> linarith
  · intro B a b c d hab hbc hcd hdk e
    interval_cases d <;> interval_cases c <;> (try omega) <;> interval_cases b <;> (try omega) <;> interval_cases a <;> (try omega) <;> rcases hB B with rfl | rfl | rfl | rfl | rfl <;> norm_num at e ⊢ <;> intros <;> skip <;> constructor <;> intro hh <;> linarith

theorem Tt_MBN (lam tm hm sm km : ℝ) :
    Tt lam (pM tm hm) pB (pN sm km) = (hm * (1 - sm) - km - tm * km) + lam * tm * (1 - sm) := by
  simp only [Tt, Dc, dF, C3.sub, pM, pB, pN]; ring

theorem Ot_NBM (ρ b tm hm sm km : ℝ) :
    Ot ρ b (pN sm km) pB (pM tm hm) = - Ot ρ b (pM tm hm) pB (pN sm km) := by
  simp only [Ot, crF, scF, C3.sub, pM, pB, pN]; ring

theorem Tt_NBM (lam tm hm sm km : ℝ) :
    Tt lam (pN sm km) pB (pM tm hm) = - Tt lam (pM tm hm) pB (pN sm km) := by
  simp only [Tt, Dc, dF, C3.sub, pM, pB, pN]; ring

/-- Choice of the tilt: for every valid `lam1`, either `lam1` or `lam1 / 2` makes `z = O(m1-,xb,m2-)`
lexicographically positive or negative. -/
theorem lam_choice {tp tm hm sp kp sm km ρ b lam1 : ℝ}
    (H : FPar tp tm hm sp kp sm km ρ b lam1) :
    (Lx ρ b lam1 (pM tm hm) pB (pN sm km) ∨ Lx ρ b lam1 (pN sm km) pB (pM tm hm)) ∨
      (FPar tp tm hm sp kp sm km ρ b (lam1 / 2) ∧ Lx ρ b (lam1 / 2) (pN sm km) pB (pM tm hm)) := by
  have htm := H.tm_pos
  have hsm1 := H.sm_lt
  have hl := H.lam_pos
  have a4 : 0 < 1 - sm := sub_pos.2 hsm1
  rcases lt_trichotomy (Ot ρ b (pM tm hm) pB (pN sm km)) 0 with hz | hz | hz
  · refine Or.inl (Or.inr (Lx_of_pos ?_))
    rw [Ot_NBM]; linarith
  · rcases lt_trichotomy (Tt lam1 (pM tm hm) pB (pN sm km)) 0 with hT | hT | hT
    · refine Or.inl (Or.inr ⟨by rw [Ot_NBM, hz]; simp, fun _ => ?_⟩)
      rw [Tt_NBM]; linarith
    · refine Or.inr ⟨⟨H.tp_pos, H.tp_lt, H.tm_pos, H.tm_lt, H.b_pos, H.ρ_pos, H.hm_pos, H.hbm, H.sp_pos,
        H.sp_lt, H.kp_pos, H.roofp, H.sm_pos, H.sm_lt, H.km_pos, H.roofm, by linarith, ?_⟩,
        ⟨by rw [Ot_NBM, hz]; simp, fun _ => ?_⟩⟩
      · have := H.lam_lt
        have h2 := mul_pos H.tp_pos H.sp_pos
        nlinarith
      · rw [Tt_NBM, Tt_MBN]
        rw [Tt_MBN] at hT
        nlinarith [mul_pos (mul_pos hl htm) a4]
    · exact Or.inl (Or.inl ⟨hz.ge, fun _ => hT⟩)
  · exact Or.inl (Or.inl (Lx_of_pos hz))


/-! ### Group E-F3: the rims with `m2+` shown (`oW < 0`): A+, B+, C+, D+ (PROOFS 37.4)

The rims `V M B U W`, `V N B U W`, `V M N B U W`, `V N M B U W` (`m2+` inserted after `m1+`); strict `oW < 0`
is the orientation of `(U, W, V)`.  New fixed-sign triples: `lx_UWV, lx_VAW, lx_UWA, lx_UWN, lx_MUW`
(all from `sp (1+ρ) < tp`, a consequence of `oW < 0` and the roof). -/

section
variable {tp tm hm sp kp sm km ρ b lam : ℝ}

theorem sR_lt (H : FPar tp tm hm sp kp sm km ρ b lam)
    (hW : Ot ρ b (pU tp b) pV (pW sp kp) < 0) : sp * (1 + ρ) < tp := by
  fpre H
  have e : Ot ρ b (pU tp b) pV (pW sp kp) = b * (1 - tp) * sp * (1 + ρ) - tp * kp + tp * sp * (ρ * b) := by
    simp only [Ot, crF, scF, C3.sub, pU, pV, pW]; ring
  rw [e] at hW
  by_contra hc
  push Not at hc
  nlinarith [mul_pos hb a1, mul_pos hb hsp, mul_nonneg hb.le (sub_nonneg.2 hc), mul_pos hb (mul_pos hsp hρ), mul_pos htp r3, mul_nonneg a1.le (mul_nonneg hb.le (sub_nonneg.2 hc))]

theorem lx_UWV (H : FPar tp tm hm sp kp sm km ρ b lam)
    (hW : Ot ρ b (pU tp b) pV (pW sp kp) < 0) : Lx ρ b lam (pU tp b) (pW sp kp) pV := by
  refine Lx_of_pos ?_
  have : Ot ρ b (pU tp b) (pW sp kp) pV = - Ot ρ b (pU tp b) pV (pW sp kp) := Ot_swap _ _ _ _ _
  rw [this]; linarith

theorem lx_VAW (H : FPar tp tm hm sp kp sm km ρ b lam)
    (hW : Ot ρ b (pU tp b) pV (pW sp kp) < 0) : Lx ρ b lam pV pA (pW sp kp) := by
  fpre H
  refine Lx_of_pos ?_
  have e : Ot ρ b pV pA (pW sp kp) = kp - sp * (ρ * b) := by
    simp only [Ot, crF, scF, C3.sub, pV, pA, pW]; ring
  have e2 : Ot ρ b (pU tp b) pV (pW sp kp) = b * (1 - tp) * sp * (1 + ρ) - tp * kp + tp * sp * (ρ * b) := by
    simp only [Ot, crF, scF, C3.sub, pU, pV, pW]; ring
  rw [e]; rw [e2] at hW
  by_contra hc
  push Not at hc
  nlinarith [mul_pos hb a1, mul_pos hb hsp, mul_pos (mul_pos hb a1) hsp, mul_pos (mul_pos hb a1) (mul_pos hsp hρ), mul_nonneg htp.le (sub_nonneg.2 hc)]

theorem lx_UWA (H : FPar tp tm hm sp kp sm km ρ b lam)
    (hW : Ot ρ b (pU tp b) pV (pW sp kp) < 0) : Lx ρ b lam (pU tp b) (pW sp kp) pA := by
  have hs := sR_lt H hW
  fpre H
  refine Lx_of_pos ?_
  have e : Ot ρ b (pU tp b) (pW sp kp) pA = b * (1 - tp) * (1 - sp * (1 + ρ)) - (kp - sp * (ρ * b)) * (1 - tp) := by
    simp only [Ot, crF, scF, C3.sub, pU, pW, pA]; ring
  rw [e]
  have : b * (1 - tp) * (1 - sp * (1 + ρ)) - (kp - sp * (ρ * b)) * (1 - tp) = (1 - tp) * (b * (1 - sp) - kp) := by ring
  rw [this]; positivity

theorem lx_UWN (H : FPar tp tm hm sp kp sm km ρ b lam)
    (hW : Ot ρ b (pU tp b) pV (pW sp kp) < 0) : Lx ρ b lam (pU tp b) (pW sp kp) (pN sm km) := by
  have hs := sR_lt H hW
  fpre H
  refine Lx_of_pos ?_
  have e : Ot ρ b (pU tp b) (pW sp kp) (pN sm km) =
      (tp - sp * (1 + ρ)) * (km + b * (1 - sm)) + (b * (1 - sp) - kp) * (sm * (1 + ρ) - tp) := by
    simp only [Ot, crF, scF, C3.sub, pU, pW, pN]; ring
  have e2 : Ot ρ b (pU tp b) pV (pW sp kp) = b * (1 - tp) * sp * (1 + ρ) - tp * kp + tp * sp * (ρ * b) := by
    simp only [Ot, crF, scF, C3.sub, pU, pV, pW]; ring
  rw [e]; rw [e2] at hW
  have hr : tp * (b * (1 - sp) - kp) < b * (tp - sp * (1 + ρ)) := by nlinarith
  have hd : 0 < tp - sp * (1 + ρ) := by linarith
  by_cases hc : tp ≤ sm * (1 + ρ)
  · nlinarith [mul_pos hd (add_pos hkm (mul_pos hb a4)), mul_nonneg r3.le (sub_nonneg.2 hc)]
  · push Not at hc
    have h1 : 0 ≤ (b * (tp - sp * (1 + ρ)) - tp * (b * (1 - sp) - kp)) * (tp - sm * (1 + ρ)) :=
      mul_nonneg (by linarith) (by linarith)
    have h2 : 0 < tp * (tp - sp * (1 + ρ)) * km + b * sm * (1 + ρ - tp) * (tp - sp * (1 + ρ)) := by positivity
    have h3 : 0 < tp * ((tp - sp * (1 + ρ)) * (km + b * (1 - sm)) + (b * (1 - sp) - kp) * (sm * (1 + ρ) - tp)) := by
      nlinarith
    exact pos_of_mul_pos_right h3 htp.le

theorem lx_MUW (H : FPar tp tm hm sp kp sm km ρ b lam)
    (hW : Ot ρ b (pU tp b) pV (pW sp kp) < 0) : Lx ρ b lam (pM tm hm) (pU tp b) (pW sp kp) := by
  have hs := sR_lt H hW
  fpre H
  refine Lx_of_pos ?_
  have e : Ot ρ b (pM tm hm) (pU tp b) (pW sp kp) =
      (tp - tm) * (kp - sp * (ρ * b)) - (b * (1 - tp) + hm) * (sp * (1 + ρ)) + tm * (b * (1 - tp)) + hm * tp := by
    simp only [Ot, crF, scF, C3.sub, pM, pU, pW]; ring
  have e2 : Ot ρ b (pU tp b) pV (pW sp kp) = b * (1 - tp) * sp * (1 + ρ) - tp * kp + tp * sp * (ρ * b) := by
    simp only [Ot, crF, scF, C3.sub, pU, pV, pW]; ring
  rw [e]; rw [e2] at hW
  have hr : tp * (b * (1 - sp) - kp) < b * (tp - sp * (1 + ρ)) := by nlinarith
  have hd : 0 < tp - sp * (1 + ρ) := by linarith
  nlinarith [mul_nonneg (sub_nonneg.2 hbm) hd.le, mul_pos htm r3]
theorem rimAP_cyc (H : FPar tp tm hm sp kp sm km ρ b lam) (hx : Lx ρ b lam pV (pM tm hm) (pN sm km)) (hz : Lx ρ b lam (pM tm hm) pB (pN sm km))
    (hW : Ot ρ b (pU tp b) pV (pW sp kp) < 0) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      CaseC09.ST (-1) (uF ρ b) (dF lam) (((quint pV (pM tm hm) pB (pU tp b) (pW sp kp)) (i + 1)).sub ((quint pV (pM tm hm) pB (pU tp b) (pW sp kp)) i))
        (((quint pV (pM tm hm) pB (pU tp b) (pW sp kp)) j).sub ((quint pV (pM tm hm) pB (pU tp b) (pW sp kp)) i)) := by
  have := lx_VMB H
  have := lx_VMU H
  have := lx_VMW H
  have := lx_VMA H
  have := lx_VBU H
  have := lx_VBW H
  have := lx_VBA H
  have := lx_VNA H
  have := lx_VNB H
  have := lx_VNU H
  have := lx_VNW H
  have := lx_VAU H
  have := lx_NBU H
  have := lx_MBU H
  have := lx_BUW H
  have := lx_NBW H
  have := lx_NBA H
  have := lx_MBW H
  have := lx_MBA H
  have := lx_BUA H
  have := lx_UWV H hW
  have := lx_VAW H hW
  have := lx_UWA H hW
  have := lx_UWN H hW
  have := lx_MUW H hW
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i j h1 h2
  apply ST_of_Lx
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals simp only [b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
  all_goals
    first
    | assumption
    | (apply Lx_rot; assumption)
    | (apply Lx_rot; apply Lx_rot; assumption)

theorem rimAP_restN (H : FPar tp tm hm sp kp sm km ρ b lam) (hx : Lx ρ b lam pV (pM tm hm) (pN sm km)) (hz : Lx ρ b lam (pM tm hm) pB (pN sm km))
    (hW : Ot ρ b (pU tp b) pV (pW sp kp) < 0) :
    ∀ i : ZMod 5,
      CaseC09.ST (-1) (uF ρ b) (dF lam) (((quint pV (pM tm hm) pB (pU tp b) (pW sp kp)) (i + 1)).sub ((quint pV (pM tm hm) pB (pU tp b) (pW sp kp)) i))
        ((pN sm km).sub ((quint pV (pM tm hm) pB (pU tp b) (pW sp kp)) i)) := by
  have := lx_VMB H
  have := lx_VMU H
  have := lx_VMW H
  have := lx_VMA H
  have := lx_VBU H
  have := lx_VBW H
  have := lx_VBA H
  have := lx_VNA H
  have := lx_VNB H
  have := lx_VNU H
  have := lx_VNW H
  have := lx_VAU H
  have := lx_NBU H
  have := lx_MBU H
  have := lx_BUW H
  have := lx_NBW H
  have := lx_NBA H
  have := lx_MBW H
  have := lx_MBA H
  have := lx_BUA H
  have := lx_UWV H hW
  have := lx_VAW H hW
  have := lx_UWA H hW
  have := lx_UWN H hW
  have := lx_MUW H hW
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  apply ST_of_Lx
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
  all_goals
    first
    | assumption
    | (apply Lx_rot; assumption)
    | (apply Lx_rot; apply Lx_rot; assumption)

theorem rimAP_restA (H : FPar tp tm hm sp kp sm km ρ b lam) (hx : Lx ρ b lam pV (pM tm hm) (pN sm km)) (hz : Lx ρ b lam (pM tm hm) pB (pN sm km))
    (hW : Ot ρ b (pU tp b) pV (pW sp kp) < 0) :
    ∀ i : ZMod 5,
      CaseC09.ST (-1) (uF ρ b) (dF lam) (((quint pV (pM tm hm) pB (pU tp b) (pW sp kp)) (i + 1)).sub ((quint pV (pM tm hm) pB (pU tp b) (pW sp kp)) i))
        (pA.sub ((quint pV (pM tm hm) pB (pU tp b) (pW sp kp)) i)) := by
  have := lx_VMB H
  have := lx_VMU H
  have := lx_VMW H
  have := lx_VMA H
  have := lx_VBU H
  have := lx_VBW H
  have := lx_VBA H
  have := lx_VNA H
  have := lx_VNB H
  have := lx_VNU H
  have := lx_VNW H
  have := lx_VAU H
  have := lx_NBU H
  have := lx_MBU H
  have := lx_BUW H
  have := lx_NBW H
  have := lx_NBA H
  have := lx_MBW H
  have := lx_MBA H
  have := lx_BUA H
  have := lx_UWV H hW
  have := lx_VAW H hW
  have := lx_UWA H hW
  have := lx_UWN H hW
  have := lx_MUW H hW
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  apply ST_of_Lx
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
  all_goals
    first
    | assumption
    | (apply Lx_rot; assumption)
    | (apply Lx_rot; apply Lx_rot; assumption)

theorem rimBP_cyc (H : FPar tp tm hm sp kp sm km ρ b lam) (hx : Ot ρ b pV (pM tm hm) (pN sm km) < 0) (hz : Lx ρ b lam (pN sm km) pB (pM tm hm))
    (hW : Ot ρ b (pU tp b) pV (pW sp kp) < 0) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      CaseC09.ST (-1) (uF ρ b) (dF lam) (((quint pV (pN sm km) pB (pU tp b) (pW sp kp)) (i + 1)).sub ((quint pV (pN sm km) pB (pU tp b) (pW sp kp)) i))
        (((quint pV (pN sm km) pB (pU tp b) (pW sp kp)) j).sub ((quint pV (pN sm km) pB (pU tp b) (pW sp kp)) i)) := by
  have hxN := lx_VNM_of H hx
  have := lx_VMB H
  have := lx_VMU H
  have := lx_VMW H
  have := lx_VMA H
  have := lx_VBU H
  have := lx_VBW H
  have := lx_VBA H
  have := lx_VNA H
  have := lx_VNB H
  have := lx_VNU H
  have := lx_VNW H
  have := lx_VAU H
  have := lx_NBU H
  have := lx_MBU H
  have := lx_BUW H
  have := lx_NBW H
  have := lx_NBA H
  have := lx_MBW H
  have := lx_MBA H
  have := lx_BUA H
  have := lx_UWV H hW
  have := lx_VAW H hW
  have := lx_UWA H hW
  have := lx_UWN H hW
  have := lx_MUW H hW
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i j h1 h2
  apply ST_of_Lx
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals simp only [b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
  all_goals
    first
    | assumption
    | (apply Lx_rot; assumption)
    | (apply Lx_rot; apply Lx_rot; assumption)

theorem rimBP_restM (H : FPar tp tm hm sp kp sm km ρ b lam) (hx : Ot ρ b pV (pM tm hm) (pN sm km) < 0) (hz : Lx ρ b lam (pN sm km) pB (pM tm hm))
    (hW : Ot ρ b (pU tp b) pV (pW sp kp) < 0) :
    ∀ i : ZMod 5,
      CaseC09.ST (-1) (uF ρ b) (dF lam) (((quint pV (pN sm km) pB (pU tp b) (pW sp kp)) (i + 1)).sub ((quint pV (pN sm km) pB (pU tp b) (pW sp kp)) i))
        ((pM tm hm).sub ((quint pV (pN sm km) pB (pU tp b) (pW sp kp)) i)) := by
  have hxN := lx_VNM_of H hx
  have := lx_VMB H
  have := lx_VMU H
  have := lx_VMW H
  have := lx_VMA H
  have := lx_VBU H
  have := lx_VBW H
  have := lx_VBA H
  have := lx_VNA H
  have := lx_VNB H
  have := lx_VNU H
  have := lx_VNW H
  have := lx_VAU H
  have := lx_NBU H
  have := lx_MBU H
  have := lx_BUW H
  have := lx_NBW H
  have := lx_NBA H
  have := lx_MBW H
  have := lx_MBA H
  have := lx_BUA H
  have := lx_UWV H hW
  have := lx_VAW H hW
  have := lx_UWA H hW
  have := lx_UWN H hW
  have := lx_MUW H hW
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  apply ST_of_Lx
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
  all_goals
    first
    | assumption
    | (apply Lx_rot; assumption)
    | (apply Lx_rot; apply Lx_rot; assumption)

theorem rimBP_restA (H : FPar tp tm hm sp kp sm km ρ b lam) (hx : Ot ρ b pV (pM tm hm) (pN sm km) < 0) (hz : Lx ρ b lam (pN sm km) pB (pM tm hm))
    (hW : Ot ρ b (pU tp b) pV (pW sp kp) < 0) :
    ∀ i : ZMod 5,
      CaseC09.ST (-1) (uF ρ b) (dF lam) (((quint pV (pN sm km) pB (pU tp b) (pW sp kp)) (i + 1)).sub ((quint pV (pN sm km) pB (pU tp b) (pW sp kp)) i))
        (pA.sub ((quint pV (pN sm km) pB (pU tp b) (pW sp kp)) i)) := by
  have hxN := lx_VNM_of H hx
  have := lx_VMB H
  have := lx_VMU H
  have := lx_VMW H
  have := lx_VMA H
  have := lx_VBU H
  have := lx_VBW H
  have := lx_VBA H
  have := lx_VNA H
  have := lx_VNB H
  have := lx_VNU H
  have := lx_VNW H
  have := lx_VAU H
  have := lx_NBU H
  have := lx_MBU H
  have := lx_BUW H
  have := lx_NBW H
  have := lx_NBA H
  have := lx_MBW H
  have := lx_MBA H
  have := lx_BUA H
  have := lx_UWV H hW
  have := lx_VAW H hW
  have := lx_UWA H hW
  have := lx_UWN H hW
  have := lx_MUW H hW
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  apply ST_of_Lx
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
  all_goals
    first
    | assumption
    | (apply Lx_rot; assumption)
    | (apply Lx_rot; apply Lx_rot; assumption)

theorem rimCP_cyc (H : FPar tp tm hm sp kp sm km ρ b lam) (hx : Lx ρ b lam pV (pM tm hm) (pN sm km)) (hz : Lx ρ b lam (pM tm hm) (pN sm km) pB)
    (hW : Ot ρ b (pU tp b) pV (pW sp kp) < 0) :
    ∀ i j : ZMod 6, j ≠ i → j ≠ i + 1 →
      CaseC09.ST (-1) (uF ρ b) (dF lam) (((hex6 pV (pM tm hm) (pN sm km) pB (pU tp b) (pW sp kp)) (i + 1)).sub ((hex6 pV (pM tm hm) (pN sm km) pB (pU tp b) (pW sp kp)) i))
        (((hex6 pV (pM tm hm) (pN sm km) pB (pU tp b) (pW sp kp)) j).sub ((hex6 pV (pM tm hm) (pN sm km) pB (pU tp b) (pW sp kp)) i)) := by
  obtain ⟨sU, sW, sA⟩ := starC H hx hz
  have := lx_VMB H
  have := lx_VMU H
  have := lx_VMW H
  have := lx_VMA H
  have := lx_VBU H
  have := lx_VBW H
  have := lx_VBA H
  have := lx_VNA H
  have := lx_VNB H
  have := lx_VNU H
  have := lx_VNW H
  have := lx_VAU H
  have := lx_NBU H
  have := lx_MBU H
  have := lx_BUW H
  have := lx_NBW H
  have := lx_NBA H
  have := lx_MBW H
  have := lx_MBA H
  have := lx_BUA H
  have := lx_UWV H hW
  have := lx_VAW H hW
  have := lx_UWA H hW
  have := lx_UWN H hW
  have := lx_MUW H hW
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := zmod6_add_one
  intro i j h1 h2
  apply ST_of_Lx
  rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals simp only [b0, b1, b2, b3, b4, b5, hex6_0, hex6_1, hex6_2, hex6_3, hex6_4, hex6_5]
  all_goals
    first
    | assumption
    | (apply Lx_rot; assumption)
    | (apply Lx_rot; apply Lx_rot; assumption)

theorem rimCP_restA (H : FPar tp tm hm sp kp sm km ρ b lam) (hx : Lx ρ b lam pV (pM tm hm) (pN sm km)) (hz : Lx ρ b lam (pM tm hm) (pN sm km) pB)
    (hW : Ot ρ b (pU tp b) pV (pW sp kp) < 0) :
    ∀ i : ZMod 6,
      CaseC09.ST (-1) (uF ρ b) (dF lam) (((hex6 pV (pM tm hm) (pN sm km) pB (pU tp b) (pW sp kp)) (i + 1)).sub ((hex6 pV (pM tm hm) (pN sm km) pB (pU tp b) (pW sp kp)) i))
        (pA.sub ((hex6 pV (pM tm hm) (pN sm km) pB (pU tp b) (pW sp kp)) i)) := by
  obtain ⟨sU, sW, sA⟩ := starC H hx hz
  have := lx_VMB H
  have := lx_VMU H
  have := lx_VMW H
  have := lx_VMA H
  have := lx_VBU H
  have := lx_VBW H
  have := lx_VBA H
  have := lx_VNA H
  have := lx_VNB H
  have := lx_VNU H
  have := lx_VNW H
  have := lx_VAU H
  have := lx_NBU H
  have := lx_MBU H
  have := lx_BUW H
  have := lx_NBW H
  have := lx_NBA H
  have := lx_MBW H
  have := lx_MBA H
  have := lx_BUA H
  have := lx_UWV H hW
  have := lx_VAW H hW
  have := lx_UWA H hW
  have := lx_UWN H hW
  have := lx_MUW H hW
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := zmod6_add_one
  intro i
  apply ST_of_Lx
  rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [b0, b1, b2, b3, b4, b5, hex6_0, hex6_1, hex6_2, hex6_3, hex6_4, hex6_5]
  all_goals
    first
    | assumption
    | (apply Lx_rot; assumption)
    | (apply Lx_rot; apply Lx_rot; assumption)

theorem rimDP_cyc (H : FPar tp tm hm sp kp sm km ρ b lam) (hx : Ot ρ b pV (pM tm hm) (pN sm km) < 0) (hz : Lx ρ b lam (pM tm hm) pB (pN sm km))
    (hW : Ot ρ b (pU tp b) pV (pW sp kp) < 0) :
    ∀ i j : ZMod 6, j ≠ i → j ≠ i + 1 →
      CaseC09.ST (-1) (uF ρ b) (dF lam) (((hex6 pV (pN sm km) (pM tm hm) pB (pU tp b) (pW sp kp)) (i + 1)).sub ((hex6 pV (pN sm km) (pM tm hm) pB (pU tp b) (pW sp kp)) i))
        (((hex6 pV (pN sm km) (pM tm hm) pB (pU tp b) (pW sp kp)) j).sub ((hex6 pV (pN sm km) (pM tm hm) pB (pU tp b) (pW sp kp)) i)) := by
  have hxN := lx_VNM_of H hx
  obtain ⟨sU, sW, sA⟩ := starD H hx hz.1
  have := lx_VMB H
  have := lx_VMU H
  have := lx_VMW H
  have := lx_VMA H
  have := lx_VBU H
  have := lx_VBW H
  have := lx_VBA H
  have := lx_VNA H
  have := lx_VNB H
  have := lx_VNU H
  have := lx_VNW H
  have := lx_VAU H
  have := lx_NBU H
  have := lx_MBU H
  have := lx_BUW H
  have := lx_NBW H
  have := lx_NBA H
  have := lx_MBW H
  have := lx_MBA H
  have := lx_BUA H
  have := lx_UWV H hW
  have := lx_VAW H hW
  have := lx_UWA H hW
  have := lx_UWN H hW
  have := lx_MUW H hW
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := zmod6_add_one
  intro i j h1 h2
  apply ST_of_Lx
  rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals simp only [b0, b1, b2, b3, b4, b5, hex6_0, hex6_1, hex6_2, hex6_3, hex6_4, hex6_5]
  all_goals
    first
    | assumption
    | (apply Lx_rot; assumption)
    | (apply Lx_rot; apply Lx_rot; assumption)

theorem rimDP_restA (H : FPar tp tm hm sp kp sm km ρ b lam) (hx : Ot ρ b pV (pM tm hm) (pN sm km) < 0) (hz : Lx ρ b lam (pM tm hm) pB (pN sm km))
    (hW : Ot ρ b (pU tp b) pV (pW sp kp) < 0) :
    ∀ i : ZMod 6,
      CaseC09.ST (-1) (uF ρ b) (dF lam) (((hex6 pV (pN sm km) (pM tm hm) pB (pU tp b) (pW sp kp)) (i + 1)).sub ((hex6 pV (pN sm km) (pM tm hm) pB (pU tp b) (pW sp kp)) i))
        (pA.sub ((hex6 pV (pN sm km) (pM tm hm) pB (pU tp b) (pW sp kp)) i)) := by
  have hxN := lx_VNM_of H hx
  obtain ⟨sU, sW, sA⟩ := starD H hx hz.1
  have := lx_VMB H
  have := lx_VMU H
  have := lx_VMW H
  have := lx_VMA H
  have := lx_VBU H
  have := lx_VBW H
  have := lx_VBA H
  have := lx_VNA H
  have := lx_VNB H
  have := lx_VNU H
  have := lx_VNW H
  have := lx_VAU H
  have := lx_NBU H
  have := lx_MBU H
  have := lx_BUW H
  have := lx_NBW H
  have := lx_NBA H
  have := lx_MBW H
  have := lx_MBA H
  have := lx_BUA H
  have := lx_UWV H hW
  have := lx_VAW H hW
  have := lx_UWA H hW
  have := lx_UWN H hW
  have := lx_MUW H hW
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := zmod6_add_one
  intro i
  apply ST_of_Lx
  rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [b0, b1, b2, b3, b4, b5, hex6_0, hex6_1, hex6_2, hex6_3, hex6_4, hex6_5]
  all_goals
    first
    | assumption
    | (apply Lx_rot; assumption)
    | (apply Lx_rot; apply Lx_rot; assumption)

end

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
theorem robust_cycP5 {a m w : ℝ} (ha : a < 0) (hw : 0 < w) (hwm : w < m) :
    IsRobustUnimodal (k := 5) (fun i : ZMod 5 => ![0, a, m, m, w] i) := by
  have hB : ∀ B : ZMod 5, B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by decide
  refine ⟨?_, ?_, ?_⟩
  · intro B a b c d hab hbc hcd hdk
    interval_cases d <;> interval_cases c <;> (try omega) <;> interval_cases b <;> (try omega) <;> interval_cases a <;> (try omega) <;> rcases hB B with rfl | rfl | rfl | rfl | rfl <;> norm_num <;> intros <;> skip <;> linarith
  · intro i j l hij hjl hil e1 e2
    rcases hB i with rfl | rfl | rfl | rfl | rfl <;> rcases hB j with rfl | rfl | rfl | rfl | rfl <;> rcases hB l with rfl | rfl | rfl | rfl | rfl <;> simp at hij hjl hil <;> norm_num at e1 e2 <;> skip <;> linarith
  · intro B a b c d hab hbc hcd hdk e
    interval_cases d <;> interval_cases c <;> (try omega) <;> interval_cases b <;> (try omega) <;> interval_cases a <;> (try omega) <;> rcases hB B with rfl | rfl | rfl | rfl | rfl <;> norm_num at e ⊢ <;> intros <;> skip <;> constructor <;> intro hh <;> linarith

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
theorem robust_cycP6 {a c m w : ℝ} (ha : a < 0) (hc : c < m) (hw : 0 < w) (hwm : w < m) :
    IsRobustUnimodal (k := 6) (fun i : ZMod 6 => ![0, a, c, m, m, w] i) := by
  have hB : ∀ B : ZMod 6, B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 ∨ B = 5 := by decide
  refine ⟨?_, ?_, ?_⟩
  · intro B a b c d hab hbc hcd hdk
    interval_cases d <;> interval_cases c <;> (try omega) <;> interval_cases b <;> (try omega) <;> interval_cases a <;> (try omega) <;> rcases hB B with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num <;> intros <;> skip <;> linarith
  · intro i j l hij hjl hil e1 e2
    rcases hB i with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hB j with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hB l with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hij hjl hil <;> norm_num at e1 e2 <;> skip <;> linarith
  · intro B a b c d hab hbc hcd hdk e
    interval_cases d <;> interval_cases c <;> (try omega) <;> interval_cases b <;> (try omega) <;> interval_cases a <;> (try omega) <;> rcases hB B with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num at e ⊢ <;> intros <;> skip <;> constructor <;> intro hh <;> linarith

namespace Frame18
variable {x : Fin 7 → ℝ³} (F : Frame18 x)

/-! ### Group E-defs: the sets `L_M'`, `Q`, `E_W` and small facts -/

/-- `L_M'` (the second disjunct of `CaseC18Special'`). -/
def LMp : Prop :=
  F.S.dp = F.S.A1 * F.S.tp ∧ F.S.A1 * F.S.tm ≤ F.S.dm ∧ F.S.ap < F.S.cp ∧ F.S.am < F.S.cm ∧
    F.gg * F.S.am * F.S.dm = F.a12 ∧ F.a11 * F.S.tp - F.gg * F.S.am * F.S.hp > F.a12 ∧
    F.a12 * F.S.cm ≤ F.a22 * F.S.am ∧ F.a22 * F.S.am ≤ F.a12 * F.S.dp

/-- `Q = L_M' ∩ {c- = d+, s+ + s- = 1}` (PROOFS 37.2). -/
def QW : Prop := F.LMp ∧ F.S.cm = F.S.dp ∧ F.S.sp + F.S.sm = 1

/-- `E_W = Q ∩ {a- s- = a+ s+, t+ s- = t- s+}` (PROOFS 37, the family E). -/
def EW : Prop := F.QW ∧ F.S.am * F.S.sm = F.S.ap * F.S.sp ∧ F.S.tp * F.S.sm = F.S.tm * F.S.sp

/-- `A12 = A11` and `A12 = A22` is impossible (it would give `u1 = u2`): proof by
`Fintype.linearIndependent_iff` with the coefficients `![1, -1, 0]`, and
`⟪u1 - u2, u1 - u2⟫ = a11 - 2 a12 + a22`. -/
theorem not_a12_eq_both (h1 : F.a12 = F.a11) (h2 : F.a12 = F.a22) : False := by
  have h : ⟪x 3 - x 4, x 3 - x 4⟫ = 0 := by
    have e1 : F.a11 = ⟪x 3 - x 5, x 3 - x 5⟫ := rfl
    have e2 : F.a22 = ⟪x 4 - x 5, x 4 - x 5⟫ := rfl
    have e3 : F.a12 = ⟪x 3 - x 5, x 4 - x 5⟫ := rfl
    have e4 : ⟪x 4 - x 5, x 3 - x 5⟫ = F.a12 := by rw [e3]; exact real_inner_comm _ _
    have : x 3 - x 4 = (x 3 - x 5) - (x 4 - x 5) := by abel
    have e5 : ⟪(x 3 - x 5) - (x 4 - x 5), (x 3 - x 5) - (x 4 - x 5)⟫ =
        ⟪x 3 - x 5, x 3 - x 5⟫ - ⟪x 3 - x 5, x 4 - x 5⟫ - ⟪x 4 - x 5, x 3 - x 5⟫ +
          ⟪x 4 - x 5, x 4 - x 5⟫ := by
      simp only [inner_sub_left, inner_sub_right]; ring
    rw [this, e5, ← e1, ← e2, ← e3, e4]
    linarith
  have h0 := inner_self_eq_zero.mp h
  have := F.toFrame7.coord_zero (a := 1) (b := -1) (c := 0) (by
    show (1 : ℝ) • (x 3 - x 5) + (-1 : ℝ) • (x 4 - x 5) + (0 : ℝ) • F.e = 0
    rw [show (1 : ℝ) • (x 3 - x 5) + (-1 : ℝ) • (x 4 - x 5) + (0 : ℝ) • F.e = x 3 - x 4 by module]
    exact h0)
  exact one_ne_zero this.1

theorem a12_lt_a11_of_eq_a22 (h : F.a12 = F.a22) : F.a12 < F.a11 :=
  lt_of_le_of_ne F.A12_le_A11 fun h1 => F.not_a12_eq_both h1 h

theorem a11_lt_a22_of_eq (h : F.a12 = F.a11) : F.a11 < F.a22 :=
  lt_of_le_of_ne (h ▸ F.A12_le_A22) fun h2 => F.not_a12_eq_both h (h.trans h2)

/-! ### Group E-A: Theorem E and Corollaries E1, E2 (edge view `m1+ - xb`; PROOFS 37.1)

View `u1 = m1+ - xb = (tp, -1, hp)` in frame coordinates, screen `(x + tp y, z + hp y)`, `σ = +1`
(`Dc a b u1 = cross2 (π a) (π b)`, checked by expansion).  Tilts `d = (d1, 0, d3)`;
`D1a = -hp d1 - (1 - tp) d3`, `D1b = -(1-sp)((dp - hp) d1 + tp d3)` (`dp - hp` is `d+ - h+`).
Sector `Q_H = {D1a > 0, D1b > 0}`: rim `(v, m1-, xa, m1+, m2+) = (5, 6, 3, 0, 1)`, `xb` (4) and `m2-`
(2) hidden.  Robust pattern: new `robust_cycH` (`0 < a1 < a2`, `a4 < a3`).  Referee fix 4: robust
route (`rupert_rim_rob`), not fixed tilts. -/

/-- Depths at `u1 = (tp, -1, hp)` of explicit coordinates. -/
theorem GGc_u1 (a b c : ℝ) :
    F.toFrame7.GG ⟨a, b, c⟩ ⟨F.S.tp, -1, F.S.hp⟩ =
      F.a11 * (a * F.S.tp) + F.a12 * (a * (-1) + F.S.tp * b) + F.a22 * (b * (-1)) +
        F.gg * (c * F.S.hp) := by
  rw [F.GG_eq]

/-- Rim (H) `(v, m1-, xa, m1+, m2+)` at the edge view `u1` with tilt `(d1, 0, d3)`, robust depths. -/
theorem rimH_rupert (d1 d3 : ℝ) (hDa : 0 < -F.S.hp * d1 - (1 - F.S.tp) * d3)
    (hDb : 0 < -((F.S.kp - F.S.hp * (1 - F.S.sp)) * d1 + F.S.tp * (1 - F.S.sp) * d3))
    (hc : F.S.cm < F.S.A1 * F.S.tp)
    (hz : IsRobustUnimodal (k := 5) fun i : ZMod 5 =>
      ![0, F.S.tm * (F.a11 * F.S.tp - F.a12) - F.gg * F.S.hp * F.S.hm,
        F.a11 * F.S.tp - F.a12, F.S.tp * (F.a11 * F.S.tp - F.a12) + F.gg * F.S.hp ^ 2,
        -F.S.sp * (F.a22 - F.a12 * F.S.tp) + F.gg * F.S.hp * F.S.kp] i) :
    IsRupert (Finset.univ.image x) := by
  have hcc : ∀ i, F.toFrame7.ptC (quint (5 : Fin 7) 6 3 0 1 i) =
      quint (⟨0, 0, 0⟩ : C3) ⟨F.S.tm, 0, -F.S.hm⟩ ⟨1, 0, 0⟩ ⟨F.S.tp, 0, F.S.hp⟩ ⟨0, F.S.sp, F.S.kp⟩ i := by
    intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [quint_0, quint_1, quint_2, quint_3, quint_4, F.ptC_5, F.ptC_6, F.ptC_3, F.ptC_0, F.ptC_1]
  have hroof := F.S.roof_p_poly
  have hroofm := F.S.roof_m_poly
  have hc' := F.S.hc_of_lt hc
  refine F.toFrame7.rupert_rim_rob (k := 5) (by norm_num) (quint (5 : Fin 7) 6 3 0 1) 1 (Or.inl rfl)
    ⟨F.S.tp, -1, F.S.hp⟩ ⟨d1, 0, d3⟩ (Or.inr (Or.inl (by norm_num))) ?_ ?_ ?_
  · intro i j h1 h2
    simp only [hcc]
    exact rimH_cyc F.S.tm F.S.hm F.S.tp F.S.hp F.S.sp F.S.kp d1 d3 F.S.tm_pos F.S.hm_pos F.S.tp_pos
      F.S.hp_pos F.S.tp_lt F.S.sp_pos F.S.sp_lt F.S.kp_pos F.S.tm_lt hroof i j h1 h2
  · intro j' hj' i
    simp only [hcc]
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (by simp [quint_3]) (hj' 3)
    · exact absurd (by simp [quint_4]) (hj' 4)
    · rw [F.ptC_2]
      exact rimH_rest F.S.tm F.S.hm F.S.tp F.S.hp F.S.sp F.S.kp F.S.sm F.S.km d1 d3 F.S.tm_pos
        F.S.hm_pos F.S.tp_pos F.S.hp_pos F.S.tp_lt F.S.sp_pos F.S.sp_lt F.S.kp_pos F.S.tm_lt
        F.S.sm_pos F.S.sm_lt F.S.km_pos hroof hroofm hc' hDa hDb _ (Or.inr rfl) i
    · exact absurd (by simp [quint_2]) (hj' 2)
    · rw [F.ptC_4]
      exact rimH_rest F.S.tm F.S.hm F.S.tp F.S.hp F.S.sp F.S.kp F.S.sm F.S.km d1 d3 F.S.tm_pos
        F.S.hm_pos F.S.tp_pos F.S.hp_pos F.S.tp_lt F.S.sp_pos F.S.sp_lt F.S.kp_pos F.S.tm_lt
        F.S.sm_pos F.S.sm_lt F.S.km_pos hroof hroofm hc' hDa hDb _ (Or.inl rfl) i
    · exact absurd (by simp [quint_0]) (hj' 0)
    · exact absurd (by simp [quint_1]) (hj' 1)
  · have : (fun i : ZMod 5 => F.toFrame7.GG (F.toFrame7.ptC (quint (5 : Fin 7) 6 3 0 1 i))
        ⟨F.S.tp, -1, F.S.hp⟩) = fun i : ZMod 5 =>
      ![0, F.S.tm * (F.a11 * F.S.tp - F.a12) - F.gg * F.S.hp * F.S.hm,
        F.a11 * F.S.tp - F.a12, F.S.tp * (F.a11 * F.S.tp - F.a12) + F.gg * F.S.hp ^ 2,
        -F.S.sp * (F.a22 - F.a12 * F.S.tp) + F.gg * F.S.hp * F.S.kp] i := by
      funext i
      rw [hcc]
      rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
        simp only [quint_0, quint_1, quint_2, quint_3, quint_4, F.GGc_u1] <;> simp <;> ring
    rw [this]; exact hz

/-- **Theorem E.**  (i) `Z1 > X`, (ii) `z_{u1}(m1+) > z_{u1}(m2+)`, (iii) `c- < A1 t+`.
(ii) written out: `z(m1+) = t+ (A11 t+ - A12) + g h+^2`,
`z(m2+) = -s+ (A22 - A12 t+) + g h+ k+`. -/
theorem thmE (hi : F.a11 * F.S.tp - F.gg * F.S.am * F.S.hp > F.a12)
    (hii : F.S.tp * (F.a11 * F.S.tp - F.a12) + F.gg * F.S.hp ^ 2 >
      -F.S.sp * (F.a22 - F.a12 * F.S.tp) + F.gg * F.S.hp * F.S.kp)
    (hiii : F.S.cm < F.S.A1 * F.S.tp) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨d1, d3, hDa, hDb⟩ := exists_tiltH F.S.tp F.S.hp F.S.sp F.S.kp F.S.tp_lt F.S.sp_lt
    F.S.roof_p_poly
  have hg := F.g_pos
  have hm := F.S.am_mul
  have e1 : F.gg * F.S.hp * F.S.hm < F.S.tm * (F.a11 * F.S.tp - F.a12) := by
    have := mul_lt_mul_of_pos_left hi F.S.tm_pos
    nlinarith [mul_pos hg F.S.hp_pos]
  have e1' : 0 < F.S.tm * (F.a11 * F.S.tp - F.a12) - F.gg * F.S.hp * F.S.hm := by linarith
  have e2 : 0 < F.a11 * F.S.tp - F.a12 := by
    by_contra hh
    push Not at hh
    nlinarith [mul_pos hg (mul_pos F.S.hp_pos F.S.hm_pos), mul_nonneg F.S.tm_pos.le (neg_nonneg.2 hh)]
  refine F.rimH_rupert d1 d3 hDa hDb hiii (robust_cycH e1' ?_ hii)
  nlinarith [mul_pos hg (mul_pos F.S.hp_pos F.S.hm_pos), F.S.tm_lt]

/-- `ii` of Theorem E for `L_M'` (the computation of Corollary E1; no `c- < d+` needed). -/
theorem hii_of_LMp (hL : F.LMp) :
    F.S.tp * (F.a11 * F.S.tp - F.a12) + F.gg * F.S.hp ^ 2 >
      -F.S.sp * (F.a22 - F.a12 * F.S.tp) + F.gg * F.S.hp * F.S.kp := by
  obtain ⟨hd, -, -, hamc, -, hi, hcm, -⟩ := hL
  have hg := F.g_pos
  have ha12 : 0 < F.a12 := F.A12_pos
  have hap := F.S.ap_mul
  have hdp := F.S.dp_mul
  have hA := F.S.A1_pos
  have hA1 : F.S.A1 = F.S.ap + F.S.am := rfl
  have hkp : F.S.kp = F.S.A1 * F.S.tp * (1 - F.S.sp) := by rw [← hd, ← hdp]
  have hhp : F.S.hp = F.S.ap * F.S.tp := hap.symm
  have hb : 0 < F.a22 - F.a12 * F.S.tp := by
    have h1 : F.a12 * F.S.cm ≤ F.a22 * F.S.am := hcm
    have h2 : F.a12 * F.S.am < F.a12 * F.S.cm := mul_lt_mul_of_pos_left hamc ha12
    have h3 : F.a22 * F.S.am > F.a12 * F.S.am := by linarith
    have h4 : F.a22 > F.a12 := lt_of_mul_lt_mul_right h3 F.S.am_pos.le
    nlinarith [F.S.tp_lt]
  have key : F.S.hp - F.S.kp = F.S.tp * (F.S.A1 * F.S.sp - F.S.am) := by
    rw [hkp, hhp, hA1]; ring
  have e1 : F.S.tp * (F.a11 * F.S.tp - F.a12 - F.gg * F.S.am * F.S.hp) > 0 :=
    mul_pos F.S.tp_pos (by linarith)
  have e2 : 0 < F.gg * F.S.hp * F.S.tp * (F.S.A1 * F.S.sp) :=
    mul_pos (mul_pos (mul_pos hg F.S.hp_pos) F.S.tp_pos) (mul_pos hA F.S.sp_pos)
  have e3 : 0 < F.S.sp * (F.a22 - F.a12 * F.S.tp) := mul_pos F.S.sp_pos hb
  have : F.S.tp * (F.a11 * F.S.tp - F.a12) + F.gg * F.S.hp ^ 2 -
      (-F.S.sp * (F.a22 - F.a12 * F.S.tp) + F.gg * F.S.hp * F.S.kp) =
      F.S.tp * (F.a11 * F.S.tp - F.a12 - F.gg * F.S.am * F.S.hp) +
        F.gg * F.S.hp * F.S.tp * (F.S.A1 * F.S.sp) +
        F.S.sp * (F.a22 - F.a12 * F.S.tp) := by
    have : F.gg * F.S.hp ^ 2 - F.gg * F.S.hp * F.S.kp = F.gg * F.S.hp * (F.S.hp - F.S.kp) := by ring
    rw [key] at this
    linear_combination this
  linarith


/-- **Corollary E1** (`L_M'` with `c- < d+`): (i), (iii) are given; (ii) by the computation of
PROOFS 37.1 (uses `Z1 > X`, `dp = A1 tp`, `A22 > A12 tp`). -/
theorem thmE1 (hL : F.LMp) (hlt : F.S.cm < F.S.dp) : IsRupert (Finset.univ.image x) := by
  obtain ⟨hd, -, -, -, -, hi, -, -⟩ := id hL
  exact F.thmE hi (F.hii_of_LMp hL) (hd ▸ hlt)

/-- The equalities of the window end `c- = d+` (`L_M'`): `h+ = a+ t+`, `h- = a- t-`,
`k+ = A1 t+ (1 - s+)`, `k- = s- A1 t+`, and the two roofs. -/
theorem e2_shape (hL : F.LMp) (heq : F.S.cm = F.S.dp) :
    F.S.hp = F.S.ap * F.S.tp ∧ F.S.hm = F.S.am * F.S.tm ∧
      F.S.kp = (F.S.ap + F.S.am) * F.S.tp * (1 - F.S.sp) ∧
      F.S.km = F.S.sm * ((F.S.ap + F.S.am) * F.S.tp) ∧
      F.S.am < (F.S.ap + F.S.am) * F.S.tp ∧
      F.S.sm * ((F.S.ap + F.S.am) * F.S.tp) * (1 - F.S.tm) < F.S.am * F.S.tm * (1 - F.S.sm) := by
  obtain ⟨hd, -, -, hamc, -, -, -, -⟩ := hL
  have hA1 : F.S.A1 = F.S.ap + F.S.am := rfl
  have hhp : F.S.hp = F.S.ap * F.S.tp := F.S.ap_mul.symm
  have hhm : F.S.hm = F.S.am * F.S.tm := F.S.am_mul.symm
  have hkp : F.S.kp = (F.S.ap + F.S.am) * F.S.tp * (1 - F.S.sp) := by
    rw [← F.S.dp_mul, hd, hA1]
  have hkm : F.S.km = F.S.sm * ((F.S.ap + F.S.am) * F.S.tp) := by
    rw [← F.S.cm_mul, heq, hd, hA1]; ring
  refine ⟨hhp, hhm, hkp, hkm, ?_, ?_⟩
  · have := hamc; rw [heq, hd, hA1] at this; exact this
  · have := F.S.roof_m_poly
    rw [hkm, hhm] at this
    exact this

/-- The metric facts at the window end: `A22 = g d- d+`, `beta1 := A22 - A12 t+ = g d- h+`,
`d-(1 - s-) = d+ s-`, and `z(m2+)(1 - s-) = g h+ d+ (1 - s+ - s-)`. -/
theorem e2_metric (hL : F.LMp) (heq : F.S.cm = F.S.dp) :
    F.a22 - F.a12 * F.S.tp = F.gg * F.S.dm * F.S.hp ∧
      (-F.S.sp * (F.a22 - F.a12 * F.S.tp) + F.gg * F.S.hp * F.S.kp) * (1 - F.S.sm) =
        F.gg * F.S.hp * F.S.dp * (1 - F.S.sp - F.S.sm) := by
  obtain ⟨hd, -, -, hamc, hgm, -, h7, h8⟩ := hL
  have hA1 : F.S.A1 = F.S.ap + F.S.am := rfl
  have hap := F.S.ap_mul
  have ham := F.S.am_pos
  have hkp := F.S.dp_mul
  have hkm : F.S.dm * (1 - F.S.sm) = F.S.dp * F.S.sm := by
    rw [F.S.dm_mul, ← F.S.cm_mul, heq]
  have hkm' : F.S.km = F.S.dp * F.S.sm := by rw [← F.S.cm_mul, heq]
  have h22 : F.a22 * F.S.am = F.a12 * F.S.dp := le_antisymm h8 (heq ▸ h7)
  have h22' : F.a22 = F.gg * F.S.dm * F.S.dp := by
    apply mul_right_cancel₀ ham.ne'
    rw [h22, ← hgm]; ring
  have hβ : F.a22 - F.a12 * F.S.tp = F.gg * F.S.dm * F.S.hp := by
    rw [h22', ← hgm, ← hap, hd, hA1]; ring
  refine ⟨hβ, ?_⟩
  rw [hβ]
  have : F.S.kp = F.S.dp * (1 - F.S.sp) := hkp.symm
  rw [this]
  have e : F.gg * F.S.hp * (F.S.dm * (1 - F.S.sm)) = F.gg * F.S.hp * (F.S.dp * F.S.sm) := by rw [hkm]
  linear_combination (-F.S.sp) * e

/-- Depths of `m1-` and `xa` (from `Z1 > X`): `0 < z(m1-) < z(xa)`. -/
theorem depth_basic (hi : F.a11 * F.S.tp - F.gg * F.S.am * F.S.hp > F.a12) :
    0 < F.S.tm * (F.a11 * F.S.tp - F.a12) - F.gg * F.S.hp * F.S.hm ∧
      F.S.tm * (F.a11 * F.S.tp - F.a12) - F.gg * F.S.hp * F.S.hm < F.a11 * F.S.tp - F.a12 := by
  have hg := F.g_pos
  have hm := F.S.am_mul
  have e1 : F.gg * F.S.hp * F.S.hm < F.S.tm * (F.a11 * F.S.tp - F.a12) := by
    have := mul_lt_mul_of_pos_left hi F.S.tm_pos
    nlinarith [mul_pos hg F.S.hp_pos]
  have e2 : 0 < F.a11 * F.S.tp - F.a12 := by
    by_contra hh
    push Not at hh
    nlinarith [mul_pos hg (mul_pos F.S.hp_pos F.S.hm_pos), mul_nonneg F.S.tm_pos.le (neg_nonneg.2 hh)]
  refine ⟨by linarith, ?_⟩
  nlinarith [mul_pos hg (mul_pos F.S.hp_pos F.S.hm_pos), F.S.tm_lt]


/-- Rim `(v, m2-, m1-, xa, m1+, m2+) = (5,2,6,3,0,1)` at `u1` with tilt `(d1, 0, d3)` on `Q_H`
at the window end `c- = d+`, robust depths. -/
theorem rimE2a_rupert (hL : F.LMp) (heq : F.S.cm = F.S.dp) (d1 d3 : ℝ)
    (hDa : 0 < -F.S.hp * d1 - (1 - F.S.tp) * d3)
    (hDb : 0 < -((F.S.kp - F.S.hp * (1 - F.S.sp)) * d1 + F.S.tp * (1 - F.S.sp) * d3))
    (hz : IsRobustUnimodal (k := 6) fun i : ZMod 6 =>
      ![0, -F.S.sm * (F.a22 - F.a12 * F.S.tp) - F.gg * F.S.hp * F.S.km,
        F.S.tm * (F.a11 * F.S.tp - F.a12) - F.gg * F.S.hp * F.S.hm,
        F.a11 * F.S.tp - F.a12, F.S.tp * (F.a11 * F.S.tp - F.a12) + F.gg * F.S.hp ^ 2,
        -F.S.sp * (F.a22 - F.a12 * F.S.tp) + F.gg * F.S.hp * F.S.kp] i) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨hhp, hhm, hkp, hkm, hr1, hr2⟩ := F.e2_shape hL heq
  have hDeq : -((F.S.kp - F.S.hp * (1 - F.S.sp)) * d1 + F.S.tp * (1 - F.S.sp) * d3) =
      -((1 - F.S.sp) * F.S.tp) * (F.S.am * d1 + d3) := by
    rw [hkp, hhp]; ring
  have hc0 : 0 < (1 - F.S.sp) * F.S.tp := mul_pos (sub_pos.2 F.S.sp_lt) F.S.tp_pos
  have hDe : F.S.am * d1 + d3 < 0 := by
    rw [hDeq] at hDb
    by_contra hh
    push Not at hh
    nlinarith [mul_nonneg hc0.le hh]
  have hDa' : 0 < -(F.S.ap * F.S.tp) * d1 - (1 - F.S.tp) * d3 := by rw [← hhp]; exact hDa
  let c : ZMod 6 → Fin 7 := ![5, 2, 6, 3, 0, 1]
  have hc : ∀ i, F.toFrame7.ptC (c i) =
      hex6 (⟨0, 0, 0⟩ : C3) ⟨0, F.S.sm, -F.S.km⟩ ⟨F.S.tm, 0, -F.S.hm⟩ ⟨1, 0, 0⟩ ⟨F.S.tp, 0, F.S.hp⟩
        ⟨0, F.S.sp, F.S.kp⟩ i := by
    intro i
    rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [c, hex6_0, hex6_1, hex6_2, hex6_3, hex6_4, hex6_5, F.ptC_5, F.ptC_2, F.ptC_6, F.ptC_3,
        F.ptC_0, F.ptC_1]
  refine F.toFrame7.rupert_rim_rob (k := 6) (by norm_num) c 1 (Or.inl rfl)
    ⟨F.S.tp, -1, F.S.hp⟩ ⟨d1, 0, d3⟩ (Or.inr (Or.inl (by norm_num))) ?_ ?_ ?_
  · intro i j h1 h2
    simp only [hc]
    exact rimE2a_cyc F.S.tm F.S.hm F.S.tp F.S.hp F.S.sp F.S.kp F.S.sm F.S.km F.S.ap F.S.am d1 d3
      F.S.tm_pos F.S.tp_pos F.S.tp_lt F.S.tm_lt F.S.sp_pos F.S.sp_lt F.S.sm_pos F.S.sm_lt
      F.S.ap_pos F.S.am_pos hhp hhm hkp hkm hr1 hr2 hDe i j h1 h2
  · intro j' hj' i
    simp only [hc]
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl (hj' 4)
    · exact absurd rfl (hj' 5)
    · exact absurd rfl (hj' 1)
    · exact absurd rfl (hj' 3)
    · rw [F.ptC_4]
      exact rimE2a_rest F.S.tm F.S.hm F.S.tp F.S.hp F.S.sp F.S.kp F.S.sm F.S.km F.S.ap F.S.am d1 d3
        F.S.tm_pos F.S.tp_pos F.S.tp_lt F.S.tm_lt F.S.sp_pos F.S.sp_lt F.S.sm_pos F.S.sm_lt
        F.S.ap_pos F.S.am_pos hhp hhm hkp hkm hr1 hr2 hDa' hDe i
    · exact absurd rfl (hj' 0)
    · exact absurd rfl (hj' 2)
  · have : (fun i : ZMod 6 => F.toFrame7.GG (F.toFrame7.ptC (c i)) ⟨F.S.tp, -1, F.S.hp⟩) =
        fun i : ZMod 6 =>
      ![0, -F.S.sm * (F.a22 - F.a12 * F.S.tp) - F.gg * F.S.hp * F.S.km,
        F.S.tm * (F.a11 * F.S.tp - F.a12) - F.gg * F.S.hp * F.S.hm,
        F.a11 * F.S.tp - F.a12, F.S.tp * (F.a11 * F.S.tp - F.a12) + F.gg * F.S.hp ^ 2,
        -F.S.sp * (F.a22 - F.a12 * F.S.tp) + F.gg * F.S.hp * F.S.kp] i := by
      funext i
      rw [hc]
      rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [hex6_0, hex6_1, hex6_2, hex6_3, hex6_4, hex6_5, F.GGc_u1] <;> simp <;> ring
    rw [this]; exact hz

/-- Rim `(v, m1-, xa, xb, m2+) = (5,6,3,4,1)` at `u1` with tilt `(d1, 0, d3)` on `Q_H'` at the
window end `c- = d+`, robust depths. -/
theorem rimE2b_rupert (hL : F.LMp) (heq : F.S.cm = F.S.dp) (d1 d3 : ℝ)
    (hDa : -F.S.hp * d1 - (1 - F.S.tp) * d3 < 0)
    (hDb : 0 < (F.S.kp - F.S.hp * (1 - F.S.sp)) * d1 + F.S.tp * (1 - F.S.sp) * d3)
    (hz : IsRobustUnimodal (k := 5) fun i : ZMod 5 =>
      ![0, F.S.tm * (F.a11 * F.S.tp - F.a12) - F.gg * F.S.hp * F.S.hm,
        F.a11 * F.S.tp - F.a12, -(F.a22 - F.a12 * F.S.tp),
        -F.S.sp * (F.a22 - F.a12 * F.S.tp) + F.gg * F.S.hp * F.S.kp] i) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨hhp, hhm, hkp, hkm, hr1, hr2⟩ := F.e2_shape hL heq
  have hDeq : -((F.S.kp - F.S.hp * (1 - F.S.sp)) * d1 + F.S.tp * (1 - F.S.sp) * d3) =
      -((1 - F.S.sp) * F.S.tp) * (F.S.am * d1 + d3) := by
    rw [hkp, hhp]; ring
  have hc0 : 0 < (1 - F.S.sp) * F.S.tp := mul_pos (sub_pos.2 F.S.sp_lt) F.S.tp_pos
  have hDe : 0 < F.S.am * d1 + d3 := by
    have h2 : (F.S.kp - F.S.hp * (1 - F.S.sp)) * d1 + F.S.tp * (1 - F.S.sp) * d3 =
        ((1 - F.S.sp) * F.S.tp) * (F.S.am * d1 + d3) := by
      rw [hkp, hhp]; ring
    rw [h2] at hDb
    exact pos_of_mul_pos_right hDb hc0.le
  have hDa' : -(F.S.ap * F.S.tp) * d1 - (1 - F.S.tp) * d3 < 0 := by rw [← hhp]; exact hDa
  have hcc : ∀ i, F.toFrame7.ptC (quint (5 : Fin 7) 6 3 4 1 i) =
      quint (⟨0, 0, 0⟩ : C3) ⟨F.S.tm, 0, -F.S.hm⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, F.S.sp, F.S.kp⟩ i := by
    intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [quint_0, quint_1, quint_2, quint_3, quint_4, F.ptC_5, F.ptC_6, F.ptC_3, F.ptC_4, F.ptC_1]
  refine F.toFrame7.rupert_rim_rob (k := 5) (by norm_num) (quint (5 : Fin 7) 6 3 4 1) 1 (Or.inl rfl)
    ⟨F.S.tp, -1, F.S.hp⟩ ⟨d1, 0, d3⟩ (Or.inr (Or.inl (by norm_num))) ?_ ?_ ?_
  · intro i j h1 h2
    simp only [hcc]
    exact rimE2b_cyc F.S.tm F.S.hm F.S.tp F.S.hp F.S.sp F.S.kp F.S.sm F.S.km F.S.ap F.S.am d1 d3
      F.S.tm_pos F.S.tp_pos F.S.tp_lt F.S.tm_lt F.S.sp_pos F.S.sp_lt F.S.sm_pos F.S.sm_lt
      F.S.ap_pos F.S.am_pos hhp hhm hkp hkm hr1 hr2 hDa' hDe i j h1 h2
  · intro j' hj' i
    simp only [hcc]
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [F.ptC_0]
      exact rimE2b_rest F.S.tm F.S.hm F.S.tp F.S.hp F.S.sp F.S.kp F.S.sm F.S.km F.S.ap F.S.am d1 d3
        F.S.tm_pos F.S.tp_pos F.S.tp_lt F.S.tm_lt F.S.sp_pos F.S.sp_lt F.S.sm_pos F.S.sm_lt
        F.S.ap_pos F.S.am_pos hhp hhm hkp hkm hr1 hr2 hDa' hDe _ (Or.inl rfl) i
    · exact absurd (by simp [quint_4]) (hj' 4)
    · rw [F.ptC_2]
      exact rimE2b_rest F.S.tm F.S.hm F.S.tp F.S.hp F.S.sp F.S.kp F.S.sm F.S.km F.S.ap F.S.am d1 d3
        F.S.tm_pos F.S.tp_pos F.S.tp_lt F.S.tm_lt F.S.sp_pos F.S.sp_lt F.S.sm_pos F.S.sm_lt
        F.S.ap_pos F.S.am_pos hhp hhm hkp hkm hr1 hr2 hDa' hDe _ (Or.inr rfl) i
    · exact absurd (by simp [quint_2]) (hj' 2)
    · exact absurd (by simp [quint_3]) (hj' 3)
    · exact absurd (by simp [quint_0]) (hj' 0)
    · exact absurd (by simp [quint_1]) (hj' 1)
  · have : (fun i : ZMod 5 => F.toFrame7.GG (F.toFrame7.ptC (quint (5 : Fin 7) 6 3 4 1 i))
        ⟨F.S.tp, -1, F.S.hp⟩) = fun i : ZMod 5 =>
      ![0, F.S.tm * (F.a11 * F.S.tp - F.a12) - F.gg * F.S.hp * F.S.hm,
        F.a11 * F.S.tp - F.a12, -(F.a22 - F.a12 * F.S.tp),
        -F.S.sp * (F.a22 - F.a12 * F.S.tp) + F.gg * F.S.hp * F.S.kp] i := by
      funext i
      rw [hcc]
      rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
        simp only [quint_0, quint_1, quint_2, quint_3, quint_4, F.GGc_u1] <;> simp <;> ring
    rw [this]; exact hz

/-- **Corollary E2** (`L_M'` with `c- = d+`): Rupert unless `s+ + s- = 1`.  Two sectors at `u1`:
`Q_H` (rim `(v, m2-, m1-, xa, m1+, m2+) = (5,2,6,3,0,1)`, `s+ + s- < 1`) and `Q_H' =
{D1a < 0, D1b < 0}` (rim `(v, m1-, xa, xb, m2+) = (5,6,3,4,1)`, `s+ + s- > 1`), using
`D1c = -(s- t- / ((1-s+) t+)) D1b` (m2- on the open side `(v, m1-)`). -/
theorem thmE2 (hL : F.LMp) (heq : F.S.cm = F.S.dp) :
    IsRupert (Finset.univ.image x) ∨ F.S.sp + F.S.sm = 1 := by
  by_cases hs : F.S.sp + F.S.sm = 1
  · exact Or.inr hs
  left
  obtain ⟨hmet1, hmet2⟩ := F.e2_metric hL heq
  have hi := hL.2.2.2.2.2.1
  obtain ⟨hz1, hz2⟩ := F.depth_basic hi
  have hii := F.hii_of_LMp hL
  have hg := F.g_pos
  have hβ : 0 < F.a22 - F.a12 * F.S.tp := by
    rw [hmet1]; exact mul_pos (mul_pos hg F.S.dm_pos) F.S.hp_pos
  have hpos : 0 < F.gg * F.S.hp * F.S.dp := mul_pos (mul_pos hg F.S.hp_pos) F.S.dp_pos
  have hsm1 := sub_pos.2 F.S.sm_lt
  obtain ⟨d1, d3, hDa, hDb⟩ := exists_tiltH F.S.tp F.S.hp F.S.sp F.S.kp F.S.tp_lt F.S.sp_lt
    F.S.roof_p_poly
  rcases lt_or_gt_of_ne hs with hlt | hgt
  · have hm2p : 0 < -F.S.sp * (F.a22 - F.a12 * F.S.tp) + F.gg * F.S.hp * F.S.kp := by
      by_contra hh
      push Not at hh
      nlinarith [mul_nonneg (neg_nonneg.2 hh) hsm1.le, mul_pos hpos (sub_pos.2 (show F.S.sp + F.S.sm < 1 from hlt))]
    have hm2m : -F.S.sm * (F.a22 - F.a12 * F.S.tp) - F.gg * F.S.hp * F.S.km < 0 := by
      nlinarith [mul_pos F.S.sm_pos hβ, mul_pos (mul_pos hg F.S.hp_pos) F.S.km_pos]
    exact F.rimE2a_rupert hL heq d1 d3 hDa hDb (robust_cycE6 hm2m hz1 hz2 hm2p hii)
  · have hm2p : -F.S.sp * (F.a22 - F.a12 * F.S.tp) + F.gg * F.S.hp * F.S.kp < 0 := by
      by_contra hh
      push Not at hh
      nlinarith [mul_nonneg hh hsm1.le, mul_pos hpos (sub_pos.2 (show 1 < F.S.sp + F.S.sm from hgt))]
    refine F.rimE2b_rupert hL heq (-d1) (-d3) (by linarith) (by linarith)
      (robust_cycE5 hz1 hz2 (neg_neg_of_pos hβ) hm2p)

/-! ### Group E-W: Theorem W (view `W = m2- - v`; PROOFS 37.2)

On `Q`: `k+ = k-`, F2 is a parallelogram.  View `W = (0, sm, -km)`, screen `(x, z + dp y)`
(`dp = km/sm`), `Dc a b W = - sm * cross2`, so `σ = -1`.  Sector W1: tilt `d = (-δx, 0, -δy)`, `δ =
(1, -am - 1)`, rim `(m2-, m1-, xa, m1+, m2+, v) = (2,6,3,0,1,5)`; sector W2: `δ = (-1, 0)`, rim
`(xb, m2-, m1-, xa, m1+, m2+) = (4,2,6,3,0,1)`.  The doubles `{v,m2-}`, `{m2+,xb}` are the
level edges of the depth cycles (robust patterns, new 6-cycle lemmas). -/

/-- Depths at the view `W = (0, sm, -km)`. -/
theorem GGc_W (a b c : ℝ) :
    F.toFrame7.GG ⟨a, b, c⟩ ⟨0, F.S.sm, -F.S.km⟩ =
      F.a11 * (a * 0) + F.a12 * (a * F.S.sm + 0 * b) + F.a22 * (b * F.S.sm) +
        F.gg * (c * -F.S.km) := by
  rw [F.GG_eq]

/-- On `Q`: the metric in terms of `lam = g d-`: `A12 = lam a-`, `A22 = lam A1 t+`, `g k = lam s+`. -/
theorem w_metric (hQ : F.QW) :
    ∃ lam : ℝ, 0 < lam ∧ F.a12 = lam * F.S.am ∧ F.a22 = lam * ((F.S.ap + F.S.am) * F.S.tp) ∧
      F.gg * F.S.km = lam * F.S.sp := by
  obtain ⟨hL, heq, hs⟩ := hQ
  obtain ⟨hd, -, -, -, hgm, -, h7, h8⟩ := id hL
  have ham := F.S.am_pos
  have h22 : F.a22 * F.S.am = F.a12 * F.S.dp := le_antisymm h8 (heq ▸ h7)
  refine ⟨F.gg * F.S.dm, mul_pos F.g_pos F.S.dm_pos, ?_, ?_, ?_⟩
  · rw [← hgm]; ring
  · apply mul_right_cancel₀ ham.ne'
    have : F.a12 = F.gg * F.S.dm * F.S.am := by rw [← hgm]; ring
    rw [h22, this, hd]
    have hA1 : F.S.A1 = F.S.ap + F.S.am := rfl
    rw [hA1]; ring
  · have := F.S.dm_mul
    have hsp : F.S.sp = 1 - F.S.sm := by linarith
    rw [hsp, ← this]; ring

/-- The depth of coordinates `(a, b, c)` at `W` on `Q`. -/
theorem w_depth (hQ : F.QW) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ a b c : ℝ, F.toFrame7.GG ⟨a, b, c⟩ ⟨0, F.S.sm, -F.S.km⟩ =
      lam * (F.S.sm * (F.S.am * a + (F.S.ap + F.S.am) * F.S.tp * b) - F.S.sp * c) := by
  obtain ⟨lam, hl, h12, h22, hk⟩ := F.w_metric hQ
  refine ⟨lam, hl, fun a b c => ?_⟩
  rw [F.GGc_W, h12, h22]
  have : F.gg * (c * -F.S.km) = -(F.gg * F.S.km) * c := by ring
  rw [this, hk]; ring

/-- The shape facts on `Q`, as in `e2_shape`, plus `W0 (c)`. -/
theorem w_shape (hQ : F.QW) :
    F.S.hp = F.S.ap * F.S.tp ∧ F.S.hm = F.S.am * F.S.tm ∧
      F.S.kp = (F.S.ap + F.S.am) * F.S.tp * (1 - F.S.sp) ∧
      F.S.km = F.S.sm * ((F.S.ap + F.S.am) * F.S.tp) ∧
      F.S.am < (F.S.ap + F.S.am) * F.S.tp ∧
      F.S.sm * ((F.S.ap + F.S.am) * F.S.tp) * (1 - F.S.tm) < F.S.am * F.S.tm * (1 - F.S.sm) ∧
      F.S.tm * F.S.sp ≤ F.S.tp * F.S.sm := by
  obtain ⟨hL, heq, hs⟩ := hQ
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := F.e2_shape hL heq
  refine ⟨h1, h2, h3, h4, h5, h6, ?_⟩
  obtain ⟨hd, hAtm, -⟩ := hL
  have hsp : F.S.sp = 1 - F.S.sm := by linarith
  -- `d- (1 - s-) = k-` and `A1 t- ≤ d-`
  have hdm := F.S.dm_mul
  have hA1 : F.S.A1 = F.S.ap + F.S.am := rfl
  have h : (F.S.ap + F.S.am) * F.S.tm * (1 - F.S.sm) ≤ F.S.km := by
    rw [← hdm, ← hA1]
    exact mul_le_mul_of_nonneg_right hAtm (sub_pos.2 F.S.sm_lt).le
  rw [h4] at h
  have hA : 0 < F.S.ap + F.S.am := add_pos F.S.ap_pos F.S.am_pos
  rw [hsp]
  by_contra hh
  push Not at hh
  have : F.S.sm * ((F.S.ap + F.S.am) * F.S.tp) < (F.S.ap + F.S.am) * F.S.tm * (1 - F.S.sm) := by
    nlinarith [mul_pos hA F.S.tm_pos]
  linarith

/-- Sector `W1`: rim `(m2-, m1-, xa, m1+, m2+, v) = (2,6,3,0,1,5)` at the view `W`, tilt
`(d1, 0, d3)`, `d1 < 0`, `a- d1 + d3 > 0`; needs `Δ ≤ M1-` and `M1+ > 0`. -/
theorem rimW1_rupert (hQ : F.QW) (d1 d3 : ℝ) (hd1 : d1 < 0) (hd3 : 0 < F.S.am * d1 + d3)
    (hΔ : (F.S.ap + F.S.am) * F.S.tp * F.S.sm ≤ F.S.am * F.S.tm)
    (hM : 0 < F.S.am * F.S.sm - F.S.ap * F.S.sp) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨hhp, hhm, hkp, hkm, hr1, hr2, hc⟩ := F.w_shape hQ
  have hs : F.S.sp + F.S.sm = 1 := hQ.2.2
  obtain ⟨lam, hl, hdep⟩ := F.w_depth hQ
  let c : ZMod 6 → Fin 7 := ![2, 6, 3, 0, 1, 5]
  have hc' : ∀ i, F.toFrame7.ptC (c i) =
      hex6 (⟨0, F.S.sm, -F.S.km⟩ : C3) ⟨F.S.tm, 0, -F.S.hm⟩ ⟨1, 0, 0⟩ ⟨F.S.tp, 0, F.S.hp⟩
        ⟨0, F.S.sp, F.S.kp⟩ ⟨0, 0, 0⟩ i := by
    intro i
    rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [c, hex6_0, hex6_1, hex6_2, hex6_3, hex6_4, hex6_5, F.ptC_5, F.ptC_2, F.ptC_6, F.ptC_3,
        F.ptC_0, F.ptC_1]
  have hsp : F.S.sp = 1 - F.S.sm := by linarith
  have hz : IsRobustUnimodal (k := 6) fun i : ZMod 6 =>
      F.toFrame7.GG (F.toFrame7.ptC (c i)) ⟨0, F.S.sm, -F.S.km⟩ := by
    have hz0 : 0 < F.S.sm * F.S.am := mul_pos F.S.sm_pos F.S.am_pos
    have e : (fun i : ZMod 6 => F.toFrame7.GG (F.toFrame7.ptC (c i)) ⟨0, F.S.sm, -F.S.km⟩) =
        fun i : ZMod 6 => hex6 (lam * ((F.S.ap + F.S.am) * F.S.tp * F.S.sm)) (lam * (F.S.am * F.S.tm))
          (lam * (F.S.am * F.S.sm)) (lam * (F.S.tp * (F.S.am * F.S.sm - F.S.ap * F.S.sp))) 0 0 i := by
      funext i
      rw [hc']
      rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [hex6_0, hex6_1, hex6_2, hex6_3, hex6_4, hex6_5, hdep] <;>
        (try simp only [hhp, hhm, hkp, hkm, hsp]) <;> ring
    rw [e]
    refine robust_cycW1 (mul_pos hl (mul_pos F.S.tp_pos hM)) ?_ ?_ ?_
    · have : F.S.tp * (F.S.am * F.S.sm - F.S.ap * F.S.sp) < F.S.am * F.S.sm := by
        nlinarith [F.S.tp_lt, mul_pos F.S.sp_pos F.S.ap_pos, mul_pos F.S.tp_pos hM, mul_pos hz0 F.S.tp_pos]
      exact mul_lt_mul_of_pos_left this hl
    · have : F.S.am * F.S.sm < (F.S.ap + F.S.am) * F.S.tp * F.S.sm := by
        nlinarith [mul_pos F.S.sm_pos (sub_pos.2 hr1)]
      exact mul_lt_mul_of_pos_left this hl
    · exact mul_le_mul_of_nonneg_left hΔ hl.le
  refine F.toFrame7.rupert_rim_rob (k := 6) (by norm_num) c (-1) (Or.inr rfl)
    ⟨0, F.S.sm, -F.S.km⟩ ⟨d1, 0, d3⟩ (Or.inr (Or.inl F.S.sm_pos.ne')) ?_ ?_ hz
  · intro i j h1 h2
    simp only [hc']
    exact rimW1_cyc F.S.tm F.S.hm F.S.tp F.S.hp F.S.sp F.S.kp F.S.sm F.S.km F.S.ap F.S.am d1 d3
      F.S.tm_pos F.S.tp_pos F.S.tp_lt F.S.tm_lt F.S.sm_pos F.S.sm_lt F.S.ap_pos F.S.am_pos hs
      hhp hhm hkp hkm hr1 hd1 hd3 i j h1 h2
  · intro j' hj' i
    simp only [hc']
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl (hj' 3)
    · exact absurd rfl (hj' 4)
    · exact absurd rfl (hj' 0)
    · exact absurd rfl (hj' 2)
    · rw [F.ptC_4]
      exact rimW1_rest F.S.tm F.S.hm F.S.tp F.S.hp F.S.sp F.S.kp F.S.sm F.S.km F.S.ap F.S.am d1 d3
        F.S.tm_pos F.S.tp_pos F.S.tp_lt F.S.tm_lt F.S.sm_pos F.S.sm_lt F.S.ap_pos F.S.am_pos hs
        hhp hhm hkp hkm hr1 hd1 hd3 i
    · exact absurd rfl (hj' 5)
    · exact absurd rfl (hj' 1)

/-- Sector `W2`: rim `(xb, m2-, m1-, xa, m1+, m2+) = (4,2,6,3,0,1)` at the view `W`, tilt
`(d1, 0, d3)`, `d1 > 0`, `a- d1 + d3 > 0`; needs `M1- < Δ` and `s- < t-`. -/
theorem rimW2_rupert (hQ : F.QW) (d1 d3 : ℝ) (hd1 : 0 < d1) (hd3 : 0 < F.S.am * d1 + d3)
    (hΔ : F.S.am * F.S.tm < (F.S.ap + F.S.am) * F.S.tp * F.S.sm)
    (hsm : F.S.sm < F.S.tm) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨hhp, hhm, hkp, hkm, hr1, hr2, hc⟩ := F.w_shape hQ
  have hs : F.S.sp + F.S.sm = 1 := hQ.2.2
  obtain ⟨lam, hl, hdep⟩ := F.w_depth hQ
  let c : ZMod 6 → Fin 7 := ![4, 2, 6, 3, 0, 1]
  have hc' : ∀ i, F.toFrame7.ptC (c i) =
      hex6 (⟨0, 1, 0⟩ : C3) ⟨0, F.S.sm, -F.S.km⟩ ⟨F.S.tm, 0, -F.S.hm⟩ ⟨1, 0, 0⟩ ⟨F.S.tp, 0, F.S.hp⟩
        ⟨0, F.S.sp, F.S.kp⟩ i := by
    intro i
    rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [c, hex6_0, hex6_1, hex6_2, hex6_3, hex6_4, hex6_5, F.ptC_4, F.ptC_2, F.ptC_6, F.ptC_3,
        F.ptC_0, F.ptC_1]
  have hsp : F.S.sp = 1 - F.S.sm := by linarith
  have hz : IsRobustUnimodal (k := 6) fun i : ZMod 6 =>
      F.toFrame7.GG (F.toFrame7.ptC (c i)) ⟨0, F.S.sm, -F.S.km⟩ := by
    have hz0 : 0 < F.S.sm * F.S.am := mul_pos F.S.sm_pos F.S.am_pos
    have e : (fun i : ZMod 6 => F.toFrame7.GG (F.toFrame7.ptC (c i)) ⟨0, F.S.sm, -F.S.km⟩) =
        fun i : ZMod 6 => hex6 (lam * ((F.S.ap + F.S.am) * F.S.tp * F.S.sm))
          (lam * ((F.S.ap + F.S.am) * F.S.tp * F.S.sm)) (lam * (F.S.am * F.S.tm))
          (lam * (F.S.am * F.S.sm)) (lam * (F.S.tp * (F.S.am * F.S.sm - F.S.ap * F.S.sp))) 0 i := by
      funext i
      rw [hc']
      rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [hex6_0, hex6_1, hex6_2, hex6_3, hex6_4, hex6_5, hdep] <;>
        (try simp only [hhp, hhm, hkp, hkm, hsp]) <;> ring
    rw [e]
    refine robust_cycW2 (mul_pos hl (by rw [mul_comm]; exact hz0)) ?_ ?_ ?_
    · have : F.S.tp * (F.S.am * F.S.sm - F.S.ap * F.S.sp) < F.S.am * F.S.sm := by
        nlinarith [F.S.tp_lt, mul_pos F.S.sp_pos F.S.ap_pos, mul_pos hz0 F.S.tp_pos,
          mul_pos F.S.tp_pos (mul_pos F.S.sp_pos F.S.ap_pos)]
      exact mul_lt_mul_of_pos_left this hl
    · have : F.S.am * F.S.sm < F.S.am * F.S.tm := mul_lt_mul_of_pos_left hsm F.S.am_pos
      exact mul_lt_mul_of_pos_left this hl
    · exact mul_lt_mul_of_pos_left hΔ hl
  refine F.toFrame7.rupert_rim_rob (k := 6) (by norm_num) c (-1) (Or.inr rfl)
    ⟨0, F.S.sm, -F.S.km⟩ ⟨d1, 0, d3⟩ (Or.inr (Or.inl F.S.sm_pos.ne')) ?_ ?_ hz
  · intro i j h1 h2
    simp only [hc']
    exact rimW2_cyc F.S.tm F.S.hm F.S.tp F.S.hp F.S.sp F.S.kp F.S.sm F.S.km F.S.ap F.S.am d1 d3
      F.S.tm_pos F.S.tp_pos F.S.tp_lt F.S.tm_lt F.S.sm_pos F.S.sm_lt F.S.ap_pos F.S.am_pos hs
      hhp hhm hkp hkm hr1 hd1 hd3 i j h1 h2
  · intro j' hj' i
    simp only [hc']
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl (hj' 4)
    · exact absurd rfl (hj' 5)
    · exact absurd rfl (hj' 1)
    · exact absurd rfl (hj' 3)
    · exact absurd rfl (hj' 0)
    · rw [F.ptC_5]
      exact rimW2_rest F.S.tm F.S.hm F.S.tp F.S.hp F.S.sp F.S.kp F.S.sm F.S.km F.S.ap F.S.am d1 d3
        F.S.tm_pos F.S.tp_pos F.S.tp_lt F.S.tm_lt F.S.sm_pos F.S.sm_lt F.S.ap_pos F.S.am_pos hs
        hhp hhm hkp hkm hr1 hd1 hd3 i
    · exact absurd rfl (hj' 2)

/-- **Theorem W.**  On `Q` off `E_W`, Rupert (PROOFS 37.2).  Case `M1- < Δ`: sector `W2` (tilt
`(1, 0, 0)`).  Case `M1- ≥ Δ`: then `M1+ ≥ 0`, and `M1+ > 0` off `E_W`: sector `W1` (tilt
`(-1, 0, a- + 1)`). -/
theorem thmW (hQ : F.QW) :
    IsRupert (Finset.univ.image x) ∨
      (F.S.am * F.S.sm = F.S.ap * F.S.sp ∧ F.S.tp * F.S.sm = F.S.tm * F.S.sp) := by
  obtain ⟨hhp, hhm, hkp, hkm, hr1, hr2, hc⟩ := F.w_shape hQ
  have hs : F.S.sp + F.S.sm = 1 := hQ.2.2
  have hsp : F.S.sp = 1 - F.S.sm := by linarith
  have ham := F.S.am_pos
  have hap := F.S.ap_pos
  have htm := F.S.tm_pos
  have htp := F.S.tp_pos
  have hsm := F.S.sm_pos
  have hsp0 := F.S.sp_pos
  by_cases hΔ : F.S.am * F.S.tm < (F.S.ap + F.S.am) * F.S.tp * F.S.sm
  · left
    have hsmt : F.S.sm < F.S.tm := by
      have h1 : F.S.am * F.S.sm < (F.S.ap + F.S.am) * F.S.tp * F.S.sm := by
        nlinarith [mul_pos hsm (sub_pos.2 hr1)]
      have h2 : F.S.sm * ((F.S.ap + F.S.am) * F.S.tp) * (1 - F.S.tm) < F.S.am * F.S.tm * (1 - F.S.sm) := hr2
      by_contra hh
      push Not at hh
      nlinarith [mul_pos (sub_pos.2 h1) (sub_pos.2 F.S.tm_lt), mul_nonneg (sub_nonneg.2 hh) ham.le]
    exact F.rimW2_rupert hQ 1 0 one_pos (by simpa using ham) hΔ hsmt
  · push Not at hΔ
    have hA : 0 < F.S.ap + F.S.am := add_pos hap ham
    have hch : (F.S.ap + F.S.am) * (F.S.tm * F.S.sp) ≤ (F.S.ap + F.S.am) * (F.S.tp * F.S.sm) :=
      mul_le_mul_of_nonneg_left hc hA.le
    have hge : (F.S.ap + F.S.am) * F.S.sp ≤ F.S.am := by
      refine le_of_mul_le_mul_right ?_ htm
      nlinarith
    by_cases hpos : 0 < F.S.am * F.S.sm - F.S.ap * F.S.sp
    · left
      exact F.rimW1_rupert hQ (-1) (F.S.am + 1) (by norm_num) (by linarith) hΔ hpos
    · right
      push Not at hpos
      have hsmE : F.S.am * F.S.sm = F.S.am - F.S.am * F.S.sp := by rw [hsp]; ring
      have heq : F.S.am * F.S.sm = F.S.ap * F.S.sp := by
        apply le_antisymm (by linarith)
        nlinarith
      refine ⟨heq, ?_⟩
      have ham' : F.S.am = (F.S.ap + F.S.am) * F.S.sp := by nlinarith
      have h1 : (F.S.ap + F.S.am) * (F.S.tp * F.S.sm) = (F.S.ap + F.S.am) * (F.S.tm * F.S.sp) := by
        apply le_antisymm _ hch
        have : (F.S.ap + F.S.am) * F.S.tp * F.S.sm ≤ (F.S.ap + F.S.am) * F.S.sp * F.S.tm := by
          rw [← ham']; exact hΔ
        nlinarith
      exact mul_left_cancel₀ hA.ne' h1

/-! ### Group E-C: Theorem C, the corners (PROOFS 37.3)

Stated in the form of the fifth disjunct (`a+ = b- = c+`, `A12 = A22`, `g a+ d+ = A12`), the
paper's Z-image: view `u1 = m1+ - xb` of Group E-A, sector `Q_H`, rim `(v, [m2-], m1-, xa, m1+,
m2+)`; `m2-` is a corner iff `c- > A1 t+`, strictly inside iff `<`, on the side iff `=`
(choose the tilt, both rims robust).  The fourth disjunct is `F.zFrame`. -/

/-- The corner relations `a+ = b- = c+` (`= a`): `hp = a t+`, `hm = a (1 - t-)`, `kp = a s+`,
the roofs `s+ < t+`, `k- < a (1 - s-)`. -/
theorem c_rel (hab : F.S.ap = F.S.bm) (hac : F.S.ap = F.S.cp) :
    F.S.hp = F.S.ap * F.S.tp ∧ F.S.hm = F.S.ap * (1 - F.S.tm) ∧ F.S.kp = F.S.ap * F.S.sp ∧
      F.S.sp < F.S.tp ∧ F.S.km < F.S.ap * (1 - F.S.sm) := by
  have hhp : F.S.hp = F.S.ap * F.S.tp := F.S.ap_mul.symm
  have hhm : F.S.hm = F.S.ap * (1 - F.S.tm) := by rw [hab]; exact F.S.bm_mul.symm
  have hkp : F.S.kp = F.S.ap * F.S.sp := by rw [hac]; exact F.S.cp_mul.symm
  refine ⟨hhp, hhm, hkp, ?_, ?_⟩
  · have := F.S.roof_p_poly
    rw [hkp, hhp] at this
    exact lt_of_not_ge fun h => by nlinarith [mul_nonneg F.S.ap_pos.le (sub_nonneg.2 h)]
  · have := F.S.roof_m_poly
    rw [hhm] at this
    have a3 := sub_pos.2 F.S.tm_lt
    refine lt_of_mul_lt_mul_right (a := 1 - F.S.tm) ?_ a3.le
    nlinarith

/-- Rim `(v, m2-, m1-, xa, m1+, m2+) = (5,2,6,3,0,1)` at `u1` with tilt `(0, 0, -1)` for the corner
relations, `c- ≥ A1 t+` (`m2-` a corner or on the side), robust depths. -/
theorem rimC6_rupert (hab : F.S.ap = F.S.bm) (hac : F.S.ap = F.S.cp)
    (hcge : F.S.A1 * F.S.tp ≤ F.S.cm)
    (hz : IsRobustUnimodal (k := 6) fun i : ZMod 6 =>
      ![0, -F.S.sm * (F.a22 - F.a12 * F.S.tp) - F.gg * F.S.hp * F.S.km,
        F.S.tm * (F.a11 * F.S.tp - F.a12) - F.gg * F.S.hp * F.S.hm,
        F.a11 * F.S.tp - F.a12, F.S.tp * (F.a11 * F.S.tp - F.a12) + F.gg * F.S.hp ^ 2,
        -F.S.sp * (F.a22 - F.a12 * F.S.tp) + F.gg * F.S.hp * F.S.kp] i) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨hhp, hhm, hkp, hroof, hr2⟩ := F.c_rel hab hac
  have hc : F.S.sm * F.S.ap * F.S.tp ≤ F.S.tm * F.S.km := by
    have h1 := mul_le_mul_of_nonneg_left hcge (mul_pos F.S.sm_pos F.S.tm_pos).le
    have e1 : F.S.sm * F.S.tm * (F.S.A1 * F.S.tp) = F.S.sm * F.S.ap * F.S.tp := by
      have : F.S.A1 = F.S.ap + F.S.am := rfl
      rw [this]
      linear_combination (F.S.sm * F.S.tp) * F.S.am_mul + (F.S.sm * F.S.tp) * hhm
    have e2 : F.S.sm * F.S.tm * F.S.cm = F.S.tm * F.S.km := by rw [← F.S.cm_mul]; ring
    linarith
  let c : ZMod 6 → Fin 7 := ![5, 2, 6, 3, 0, 1]
  have hc6 : ∀ i, F.toFrame7.ptC (c i) =
      hex6 (⟨0, 0, 0⟩ : C3) ⟨0, F.S.sm, -F.S.km⟩ ⟨F.S.tm, 0, -F.S.hm⟩ ⟨1, 0, 0⟩ ⟨F.S.tp, 0, F.S.hp⟩
        ⟨0, F.S.sp, F.S.kp⟩ i := by
    intro i
    rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [c, hex6_0, hex6_1, hex6_2, hex6_3, hex6_4, hex6_5, F.ptC_5, F.ptC_2, F.ptC_6, F.ptC_3,
        F.ptC_0, F.ptC_1]
  refine F.toFrame7.rupert_rim_rob (k := 6) (by norm_num) c 1 (Or.inl rfl)
    ⟨F.S.tp, -1, F.S.hp⟩ ⟨0, 0, -1⟩ (Or.inr (Or.inl (by norm_num))) ?_ ?_ ?_
  · intro i j h1 h2
    simp only [hc6]
    exact rimC6_cyc F.S.tm F.S.hm F.S.tp F.S.hp F.S.sp F.S.kp F.S.sm F.S.km F.S.ap
      F.S.tm_pos F.S.tp_pos F.S.tp_lt F.S.tm_lt F.S.sp_pos F.S.sp_lt F.S.sm_pos F.S.sm_lt
      F.S.ap_pos F.S.km_pos hhp hhm hkp hroof hr2 hc i j h1 h2
  · intro j' hj' i
    simp only [hc6]
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl (hj' 4)
    · exact absurd rfl (hj' 5)
    · exact absurd rfl (hj' 1)
    · exact absurd rfl (hj' 3)
    · rw [F.ptC_4]
      exact rimC6_rest F.S.tm F.S.hm F.S.tp F.S.hp F.S.sp F.S.kp F.S.sm F.S.km F.S.ap
        F.S.tm_pos F.S.tp_pos F.S.tp_lt F.S.tm_lt F.S.sp_pos F.S.sp_lt F.S.sm_pos F.S.sm_lt
        F.S.ap_pos F.S.km_pos hhp hhm hkp hroof hr2 hc i
    · exact absurd rfl (hj' 0)
    · exact absurd rfl (hj' 2)
  · have : (fun i : ZMod 6 => F.toFrame7.GG (F.toFrame7.ptC (c i)) ⟨F.S.tp, -1, F.S.hp⟩) =
        fun i : ZMod 6 =>
      ![0, -F.S.sm * (F.a22 - F.a12 * F.S.tp) - F.gg * F.S.hp * F.S.km,
        F.S.tm * (F.a11 * F.S.tp - F.a12) - F.gg * F.S.hp * F.S.hm,
        F.a11 * F.S.tp - F.a12, F.S.tp * (F.a11 * F.S.tp - F.a12) + F.gg * F.S.hp ^ 2,
        -F.S.sp * (F.a22 - F.a12 * F.S.tp) + F.gg * F.S.hp * F.S.kp] i := by
      funext i
      rw [hc6]
      rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [hex6_0, hex6_1, hex6_2, hex6_3, hex6_4, hex6_5, F.GGc_u1] <;> simp <;> ring
    rw [this]; exact hz

theorem thmC (hα : F.a12 < F.a11) (hab : F.S.ap = F.S.bm) (hac : F.S.ap = F.S.cp)
    (h22 : F.a12 = F.a22) (hg : F.gg * F.S.ap * F.S.dp = F.a12) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨hhp, hhm, hkp, hroof, hr2⟩ := F.c_rel hab hac
  have hgg := F.g_pos
  have hp0 : 0 < F.a12 := F.A12_pos
  have hdp := F.S.dp_mul
  have hgs : F.gg * F.S.ap ^ 2 * F.S.sp = F.a12 * (1 - F.S.sp) := by
    linear_combination (1 - F.S.sp) * hg - (F.gg * F.S.ap) * hdp - (F.gg * F.S.ap) * hkp
  have hsp := F.S.sp_pos
  have htp := F.S.tp_pos
  have hd := sub_pos.2 hroof
  have hα' := sub_pos.2 hα
  have E1 : -F.S.sp * (F.a22 - F.a12 * F.S.tp) + F.gg * F.S.hp * F.S.kp =
      F.a12 * (F.S.tp - F.S.sp) := by
    rw [hhp, hkp, ← h22]; linear_combination F.S.tp * hgs
  have E2 : F.S.sp * ((F.a11 * F.S.tp - F.a12) -
      (F.S.tm * (F.a11 * F.S.tp - F.a12) - F.gg * F.S.hp * F.S.hm)) =
      (1 - F.S.tm) * (F.S.sp * F.S.tp * (F.a11 - F.a12) + F.a12 * (F.S.tp - F.S.sp)) := by
    rw [hhp, hhm]; linear_combination (F.S.tp * (1 - F.S.tm)) * hgs
  have E3 : F.S.sp * ((F.S.tp * (F.a11 * F.S.tp - F.a12) + F.gg * F.S.hp ^ 2) -
      (-F.S.sp * (F.a22 - F.a12 * F.S.tp) + F.gg * F.S.hp * F.S.kp)) =
      F.S.sp * F.S.tp ^ 2 * (F.a11 - F.a12) + F.a12 * (F.S.tp - F.S.sp) ^ 2 := by
    rw [hhp, hkp, ← h22]; linear_combination (F.S.tp ^ 2 - F.S.sp * F.S.tp) * hgs
  have h4 : 0 < -F.S.sp * (F.a22 - F.a12 * F.S.tp) + F.gg * F.S.hp * F.S.kp := by
    rw [E1]; exact mul_pos hp0 hd
  have h2 : F.S.tm * (F.a11 * F.S.tp - F.a12) - F.gg * F.S.hp * F.S.hm <
      F.a11 * F.S.tp - F.a12 := by
    have : 0 < F.S.sp * ((F.a11 * F.S.tp - F.a12) -
        (F.S.tm * (F.a11 * F.S.tp - F.a12) - F.gg * F.S.hp * F.S.hm)) := by
      rw [E2]
      exact mul_pos (sub_pos.2 F.S.tm_lt)
        (add_pos (mul_pos (mul_pos hsp htp) hα') (mul_pos hp0 hd))
    have := pos_of_mul_pos_right this hsp.le
    linarith
  have h5 : -F.S.sp * (F.a22 - F.a12 * F.S.tp) + F.gg * F.S.hp * F.S.kp <
      F.S.tp * (F.a11 * F.S.tp - F.a12) + F.gg * F.S.hp ^ 2 := by
    have : 0 < F.S.sp * ((F.S.tp * (F.a11 * F.S.tp - F.a12) + F.gg * F.S.hp ^ 2) -
        (-F.S.sp * (F.a22 - F.a12 * F.S.tp) + F.gg * F.S.hp * F.S.kp)) := by
      rw [E3]
      exact add_pos (mul_pos (mul_pos hsp (pow_pos htp 2)) hα') (mul_pos hp0 (pow_pos hd 2))
    have := pos_of_mul_pos_right this hsp.le
    linarith
  by_cases hc : F.S.cm < F.S.A1 * F.S.tp
  · refine F.rimH_rupert 0 (-1) (by nlinarith [F.S.tp_lt]) ?_ hc (robust_cycC5 h2 h4 h5)
    nlinarith [mul_pos htp (sub_pos.2 F.S.sp_lt)]
  · push Not at hc
    have hb : -F.S.sm * (F.a22 - F.a12 * F.S.tp) - F.gg * F.S.hp * F.S.km < 0 := by
      have h22' : F.a22 - F.a12 * F.S.tp = F.a12 * (1 - F.S.tp) := by rw [← h22]; ring
      rw [h22']
      linarith [mul_pos F.S.sm_pos (mul_pos hp0 (sub_pos.2 F.S.tp_lt)),
        mul_pos (mul_pos hgg F.S.hp_pos) F.S.km_pos]
    exact F.rimC6_rupert hab hac hc (robust_cycC6 hb h2 h4 h5)

theorem thmCz (hab : F.S.am = F.S.bp) (hac : F.S.am = F.S.cm)
    (h22 : F.a12 = F.a22) (hg : F.gg * F.S.am * F.S.dm = F.a12) :
    IsRupert (Finset.univ.image x) :=
  have hg' : F.zFrame.gg * F.zFrame.S.ap * F.zFrame.S.dp = F.zFrame.a12 := by
    rw [F.zFrame_gg, F.zFrame_a12]; exact hg
  rupert_of_z (F.zFrame.thmC (F.a12_lt_a11_of_eq_a22 h22) hab hac h22 hg')

/-! ### Group E-R: the R1' residual, Theorems R' and F (PROOFS 37.4) -/

/-- Rim (B) `(v, m2-, xb, m1+)` at `u0` with `am = bp` (`xa` is a double of `m1+`, `m2+` strictly
inside), tilt `(q, P, 0)`. -/
theorem rimBe_rupert (hab : F.S.am = F.S.bp) (P q : ℝ) (hP : P < 0)
    (hV1 : F.S.sm * F.S.hm * q + F.S.tm * F.S.km * P < 0) (hQ : 0 < q + P)
    (hQe : ∀ᶠ s in 𝓝[>] (0 : ℝ), Q4 fun i => F.toFrame7.GG
        (quad (⟨0, 0, 0⟩ : C3) ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨F.S.tp, 0, F.S.hp⟩ i) ⟨F.S.tm, 0, -F.S.hm⟩ +
      s * F.toFrame7.GG (quad (⟨0, 0, 0⟩ : C3) ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨F.S.tp, 0, F.S.hp⟩ i) ⟨q, P, 0⟩) :
    IsRupert (Finset.univ.image x) := by
  have hE := F.S.hE_of_eq hab
  have hV := F.S.hVs_of_eq hab
  refine F.toFrame7.rupert_rim4 5 2 4 0 ⟨0, 0, 0⟩ ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨F.S.tp, 0, F.S.hp⟩
    F.ptC_5 F.ptC_2 F.ptC_4 F.ptC_0 1 (Or.inl rfl) ⟨F.S.tm, 0, -F.S.hm⟩ ⟨q, P, 0⟩
    (Or.inl F.S.tm_pos.ne') (rimB_cyc F.S P q hP hV1) ?_ hQe
  intro j' h0 h1 h2 h3 i
  rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl h3
  · rw [F.ptC_1]; exact rimBe_rest F.S P q hP hV1 hQ hE hV _ (Or.inl rfl) i
  · exact absurd rfl h1
  · rw [F.ptC_3]; exact rimBe_rest F.S P q hP hV1 hQ hE hV _ (Or.inr (Or.inl rfl)) i
  · exact absurd rfl h2
  · exact absurd rfl h0
  · rw [F.ptC_6]; exact rimBe_rest F.S P q hP hV1 hQ hE hV _ (Or.inr (Or.inr rfl)) i

/-- **Theorem R'** (`A12 = A11`, `a- = b+`): Rupert unless `g a- d- = A11` and `c- <= a-`.
View `u0 = m1-`; sectors (B') for `zeta- < 0`, (C) for `zeta- > 0` (both with `X = T`: the
depth patterns `![0,Z2,T,T,Z1]`, `![R,Z2,T,Z1,T]`), and (B) `(v,m2-,xb,m1+)` for `zeta- = 0`,
`a- < c-`. -/
theorem thmRp (heq : F.a12 = F.a11) (hb : F.S.am = F.S.bp) :
    IsRupert (Finset.univ.image x) ∨
      (F.gg * F.S.am * F.S.dm = F.a11 ∧ F.S.cm ≤ F.S.am) := by
  have htm := F.S.tm_pos; have hhm := F.S.hm_pos; have hkm := F.S.km_pos; have hsm := F.S.sm_pos
  have hs : 0 < (1 - F.S.sm) * F.S.tm := mul_pos (sub_pos.2 F.S.sm_lt) htm
  have e1 := F.u0Z2_sub_X
  have hXT := F.u0X_eq_T heq
  rcases lt_trichotomy (F.gg * F.S.am * F.S.dm) F.a11 with hZ | hZ | hZ
  · left
    have hZ' : F.gg * F.S.am * F.S.dm < F.a12 := by rw [heq]; exact hZ
    refine F.rimBp_rupert hb (-1) (-1) (by norm_num)
      (by nlinarith [mul_pos hsm hhm, mul_pos htm hkm]) (by norm_num) ?_
    rw [hXT]
    exact robust_cycS2 F.u0Z2_pos (by rw [← hXT]; nlinarith [mul_pos hs (sub_pos.2 hZ')])
      F.u0Z1_lt_T
  · by_cases hc : F.S.cm ≤ F.S.am
    · exact Or.inr ⟨hZ, hc⟩
    · left
      push Not at hc
      have hcm := F.S.cm_mul
      have ham := F.S.am_mul
      have hamp := F.S.am_pos
      set q : ℝ := (F.S.am + F.S.cm) / (2 * F.S.am) with hq
      have hq1 : F.S.am * q = (F.S.am + F.S.cm) / 2 := by rw [hq]; field_simp
      have hq2 : 1 < q := by
        refine lt_of_mul_lt_mul_left (a := F.S.am) ?_ hamp.le
        linarith
      have hV1 : F.S.sm * F.S.hm * q + F.S.tm * F.S.km * (-1) < 0 := by
        have : F.S.sm * F.S.hm * q + F.S.tm * F.S.km * (-1) =
            F.S.sm * F.S.tm * ((F.S.am + F.S.cm) / 2 - F.S.cm) := by
          rw [← ham, ← hcm]; linear_combination (F.S.sm * F.S.tm) * hq1
        rw [this]
        nlinarith [mul_pos hsm htm]
      refine F.rimBe_rupert hb (-1) q (by norm_num) hV1 (by linarith) ?_
      obtain ⟨gR, gT, gX, gZ1, gZ2, gZp, g0⟩ := F.GGc_u0
      refine Q4_eventually (z := fun i => F.toFrame7.GG
          (quad (⟨0, 0, 0⟩ : C3) ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨F.S.tp, 0, F.S.hp⟩ i) ⟨F.S.tm, 0, -F.S.hm⟩)
        (w := fun i => F.toFrame7.GG
          (quad (⟨0, 0, 0⟩ : C3) ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨F.S.tp, 0, F.S.hp⟩ i) ⟨q, -1, 0⟩)
        (Or.inl (Or.inl ?_)) (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
      · simp only [quad_0, quad_1, g0, gZ2]; exact F.u0Z2_pos
      · simp only [quad_2, quad_3, gZ1, gX]; rw [hXT]; exact F.u0Z1_lt_T
  · left
    have hZ' : F.a12 < F.gg * F.S.am * F.S.dm := by rw [heq]; exact hZ
    have hT : F.u0T ≤ F.u0Z2 := by
      rw [← hXT]; nlinarith [mul_pos hs (sub_pos.2 hZ')]
    have hTZ : F.u0T < F.u0Z2 := by
      rw [← hXT]; nlinarith [mul_pos hs (sub_pos.2 hZ')]
    refine F.rimCe_rupert hb 1 1 one_pos (by nlinarith [mul_pos hsm hhm, mul_pos htm hkm])
      (by norm_num) ?_
    rw [hXT]
    exact robust_cycCT F.u0Z1_lt_T (F.u0_R_gt_T_of_ge heq hT) hTZ


/-- `g = gg / a11` (the normalisation `A11 = 1`). -/
noncomputable def fG : ℝ := F.gg / F.a11
/-- `μ = g h+ b+ - t+`. -/
noncomputable def fMu : ℝ := F.fG * F.S.hp * F.S.bp - F.S.tp
/-- `ρ = β / D`, `β = a22/a11 - 1`, `D = μ + 1`. -/
noncomputable def fRho : ℝ := (F.a22 / F.a11 - 1) / (F.fMu + 1)

theorem fData (heq : F.a12 = F.a11) (h22 : F.a11 < F.a22)
    (hg : F.gg * F.S.ap * F.S.dp = F.a11) :
    0 < F.a11 ∧ 0 < F.fG ∧ 0 < F.fMu ∧ 0 < F.fRho ∧ F.S.hp = F.S.bp * (1 - F.S.tp) ∧
    F.fG * F.S.ap * F.S.dp = 1 ∧
    (∀ p : C3, F.toFrame7.GG p (uF F.fRho F.S.bp) =
      F.a11 * F.fRho * (-p.x + F.fMu * p.y + F.fG * F.S.bp * p.z)) := by
  have hA11 : 0 < F.a11 := lt_of_lt_of_le F.A12_pos F.A12_le_A11
  have hG : 0 < F.fG := div_pos F.g_pos hA11
  have hG1 : F.fG * F.S.ap * F.S.dp = 1 := by
    unfold fG; field_simp; linarith
  have hhp : F.S.hp = F.S.bp * (1 - F.S.tp) := F.S.bp_mul.symm
  have hmu : F.fMu = F.S.tp * (F.fG * F.S.ap * F.S.bp - 1) := by
    unfold fMu; rw [← F.S.ap_mul]; ring
  have hroof := F.S.dp_lt_bp
  have hmu0 : 0 < F.fMu := by
    rw [hmu]
    refine mul_pos F.S.tp_pos ?_
    have : F.fG * F.S.ap * F.S.dp < F.fG * F.S.ap * F.S.bp :=
      mul_lt_mul_of_pos_left hroof (mul_pos hG F.S.ap_pos)
    linarith
  have hD : 0 < F.fMu + 1 := by linarith
  have hρ : 0 < F.fRho := by
    unfold fRho
    refine div_pos ?_ hD
    have : 1 < F.a22 / F.a11 := by rw [lt_div_iff₀ hA11]; linarith
    linarith
  refine ⟨hA11, hG, hmu0, hρ, hhp, hG1, fun p => ?_⟩
  have hr : F.fRho * (F.fMu + 1) = F.a22 / F.a11 - 1 := by
    unfold fRho; field_simp
  have h22' : F.a22 = F.a11 * (1 + F.fRho * (F.fMu + 1)) := by
    rw [hr]; field_simp; ring
  have hgg : F.gg = F.fG * F.a11 := by unfold fG; field_simp
  rw [F.GG_eq, heq, uF]
  simp only
  rw [h22', hgg]
  ring



/-- Screen orientation numbers of the F view (all `crF` of screen differences, `hp` eliminated):
`oN1 = O(v, m1-, m2-)`, `oN2 = O(m1-, xb, m2-)`, `oW = O(m1+, v, m2+)`. -/
noncomputable def oN1 : ℝ := -(F.S.tm * F.S.km) - F.S.tm * F.S.sm * (F.fRho * F.S.bp) +
  F.S.hm * F.S.sm * (1 + F.fRho)
noncomputable def oN2 : ℝ := (1 + F.fRho - F.S.tm) * (-F.S.km - F.S.sm * (F.fRho * F.S.bp) + F.S.hm) -
  (-(F.fRho * F.S.bp) + F.S.hm) * (F.S.sm * (1 + F.fRho) - F.S.tm)
noncomputable def oW : ℝ := F.S.bp * (1 - F.S.tp) * F.S.sp * (1 + F.fRho) - F.S.tp * F.S.kp +
  F.S.tp * F.S.sp * (F.fRho * F.S.bp)

theorem rimFA_rupert (heq : F.a12 = F.a11) (h22 : F.a11 < F.a22)
    (hg : F.gg * F.S.ap * F.S.dp = F.a11) (hb : F.S.bp ≤ F.S.am)
    (HN1 : 0 < F.oN1) (HN2 : 0 < F.oN2) (HW : 0 < F.oW) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨hA11, hG, hmu, hρ, hhp, -, hdep⟩ := F.fData heq h22 hg
  have hbm : F.S.bp * F.S.tm ≤ F.S.hm := by
    rw [← F.S.am_mul]; exact mul_le_mul_of_nonneg_right hb F.S.tm_pos.le
  have hroof : F.S.kp < F.S.bp * (1 - F.S.sp) := by
    have h1 := F.S.dp_lt_bp
    have h2 := F.S.dp_mul
    have : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
    nlinarith
  have hcc : ∀ i, F.toFrame7.ptC (quad (5 : Fin 7) 6 4 0 i) =
      quad (⟨0, 0, 0⟩ : C3) ⟨F.S.tm, 0, -F.S.hm⟩ ⟨0, 1, 0⟩ ⟨F.S.tp, 0, F.S.bp * (1 - F.S.tp)⟩ i := by
    intro i
    rw [← hhp]
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp [quad_0, quad_1, quad_2, quad_3, F.ptC_5, F.ptC_6, F.ptC_4, F.ptC_0]
  refine F.toFrame7.rupert_rim_rob (k := 4) (by norm_num) (quad (5 : Fin 7) 6 4 0) (-1) (Or.inr rfl)
    (uF F.fRho F.S.bp) ⟨0, 0, -1⟩ (Or.inr (Or.inl (by simp [uF]))) ?_ ?_ ?_
  · intro i j h1 h2
    simp only [hcc]
    exact rimA_cyc F.S.tp F.S.tm F.S.hm F.S.sp F.S.kp F.S.sm F.S.km F.fRho F.S.bp _ F.S.tp_pos
      F.S.tp_lt F.S.tm_pos F.S.tm_lt F.S.bp_pos hρ F.S.hm_pos hbm i j h1 h2
  · intro j' hj' i
    simp only [hcc]
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (by simp [quad_3]) (hj' 3)
    · rw [F.ptC_1]
      exact rimA_restW F.S.tp F.S.tm F.S.hm F.S.sp F.S.kp F.fRho F.S.bp _ F.S.tp_pos F.S.tp_lt
        F.S.tm_pos F.S.tm_lt F.S.bp_pos hρ F.S.hm_pos hbm F.S.sp_pos F.S.sp_lt F.S.kp_pos hroof HW i
    · rw [F.ptC_2]
      exact rimA_restN F.S.tp F.S.tm F.S.hm F.S.sm F.S.km F.fRho F.S.bp _ F.S.tp_pos F.S.tp_lt
        F.S.tm_pos F.S.tm_lt F.S.bp_pos hρ F.S.hm_pos hbm F.S.sm_pos F.S.sm_lt F.S.km_pos HN1 HN2 i
    · rw [F.ptC_3]
      exact rimA_restA F.S.tp F.S.tm F.S.hm F.fRho F.S.bp F.S.tp_pos F.S.tp_lt F.S.tm_pos
        F.S.tm_lt F.S.bp_pos hρ F.S.hm_pos i
    · exact absurd (by simp [quad_2]) (hj' 2)
    · exact absurd (by simp [quad_0]) (hj' 0)
    · exact absurd (by simp [quad_1]) (hj' 1)
  · have e : (fun i : ZMod 4 => F.toFrame7.GG (F.toFrame7.ptC (quad (5 : Fin 7) 6 4 0 i)) (uF F.fRho F.S.bp)) =
        fun i : ZMod 4 => F.a11 * F.fRho * quad (0 : ℝ)
          (-F.S.tm - F.fG * F.S.bp * F.S.hm) F.fMu F.fMu i := by
      funext i
      rw [hdep, hcc]
      have hU : F.fMu = F.fG * (F.S.bp * (1 - F.S.tp)) * F.S.bp - F.S.tp := by
        unfold fMu; rw [← hhp]
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3] <;> (try rw [hU]) <;> ring
    rw [e]
    refine robust_smul_pos (robust_quad_of_nws ?_ ?_) (mul_pos hA11 hρ)
    · exact Or.inr (Or.inl hmu)
    · left
      have := mul_pos hG (mul_pos F.S.bp_pos F.S.hm_pos)
      nlinarith [F.S.tm_pos]

theorem fPar (heq : F.a12 = F.a11) (h22 : F.a11 < F.a22)
    (hg : F.gg * F.S.ap * F.S.dp = F.a11) (hb : F.S.bp ≤ F.S.am) {lam : ℝ} (hl : 0 < lam)
    (hlW : lam * F.S.tp * F.S.sp < F.S.bp * (1 - F.S.tp) * F.S.sp + F.S.tp * F.S.kp) :
    FPar F.S.tp F.S.tm F.S.hm F.S.sp F.S.kp F.S.sm F.S.km F.fRho F.S.bp lam := by
  obtain ⟨hA11, hG, hmu, hρ, hhp, -, hdep⟩ := F.fData heq h22 hg
  have hbm : F.S.bp * F.S.tm ≤ F.S.hm := by
    rw [← F.S.am_mul]; exact mul_le_mul_of_nonneg_right hb F.S.tm_pos.le
  have hroof : F.S.kp < F.S.bp * (1 - F.S.sp) := by
    have h1 := F.S.dp_lt_bp
    have h2 := F.S.dp_mul
    have : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
    nlinarith
  exact ⟨F.S.tp_pos, F.S.tp_lt, F.S.tm_pos, F.S.tm_lt, F.S.bp_pos, hρ, F.S.hm_pos, hbm, F.S.sp_pos,
    F.S.sp_lt, F.S.kp_pos, hroof, F.S.sm_pos, F.S.sm_lt, F.S.km_pos, F.S.roof_m_poly, hl, hlW⟩

theorem rimFA2_rupert (heq : F.a12 = F.a11) (h22 : F.a11 < F.a22)
    (hg : F.gg * F.S.ap * F.S.dp = F.a11) (hb : F.S.bp ≤ F.S.am) {lam : ℝ} (hl : 0 < lam)
    (hlW : lam * F.S.tp * F.S.sp < F.S.bp * (1 - F.S.tp) * F.S.sp + F.S.tp * F.S.kp)
    (hx : Lx F.fRho F.S.bp lam pV (pM F.S.tm F.S.hm) (pN F.S.sm F.S.km)) (hz : Lx F.fRho F.S.bp lam (pM F.S.tm F.S.hm) pB (pN F.S.sm F.S.km))
    (hw : Lx F.fRho F.S.bp lam (pU F.S.tp F.S.bp) pV (pW F.S.sp F.S.kp)) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨hA11, hG, hmu, hρ, hhp, -, hdep⟩ := F.fData heq h22 hg
  have H := F.fPar heq h22 hg hb hl hlW
  have hcc : ∀ i, F.toFrame7.ptC (quad (5 : Fin 7) 6 4 0 i) =
      quad pV (pM F.S.tm F.S.hm) pB (pU F.S.tp F.S.bp) i := by
    intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp [quad_0, quad_1, quad_2, quad_3, F.ptC_5, F.ptC_6, F.ptC_4, F.ptC_0, pB, pM, pU, pV, hhp]
  refine F.toFrame7.rupert_rim_rob (k := 4) (by norm_num) (quad (5 : Fin 7) 6 4 0) (-1)
    (Or.inr rfl) (uF F.fRho F.S.bp) (dF lam) (Or.inr (Or.inl (by simp [uF]))) ?_ ?_ ?_
  · intro i j h1 h2
    simp only [hcc]
    exact rimFA_cyc H hx hz hw i j h1 h2
  · intro j' hj' i
    simp only [hcc]
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (by simp [quad_3]) (hj' 3)
    · rw [F.ptC_1]
      exact rimFA_restW H hx hz hw i
    · rw [F.ptC_2]
      exact rimFA_restN H hx hz hw i
    · rw [F.ptC_3]
      exact rimFA_restA H hx hz hw i
    · exact absurd (by simp [quad_2]) (hj' 2)
    · exact absurd (by simp [quad_0]) (hj' 0)
    · exact absurd (by simp [quad_1]) (hj' 1)
  · have e : (fun i : ZMod 4 => F.toFrame7.GG (F.toFrame7.ptC (quad (5 : Fin 7) 6 4 0 i)) (uF F.fRho F.S.bp)) =
        fun i : ZMod 4 => F.a11 * F.fRho * quad (0:ℝ) (-F.S.tm - F.fG * F.S.bp * F.S.hm) F.fMu F.fMu i := by
      funext i
      rw [hdep, hcc]
      have hU : F.fMu = F.fG * (F.S.bp * (1 - F.S.tp)) * F.S.bp - F.S.tp := by
        unfold fMu; rw [← hhp]
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3, pV, pM, pB, pU, pN, pW, pA] <;> (try rw [hU]) <;> ring
    rw [e]
    refine robust_smul_pos (robust_quad_of_nws ?_ ?_) (mul_pos hA11 hρ)
    · exact Or.inr (Or.inl hmu)
    · left
      have := mul_pos hG (mul_pos F.S.bp_pos F.S.hm_pos)
      nlinarith [F.S.tm_pos]

theorem rimFB_rupert (heq : F.a12 = F.a11) (h22 : F.a11 < F.a22)
    (hg : F.gg * F.S.ap * F.S.dp = F.a11) (hb : F.S.bp ≤ F.S.am) {lam : ℝ} (hl : 0 < lam)
    (hlW : lam * F.S.tp * F.S.sp < F.S.bp * (1 - F.S.tp) * F.S.sp + F.S.tp * F.S.kp)
    (hx : Ot F.fRho F.S.bp pV (pM F.S.tm F.S.hm) (pN F.S.sm F.S.km) < 0) (hz : Lx F.fRho F.S.bp lam (pN F.S.sm F.S.km) pB (pM F.S.tm F.S.hm))
    (hw : Lx F.fRho F.S.bp lam (pU F.S.tp F.S.bp) pV (pW F.S.sp F.S.kp)) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨hA11, hG, hmu, hρ, hhp, -, hdep⟩ := F.fData heq h22 hg
  have H := F.fPar heq h22 hg hb hl hlW
  have hzN1 : F.fMu * F.S.sm - F.fG * F.S.bp * F.S.km < F.fMu := by
    have := mul_pos hG (mul_pos F.S.bp_pos F.S.km_pos)
    nlinarith [mul_pos hmu (sub_pos.2 F.S.sm_lt)]
  have hcc : ∀ i, F.toFrame7.ptC (quad (5 : Fin 7) 2 4 0 i) =
      quad pV (pN F.S.sm F.S.km) pB (pU F.S.tp F.S.bp) i := by
    intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp [quad_0, quad_1, quad_2, quad_3, F.ptC_5, F.ptC_2, F.ptC_4, F.ptC_0, pB, pN, pU, pV, hhp]
  refine F.toFrame7.rupert_rim_rob (k := 4) (by norm_num) (quad (5 : Fin 7) 2 4 0) (-1)
    (Or.inr rfl) (uF F.fRho F.S.bp) (dF lam) (Or.inr (Or.inl (by simp [uF]))) ?_ ?_ ?_
  · intro i j h1 h2
    simp only [hcc]
    exact rimFB_cyc H hx hz hw i j h1 h2
  · intro j' hj' i
    simp only [hcc]
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (by simp [quad_3]) (hj' 3)
    · rw [F.ptC_1]
      exact rimFB_restW H hx hz hw i
    · exact absurd (by simp [quad_1]) (hj' 1)
    · rw [F.ptC_3]
      exact rimFB_restA H hx hz hw i
    · exact absurd (by simp [quad_2]) (hj' 2)
    · exact absurd (by simp [quad_0]) (hj' 0)
    · rw [F.ptC_6]
      exact rimFB_restM H hx hz hw i
  · have e : (fun i : ZMod 4 => F.toFrame7.GG (F.toFrame7.ptC (quad (5 : Fin 7) 2 4 0 i)) (uF F.fRho F.S.bp)) =
        fun i : ZMod 4 => F.a11 * F.fRho * quad (0:ℝ) (F.fMu * F.S.sm - F.fG * F.S.bp * F.S.km) F.fMu F.fMu i := by
      funext i
      rw [hdep, hcc]
      have hU : F.fMu = F.fG * (F.S.bp * (1 - F.S.tp)) * F.S.bp - F.S.tp := by
        unfold fMu; rw [← hhp]
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3, pV, pM, pB, pU, pN, pW, pA] <;> (try rw [hU]) <;> ring
    rw [e]
    refine robust_smul_pos (robust_quad_of_nws ?_ ?_) (mul_pos hA11 hρ)
    · exact Or.inr (Or.inl hmu)
    · exact Or.inr (Or.inr (Or.inl hzN1))

theorem rimFC_rupert (heq : F.a12 = F.a11) (h22 : F.a11 < F.a22)
    (hg : F.gg * F.S.ap * F.S.dp = F.a11) (hb : F.S.bp ≤ F.S.am) {lam : ℝ} (hl : 0 < lam)
    (hlW : lam * F.S.tp * F.S.sp < F.S.bp * (1 - F.S.tp) * F.S.sp + F.S.tp * F.S.kp)
    (hx : Lx F.fRho F.S.bp lam pV (pM F.S.tm F.S.hm) (pN F.S.sm F.S.km)) (hz : Lx F.fRho F.S.bp lam (pM F.S.tm F.S.hm) (pN F.S.sm F.S.km) pB)
    (hw : Lx F.fRho F.S.bp lam (pU F.S.tp F.S.bp) pV (pW F.S.sp F.S.kp)) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨hA11, hG, hmu, hρ, hhp, -, hdep⟩ := F.fData heq h22 hg
  have H := F.fPar heq h22 hg hb hl hlW
  have hzN1 : F.fMu * F.S.sm - F.fG * F.S.bp * F.S.km < F.fMu := by
    have := mul_pos hG (mul_pos F.S.bp_pos F.S.km_pos)
    nlinarith [mul_pos hmu (sub_pos.2 F.S.sm_lt)]
  have hcc : ∀ i, F.toFrame7.ptC (quint (5 : Fin 7) 6 2 4 0 i) =
      quint pV (pM F.S.tm F.S.hm) (pN F.S.sm F.S.km) pB (pU F.S.tp F.S.bp) i := by
    intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [quint_0, quint_1, quint_2, quint_3, quint_4, F.ptC_5, F.ptC_6, F.ptC_2, F.ptC_4, F.ptC_0, pB, pM, pN, pU, pV, hhp]
  refine F.toFrame7.rupert_rim_rob (k := 5) (by norm_num) (quint (5 : Fin 7) 6 2 4 0) (-1)
    (Or.inr rfl) (uF F.fRho F.S.bp) (dF lam) (Or.inr (Or.inl (by simp [uF]))) ?_ ?_ ?_
  · intro i j h1 h2
    simp only [hcc]
    exact rimFC_cyc H hx hz hw i j h1 h2
  · intro j' hj' i
    simp only [hcc]
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (by simp [quint_4]) (hj' 4)
    · rw [F.ptC_1]
      exact rimFC_restW H hx hz hw i
    · exact absurd (by simp [quint_2]) (hj' 2)
    · rw [F.ptC_3]
      exact rimFC_restA H hx hz hw i
    · exact absurd (by simp [quint_3]) (hj' 3)
    · exact absurd (by simp [quint_0]) (hj' 0)
    · exact absurd (by simp [quint_1]) (hj' 1)
  · have e : (fun i : ZMod 5 => F.toFrame7.GG (F.toFrame7.ptC (quint (5 : Fin 7) 6 2 4 0 i)) (uF F.fRho F.S.bp)) =
        fun i : ZMod 5 => F.a11 * F.fRho * quint (0:ℝ) (-F.S.tm - F.fG * F.S.bp * F.S.hm) (F.fMu * F.S.sm - F.fG * F.S.bp * F.S.km) F.fMu F.fMu i := by
      funext i
      rw [hdep, hcc]
      have hU : F.fMu = F.fG * (F.S.bp * (1 - F.S.tp)) * F.S.bp - F.S.tp := by
        unfold fMu; rw [← hhp]
      rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
        simp only [quint_0, quint_1, quint_2, quint_3, quint_4, pV, pM, pB, pU, pN, pW, pA] <;> (try rw [hU]) <;> ring
    rw [e]
    refine robust_smul_pos (robust_cycF5 ?_ hzN1 hmu) (mul_pos hA11 hρ)
    have := mul_pos hG (mul_pos F.S.bp_pos F.S.hm_pos)
    nlinarith [F.S.tm_pos]

theorem rimFD_rupert (heq : F.a12 = F.a11) (h22 : F.a11 < F.a22)
    (hg : F.gg * F.S.ap * F.S.dp = F.a11) (hb : F.S.bp ≤ F.S.am) {lam : ℝ} (hl : 0 < lam)
    (hlW : lam * F.S.tp * F.S.sp < F.S.bp * (1 - F.S.tp) * F.S.sp + F.S.tp * F.S.kp)
    (hx : Ot F.fRho F.S.bp pV (pM F.S.tm F.S.hm) (pN F.S.sm F.S.km) < 0) (hz : Lx F.fRho F.S.bp lam (pM F.S.tm F.S.hm) pB (pN F.S.sm F.S.km))
    (hw : Lx F.fRho F.S.bp lam (pU F.S.tp F.S.bp) pV (pW F.S.sp F.S.kp)) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨hA11, hG, hmu, hρ, hhp, -, hdep⟩ := F.fData heq h22 hg
  have H := F.fPar heq h22 hg hb hl hlW
  have hzN0 : F.fMu * F.S.sm - F.fG * F.S.bp * F.S.km < 0 := by
    have hk : F.S.bp * F.S.sm < F.S.km := by
      have h1 : F.S.tm * (F.S.bp * F.S.sm) < F.S.tm * F.S.km := by
        simp only [Ot, crF, scF, C3.sub, pV, pM, pN] at hx
        nlinarith [mul_nonneg hρ.le (sub_nonneg.2 H.hbm), mul_pos F.S.sm_pos F.S.hm_pos,
          mul_nonneg F.S.sm_pos.le (sub_nonneg.2 H.hbm), mul_pos hρ F.S.tm_pos]
      exact lt_of_mul_lt_mul_left h1 F.S.tm_pos.le
    have hU : F.fMu = F.fG * (F.S.bp * (1 - F.S.tp)) * F.S.bp - F.S.tp := by
      unfold fMu; rw [← hhp]
    have h2 : F.S.bp * (1 - F.S.tp) * F.S.sm < F.S.km := by
      nlinarith [mul_pos F.S.bp_pos F.S.tp_pos, mul_pos F.S.sm_pos (mul_pos F.S.bp_pos F.S.tp_pos)]
    rw [hU]
    nlinarith [mul_pos hG (mul_pos F.S.bp_pos (sub_pos.2 h2)), mul_pos F.S.tp_pos F.S.sm_pos]
  have hcc : ∀ i, F.toFrame7.ptC (quint (5 : Fin 7) 2 6 4 0 i) =
      quint pV (pN F.S.sm F.S.km) (pM F.S.tm F.S.hm) pB (pU F.S.tp F.S.bp) i := by
    intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [quint_0, quint_1, quint_2, quint_3, quint_4, F.ptC_5, F.ptC_2, F.ptC_6, F.ptC_4, F.ptC_0, pB, pM, pN, pU, pV, hhp]
  refine F.toFrame7.rupert_rim_rob (k := 5) (by norm_num) (quint (5 : Fin 7) 2 6 4 0) (-1)
    (Or.inr rfl) (uF F.fRho F.S.bp) (dF lam) (Or.inr (Or.inl (by simp [uF]))) ?_ ?_ ?_
  · intro i j h1 h2
    simp only [hcc]
    exact rimFD_cyc H hx hz hw i j h1 h2
  · intro j' hj' i
    simp only [hcc]
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (by simp [quint_4]) (hj' 4)
    · rw [F.ptC_1]
      exact rimFD_restW H hx hz hw i
    · exact absurd (by simp [quint_1]) (hj' 1)
    · rw [F.ptC_3]
      exact rimFD_restA H hx hz hw i
    · exact absurd (by simp [quint_3]) (hj' 3)
    · exact absurd (by simp [quint_0]) (hj' 0)
    · exact absurd (by simp [quint_2]) (hj' 2)
  · have e : (fun i : ZMod 5 => F.toFrame7.GG (F.toFrame7.ptC (quint (5 : Fin 7) 2 6 4 0 i)) (uF F.fRho F.S.bp)) =
        fun i : ZMod 5 => F.a11 * F.fRho * quint (0:ℝ) (F.fMu * F.S.sm - F.fG * F.S.bp * F.S.km) (-F.S.tm - F.fG * F.S.bp * F.S.hm) F.fMu F.fMu i := by
      funext i
      rw [hdep, hcc]
      have hU : F.fMu = F.fG * (F.S.bp * (1 - F.S.tp)) * F.S.bp - F.S.tp := by
        unfold fMu; rw [← hhp]
      rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
        simp only [quint_0, quint_1, quint_2, quint_3, quint_4, pV, pM, pB, pU, pN, pW, pA] <;> (try rw [hU]) <;> ring
    rw [e]
    refine robust_smul_pos (robust_cycF5 hzN0 ?_ hmu) (mul_pos hA11 hρ)
    have := mul_pos hG (mul_pos F.S.bp_pos F.S.hm_pos)
    nlinarith [F.S.tm_pos]


theorem oW_eq : F.oW = Ot F.fRho F.S.bp (pU F.S.tp F.S.bp) pV (pW F.S.sp F.S.kp) := by
  simp only [oW, Ot, crF, scF, C3.sub, pU, pV, pW]; ring

theorem rimF_lam (heq : F.a12 = F.a11) (h22 : F.a11 < F.a22)
    (hg : F.gg * F.S.ap * F.S.dp = F.a11) (hb : F.S.bp ≤ F.S.am) {lam : ℝ} (hl : 0 < lam)
    (hlW : lam * F.S.tp * F.S.sp < F.S.bp * (1 - F.S.tp) * F.S.sp + F.S.tp * F.S.kp)
    (hw : 0 ≤ Ot F.fRho F.S.bp (pU F.S.tp F.S.bp) pV (pW F.S.sp F.S.kp))
    (hx : 0 ≤ Ot F.fRho F.S.bp pV (pM F.S.tm F.S.hm) (pN F.S.sm F.S.km) ∨
      Ot F.fRho F.S.bp pV (pM F.S.tm F.S.hm) (pN F.S.sm F.S.km) < 0)
    (hz : Lx F.fRho F.S.bp lam (pM F.S.tm F.S.hm) pB (pN F.S.sm F.S.km) ∨
      Lx F.fRho F.S.bp lam (pN F.S.sm F.S.km) pB (pM F.S.tm F.S.hm)) :
    IsRupert (Finset.univ.image x) := by
  have H := F.fPar heq h22 hg hb hl hlW
  have hW := lx_UVW_of H hw
  rcases hx with hx | hx
  · have hx' := lx_VMN_of H hx
    rcases hz with hz | hz
    · exact F.rimFA2_rupert heq h22 hg hb hl hlW hx' hz hW
    · exact F.rimFC_rupert heq h22 hg hb hl hlW hx' (Lx_rot (Lx_rot hz)) hW
  · rcases hz with hz | hz
    · exact F.rimFD_rupert heq h22 hg hb hl hlW hx hz hW
    · exact F.rimFB_rupert heq h22 hg hb hl hlW hx hz hW


theorem fW_lt (heq : F.a12 = F.a11) (h22 : F.a11 < F.a22)
    (hg : F.gg * F.S.ap * F.S.dp = F.a11) (hc : F.a11 * F.S.cp ≤ F.a22 * F.S.ap) (hW : F.oW < 0) :
    F.fG * F.S.bp * F.S.kp < F.fMu * (1 - F.S.sp) := by
  obtain ⟨hA11, hG, hmu, hρ, hhp, hG1, hdep⟩ := F.fData heq h22 hg
  have hD : 0 < F.fMu + 1 := by linarith
  have hr : F.fRho * (F.fMu + 1) = F.a22 / F.a11 - 1 := by
    unfold fRho; field_simp
  have h22' : F.a22 = F.a11 * (1 + F.fRho * (F.fMu + 1)) := by
    rw [hr]; field_simp; ring
  have hc' : F.S.cp ≤ F.S.ap * (1 + F.fRho * (F.fMu + 1)) := by
    rw [h22'] at hc
    have : F.a11 * F.S.cp ≤ F.a11 * (F.S.ap * (1 + F.fRho * (F.fMu + 1))) := by linarith
    exact le_of_mul_le_mul_left this hA11
  have e : F.oW = F.S.tp * F.S.sp * (F.S.ap * (1 + F.fRho) + F.fRho * F.S.bp - F.S.cp) := by
    unfold oW
    linear_combination (F.S.sp * (1 + F.fRho)) * F.S.bp_mul - (F.S.sp * (1 + F.fRho)) * F.S.ap_mul + F.S.tp * F.S.cp_mul
  have hts : 0 < F.S.tp * F.S.sp := mul_pos F.S.tp_pos F.S.sp_pos
  have h1 : F.S.ap * (1 + F.fRho) + F.fRho * F.S.bp - F.S.cp < 0 := by
    rw [e] at hW
    by_contra hcon
    push Not at hcon
    nlinarith [mul_nonneg hts.le hcon]
  have h2 : F.fRho * F.S.bp < F.fRho * (F.S.ap * F.fMu) := by nlinarith
  have h3 : F.S.bp < F.S.ap * F.fMu := lt_of_mul_lt_mul_left h2 hρ.le
  have h4 : F.fG * F.S.bp * F.S.dp < F.fMu := by
    have : (F.fG * F.S.bp * F.S.dp) * F.S.ap < F.fMu * F.S.ap := by
      have : (F.fG * F.S.bp * F.S.dp) * F.S.ap = F.S.bp * (F.fG * F.S.ap * F.S.dp) := by ring
      rw [this, hG1]; linarith
    exact lt_of_mul_lt_mul_right this F.S.ap_pos.le
  have h5 : F.S.kp = F.S.dp * (1 - F.S.sp) := F.S.dp_mul.symm
  rw [h5]
  have := mul_lt_mul_of_pos_right h4 (sub_pos.2 F.S.sp_lt)
  linarith

theorem fzN0 (heq : F.a12 = F.a11) (h22 : F.a11 < F.a22)
    (hg : F.gg * F.S.ap * F.S.dp = F.a11) (hb : F.S.bp ≤ F.S.am)
    (hx : Ot F.fRho F.S.bp pV (pM F.S.tm F.S.hm) (pN F.S.sm F.S.km) < 0) :
    F.fMu * F.S.sm - F.fG * F.S.bp * F.S.km < 0 := by
  obtain ⟨hA11, hG, hmu, hρ, hhp, -, hdep⟩ := F.fData heq h22 hg
  have hbm : F.S.bp * F.S.tm ≤ F.S.hm := by
    rw [← F.S.am_mul]; exact mul_le_mul_of_nonneg_right hb F.S.tm_pos.le
  have hk : F.S.bp * F.S.sm < F.S.km := by
    have h1 : F.S.tm * (F.S.bp * F.S.sm) < F.S.tm * F.S.km := by
      simp only [Ot, crF, scF, C3.sub, pV, pM, pN] at hx
      nlinarith [mul_nonneg hρ.le (sub_nonneg.2 hbm), mul_pos F.S.sm_pos F.S.hm_pos,
        mul_nonneg F.S.sm_pos.le (sub_nonneg.2 hbm), mul_pos hρ F.S.tm_pos]
    exact lt_of_mul_lt_mul_left h1 F.S.tm_pos.le
  have hU : F.fMu = F.fG * (F.S.bp * (1 - F.S.tp)) * F.S.bp - F.S.tp := by
    unfold fMu; rw [← hhp]
  have h2 : F.S.bp * (1 - F.S.tp) * F.S.sm < F.S.km := by
    nlinarith [mul_pos F.S.bp_pos F.S.tp_pos, mul_pos F.S.sm_pos (mul_pos F.S.bp_pos F.S.tp_pos)]
  rw [hU]
  nlinarith [mul_pos hG (mul_pos F.S.bp_pos (sub_pos.2 h2)), mul_pos F.S.tp_pos F.S.sm_pos]


theorem rimFAP_rupert (heq : F.a12 = F.a11) (h22 : F.a11 < F.a22)
    (hg : F.gg * F.S.ap * F.S.dp = F.a11) (hc : F.a11 * F.S.cp ≤ F.a22 * F.S.ap) (hb : F.S.bp ≤ F.S.am) {lam : ℝ} (hl : 0 < lam)
    (hlW : lam * F.S.tp * F.S.sp < F.S.bp * (1 - F.S.tp) * F.S.sp + F.S.tp * F.S.kp)
    (hW : F.oW < 0)
    (hx : Lx F.fRho F.S.bp lam pV (pM F.S.tm F.S.hm) (pN F.S.sm F.S.km)) (hz : Lx F.fRho F.S.bp lam (pM F.S.tm F.S.hm) pB (pN F.S.sm F.S.km)) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨hA11, hG, hmu, hρ, hhp, -, hdep⟩ := F.fData heq h22 hg
  have H := F.fPar heq h22 hg hb hl hlW
  have hW' : Ot F.fRho F.S.bp (pU F.S.tp F.S.bp) pV (pW F.S.sp F.S.kp) < 0 := by
    rw [← F.oW_eq]; exact hW
  have hwm := F.fW_lt heq h22 hg hc hW
  have hw0 : 0 < F.fMu * F.S.sp + F.fG * F.S.bp * F.S.kp := by
    have := mul_pos hG (mul_pos F.S.bp_pos F.S.kp_pos)
    nlinarith [mul_pos hmu F.S.sp_pos]
  have hwm : F.fMu * F.S.sp + F.fG * F.S.bp * F.S.kp < F.fMu := by nlinarith
  have hzN1 : F.fMu * F.S.sm - F.fG * F.S.bp * F.S.km < F.fMu := by
    have := mul_pos hG (mul_pos F.S.bp_pos F.S.km_pos)
    nlinarith [mul_pos hmu (sub_pos.2 F.S.sm_lt)]
  have hcc : ∀ i, F.toFrame7.ptC (quint (5 : Fin 7) 6 4 0 1 i) =
      quint pV (pM F.S.tm F.S.hm) pB (pU F.S.tp F.S.bp) (pW F.S.sp F.S.kp) i := by
    intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [quint_0, quint_1, quint_2, quint_3, quint_4, F.ptC_5, F.ptC_6, F.ptC_4, F.ptC_0, F.ptC_1, pB, pM, pN, pU, pV, pW, hhp]
  refine F.toFrame7.rupert_rim_rob (k := 5) (by norm_num) (quint (5 : Fin 7) 6 4 0 1) (-1)
    (Or.inr rfl) (uF F.fRho F.S.bp) (dF lam) (Or.inr (Or.inl (by simp [uF]))) ?_ ?_ ?_
  · intro i j h1 h2
    simp only [hcc]
    exact rimAP_cyc H hx hz hW' i j h1 h2
  · intro j' hj' i
    simp only [hcc]
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (by simp [quint_3]) (hj' 3)
    · exact absurd (by simp [quint_4]) (hj' 4)
    · rw [F.ptC_2]
      exact rimAP_restN H hx hz hW' i
    · rw [F.ptC_3]
      exact rimAP_restA H hx hz hW' i
    · exact absurd (by simp [quint_2]) (hj' 2)
    · exact absurd (by simp [quint_0]) (hj' 0)
    · exact absurd (by simp [quint_1]) (hj' 1)
  · have e : (fun i : ZMod 5 => F.toFrame7.GG (F.toFrame7.ptC (quint (5 : Fin 7) 6 4 0 1 i)) (uF F.fRho F.S.bp)) =
        fun i : ZMod 5 => F.a11 * F.fRho * quint (0:ℝ) (-F.S.tm - F.fG * F.S.bp * F.S.hm) F.fMu F.fMu (F.fMu * F.S.sp + F.fG * F.S.bp * F.S.kp) i := by
      funext i
      rw [hdep, hcc]
      have hU : F.fMu = F.fG * (F.S.bp * (1 - F.S.tp)) * F.S.bp - F.S.tp := by
        unfold fMu; rw [← hhp]
      rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
        simp only [quint_0, quint_1, quint_2, quint_3, quint_4, pV, pM, pB, pU, pN, pW, pA] <;> (try rw [hU]) <;> ring
    rw [e]
    refine robust_smul_pos (robust_cycP5 (by have := mul_pos hG (mul_pos F.S.bp_pos F.S.hm_pos); nlinarith [F.S.tm_pos]) hw0 hwm) (mul_pos hA11 hρ)

theorem rimFBP_rupert (heq : F.a12 = F.a11) (h22 : F.a11 < F.a22)
    (hg : F.gg * F.S.ap * F.S.dp = F.a11) (hc : F.a11 * F.S.cp ≤ F.a22 * F.S.ap) (hb : F.S.bp ≤ F.S.am) {lam : ℝ} (hl : 0 < lam)
    (hlW : lam * F.S.tp * F.S.sp < F.S.bp * (1 - F.S.tp) * F.S.sp + F.S.tp * F.S.kp)
    (hW : F.oW < 0)
    (hx : Ot F.fRho F.S.bp pV (pM F.S.tm F.S.hm) (pN F.S.sm F.S.km) < 0) (hz : Lx F.fRho F.S.bp lam (pN F.S.sm F.S.km) pB (pM F.S.tm F.S.hm)) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨hA11, hG, hmu, hρ, hhp, -, hdep⟩ := F.fData heq h22 hg
  have H := F.fPar heq h22 hg hb hl hlW
  have hW' : Ot F.fRho F.S.bp (pU F.S.tp F.S.bp) pV (pW F.S.sp F.S.kp) < 0 := by
    rw [← F.oW_eq]; exact hW
  have hwm := F.fW_lt heq h22 hg hc hW
  have hw0 : 0 < F.fMu * F.S.sp + F.fG * F.S.bp * F.S.kp := by
    have := mul_pos hG (mul_pos F.S.bp_pos F.S.kp_pos)
    nlinarith [mul_pos hmu F.S.sp_pos]
  have hwm : F.fMu * F.S.sp + F.fG * F.S.bp * F.S.kp < F.fMu := by nlinarith
  have hzN1 : F.fMu * F.S.sm - F.fG * F.S.bp * F.S.km < F.fMu := by
    have := mul_pos hG (mul_pos F.S.bp_pos F.S.km_pos)
    nlinarith [mul_pos hmu (sub_pos.2 F.S.sm_lt)]
  have hcc : ∀ i, F.toFrame7.ptC (quint (5 : Fin 7) 2 4 0 1 i) =
      quint pV (pN F.S.sm F.S.km) pB (pU F.S.tp F.S.bp) (pW F.S.sp F.S.kp) i := by
    intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [quint_0, quint_1, quint_2, quint_3, quint_4, F.ptC_5, F.ptC_2, F.ptC_4, F.ptC_0, F.ptC_1, pB, pM, pN, pU, pV, pW, hhp]
  refine F.toFrame7.rupert_rim_rob (k := 5) (by norm_num) (quint (5 : Fin 7) 2 4 0 1) (-1)
    (Or.inr rfl) (uF F.fRho F.S.bp) (dF lam) (Or.inr (Or.inl (by simp [uF]))) ?_ ?_ ?_
  · intro i j h1 h2
    simp only [hcc]
    exact rimBP_cyc H hx hz hW' i j h1 h2
  · intro j' hj' i
    simp only [hcc]
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (by simp [quint_3]) (hj' 3)
    · exact absurd (by simp [quint_4]) (hj' 4)
    · exact absurd (by simp [quint_1]) (hj' 1)
    · rw [F.ptC_3]
      exact rimBP_restA H hx hz hW' i
    · exact absurd (by simp [quint_2]) (hj' 2)
    · exact absurd (by simp [quint_0]) (hj' 0)
    · rw [F.ptC_6]
      exact rimBP_restM H hx hz hW' i
  · have e : (fun i : ZMod 5 => F.toFrame7.GG (F.toFrame7.ptC (quint (5 : Fin 7) 2 4 0 1 i)) (uF F.fRho F.S.bp)) =
        fun i : ZMod 5 => F.a11 * F.fRho * quint (0:ℝ) (F.fMu * F.S.sm - F.fG * F.S.bp * F.S.km) F.fMu F.fMu (F.fMu * F.S.sp + F.fG * F.S.bp * F.S.kp) i := by
      funext i
      rw [hdep, hcc]
      have hU : F.fMu = F.fG * (F.S.bp * (1 - F.S.tp)) * F.S.bp - F.S.tp := by
        unfold fMu; rw [← hhp]
      rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
        simp only [quint_0, quint_1, quint_2, quint_3, quint_4, pV, pM, pB, pU, pN, pW, pA] <;> (try rw [hU]) <;> ring
    rw [e]
    refine robust_smul_pos (robust_cycP5 (F.fzN0 heq h22 hg hb hx) hw0 hwm) (mul_pos hA11 hρ)

theorem rimFCP_rupert (heq : F.a12 = F.a11) (h22 : F.a11 < F.a22)
    (hg : F.gg * F.S.ap * F.S.dp = F.a11) (hc : F.a11 * F.S.cp ≤ F.a22 * F.S.ap) (hb : F.S.bp ≤ F.S.am) {lam : ℝ} (hl : 0 < lam)
    (hlW : lam * F.S.tp * F.S.sp < F.S.bp * (1 - F.S.tp) * F.S.sp + F.S.tp * F.S.kp)
    (hW : F.oW < 0)
    (hx : Lx F.fRho F.S.bp lam pV (pM F.S.tm F.S.hm) (pN F.S.sm F.S.km)) (hz : Lx F.fRho F.S.bp lam (pM F.S.tm F.S.hm) (pN F.S.sm F.S.km) pB) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨hA11, hG, hmu, hρ, hhp, -, hdep⟩ := F.fData heq h22 hg
  have H := F.fPar heq h22 hg hb hl hlW
  have hW' : Ot F.fRho F.S.bp (pU F.S.tp F.S.bp) pV (pW F.S.sp F.S.kp) < 0 := by
    rw [← F.oW_eq]; exact hW
  have hwm := F.fW_lt heq h22 hg hc hW
  have hw0 : 0 < F.fMu * F.S.sp + F.fG * F.S.bp * F.S.kp := by
    have := mul_pos hG (mul_pos F.S.bp_pos F.S.kp_pos)
    nlinarith [mul_pos hmu F.S.sp_pos]
  have hwm : F.fMu * F.S.sp + F.fG * F.S.bp * F.S.kp < F.fMu := by nlinarith
  have hzN1 : F.fMu * F.S.sm - F.fG * F.S.bp * F.S.km < F.fMu := by
    have := mul_pos hG (mul_pos F.S.bp_pos F.S.km_pos)
    nlinarith [mul_pos hmu (sub_pos.2 F.S.sm_lt)]
  have hcc : ∀ i, F.toFrame7.ptC (hex6 (5 : Fin 7) 6 2 4 0 1 i) =
      hex6 pV (pM F.S.tm F.S.hm) (pN F.S.sm F.S.km) pB (pU F.S.tp F.S.bp) (pW F.S.sp F.S.kp) i := by
    intro i
    rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [hex6_0, hex6_1, hex6_2, hex6_3, hex6_4, hex6_5, F.ptC_5, F.ptC_6, F.ptC_2, F.ptC_4, F.ptC_0, F.ptC_1, pB, pM, pN, pU, pV, pW, hhp]
  refine F.toFrame7.rupert_rim_rob (k := 6) (by norm_num) (hex6 (5 : Fin 7) 6 2 4 0 1) (-1)
    (Or.inr rfl) (uF F.fRho F.S.bp) (dF lam) (Or.inr (Or.inl (by simp [uF]))) ?_ ?_ ?_
  · intro i j h1 h2
    simp only [hcc]
    exact rimCP_cyc H hx hz hW' i j h1 h2
  · intro j' hj' i
    simp only [hcc]
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (by simp [hex6_4]) (hj' 4)
    · exact absurd (by simp [hex6_5]) (hj' 5)
    · exact absurd (by simp [hex6_2]) (hj' 2)
    · rw [F.ptC_3]
      exact rimCP_restA H hx hz hW' i
    · exact absurd (by simp [hex6_3]) (hj' 3)
    · exact absurd (by simp [hex6_0]) (hj' 0)
    · exact absurd (by simp [hex6_1]) (hj' 1)
  · have e : (fun i : ZMod 6 => F.toFrame7.GG (F.toFrame7.ptC (hex6 (5 : Fin 7) 6 2 4 0 1 i)) (uF F.fRho F.S.bp)) =
        fun i : ZMod 6 => F.a11 * F.fRho * hex6 (0:ℝ) (-F.S.tm - F.fG * F.S.bp * F.S.hm) (F.fMu * F.S.sm - F.fG * F.S.bp * F.S.km) F.fMu F.fMu (F.fMu * F.S.sp + F.fG * F.S.bp * F.S.kp) i := by
      funext i
      rw [hdep, hcc]
      have hU : F.fMu = F.fG * (F.S.bp * (1 - F.S.tp)) * F.S.bp - F.S.tp := by
        unfold fMu; rw [← hhp]
      rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [hex6_0, hex6_1, hex6_2, hex6_3, hex6_4, hex6_5, pV, pM, pB, pU, pN, pW, pA] <;> (try rw [hU]) <;> ring
    rw [e]
    refine robust_smul_pos (robust_cycP6 (by have := mul_pos hG (mul_pos F.S.bp_pos F.S.hm_pos); nlinarith [F.S.tm_pos]) hzN1 hw0 hwm) (mul_pos hA11 hρ)

theorem rimFDP_rupert (heq : F.a12 = F.a11) (h22 : F.a11 < F.a22)
    (hg : F.gg * F.S.ap * F.S.dp = F.a11) (hc : F.a11 * F.S.cp ≤ F.a22 * F.S.ap) (hb : F.S.bp ≤ F.S.am) {lam : ℝ} (hl : 0 < lam)
    (hlW : lam * F.S.tp * F.S.sp < F.S.bp * (1 - F.S.tp) * F.S.sp + F.S.tp * F.S.kp)
    (hW : F.oW < 0)
    (hx : Ot F.fRho F.S.bp pV (pM F.S.tm F.S.hm) (pN F.S.sm F.S.km) < 0) (hz : Lx F.fRho F.S.bp lam (pM F.S.tm F.S.hm) pB (pN F.S.sm F.S.km)) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨hA11, hG, hmu, hρ, hhp, -, hdep⟩ := F.fData heq h22 hg
  have H := F.fPar heq h22 hg hb hl hlW
  have hW' : Ot F.fRho F.S.bp (pU F.S.tp F.S.bp) pV (pW F.S.sp F.S.kp) < 0 := by
    rw [← F.oW_eq]; exact hW
  have hwm := F.fW_lt heq h22 hg hc hW
  have hw0 : 0 < F.fMu * F.S.sp + F.fG * F.S.bp * F.S.kp := by
    have := mul_pos hG (mul_pos F.S.bp_pos F.S.kp_pos)
    nlinarith [mul_pos hmu F.S.sp_pos]
  have hwm : F.fMu * F.S.sp + F.fG * F.S.bp * F.S.kp < F.fMu := by nlinarith
  have hzN1 : F.fMu * F.S.sm - F.fG * F.S.bp * F.S.km < F.fMu := by
    have := mul_pos hG (mul_pos F.S.bp_pos F.S.km_pos)
    nlinarith [mul_pos hmu (sub_pos.2 F.S.sm_lt)]
  have hcc : ∀ i, F.toFrame7.ptC (hex6 (5 : Fin 7) 2 6 4 0 1 i) =
      hex6 pV (pN F.S.sm F.S.km) (pM F.S.tm F.S.hm) pB (pU F.S.tp F.S.bp) (pW F.S.sp F.S.kp) i := by
    intro i
    rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [hex6_0, hex6_1, hex6_2, hex6_3, hex6_4, hex6_5, F.ptC_5, F.ptC_2, F.ptC_6, F.ptC_4, F.ptC_0, F.ptC_1, pB, pM, pN, pU, pV, pW, hhp]
  refine F.toFrame7.rupert_rim_rob (k := 6) (by norm_num) (hex6 (5 : Fin 7) 2 6 4 0 1) (-1)
    (Or.inr rfl) (uF F.fRho F.S.bp) (dF lam) (Or.inr (Or.inl (by simp [uF]))) ?_ ?_ ?_
  · intro i j h1 h2
    simp only [hcc]
    exact rimDP_cyc H hx hz hW' i j h1 h2
  · intro j' hj' i
    simp only [hcc]
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (by simp [hex6_4]) (hj' 4)
    · exact absurd (by simp [hex6_5]) (hj' 5)
    · exact absurd (by simp [hex6_1]) (hj' 1)
    · rw [F.ptC_3]
      exact rimDP_restA H hx hz hW' i
    · exact absurd (by simp [hex6_3]) (hj' 3)
    · exact absurd (by simp [hex6_0]) (hj' 0)
    · exact absurd (by simp [hex6_2]) (hj' 2)
  · have e : (fun i : ZMod 6 => F.toFrame7.GG (F.toFrame7.ptC (hex6 (5 : Fin 7) 2 6 4 0 1 i)) (uF F.fRho F.S.bp)) =
        fun i : ZMod 6 => F.a11 * F.fRho * hex6 (0:ℝ) (F.fMu * F.S.sm - F.fG * F.S.bp * F.S.km) (-F.S.tm - F.fG * F.S.bp * F.S.hm) F.fMu F.fMu (F.fMu * F.S.sp + F.fG * F.S.bp * F.S.kp) i := by
      funext i
      rw [hdep, hcc]
      have hU : F.fMu = F.fG * (F.S.bp * (1 - F.S.tp)) * F.S.bp - F.S.tp := by
        unfold fMu; rw [← hhp]
      rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [hex6_0, hex6_1, hex6_2, hex6_3, hex6_4, hex6_5, pV, pM, pB, pU, pN, pW, pA] <;> (try rw [hU]) <;> ring
    rw [e]
    refine robust_smul_pos (robust_cycP6 (F.fzN0 heq h22 hg hb hx) (by have := mul_pos hG (mul_pos F.S.bp_pos F.S.hm_pos); nlinarith [F.S.tm_pos]) hw0 hwm) (mul_pos hA11 hρ)


theorem rimF_lamP (heq : F.a12 = F.a11) (h22 : F.a11 < F.a22)
    (hg : F.gg * F.S.ap * F.S.dp = F.a11) (hc : F.a11 * F.S.cp ≤ F.a22 * F.S.ap) (hb : F.S.bp ≤ F.S.am) {lam : ℝ} (hl : 0 < lam)
    (hlW : lam * F.S.tp * F.S.sp < F.S.bp * (1 - F.S.tp) * F.S.sp + F.S.tp * F.S.kp)
    (hW : F.oW < 0)
    (hx : 0 ≤ Ot F.fRho F.S.bp pV (pM F.S.tm F.S.hm) (pN F.S.sm F.S.km) ∨
      Ot F.fRho F.S.bp pV (pM F.S.tm F.S.hm) (pN F.S.sm F.S.km) < 0)
    (hz : Lx F.fRho F.S.bp lam (pM F.S.tm F.S.hm) pB (pN F.S.sm F.S.km) ∨
      Lx F.fRho F.S.bp lam (pN F.S.sm F.S.km) pB (pM F.S.tm F.S.hm)) :
    IsRupert (Finset.univ.image x) := by
  have H := F.fPar heq h22 hg hb hl hlW
  rcases hx with hx | hx
  · have hx' := lx_VMN_of H hx
    rcases hz with hz | hz
    · exact F.rimFAP_rupert heq h22 hg hc hb hl hlW hW hx' hz
    · exact F.rimFCP_rupert heq h22 hg hc hb hl hlW hW hx' (Lx_rot (Lx_rot hz))
  · rcases hz with hz | hz
    · exact F.rimFDP_rupert heq h22 hg hc hb hl hlW hW hx hz
    · exact F.rimFBP_rupert heq h22 hg hc hb hl hlW hW hx hz


/-- **`thmF_rest3`**: the rims with `m2+` shown (`oW < 0`), rims A+, B+, C+, D+. -/
theorem thmF_rest3 (heq : F.a12 = F.a11) (h22 : F.a11 < F.a22)
    (hg : F.gg * F.S.ap * F.S.dp = F.a11) (hc : F.a11 * F.S.cp ≤ F.a22 * F.S.ap)
    (hb : F.S.bp ≤ F.S.am) (h : F.oW < 0) :
    IsRupert (Finset.univ.image x) := by
  have hnum : 0 < F.S.bp * (1 - F.S.tp) * F.S.sp + F.S.tp * F.S.kp := by
    have := F.S.tp_lt
    have := mul_pos F.S.bp_pos (sub_pos.2 F.S.tp_lt)
    have := mul_pos this F.S.sp_pos
    have := mul_pos F.S.tp_pos F.S.kp_pos
    linarith
  have hden : 0 < F.S.tp * F.S.sp := mul_pos F.S.tp_pos F.S.sp_pos
  set lam1 := (F.S.bp * (1 - F.S.tp) * F.S.sp + F.S.tp * F.S.kp) / (2 * (F.S.tp * F.S.sp)) with hlam1
  have hl1 : 0 < lam1 := by positivity
  have hl1W : lam1 * F.S.tp * F.S.sp < F.S.bp * (1 - F.S.tp) * F.S.sp + F.S.tp * F.S.kp := by
    have key : lam1 * (2 * (F.S.tp * F.S.sp)) =
        F.S.bp * (1 - F.S.tp) * F.S.sp + F.S.tp * F.S.kp :=
      div_mul_cancel₀ _ (by positivity)
    nlinarith [key, hnum]
  have H := F.fPar heq h22 hg hb hl1 hl1W
  rcases lam_choice H with hz | ⟨H2, hz⟩
  · exact F.rimF_lamP heq h22 hg hc hb hl1 hl1W h (le_or_gt _ _) hz
  · exact F.rimF_lamP heq h22 hg hc hb H2.lam_pos H2.lam_lt h (le_or_gt _ _) (Or.inr hz)

theorem thmF_rest (heq : F.a12 = F.a11) (h22 : F.a11 < F.a22)
    (hg : F.gg * F.S.ap * F.S.dp = F.a11) (hc : F.a11 * F.S.cp ≤ F.a22 * F.S.ap)
    (hb : F.S.bp ≤ F.S.am) (h : ¬ (0 < F.oN1 ∧ 0 < F.oN2 ∧ 0 < F.oW)) :
    IsRupert (Finset.univ.image x) := by
  by_cases hW : F.oW < 0
  · exact F.thmF_rest3 heq h22 hg hc hb hW
  · have hW0 : 0 ≤ F.oW := not_lt.1 hW
    have hnum : 0 < F.S.bp * (1 - F.S.tp) * F.S.sp + F.S.tp * F.S.kp := by
      have := F.S.tp_lt
      have := mul_pos F.S.bp_pos (sub_pos.2 F.S.tp_lt)
      have := mul_pos this F.S.sp_pos
      have := mul_pos F.S.tp_pos F.S.kp_pos
      linarith
    have hden : 0 < F.S.tp * F.S.sp := mul_pos F.S.tp_pos F.S.sp_pos
    set lam1 := (F.S.bp * (1 - F.S.tp) * F.S.sp + F.S.tp * F.S.kp) / (2 * (F.S.tp * F.S.sp)) with hlam1
    have hl1 : 0 < lam1 := by positivity
    have hl1W : lam1 * F.S.tp * F.S.sp < F.S.bp * (1 - F.S.tp) * F.S.sp + F.S.tp * F.S.kp := by
      have key : lam1 * (2 * (F.S.tp * F.S.sp)) =
          F.S.bp * (1 - F.S.tp) * F.S.sp + F.S.tp * F.S.kp :=
        div_mul_cancel₀ _ (by positivity)
      nlinarith [key, hnum]
    have H := F.fPar heq h22 hg hb hl1 hl1W
    have hw : 0 ≤ Ot F.fRho F.S.bp (pU F.S.tp F.S.bp) pV (pW F.S.sp F.S.kp) := by
      rw [← F.oW_eq]; exact hW0
    rcases lam_choice H with hz | ⟨H2, hz⟩
    · exact F.rimF_lam heq h22 hg hb hl1 hl1W hw (le_or_gt _ _) hz
    · have hl2 := H2.lam_pos
      have hl2W := H2.lam_lt
      have hw2 : 0 ≤ Ot F.fRho F.S.bp (pU F.S.tp F.S.bp) pV (pW F.S.sp F.S.kp) := hw
      exact F.rimF_lam heq h22 hg hb hl2 hl2W hw2 (le_or_gt _ _) (Or.inr hz)


/-- **Theorem F** (`A12 = A11 < A22`, `TF+`: `g a+ d+ = A11`, `A22 a+ ≥ A11 c+`, and `b+ ≤ a-`):
the view `u' = (-(β + D), D, b+ β)` (`A11 = 1`: `β = A22/A11 - 1`, `g` replaced by `gg/a11`,
`D = 1 - t+ + g h+ b+`), face `(m1+, xa, xb)` edge-on, `xa` hidden; the rims are the upper chain
`v → [m2+] → m1+ → xb` and a lower chain `xb → (m1-, m2- in some order) → v`. -/
theorem thmF (heq : F.a12 = F.a11) (h22 : F.a11 < F.a22)
    (hg : F.gg * F.S.ap * F.S.dp = F.a11) (hc : F.a11 * F.S.cp ≤ F.a22 * F.S.ap)
    (hb : F.S.bp ≤ F.S.am) : IsRupert (Finset.univ.image x) := by
  by_cases hA : 0 < F.oN1 ∧ 0 < F.oN2 ∧ 0 < F.oW
  · exact F.rimFA_rupert heq h22 hg hb hA.1 hA.2.1 hA.2.2
  · exact F.thmF_rest heq h22 hg hc hb hA

theorem thmFz (heq : F.a12 = F.a11) (h22 : F.a11 < F.a22)
    (hg : F.gg * F.S.am * F.S.dm = F.a11) (hc : F.a11 * F.S.cm ≤ F.a22 * F.S.am)
    (hb : F.S.bm ≤ F.S.ap) : IsRupert (Finset.univ.image x) := by
  have hg' : F.zFrame.gg * F.zFrame.S.ap * F.zFrame.S.dp = F.zFrame.a11 := by
    rw [F.zFrame_gg, F.zFrame_a11]; exact hg
  exact rupert_of_z (F.zFrame.thmF heq h22 hg' hc hb)

/-- The first disjunct of `CaseC18Special'` (the R1' residual) is Rupert. -/
theorem isRupert_of_D1 (heq : F.a12 = F.a11) (n1 : F.S.bp ≤ F.S.am) (n2 : F.S.bm ≤ F.S.ap)
    (A : F.S.am = F.S.bp ∨ (F.gg * F.S.am * F.S.dm = F.a11 ∧ F.a22 * F.S.am ≥ F.a11 * F.S.cm)) :
    IsRupert (Finset.univ.image x) := by
  have h22 := F.a11_lt_a22_of_eq heq
  by_cases hTp : F.gg * F.S.ap * F.S.dp = F.a11 ∧ F.a22 * F.S.ap ≥ F.a11 * F.S.cp
  · exact F.thmF heq h22 hTp.1 hTp.2 n1
  by_cases hTm : F.gg * F.S.am * F.S.dm = F.a11 ∧ F.a22 * F.S.am ≥ F.a11 * F.S.cm
  · exact F.thmFz heq h22 hTm.1 hTm.2 n2
  have hA : F.S.am = F.S.bp := A.resolve_right hTm
  rcases F.thmRp heq hA with h | ⟨e1, e2⟩
  · exact h
  · exfalso
    apply hTm
    refine ⟨e1, ?_⟩
    have hamp : 0 < F.S.am := div_pos F.S.hm_pos F.S.tm_pos
    have : F.a11 * F.S.cm ≤ F.a11 * F.S.am :=
      mul_le_mul_of_nonneg_left e2 (by have h0 : 0 < F.a12 := F.A12_pos; linarith)
    have h2 : F.a11 * F.S.am ≤ F.a22 * F.S.am := mul_le_mul_of_nonneg_right h22.le hamp.le
    linarith

end Frame18

/-! ### Group E-star: Theorem E* (PROOFS 38), the family E, first-order motion with spin

The Frame7-level core: the normalised family `K(t+, t-, γ)` (`h = 1`, `z`-coordinates `±1`) with
Gram `lam * [[1, p, 0], [p, p T, 0], [0, 0, γ]]`, `T = t+ + t-`, `p = γ T / (t+ t-)`.  The view is
`u_ε = W + ε d` with `W = m2- - v = (0, t- / T, -1)`, `d = (-η, 0, 1)`; `σ = -1`; the certificate is
`FoCert` (local: six corners `(v, m2-, m1-, xa, m1+, m2+) = (5, 2, 6, 3, 0, 1)` with their ccw
neighbours, and `xb` (4) in the triangle `(v, m1+, m2+) = (5, 0, 1)`), every test affine in `ε`. -/

namespace Efam

/-- `T = t+ + t-`. -/
noncomputable def T (tp tm : ℝ) : ℝ := tp + tm

/-- `κ = T/(γ t-) - 1/(t+ t-)` of Lemma D. -/
noncomputable def kappa (tp tm γ : ℝ) : ℝ := (tp + tm) / (γ * tm) - 1 / (tp * tm)

/-- `a = (T - 1)/(T κ)` (the spin). -/
noncomputable def spin (tp tm γ : ℝ) : ℝ := (tp + tm - 1) / ((tp + tm) * kappa tp tm γ)

/-- `B = 1 - t+ (T-1)/T - (T-1)/(T κ t-)`. -/
noncomputable def bB (tp tm γ : ℝ) : ℝ :=
  1 - tp * (tp + tm - 1) / (tp + tm) - (tp + tm - 1) / ((tp + tm) * kappa tp tm γ * tm)

/-- **F1** `κ t-^2 > 1`, i.e. `γ < t+ t-`. -/
theorem F1 {tp tm γ : ℝ} (htp : 0 < tp) (htm : 0 < tm) (hγ : 0 < γ) (hγ1 : γ < tp * tm) :
    1 < kappa tp tm γ * tm ^ 2 := by
  unfold kappa
  have h : ((tp + tm) / (γ * tm) - 1 / (tp * tm)) * tm ^ 2 = (tp + tm) * tm / γ - tm / tp := by
    field_simp
  rw [h, lt_sub_iff_add_lt, lt_div_iff₀ hγ]
  have : 1 + tm / tp = (tp + tm) / tp := by field_simp
  rw [this, div_mul_eq_mul_div, div_lt_iff₀ htp]
  nlinarith [mul_pos htp htm, mul_pos (add_pos htp htm) (sub_pos.2 hγ1)]

/-- **F2** `B > 2 - T > 0` (uses F1 and `T > 1`, `t± < 1`). -/
theorem F2 {tp tm γ : ℝ} (htp : 0 < tp) (htp1 : tp < 1) (htm : 0 < tm) (htm1 : tm < 1)
    (hT : 1 < tp + tm) (hγ : 0 < γ) (hγ1 : γ < tp * tm) :
    2 - (tp + tm) < bB tp tm γ ∧ 0 < 2 - (tp + tm) := by
  refine ⟨?_, by linarith⟩
  have hk := F1 htp htm hγ hγ1
  have hT0 : 0 < tp + tm := by linarith
  have hκ : 0 < kappa tp tm γ := by
    by_contra hc
    push_neg at hc
    nlinarith [sq_nonneg tm]
  unfold bB
  -- (T-1)/(T κ t-) < (T-1) t-/T since 1/(κ t-) < t-
  have h1 : (tp + tm - 1) / ((tp + tm) * kappa tp tm γ * tm) < (tp + tm - 1) * tm / (tp + tm) := by
    rw [div_lt_div_iff₀ (by positivity) hT0]
    have : (tp + tm - 1) * (tp + tm) < (tp + tm - 1) * (tp + tm) * (kappa tp tm γ * tm ^ 2) := by
      have hp : 0 < (tp + tm - 1) * (tp + tm) := mul_pos (by linarith) hT0
      nlinarith
    nlinarith
  have h2 : 1 - tp * (tp + tm - 1) / (tp + tm) - (tp + tm - 1) * tm / (tp + tm) = 2 - (tp + tm) := by
    field_simp; ring
  linarith

/-- **F3** `(T - 1)/(κ t-^2) < T - 1 < 1`. -/
theorem F3 {tp tm γ : ℝ} (htp : 0 < tp) (htp1 : tp < 1) (htm : 0 < tm) (htm1 : tm < 1)
    (hT : 1 < tp + tm) (hγ : 0 < γ) (hγ1 : γ < tp * tm) :
    (tp + tm - 1) / (kappa tp tm γ * tm ^ 2) < tp + tm - 1 ∧ tp + tm - 1 < 1 := by
  refine ⟨?_, by linarith⟩
  have hk := F1 htp htm hγ hγ1
  rw [div_lt_iff₀ (by linarith)]
  nlinarith [sub_pos.2 hT]

end Efam

/-- The normalised family E as hypotheses on a `Frame7` (`lam > 0` is the common scale of the
Gram form, `lam = A11`). -/
structure EFam {x : Fin 7 → ℝ³} (F : Frame7 x) (tp tm γ lam : ℝ) : Prop where
  tp_pos : 0 < tp
  tp_lt : tp < 1
  tm_pos : 0 < tm
  tm_lt : tm < 1
  T_gt : 1 < tp + tm
  γ_pos : 0 < γ
  γ_lt : γ < tp * tm
  lam_pos : 0 < lam
  p0 : F.ptC 0 = ⟨tp, 0, 1⟩
  p1 : F.ptC 1 = ⟨0, tp / (tp + tm), 1⟩
  p2 : F.ptC 2 = ⟨0, tm / (tp + tm), -1⟩
  p3 : F.ptC 3 = ⟨1, 0, 0⟩
  p4 : F.ptC 4 = ⟨0, 1, 0⟩
  p5 : F.ptC 5 = ⟨0, 0, 0⟩
  p6 : F.ptC 6 = ⟨tm, 0, -1⟩
  ha11 : F.a11 = lam
  ha12 : F.a12 = lam * (γ * (tp + tm) / (tp * tm))
  ha22 : F.a22 = lam * (γ * (tp + tm) / (tp * tm)) * (tp + tm)
  hgg : F.gg = lam * γ

namespace Frame7
variable {x : Fin 7 → ℝ³} (F : Frame7 x)

/-- The screen map at `W`: `π(x, y, z) = (x, z + d+ y)`, `d+ = T/t-`. -/
noncomputable def screenW (tp tm : ℝ) (q : C3) : ℝ × ℝ :=
  (q.x, q.z + (tp + tm) / tm * q.y)

/-- The depth coordinate `ζ(p) = ⟪W, p⟫_G / ⟪W, W⟫_G`, `W = (0, t- / T, -1)`. -/
noncomputable def zetaW (tp tm : ℝ) (p : C3) : ℝ :=
  F.GG ⟨0, tm / (tp + tm), -1⟩ p / F.GG ⟨0, tm / (tp + tm), -1⟩ ⟨0, tm / (tp + tm), -1⟩

/-- `K J` with `K = [[1, -a-], [-a-, κ]]`, `a- = 1/t-`, `J (X, Y) = (-Y, X)`. -/
noncomputable def kjW (tp tm γ : ℝ) (q : ℝ × ℝ) : ℝ × ℝ :=
  (-q.2 - q.1 / tm, q.2 / tm + Efam.kappa tp tm γ * q.1)

/-- 2D cross product. -/
def cr (p q : ℝ × ℝ) : ℝ := p.1 * q.2 - p.2 * q.1

theorem Dc_tilt (a b W d : C3) (ε : ℝ) : Dc a b (C3.tilt W d ε) = Dc a b W + ε * Dc a b d := by
  simp only [Dc, C3.tilt]; ring

theorem Dc_W {tp tm : ℝ} (htp : 0 < tp) (htm : 0 < tm) (a b : C3) :
    Dc a b ⟨0, tm / (tp + tm), -1⟩ =
      -(tm / (tp + tm)) * cr (Frame7.screenW tp tm a) (Frame7.screenW tp tm b) := by
  have : tp + tm ≠ 0 := by positivity
  simp only [Dc, cr, Frame7.screenW]; field_simp; ring

/-- A test is good at `W` with tilt `d`. -/
def Good (W d a b : C3) : Prop := 0 < -Dc a b W ∨ (-Dc a b W = 0 ∧ 0 < -Dc a b d)

theorem ev_of_good {W d a b : C3} (h : Good W d a b) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < (-1 : ℝ) * Dc a b (C3.tilt W d ε) := by
  have := eventually_pos_affine h
  filter_upwards [this] with ε hε
  rw [Dc_tilt]; linarith

theorem good_pos {tp tm : ℝ} (htp : 0 < tp) (htm : 0 < tm) {d a b : C3}
    (h : 0 < cr (Frame7.screenW tp tm a) (Frame7.screenW tp tm b)) :
    Good ⟨0, tm / (tp + tm), -1⟩ d a b := by
  left
  rw [Dc_W htp htm]
  have : 0 < tm / (tp + tm) := by positivity
  nlinarith

theorem sc_sub (tp tm : ℝ) (a b : C3) :
    Frame7.screenW tp tm (a.sub b) = Frame7.screenW tp tm a - Frame7.screenW tp tm b := by
  simp only [Frame7.screenW, C3.sub]; ext <;> simp <;> ring

theorem sc_add (tp tm : ℝ) (a b : C3) :
    Frame7.screenW tp tm (a.add b) = Frame7.screenW tp tm a + Frame7.screenW tp tm b := by
  simp only [Frame7.screenW, C3.add]; ext <;> simp <;> ring

theorem zeta_formula {tp tm γ lam : ℝ} (h : EFam F tp tm γ lam) (q : C3) :
    F.zetaW tp tm q = (q.x + (tp + tm) * q.y - tp * q.z) / (tp + tm) := by
  have htp := h.tp_pos
  have htm := h.tm_pos
  have hγ := h.γ_pos
  have hlam := h.lam_pos
  have hT : tp + tm ≠ 0 := by positivity
  simp only [Frame7.zetaW, Frame7.GG, Gf, h.ha11, h.ha12, h.ha22, h.hgg]
  have hZ : lam * (0 * 0) + lam * (γ * (tp + tm) / (tp * tm)) * (0 * (tm / (tp + tm)) + 0 * (tm / (tp + tm))) +
      lam * (γ * (tp + tm) / (tp * tm)) * (tp + tm) * (tm / (tp + tm) * (tm / (tp + tm))) + lam * γ * (-1 * -1)
      = lam * γ * (tp + tm) / tp := by field_simp; ring
  rw [hZ]
  field_simp
  ring

theorem Dc_Wbd {tp tm : ℝ} (htp : 0 < tp) (htm : 0 < tm) (b : C3) (η : ℝ) :
    Dc ⟨0, tm / (tp + tm), -1⟩ b ⟨-η, 0, 1⟩ =
      -(tm / (tp + tm)) * (η * (Frame7.screenW tp tm b).2 + (Frame7.screenW tp tm b).1) := by
  have : tp + tm ≠ 0 := by positivity
  simp only [Dc, Frame7.screenW]; field_simp; ring

/-- **Lemma D** (velocities at `W`): for all `c ∈ ℝ²`, `a ∈ ℝ` there is a spin `ωc` with
`π(crossC ωc p) = ζ(p) c + a K J π(p)` for every frame point `p`.  Proof (PROOFS 38.3): spin `a`
about `W` gives `μ K J π`, `μ = -t- / (T - p)` (two explicit products `W × e1`, `W × e3`, then
`e1, e3, W` is a basis); and for `σ ⟂_G W` the map `σ ↦ π(Ω_σ W)` is injective hence onto `ℝ²`.
In Lean: solve the linear system for `ωc` explicitly (Cramer) and check by `field_simp; ring`. -/
theorem lemmaD {tp tm γ lam : ℝ} (h : EFam F tp tm γ lam) (c : ℝ × ℝ) (a : ℝ) :
    ∃ ωc : C3, ∀ p : C3,
      (Frame7.screenW tp tm (F.crossC ωc p)) =
        (F.zetaW tp tm p • c + a • Frame7.kjW tp tm γ (Frame7.screenW tp tm p)) := by
  have htp := h.tp_pos
  have htm := h.tm_pos
  have hγ := h.γ_pos
  have hlam := h.lam_pos
  have hκF := F.kap_ne
  have hF1 := Efam.F1 h.tp_pos h.tm_pos h.γ_pos h.γ_lt
  have hT : 0 < tp + tm := by linarith
  have hκ : Efam.kappa tp tm γ = (tp + tm) / (γ * tm) - 1 / (tp * tm) := rfl
  have hΦ : (1 - Efam.kappa tp tm γ * tm ^ 2) ≠ 0 := by linarith
  have hp : γ * (tp + tm) / (tp * tm) < tp + tm := by
    rw [div_lt_iff₀ (by positivity)]; nlinarith [h.γ_lt, hT]
  have hTp : (tp + tm) - γ * (tp + tm) / (tp * tm) ≠ 0 := by linarith
  have hd3 : lam * ((tp + tm) - γ * (tp + tm) / (tp * tm)) ≠ 0 := mul_ne_zero hlam.ne' hTp
  -- σ
  set N := lam * ((tp + tm) - γ * (tp + tm) / (tp * tm)) with hN
  set κ := Efam.kappa tp tm γ with hκs
  set s3 := N * (a / tm - c.1 / (tp + tm)) with hs3
  set s2 := (tm / (tp + tm)) * (N * (c.2 + κ * tm * c.1) / (1 - κ * tm ^ 2) - s3) with hs2
  set s1 := -(tp + tm) * s2 - tm * s3 - N * c.1 with hs1
  have hκ0 : Efam.kappa tp tm γ = (tp + tm) / (γ * tm) - 1 / (tp * tm) := rfl
  have hΦe : 1 - κ * tm ^ 2 = (tp + tm) * (γ - tp * tm) / (γ * tp) := by
    rw [hκ]; field_simp; ring
  have hγt : γ - tp * tm ≠ 0 := by linarith [h.γ_lt]
  have hγt2 : tp * tm - γ ≠ 0 := by linarith [h.γ_lt]
  have hZ : lam * (0 * 0) + lam * (γ * (tp + tm) / (tp * tm)) * (0 * (tm / (tp + tm)) + 0 * (tm / (tp + tm))) +
      lam * (γ * (tp + tm) / (tp * tm)) * (tp + tm) * (tm / (tp + tm) * (tm / (tp + tm))) + lam * γ * (-1 * -1)
      = lam * γ * (tp + tm) / tp := by field_simp; ring
  refine ⟨⟨s1 / F.kap, s2 / F.kap, s3 / F.kap⟩, fun q => ?_⟩
  have hden : F.a11 * F.a22 - F.a12 ^ 2 ≠ 0 := F.gram_pos.ne'
  have hgg : F.gg ≠ 0 := F.gg_pos.ne'
  have hGW : F.GG ⟨0, tm / (tp + tm), -1⟩ ⟨0, tm / (tp + tm), -1⟩ ≠ 0 := by
    have := F.GG_self_pos ⟨0, tm / (tp + tm), -1⟩ (Or.inr (Or.inr (by norm_num)))
    exact this.ne'
  simp only [Frame7.crossC, Frame7.screenW, Frame7.zetaW, Frame7.kjW, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  refine Prod.ext ?_ ?_
  all_goals
    simp only [Frame7.GG, Gf, h.ha11, h.ha12, h.ha22, h.hgg, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rw [hZ, hs1, hs2, hs3, hN, hΦe]
    simp only [hκ, hκ0]
    field_simp

    ring

/-- **Theorem E\* (core, normalised).**  There is a motion `(ωc, m)` and a tilt `d` such that
for all small `ε > 0` every vertex has a local certificate at the view `W + ε d`
(`σ = -1`).  Certificate (PROOFS 38.3): `a = (T-1)/(Tκ)`, `τ = (τ1, -1)`, `τ1 = a T/t- + s`,
`c = (s - τ1, 1)`, `σ0 = ε1 = s` (so `c = (-a d+, 1)` does not depend on `s`), `η = τ1/2`,
`d = (-η, 0, 1)`; the velocity table of 38.3 gives the 12 corner rows + the 4 triangle rows; each
test is `A + ε B` with `A > 0`, or `A = 0 ∧ B > 0` (edges through `W` itself: `v → m2-`, and for
`xb` the sides `m1+ → m2+`, `m2+ → v`), and the table rows C1-C5 are positive for small `s`
by F1-F3 (pick `s` by `eventually_pos_affine`, then `ε`). -/
theorem eStar_cert {tp tm γ lam : ℝ} (h : EFam F tp tm γ lam) :
    ∃ ωc m d : C3, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ j, F.FoCert (-1) (C3.tilt ⟨0, tm / (tp + tm), -1⟩ d ε) ωc m j := by
  have htp := h.tp_pos
  have htp1 := h.tp_lt
  have htm := h.tm_pos
  have htm1 := h.tm_lt
  have hT1 := h.T_gt
  have hγ := h.γ_pos
  have hγ1 := h.γ_lt
  have hT0 : 0 < tp + tm := by linarith
  have hF1 := Efam.F1 htp htm hγ hγ1
  obtain ⟨hF2, -⟩ := Efam.F2 htp htp1 htm htm1 hT1 hγ hγ1
  obtain ⟨hF3, hF3'⟩ := Efam.F3 htp htp1 htm htm1 hT1 hγ hγ1
  obtain ⟨κ, hκ⟩ : ∃ κ, Efam.kappa tp tm γ = κ := ⟨_, rfl⟩
  rw [hκ] at hF1 hF3
  have hκpos : 0 < κ := by
    by_contra hc
    push_neg at hc
    nlinarith [sq_nonneg tm]
  obtain ⟨a, ha⟩ : ∃ a, a = (tp + tm - 1) / ((tp + tm) * κ) := ⟨_, rfl⟩
  have hapos : 0 < a := by rw [ha]; apply div_pos <;> [linarith; positivity]
  have haκ : a * κ * (tp + tm) = tp + tm - 1 := by rw [ha]; field_simp
  obtain ⟨B, hB⟩ : ∃ B, B = 1 - tp * (tp + tm - 1) / (tp + tm) - a / tm := ⟨_, rfl⟩
  have hB2 : 2 - (tp + tm) < B := by
    have : Efam.bB tp tm γ = B := by
      unfold Efam.bB
      rw [hκ, hB, ha]; field_simp
    linarith
  have hF3a : a * (tp + tm) / tm ^ 2 < tp + tm - 1 := by
    have : (tp + tm - 1) / (κ * tm ^ 2) = a * (tp + tm) / tm ^ 2 := by
      rw [ha]; field_simp
    linarith
  -- the rows
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s ∧
      0 < (1 - tm) * (a * (κ * tm - 1 / tm)) + s * (-1) ∧
      0 < a * (2 - (tp + tm)) / tm + s * (-1) ∧
      0 < (1 - tp) * B + s * (-1) ∧
      0 < tm * B + s * (-1) ∧
      0 < (tm - a * (tp + tm) / tm) + s * (-1) := by
    have e0 : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
    refine e0.and ?_
    have hT2 : tp + tm < 2 := by linarith
    have p1 : 0 < κ * tm - 1 / tm := by
      rw [sub_pos, div_lt_iff₀ htm]; nlinarith
    have p3 : 0 < B := by linarith
    have p5 : 0 < tm - a * (tp + tm) / tm := by
      have : a * (tp + tm) / tm = tm * (a * (tp + tm) / tm ^ 2) := by field_simp
      rw [this]; nlinarith
    exact (eventually_pos_affine (A := (1 - tm) * (a * (κ * tm - 1 / tm))) (B := -1)
        (Or.inl (by have := sub_pos.2 htm1; positivity))).and
      ((eventually_pos_affine (A := a * (2 - (tp + tm)) / tm) (B := -1)
        (Or.inl (by have : 0 < 2 - (tp + tm) := by linarith
                    positivity))).and
      ((eventually_pos_affine (A := (1 - tp) * B) (B := -1)
        (Or.inl (by have := sub_pos.2 htp1; positivity))).and
      ((eventually_pos_affine (A := tm * B) (B := -1) (Or.inl (by positivity))).and
      (eventually_pos_affine (A := tm - a * (tp + tm) / tm) (B := -1) (Or.inl p5)))))
  obtain ⟨s, hs0, hC1, hC2, hC3, hC4, hC5⟩ := hev.exists
  obtain ⟨τ1, hτ1⟩ : ∃ τ1, τ1 = a * (tp + tm) / tm + s := ⟨_, rfl⟩
  have hτpos : 0 < τ1 := by rw [hτ1]; positivity
  have hτlt : τ1 < tm := by rw [hτ1]; linarith
  obtain ⟨ωc, hωc⟩ := F.lemmaD h (s - τ1, 1) a
  refine ⟨ωc, ⟨τ1, 0, -1⟩, ⟨-(τ1 / 2), 0, 1⟩, ?_⟩
  have velgen : ∀ q : C3, Frame7.screenW tp tm (F.velC ωc ⟨τ1, 0, -1⟩ q) =
      ((q.x + (tp + tm) * q.y - tp * q.z) / (tp + tm)) • (s - τ1, (1 : ℝ)) +
        a • Frame7.kjW tp tm γ (Frame7.screenW tp tm q) + (τ1, -1) := by
    intro q
    unfold Frame7.velC
    rw [sc_add, hωc, F.zeta_formula h]
    simp [Frame7.screenW]
  have hT : tp + tm ≠ 0 := by positivity
  have v5 : Frame7.screenW tp tm (F.velC ωc ⟨τ1, 0, -1⟩ (F.ptC 5)) = (τ1, -1) := by
    rw [velgen, h.p5]
    simp [Frame7.kjW, Frame7.screenW]
  have v2 : Frame7.screenW tp tm (F.velC ωc ⟨τ1, 0, -1⟩ (F.ptC 2)) = (s, 0) := by
    rw [velgen, h.p2]
    simp [Frame7.kjW, Frame7.screenW, hκ]
    field_simp
    constructor <;> ring
  have v6 : Frame7.screenW tp tm (F.velC ωc ⟨τ1, 0, -1⟩ (F.ptC 6)) =
      (s, a * (κ * tm - 1 / tm)) := by
    rw [velgen, h.p6]
    simp [Frame7.kjW, Frame7.screenW, hκ]
    field_simp
    constructor <;> ring
  have v3 : Frame7.screenW tp tm (F.velC ωc ⟨τ1, 0, -1⟩ (F.ptC 3)) =
      (s + a * (tp + tm - 2) / tm, 0) := by
    rw [velgen, h.p3]
    simp [Frame7.kjW, Frame7.screenW, hκ]
    field_simp
    constructor
    · rw [hτ1]; field_simp; ring
    · linear_combination haκ
  have v0 : Frame7.screenW tp tm (F.velC ωc ⟨τ1, 0, -1⟩ (F.ptC 0)) = (s, -B) := by
    rw [velgen, h.p0]
    simp [Frame7.kjW, Frame7.screenW, hκ]
    field_simp
    constructor
    · rw [hτ1]; field_simp; ring
    · rw [hB]; field_simp; linear_combination (tp * tm) * haκ
  have v1 : Frame7.screenW tp tm (F.velC ωc ⟨τ1, 0, -1⟩ (F.ptC 1)) =
      (s, a * (tp + tm) / tm ^ 2 - 1) := by
    rw [velgen, h.p1]
    simp [Frame7.kjW, Frame7.screenW, hκ]
    field_simp
    constructor
    · rw [hτ1]; field_simp; ring
    · ring
  have scp0 : Frame7.screenW tp tm (F.ptC 0) = (tp, 1) := by
    rw [h.p0]; simp [Frame7.screenW]
  have scp1 : Frame7.screenW tp tm (F.ptC 1) = (0, (tp + tm) / tm) := by
    rw [h.p1]; simp [Frame7.screenW]; field_simp; ring
  have scp2 : Frame7.screenW tp tm (F.ptC 2) = (0, 0) := by
    rw [h.p2]; simp [Frame7.screenW]; field_simp; ring
  have scp3 : Frame7.screenW tp tm (F.ptC 3) = (1, 0) := by
    rw [h.p3]; simp [Frame7.screenW]
  have scp4 : Frame7.screenW tp tm (F.ptC 4) = (0, (tp + tm) / tm) := by
    rw [h.p4]; simp [Frame7.screenW]
  have scp5 : Frame7.screenW tp tm (F.ptC 5) = (0, 0) := by
    rw [h.p5]; simp [Frame7.screenW]
  have scp6 : Frame7.screenW tp tm (F.ptC 6) = (tm, -1) := by
    rw [h.p6]; simp [Frame7.screenW]
  have hκtm : 0 < κ * tm - 1 / tm := by
    rw [sub_pos, div_lt_iff₀ htm]; nlinarith
  have vel5 : F.velC ωc ⟨τ1, 0, -1⟩ (F.ptC 5) = ⟨τ1, 0, -1⟩ := by
    simp [Frame7.velC, Frame7.crossC, h.p5, C3.add]
  have sub25 : (F.ptC 2).sub (F.ptC 5) = ⟨0, tm / (tp + tm), -1⟩ := by
    rw [h.p2, h.p5]; simp [C3.sub]
  have g53 : Good ⟨0, tm / (tp + tm), -1⟩ ⟨-(τ1 / 2), 0, 1⟩ ((F.ptC 5).sub (F.ptC 1)) (F.velC ωc ⟨τ1, 0, -1⟩ (F.ptC 5)) := by
    refine good_pos htp htm ?_
    simp only [sc_sub, scp0, scp1, scp2, scp3, scp4, scp5, scp6, v5, v2, v6, v3, v0, v1, cr, Prod.mk_sub_mk]
    have hR : 0 < (tp + tm) / tm * τ1 := by positivity
    refine lt_of_lt_of_eq hR ?_
    field_simp
    ring
  have g22 : Good ⟨0, tm / (tp + tm), -1⟩ ⟨-(τ1 / 2), 0, 1⟩ ((F.ptC 6).sub (F.ptC 2)) (F.velC ωc ⟨τ1, 0, -1⟩ (F.ptC 2)) := by
    refine good_pos htp htm ?_
    simp only [sc_sub, scp0, scp1, scp2, scp3, scp4, scp5, scp6, v5, v2, v6, v3, v0, v1, cr, Prod.mk_sub_mk]
    have hR : 0 < s := hs0
    refine lt_of_lt_of_eq hR ?_
    field_simp
    ring
  have g61 : Good ⟨0, tm / (tp + tm), -1⟩ ⟨-(τ1 / 2), 0, 1⟩ ((F.ptC 3).sub (F.ptC 6)) ((F.ptC 2).sub (F.ptC 6)) := by
    refine good_pos htp htm ?_
    simp only [sc_sub, scp0, scp1, scp2, scp3, scp4, scp5, scp6, v5, v2, v6, v3, v0, v1, cr, Prod.mk_sub_mk]
    have hR : (0:ℝ) < 1 := one_pos
    refine lt_of_lt_of_eq hR ?_
    field_simp
    ring
  have g62 : Good ⟨0, tm / (tp + tm), -1⟩ ⟨-(τ1 / 2), 0, 1⟩ ((F.ptC 3).sub (F.ptC 6)) (F.velC ωc ⟨τ1, 0, -1⟩ (F.ptC 6)) := by
    refine good_pos htp htm ?_
    simp only [sc_sub, scp0, scp1, scp2, scp3, scp4, scp5, scp6, v5, v2, v6, v3, v0, v1, cr, Prod.mk_sub_mk]
    have hR : 0 < (1 - tm) * (a * (κ * tm - 1 / tm)) + s * (-1) := hC1
    refine lt_of_lt_of_eq hR ?_
    field_simp
    ring
  have g63 : Good ⟨0, tm / (tp + tm), -1⟩ ⟨-(τ1 / 2), 0, 1⟩ ((F.ptC 6).sub (F.ptC 2)) (F.velC ωc ⟨τ1, 0, -1⟩ (F.ptC 6)) := by
    refine good_pos htp htm ?_
    simp only [sc_sub, scp0, scp1, scp2, scp3, scp4, scp5, scp6, v5, v2, v6, v3, v0, v1, cr, Prod.mk_sub_mk]
    have hR : 0 < tm * (a * (κ * tm - 1 / tm)) + s := by positivity
    refine lt_of_lt_of_eq hR ?_
    field_simp
    ring
  have g31 : Good ⟨0, tm / (tp + tm), -1⟩ ⟨-(τ1 / 2), 0, 1⟩ ((F.ptC 0).sub (F.ptC 3)) ((F.ptC 6).sub (F.ptC 3)) := by
    refine good_pos htp htm ?_
    simp only [sc_sub, scp0, scp1, scp2, scp3, scp4, scp5, scp6, v5, v2, v6, v3, v0, v1, cr, Prod.mk_sub_mk]
    have hR : 0 < 2 - (tp + tm) := by linarith
    refine lt_of_lt_of_eq hR ?_
    field_simp
    ring
  have g32 : Good ⟨0, tm / (tp + tm), -1⟩ ⟨-(τ1 / 2), 0, 1⟩ ((F.ptC 0).sub (F.ptC 3)) (F.velC ωc ⟨τ1, 0, -1⟩ (F.ptC 3)) := by
    refine good_pos htp htm ?_
    simp only [sc_sub, scp0, scp1, scp2, scp3, scp4, scp5, scp6, v5, v2, v6, v3, v0, v1, cr, Prod.mk_sub_mk]
    have hR : 0 < a * (2 - (tp + tm)) / tm + s * (-1) := hC2
    refine lt_of_lt_of_eq hR ?_
    field_simp
    ring
  have g33 : Good ⟨0, tm / (tp + tm), -1⟩ ⟨-(τ1 / 2), 0, 1⟩ ((F.ptC 3).sub (F.ptC 6)) (F.velC ωc ⟨τ1, 0, -1⟩ (F.ptC 3)) := by
    refine good_pos htp htm ?_
    simp only [sc_sub, scp0, scp1, scp2, scp3, scp4, scp5, scp6, v5, v2, v6, v3, v0, v1, cr, Prod.mk_sub_mk]
    have hR : 0 < a * (2 - (tp + tm)) / tm + s * (-1) := hC2
    refine lt_of_lt_of_eq hR ?_
    field_simp
    ring
  have g01 : Good ⟨0, tm / (tp + tm), -1⟩ ⟨-(τ1 / 2), 0, 1⟩ ((F.ptC 1).sub (F.ptC 0)) ((F.ptC 3).sub (F.ptC 0)) := by
    refine good_pos htp htm ?_
    simp only [sc_sub, scp0, scp1, scp2, scp3, scp4, scp5, scp6, v5, v2, v6, v3, v0, v1, cr, Prod.mk_sub_mk]
    have hR : 0 < tp * (tp + tm - 1) / tm := div_pos (mul_pos htp (by linarith)) htm
    refine lt_of_lt_of_eq hR ?_
    field_simp
    ring
  have g02 : Good ⟨0, tm / (tp + tm), -1⟩ ⟨-(τ1 / 2), 0, 1⟩ ((F.ptC 1).sub (F.ptC 0)) (F.velC ωc ⟨τ1, 0, -1⟩ (F.ptC 0)) := by
    refine good_pos htp htm ?_
    simp only [sc_sub, scp0, scp1, scp2, scp3, scp4, scp5, scp6, v5, v2, v6, v3, v0, v1, cr, Prod.mk_sub_mk]
    have hR : 0 < tp / tm * (tm * B + s * (-1)) := mul_pos (by positivity) hC4
    refine lt_of_lt_of_eq hR ?_
    field_simp
    ring
  have g03 : Good ⟨0, tm / (tp + tm), -1⟩ ⟨-(τ1 / 2), 0, 1⟩ ((F.ptC 0).sub (F.ptC 3)) (F.velC ωc ⟨τ1, 0, -1⟩ (F.ptC 0)) := by
    refine good_pos htp htm ?_
    simp only [sc_sub, scp0, scp1, scp2, scp3, scp4, scp5, scp6, v5, v2, v6, v3, v0, v1, cr, Prod.mk_sub_mk]
    have hR : 0 < (1 - tp) * B + s * (-1) := hC3
    refine lt_of_lt_of_eq hR ?_
    field_simp
    ring
  have g11 : Good ⟨0, tm / (tp + tm), -1⟩ ⟨-(τ1 / 2), 0, 1⟩ ((F.ptC 5).sub (F.ptC 1)) ((F.ptC 0).sub (F.ptC 1)) := by
    refine good_pos htp htm ?_
    simp only [sc_sub, scp0, scp1, scp2, scp3, scp4, scp5, scp6, v5, v2, v6, v3, v0, v1, cr, Prod.mk_sub_mk]
    have hR : 0 < (tp + tm) / tm * tp := by positivity
    refine lt_of_lt_of_eq hR ?_
    field_simp
    ring
  have g12 : Good ⟨0, tm / (tp + tm), -1⟩ ⟨-(τ1 / 2), 0, 1⟩ ((F.ptC 5).sub (F.ptC 1)) (F.velC ωc ⟨τ1, 0, -1⟩ (F.ptC 1)) := by
    refine good_pos htp htm ?_
    simp only [sc_sub, scp0, scp1, scp2, scp3, scp4, scp5, scp6, v5, v2, v6, v3, v0, v1, cr, Prod.mk_sub_mk]
    have hR : 0 < (tp + tm) / tm * s := by positivity
    refine lt_of_lt_of_eq hR ?_
    field_simp
    ring
  have g13 : Good ⟨0, tm / (tp + tm), -1⟩ ⟨-(τ1 / 2), 0, 1⟩ ((F.ptC 1).sub (F.ptC 0)) (F.velC ωc ⟨τ1, 0, -1⟩ (F.ptC 1)) := by
    refine good_pos htp htm ?_
    simp only [sc_sub, scp0, scp1, scp2, scp3, scp4, scp5, scp6, v5, v2, v6, v3, v0, v1, cr, Prod.mk_sub_mk]
    have hR : 0 < tp / tm * ((tm - a * (tp + tm) / tm) + s * (-1)) := mul_pos (by positivity) hC5
    refine lt_of_lt_of_eq hR ?_
    field_simp
    ring
  have g41 : Good ⟨0, tm / (tp + tm), -1⟩ ⟨-(τ1 / 2), 0, 1⟩ ((F.ptC 0).sub (F.ptC 5)) ((F.ptC 1).sub (F.ptC 5)) := by
    refine good_pos htp htm ?_
    simp only [sc_sub, scp0, scp1, scp2, scp3, scp4, scp5, scp6, v5, v2, v6, v3, v0, v1, cr, Prod.mk_sub_mk]
    have hR : 0 < tp * (tp + tm) / tm := by positivity
    refine lt_of_lt_of_eq hR ?_
    field_simp
    ring
  have g42 : Good ⟨0, tm / (tp + tm), -1⟩ ⟨-(τ1 / 2), 0, 1⟩ ((F.ptC 0).sub (F.ptC 5)) ((F.ptC 4).sub (F.ptC 5)) := by
    refine good_pos htp htm ?_
    simp only [sc_sub, scp0, scp1, scp2, scp3, scp4, scp5, scp6, v5, v2, v6, v3, v0, v1, cr, Prod.mk_sub_mk]
    have hR : 0 < tp * (tp + tm) / tm := by positivity
    refine lt_of_lt_of_eq hR ?_
    field_simp
    ring
  have g51 : Good ⟨0, tm / (tp + tm), -1⟩ ⟨-(τ1 / 2), 0, 1⟩ ((F.ptC 2).sub (F.ptC 5)) ((F.ptC 1).sub (F.ptC 5)) := by
    right
    exact ⟨by simp only [Dc, C3.sub, h.p2, h.p5, h.p1]; ring, by simp only [Dc, C3.sub, h.p2, h.p5, h.p1]; exact lt_of_lt_of_eq (half_pos hτpos) (by field_simp; ring)⟩
  have g52 : Good ⟨0, tm / (tp + tm), -1⟩ ⟨-(τ1 / 2), 0, 1⟩ ((F.ptC 2).sub (F.ptC 5)) (F.velC ωc ⟨τ1, 0, -1⟩ (F.ptC 5)) := by
    right
    rw [vel5, sub25]
    constructor
    · simp only [Dc]; ring
    · rw [Dc_Wbd htp htm]
      simp only [Frame7.screenW]
      have : 0 < tm / (tp + tm) := by positivity
      nlinarith
  have g21 : Good ⟨0, tm / (tp + tm), -1⟩ ⟨-(τ1 / 2), 0, 1⟩ ((F.ptC 6).sub (F.ptC 2)) ((F.ptC 5).sub (F.ptC 2)) := by
    right
    exact ⟨by simp only [Dc, C3.sub, h.p2, h.p5, h.p6]; ring, by simp only [Dc, C3.sub, h.p2, h.p5, h.p6]; exact lt_of_lt_of_eq (mul_pos (by positivity : 0 < tm / (tp + tm)) (by linarith : 0 < tm - τ1 / 2)) (by field_simp; ring)⟩
  have g23 : Good ⟨0, tm / (tp + tm), -1⟩ ⟨-(τ1 / 2), 0, 1⟩ ((F.ptC 2).sub (F.ptC 5)) (F.velC ωc ⟨τ1, 0, -1⟩ (F.ptC 2)) := by
    right
    rw [sub25]
    constructor
    · simp only [Dc]; ring
    · rw [Dc_Wbd htp htm, v2]
      have : 0 < tm / (tp + tm) := by positivity
      simp only
      nlinarith
  have g43 : Good ⟨0, tm / (tp + tm), -1⟩ ⟨-(τ1 / 2), 0, 1⟩ ((F.ptC 1).sub (F.ptC 0)) ((F.ptC 4).sub (F.ptC 0)) := by
    right
    exact ⟨by simp only [Dc, C3.sub, h.p1, h.p0, h.p4, h.p5]; field_simp; ring, by simp only [Dc, C3.sub, h.p1, h.p0, h.p4, h.p5]; exact lt_of_lt_of_eq (mul_pos (by positivity : 0 < tp / (tp + tm)) (by linarith : 0 < tm - τ1 / 2)) (by field_simp; ring)⟩
  have g44 : Good ⟨0, tm / (tp + tm), -1⟩ ⟨-(τ1 / 2), 0, 1⟩ ((F.ptC 5).sub (F.ptC 1)) ((F.ptC 4).sub (F.ptC 1)) := by
    right
    exact ⟨by simp only [Dc, C3.sub, h.p1, h.p5, h.p4]; field_simp; ring, by simp only [Dc, C3.sub, h.p1, h.p5, h.p4]; exact lt_of_lt_of_eq (half_pos hτpos) (by field_simp; ring)⟩
  refine Filter.eventually_all.2 fun j => ?_
  fin_cases j
  · filter_upwards [ev_of_good g01, ev_of_good g02, ev_of_good g03] with ε a b c
    exact Or.inl ⟨3, 1, a, b, c⟩
  · filter_upwards [ev_of_good g11, ev_of_good g12, ev_of_good g13] with ε a b c
    exact Or.inl ⟨0, 5, a, b, c⟩
  · filter_upwards [ev_of_good g21, ev_of_good g22, ev_of_good g23] with ε a b c
    exact Or.inl ⟨5, 6, a, b, c⟩
  · filter_upwards [ev_of_good g31, ev_of_good g32, ev_of_good g33] with ε a b c
    exact Or.inl ⟨6, 0, a, b, c⟩
  · filter_upwards [ev_of_good g41, ev_of_good g42, ev_of_good g43, ev_of_good g44]
      with ε a b c d
    exact Or.inr ⟨5, 0, 1, a, b, c, d⟩
  · filter_upwards [ev_of_good g51, ev_of_good g52, ev_of_good g53] with ε a b c
    exact Or.inl ⟨1, 2, a, b, c⟩
  · filter_upwards [ev_of_good g61, ev_of_good g62, ev_of_good g63] with ε a b c
    exact Or.inl ⟨2, 3, a, b, c⟩

/-- **Theorem E\*** for the normalised family (bridge `rupert_of_foCert_eventually`). -/
theorem rupert_of_EFam {tp tm γ lam : ℝ} (h : EFam F tp tm γ lam) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨ωc, m, d, hd⟩ := F.eStar_cert h
  exact F.rupert_of_foCert_eventually (-1) (Or.inr rfl) ⟨0, tm / (tp + tm), -1⟩ d ωc m
    (Or.inr (Or.inr (by norm_num))) hd

end Frame7

namespace Frame18
variable {x : Fin 7 → ℝ³} (F : Frame18 x)

set_option maxHeartbeats 1600000 in
/-- **`E_W` is the normalised family** (PROOFS 37.2 "E_W explicitly"): from `EW` derive
`s± = t±/T`, `h+ = h- = k+ = k- =: h`, `A12 = g h^2 T/(t+ t-)`, `A22 = A12 T`, then
`F.toFrame7.scaleE h` is an `EFam` with `tp, tm = S.tp, S.tm`, `lam = a11`,
`γ = g h^2 / a11`; `γ < t+ t-` from `A12 < A11` (`γ < t+ t- / T`).  Algebra on `Shape18`
(`dp_mul`, `bp_mul`, ... lemmas of `CaseC18Alg`). -/
theorem EW_toEFam (hE : F.EW) :
    ∃ (tp tm γ lam h : ℝ) (hh : 0 < h), EFam (F.toFrame7.scaleE h hh) tp tm γ lam := by
  obtain ⟨⟨⟨hdp, -, -, -, hg, h6, h7, h8⟩, hcd, hs⟩, hams, hts⟩ := hE
  have hA12 : 0 < F.a12 := F.A12_pos
  have hA11 : 0 < F.a11 := lt_of_lt_of_le F.A12_pos F.A12_le_A11
  have hgg : 0 < F.gg := F.g_pos
  have tp0 := F.S.tp_pos
  have tp1 := F.S.tp_lt
  have tm0 := F.S.tm_pos
  have tm1 := F.S.tm_lt
  have hsm : F.S.sm = 1 - F.S.sp := by linarith
  have e2 : F.S.sp * (F.S.tp + F.S.tm) = F.S.tp := by rw [hsm] at hts; linarith
  have e1 : F.S.sm * (F.S.tp + F.S.tm) = F.S.tm := by rw [hsm]; linarith
  have amm := F.S.am_mul
  have app := F.S.ap_mul
  have hmp : F.S.hm = F.S.hp := by
    linear_combination (-1 : ℝ) * amm + app + (F.S.tp + F.S.tm) * hams - F.S.am * e1 + F.S.ap * e2
  have dpm := F.S.dp_mul
  have cmm := F.S.cm_mul
  rw [← hsm] at dpm
  rw [hcd] at cmm
  have hkk : F.S.km = F.S.kp := by linarith
  have hk : F.S.kp * (F.S.tp + F.S.tm) = F.S.hp * (F.S.tp + F.S.tm) := by
    calc F.S.kp * (F.S.tp + F.S.tm) = F.S.dp * F.S.sm * (F.S.tp + F.S.tm) := by rw [dpm]
      _ = F.S.dp * F.S.tm := by rw [mul_assoc, e1]
      _ = (F.S.ap + F.S.am) * F.S.tp * F.S.tm := by rw [hdp]; rfl
      _ = (F.S.ap * F.S.tp) * F.S.tm + (F.S.am * F.S.tm) * F.S.tp := by ring
      _ = F.S.hp * F.S.tm + F.S.hm * F.S.tp := by rw [app, amm]
      _ = F.S.hp * (F.S.tp + F.S.tm) := by rw [hmp]; ring
  have hkh : F.S.kp = F.S.hp := mul_right_cancel₀ (by linarith : F.S.tp + F.S.tm ≠ 0) hk
  have hdpt : F.S.dp * F.S.tm = F.S.hp * (F.S.tp + F.S.tm) := by
    calc F.S.dp * F.S.tm = (F.S.ap + F.S.am) * F.S.tp * F.S.tm := by rw [hdp]; rfl
      _ = (F.S.ap * F.S.tp) * F.S.tm + (F.S.am * F.S.tm) * F.S.tp := by ring
      _ = F.S.hp * (F.S.tp + F.S.tm) := by rw [app, amm, hmp]; ring
  have hhp := F.S.hp_pos
  have h22 : F.a22 = F.a12 * (F.S.tp + F.S.tm) := by
    have hle : F.a22 * F.S.am = F.a12 * F.S.dp := le_antisymm h8 (by rw [← hcd]; exact h7)
    have : (F.a22 - F.a12 * (F.S.tp + F.S.tm)) * F.S.hp = 0 := by
      have : F.a22 * F.S.am * F.S.tm = F.a12 * F.S.dp * F.S.tm := by rw [hle]
      have amm' : F.S.am * F.S.tm = F.S.hp := by rw [amm, hmp]
      linear_combination (-F.a22) * amm' + this + F.a12 * hdpt
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  have dmm := F.S.dm_mul
  rw [hsm, sub_sub_cancel, hkk, hkh] at dmm
  have hmmp : F.S.hp = F.S.hp := rfl
  have h12 : F.a12 * (F.S.tp * F.S.tm) = F.gg * F.S.hp ^ 2 * (F.S.tp + F.S.tm) := by
    have hdt : F.S.dm * F.S.tp = F.S.hp * (F.S.tp + F.S.tm) := by
      calc F.S.dm * F.S.tp = F.S.dm * (F.S.sp * (F.S.tp + F.S.tm)) := by rw [e2]
        _ = (F.S.dm * F.S.sp) * (F.S.tp + F.S.tm) := by ring
        _ = _ := by rw [dmm]
    calc F.a12 * (F.S.tp * F.S.tm) = F.gg * F.S.am * F.S.dm * (F.S.tp * F.S.tm) := by rw [hg]
      _ = F.gg * (F.S.am * F.S.tm) * (F.S.dm * F.S.tp) := by ring
      _ = _ := by rw [amm, hdt, hmp]; ring
  have hlt : F.a12 < F.a11 := by
    have : 0 < F.gg * F.S.am * F.S.hp := by
      have := F.S.am_pos; positivity
    nlinarith
  have hT1 : 1 < F.S.tp + F.S.tm := by
    have := F.S.roof_p
    rw [← hsm, hkh] at this
    have hsm0 : 0 < F.S.sm := F.S.sm_pos
    rw [div_lt_div_iff₀ hsm0 (by linarith)] at this
    have h1 : 1 - F.S.tp < F.S.sm := by nlinarith
    nlinarith
  have hγ0 : 0 < F.gg * F.S.hp ^ 2 / F.a11 := by positivity
  have hγT : F.gg * F.S.hp ^ 2 / F.a11 * (F.S.tp + F.S.tm) < F.S.tp * F.S.tm := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hA11]
    have := mul_lt_mul_of_pos_right hlt (mul_pos tp0 tm0)
    linarith
  have hγ1 : F.gg * F.S.hp ^ 2 / F.a11 < F.S.tp * F.S.tm := by
    have key : ∀ g T P : ℝ, 0 < g → 1 < T → g * T < P → g < P := by
      intro g T P h1 h2 h3; exact lt_of_le_of_lt (le_mul_of_one_le_right h1.le h2.le) h3
    exact key _ _ _ hγ0 hT1 hγT
  have hT0 : F.S.tp + F.S.tm ≠ 0 := by linarith
  have hsp : F.S.sp = F.S.tp / (F.S.tp + F.S.tm) := eq_div_of_mul_eq hT0 e2
  have hsm' : F.S.sm = F.S.tm / (F.S.tp + F.S.tm) := eq_div_of_mul_eq hT0 e1
  refine ⟨F.S.tp, F.S.tm, F.gg * F.S.hp ^ 2 / F.a11, F.a11, F.S.hp, hhp, ?_⟩
  refine ⟨tp0, tp1, tm0, tm1, hT1, hγ0, hγ1, hA11, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [F.toFrame7.scaleE_ptC, F.ptC_0]
    simp [hhp.ne']
  · rw [F.toFrame7.scaleE_ptC, F.ptC_1]
    simp [hkh, hsp, hhp.ne']
  · rw [F.toFrame7.scaleE_ptC, F.ptC_2]
    simp [hkk, hkh, hsm', hhp.ne']
  · rw [F.toFrame7.scaleE_ptC, F.ptC_3]; simp
  · rw [F.toFrame7.scaleE_ptC, F.ptC_4]; simp
  · rw [F.toFrame7.scaleE_ptC, F.ptC_5]; simp
  · rw [F.toFrame7.scaleE_ptC, F.ptC_6]
    simp [hmp, hhp.ne']
  · show F.a11 = F.a11
    rfl
  · show F.a12 = F.a11 * (F.gg * F.S.hp ^ 2 / F.a11 * (F.S.tp + F.S.tm) / (F.S.tp * F.S.tm))
    field_simp
    linarith
  · show F.a22 = F.a11 * (F.gg * F.S.hp ^ 2 / F.a11 * (F.S.tp + F.S.tm) / (F.S.tp * F.S.tm)) * (F.S.tp + F.S.tm)
    rw [h22]
    field_simp
    linarith
  · rw [F.toFrame7.scaleE_gg]
    show F.S.hp ^ 2 * F.gg = F.a11 * (F.gg * F.S.hp ^ 2 / F.a11)
    field_simp

/-- **Theorem E\*** : every point of `E_W` is Rupert. -/
theorem thmEstar (hE : F.EW) : IsRupert (Finset.univ.image x) := by
  obtain ⟨tp, tm, γ, lam, h, hh, hF⟩ := F.EW_toEFam hE
  exact (F.toFrame7.scaleE h hh).rupert_of_EFam hF

/-- **`L_M'` is Rupert.**  `c- ≤ d+` holds on `L_M'` (`A12 c- ≤ A22 a- ≤ A12 d+`, `A12 > 0`);
`c- < d+`: Corollary E1; `c- = d+`: Corollary E2, then `Q`: Theorem W, then `E_W`: Theorem E*. -/
theorem LMp_isRupert (hL : F.LMp) : IsRupert (Finset.univ.image x) := by
  obtain ⟨-, -, -, -, -, -, h7, h8⟩ := id hL
  have hA12 : 0 < F.a12 := F.A12_pos
  have hcd : F.S.cm ≤ F.S.dp := by
    have := le_trans h7 h8
    exact le_of_mul_le_mul_left this hA12
  rcases hcd.lt_or_eq with hlt | heq
  · exact F.thmE1 hL hlt
  rcases F.thmE2 hL heq with h | hs
  · exact h
  rcases F.thmW ⟨hL, heq, hs⟩ with h | ⟨e1, e2⟩
  · exact h
  exact F.thmEstar ⟨⟨hL, heq, hs⟩, e1, e2⟩

end Frame18

/-! ### Final assembly: no special set is left in type 18 -/

/-- **`CaseC18Special' x` is Rupert.**  (Disjunct 1: `isRupert_of_D1`; 2: `LMp_isRupert`; 3: its
`Z`-image; 4: `thmCz`; 5: `thmC`.)  It closes the type-18 branch of the
skeleton `Minimality.lean` (`by_cases hrest : CaseC18Special' x`, first branch):
`exact hN.2 (Minimality.CaseC18.CaseC18Special'.isRupert hrest)`. -/
theorem CaseC18Special'.isRupert {x : Fin 7 → ℝ³} (h : CaseC18Special' x) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨F, h1 | h2 | h3 | h4 | h5⟩ := h
  · obtain ⟨heq, n1, n2, -, -, A, -⟩ := h1
    exact F.isRupert_of_D1 heq n1 n2 A
  · exact F.LMp_isRupert h2
  · have h3' : F.zFrame.LMp := by
      unfold Frame18.LMp
      rw [F.zFrame_gg, F.zFrame_A1, F.zFrame_a12, F.zFrame_a11, F.zFrame_a22]
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := h3
      exact ⟨a1, a2, a4, a3, a5, a6, a7, a8⟩
    exact rupert_of_z (F.zFrame.LMp_isRupert h3')
  · obtain ⟨hab, hac, h22, hg, -⟩ := h4
    exact F.thmCz hab hac h22 hg
  · obtain ⟨hab, hac, h22, hg, -⟩ := h5
    exact F.thmC (F.a12_lt_a11_of_eq_a22 h22) hab hac h22 hg

end Minimality.CaseC18

end
