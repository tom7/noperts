module

public import Minimality.Type02A

@[expose] public section

namespace Minimality.CaseC18
open Finset Filter Minimality.CaseC09
open scoped RealInnerProductSpace Topology

set_option hygiene false in
macro "stfin2" : tactic => `(tactic| first
  | stfin
  | (right; refine ⟨by ring, ?_⟩; nlinarith [mul_pos htp a1, mul_pos htm a3, mul_pos hsp a2, mul_pos hsm a4])
  | (left; nlinarith [mul_pos htp a1, mul_pos htm a3, mul_pos hsp a2, mul_pos hsm a4])
  | nlinarith [mul_pos htp a1, mul_pos htm a3, mul_pos hsp a2, mul_pos hsm a4])

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
theorem cyc_V1B5 (tp tm sp sm κp κm : ℝ) (htp : 0 < tp) (htp1 : tp < 1) (htm : 0 < tm) (htm1 : tm < 1)
    (hsp : 0 < sp) (hsp1 : sp < 1) (hsm : 0 < sm) (hsm1 : sm < 1) (hκp : 0 < κp) (hκm : 0 < κm)
    (hA : sp = tp) (hB : tm < sm) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      CaseC09.ST (-1) ⟨-1, 1, 0⟩ ⟨1, 0, 0⟩
        ((quint (ptv tp tm sp sm κp κm 5) (ptv tp tm sp sm κp κm 3) (ptv tp tm sp sm κp κm 0) (ptv tp tm sp sm κp κm 1) (ptv tp tm sp sm κp κm 2) (i + 1)).sub (quint (ptv tp tm sp sm κp κm 5) (ptv tp tm sp sm κp κm 3) (ptv tp tm sp sm κp κm 0) (ptv tp tm sp sm κp κm 1) (ptv tp tm sp sm κp κm 2) i)) ((quint (ptv tp tm sp sm κp κm 5) (ptv tp tm sp sm κp κm 3) (ptv tp tm sp sm κp κm 0) (ptv tp tm sp sm κp κm 1) (ptv tp tm sp sm κp κm 2) j).sub (quint (ptv tp tm sp sm κp κm 5) (ptv tp tm sp sm κp κm 3) (ptv tp tm sp sm κp κm 0) (ptv tp tm sp sm κp κm 1) (ptv tp tm sp sm κp κm 2) i)) := by
  have a1 := sub_pos.2 htp1
  have a2 := sub_pos.2 hsp1
  have a3 := sub_pos.2 htm1
  have a4 := sub_pos.2 hsm1
  have a5 := sub_pos.2 hB
  have a6 := a1
  subst hA
  obtain ⟨b0, b1, b2, b3, b4⟩ := z5a
  intro i j h1 h2
  rcases z5c i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5c j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [CaseC09.ST, Dc, C3.sub, ptv, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    norm_num
    stfin

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
theorem rest_V1B5 (tp tm sp sm κp κm : ℝ) (htp : 0 < tp) (htp1 : tp < 1) (htm : 0 < tm) (htm1 : tm < 1)
    (hsp : 0 < sp) (hsp1 : sp < 1) (hsm : 0 < sm) (hsm1 : sm < 1) (hκp : 0 < κp) (hκm : 0 < κm)
    (hA : sp = tp) (hB : tm < sm) (j' : Fin 7) (hw : j' = 4 ∨ j' = 6) :
    ∀ i : ZMod 5,
      CaseC09.ST (-1) ⟨-1, 1, 0⟩ ⟨1, 0, 0⟩
        ((quint (ptv tp tm sp sm κp κm 5) (ptv tp tm sp sm κp κm 3) (ptv tp tm sp sm κp κm 0) (ptv tp tm sp sm κp κm 1) (ptv tp tm sp sm κp κm 2) (i + 1)).sub (quint (ptv tp tm sp sm κp κm 5) (ptv tp tm sp sm κp κm 3) (ptv tp tm sp sm κp κm 0) (ptv tp tm sp sm κp κm 1) (ptv tp tm sp sm κp κm 2) i)) ((ptv tp tm sp sm κp κm j').sub (quint (ptv tp tm sp sm κp κm 5) (ptv tp tm sp sm κp κm 3) (ptv tp tm sp sm κp κm 0) (ptv tp tm sp sm κp κm 1) (ptv tp tm sp sm κp κm 2) i)) := by
  have a1 := sub_pos.2 htp1
  have a2 := sub_pos.2 hsp1
  have a3 := sub_pos.2 htm1
  have a4 := sub_pos.2 hsm1
  have a5 := sub_pos.2 hB
  have a6 := a1
  subst hA
  obtain ⟨b0, b1, b2, b3, b4⟩ := z5a
  intro i
  rcases hw with rfl | rfl <;>
  rcases z5c i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, ptv, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    norm_num
    stfin

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
theorem cyc_V1B6 (tp tm sp sm κp κm : ℝ) (htp : 0 < tp) (htp1 : tp < 1) (htm : 0 < tm) (htm1 : tm < 1)
    (hsp : 0 < sp) (hsp1 : sp < 1) (hsm : 0 < sm) (hsm1 : sm < 1) (hκp : 0 < κp) (hκm : 0 < κm)
    (hA : sp = tp) (hB : sm < tm) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      CaseC09.ST (-1) ⟨-1, 1, 0⟩ ⟨-1, 0, 0⟩
        ((quint (ptv tp tm sp sm κp κm 6) (ptv tp tm sp sm κp κm 4) (ptv tp tm sp sm κp κm 1) (ptv tp tm sp sm κp κm 0) (ptv tp tm sp sm κp κm 2) (i + 1)).sub (quint (ptv tp tm sp sm κp κm 6) (ptv tp tm sp sm κp κm 4) (ptv tp tm sp sm κp κm 1) (ptv tp tm sp sm κp κm 0) (ptv tp tm sp sm κp κm 2) i)) ((quint (ptv tp tm sp sm κp κm 6) (ptv tp tm sp sm κp κm 4) (ptv tp tm sp sm κp κm 1) (ptv tp tm sp sm κp κm 0) (ptv tp tm sp sm κp κm 2) j).sub (quint (ptv tp tm sp sm κp κm 6) (ptv tp tm sp sm κp κm 4) (ptv tp tm sp sm κp κm 1) (ptv tp tm sp sm κp κm 0) (ptv tp tm sp sm κp κm 2) i)) := by
  have a1 := sub_pos.2 htp1
  have a2 := sub_pos.2 hsp1
  have a3 := sub_pos.2 htm1
  have a4 := sub_pos.2 hsm1
  have a5 := sub_pos.2 hB
  have a6 := a1
  subst hA
  obtain ⟨b0, b1, b2, b3, b4⟩ := z5a
  intro i j h1 h2
  rcases z5c i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5c j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [CaseC09.ST, Dc, C3.sub, ptv, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    norm_num
    stfin

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
theorem rest_V1B6 (tp tm sp sm κp κm : ℝ) (htp : 0 < tp) (htp1 : tp < 1) (htm : 0 < tm) (htm1 : tm < 1)
    (hsp : 0 < sp) (hsp1 : sp < 1) (hsm : 0 < sm) (hsm1 : sm < 1) (hκp : 0 < κp) (hκm : 0 < κm)
    (hA : sp = tp) (hB : sm < tm) (j' : Fin 7) (hw : j' = 3 ∨ j' = 5) :
    ∀ i : ZMod 5,
      CaseC09.ST (-1) ⟨-1, 1, 0⟩ ⟨-1, 0, 0⟩
        ((quint (ptv tp tm sp sm κp κm 6) (ptv tp tm sp sm κp κm 4) (ptv tp tm sp sm κp κm 1) (ptv tp tm sp sm κp κm 0) (ptv tp tm sp sm κp κm 2) (i + 1)).sub (quint (ptv tp tm sp sm κp κm 6) (ptv tp tm sp sm κp κm 4) (ptv tp tm sp sm κp κm 1) (ptv tp tm sp sm κp κm 0) (ptv tp tm sp sm κp κm 2) i)) ((ptv tp tm sp sm κp κm j').sub (quint (ptv tp tm sp sm κp κm 6) (ptv tp tm sp sm κp κm 4) (ptv tp tm sp sm κp κm 1) (ptv tp tm sp sm κp κm 0) (ptv tp tm sp sm κp κm 2) i)) := by
  have a1 := sub_pos.2 htp1
  have a2 := sub_pos.2 hsp1
  have a3 := sub_pos.2 htm1
  have a4 := sub_pos.2 hsm1
  have a5 := sub_pos.2 hB
  have a6 := a1
  subst hA
  obtain ⟨b0, b1, b2, b3, b4⟩ := z5a
  intro i
  rcases hw with rfl | rfl <;>
  rcases z5c i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, ptv, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    norm_num
    stfin

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
/-- Pure-real robust unimodality of the 5-cycle `![p0, p1, p2, p3, p4]` with `p3` the minimum, `p1` the maximum, and the
two monotone paths `p3 < p2 < p1`, `p3 < p4 < p0 < p1`. -/
theorem robust5_B {p0 p1 p2 p3 p4 : ℝ} (h1 : p3 < p2) (h2 : p2 < p1) (h3 : p3 < p4) (h4 : p4 < p0) (h5 : p0 < p1) :
    IsRobustUnimodal (k := 5) (fun i : ZMod 5 => ![p0, p1, p2, p3, p4] i) := by
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
set_option maxHeartbeats 1000000 in
theorem cyc_V12 (tp tm sp sm κp κm : ℝ) (htp : 0 < tp) (htp1 : tp < 1) (htm : 0 < tm) (htm1 : tm < 1)
    (hsp : 0 < sp) (hsp1 : sp < 1) (hsm : 0 < sm) (hsm1 : sm < 1) (hκp : 0 < κp) (hκm : 0 < κm)
    (hA : sp = tp) (hB : sm = tm) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      CaseC09.ST (-1) ⟨-1, 1, 0⟩ ⟨0, 0, -1⟩
        ((quint (ptv tp tm sp sm κp κm 5) (ptv tp tm sp sm κp κm 3) (ptv tp tm sp sm κp κm 4) (ptv tp tm sp sm κp κm 1) (ptv tp tm sp sm κp κm 2) (i + 1)).sub (quint (ptv tp tm sp sm κp κm 5) (ptv tp tm sp sm κp κm 3) (ptv tp tm sp sm κp κm 4) (ptv tp tm sp sm κp κm 1) (ptv tp tm sp sm κp κm 2) i)) ((quint (ptv tp tm sp sm κp κm 5) (ptv tp tm sp sm κp κm 3) (ptv tp tm sp sm κp κm 4) (ptv tp tm sp sm κp κm 1) (ptv tp tm sp sm κp κm 2) j).sub (quint (ptv tp tm sp sm κp κm 5) (ptv tp tm sp sm κp κm 3) (ptv tp tm sp sm κp κm 4) (ptv tp tm sp sm κp κm 1) (ptv tp tm sp sm κp κm 2) i)) := by
  have a1 := sub_pos.2 htp1
  have a2 := sub_pos.2 hsp1
  have a3 := sub_pos.2 htm1
  have a4 := sub_pos.2 hsm1
  have a5 := a1
  have a6 := a3
  subst hA hB
  obtain ⟨b0, b1, b2, b3, b4⟩ := z5a
  intro i j h1 h2
  rcases z5c i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5c j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [CaseC09.ST, Dc, C3.sub, ptv, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    norm_num <;>
    stfin2

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
theorem rest_V12 (tp tm sp sm κp κm : ℝ) (htp : 0 < tp) (htp1 : tp < 1) (htm : 0 < tm) (htm1 : tm < 1)
    (hsp : 0 < sp) (hsp1 : sp < 1) (hsm : 0 < sm) (hsm1 : sm < 1) (hκp : 0 < κp) (hκm : 0 < κm)
    (hA : sp = tp) (hB : sm = tm) (j' : Fin 7) (hw : j' = 0 ∨ j' = 6) :
    ∀ i : ZMod 5,
      CaseC09.ST (-1) ⟨-1, 1, 0⟩ ⟨0, 0, -1⟩
        ((quint (ptv tp tm sp sm κp κm 5) (ptv tp tm sp sm κp κm 3) (ptv tp tm sp sm κp κm 4) (ptv tp tm sp sm κp κm 1) (ptv tp tm sp sm κp κm 2) (i + 1)).sub (quint (ptv tp tm sp sm κp κm 5) (ptv tp tm sp sm κp κm 3) (ptv tp tm sp sm κp κm 4) (ptv tp tm sp sm κp κm 1) (ptv tp tm sp sm κp κm 2) i)) ((ptv tp tm sp sm κp κm j').sub (quint (ptv tp tm sp sm κp κm 5) (ptv tp tm sp sm κp κm 3) (ptv tp tm sp sm κp κm 4) (ptv tp tm sp sm κp κm 1) (ptv tp tm sp sm κp κm 2) i)) := by
  have a1 := sub_pos.2 htp1
  have a2 := sub_pos.2 hsp1
  have a3 := sub_pos.2 htm1
  have a4 := sub_pos.2 hsm1
  have a5 := a1
  have a6 := a3
  subst hA hB
  obtain ⟨b0, b1, b2, b3, b4⟩ := z5a
  intro i
  rcases hw with rfl | rfl <;>
  rcases z5c i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, ptv, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    norm_num <;>
    stfin2

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
/-- Pure-real robust unimodality of the 5-cycle `![p0, p1, p2, p3, p4]` with `p1` the minimum, `p2` the maximum (adjacent) and the monotone path `p1 < p0 < p4 < p3 < p2`. -/
theorem robust5_C {p0 p1 p2 p3 p4 : ℝ} (h1 : p1 < p0) (h2 : p0 < p4) (h3 : p4 < p3) (h4 : p3 < p2) :
    IsRobustUnimodal (k := 5) (fun i : ZMod 5 => ![p0, p1, p2, p3, p4] i) := by
  have hB : ∀ B : ZMod 5, B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by decide
  refine ⟨?_, ?_, ?_⟩
  · intro B a b c d hab hbc hcd hdk
    interval_cases d <;> interval_cases c <;> (try omega) <;> interval_cases b <;> (try omega) <;> interval_cases a <;> (try omega) <;> rcases hB B with rfl | rfl | rfl | rfl | rfl <;> norm_num <;> intros <;> skip <;> linarith
  · intro i j l hij hjl hil e1 e2
    rcases hB i with rfl | rfl | rfl | rfl | rfl <;> rcases hB j with rfl | rfl | rfl | rfl | rfl <;> rcases hB l with rfl | rfl | rfl | rfl | rfl <;> simp at hij hjl hil <;> norm_num at e1 e2 <;> skip <;> linarith
  · intro B a b c d hab hbc hcd hdk e
    interval_cases d <;> interval_cases c <;> (try omega) <;> interval_cases b <;> (try omega) <;> interval_cases a <;> (try omega) <;> rcases hB B with rfl | rfl | rfl | rfl | rfl <;> norm_num at e ⊢ <;> intros <;> skip <;> constructor <;> intro hh <;> linarith

namespace Frame02
variable {x : Fin 7 → ℝ³} (F : Frame02 x)

theorem acute_V1B5_pf (h1 : gA12 x < gA11 x) (h2 : gA12 x < gA22 x)
    (hA : F.S.tp = F.S.sp) (hB : F.S.tm < F.S.sm) : IsRupert (Finset.univ.image x) := by
  obtain ⟨κp, κm, hκp, hκm, hpt⟩ := F.ptC_ptv
  have hα : 0 < gA11 x - gA12 x := by linarith
  have hγ : 0 < gA22 x - gA12 x := by linarith
  have hc : ∀ i, F.toFrame7.ptC (quint ((5 : Fin 7)) 3 0 1 2 i) =
      quint (ptv F.S.tp F.S.tm F.S.sp F.S.sm κp κm 5) (ptv F.S.tp F.S.tm F.S.sp F.S.sm κp κm 3) (ptv F.S.tp F.S.tm F.S.sp F.S.sm κp κm 0) (ptv F.S.tp F.S.tm F.S.sp F.S.sm κp κm 1) (ptv F.S.tp F.S.tm F.S.sp F.S.sm κp κm 2) i := by
    intro i
    rcases z5c i with rfl | rfl | rfl | rfl | rfl <;>
      simp [quint_0, quint_1, quint_2, quint_3, quint_4, hpt]
  refine F.toFrame7.rupert_rim_rob (k := 5) (by norm_num) (quint ((5 : Fin 7)) 3 0 1 2)
    (-1) (Or.inr rfl) ⟨-1, 1, 0⟩ ⟨1, 0, 0⟩ (Or.inl (by norm_num)) ?_ ?_ ?_
  · intro i j h1' h2'
    simp only [hc]
    exact cyc_V1B5 F.S.tp F.S.tm F.S.sp F.S.sm κp κm F.S.tp_pos F.S.tp_lt F.S.tm_pos F.S.tm_lt F.S.sp_pos F.S.sp_lt F.S.sm_pos F.S.sm_lt hκp hκm hA.symm hB i j h1' h2'
  · intro j' hj' i
    simp only [hc]
    rw [hpt]
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (by simp [quint_2]) (hj' 2)
    · exact absurd (by simp [quint_3]) (hj' 3)
    · exact absurd (by simp [quint_4]) (hj' 4)
    · exact absurd (by simp [quint_1]) (hj' 1)
    · exact rest_V1B5 F.S.tp F.S.tm F.S.sp F.S.sm κp κm F.S.tp_pos F.S.tp_lt F.S.tm_pos F.S.tm_lt F.S.sp_pos F.S.sp_lt F.S.sm_pos F.S.sm_lt hκp hκm hA.symm hB _ (Or.inl rfl) i
    · exact absurd (by simp [quint_0]) (hj' 0)
    · exact rest_V1B5 F.S.tp F.S.tm F.S.sp F.S.sm κp κm F.S.tp_pos F.S.tp_lt F.S.tm_pos F.S.tm_lt F.S.sp_pos F.S.sp_lt F.S.sm_pos F.S.sm_lt hκp hκm hA.symm hB _ (Or.inr rfl) i
  · have hz : (fun i : ZMod 5 => F.toFrame7.GG (F.toFrame7.ptC (quint ((5 : Fin 7)) 3 0 1 2 i))
        ⟨-1, 1, 0⟩) = fun i : ZMod 5 => quint (-((gA11 x - gA12 x) * F.S.tm)) (-(gA11 x - gA12 x)) (-((gA11 x - gA12 x) * F.S.tp)) ((gA22 x - gA12 x) * F.S.sp) 0 i := by
      funext i
      rw [hc]
      rcases z5c i with rfl | rfl | rfl | rfl | rfl <;>
        simp [quint_0, quint_1, quint_2, quint_3, quint_4, F.GG_uA, ptv] <;> ring
    rw [hz]
    refine robust5_A ?_ ?_ ?_ ?_ ?_
    · nlinarith [mul_pos hα (sub_pos.2 F.S.tm_lt)]
    · nlinarith [mul_pos hα F.S.tm_pos]
    · nlinarith [mul_pos hγ F.S.sp_pos]
    · nlinarith [mul_pos hα (sub_pos.2 F.S.tp_lt)]
    · nlinarith [mul_pos hα F.S.tp_pos, mul_pos hγ F.S.sp_pos]

theorem acute_V1B6_pf (h1 : gA12 x < gA11 x) (h2 : gA12 x < gA22 x)
    (hA : F.S.tp = F.S.sp) (hB : F.S.sm < F.S.tm) : IsRupert (Finset.univ.image x) := by
  obtain ⟨κp, κm, hκp, hκm, hpt⟩ := F.ptC_ptv
  have hα : 0 < gA11 x - gA12 x := by linarith
  have hγ : 0 < gA22 x - gA12 x := by linarith
  have hc : ∀ i, F.toFrame7.ptC (quint ((6 : Fin 7)) 4 1 0 2 i) =
      quint (ptv F.S.tp F.S.tm F.S.sp F.S.sm κp κm 6) (ptv F.S.tp F.S.tm F.S.sp F.S.sm κp κm 4) (ptv F.S.tp F.S.tm F.S.sp F.S.sm κp κm 1) (ptv F.S.tp F.S.tm F.S.sp F.S.sm κp κm 0) (ptv F.S.tp F.S.tm F.S.sp F.S.sm κp κm 2) i := by
    intro i
    rcases z5c i with rfl | rfl | rfl | rfl | rfl <;>
      simp [quint_0, quint_1, quint_2, quint_3, quint_4, hpt]
  refine F.toFrame7.rupert_rim_rob (k := 5) (by norm_num) (quint ((6 : Fin 7)) 4 1 0 2)
    (-1) (Or.inr rfl) ⟨-1, 1, 0⟩ ⟨-1, 0, 0⟩ (Or.inl (by norm_num)) ?_ ?_ ?_
  · intro i j h1' h2'
    simp only [hc]
    exact cyc_V1B6 F.S.tp F.S.tm F.S.sp F.S.sm κp κm F.S.tp_pos F.S.tp_lt F.S.tm_pos F.S.tm_lt F.S.sp_pos F.S.sp_lt F.S.sm_pos F.S.sm_lt hκp hκm hA.symm hB i j h1' h2'
  · intro j' hj' i
    simp only [hc]
    rw [hpt]
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (by simp [quint_3]) (hj' 3)
    · exact absurd (by simp [quint_2]) (hj' 2)
    · exact absurd (by simp [quint_4]) (hj' 4)
    · exact rest_V1B6 F.S.tp F.S.tm F.S.sp F.S.sm κp κm F.S.tp_pos F.S.tp_lt F.S.tm_pos F.S.tm_lt F.S.sp_pos F.S.sp_lt F.S.sm_pos F.S.sm_lt hκp hκm hA.symm hB _ (Or.inl rfl) i
    · exact absurd (by simp [quint_1]) (hj' 1)
    · exact rest_V1B6 F.S.tp F.S.tm F.S.sp F.S.sm κp κm F.S.tp_pos F.S.tp_lt F.S.tm_pos F.S.tm_lt F.S.sp_pos F.S.sp_lt F.S.sm_pos F.S.sm_lt hκp hκm hA.symm hB _ (Or.inr rfl) i
    · exact absurd (by simp [quint_0]) (hj' 0)
  · have hz : (fun i : ZMod 5 => F.toFrame7.GG (F.toFrame7.ptC (quint ((6 : Fin 7)) 4 1 0 2 i))
        ⟨-1, 1, 0⟩) = fun i : ZMod 5 => quint ((gA22 x - gA12 x) * F.S.sm) (gA22 x - gA12 x) ((gA22 x - gA12 x) * F.S.sp) (-((gA11 x - gA12 x) * F.S.tp)) 0 i := by
      funext i
      rw [hc]
      rcases z5c i with rfl | rfl | rfl | rfl | rfl <;>
        simp [quint_0, quint_1, quint_2, quint_3, quint_4, F.GG_uA, ptv] <;> ring
    rw [hz]
    refine robust5_B ?_ ?_ ?_ ?_ ?_
    · nlinarith [mul_pos hα F.S.tp_pos, mul_pos hγ F.S.sp_pos]
    · nlinarith [mul_pos hγ (sub_pos.2 F.S.sp_lt)]
    · nlinarith [mul_pos hα F.S.tp_pos]
    · nlinarith [mul_pos hγ F.S.sm_pos]
    · nlinarith [mul_pos hγ (sub_pos.2 F.S.sm_lt)]

theorem acute_V12_pf (h1 : gA12 x < gA11 x) (h2 : gA12 x < gA22 x)
    (hA : F.S.tp = F.S.sp) (hB : F.S.tm = F.S.sm) : IsRupert (Finset.univ.image x) := by
  obtain ⟨κp, κm, hκp, hκm, hpt⟩ := F.ptC_ptv
  have hα : 0 < gA11 x - gA12 x := by linarith
  have hγ : 0 < gA22 x - gA12 x := by linarith
  have hc : ∀ i, F.toFrame7.ptC (quint ((5 : Fin 7)) 3 4 1 2 i) =
      quint (ptv F.S.tp F.S.tm F.S.sp F.S.sm κp κm 5) (ptv F.S.tp F.S.tm F.S.sp F.S.sm κp κm 3) (ptv F.S.tp F.S.tm F.S.sp F.S.sm κp κm 4) (ptv F.S.tp F.S.tm F.S.sp F.S.sm κp κm 1) (ptv F.S.tp F.S.tm F.S.sp F.S.sm κp κm 2) i := by
    intro i
    rcases z5c i with rfl | rfl | rfl | rfl | rfl <;>
      simp [quint_0, quint_1, quint_2, quint_3, quint_4, hpt]
  refine F.toFrame7.rupert_rim_rob (k := 5) (by norm_num) (quint ((5 : Fin 7)) 3 4 1 2)
    (-1) (Or.inr rfl) ⟨-1, 1, 0⟩ ⟨0, 0, -1⟩ (Or.inl (by norm_num)) ?_ ?_ ?_
  · intro i j h1' h2'
    simp only [hc]
    exact cyc_V12 F.S.tp F.S.tm F.S.sp F.S.sm κp κm F.S.tp_pos F.S.tp_lt F.S.tm_pos F.S.tm_lt F.S.sp_pos F.S.sp_lt F.S.sm_pos F.S.sm_lt hκp hκm hA.symm hB.symm i j h1' h2'
  · intro j' hj' i
    simp only [hc]
    rw [hpt]
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rest_V12 F.S.tp F.S.tm F.S.sp F.S.sm κp κm F.S.tp_pos F.S.tp_lt F.S.tm_pos F.S.tm_lt F.S.sp_pos F.S.sp_lt F.S.sm_pos F.S.sm_lt hκp hκm hA.symm hB.symm _ (Or.inl rfl) i
    · exact absurd (by simp [quint_3]) (hj' 3)
    · exact absurd (by simp [quint_4]) (hj' 4)
    · exact absurd (by simp [quint_1]) (hj' 1)
    · exact absurd (by simp [quint_2]) (hj' 2)
    · exact absurd (by simp [quint_0]) (hj' 0)
    · exact rest_V12 F.S.tp F.S.tm F.S.sp F.S.sm κp κm F.S.tp_pos F.S.tp_lt F.S.tm_pos F.S.tm_lt F.S.sp_pos F.S.sp_lt F.S.sm_pos F.S.sm_lt hκp hκm hA.symm hB.symm _ (Or.inr rfl) i
  · have hz : (fun i : ZMod 5 => F.toFrame7.GG (F.toFrame7.ptC (quint ((5 : Fin 7)) 3 4 1 2 i))
        ⟨-1, 1, 0⟩) = fun i : ZMod 5 => quint (-((gA11 x - gA12 x) * F.S.tm)) (-(gA11 x - gA12 x)) (gA22 x - gA12 x) ((gA22 x - gA12 x) * F.S.sp) 0 i := by
      funext i
      rw [hc]
      rcases z5c i with rfl | rfl | rfl | rfl | rfl <;>
        simp [quint_0, quint_1, quint_2, quint_3, quint_4, F.GG_uA, ptv] <;> ring
    rw [hz]
    refine robust5_C ?_ ?_ ?_ ?_
    · nlinarith [mul_pos hα (sub_pos.2 F.S.tm_lt)]
    · nlinarith [mul_pos hα F.S.tm_pos]
    · nlinarith [mul_pos hγ F.S.sp_pos]
    · nlinarith [mul_pos hγ (sub_pos.2 F.S.sp_lt)]

end Frame02

end Minimality.CaseC18
