module

public import Minimality.Type02Frame

@[expose] public section

/-! # sp02 Lean, group A: the generic acute rims of type 02's case (c)  (scratch)

Coordinates `(x, y, z)` in the frame `(u1, u2, e)`; the 34-view is `u = ⟨-1, 1, 0⟩`; the screen coordinates are
`(x + y, z)`, `σ = -1` (counterclockwise rims).  Tilt `⟨1,0,0⟩` for the rims through `5` ((5,3,0,2), (5,3,0,1,2)),
`⟨-1,0,0⟩` for the rim (6,4,1,2).  The cap relations are written `hp = κp (1-tp)`, `kp = κp (1-sp)`,
`hm = κm (1-tm)`, `km = κm (1-sm)` (from the two planarity equalities). -/

namespace Minimality.CaseC18
open Finset Filter Minimality.CaseC09
open scoped RealInnerProductSpace Topology

/-- Frame coordinates of the seven points with the cap relations substituted. -/
noncomputable def ptv (tp tm sp sm κp κm : ℝ) : Fin 7 → C3 :=
  ![⟨tp, 0, κp * (1 - tp)⟩, ⟨0, sp, κp * (1 - sp)⟩, ⟨0, 0, 0⟩, ⟨1, 0, 0⟩, ⟨0, 1, 0⟩,
    ⟨tm, 0, -(κm * (1 - tm))⟩, ⟨0, sm, -(κm * (1 - sm))⟩]

theorem z4a : (0 : ZMod 4) + 1 = 1 ∧ (1 : ZMod 4) + 1 = 2 ∧ (2 : ZMod 4) + 1 = 3 ∧
    (3 : ZMod 4) + 1 = 0 := by decide
theorem z4c (i : ZMod 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by revert i; decide
theorem z5a : (0 : ZMod 5) + 1 = 1 ∧ (1 : ZMod 5) + 1 = 2 ∧ (2 : ZMod 5) + 1 = 3 ∧
    (3 : ZMod 5) + 1 = 4 ∧ (4 : ZMod 5) + 1 = 0 := by decide
theorem z5c (i : ZMod 5) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by revert i; decide

set_option hygiene false in
macro "stfin" : tactic => `(tactic| first
  | (left; linarith [mul_pos hκp htp, mul_pos hκp htm, mul_pos hκp hsp, mul_pos hκp hsm, mul_pos hκp a1, mul_pos hκp a2, mul_pos hκp a3, mul_pos hκp a4, mul_pos hκp a5, mul_pos hκp a6, mul_pos (mul_pos hκp htp) htp, mul_pos (mul_pos hκp htp) htm, mul_pos (mul_pos hκp htp) hsp, mul_pos (mul_pos hκp htp) hsm, mul_pos (mul_pos hκp htp) a1, mul_pos (mul_pos hκp htp) a2, mul_pos (mul_pos hκp htp) a3, mul_pos (mul_pos hκp htp) a4, mul_pos (mul_pos hκp htp) a5, mul_pos (mul_pos hκp htp) a6, mul_pos (mul_pos hκp htm) htm, mul_pos (mul_pos hκp htm) hsp, mul_pos (mul_pos hκp htm) hsm, mul_pos (mul_pos hκp htm) a1, mul_pos (mul_pos hκp htm) a2, mul_pos (mul_pos hκp htm) a3, mul_pos (mul_pos hκp htm) a4, mul_pos (mul_pos hκp htm) a5, mul_pos (mul_pos hκp htm) a6, mul_pos (mul_pos hκp hsp) hsp, mul_pos (mul_pos hκp hsp) hsm, mul_pos (mul_pos hκp hsp) a1, mul_pos (mul_pos hκp hsp) a2, mul_pos (mul_pos hκp hsp) a3, mul_pos (mul_pos hκp hsp) a4, mul_pos (mul_pos hκp hsp) a5, mul_pos (mul_pos hκp hsp) a6, mul_pos (mul_pos hκp hsm) hsm, mul_pos (mul_pos hκp hsm) a1, mul_pos (mul_pos hκp hsm) a2, mul_pos (mul_pos hκp hsm) a3, mul_pos (mul_pos hκp hsm) a4, mul_pos (mul_pos hκp hsm) a5, mul_pos (mul_pos hκp hsm) a6, mul_pos (mul_pos hκp a1) a1, mul_pos (mul_pos hκp a1) a2, mul_pos (mul_pos hκp a1) a3, mul_pos (mul_pos hκp a1) a4, mul_pos (mul_pos hκp a1) a5, mul_pos (mul_pos hκp a1) a6, mul_pos (mul_pos hκp a2) a2, mul_pos (mul_pos hκp a2) a3, mul_pos (mul_pos hκp a2) a4, mul_pos (mul_pos hκp a2) a5, mul_pos (mul_pos hκp a2) a6, mul_pos (mul_pos hκp a3) a3, mul_pos (mul_pos hκp a3) a4, mul_pos (mul_pos hκp a3) a5, mul_pos (mul_pos hκp a3) a6, mul_pos (mul_pos hκp a4) a4, mul_pos (mul_pos hκp a4) a5, mul_pos (mul_pos hκp a4) a6, mul_pos (mul_pos hκp a5) a5, mul_pos (mul_pos hκp a5) a6, mul_pos (mul_pos hκp a6) a6, mul_pos hκm htp, mul_pos hκm htm, mul_pos hκm hsp, mul_pos hκm hsm, mul_pos hκm a1, mul_pos hκm a2, mul_pos hκm a3, mul_pos hκm a4, mul_pos hκm a5, mul_pos hκm a6, mul_pos (mul_pos hκm htp) htp, mul_pos (mul_pos hκm htp) htm, mul_pos (mul_pos hκm htp) hsp, mul_pos (mul_pos hκm htp) hsm, mul_pos (mul_pos hκm htp) a1, mul_pos (mul_pos hκm htp) a2, mul_pos (mul_pos hκm htp) a3, mul_pos (mul_pos hκm htp) a4, mul_pos (mul_pos hκm htp) a5, mul_pos (mul_pos hκm htp) a6, mul_pos (mul_pos hκm htm) htm, mul_pos (mul_pos hκm htm) hsp, mul_pos (mul_pos hκm htm) hsm, mul_pos (mul_pos hκm htm) a1, mul_pos (mul_pos hκm htm) a2, mul_pos (mul_pos hκm htm) a3, mul_pos (mul_pos hκm htm) a4, mul_pos (mul_pos hκm htm) a5, mul_pos (mul_pos hκm htm) a6, mul_pos (mul_pos hκm hsp) hsp, mul_pos (mul_pos hκm hsp) hsm, mul_pos (mul_pos hκm hsp) a1, mul_pos (mul_pos hκm hsp) a2, mul_pos (mul_pos hκm hsp) a3, mul_pos (mul_pos hκm hsp) a4, mul_pos (mul_pos hκm hsp) a5, mul_pos (mul_pos hκm hsp) a6, mul_pos (mul_pos hκm hsm) hsm, mul_pos (mul_pos hκm hsm) a1, mul_pos (mul_pos hκm hsm) a2, mul_pos (mul_pos hκm hsm) a3, mul_pos (mul_pos hκm hsm) a4, mul_pos (mul_pos hκm hsm) a5, mul_pos (mul_pos hκm hsm) a6, mul_pos (mul_pos hκm a1) a1, mul_pos (mul_pos hκm a1) a2, mul_pos (mul_pos hκm a1) a3, mul_pos (mul_pos hκm a1) a4, mul_pos (mul_pos hκm a1) a5, mul_pos (mul_pos hκm a1) a6, mul_pos (mul_pos hκm a2) a2, mul_pos (mul_pos hκm a2) a3, mul_pos (mul_pos hκm a2) a4, mul_pos (mul_pos hκm a2) a5, mul_pos (mul_pos hκm a2) a6, mul_pos (mul_pos hκm a3) a3, mul_pos (mul_pos hκm a3) a4, mul_pos (mul_pos hκm a3) a5, mul_pos (mul_pos hκm a3) a6, mul_pos (mul_pos hκm a4) a4, mul_pos (mul_pos hκm a4) a5, mul_pos (mul_pos hκm a4) a6, mul_pos (mul_pos hκm a5) a5, mul_pos (mul_pos hκm a5) a6, mul_pos (mul_pos hκm a6) a6])
  | (right; refine ⟨by ring, ?_⟩; linarith [mul_pos hκp htp, mul_pos hκp htm, mul_pos hκp hsp, mul_pos hκp hsm, mul_pos hκp a1, mul_pos hκp a2, mul_pos hκp a3, mul_pos hκp a4, mul_pos hκp a5, mul_pos hκp a6, mul_pos (mul_pos hκp htp) htp, mul_pos (mul_pos hκp htp) htm, mul_pos (mul_pos hκp htp) hsp, mul_pos (mul_pos hκp htp) hsm, mul_pos (mul_pos hκp htp) a1, mul_pos (mul_pos hκp htp) a2, mul_pos (mul_pos hκp htp) a3, mul_pos (mul_pos hκp htp) a4, mul_pos (mul_pos hκp htp) a5, mul_pos (mul_pos hκp htp) a6, mul_pos (mul_pos hκp htm) htm, mul_pos (mul_pos hκp htm) hsp, mul_pos (mul_pos hκp htm) hsm, mul_pos (mul_pos hκp htm) a1, mul_pos (mul_pos hκp htm) a2, mul_pos (mul_pos hκp htm) a3, mul_pos (mul_pos hκp htm) a4, mul_pos (mul_pos hκp htm) a5, mul_pos (mul_pos hκp htm) a6, mul_pos (mul_pos hκp hsp) hsp, mul_pos (mul_pos hκp hsp) hsm, mul_pos (mul_pos hκp hsp) a1, mul_pos (mul_pos hκp hsp) a2, mul_pos (mul_pos hκp hsp) a3, mul_pos (mul_pos hκp hsp) a4, mul_pos (mul_pos hκp hsp) a5, mul_pos (mul_pos hκp hsp) a6, mul_pos (mul_pos hκp hsm) hsm, mul_pos (mul_pos hκp hsm) a1, mul_pos (mul_pos hκp hsm) a2, mul_pos (mul_pos hκp hsm) a3, mul_pos (mul_pos hκp hsm) a4, mul_pos (mul_pos hκp hsm) a5, mul_pos (mul_pos hκp hsm) a6, mul_pos (mul_pos hκp a1) a1, mul_pos (mul_pos hκp a1) a2, mul_pos (mul_pos hκp a1) a3, mul_pos (mul_pos hκp a1) a4, mul_pos (mul_pos hκp a1) a5, mul_pos (mul_pos hκp a1) a6, mul_pos (mul_pos hκp a2) a2, mul_pos (mul_pos hκp a2) a3, mul_pos (mul_pos hκp a2) a4, mul_pos (mul_pos hκp a2) a5, mul_pos (mul_pos hκp a2) a6, mul_pos (mul_pos hκp a3) a3, mul_pos (mul_pos hκp a3) a4, mul_pos (mul_pos hκp a3) a5, mul_pos (mul_pos hκp a3) a6, mul_pos (mul_pos hκp a4) a4, mul_pos (mul_pos hκp a4) a5, mul_pos (mul_pos hκp a4) a6, mul_pos (mul_pos hκp a5) a5, mul_pos (mul_pos hκp a5) a6, mul_pos (mul_pos hκp a6) a6, mul_pos hκm htp, mul_pos hκm htm, mul_pos hκm hsp, mul_pos hκm hsm, mul_pos hκm a1, mul_pos hκm a2, mul_pos hκm a3, mul_pos hκm a4, mul_pos hκm a5, mul_pos hκm a6, mul_pos (mul_pos hκm htp) htp, mul_pos (mul_pos hκm htp) htm, mul_pos (mul_pos hκm htp) hsp, mul_pos (mul_pos hκm htp) hsm, mul_pos (mul_pos hκm htp) a1, mul_pos (mul_pos hκm htp) a2, mul_pos (mul_pos hκm htp) a3, mul_pos (mul_pos hκm htp) a4, mul_pos (mul_pos hκm htp) a5, mul_pos (mul_pos hκm htp) a6, mul_pos (mul_pos hκm htm) htm, mul_pos (mul_pos hκm htm) hsp, mul_pos (mul_pos hκm htm) hsm, mul_pos (mul_pos hκm htm) a1, mul_pos (mul_pos hκm htm) a2, mul_pos (mul_pos hκm htm) a3, mul_pos (mul_pos hκm htm) a4, mul_pos (mul_pos hκm htm) a5, mul_pos (mul_pos hκm htm) a6, mul_pos (mul_pos hκm hsp) hsp, mul_pos (mul_pos hκm hsp) hsm, mul_pos (mul_pos hκm hsp) a1, mul_pos (mul_pos hκm hsp) a2, mul_pos (mul_pos hκm hsp) a3, mul_pos (mul_pos hκm hsp) a4, mul_pos (mul_pos hκm hsp) a5, mul_pos (mul_pos hκm hsp) a6, mul_pos (mul_pos hκm hsm) hsm, mul_pos (mul_pos hκm hsm) a1, mul_pos (mul_pos hκm hsm) a2, mul_pos (mul_pos hκm hsm) a3, mul_pos (mul_pos hκm hsm) a4, mul_pos (mul_pos hκm hsm) a5, mul_pos (mul_pos hκm hsm) a6, mul_pos (mul_pos hκm a1) a1, mul_pos (mul_pos hκm a1) a2, mul_pos (mul_pos hκm a1) a3, mul_pos (mul_pos hκm a1) a4, mul_pos (mul_pos hκm a1) a5, mul_pos (mul_pos hκm a1) a6, mul_pos (mul_pos hκm a2) a2, mul_pos (mul_pos hκm a2) a3, mul_pos (mul_pos hκm a2) a4, mul_pos (mul_pos hκm a2) a5, mul_pos (mul_pos hκm a2) a6, mul_pos (mul_pos hκm a3) a3, mul_pos (mul_pos hκm a3) a4, mul_pos (mul_pos hκm a3) a5, mul_pos (mul_pos hκm a3) a6, mul_pos (mul_pos hκm a4) a4, mul_pos (mul_pos hκm a4) a5, mul_pos (mul_pos hκm a4) a6, mul_pos (mul_pos hκm a5) a5, mul_pos (mul_pos hκm a5) a6, mul_pos (mul_pos hκm a6) a6])
  | linarith [mul_pos hκp htp, mul_pos hκp htm, mul_pos hκp hsp, mul_pos hκp hsm, mul_pos hκp a1, mul_pos hκp a2, mul_pos hκp a3, mul_pos hκp a4, mul_pos hκp a5, mul_pos hκp a6, mul_pos (mul_pos hκp htp) htp, mul_pos (mul_pos hκp htp) htm, mul_pos (mul_pos hκp htp) hsp, mul_pos (mul_pos hκp htp) hsm, mul_pos (mul_pos hκp htp) a1, mul_pos (mul_pos hκp htp) a2, mul_pos (mul_pos hκp htp) a3, mul_pos (mul_pos hκp htp) a4, mul_pos (mul_pos hκp htp) a5, mul_pos (mul_pos hκp htp) a6, mul_pos (mul_pos hκp htm) htm, mul_pos (mul_pos hκp htm) hsp, mul_pos (mul_pos hκp htm) hsm, mul_pos (mul_pos hκp htm) a1, mul_pos (mul_pos hκp htm) a2, mul_pos (mul_pos hκp htm) a3, mul_pos (mul_pos hκp htm) a4, mul_pos (mul_pos hκp htm) a5, mul_pos (mul_pos hκp htm) a6, mul_pos (mul_pos hκp hsp) hsp, mul_pos (mul_pos hκp hsp) hsm, mul_pos (mul_pos hκp hsp) a1, mul_pos (mul_pos hκp hsp) a2, mul_pos (mul_pos hκp hsp) a3, mul_pos (mul_pos hκp hsp) a4, mul_pos (mul_pos hκp hsp) a5, mul_pos (mul_pos hκp hsp) a6, mul_pos (mul_pos hκp hsm) hsm, mul_pos (mul_pos hκp hsm) a1, mul_pos (mul_pos hκp hsm) a2, mul_pos (mul_pos hκp hsm) a3, mul_pos (mul_pos hκp hsm) a4, mul_pos (mul_pos hκp hsm) a5, mul_pos (mul_pos hκp hsm) a6, mul_pos (mul_pos hκp a1) a1, mul_pos (mul_pos hκp a1) a2, mul_pos (mul_pos hκp a1) a3, mul_pos (mul_pos hκp a1) a4, mul_pos (mul_pos hκp a1) a5, mul_pos (mul_pos hκp a1) a6, mul_pos (mul_pos hκp a2) a2, mul_pos (mul_pos hκp a2) a3, mul_pos (mul_pos hκp a2) a4, mul_pos (mul_pos hκp a2) a5, mul_pos (mul_pos hκp a2) a6, mul_pos (mul_pos hκp a3) a3, mul_pos (mul_pos hκp a3) a4, mul_pos (mul_pos hκp a3) a5, mul_pos (mul_pos hκp a3) a6, mul_pos (mul_pos hκp a4) a4, mul_pos (mul_pos hκp a4) a5, mul_pos (mul_pos hκp a4) a6, mul_pos (mul_pos hκp a5) a5, mul_pos (mul_pos hκp a5) a6, mul_pos (mul_pos hκp a6) a6, mul_pos hκm htp, mul_pos hκm htm, mul_pos hκm hsp, mul_pos hκm hsm, mul_pos hκm a1, mul_pos hκm a2, mul_pos hκm a3, mul_pos hκm a4, mul_pos hκm a5, mul_pos hκm a6, mul_pos (mul_pos hκm htp) htp, mul_pos (mul_pos hκm htp) htm, mul_pos (mul_pos hκm htp) hsp, mul_pos (mul_pos hκm htp) hsm, mul_pos (mul_pos hκm htp) a1, mul_pos (mul_pos hκm htp) a2, mul_pos (mul_pos hκm htp) a3, mul_pos (mul_pos hκm htp) a4, mul_pos (mul_pos hκm htp) a5, mul_pos (mul_pos hκm htp) a6, mul_pos (mul_pos hκm htm) htm, mul_pos (mul_pos hκm htm) hsp, mul_pos (mul_pos hκm htm) hsm, mul_pos (mul_pos hκm htm) a1, mul_pos (mul_pos hκm htm) a2, mul_pos (mul_pos hκm htm) a3, mul_pos (mul_pos hκm htm) a4, mul_pos (mul_pos hκm htm) a5, mul_pos (mul_pos hκm htm) a6, mul_pos (mul_pos hκm hsp) hsp, mul_pos (mul_pos hκm hsp) hsm, mul_pos (mul_pos hκm hsp) a1, mul_pos (mul_pos hκm hsp) a2, mul_pos (mul_pos hκm hsp) a3, mul_pos (mul_pos hκm hsp) a4, mul_pos (mul_pos hκm hsp) a5, mul_pos (mul_pos hκm hsp) a6, mul_pos (mul_pos hκm hsm) hsm, mul_pos (mul_pos hκm hsm) a1, mul_pos (mul_pos hκm hsm) a2, mul_pos (mul_pos hκm hsm) a3, mul_pos (mul_pos hκm hsm) a4, mul_pos (mul_pos hκm hsm) a5, mul_pos (mul_pos hκm hsm) a6, mul_pos (mul_pos hκm a1) a1, mul_pos (mul_pos hκm a1) a2, mul_pos (mul_pos hκm a1) a3, mul_pos (mul_pos hκm a1) a4, mul_pos (mul_pos hκm a1) a5, mul_pos (mul_pos hκm a1) a6, mul_pos (mul_pos hκm a2) a2, mul_pos (mul_pos hκm a2) a3, mul_pos (mul_pos hκm a2) a4, mul_pos (mul_pos hκm a2) a5, mul_pos (mul_pos hκm a2) a6, mul_pos (mul_pos hκm a3) a3, mul_pos (mul_pos hκm a3) a4, mul_pos (mul_pos hκm a3) a5, mul_pos (mul_pos hκm a3) a6, mul_pos (mul_pos hκm a4) a4, mul_pos (mul_pos hκm a4) a5, mul_pos (mul_pos hκm a4) a6, mul_pos (mul_pos hκm a5) a5, mul_pos (mul_pos hκm a5) a6, mul_pos (mul_pos hκm a6) a6])

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
/-- Pure-real robust unimodality of the 5-cycle `![p0, p1, p2, p3, p4]` with `p1` the minimum, `p3` the maximum, and the
two monotone paths `p1 < p2 < p3`, `p1 < p0 < p4 < p3`. -/
theorem robust5_A {p0 p1 p2 p3 p4 : ℝ} (h1 : p1 < p0) (h2 : p0 < p4) (h3 : p4 < p3) (h4 : p1 < p2) (h5 : p2 < p3) :
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
theorem cyc_A0B5 (tp tm sp sm κp κm : ℝ) (htp : 0 < tp) (htp1 : tp < 1) (htm : 0 < tm) (htm1 : tm < 1)
    (hsp : 0 < sp) (hsp1 : sp < 1) (hsm : 0 < sm) (hsm1 : sm < 1) (hκp : 0 < κp) (hκm : 0 < κm)
    (hA : tp < sp) (hB : tm < sm) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      CaseC09.ST (-1) ⟨-1, 1, 0⟩ ⟨1, 0, 0⟩
        ((quad (ptv tp tm sp sm κp κm 5) (ptv tp tm sp sm κp κm 3) (ptv tp tm sp sm κp κm 0) (ptv tp tm sp sm κp κm 2) (i + 1)).sub (quad (ptv tp tm sp sm κp κm 5) (ptv tp tm sp sm κp κm 3) (ptv tp tm sp sm κp κm 0) (ptv tp tm sp sm κp κm 2) i)) ((quad (ptv tp tm sp sm κp κm 5) (ptv tp tm sp sm κp κm 3) (ptv tp tm sp sm κp κm 0) (ptv tp tm sp sm κp κm 2) j).sub (quad (ptv tp tm sp sm κp κm 5) (ptv tp tm sp sm κp κm 3) (ptv tp tm sp sm κp κm 0) (ptv tp tm sp sm κp κm 2) i)) := by
  have a1 := sub_pos.2 htp1
  have a2 := sub_pos.2 hsp1
  have a3 := sub_pos.2 htm1
  have a4 := sub_pos.2 hsm1
  have a5 := sub_pos.2 hA
  have a6 := sub_pos.2 hB
  obtain ⟨b0, b1, b2, b3⟩ := z4a
  intro i j h1 h2
  rcases z4c i with rfl | rfl | rfl | rfl <;>
    rcases z4c j with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [CaseC09.ST, Dc, C3.sub, ptv, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    norm_num
    stfin

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
theorem rest_A0B5 (tp tm sp sm κp κm : ℝ) (htp : 0 < tp) (htp1 : tp < 1) (htm : 0 < tm) (htm1 : tm < 1)
    (hsp : 0 < sp) (hsp1 : sp < 1) (hsm : 0 < sm) (hsm1 : sm < 1) (hκp : 0 < κp) (hκm : 0 < κm)
    (hA : tp < sp) (hB : tm < sm) (j' : Fin 7) (hw : j' = 1 ∨ j' = 4 ∨ j' = 6) :
    ∀ i : ZMod 4,
      CaseC09.ST (-1) ⟨-1, 1, 0⟩ ⟨1, 0, 0⟩
        ((quad (ptv tp tm sp sm κp κm 5) (ptv tp tm sp sm κp κm 3) (ptv tp tm sp sm κp κm 0) (ptv tp tm sp sm κp κm 2) (i + 1)).sub (quad (ptv tp tm sp sm κp κm 5) (ptv tp tm sp sm κp κm 3) (ptv tp tm sp sm κp κm 0) (ptv tp tm sp sm κp κm 2) i)) ((ptv tp tm sp sm κp κm j').sub (quad (ptv tp tm sp sm κp κm 5) (ptv tp tm sp sm κp κm 3) (ptv tp tm sp sm κp κm 0) (ptv tp tm sp sm κp κm 2) i)) := by
  have a1 := sub_pos.2 htp1
  have a2 := sub_pos.2 hsp1
  have a3 := sub_pos.2 htm1
  have a4 := sub_pos.2 hsm1
  have a5 := sub_pos.2 hA
  have a6 := sub_pos.2 hB
  obtain ⟨b0, b1, b2, b3⟩ := z4a
  intro i
  rcases hw with rfl | rfl | rfl <;>
  rcases z4c i with rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, ptv, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    norm_num
    stfin

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
theorem cyc_A1B5 (tp tm sp sm κp κm : ℝ) (htp : 0 < tp) (htp1 : tp < 1) (htm : 0 < tm) (htm1 : tm < 1)
    (hsp : 0 < sp) (hsp1 : sp < 1) (hsm : 0 < sm) (hsm1 : sm < 1) (hκp : 0 < κp) (hκm : 0 < κm)
    (hA : sp < tp) (hB : tm < sm) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      CaseC09.ST (-1) ⟨-1, 1, 0⟩ ⟨1, 0, 0⟩
        ((quint (ptv tp tm sp sm κp κm 5) (ptv tp tm sp sm κp κm 3) (ptv tp tm sp sm κp κm 0) (ptv tp tm sp sm κp κm 1) (ptv tp tm sp sm κp κm 2) (i + 1)).sub (quint (ptv tp tm sp sm κp κm 5) (ptv tp tm sp sm κp κm 3) (ptv tp tm sp sm κp κm 0) (ptv tp tm sp sm κp κm 1) (ptv tp tm sp sm κp κm 2) i)) ((quint (ptv tp tm sp sm κp κm 5) (ptv tp tm sp sm κp κm 3) (ptv tp tm sp sm κp κm 0) (ptv tp tm sp sm κp κm 1) (ptv tp tm sp sm κp κm 2) j).sub (quint (ptv tp tm sp sm κp κm 5) (ptv tp tm sp sm κp κm 3) (ptv tp tm sp sm κp κm 0) (ptv tp tm sp sm κp κm 1) (ptv tp tm sp sm κp κm 2) i)) := by
  have a1 := sub_pos.2 htp1
  have a2 := sub_pos.2 hsp1
  have a3 := sub_pos.2 htm1
  have a4 := sub_pos.2 hsm1
  have a5 := sub_pos.2 hA
  have a6 := sub_pos.2 hB
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
theorem rest_A1B5 (tp tm sp sm κp κm : ℝ) (htp : 0 < tp) (htp1 : tp < 1) (htm : 0 < tm) (htm1 : tm < 1)
    (hsp : 0 < sp) (hsp1 : sp < 1) (hsm : 0 < sm) (hsm1 : sm < 1) (hκp : 0 < κp) (hκm : 0 < κm)
    (hA : sp < tp) (hB : tm < sm) (j' : Fin 7) (hw : j' = 4 ∨ j' = 6) :
    ∀ i : ZMod 5,
      CaseC09.ST (-1) ⟨-1, 1, 0⟩ ⟨1, 0, 0⟩
        ((quint (ptv tp tm sp sm κp κm 5) (ptv tp tm sp sm κp κm 3) (ptv tp tm sp sm κp κm 0) (ptv tp tm sp sm κp κm 1) (ptv tp tm sp sm κp κm 2) (i + 1)).sub (quint (ptv tp tm sp sm κp κm 5) (ptv tp tm sp sm κp κm 3) (ptv tp tm sp sm κp κm 0) (ptv tp tm sp sm κp κm 1) (ptv tp tm sp sm κp κm 2) i)) ((ptv tp tm sp sm κp κm j').sub (quint (ptv tp tm sp sm κp κm 5) (ptv tp tm sp sm κp κm 3) (ptv tp tm sp sm κp κm 0) (ptv tp tm sp sm κp κm 1) (ptv tp tm sp sm κp κm 2) i)) := by
  have a1 := sub_pos.2 htp1
  have a2 := sub_pos.2 hsp1
  have a3 := sub_pos.2 htm1
  have a4 := sub_pos.2 hsm1
  have a5 := sub_pos.2 hA
  have a6 := sub_pos.2 hB
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
theorem cyc_A1B6 (tp tm sp sm κp κm : ℝ) (htp : 0 < tp) (htp1 : tp < 1) (htm : 0 < tm) (htm1 : tm < 1)
    (hsp : 0 < sp) (hsp1 : sp < 1) (hsm : 0 < sm) (hsm1 : sm < 1) (hκp : 0 < κp) (hκm : 0 < κm)
    (hA : sp < tp) (hB : sm < tm) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      CaseC09.ST (-1) ⟨-1, 1, 0⟩ ⟨-1, 0, 0⟩
        ((quad (ptv tp tm sp sm κp κm 6) (ptv tp tm sp sm κp κm 4) (ptv tp tm sp sm κp κm 1) (ptv tp tm sp sm κp κm 2) (i + 1)).sub (quad (ptv tp tm sp sm κp κm 6) (ptv tp tm sp sm κp κm 4) (ptv tp tm sp sm κp κm 1) (ptv tp tm sp sm κp κm 2) i)) ((quad (ptv tp tm sp sm κp κm 6) (ptv tp tm sp sm κp κm 4) (ptv tp tm sp sm κp κm 1) (ptv tp tm sp sm κp κm 2) j).sub (quad (ptv tp tm sp sm κp κm 6) (ptv tp tm sp sm κp κm 4) (ptv tp tm sp sm κp κm 1) (ptv tp tm sp sm κp κm 2) i)) := by
  have a1 := sub_pos.2 htp1
  have a2 := sub_pos.2 hsp1
  have a3 := sub_pos.2 htm1
  have a4 := sub_pos.2 hsm1
  have a5 := sub_pos.2 hA
  have a6 := sub_pos.2 hB
  obtain ⟨b0, b1, b2, b3⟩ := z4a
  intro i j h1 h2
  rcases z4c i with rfl | rfl | rfl | rfl <;>
    rcases z4c j with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [CaseC09.ST, Dc, C3.sub, ptv, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    norm_num
    stfin

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
theorem rest_A1B6 (tp tm sp sm κp κm : ℝ) (htp : 0 < tp) (htp1 : tp < 1) (htm : 0 < tm) (htm1 : tm < 1)
    (hsp : 0 < sp) (hsp1 : sp < 1) (hsm : 0 < sm) (hsm1 : sm < 1) (hκp : 0 < κp) (hκm : 0 < κm)
    (hA : sp < tp) (hB : sm < tm) (j' : Fin 7) (hw : j' = 3 ∨ j' = 0 ∨ j' = 5) :
    ∀ i : ZMod 4,
      CaseC09.ST (-1) ⟨-1, 1, 0⟩ ⟨-1, 0, 0⟩
        ((quad (ptv tp tm sp sm κp κm 6) (ptv tp tm sp sm κp κm 4) (ptv tp tm sp sm κp κm 1) (ptv tp tm sp sm κp κm 2) (i + 1)).sub (quad (ptv tp tm sp sm κp κm 6) (ptv tp tm sp sm κp κm 4) (ptv tp tm sp sm κp κm 1) (ptv tp tm sp sm κp κm 2) i)) ((ptv tp tm sp sm κp κm j').sub (quad (ptv tp tm sp sm κp κm 6) (ptv tp tm sp sm κp κm 4) (ptv tp tm sp sm κp κm 1) (ptv tp tm sp sm κp κm 2) i)) := by
  have a1 := sub_pos.2 htp1
  have a2 := sub_pos.2 hsp1
  have a3 := sub_pos.2 htm1
  have a4 := sub_pos.2 hsm1
  have a5 := sub_pos.2 hA
  have a6 := sub_pos.2 hB
  obtain ⟨b0, b1, b2, b3⟩ := z4a
  intro i
  rcases hw with rfl | rfl | rfl <;>
  rcases z4c i with rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, ptv, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    norm_num
    stfin



/-! ### Depth cycles (pure real) -/

theorem rob_A0B5 {α tp tm : ℝ} (hα : 0 < α) (htm : 0 < tm) (htm1 : tm < 1) :
    IsRobustUnimodal (quad (-(α * tm)) (-α) (-(α * tp)) 0) :=
  robust_quad_of_nws (Or.inr (Or.inl (by nlinarith [mul_pos hα htm])))
    (Or.inl (by nlinarith [mul_pos hα (sub_pos.2 htm1)]))

theorem rob_A1B6 {γ sp sm : ℝ} (hγ : 0 < γ) (hsm : 0 < sm) (hsm1 : sm < 1) :
    IsRobustUnimodal (quad (γ * sm) γ (γ * sp) 0) :=
  robust_quad_of_nws (Or.inl (by nlinarith [mul_pos hγ (sub_pos.2 hsm1)]))
    (Or.inr (Or.inl (by nlinarith [mul_pos hγ hsm])))

/-! ### The shape in `ptv` form -/

namespace Frame02
variable {x : Fin 7 → ℝ³} (F : Frame02 x)

theorem ptC_ptv : ∃ κp κm : ℝ, 0 < κp ∧ 0 < κm ∧
    F.toFrame7.ptC = ptv F.S.tp F.S.tm F.S.sp F.S.sm κp κm := by
  have h1 := F.S.tp_lt; have h2 := F.S.sp_lt; have h3 := F.S.tm_lt; have h4 := F.S.sm_lt
  have n1 : (1 - F.S.tp) ≠ 0 := by linarith
  have n2 : (1 - F.S.sp) ≠ 0 := by linarith
  have n3 : (1 - F.S.tm) ≠ 0 := by linarith
  have n4 : (1 - F.S.sm) ≠ 0 := by linarith
  obtain ⟨κp, hκp, e1, e2⟩ : ∃ κp : ℝ, 0 < κp ∧ F.S.hp = κp * (1 - F.S.tp) ∧ F.S.kp = κp * (1 - F.S.sp) := by
    refine ⟨F.S.hp / (1 - F.S.tp), div_pos F.S.hp_pos (by linarith), ?_, ?_⟩
    · field_simp
    · rw [F.S.plane_up]; field_simp
  obtain ⟨κm, hκm, e3, e4⟩ : ∃ κm : ℝ, 0 < κm ∧ F.S.hm = κm * (1 - F.S.tm) ∧ F.S.km = κm * (1 - F.S.sm) := by
    refine ⟨F.S.hm / (1 - F.S.tm), div_pos F.S.hm_pos (by linarith), ?_, ?_⟩
    · field_simp
    · rw [F.S.plane_dn]; field_simp
  refine ⟨κp, κm, hκp, hκm, ?_⟩
  show Frame02.pt F.S = _
  unfold Frame02.pt ptv
  rw [e1, e2, e3, e4]

/-- `GG` of a frame point against the 34-view `⟨-1, 1, 0⟩`. -/
theorem GG_uA (p : C3) : F.toFrame7.GG p ⟨-1, 1, 0⟩ =
    -(gA11 x - gA12 x) * p.x + (gA22 x - gA12 x) * p.y := by
  show Gf (⟪x 3 - x 2, x 3 - x 2⟫) (⟪x 3 - x 2, x 4 - x 2⟫) (⟪x 4 - x 2, x 4 - x 2⟫) _ _ _ = _
  simp only [Gf, gA11, gA12, gA22]
  ring

end Frame02


namespace Frame02
variable {x : Fin 7 → ℝ³} (F : Frame02 x)

theorem acute_A0B5_pf (h1 : gA12 x < gA11 x) (h2 : gA12 x < gA22 x)
    (hA : F.S.tp < F.S.sp) (hB : F.S.tm < F.S.sm) : IsRupert (Finset.univ.image x) := by
  obtain ⟨κp, κm, hκp, hκm, hpt⟩ := F.ptC_ptv
  have hα : 0 < gA11 x - gA12 x := by linarith
  have hγ : 0 < gA22 x - gA12 x := by linarith
  have hc : ∀ i, F.toFrame7.ptC (quad ((5 : Fin 7)) 3 0 2 i) =
      quad (ptv F.S.tp F.S.tm F.S.sp F.S.sm κp κm 5) (ptv F.S.tp F.S.tm F.S.sp F.S.sm κp κm 3) (ptv F.S.tp F.S.tm F.S.sp F.S.sm κp κm 0) (ptv F.S.tp F.S.tm F.S.sp F.S.sm κp κm 2) i := by
    intro i
    rcases z4c i with rfl | rfl | rfl | rfl <;>
      simp [quad_0, quad_1, quad_2, quad_3, hpt]
  refine F.toFrame7.rupert_rim_rob (k := 4) (by norm_num) (quad ((5 : Fin 7)) 3 0 2)
    (-1) (Or.inr rfl) ⟨-1, 1, 0⟩ ⟨1, 0, 0⟩ (Or.inl (by norm_num)) ?_ ?_ ?_
  · intro i j h1' h2'
    simp only [hc]
    exact cyc_A0B5 F.S.tp F.S.tm F.S.sp F.S.sm κp κm F.S.tp_pos F.S.tp_lt F.S.tm_pos F.S.tm_lt F.S.sp_pos F.S.sp_lt F.S.sm_pos F.S.sm_lt hκp hκm hA hB i j h1' h2'
  · intro j' hj' i
    simp only [hc]
    rw [hpt]
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (by simp [quad_2]) (hj' 2)
    · exact rest_A0B5 F.S.tp F.S.tm F.S.sp F.S.sm κp κm F.S.tp_pos F.S.tp_lt F.S.tm_pos F.S.tm_lt F.S.sp_pos F.S.sp_lt F.S.sm_pos F.S.sm_lt hκp hκm hA hB _ (Or.inl rfl) i
    · exact absurd (by simp [quad_3]) (hj' 3)
    · exact absurd (by simp [quad_1]) (hj' 1)
    · exact rest_A0B5 F.S.tp F.S.tm F.S.sp F.S.sm κp κm F.S.tp_pos F.S.tp_lt F.S.tm_pos F.S.tm_lt F.S.sp_pos F.S.sp_lt F.S.sm_pos F.S.sm_lt hκp hκm hA hB _ (Or.inr (Or.inl rfl)) i
    · exact absurd (by simp [quad_0]) (hj' 0)
    · exact rest_A0B5 F.S.tp F.S.tm F.S.sp F.S.sm κp κm F.S.tp_pos F.S.tp_lt F.S.tm_pos F.S.tm_lt F.S.sp_pos F.S.sp_lt F.S.sm_pos F.S.sm_lt hκp hκm hA hB _ (Or.inr (Or.inr rfl)) i
  · have hz : (fun i : ZMod 4 => F.toFrame7.GG (F.toFrame7.ptC (quad ((5 : Fin 7)) 3 0 2 i))
        ⟨-1, 1, 0⟩) = fun i : ZMod 4 => quad (-((gA11 x - gA12 x) * F.S.tm)) (-(gA11 x - gA12 x)) (-((gA11 x - gA12 x) * F.S.tp)) 0 i := by
      funext i
      rw [hc]
      rcases z4c i with rfl | rfl | rfl | rfl <;>
        simp [quad_0, quad_1, quad_2, quad_3, F.GG_uA, ptv] <;> ring
    rw [hz]
    exact rob_A0B5 hα F.S.tm_pos F.S.tm_lt

theorem acute_A1B5_pf (h1 : gA12 x < gA11 x) (h2 : gA12 x < gA22 x)
    (hA : F.S.sp < F.S.tp) (hB : F.S.tm < F.S.sm) : IsRupert (Finset.univ.image x) := by
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
    exact cyc_A1B5 F.S.tp F.S.tm F.S.sp F.S.sm κp κm F.S.tp_pos F.S.tp_lt F.S.tm_pos F.S.tm_lt F.S.sp_pos F.S.sp_lt F.S.sm_pos F.S.sm_lt hκp hκm hA hB i j h1' h2'
  · intro j' hj' i
    simp only [hc]
    rw [hpt]
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (by simp [quint_2]) (hj' 2)
    · exact absurd (by simp [quint_3]) (hj' 3)
    · exact absurd (by simp [quint_4]) (hj' 4)
    · exact absurd (by simp [quint_1]) (hj' 1)
    · exact rest_A1B5 F.S.tp F.S.tm F.S.sp F.S.sm κp κm F.S.tp_pos F.S.tp_lt F.S.tm_pos F.S.tm_lt F.S.sp_pos F.S.sp_lt F.S.sm_pos F.S.sm_lt hκp hκm hA hB _ (Or.inl rfl) i
    · exact absurd (by simp [quint_0]) (hj' 0)
    · exact rest_A1B5 F.S.tp F.S.tm F.S.sp F.S.sm κp κm F.S.tp_pos F.S.tp_lt F.S.tm_pos F.S.tm_lt F.S.sp_pos F.S.sp_lt F.S.sm_pos F.S.sm_lt hκp hκm hA hB _ (Or.inr rfl) i
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

theorem acute_A1B6_pf (h1 : gA12 x < gA11 x) (h2 : gA12 x < gA22 x)
    (hA : F.S.sp < F.S.tp) (hB : F.S.sm < F.S.tm) : IsRupert (Finset.univ.image x) := by
  obtain ⟨κp, κm, hκp, hκm, hpt⟩ := F.ptC_ptv
  have hα : 0 < gA11 x - gA12 x := by linarith
  have hγ : 0 < gA22 x - gA12 x := by linarith
  have hc : ∀ i, F.toFrame7.ptC (quad ((6 : Fin 7)) 4 1 2 i) =
      quad (ptv F.S.tp F.S.tm F.S.sp F.S.sm κp κm 6) (ptv F.S.tp F.S.tm F.S.sp F.S.sm κp κm 4) (ptv F.S.tp F.S.tm F.S.sp F.S.sm κp κm 1) (ptv F.S.tp F.S.tm F.S.sp F.S.sm κp κm 2) i := by
    intro i
    rcases z4c i with rfl | rfl | rfl | rfl <;>
      simp [quad_0, quad_1, quad_2, quad_3, hpt]
  refine F.toFrame7.rupert_rim_rob (k := 4) (by norm_num) (quad ((6 : Fin 7)) 4 1 2)
    (-1) (Or.inr rfl) ⟨-1, 1, 0⟩ ⟨-1, 0, 0⟩ (Or.inl (by norm_num)) ?_ ?_ ?_
  · intro i j h1' h2'
    simp only [hc]
    exact cyc_A1B6 F.S.tp F.S.tm F.S.sp F.S.sm κp κm F.S.tp_pos F.S.tp_lt F.S.tm_pos F.S.tm_lt F.S.sp_pos F.S.sp_lt F.S.sm_pos F.S.sm_lt hκp hκm hA hB i j h1' h2'
  · intro j' hj' i
    simp only [hc]
    rw [hpt]
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rest_A1B6 F.S.tp F.S.tm F.S.sp F.S.sm κp κm F.S.tp_pos F.S.tp_lt F.S.tm_pos F.S.tm_lt F.S.sp_pos F.S.sp_lt F.S.sm_pos F.S.sm_lt hκp hκm hA hB _ (Or.inr (Or.inl rfl)) i
    · exact absurd (by simp [quad_2]) (hj' 2)
    · exact absurd (by simp [quad_3]) (hj' 3)
    · exact rest_A1B6 F.S.tp F.S.tm F.S.sp F.S.sm κp κm F.S.tp_pos F.S.tp_lt F.S.tm_pos F.S.tm_lt F.S.sp_pos F.S.sp_lt F.S.sm_pos F.S.sm_lt hκp hκm hA hB _ (Or.inl rfl) i
    · exact absurd (by simp [quad_1]) (hj' 1)
    · exact rest_A1B6 F.S.tp F.S.tm F.S.sp F.S.sm κp κm F.S.tp_pos F.S.tp_lt F.S.tm_pos F.S.tm_lt F.S.sp_pos F.S.sp_lt F.S.sm_pos F.S.sm_lt hκp hκm hA hB _ (Or.inr (Or.inr rfl)) i
    · exact absurd (by simp [quad_0]) (hj' 0)
  · have hz : (fun i : ZMod 4 => F.toFrame7.GG (F.toFrame7.ptC (quad ((6 : Fin 7)) 4 1 2 i))
        ⟨-1, 1, 0⟩) = fun i : ZMod 4 => quad ((gA22 x - gA12 x) * F.S.sm) (gA22 x - gA12 x) ((gA22 x - gA12 x) * F.S.sp) 0 i := by
      funext i
      rw [hc]
      rcases z4c i with rfl | rfl | rfl | rfl <;>
        simp [quad_0, quad_1, quad_2, quad_3, F.GG_uA, ptv] <;> ring
    rw [hz]
    exact rob_A1B6 hγ F.S.sm_pos F.S.sm_lt

end Frame02

end Minimality.CaseC18
