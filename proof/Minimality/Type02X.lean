module

public import Minimality.Type02B

@[expose] public section

/-! # sp02 Lean, group X (and W): exceptional sets X1, X2 (scratch) -/

namespace Minimality.CaseC18
open Finset Filter Minimality.CaseC09
open scoped RealInnerProductSpace Topology

def sext {α : Type*} (p0 p1 p2 p3 p4 p5 : α) : ZMod 6 → α := ![p0, p1, p2, p3, p4, p5]
section sext
variable {α : Type*} (p0 p1 p2 p3 p4 p5 : α)
theorem sext_0 : sext p0 p1 p2 p3 p4 p5 0 = p0 := rfl
theorem sext_1 : sext p0 p1 p2 p3 p4 p5 1 = p1 := rfl
theorem sext_2 : sext p0 p1 p2 p3 p4 p5 2 = p2 := rfl
theorem sext_3 : sext p0 p1 p2 p3 p4 p5 3 = p3 := rfl
theorem sext_4 : sext p0 p1 p2 p3 p4 p5 4 = p4 := rfl
theorem sext_5 : sext p0 p1 p2 p3 p4 p5 5 = p5 := rfl
end sext
theorem z6a : (0 : ZMod 6) + 1 = 1 ∧ (1 : ZMod 6) + 1 = 2 ∧ (2 : ZMod 6) + 1 = 3 ∧
    (3 : ZMod 6) + 1 = 4 ∧ (4 : ZMod 6) + 1 = 5 ∧ (5 : ZMod 6) + 1 = 0 := by decide
theorem z6c (i : ZMod 6) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by revert i; decide

/-! ### X1: rim `(4,6,5,2,0,1)` at the edge view `02`, lexicographic depth predicate. -/

/-- depth predicate for the rim (index `0..5` = vertices `4,6,5,2,0,1`): `z4 < z5 < z0 < z1 < z2, z3`. -/
def Q6x (z : ZMod 6 → ℝ) : Prop :=
  z 4 < z 5 ∧ z 5 < z 0 ∧ z 0 < z 1 ∧ z 1 < z 2 ∧ z 1 < z 3

theorem Q6x_open : IsOpen {z : ZMod 6 → ℝ | Q6x z} := by
  have hlt : ∀ i j : ZMod 6, IsOpen {z : ZMod 6 → ℝ | z i < z j} := fun i j =>
    isOpen_lt (continuous_apply i) (continuous_apply j)
  simp only [Q6x, Set.ofPred_and]
  exact (hlt 4 5).inter ((hlt 5 0).inter ((hlt 0 1).inter ((hlt 1 2).inter (hlt 1 3))))

theorem Q6x_smul {z : ZMod 6 → ℝ} {a : ℝ} (ha : 0 < a) (h : Q6x z) : Q6x fun i => a * z i := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨mul_lt_mul_of_pos_left h1 ha, mul_lt_mul_of_pos_left h2 ha,
    mul_lt_mul_of_pos_left h3 ha, mul_lt_mul_of_pos_left h4 ha, mul_lt_mul_of_pos_left h5 ha⟩

theorem Q6x_shift {z : ZMod 6 → ℝ} (a : ℝ) (h : Q6x z) : Q6x fun i => z i + a := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem zmod6_sub_one' : (0 : ZMod 6) - 1 = 5 ∧ (1 : ZMod 6) - 1 = 0 ∧ (2 : ZMod 6) - 1 = 1 ∧
    (3 : ZMod 6) - 1 = 2 ∧ (4 : ZMod 6) - 1 = 3 ∧ (5 : ZMod 6) - 1 = 4 := by decide

theorem Q6x_unimodal {z : ZMod 6 → ℝ} (hinj : Function.Injective z) (h : Q6x z) :
    IsCyclicUnimodal z := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hc : ∀ i : ZMod 6, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by decide
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := z6a
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := zmod6_sub_one'
  have h23 : z 2 ≠ z 3 := hinj.ne (by decide)
  rcases lt_or_gt_of_ne h23 with h6 | h6
  · refine isCyclicUnimodal_of_top (by norm_num) hinj 3 ?_
    intro i hi
    rcases hc i with rfl | rfl | rfl | rfl | rfl | rfl
    · right; rw [a0]; linarith
    · right; rw [a1]; exact h4
    · right; rw [a2]; exact h6
    · exact absurd rfl hi
    · right; rw [a4]; exact h1
    · right; rw [a5]; linarith
  · refine isCyclicUnimodal_of_top (by norm_num) hinj 2 ?_
    intro i hi
    rcases hc i with rfl | rfl | rfl | rfl | rfl | rfl
    · right; rw [a0]; linarith
    · right; rw [a1]; exact h4
    · exact absurd rfl hi
    · left; rw [b3]; exact h6
    · right; rw [a4]; exact h1
    · right; rw [a5]; linarith

theorem Q6x_eventually {z w : ZMod 6 → ℝ}
    (h1 : z 4 < z 5 ∨ (z 4 = z 5 ∧ w 4 < w 5)) (h2 : z 5 < z 0 ∨ (z 5 = z 0 ∧ w 5 < w 0))
    (h3 : z 0 < z 1 ∨ (z 0 = z 1 ∧ w 0 < w 1)) (h4 : z 1 < z 2 ∨ (z 1 = z 2 ∧ w 1 < w 2))
    (h5 : z 1 < z 3 ∨ (z 1 = z 3 ∧ w 1 < w 3)) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), Q6x fun i => z i + s * w i := by
  filter_upwards [ev_lt h1, ev_lt h2, ev_lt h3, ev_lt h4, ev_lt h5] with s a b c d e
  exact ⟨a, b, c, d, e⟩

/-- X1 points: `x2 = 0`, `tp = sp = t`, `tm = 1-t`, `hp = hm = kp = k t`, `km = k (1-sm)`. -/
noncomputable def pX1 (t k sm : ℝ) : Fin 7 → C3 :=
  ![⟨t, 0, k * t⟩, ⟨0, t, k * t⟩, ⟨0, 0, 0⟩, ⟨1, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1 - t, 0, -(k * t)⟩,
    ⟨0, sm, -(k * (1 - sm))⟩]

/-- the rim `(4,6,5,2,0,1)` -/
noncomputable def cX1 (t k sm : ℝ) : ZMod 6 → C3 :=
  sext ⟨0, 1, 0⟩ ⟨0, sm, -(k * (1 - sm))⟩ ⟨1 - t, 0, -(k * t)⟩ ⟨0, 0, 0⟩ ⟨t, 0, k * t⟩ ⟨0, t, k * t⟩

set_option hygiene false in
macro "stx1" : tactic => `(tactic| first
  | (left; linarith [hk, (mul_pos hk ht), (mul_pos hk ha1), (mul_pos hk ha5), (mul_pos hk ha6), (mul_pos (mul_pos hk ht) ht), (mul_pos (mul_pos hk ht) ha1), (mul_pos (mul_pos hk ht) ha5), (mul_pos (mul_pos hk ht) ha6), (mul_pos (mul_pos hk ha1) ha1), (mul_pos (mul_pos hk ha1) ha5), (mul_pos (mul_pos hk ha1) ha6), (mul_pos (mul_pos hk ha5) ha5), (mul_pos (mul_pos hk ha5) ha6), (mul_pos (mul_pos hk ha6) ha6), (mul_pos (mul_pos (mul_pos hk ht) ht) ht), (mul_pos (mul_pos (mul_pos hk ht) ht) ha1), (mul_pos (mul_pos (mul_pos hk ht) ht) ha5), (mul_pos (mul_pos (mul_pos hk ht) ht) ha6), (mul_pos (mul_pos (mul_pos hk ht) ha1) ha1), (mul_pos (mul_pos (mul_pos hk ht) ha1) ha5), (mul_pos (mul_pos (mul_pos hk ht) ha1) ha6), (mul_pos (mul_pos (mul_pos hk ht) ha5) ha5), (mul_pos (mul_pos (mul_pos hk ht) ha5) ha6), (mul_pos (mul_pos (mul_pos hk ht) ha6) ha6), (mul_pos (mul_pos (mul_pos hk ha1) ha1) ha1), (mul_pos (mul_pos (mul_pos hk ha1) ha1) ha5), (mul_pos (mul_pos (mul_pos hk ha1) ha1) ha6), (mul_pos (mul_pos (mul_pos hk ha1) ha5) ha5), (mul_pos (mul_pos (mul_pos hk ha1) ha5) ha6), (mul_pos (mul_pos (mul_pos hk ha1) ha6) ha6), (mul_pos (mul_pos (mul_pos hk ha5) ha5) ha5), (mul_pos (mul_pos (mul_pos hk ha5) ha5) ha6), (mul_pos (mul_pos (mul_pos hk ha5) ha6) ha6), (mul_pos (mul_pos (mul_pos hk ha6) ha6) ha6), (mul_pos hk hδ), (mul_pos (mul_pos hk hδ) ht), (mul_pos (mul_pos hk hδ) ha1), (mul_pos (mul_pos hk hδ) ha5), (mul_pos (mul_pos hk hδ) ha6), (mul_pos (mul_pos (mul_pos hk hδ) ht) ht), (mul_pos (mul_pos (mul_pos hk hδ) ht) ha1), (mul_pos (mul_pos (mul_pos hk hδ) ht) ha5), (mul_pos (mul_pos (mul_pos hk hδ) ht) ha6), (mul_pos (mul_pos (mul_pos hk hδ) ha1) ha1), (mul_pos (mul_pos (mul_pos hk hδ) ha1) ha5), (mul_pos (mul_pos (mul_pos hk hδ) ha1) ha6), (mul_pos (mul_pos (mul_pos hk hδ) ha5) ha5), (mul_pos (mul_pos (mul_pos hk hδ) ha5) ha6), (mul_pos (mul_pos (mul_pos hk hδ) ha6) ha6), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ht) ht) ht), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ht) ht) ha1), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ht) ht) ha5), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ht) ht) ha6), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ht) ha1) ha1), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ht) ha1) ha5), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ht) ha1) ha6), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ht) ha5) ha5), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ht) ha5) ha6), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ht) ha6) ha6), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ha1) ha1) ha1), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ha1) ha1) ha5), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ha1) ha1) ha6), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ha1) ha5) ha5), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ha1) ha5) ha6), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ha1) ha6) ha6), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ha5) ha5) ha5), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ha5) ha5) ha6), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ha5) ha6) ha6), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ha6) ha6) ha6)])
  | (right; refine ⟨by ring, ?_⟩; linarith [hk, (mul_pos hk ht), (mul_pos hk ha1), (mul_pos hk ha5), (mul_pos hk ha6), (mul_pos (mul_pos hk ht) ht), (mul_pos (mul_pos hk ht) ha1), (mul_pos (mul_pos hk ht) ha5), (mul_pos (mul_pos hk ht) ha6), (mul_pos (mul_pos hk ha1) ha1), (mul_pos (mul_pos hk ha1) ha5), (mul_pos (mul_pos hk ha1) ha6), (mul_pos (mul_pos hk ha5) ha5), (mul_pos (mul_pos hk ha5) ha6), (mul_pos (mul_pos hk ha6) ha6), (mul_pos (mul_pos (mul_pos hk ht) ht) ht), (mul_pos (mul_pos (mul_pos hk ht) ht) ha1), (mul_pos (mul_pos (mul_pos hk ht) ht) ha5), (mul_pos (mul_pos (mul_pos hk ht) ht) ha6), (mul_pos (mul_pos (mul_pos hk ht) ha1) ha1), (mul_pos (mul_pos (mul_pos hk ht) ha1) ha5), (mul_pos (mul_pos (mul_pos hk ht) ha1) ha6), (mul_pos (mul_pos (mul_pos hk ht) ha5) ha5), (mul_pos (mul_pos (mul_pos hk ht) ha5) ha6), (mul_pos (mul_pos (mul_pos hk ht) ha6) ha6), (mul_pos (mul_pos (mul_pos hk ha1) ha1) ha1), (mul_pos (mul_pos (mul_pos hk ha1) ha1) ha5), (mul_pos (mul_pos (mul_pos hk ha1) ha1) ha6), (mul_pos (mul_pos (mul_pos hk ha1) ha5) ha5), (mul_pos (mul_pos (mul_pos hk ha1) ha5) ha6), (mul_pos (mul_pos (mul_pos hk ha1) ha6) ha6), (mul_pos (mul_pos (mul_pos hk ha5) ha5) ha5), (mul_pos (mul_pos (mul_pos hk ha5) ha5) ha6), (mul_pos (mul_pos (mul_pos hk ha5) ha6) ha6), (mul_pos (mul_pos (mul_pos hk ha6) ha6) ha6), (mul_pos hk hδ), (mul_pos (mul_pos hk hδ) ht), (mul_pos (mul_pos hk hδ) ha1), (mul_pos (mul_pos hk hδ) ha5), (mul_pos (mul_pos hk hδ) ha6), (mul_pos (mul_pos (mul_pos hk hδ) ht) ht), (mul_pos (mul_pos (mul_pos hk hδ) ht) ha1), (mul_pos (mul_pos (mul_pos hk hδ) ht) ha5), (mul_pos (mul_pos (mul_pos hk hδ) ht) ha6), (mul_pos (mul_pos (mul_pos hk hδ) ha1) ha1), (mul_pos (mul_pos (mul_pos hk hδ) ha1) ha5), (mul_pos (mul_pos (mul_pos hk hδ) ha1) ha6), (mul_pos (mul_pos (mul_pos hk hδ) ha5) ha5), (mul_pos (mul_pos (mul_pos hk hδ) ha5) ha6), (mul_pos (mul_pos (mul_pos hk hδ) ha6) ha6), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ht) ht) ht), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ht) ht) ha1), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ht) ht) ha5), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ht) ht) ha6), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ht) ha1) ha1), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ht) ha1) ha5), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ht) ha1) ha6), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ht) ha5) ha5), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ht) ha5) ha6), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ht) ha6) ha6), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ha1) ha1) ha1), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ha1) ha1) ha5), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ha1) ha1) ha6), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ha1) ha5) ha5), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ha1) ha5) ha6), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ha1) ha6) ha6), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ha5) ha5) ha5), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ha5) ha5) ha6), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ha5) ha6) ha6), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ha6) ha6) ha6)])
  | linarith [hk, (mul_pos hk ht), (mul_pos hk ha1), (mul_pos hk ha5), (mul_pos hk ha6), (mul_pos (mul_pos hk ht) ht), (mul_pos (mul_pos hk ht) ha1), (mul_pos (mul_pos hk ht) ha5), (mul_pos (mul_pos hk ht) ha6), (mul_pos (mul_pos hk ha1) ha1), (mul_pos (mul_pos hk ha1) ha5), (mul_pos (mul_pos hk ha1) ha6), (mul_pos (mul_pos hk ha5) ha5), (mul_pos (mul_pos hk ha5) ha6), (mul_pos (mul_pos hk ha6) ha6), (mul_pos (mul_pos (mul_pos hk ht) ht) ht), (mul_pos (mul_pos (mul_pos hk ht) ht) ha1), (mul_pos (mul_pos (mul_pos hk ht) ht) ha5), (mul_pos (mul_pos (mul_pos hk ht) ht) ha6), (mul_pos (mul_pos (mul_pos hk ht) ha1) ha1), (mul_pos (mul_pos (mul_pos hk ht) ha1) ha5), (mul_pos (mul_pos (mul_pos hk ht) ha1) ha6), (mul_pos (mul_pos (mul_pos hk ht) ha5) ha5), (mul_pos (mul_pos (mul_pos hk ht) ha5) ha6), (mul_pos (mul_pos (mul_pos hk ht) ha6) ha6), (mul_pos (mul_pos (mul_pos hk ha1) ha1) ha1), (mul_pos (mul_pos (mul_pos hk ha1) ha1) ha5), (mul_pos (mul_pos (mul_pos hk ha1) ha1) ha6), (mul_pos (mul_pos (mul_pos hk ha1) ha5) ha5), (mul_pos (mul_pos (mul_pos hk ha1) ha5) ha6), (mul_pos (mul_pos (mul_pos hk ha1) ha6) ha6), (mul_pos (mul_pos (mul_pos hk ha5) ha5) ha5), (mul_pos (mul_pos (mul_pos hk ha5) ha5) ha6), (mul_pos (mul_pos (mul_pos hk ha5) ha6) ha6), (mul_pos (mul_pos (mul_pos hk ha6) ha6) ha6), (mul_pos hk hδ), (mul_pos (mul_pos hk hδ) ht), (mul_pos (mul_pos hk hδ) ha1), (mul_pos (mul_pos hk hδ) ha5), (mul_pos (mul_pos hk hδ) ha6), (mul_pos (mul_pos (mul_pos hk hδ) ht) ht), (mul_pos (mul_pos (mul_pos hk hδ) ht) ha1), (mul_pos (mul_pos (mul_pos hk hδ) ht) ha5), (mul_pos (mul_pos (mul_pos hk hδ) ht) ha6), (mul_pos (mul_pos (mul_pos hk hδ) ha1) ha1), (mul_pos (mul_pos (mul_pos hk hδ) ha1) ha5), (mul_pos (mul_pos (mul_pos hk hδ) ha1) ha6), (mul_pos (mul_pos (mul_pos hk hδ) ha5) ha5), (mul_pos (mul_pos (mul_pos hk hδ) ha5) ha6), (mul_pos (mul_pos (mul_pos hk hδ) ha6) ha6), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ht) ht) ht), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ht) ht) ha1), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ht) ht) ha5), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ht) ht) ha6), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ht) ha1) ha1), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ht) ha1) ha5), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ht) ha1) ha6), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ht) ha5) ha5), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ht) ha5) ha6), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ht) ha6) ha6), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ha1) ha1) ha1), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ha1) ha1) ha5), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ha1) ha1) ha6), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ha1) ha5) ha5), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ha1) ha5) ha6), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ha1) ha6) ha6), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ha5) ha5) ha5), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ha5) ha5) ha6), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ha5) ha6) ha6), (mul_pos (mul_pos (mul_pos (mul_pos hk hδ) ha6) ha6) ha6)])

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
theorem cyc_X1 (t k δ sm : ℝ) (ht : 0 < t) (ht1 : t < 1) (hk : 0 < k) (hδ : 0 < δ)
    (hs : 1 - t < sm) (hs1 : sm < 1) :
    ∀ i j : ZMod 6, j ≠ i → j ≠ i + 1 →
      CaseC09.ST 1 ⟨-t, 0, -(k * t)⟩ ⟨-1, 1, k * δ⟩
        ((cX1 t k sm (i + 1)).sub (cX1 t k sm i)) ((cX1 t k sm j).sub (cX1 t k sm i)) := by
  have ha1 := sub_pos.2 ht1
  have ha5 := sub_pos.2 hs
  have ha6 := sub_pos.2 hs1
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := z6a
  intro i j h1 h2
  rcases z6c i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases z6c j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [CaseC09.ST, Dc, C3.sub, cX1, b0, b1, b2, b3, b4, b5, sext_0, sext_1, sext_2, sext_3, sext_4, sext_5]
    norm_num
    stx1

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
theorem rest_X1 (t k δ sm : ℝ) (ht : 0 < t) (ht1 : t < 1) (hk : 0 < k) (hδ : 0 < δ)
    (hs : 1 - t < sm) (hs1 : sm < 1) :
    ∀ i : ZMod 6,
      CaseC09.ST 1 ⟨-t, 0, -(k * t)⟩ ⟨-1, 1, k * δ⟩
        ((cX1 t k sm (i + 1)).sub (cX1 t k sm i)) ((pX1 t k sm 3).sub (cX1 t k sm i)) := by
  have ha1 := sub_pos.2 ht1
  have ha5 := sub_pos.2 hs
  have ha6 := sub_pos.2 hs1
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := z6a
  intro i
  rcases z6c i with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, cX1, pX1, b0, b1, b2, b3, b4, b5, sext_0, sext_1, sext_2, sext_3, sext_4, sext_5]
    norm_num
    stx1

/-! ### Metric facts from `F1Rect` and `A12 = A11` -/

namespace Frame02
variable {x : Fin 7 → ℝ³} (F : Frame02 x)

theorem inner_x0x5 : ⟪x 0 - x 2, x 5 - x 2⟫ =
    F.S.tp * F.S.tm * gA11 x - F.S.hp * F.S.hm * ⟪F.e, F.e⟫ := by
  have hue := F.inner_u1_e
  have heu : ⟪F.e, x 3 - x 2⟫ = 0 := by rw [real_inner_comm]; exact hue
  have e0 : x 0 - x 2 = F.S.tp • (x 3 - x 2) + F.S.hp • F.e := by rw [F.x0_eq]; abel
  have e5 : x 5 - x 2 = F.S.tm • (x 3 - x 2) - F.S.hm • F.e := by rw [F.x5_eq]; abel
  have hA : gA11 x = ⟪x 3 - x 2, x 3 - x 2⟫ := rfl
  rw [hA]
  generalize x 3 - x 2 = u at *
  rw [e0, e5]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, hue, heu, RCLike.conj_to_real]
  ring

theorem rect_data (hRect : F1Rect x) :
    F.S.tm = 1 - F.S.tp ∧ F.S.hm = F.S.hp ∧
    ⟪F.e, F.e⟫ * (F.S.hp * F.S.hm) = gA11 x * (F.S.tp * F.S.tm) := by
  obtain ⟨h1, h2⟩ := hRect
  have e0 : x 0 - x 2 = F.S.tp • (x 3 - x 2) + F.S.hp • F.e := by rw [F.x0_eq]; abel
  have e5 : x 5 - x 2 = F.S.tm • (x 3 - x 2) - F.S.hm • F.e := by rw [F.x5_eq]; abel
  rw [e0, e5] at h1
  have := F.toFrame7.coord_zero (a := 1 - F.S.tp - F.S.tm) (b := 0) (c := F.S.hm - F.S.hp) (by
    show (1 - F.S.tp - F.S.tm) • (x 3 - x 2) + (0:ℝ) • (x 4 - x 2) + (F.S.hm - F.S.hp) • F.e = 0
    have : (1 - F.S.tp - F.S.tm) • (x 3 - x 2) + (0:ℝ) • (x 4 - x 2) + (F.S.hm - F.S.hp) • F.e =
      (x 3 - x 2) - ((F.S.tp • (x 3 - x 2) + F.S.hp • F.e) + (F.S.tm • (x 3 - x 2) - F.S.hm • F.e)) := by
      module
    rw [this]; exact sub_eq_zero.mpr h1)
  obtain ⟨c1, -, c3⟩ := this
  rw [F.inner_x0x5] at h2
  refine ⟨by linarith, by linarith, by linarith⟩

include F in
theorem a22_gt (hr : gA12 x = gA11 x) : gA11 x < gA22 x := by
  have hle : gA12 x ≤ gA22 x := F.A12_le_A22
  by_contra hcon
  have heq : gA22 x = gA11 x := by linarith [not_lt.1 hcon]
  have h0 : ⟪(x 4 - x 2) - (x 3 - x 2), (x 4 - x 2) - (x 3 - x 2)⟫ = 0 := by
    have h12 : ⟪x 3 - x 2, x 4 - x 2⟫ = gA11 x := hr
    have h22 : ⟪x 4 - x 2, x 4 - x 2⟫ = gA11 x := heq
    have h11 : ⟪x 3 - x 2, x 3 - x 2⟫ = gA11 x := rfl
    generalize x 3 - x 2 = u at *
    generalize x 4 - x 2 = w at *
    have h12' : ⟪w, u⟫ = gA11 x := by rw [real_inner_comm]; exact h12
    simp only [inner_sub_left, inner_sub_right]
    rw [h12, h12', h22, h11]; ring
  have h1 := inner_self_eq_zero.mp h0
  have := F.toFrame7.coord_zero (a := -1) (b := 1) (c := 0) (by
    show (-1:ℝ) • (x 3 - x 2) + (1:ℝ) • (x 4 - x 2) + (0:ℝ) • F.e = 0
    have : (-1:ℝ) • (x 3 - x 2) + (1:ℝ) • (x 4 - x 2) + (0:ℝ) • F.e = (x 4 - x 2) - (x 3 - x 2) := by
      module
    rw [this]; exact h1)
  exact one_ne_zero this.2.1

end Frame02

/-! ### X1: the depth condition and the theorem -/

set_option maxHeartbeats 1000000 in
theorem X1_Q (a a22 g t k sm δ : ℝ) (ha : 0 < a) (ht : 0 < t) (ht1 : t < 1) (hk : 0 < k) (hδ : 0 < δ)
    (hs : 1 - t < sm) (hs1 : sm < 1) (hmet : g * k ^ 2 * t = (1 - t) * a) (hd : 2 * a * δ = a22 - a) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), Q6x fun i => Gf a a a22 g (cX1 t k sm i) ⟨-t, 0, -(k * t)⟩ +
      s * Gf a a a22 g (cX1 t k sm i) ⟨-1, 1, k * δ⟩ := by
  have hm2 : g * k ^ 2 * t * (1 - sm) = (1 - t) * a * (1 - sm) := by rw [hmet]
  have hm3 : g * k ^ 2 * t * δ = (1 - t) * a * δ := by rw [hmet]
  have p1 := mul_pos ha (sub_pos.2 hs1)
  have p2 := mul_pos ha (sub_pos.2 hs)
  have p3 := mul_pos (mul_pos ha hδ) (sub_pos.2 ht1)
  have p4 := mul_pos (mul_pos ha hδ) ht
  refine Q6x_eventually (z := fun i => Gf a a a22 g (cX1 t k sm i) ⟨-t, 0, -(k * t)⟩)
    (w := fun i => Gf a a a22 g (cX1 t k sm i) ⟨-1, 1, k * δ⟩) ?_ ?_ ?_ ?_ ?_
  · right; simp only [cX1, sext_0, sext_1, sext_2, sext_3, sext_4, sext_5, Gf]
    exact ⟨by ring, by nlinarith⟩
  · right; simp only [cX1, sext_0, sext_1, sext_2, sext_3, sext_4, sext_5, Gf]
    exact ⟨by linear_combination (-t) * hmet, by nlinarith⟩
  · left; simp only [cX1, sext_0, sext_1, sext_2, sext_3, sext_4, sext_5, Gf]
    nlinarith
  · left; simp only [cX1, sext_0, sext_1, sext_2, sext_3, sext_4, sext_5, Gf]
    nlinarith
  · left; simp only [cX1, sext_0, sext_1, sext_2, sext_3, sext_4, sext_5, Gf]
    nlinarith

namespace Frame02
variable {x : Fin 7 → ℝ³} (F : Frame02 x)

theorem right_X1_pf (hr : gA12 x = gA11 x)
    (hA : F.S.tp = F.S.sp) (hB : F.S.tm < F.S.sm) (hRect : F1Rect x) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨htm, hhm, hmet0⟩ := F.rect_data hRect
  have ht := F.S.tp_pos; have ht1 := F.S.tp_lt
  have hsm1 := F.S.sm_lt
  have hhp := F.S.hp_pos
  obtain ⟨k, hk, e1⟩ : ∃ k : ℝ, 0 < k ∧ F.S.hp = k * F.S.tp :=
    ⟨F.S.hp / F.S.tp, div_pos hhp ht, by field_simp⟩
  have n1 : (1 - F.S.tp) ≠ 0 := by linarith
  have e2 : F.S.kp = k * F.S.tp := by
    have := F.S.plane_up
    rw [← hA] at this
    have h2 : F.S.kp = F.S.hp := by
      field_simp at this; linarith
    rw [h2, e1]
  have e3 : F.S.km = k * (1 - F.S.sm) := by
    have := F.S.plane_dn
    rw [htm, hhm, e1] at this
    have h1 : (1 - (1 - F.S.tp)) = F.S.tp := by ring
    rw [h1] at this
    have n2 : (1 - F.S.sm) ≠ 0 := by linarith
    field_simp at this
    linarith
  have hpt : F.toFrame7.ptC = pX1 F.S.tp k F.S.sm := by
    show Frame02.pt F.S = _
    funext j
    fin_cases j <;> simp [Frame02.pt, pX1, e1, e2, e3, htm, hhm, ← hA]
  have hmet : ⟪F.e, F.e⟫ * k ^ 2 * F.S.tp = (1 - F.S.tp) * gA11 x := by
    rw [htm, hhm, e1] at hmet0
    have : (⟪F.e, F.e⟫ * k ^ 2 * F.S.tp - (1 - F.S.tp) * gA11 x) * F.S.tp = 0 := by
      linear_combination hmet0
    have := (mul_eq_zero.mp this).resolve_right ht.ne'
    linarith
  have ha : 0 < gA11 x := real_inner_self_pos.mpr (F.indep.ne_zero 0)
  have hgt := F.a22_gt hr
  obtain ⟨δ, hδ, hd⟩ : ∃ δ : ℝ, 0 < δ ∧ 2 * gA11 x * δ = gA22 x - gA11 x :=
    ⟨(gA22 x - gA11 x) / (2 * gA11 x), div_pos (by linarith) (by linarith), by field_simp⟩
  have hc : ∀ i, F.toFrame7.ptC (sext (4 : Fin 7) 6 5 2 0 1 i) = cX1 F.S.tp k F.S.sm i := by
    intro i
    rcases z6c i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [cX1, sext_0, sext_1, sext_2, sext_3, sext_4, sext_5, hpt, pX1]
  refine F.toFrame7.rupert_rim (k := 6) (by norm_num) (sext (4 : Fin 7) 6 5 2 0 1)
    1 (Or.inl rfl) ⟨-F.S.tp, 0, -(k * F.S.tp)⟩ ⟨-1, 1, k * δ⟩ (Or.inl (by simpa using ht.ne')) ?_ ?_
    Q6x Q6x_open (fun z a ha => Q6x_smul ha) (fun z a => Q6x_shift a) ?_
    (fun z hz hq => Q6x_unimodal hz hq)
  · intro i j h1 h2
    simp only [hc]
    exact cyc_X1 F.S.tp k δ F.S.sm ht ht1 hk hδ (by linarith) hsm1 i j h1 h2
  · intro j' hj' i
    simp only [hc]
    rw [hpt]
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl (hj' 4)
    · exact absurd rfl (hj' 5)
    · exact absurd rfl (hj' 3)
    · exact rest_X1 F.S.tp k δ F.S.sm ht ht1 hk hδ (by linarith) hsm1 i
    · exact absurd rfl (hj' 0)
    · exact absurd rfl (hj' 2)
    · exact absurd rfl (hj' 1)
  · have := X1_Q (gA11 x) (gA22 x) ⟪F.e, F.e⟫ F.S.tp k F.S.sm δ ha ht ht1 hk hδ (by linarith) hsm1 hmet hd
    refine this.mono fun s hs => ?_
    have hG : ∀ i p, F.toFrame7.GG (F.toFrame7.ptC (sext (4 : Fin 7) 6 5 2 0 1 i)) p =
        Gf (gA11 x) (gA11 x) (gA22 x) ⟪F.e, F.e⟫ (cX1 F.S.tp k F.S.sm i) p := by
      intro i p
      rw [hc]
      show Gf (gA11 x) (gA12 x) (gA22 x) _ _ _ = _
      rw [hr]; rfl
    simpa only [hG] using hs

end Frame02

/-! ### X2 (obtuse): rim `(3,5,6,4)` at the edge view `03`, robust depth cycle. -/

noncomputable def pX2 (tp tm hp hm : ℝ) : Fin 7 → C3 :=
  ![⟨tp, 0, hp⟩, ⟨0, tp, hp⟩, ⟨0, 0, 0⟩, ⟨1, 0, 0⟩, ⟨0, 1, 0⟩, ⟨tm, 0, -hm⟩, ⟨0, tm, -hm⟩]

noncomputable def cX2 (tp tm hp hm : ℝ) : ZMod 4 → C3 :=
  quad ⟨1, 0, 0⟩ ⟨tm, 0, -hm⟩ ⟨0, tm, -hm⟩ ⟨0, 1, 0⟩

set_option hygiene false in
macro "stx2" : tactic => `(tactic| first
  | (left; linarith [hhp, (mul_pos hhp htp), (mul_pos hhp htm), (mul_pos hhp a1), (mul_pos hhp a2), (mul_pos hhp a3), (mul_pos (mul_pos hhp htp) htp), (mul_pos (mul_pos hhp htp) htm), (mul_pos (mul_pos hhp htp) a1), (mul_pos (mul_pos hhp htp) a2), (mul_pos (mul_pos hhp htp) a3), (mul_pos (mul_pos hhp htm) htm), (mul_pos (mul_pos hhp htm) a1), (mul_pos (mul_pos hhp htm) a2), (mul_pos (mul_pos hhp htm) a3), (mul_pos (mul_pos hhp a1) a1), (mul_pos (mul_pos hhp a1) a2), (mul_pos (mul_pos hhp a1) a3), (mul_pos (mul_pos hhp a2) a2), (mul_pos (mul_pos hhp a2) a3), (mul_pos (mul_pos hhp a3) a3), hhm, (mul_pos hhm htp), (mul_pos hhm htm), (mul_pos hhm a1), (mul_pos hhm a2), (mul_pos hhm a3), (mul_pos (mul_pos hhm htp) htp), (mul_pos (mul_pos hhm htp) htm), (mul_pos (mul_pos hhm htp) a1), (mul_pos (mul_pos hhm htp) a2), (mul_pos (mul_pos hhm htp) a3), (mul_pos (mul_pos hhm htm) htm), (mul_pos (mul_pos hhm htm) a1), (mul_pos (mul_pos hhm htm) a2), (mul_pos (mul_pos hhm htm) a3), (mul_pos (mul_pos hhm a1) a1), (mul_pos (mul_pos hhm a1) a2), (mul_pos (mul_pos hhm a1) a3), (mul_pos (mul_pos hhm a2) a2), (mul_pos (mul_pos hhm a2) a3), (mul_pos (mul_pos hhm a3) a3), q1, (mul_pos q1 htp), (mul_pos q1 htm), (mul_pos q1 a1), (mul_pos q1 a2), (mul_pos q1 a3), (mul_pos (mul_pos q1 htp) htp), (mul_pos (mul_pos q1 htp) htm), (mul_pos (mul_pos q1 htp) a1), (mul_pos (mul_pos q1 htp) a2), (mul_pos (mul_pos q1 htp) a3), (mul_pos (mul_pos q1 htm) htm), (mul_pos (mul_pos q1 htm) a1), (mul_pos (mul_pos q1 htm) a2), (mul_pos (mul_pos q1 htm) a3), (mul_pos (mul_pos q1 a1) a1), (mul_pos (mul_pos q1 a1) a2), (mul_pos (mul_pos q1 a1) a3), (mul_pos (mul_pos q1 a2) a2), (mul_pos (mul_pos q1 a2) a3), (mul_pos (mul_pos q1 a3) a3), q2, (mul_pos q2 htp), (mul_pos q2 htm), (mul_pos q2 a1), (mul_pos q2 a2), (mul_pos q2 a3), (mul_pos (mul_pos q2 htp) htp), (mul_pos (mul_pos q2 htp) htm), (mul_pos (mul_pos q2 htp) a1), (mul_pos (mul_pos q2 htp) a2), (mul_pos (mul_pos q2 htp) a3), (mul_pos (mul_pos q2 htm) htm), (mul_pos (mul_pos q2 htm) a1), (mul_pos (mul_pos q2 htm) a2), (mul_pos (mul_pos q2 htm) a3), (mul_pos (mul_pos q2 a1) a1), (mul_pos (mul_pos q2 a1) a2), (mul_pos (mul_pos q2 a1) a3), (mul_pos (mul_pos q2 a2) a2), (mul_pos (mul_pos q2 a2) a3), (mul_pos (mul_pos q2 a3) a3)])
  | (right; refine ⟨by ring, ?_⟩; linarith [hhp, (mul_pos hhp htp), (mul_pos hhp htm), (mul_pos hhp a1), (mul_pos hhp a2), (mul_pos hhp a3), (mul_pos (mul_pos hhp htp) htp), (mul_pos (mul_pos hhp htp) htm), (mul_pos (mul_pos hhp htp) a1), (mul_pos (mul_pos hhp htp) a2), (mul_pos (mul_pos hhp htp) a3), (mul_pos (mul_pos hhp htm) htm), (mul_pos (mul_pos hhp htm) a1), (mul_pos (mul_pos hhp htm) a2), (mul_pos (mul_pos hhp htm) a3), (mul_pos (mul_pos hhp a1) a1), (mul_pos (mul_pos hhp a1) a2), (mul_pos (mul_pos hhp a1) a3), (mul_pos (mul_pos hhp a2) a2), (mul_pos (mul_pos hhp a2) a3), (mul_pos (mul_pos hhp a3) a3), hhm, (mul_pos hhm htp), (mul_pos hhm htm), (mul_pos hhm a1), (mul_pos hhm a2), (mul_pos hhm a3), (mul_pos (mul_pos hhm htp) htp), (mul_pos (mul_pos hhm htp) htm), (mul_pos (mul_pos hhm htp) a1), (mul_pos (mul_pos hhm htp) a2), (mul_pos (mul_pos hhm htp) a3), (mul_pos (mul_pos hhm htm) htm), (mul_pos (mul_pos hhm htm) a1), (mul_pos (mul_pos hhm htm) a2), (mul_pos (mul_pos hhm htm) a3), (mul_pos (mul_pos hhm a1) a1), (mul_pos (mul_pos hhm a1) a2), (mul_pos (mul_pos hhm a1) a3), (mul_pos (mul_pos hhm a2) a2), (mul_pos (mul_pos hhm a2) a3), (mul_pos (mul_pos hhm a3) a3), q1, (mul_pos q1 htp), (mul_pos q1 htm), (mul_pos q1 a1), (mul_pos q1 a2), (mul_pos q1 a3), (mul_pos (mul_pos q1 htp) htp), (mul_pos (mul_pos q1 htp) htm), (mul_pos (mul_pos q1 htp) a1), (mul_pos (mul_pos q1 htp) a2), (mul_pos (mul_pos q1 htp) a3), (mul_pos (mul_pos q1 htm) htm), (mul_pos (mul_pos q1 htm) a1), (mul_pos (mul_pos q1 htm) a2), (mul_pos (mul_pos q1 htm) a3), (mul_pos (mul_pos q1 a1) a1), (mul_pos (mul_pos q1 a1) a2), (mul_pos (mul_pos q1 a1) a3), (mul_pos (mul_pos q1 a2) a2), (mul_pos (mul_pos q1 a2) a3), (mul_pos (mul_pos q1 a3) a3), q2, (mul_pos q2 htp), (mul_pos q2 htm), (mul_pos q2 a1), (mul_pos q2 a2), (mul_pos q2 a3), (mul_pos (mul_pos q2 htp) htp), (mul_pos (mul_pos q2 htp) htm), (mul_pos (mul_pos q2 htp) a1), (mul_pos (mul_pos q2 htp) a2), (mul_pos (mul_pos q2 htp) a3), (mul_pos (mul_pos q2 htm) htm), (mul_pos (mul_pos q2 htm) a1), (mul_pos (mul_pos q2 htm) a2), (mul_pos (mul_pos q2 htm) a3), (mul_pos (mul_pos q2 a1) a1), (mul_pos (mul_pos q2 a1) a2), (mul_pos (mul_pos q2 a1) a3), (mul_pos (mul_pos q2 a2) a2), (mul_pos (mul_pos q2 a2) a3), (mul_pos (mul_pos q2 a3) a3)])
  | linarith [hhp, (mul_pos hhp htp), (mul_pos hhp htm), (mul_pos hhp a1), (mul_pos hhp a2), (mul_pos hhp a3), (mul_pos (mul_pos hhp htp) htp), (mul_pos (mul_pos hhp htp) htm), (mul_pos (mul_pos hhp htp) a1), (mul_pos (mul_pos hhp htp) a2), (mul_pos (mul_pos hhp htp) a3), (mul_pos (mul_pos hhp htm) htm), (mul_pos (mul_pos hhp htm) a1), (mul_pos (mul_pos hhp htm) a2), (mul_pos (mul_pos hhp htm) a3), (mul_pos (mul_pos hhp a1) a1), (mul_pos (mul_pos hhp a1) a2), (mul_pos (mul_pos hhp a1) a3), (mul_pos (mul_pos hhp a2) a2), (mul_pos (mul_pos hhp a2) a3), (mul_pos (mul_pos hhp a3) a3), hhm, (mul_pos hhm htp), (mul_pos hhm htm), (mul_pos hhm a1), (mul_pos hhm a2), (mul_pos hhm a3), (mul_pos (mul_pos hhm htp) htp), (mul_pos (mul_pos hhm htp) htm), (mul_pos (mul_pos hhm htp) a1), (mul_pos (mul_pos hhm htp) a2), (mul_pos (mul_pos hhm htp) a3), (mul_pos (mul_pos hhm htm) htm), (mul_pos (mul_pos hhm htm) a1), (mul_pos (mul_pos hhm htm) a2), (mul_pos (mul_pos hhm htm) a3), (mul_pos (mul_pos hhm a1) a1), (mul_pos (mul_pos hhm a1) a2), (mul_pos (mul_pos hhm a1) a3), (mul_pos (mul_pos hhm a2) a2), (mul_pos (mul_pos hhm a2) a3), (mul_pos (mul_pos hhm a3) a3), q1, (mul_pos q1 htp), (mul_pos q1 htm), (mul_pos q1 a1), (mul_pos q1 a2), (mul_pos q1 a3), (mul_pos (mul_pos q1 htp) htp), (mul_pos (mul_pos q1 htp) htm), (mul_pos (mul_pos q1 htp) a1), (mul_pos (mul_pos q1 htp) a2), (mul_pos (mul_pos q1 htp) a3), (mul_pos (mul_pos q1 htm) htm), (mul_pos (mul_pos q1 htm) a1), (mul_pos (mul_pos q1 htm) a2), (mul_pos (mul_pos q1 htm) a3), (mul_pos (mul_pos q1 a1) a1), (mul_pos (mul_pos q1 a1) a2), (mul_pos (mul_pos q1 a1) a3), (mul_pos (mul_pos q1 a2) a2), (mul_pos (mul_pos q1 a2) a3), (mul_pos (mul_pos q1 a3) a3), q2, (mul_pos q2 htp), (mul_pos q2 htm), (mul_pos q2 a1), (mul_pos q2 a2), (mul_pos q2 a3), (mul_pos (mul_pos q2 htp) htp), (mul_pos (mul_pos q2 htp) htm), (mul_pos (mul_pos q2 htp) a1), (mul_pos (mul_pos q2 htp) a2), (mul_pos (mul_pos q2 htp) a3), (mul_pos (mul_pos q2 htm) htm), (mul_pos (mul_pos q2 htm) a1), (mul_pos (mul_pos q2 htm) a2), (mul_pos (mul_pos q2 htm) a3), (mul_pos (mul_pos q2 a1) a1), (mul_pos (mul_pos q2 a1) a2), (mul_pos (mul_pos q2 a1) a3), (mul_pos (mul_pos q2 a2) a2), (mul_pos (mul_pos q2 a2) a3), (mul_pos (mul_pos q2 a3) a3)])

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
theorem cyc_X2 (tp tm hp hm : ℝ) (htp : 0 < tp) (htm : 0 < tm) (hhp : 0 < hp) (hhm : 0 < hm)
    (hs : tp + tm < 1) (hq1 : tm * hp < hm * (1 - tp)) (hq2 : tp * hm < hp * (1 - tm)) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      CaseC09.ST 1 ⟨1 - tp, 0, -hp⟩ ⟨-1, 1, -1⟩
        ((cX2 tp tm hp hm (i + 1)).sub (cX2 tp tm hp hm i)) ((cX2 tp tm hp hm j).sub (cX2 tp tm hp hm i)) := by
  have a1 : 0 < 1 - tp := by linarith
  have a2 : 0 < 1 - tm := by linarith
  have a3 : 0 < 1 - tp - tm := by linarith
  have q1 : 0 < hm * (1 - tp) - tm * hp := by linarith
  have q2 : 0 < hp * (1 - tm) - tp * hm := by linarith
  obtain ⟨b0, b1, b2, b3⟩ := z4a
  intro i j h1 h2
  rcases z4c i with rfl | rfl | rfl | rfl <;>
    rcases z4c j with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [CaseC09.ST, Dc, C3.sub, cX2, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    norm_num
    stx2

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
theorem rest_X2 (tp tm hp hm : ℝ) (htp : 0 < tp) (htm : 0 < tm) (hhp : 0 < hp) (hhm : 0 < hm)
    (hs : tp + tm < 1) (hq1 : tm * hp < hm * (1 - tp)) (hq2 : tp * hm < hp * (1 - tm))
    (j' : Fin 7) (hw : j' = 0 ∨ j' = 1 ∨ j' = 2) :
    ∀ i : ZMod 4,
      CaseC09.ST 1 ⟨1 - tp, 0, -hp⟩ ⟨-1, 1, -1⟩
        ((cX2 tp tm hp hm (i + 1)).sub (cX2 tp tm hp hm i)) ((pX2 tp tm hp hm j').sub (cX2 tp tm hp hm i)) := by
  have a1 : 0 < 1 - tp := by linarith
  have a2 : 0 < 1 - tm := by linarith
  have a3 : 0 < 1 - tp - tm := by linarith
  have q1 : 0 < hm * (1 - tp) - tm * hp := by linarith
  have q2 : 0 < hp * (1 - tm) - tp * hm := by linarith
  obtain ⟨b0, b1, b2, b3⟩ := z4a
  intro i
  rcases hw with rfl | rfl | rfl <;>
  rcases z4c i with rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, cX2, pX2, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    norm_num
    stx2

theorem X2_real (a g tp tm hp hm : ℝ) (ha : 0 < a) (hg : 0 < g) (htp : 0 < tp) (htp1 : tp < 1)
    (htm : 0 < tm) (htm1 : tm < 1) (hhp : 0 < hp) (hhm : 0 < hm)
    (hP : g * hp ^ 2 = a * tp * (1 - tp)) (hQ : g * hm ^ 2 = a * tm * (1 - tm))
    (hob : a * tp * tm < g * hp * hm) :
    tp + tm < 1 ∧ tm * hp < hm * (1 - tp) ∧ tp * hm < hp * (1 - tm) ∧
      g * hp * hm < a * (1 - tp) * (1 - tm) := by
  have a1 : 0 < 1 - tp := by linarith
  have a2 : 0 < 1 - tm := by linarith
  have sq : (g * hp * hm) ^ 2 = a ^ 2 * (tp * tm) * ((1 - tp) * (1 - tm)) := by
    have : (g * hp * hm) ^ 2 = (g * hp ^ 2) * (g * hm ^ 2) := by ring
    rw [this, hP, hQ]; ring
  have hsq : (a * tp * tm) ^ 2 < (g * hp * hm) ^ 2 :=
    pow_lt_pow_left₀ hob (by positivity) two_ne_zero
  have hs : tp + tm < 1 := by
    by_contra hcon
    have h1 : (1 - tp) * (1 - tm) ≤ tp * tm := by nlinarith [not_lt.1 hcon]
    have h2 : a ^ 2 * (tp * tm) * ((1 - tp) * (1 - tm)) ≤ a ^ 2 * (tp * tm) * (tp * tm) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    nlinarith
  have hd : 0 < (1 - tp) * (1 - tm) - tp * tm := by nlinarith
  refine ⟨hs, ?_, ?_, ?_⟩
  · by_contra hcon
    have h := not_lt.1 hcon
    have h2 : (hm * (1 - tp)) ^ 2 ≤ (tm * hp) ^ 2 := pow_le_pow_left₀ (by positivity) h 2
    have h3 : g * (hm * (1 - tp)) ^ 2 ≤ g * (tm * hp) ^ 2 := mul_le_mul_of_nonneg_left h2 hg.le
    have e1 : g * (hm * (1 - tp)) ^ 2 = a * tm * (1 - tm) * (1 - tp) ^ 2 := by
      rw [← hQ]; ring
    have e2 : g * (tm * hp) ^ 2 = tm ^ 2 * (a * tp * (1 - tp)) := by
      rw [← hP]; ring
    have h4 : a * tm * (1 - tp) * ((1 - tp) * (1 - tm) - tp * tm) ≤ 0 := by
      rw [e1, e2] at h3; nlinarith [h3]
    have : 0 < a * tm * (1 - tp) * ((1 - tp) * (1 - tm) - tp * tm) := by positivity
    linarith
  · by_contra hcon
    have h := not_lt.1 hcon
    have h2 : (hp * (1 - tm)) ^ 2 ≤ (tp * hm) ^ 2 := pow_le_pow_left₀ (by positivity) h 2
    have h3 : g * (hp * (1 - tm)) ^ 2 ≤ g * (tp * hm) ^ 2 := mul_le_mul_of_nonneg_left h2 hg.le
    have e1 : g * (hp * (1 - tm)) ^ 2 = a * tp * (1 - tp) * (1 - tm) ^ 2 := by
      rw [← hP]; ring
    have e2 : g * (tp * hm) ^ 2 = tp ^ 2 * (a * tm * (1 - tm)) := by
      rw [← hQ]; ring
    have h4 : a * tp * (1 - tm) * ((1 - tp) * (1 - tm) - tp * tm) ≤ 0 := by
      rw [e1, e2] at h3; nlinarith [h3]
    have : 0 < a * tp * (1 - tm) * ((1 - tp) * (1 - tm) - tp * tm) := by positivity
    linarith
  · refine lt_of_pow_lt_pow_left₀ 2 (by positivity) ?_
    rw [sq]
    have : a ^ 2 * (tp * tm) * ((1 - tp) * (1 - tm)) < (a * (1 - tp) * (1 - tm)) ^ 2 := by
      have : (a * (1 - tp) * (1 - tm)) ^ 2 - a ^ 2 * (tp * tm) * ((1 - tp) * (1 - tm)) =
        a ^ 2 * ((1 - tp) * (1 - tm)) * ((1 - tp) * (1 - tm) - tp * tm) := by ring
      have h5 : 0 < a ^ 2 * ((1 - tp) * (1 - tm)) * ((1 - tp) * (1 - tm) - tp * tm) := by positivity
      linarith
    exact this

namespace Frame02
variable {x : Fin 7 → ℝ³} (F : Frame02 x)

theorem X2_metric (hX : X2Set x) :
    ⟪F.e, F.e⟫ * F.S.hp ^ 2 = gA11 x * F.S.tp * (1 - F.S.tp) ∧
    ⟪F.e, F.e⟫ * F.S.hm ^ 2 = gA11 x * F.S.tm * (1 - F.S.tm) := by
  obtain ⟨hA, hB, -⟩ := hX
  have hue := F.inner_u1_e
  have heu : ⟪F.e, x 3 - x 2⟫ = 0 := by rw [real_inner_comm]; exact hue
  have e0 : x 0 - x 2 = F.S.tp • (x 3 - x 2) + F.S.hp • F.e := by rw [F.x0_eq]; abel
  have e5 : x 5 - x 2 = F.S.tm • (x 3 - x 2) - F.S.hm • F.e := by rw [F.x5_eq]; abel
  have hA11 : gA11 x = ⟪x 3 - x 2, x 3 - x 2⟫ := rfl
  have e30 : x 3 - x 0 = (1 - F.S.tp) • (x 3 - x 2) - F.S.hp • F.e := by
    have : x 3 - x 0 = (x 3 - x 2) - (x 0 - x 2) := by abel
    rw [this, e0]; module
  have e35 : x 3 - x 5 = (1 - F.S.tm) • (x 3 - x 2) + F.S.hm • F.e := by
    have : x 3 - x 5 = (x 3 - x 2) - (x 5 - x 2) := by abel
    rw [this, e5]; module
  have e20 : x 2 - x 0 = -(F.S.tp • (x 3 - x 2) + F.S.hp • F.e) := by rw [← e0]; abel
  have e25 : x 2 - x 5 = -(F.S.tm • (x 3 - x 2) - F.S.hm • F.e) := by rw [← e5]; abel
  rw [e20, e30] at hA
  rw [e25, e35] at hB
  rw [hA11]
  generalize x 3 - x 2 = u at *
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, inner_neg_left,
    inner_smul_left, inner_smul_right, hue, heu, RCLike.conj_to_real] at hA hB
  constructor <;> nlinarith [hA, hB]

end Frame02

namespace Frame02
variable {x : Fin 7 → ℝ³} (F : Frame02 x)

theorem right_X2_obtuse_pf (hr : gA12 x = gA11 x)
    (hA : F.S.tp = F.S.sp) (hB : F.S.tm = F.S.sm) (hX2 : X2Set x)
    (hobt : ⟪x 0 - x 2, x 5 - x 2⟫ < 0) : IsRupert (Finset.univ.image x) := by
  have htp := F.S.tp_pos; have htp1 := F.S.tp_lt
  have htm := F.S.tm_pos; have htm1 := F.S.tm_lt
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos
  have ha : 0 < gA11 x := real_inner_self_pos.mpr (F.indep.ne_zero 0)
  have hg : 0 < ⟪F.e, F.e⟫ := real_inner_self_pos.mpr F.e_ne
  obtain ⟨hP0, hQ0⟩ := F.X2_metric hX2
  rw [F.inner_x0x5] at hobt
  obtain ⟨hs, hq1, hq2, hD⟩ := X2_real (gA11 x) ⟪F.e, F.e⟫ F.S.tp F.S.tm F.S.hp F.S.hm ha hg htp htp1 htm
    htm1 hhp hhm hP0 hQ0 (by nlinarith)
  have e2 : F.S.kp = F.S.hp := by
    have := F.S.plane_up
    rw [← hA] at this
    have n1 : (1 - F.S.tp) ≠ 0 := by linarith
    field_simp at this; linarith
  have e3 : F.S.km = F.S.hm := by
    have := F.S.plane_dn
    rw [← hB] at this
    have n1 : (1 - F.S.tm) ≠ 0 := by linarith
    field_simp at this; linarith
  have hpt : F.toFrame7.ptC = pX2 F.S.tp F.S.tm F.S.hp F.S.hm := by
    show Frame02.pt F.S = _
    funext j
    fin_cases j <;> simp [Frame02.pt, pX2, e2, e3, ← hA, ← hB]
  have hc : ∀ i, F.toFrame7.ptC (quad ((3 : Fin 7)) 5 6 4 i) = cX2 F.S.tp F.S.tm F.S.hp F.S.hm i := by
    intro i
    rcases z4c i with rfl | rfl | rfl | rfl <;>
      simp [cX2, quad_0, quad_1, quad_2, quad_3, hpt, pX2]
  refine F.toFrame7.rupert_rim_rob (k := 4) (by norm_num) (quad ((3 : Fin 7)) 5 6 4)
    1 (Or.inl rfl) ⟨1 - F.S.tp, 0, -F.S.hp⟩ ⟨-1, 1, -1⟩ (Or.inl (by simp; linarith)) ?_ ?_ ?_
  · intro i j h1 h2
    simp only [hc]
    exact cyc_X2 F.S.tp F.S.tm F.S.hp F.S.hm htp htm hhp hhm hs hq1 hq2 i j h1 h2
  · intro j' hj' i
    simp only [hc]
    rw [hpt]
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rest_X2 F.S.tp F.S.tm F.S.hp F.S.hm htp htm hhp hhm hs hq1 hq2 _ (Or.inl rfl) i
    · exact rest_X2 F.S.tp F.S.tm F.S.hp F.S.hm htp htm hhp hhm hs hq1 hq2 _ (Or.inr (Or.inl rfl)) i
    · exact rest_X2 F.S.tp F.S.tm F.S.hp F.S.hm htp htm hhp hhm hs hq1 hq2 _ (Or.inr (Or.inr rfl)) i
    · exact absurd (by simp [quad_0]) (hj' 0)
    · exact absurd (by simp [quad_3]) (hj' 3)
    · exact absurd (by simp [quad_1]) (hj' 1)
    · exact absurd (by simp [quad_2]) (hj' 2)
  · have hG : ∀ i p, F.toFrame7.GG (F.toFrame7.ptC (quad ((3 : Fin 7)) 5 6 4 i)) p =
        Gf (gA11 x) (gA11 x) (gA22 x) ⟪F.e, F.e⟫ (cX2 F.S.tp F.S.tm F.S.hp F.S.hm i) p := by
      intro i p
      rw [hc]
      show Gf (gA11 x) (gA12 x) (gA22 x) _ _ _ = _
      rw [hr]; rfl
    have hz : (fun i : ZMod 4 => F.toFrame7.GG (F.toFrame7.ptC (quad ((3 : Fin 7)) 5 6 4 i))
        ⟨1 - F.S.tp, 0, -F.S.hp⟩) =
        fun i : ZMod 4 => quad (gA11 x * (1 - F.S.tp)) (gA11 x * (1 - F.S.tp) * F.S.tm + ⟪F.e, F.e⟫ * F.S.hp * F.S.hm)
          (gA11 x * (1 - F.S.tp) * F.S.tm + ⟪F.e, F.e⟫ * F.S.hp * F.S.hm) (gA11 x * (1 - F.S.tp)) i := by
      funext i
      rw [hG]
      rcases z4c i with rfl | rfl | rfl | rfl <;>
        simp [quad_0, quad_1, quad_2, quad_3, cX2, Gf] <;> ring
    rw [hz]
    have hlt : gA11 x * (1 - F.S.tp) * F.S.tm + ⟪F.e, F.e⟫ * F.S.hp * F.S.hm < gA11 x * (1 - F.S.tp) := by
      nlinarith
    exact robust_quad_of_nws (Or.inr (Or.inr (Or.inr hlt))) (Or.inl hlt)

end Frame02

/-! ### W: the corner wedge (Theorem 02.W of sp02b), frame form -/

/-- the wedge in the frame `(x0 - x2, x4 - x3, x5 - x2)` -/
noncomputable def wpts (ρ : ℝ) : Fin 7 → C3 :=
  ![⟨1, 0, 0⟩, ⟨1, ρ, 0⟩, ⟨0, 0, 0⟩, ⟨1, 0, 1⟩, ⟨1, 1, 1⟩, ⟨0, 0, 1⟩, ⟨0, 1 - ρ, 1⟩]

set_option hygiene false in
macro "stw" : tactic => `(tactic| first
  | (left; linarith [ha, hb, hρ, hρ1, hγ, hδ, hs, hr, hsb, hP, hf5, (mul_pos ha ha), (mul_pos ha hb), (mul_pos ha hρ), (mul_pos ha hρ1), (mul_pos ha hγ), (mul_pos ha hδ), (mul_pos ha hs), (mul_pos ha hr), (mul_pos ha hsb), (mul_pos ha hP), (mul_pos ha hf5), (mul_pos hb hb), (mul_pos hb hρ), (mul_pos hb hρ1), (mul_pos hb hγ), (mul_pos hb hδ), (mul_pos hb hs), (mul_pos hb hr), (mul_pos hb hsb), (mul_pos hb hP), (mul_pos hb hf5), (mul_pos hρ hρ), (mul_pos hρ hρ1), (mul_pos hρ hγ), (mul_pos hρ hδ), (mul_pos hρ hs), (mul_pos hρ hr), (mul_pos hρ hsb), (mul_pos hρ hP), (mul_pos hρ hf5), (mul_pos hρ1 hρ1), (mul_pos hρ1 hγ), (mul_pos hρ1 hδ), (mul_pos hρ1 hs), (mul_pos hρ1 hr), (mul_pos hρ1 hsb), (mul_pos hρ1 hP), (mul_pos hρ1 hf5), (mul_pos hγ hγ), (mul_pos hγ hδ), (mul_pos hγ hs), (mul_pos hγ hr), (mul_pos hγ hsb), (mul_pos hγ hP), (mul_pos hγ hf5), (mul_pos hδ hδ), (mul_pos hδ hs), (mul_pos hδ hr), (mul_pos hδ hsb), (mul_pos hδ hP), (mul_pos hδ hf5), (mul_pos hs hs), (mul_pos hs hr), (mul_pos hs hsb), (mul_pos hs hP), (mul_pos hs hf5), (mul_pos hr hr), (mul_pos hr hsb), (mul_pos hr hP), (mul_pos hr hf5), (mul_pos hsb hsb), (mul_pos hsb hP), (mul_pos hsb hf5), (mul_pos hP hP), (mul_pos hP hf5), (mul_pos hf5 hf5)])
  | (right; refine ⟨by ring, ?_⟩; linarith [ha, hb, hρ, hρ1, hγ, hδ, hs, hr, hsb, hP, hf5, (mul_pos ha ha), (mul_pos ha hb), (mul_pos ha hρ), (mul_pos ha hρ1), (mul_pos ha hγ), (mul_pos ha hδ), (mul_pos ha hs), (mul_pos ha hr), (mul_pos ha hsb), (mul_pos ha hP), (mul_pos ha hf5), (mul_pos hb hb), (mul_pos hb hρ), (mul_pos hb hρ1), (mul_pos hb hγ), (mul_pos hb hδ), (mul_pos hb hs), (mul_pos hb hr), (mul_pos hb hsb), (mul_pos hb hP), (mul_pos hb hf5), (mul_pos hρ hρ), (mul_pos hρ hρ1), (mul_pos hρ hγ), (mul_pos hρ hδ), (mul_pos hρ hs), (mul_pos hρ hr), (mul_pos hρ hsb), (mul_pos hρ hP), (mul_pos hρ hf5), (mul_pos hρ1 hρ1), (mul_pos hρ1 hγ), (mul_pos hρ1 hδ), (mul_pos hρ1 hs), (mul_pos hρ1 hr), (mul_pos hρ1 hsb), (mul_pos hρ1 hP), (mul_pos hρ1 hf5), (mul_pos hγ hγ), (mul_pos hγ hδ), (mul_pos hγ hs), (mul_pos hγ hr), (mul_pos hγ hsb), (mul_pos hγ hP), (mul_pos hγ hf5), (mul_pos hδ hδ), (mul_pos hδ hs), (mul_pos hδ hr), (mul_pos hδ hsb), (mul_pos hδ hP), (mul_pos hδ hf5), (mul_pos hs hs), (mul_pos hs hr), (mul_pos hs hsb), (mul_pos hs hP), (mul_pos hs hf5), (mul_pos hr hr), (mul_pos hr hsb), (mul_pos hr hP), (mul_pos hr hf5), (mul_pos hsb hsb), (mul_pos hsb hP), (mul_pos hsb hf5), (mul_pos hP hP), (mul_pos hP hf5), (mul_pos hf5 hf5)])
  | linarith [ha, hb, hρ, hρ1, hγ, hδ, hs, hr, hsb, hP, hf5, (mul_pos ha ha), (mul_pos ha hb), (mul_pos ha hρ), (mul_pos ha hρ1), (mul_pos ha hγ), (mul_pos ha hδ), (mul_pos ha hs), (mul_pos ha hr), (mul_pos ha hsb), (mul_pos ha hP), (mul_pos ha hf5), (mul_pos hb hb), (mul_pos hb hρ), (mul_pos hb hρ1), (mul_pos hb hγ), (mul_pos hb hδ), (mul_pos hb hs), (mul_pos hb hr), (mul_pos hb hsb), (mul_pos hb hP), (mul_pos hb hf5), (mul_pos hρ hρ), (mul_pos hρ hρ1), (mul_pos hρ hγ), (mul_pos hρ hδ), (mul_pos hρ hs), (mul_pos hρ hr), (mul_pos hρ hsb), (mul_pos hρ hP), (mul_pos hρ hf5), (mul_pos hρ1 hρ1), (mul_pos hρ1 hγ), (mul_pos hρ1 hδ), (mul_pos hρ1 hs), (mul_pos hρ1 hr), (mul_pos hρ1 hsb), (mul_pos hρ1 hP), (mul_pos hρ1 hf5), (mul_pos hγ hγ), (mul_pos hγ hδ), (mul_pos hγ hs), (mul_pos hγ hr), (mul_pos hγ hsb), (mul_pos hγ hP), (mul_pos hγ hf5), (mul_pos hδ hδ), (mul_pos hδ hs), (mul_pos hδ hr), (mul_pos hδ hsb), (mul_pos hδ hP), (mul_pos hδ hf5), (mul_pos hs hs), (mul_pos hs hr), (mul_pos hs hsb), (mul_pos hs hP), (mul_pos hs hf5), (mul_pos hr hr), (mul_pos hr hsb), (mul_pos hr hP), (mul_pos hr hf5), (mul_pos hsb hsb), (mul_pos hsb hP), (mul_pos hsb hf5), (mul_pos hP hP), (mul_pos hP hf5), (mul_pos hf5 hf5)])

/-- base view `e_Z` and tilt `γ e_X - δ e_y`. -/
def wU : C3 := ⟨0, 0, 1⟩
def wD (γ δ : ℝ) : C3 := ⟨γ, -δ, 0⟩

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
theorem wrow2 (ρ a b γ δ s r : ℝ) (ha : 0 < a) (hb : 0 < b) (hρ : 0 < ρ) (hρ1 : 0 < 1 - ρ)
    (hγ : 0 < γ) (hδ : 0 < δ) (hs : 0 < s) (hr : 0 < r) (hsb : 0 < b * ρ - s) (hP : 0 < b - s)
    (hf5 : 0 < δ * (b - s) + γ * (-a - ρ * s - r)) (V : C3) (hx : V.x = -γ) (hy : V.y = 2 * δ) :
    CaseC09.ST 1 wU (wD γ δ) ((wpts ρ 0).sub (wpts ρ 2)) ((wpts ρ 5).sub (wpts ρ 2)) ∧
    CaseC09.ST 1 wU (wD γ δ) ((wpts ρ 0).sub (wpts ρ 2)) V ∧
    CaseC09.ST 1 wU (wD γ δ) ((wpts ρ 2).sub (wpts ρ 5)) V := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [CaseC09.ST, wU, wD, Dc, C3.sub, wpts, hx, hy]
    norm_num
    stw

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
theorem wrow0 (ρ a b γ δ s r : ℝ) (ha : 0 < a) (hb : 0 < b) (hρ : 0 < ρ) (hρ1 : 0 < 1 - ρ)
    (hγ : 0 < γ) (hδ : 0 < δ) (hs : 0 < s) (hr : 0 < r) (hsb : 0 < b * ρ - s) (hP : 0 < b - s)
    (hf5 : 0 < δ * (b - s) + γ * (-a - ρ * s - r)) (V : C3) (hx : V.x = -γ) (hy : V.y = a + 2 * δ) :
    CaseC09.ST 1 wU (wD γ δ) ((wpts ρ 1).sub (wpts ρ 0)) ((wpts ρ 2).sub (wpts ρ 0)) ∧
    CaseC09.ST 1 wU (wD γ δ) ((wpts ρ 1).sub (wpts ρ 0)) V ∧
    CaseC09.ST 1 wU (wD γ δ) ((wpts ρ 0).sub (wpts ρ 2)) V := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [CaseC09.ST, wU, wD, Dc, C3.sub, wpts, hx, hy]
    norm_num
    stw

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
theorem wrow1 (ρ a b γ δ s r : ℝ) (ha : 0 < a) (hb : 0 < b) (hρ : 0 < ρ) (hρ1 : 0 < 1 - ρ)
    (hγ : 0 < γ) (hδ : 0 < δ) (hs : 0 < s) (hr : 0 < r) (hsb : 0 < b * ρ - s) (hP : 0 < b - s)
    (hf5 : 0 < δ * (b - s) + γ * (-a - ρ * s - r)) (V : C3) (hx : V.x = -γ - b * ρ) (hy : V.y = a + 2 * δ) :
    CaseC09.ST 1 wU (wD γ δ) ((wpts ρ 4).sub (wpts ρ 1)) ((wpts ρ 0).sub (wpts ρ 1)) ∧
    CaseC09.ST 1 wU (wD γ δ) ((wpts ρ 4).sub (wpts ρ 1)) V ∧
    CaseC09.ST 1 wU (wD γ δ) ((wpts ρ 1).sub (wpts ρ 0)) V := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [CaseC09.ST, wU, wD, Dc, C3.sub, wpts, hx, hy]
    norm_num
    stw

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
theorem wrow4 (ρ a b γ δ s r : ℝ) (ha : 0 < a) (hb : 0 < b) (hρ : 0 < ρ) (hρ1 : 0 < 1 - ρ)
    (hγ : 0 < γ) (hδ : 0 < δ) (hs : 0 < s) (hr : 0 < r) (hsb : 0 < b * ρ - s) (hP : 0 < b - s)
    (hf5 : 0 < δ * (b - s) + γ * (-a - ρ * s - r)) (V : C3) (hx : V.x = -s) (hy : V.y = -(ρ * s) - r) :
    CaseC09.ST 1 wU (wD γ δ) ((wpts ρ 6).sub (wpts ρ 4)) ((wpts ρ 1).sub (wpts ρ 4)) ∧
    CaseC09.ST 1 wU (wD γ δ) ((wpts ρ 6).sub (wpts ρ 4)) V ∧
    CaseC09.ST 1 wU (wD γ δ) ((wpts ρ 4).sub (wpts ρ 1)) V := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [CaseC09.ST, wU, wD, Dc, C3.sub, wpts, hx, hy]
    norm_num
    stw

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
theorem wrow6 (ρ a b γ δ s r : ℝ) (ha : 0 < a) (hb : 0 < b) (hρ : 0 < ρ) (hρ1 : 0 < 1 - ρ)
    (hγ : 0 < γ) (hδ : 0 < δ) (hs : 0 < s) (hr : 0 < r) (hsb : 0 < b * ρ - s) (hP : 0 < b - s)
    (hf5 : 0 < δ * (b - s) + γ * (-a - ρ * s - r)) (V : C3) (hx : V.x = b * ρ - s) (hy : V.y = -a - ρ * s - r) :
    CaseC09.ST 1 wU (wD γ δ) ((wpts ρ 5).sub (wpts ρ 6)) ((wpts ρ 4).sub (wpts ρ 6)) ∧
    CaseC09.ST 1 wU (wD γ δ) ((wpts ρ 5).sub (wpts ρ 6)) V ∧
    CaseC09.ST 1 wU (wD γ δ) ((wpts ρ 6).sub (wpts ρ 4)) V := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [CaseC09.ST, wU, wD, Dc, C3.sub, wpts, hx, hy]
    norm_num
    stw

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
theorem wrow5 (ρ a b γ δ s r : ℝ) (ha : 0 < a) (hb : 0 < b) (hρ : 0 < ρ) (hρ1 : 0 < 1 - ρ)
    (hγ : 0 < γ) (hδ : 0 < δ) (hs : 0 < s) (hr : 0 < r) (hsb : 0 < b * ρ - s) (hP : 0 < b - s)
    (hf5 : 0 < δ * (b - s) + γ * (-a - ρ * s - r)) (V : C3) (hx : V.x = b - s) (hy : V.y = -a - ρ * s - r) :
    CaseC09.ST 1 wU (wD γ δ) ((wpts ρ 2).sub (wpts ρ 5)) ((wpts ρ 6).sub (wpts ρ 5)) ∧
    CaseC09.ST 1 wU (wD γ δ) ((wpts ρ 2).sub (wpts ρ 5)) V ∧
    CaseC09.ST 1 wU (wD γ δ) ((wpts ρ 5).sub (wpts ρ 6)) V := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [CaseC09.ST, wU, wD, Dc, C3.sub, wpts, hx, hy]
    norm_num
    stw

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
theorem wtri (ρ a b γ δ : ℝ) (ha : 0 < a) (hb : 0 < b) (hρ : 0 < ρ) (hρ1 : 0 < 1 - ρ)
    (hγ : 0 < γ) (hδ : 0 < δ) (hs : 0 < γ) (hr : 0 < γ) (hsb : 0 < γ) (hP : 0 < γ) (hf5 : 0 < γ) :
    CaseC09.ST 1 wU (wD γ δ) ((wpts ρ 0).sub (wpts ρ 2)) ((wpts ρ 4).sub (wpts ρ 2)) ∧
    CaseC09.ST 1 wU (wD γ δ) ((wpts ρ 0).sub (wpts ρ 2)) ((wpts ρ 3).sub (wpts ρ 2)) ∧
    CaseC09.ST 1 wU (wD γ δ) ((wpts ρ 4).sub (wpts ρ 0)) ((wpts ρ 3).sub (wpts ρ 0)) ∧
    CaseC09.ST 1 wU (wD γ δ) ((wpts ρ 2).sub (wpts ρ 4)) ((wpts ρ 3).sub (wpts ρ 4)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [CaseC09.ST, wU, wD, Dc, C3.sub, wpts]
    norm_num <;> stw

theorem Dc_tilt' (a b W d : C3) (ε : ℝ) :
    Dc a b (C3.tilt W d ε) = Dc a b W + ε * Dc a b d := by
  simp only [Dc, C3.tilt]; ring

theorem ev_ST {a b W d : C3} (h : CaseC09.ST 1 W d a b) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < 1 * Dc a b (C3.tilt W d ε) := by
  have h' : 0 < 1 * Dc a b W ∨ (1 * Dc a b W = 0 ∧ 0 < 1 * Dc a b d) := by
    rcases h with h | ⟨h0, h1⟩
    · exact Or.inl h
    · exact Or.inr ⟨by rw [one_mul, h0], by linarith⟩
  filter_upwards [eventually_pos_affine h'] with ε hε
  rw [Dc_tilt']; linarith

namespace Frame7
variable {x : Fin 7 → ℝ³} (G : Frame7 x)

theorem ev_corner (U D ωc m : C3) (j j0 j1 : Fin 7)
    (c1 : CaseC09.ST 1 U D ((G.ptC j1).sub (G.ptC j)) ((G.ptC j0).sub (G.ptC j)))
    (c2 : CaseC09.ST 1 U D ((G.ptC j1).sub (G.ptC j)) (G.velC ωc m (G.ptC j)))
    (c3 : CaseC09.ST 1 U D ((G.ptC j).sub (G.ptC j0)) (G.velC ωc m (G.ptC j))) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), G.FoCert 1 (C3.tilt U D ε) ωc m j := by
  filter_upwards [ev_ST c1, ev_ST c2, ev_ST c3] with ε h1 h2 h3
  exact Or.inl ⟨j0, j1, h1, h2, h3⟩

theorem ev_tri (U D ωc m : C3) (j a b c : Fin 7)
    (c0 : CaseC09.ST 1 U D ((G.ptC b).sub (G.ptC a)) ((G.ptC c).sub (G.ptC a)))
    (c1 : CaseC09.ST 1 U D ((G.ptC b).sub (G.ptC a)) ((G.ptC j).sub (G.ptC a)))
    (c2 : CaseC09.ST 1 U D ((G.ptC c).sub (G.ptC b)) ((G.ptC j).sub (G.ptC b)))
    (c3 : CaseC09.ST 1 U D ((G.ptC a).sub (G.ptC c)) ((G.ptC j).sub (G.ptC c))) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), G.FoCert 1 (C3.tilt U D ε) ωc m j := by
  filter_upwards [ev_ST c0, ev_ST c1, ev_ST c2, ev_ST c3] with ε h0 h1 h2 h3
  exact Or.inr ⟨a, b, c, h0, h1, h2, h3⟩

theorem vel_xy (h12 : G.a12 = 0) (wx wy tx ty : ℝ) (p : C3) :
    (G.velC ⟨-(G.a22 * wy) / G.kap, G.a11 * wx / G.kap, G.a11 * G.a22 / G.kap⟩ ⟨tx, ty, 0⟩ p).x =
      wx * p.z - G.a22 * p.y + tx ∧
    (G.velC ⟨-(G.a22 * wy) / G.kap, G.a11 * wx / G.kap, G.a11 * G.a22 / G.kap⟩ ⟨tx, ty, 0⟩ p).y =
      G.a11 * p.x + wy * p.z + ty := by
  have hκ := G.kap_ne
  have h1 : 0 < G.a11 := by
    have h := G.GG_self_pos ⟨1, 0, 0⟩ (Or.inl one_ne_zero)
    simpa [GG, Gf] using h
  have h2 : 0 < G.a22 := by
    have h := G.GG_self_pos ⟨0, 1, 0⟩ (Or.inr (Or.inl one_ne_zero))
    simpa [GG, Gf] using h
  have hn : G.a11 * G.a22 - G.a12 ^ 2 ≠ 0 := by rw [h12]; nlinarith [mul_pos h1 h2]
  have hg := G.gg_pos
  constructor
  · simp only [velC, crossC, C3.add, h12]
    field_simp
    ring
  · simp only [velC, crossC, C3.add, h12]
    field_simp
    ring

set_option maxHeartbeats 1600000 in
/-- **Theorem 02.W** in the frame `diag(a, b, gg)`: the corner wedge is Rupert. -/
theorem wedge_rupert (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) (h12 : G.a12 = 0)
    (hpt : G.ptC = wpts ρ) : IsRupert (Finset.univ.image x) := by
  have ha : 0 < G.a11 := by
    have h := G.GG_self_pos ⟨1, 0, 0⟩ (Or.inl one_ne_zero)
    simpa [GG, Gf] using h
  have hb : 0 < G.a22 := by
    have h := G.GG_self_pos ⟨0, 1, 0⟩ (Or.inr (Or.inl one_ne_zero))
    simpa [GG, Gf] using h
  have hρ1' : 0 < 1 - ρ := by linarith
  have hκ := G.kap_ne
  obtain ⟨γ, hγdef⟩ : ∃ γ : ℝ, γ = G.a22 / (2 * G.a11) := ⟨_, rfl⟩
  have hγ : 0 < γ := by rw [hγdef]; positivity
  have hγa : γ * G.a11 = G.a22 / 2 := by rw [hγdef]; field_simp
  obtain ⟨s, hs0, hsb', hs2⟩ : ∃ s : ℝ, 0 < s ∧ s < G.a22 * ρ ∧ s * (1 + γ * ρ) < G.a22 / 4 := by
    have hq : 0 < 1 + γ * ρ := by positivity
    refine ⟨min (G.a22 * ρ / 2) (G.a22 / (8 * (1 + γ * ρ))), lt_min (by positivity) (by positivity), ?_, ?_⟩
    · have := min_le_left (G.a22 * ρ / 2) (G.a22 / (8 * (1 + γ * ρ)))
      nlinarith [mul_pos hb hρ]
    · have h1 := min_le_right (G.a22 * ρ / 2) (G.a22 / (8 * (1 + γ * ρ)))
      have h2 : min (G.a22 * ρ / 2) (G.a22 / (8 * (1 + γ * ρ))) * (1 + γ * ρ) ≤
          G.a22 / (8 * (1 + γ * ρ)) * (1 + γ * ρ) := mul_le_mul_of_nonneg_right h1 hq.le
      have h3 : G.a22 / (8 * (1 + γ * ρ)) * (1 + γ * ρ) = G.a22 / 8 := by field_simp
      linarith
  have hr : 0 < G.a11 / 4 := by positivity
  have hsb : 0 < G.a22 * ρ - s := by linarith
  have hP : 0 < G.a22 - s := by nlinarith [mul_pos hb hρ1']
  have hf5 : 0 < 1 * (G.a22 - s) + γ * (-G.a11 - ρ * s - G.a11 / 4) := by nlinarith [hγa, hs2]
  obtain ⟨ωc, hωc⟩ : ∃ ωc : C3, ωc = ⟨-(G.a22 * (-G.a11 - ρ * s - G.a11 / 4 - 2 * 1)) / G.kap,
      G.a11 * (G.a22 - s + γ) / G.kap, G.a11 * G.a22 / G.kap⟩ := ⟨_, rfl⟩
  have hv : ∀ p : C3, (G.velC ωc ⟨-γ, 2 * 1, 0⟩ p).x = (G.a22 - s + γ) * p.z - G.a22 * p.y + -γ ∧
      (G.velC ωc ⟨-γ, 2 * 1, 0⟩ p).y = G.a11 * p.x + (-G.a11 - ρ * s - G.a11 / 4 - 2 * 1) * p.z + 2 * 1 := by
    intro p; rw [hωc]; exact G.vel_xy h12 _ _ _ _ p
  refine G.rupert_of_foCert_eventually 1 (Or.inl rfl) wU (wD γ 1) ωc ⟨-γ, 2 * 1, 0⟩
    (Or.inr (Or.inr (by simp [wU]))) ?_
  rw [Filter.eventually_all]
  intro j
  rcases fin7_cases j with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨k1, k2, k3⟩ := wrow0 ρ G.a11 G.a22 γ 1 s (G.a11 / 4) ha hb hρ hρ1' hγ one_pos hs0 hr hsb hP hf5
      (G.velC ωc ⟨-γ, 2 * 1, 0⟩ (wpts ρ 0)) (by rw [(hv _).1]; norm_num [wpts] <;> ring)
      (by rw [(hv _).2]; norm_num [wpts] <;> ring)
    rw [← hpt] at k1 k2 k3
    exact G.ev_corner _ _ _ _ 0 2 1 k1 k2 k3
  · obtain ⟨k1, k2, k3⟩ := wrow1 ρ G.a11 G.a22 γ 1 s (G.a11 / 4) ha hb hρ hρ1' hγ one_pos hs0 hr hsb hP hf5
      (G.velC ωc ⟨-γ, 2 * 1, 0⟩ (wpts ρ 1)) (by rw [(hv _).1]; norm_num [wpts] <;> ring)
      (by rw [(hv _).2]; norm_num [wpts] <;> ring)
    rw [← hpt] at k1 k2 k3
    exact G.ev_corner _ _ _ _ 1 0 4 k1 k2 k3
  · obtain ⟨k1, k2, k3⟩ := wrow2 ρ G.a11 G.a22 γ 1 s (G.a11 / 4) ha hb hρ hρ1' hγ one_pos hs0 hr hsb hP hf5
      (G.velC ωc ⟨-γ, 2 * 1, 0⟩ (wpts ρ 2)) (by rw [(hv _).1]; norm_num [wpts] <;> ring)
      (by rw [(hv _).2]; norm_num [wpts] <;> ring)
    rw [← hpt] at k1 k2 k3
    exact G.ev_corner _ _ _ _ 2 5 0 k1 k2 k3
  · obtain ⟨k0, k1, k2, k3⟩ := wtri ρ G.a11 G.a22 γ 1 ha hb hρ hρ1' hγ one_pos hγ hγ hγ hγ hγ
    rw [← hpt] at k0 k1 k2 k3
    exact G.ev_tri _ _ _ _ 3 2 0 4 k0 k1 k2 k3
  · obtain ⟨k1, k2, k3⟩ := wrow4 ρ G.a11 G.a22 γ 1 s (G.a11 / 4) ha hb hρ hρ1' hγ one_pos hs0 hr hsb hP hf5
      (G.velC ωc ⟨-γ, 2 * 1, 0⟩ (wpts ρ 4)) (by rw [(hv _).1]; norm_num [wpts] <;> ring)
      (by rw [(hv _).2]; norm_num [wpts] <;> ring)
    rw [← hpt] at k1 k2 k3
    exact G.ev_corner _ _ _ _ 4 1 6 k1 k2 k3
  · obtain ⟨k1, k2, k3⟩ := wrow5 ρ G.a11 G.a22 γ 1 s (G.a11 / 4) ha hb hρ hρ1' hγ one_pos hs0 hr hsb hP hf5
      (G.velC ωc ⟨-γ, 2 * 1, 0⟩ (wpts ρ 5)) (by rw [(hv _).1]; norm_num [wpts] <;> ring)
      (by rw [(hv _).2]; norm_num [wpts] <;> ring)
    rw [← hpt] at k1 k2 k3
    exact G.ev_corner _ _ _ _ 5 6 2 k1 k2 k3
  · obtain ⟨k1, k2, k3⟩ := wrow6 ρ G.a11 G.a22 γ 1 s (G.a11 / 4) ha hb hρ hρ1' hγ one_pos hs0 hr hsb hP hf5
      (G.velC ωc ⟨-γ, 2 * 1, 0⟩ (wpts ρ 6)) (by rw [(hv _).1]; norm_num [wpts] <;> ring)
      (by rw [(hv _).2]; norm_num [wpts] <;> ring)
    rw [← hpt] at k1 k2 k3
    exact G.ev_corner _ _ _ _ 6 4 5 k1 k2 k3

end Frame7

theorem orth3 (U W E : ℝ³) (t h : ℝ) (hUE : ⟪U, E⟫ = 0) (hWE : ⟪W, E⟫ = 0)
    (hUW : ⟪U, W⟫ = ⟪U, U⟫) :
    ⟪t • U + h • E, W - U⟫ = 0 ∧ ⟪W - U, (1 - t) • U - h • E⟫ = 0 := by
  have hEU : ⟪E, U⟫ = 0 := by rw [real_inner_comm]; exact hUE
  have hEW : ⟪E, W⟫ = 0 := by rw [real_inner_comm]; exact hWE
  have hWU : ⟪W, U⟫ = ⟪U, U⟫ := by rw [real_inner_comm]; exact hUW
  constructor <;>
  · simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      inner_smul_left, inner_smul_right, hUE, hWE, hEU, hEW, hUW, hWU, RCLike.conj_to_real]
    ring

namespace Frame02
variable {x : Fin 7 → ℝ³} (F : Frame02 x)

theorem right_X12_pf (hr : gA12 x = gA11 x)
    (hA : F.S.tp = F.S.sp) (hB : F.S.tm = F.S.sm) (hRect : F1Rect x) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨htm, hhm, hmet0⟩ := F.rect_data hRect
  have ht := F.S.tp_pos; have ht1 := F.S.tp_lt
  have hhp := F.S.hp_pos
  have e2 : F.S.kp = F.S.hp := by
    have := F.S.plane_up
    rw [← hA] at this
    have n1 : (1 - F.S.tp) ≠ 0 := by linarith
    field_simp at this; linarith
  have e3 : F.S.km = F.S.hm := by
    have := F.S.plane_dn
    rw [← hB] at this
    have n1 : (1 - F.S.tm) ≠ 0 := by linarith
    field_simp at this; linarith
  have hue := F.inner_u1_e
  have hwe := F.inner_u2_e
  have hUW : ⟪x 3 - x 2, x 4 - x 2⟫ = ⟪x 3 - x 2, x 3 - x 2⟫ := hr
  have e0 : x 0 - x 2 = F.S.tp • (x 3 - x 2) + F.S.hp • F.e := by rw [F.x0_eq]; abel
  have e5 : x 5 - x 2 = (1 - F.S.tp) • (x 3 - x 2) - F.S.hp • F.e := by
    rw [F.x5_eq, htm, hhm]; module
  have f2 : x 4 - x 3 = (x 4 - x 2) - (x 3 - x 2) := by abel
  obtain ⟨o12, o23⟩ := orth3 (x 3 - x 2) (x 4 - x 2) F.e F.S.tp F.S.hp hue hwe hUW
  rw [← e0, ← f2] at o12
  rw [← f2, ← e5] at o23
  have o13 : ⟪x 0 - x 2, x 5 - x 2⟫ = 0 := hRect.2
  have n1 : x 0 - x 2 ≠ 0 := by
    intro h0
    rw [e0] at h0
    have := F.toFrame7.coord_zero (a := F.S.tp) (b := 0) (c := F.S.hp) (by
      show F.S.tp • (x 3 - x 2) + (0:ℝ) • (x 4 - x 2) + F.S.hp • F.e = 0
      rw [zero_smul, add_zero]; exact h0)
    exact ht.ne' this.1
  have n3 : x 5 - x 2 ≠ 0 := by
    intro h0
    rw [e5] at h0
    have := F.toFrame7.coord_zero (a := 1 - F.S.tp) (b := 0) (c := -F.S.hp) (by
      show (1 - F.S.tp) • (x 3 - x 2) + (0:ℝ) • (x 4 - x 2) + (-F.S.hp) • F.e = 0
      rw [zero_smul, add_zero, neg_smul, ← sub_eq_add_neg]; exact h0)
    linarith [this.1]
  have n2 : x 4 - x 3 ≠ 0 := by
    intro h0
    rw [f2] at h0
    have := F.toFrame7.coord_zero (a := -1) (b := 1) (c := 0) (by
      show (-1:ℝ) • (x 3 - x 2) + (1:ℝ) • (x 4 - x 2) + (0:ℝ) • F.e = 0
      have : (-1:ℝ) • (x 3 - x 2) + (1:ℝ) • (x 4 - x 2) + (0:ℝ) • F.e = (x 4 - x 2) - (x 3 - x 2) := by
        module
      rw [this]; exact h0)
    exact one_ne_zero this.2.1
  have hind : LinearIndependent ℝ ![x 0 - x 2, x 4 - x 3, x 5 - x 2] := by
    refine linearIndependent_of_ne_zero_of_inner_eq_zero ?_ ?_
    · intro i; fin_cases i <;> simpa using ‹_›
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
      first | exact o12 | exact o13 | exact o23 | (rw [real_inner_comm]; exact o12) |
        (rw [real_inner_comm]; exact o13) | (rw [real_inner_comm]; exact o23)
  have hxe : ∀ j : Fin 7, x j = x 2 + (wpts F.S.tp j).x • (x 0 - x 2) + (wpts F.S.tp j).y • (x 4 - x 3) +
      (wpts F.S.tp j).z • (x 5 - x 2) := by
    intro j
    rcases fin7_cases j with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · norm_num [wpts] <;>
      simp only [F.x0_eq, F.x1_eq, F.x5_eq, F.x6_eq, htm, hhm, e2, e3, ← hA, ← hB] <;> module
  let G : Frame7 x :=
    { base := x 2, u1 := x 0 - x 2, u2 := x 4 - x 3, e := x 5 - x 2, indep := hind
      inner_u1_e := o13, inner_u2_e := o23
      ptC := wpts F.S.tp, x_eq := hxe }
  exact G.wedge_rupert F.S.tp ht ht1 o12 rfl

end Frame02

end Minimality.CaseC18
