module

public import Minimality.Type02Frame

@[expose] public section

/-! # sp02 Lean, group R: right far angle at `x3` (`A12 = A11`).  Theorem 02.R, sp02 draft §5.

The 34 view `u = ⟨-1, 1, 0⟩` kills `x + y`; its screen is `(s, c) = (x + y, z)`.  With `A12 = A11` the
depth is `z(p) = p.y * D`, `D = A22 - A12 > 0`.  All tilts are `v = ⟨∓1, 0, 0⟩` (screen direction `∓s`). -/

namespace Minimality.CaseC18
open Finset Filter Minimality.CaseC09
open scoped RealInnerProductSpace Topology


set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
theorem rob5 {z0 z1 z2 z3 z4 : ℝ} (h1 : z1 < z2) (h2 : z2 < z3) (h3 : z4 < z3) (h4 : z0 < z4) :
    IsRobustUnimodal (k := 5) (fun i : ZMod 5 => ![z0, z1, z2, z3, z4] i) := by
  have hB : ∀ B : ZMod 5, B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by decide
  refine ⟨?_, ?_, ?_⟩
  · intro B a b c d hab hbc hcd hdk
    interval_cases d <;> interval_cases c <;> (try omega) <;> interval_cases b <;> (try omega) <;> interval_cases a <;> (try omega) <;> rcases hB B with rfl | rfl | rfl | rfl | rfl <;> norm_num <;> intros <;> linarith
  · intro i j l hij hjl hil e1 e2
    rcases hB i with rfl | rfl | rfl | rfl | rfl <;> rcases hB j with rfl | rfl | rfl | rfl | rfl <;> rcases hB l with rfl | rfl | rfl | rfl | rfl <;> simp at hij hjl hil <;> norm_num at e1 e2 <;> linarith
  · intro B a b c d hab hbc hcd hdk e
    interval_cases d <;> interval_cases c <;> (try omega) <;> interval_cases b <;> (try omega) <;> interval_cases a <;> (try omega) <;> rcases hB B with rfl | rfl | rfl | rfl | rfl <;> norm_num at e ⊢ <;> intros <;> constructor <;> intro hh <;> linarith

namespace Frame02
variable {x : Fin 7 → ℝ³}

theorem exists_kl (S : Shape02) : ∃ k l : ℝ, 0 < k ∧ 0 < l ∧ S.hp = k * (1 - S.tp) ∧
    S.kp = k * (1 - S.sp) ∧ S.hm = l * (1 - S.tm) ∧ S.km = l * (1 - S.sm) := by
  have a1 := sub_pos.2 S.tp_lt
  have a2 := sub_pos.2 S.sp_lt
  have a3 := sub_pos.2 S.tm_lt
  have a4 := sub_pos.2 S.sm_lt
  refine ⟨S.hp / (1 - S.tp), S.hm / (1 - S.tm), div_pos S.hp_pos a1, div_pos S.hm_pos a3,
    by field_simp, ?_, by field_simp, ?_⟩
  · rw [S.plane_up]; field_simp
  · rw [S.plane_dn]; field_simp

theorem D_pos (F : Frame02 x) (hr : gA12 x = gA11 x) : 0 < gA22 x - gA12 x := by
  have hne : x 3 - x 2 - (x 4 - x 2) ≠ 0 := by
    intro h
    have h2 : x 3 - x 2 = x 4 - x 2 := sub_eq_zero.1 h
    have := F.indep.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
    exact this (by simpa using h2)
  have hp := real_inner_self_pos.2 hne
  have : ⟪x 3 - x 2 - (x 4 - x 2), x 3 - x 2 - (x 4 - x 2)⟫ = gA11 x - 2 * gA12 x + gA22 x := by
    simp only [gA11, gA12, gA22, inner_sub_left, inner_sub_right, real_inner_comm (x 3 - x 2)]
    ring
  linarith

theorem GG_u (F : Frame02 x) (hr : gA12 x = gA11 x) (p : C3) :
    F.toFrame7.GG p ⟨-1, 1, 0⟩ = p.y * (gA22 x - gA12 x) := by
  have : F.toFrame7.GG p ⟨-1, 1, 0⟩ = Gf (gA11 x) (gA12 x) (gA22 x) F.toFrame7.gg p ⟨-1, 1, 0⟩ := rfl
  rw [this]; simp only [Gf]; rw [← hr]; ring


/-- the seven points with the planarity relations solved (`κ = k`, `λ = l`). -/
def Pt (tp sp tm sm k l : ℝ) : Fin 7 → C3 :=
  ![⟨tp, 0, k * (1 - tp)⟩, ⟨0, sp, k * (1 - sp)⟩, ⟨0, 0, 0⟩, ⟨1, 0, 0⟩, ⟨0, 1, 0⟩,
    ⟨tm, 0, -(l * (1 - tm))⟩, ⟨0, sm, -(l * (1 - sm))⟩]

section Pt
variable (tp sp tm sm k l : ℝ)
theorem Pt_0 : Pt tp sp tm sm k l 0 = ⟨tp, 0, k * (1 - tp)⟩ := rfl
theorem Pt_1 : Pt tp sp tm sm k l 1 = ⟨0, sp, k * (1 - sp)⟩ := rfl
theorem Pt_2 : Pt tp sp tm sm k l 2 = ⟨0, 0, 0⟩ := rfl
theorem Pt_3 : Pt tp sp tm sm k l 3 = ⟨1, 0, 0⟩ := rfl
theorem Pt_4 : Pt tp sp tm sm k l 4 = ⟨0, 1, 0⟩ := rfl
theorem Pt_5 : Pt tp sp tm sm k l 5 = ⟨tm, 0, -(l * (1 - tm))⟩ := rfl
theorem Pt_6 : Pt tp sp tm sm k l 6 = ⟨0, sm, -(l * (1 - sm))⟩ := rfl
end Pt

/-- the 4-cycle / 5-cycle of points `P a, P b, ...` -/
def Qd (P : Fin 7 → C3) (a b c d : Fin 7) : ZMod 4 → C3 := quad (P a) (P b) (P c) (P d)
def Qn (P : Fin 7 → C3) (a b c d e : Fin 7) : ZMod 5 → C3 := quint (P a) (P b) (P c) (P d) (P e)

theorem ptC_eq (F : Frame02 x) {k l : ℝ} (h1 : F.S.hp = k * (1 - F.S.tp))
    (h2 : F.S.kp = k * (1 - F.S.sp)) (h3 : F.S.hm = l * (1 - F.S.tm))
    (h4 : F.S.km = l * (1 - F.S.sm)) :
    F.toFrame7.ptC = Pt F.S.tp F.S.sp F.S.tm F.S.sm k l := by
  funext j
  fin_cases j <;> simp [toFrame7, pt, Pt, h1, h2, h3, h4]

-- sign test row: strict at `u`, or a tie broken by the tilt
set_option hygiene false in
macro "rowtac4" : tactic => `(tactic| (
  simp only [CaseC09.ST, Dc, C3.sub, Qd, Qn, Pt_0, Pt_1, Pt_2, Pt_3, Pt_4, Pt_5, Pt_6, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
  first
  | (left; linarith [mul_pos ha1 ha2, mul_pos ha1 ha3, mul_pos ha1 ha4, mul_pos ha1 a1, mul_pos ha1 a2, mul_pos ha1 a3, mul_pos ha1 a4, mul_pos ha2 ha3, mul_pos ha2 ha4, mul_pos ha2 a1, mul_pos ha2 a2, mul_pos ha2 a3, mul_pos ha2 a4, mul_pos ha3 ha4, mul_pos ha3 a1, mul_pos ha3 a2, mul_pos ha3 a3, mul_pos ha3 a4, mul_pos ha4 a1, mul_pos ha4 a2, mul_pos ha4 a3, mul_pos ha4 a4, mul_pos a1 a2, mul_pos a1 a3, mul_pos a1 a4, mul_pos a2 a3, mul_pos a2 a4, mul_pos a3 a4, mul_pos hk ha1, mul_pos hk ha2, mul_pos hk ha3, mul_pos hk ha4, mul_pos hk a1, mul_pos hk a2, mul_pos hk a3, mul_pos hk a4, mul_pos (mul_pos hk ha1) ha2, mul_pos (mul_pos hk ha1) ha3, mul_pos (mul_pos hk ha1) ha4, mul_pos (mul_pos hk ha1) a1, mul_pos (mul_pos hk ha1) a2, mul_pos (mul_pos hk ha1) a3, mul_pos (mul_pos hk ha1) a4, mul_pos (mul_pos hk ha2) ha3, mul_pos (mul_pos hk ha2) ha4, mul_pos (mul_pos hk ha2) a1, mul_pos (mul_pos hk ha2) a2, mul_pos (mul_pos hk ha2) a3, mul_pos (mul_pos hk ha2) a4, mul_pos (mul_pos hk ha3) ha4, mul_pos (mul_pos hk ha3) a1, mul_pos (mul_pos hk ha3) a2, mul_pos (mul_pos hk ha3) a3, mul_pos (mul_pos hk ha3) a4, mul_pos (mul_pos hk ha4) a1, mul_pos (mul_pos hk ha4) a2, mul_pos (mul_pos hk ha4) a3, mul_pos (mul_pos hk ha4) a4, mul_pos (mul_pos hk a1) a2, mul_pos (mul_pos hk a1) a3, mul_pos (mul_pos hk a1) a4, mul_pos (mul_pos hk a2) a3, mul_pos (mul_pos hk a2) a4, mul_pos (mul_pos hk a3) a4, mul_pos hl ha1, mul_pos hl ha2, mul_pos hl ha3, mul_pos hl ha4, mul_pos hl a1, mul_pos hl a2, mul_pos hl a3, mul_pos hl a4, mul_pos (mul_pos hl ha1) ha2, mul_pos (mul_pos hl ha1) ha3, mul_pos (mul_pos hl ha1) ha4, mul_pos (mul_pos hl ha1) a1, mul_pos (mul_pos hl ha1) a2, mul_pos (mul_pos hl ha1) a3, mul_pos (mul_pos hl ha1) a4, mul_pos (mul_pos hl ha2) ha3, mul_pos (mul_pos hl ha2) ha4, mul_pos (mul_pos hl ha2) a1, mul_pos (mul_pos hl ha2) a2, mul_pos (mul_pos hl ha2) a3, mul_pos (mul_pos hl ha2) a4, mul_pos (mul_pos hl ha3) ha4, mul_pos (mul_pos hl ha3) a1, mul_pos (mul_pos hl ha3) a2, mul_pos (mul_pos hl ha3) a3, mul_pos (mul_pos hl ha3) a4, mul_pos (mul_pos hl ha4) a1, mul_pos (mul_pos hl ha4) a2, mul_pos (mul_pos hl ha4) a3, mul_pos (mul_pos hl ha4) a4, mul_pos (mul_pos hl a1) a2, mul_pos (mul_pos hl a1) a3, mul_pos (mul_pos hl a1) a4, mul_pos (mul_pos hl a2) a3, mul_pos (mul_pos hl a2) a4, mul_pos (mul_pos hl a3) a4, mul_pos hk hl, mul_pos hAB ha1, mul_pos hAB ha2, mul_pos hAB ha3, mul_pos hAB ha4, mul_pos hAB a1, mul_pos hAB a2, mul_pos hAB a3, mul_pos hAB a4, mul_pos hk hAB, mul_pos (mul_pos hk hAB) ha1, mul_pos (mul_pos hk hAB) ha2, mul_pos (mul_pos hk hAB) ha3, mul_pos (mul_pos hk hAB) ha4, mul_pos (mul_pos hk hAB) a1, mul_pos (mul_pos hk hAB) a2, mul_pos (mul_pos hk hAB) a3, mul_pos (mul_pos hk hAB) a4, mul_pos hl hAB, mul_pos (mul_pos hl hAB) ha1, mul_pos (mul_pos hl hAB) ha2, mul_pos (mul_pos hl hAB) ha3, mul_pos (mul_pos hl hAB) ha4, mul_pos (mul_pos hl hAB) a1, mul_pos (mul_pos hl hAB) a2, mul_pos (mul_pos hl hAB) a3, mul_pos (mul_pos hl hAB) a4, mul_pos (mul_pos hAB ha1) ha2, mul_pos (mul_pos hAB ha1) ha3, mul_pos (mul_pos hAB ha1) ha4, mul_pos (mul_pos hAB ha1) a1, mul_pos (mul_pos hAB ha1) a2, mul_pos (mul_pos hAB ha1) a3, mul_pos (mul_pos hAB ha1) a4, mul_pos (mul_pos hAB ha2) ha3, mul_pos (mul_pos hAB ha2) ha4, mul_pos (mul_pos hAB ha2) a1, mul_pos (mul_pos hAB ha2) a2, mul_pos (mul_pos hAB ha2) a3, mul_pos (mul_pos hAB ha2) a4, mul_pos (mul_pos hAB ha3) ha4, mul_pos (mul_pos hAB ha3) a1, mul_pos (mul_pos hAB ha3) a2, mul_pos (mul_pos hAB ha3) a3, mul_pos (mul_pos hAB ha3) a4, mul_pos (mul_pos hAB ha4) a1, mul_pos (mul_pos hAB ha4) a2, mul_pos (mul_pos hAB ha4) a3, mul_pos (mul_pos hAB ha4) a4, mul_pos (mul_pos hAB a1) a2, mul_pos (mul_pos hAB a1) a3, mul_pos (mul_pos hAB a1) a4, mul_pos (mul_pos hAB a2) a3, mul_pos (mul_pos hAB a2) a4, mul_pos (mul_pos hAB a3) a4, mul_pos hBB ha1, mul_pos hBB ha2, mul_pos hBB ha3, mul_pos hBB ha4, mul_pos hBB a1, mul_pos hBB a2, mul_pos hBB a3, mul_pos hBB a4, mul_pos hk hBB, mul_pos (mul_pos hk hBB) ha1, mul_pos (mul_pos hk hBB) ha2, mul_pos (mul_pos hk hBB) ha3, mul_pos (mul_pos hk hBB) ha4, mul_pos (mul_pos hk hBB) a1, mul_pos (mul_pos hk hBB) a2, mul_pos (mul_pos hk hBB) a3, mul_pos (mul_pos hk hBB) a4, mul_pos hl hBB, mul_pos (mul_pos hl hBB) ha1, mul_pos (mul_pos hl hBB) ha2, mul_pos (mul_pos hl hBB) ha3, mul_pos (mul_pos hl hBB) ha4, mul_pos (mul_pos hl hBB) a1, mul_pos (mul_pos hl hBB) a2, mul_pos (mul_pos hl hBB) a3, mul_pos (mul_pos hl hBB) a4, mul_pos (mul_pos hBB ha1) ha2, mul_pos (mul_pos hBB ha1) ha3, mul_pos (mul_pos hBB ha1) ha4, mul_pos (mul_pos hBB ha1) a1, mul_pos (mul_pos hBB ha1) a2, mul_pos (mul_pos hBB ha1) a3, mul_pos (mul_pos hBB ha1) a4, mul_pos (mul_pos hBB ha2) ha3, mul_pos (mul_pos hBB ha2) ha4, mul_pos (mul_pos hBB ha2) a1, mul_pos (mul_pos hBB ha2) a2, mul_pos (mul_pos hBB ha2) a3, mul_pos (mul_pos hBB ha2) a4, mul_pos (mul_pos hBB ha3) ha4, mul_pos (mul_pos hBB ha3) a1, mul_pos (mul_pos hBB ha3) a2, mul_pos (mul_pos hBB ha3) a3, mul_pos (mul_pos hBB ha3) a4, mul_pos (mul_pos hBB ha4) a1, mul_pos (mul_pos hBB ha4) a2, mul_pos (mul_pos hBB ha4) a3, mul_pos (mul_pos hBB ha4) a4, mul_pos (mul_pos hBB a1) a2, mul_pos (mul_pos hBB a1) a3, mul_pos (mul_pos hBB a1) a4, mul_pos (mul_pos hBB a2) a3, mul_pos (mul_pos hBB a2) a4, mul_pos (mul_pos hBB a3) a4])
  | (right; constructor <;> linarith [mul_pos ha1 ha2, mul_pos ha1 ha3, mul_pos ha1 ha4, mul_pos ha1 a1, mul_pos ha1 a2, mul_pos ha1 a3, mul_pos ha1 a4, mul_pos ha2 ha3, mul_pos ha2 ha4, mul_pos ha2 a1, mul_pos ha2 a2, mul_pos ha2 a3, mul_pos ha2 a4, mul_pos ha3 ha4, mul_pos ha3 a1, mul_pos ha3 a2, mul_pos ha3 a3, mul_pos ha3 a4, mul_pos ha4 a1, mul_pos ha4 a2, mul_pos ha4 a3, mul_pos ha4 a4, mul_pos a1 a2, mul_pos a1 a3, mul_pos a1 a4, mul_pos a2 a3, mul_pos a2 a4, mul_pos a3 a4, mul_pos hk ha1, mul_pos hk ha2, mul_pos hk ha3, mul_pos hk ha4, mul_pos hk a1, mul_pos hk a2, mul_pos hk a3, mul_pos hk a4, mul_pos (mul_pos hk ha1) ha2, mul_pos (mul_pos hk ha1) ha3, mul_pos (mul_pos hk ha1) ha4, mul_pos (mul_pos hk ha1) a1, mul_pos (mul_pos hk ha1) a2, mul_pos (mul_pos hk ha1) a3, mul_pos (mul_pos hk ha1) a4, mul_pos (mul_pos hk ha2) ha3, mul_pos (mul_pos hk ha2) ha4, mul_pos (mul_pos hk ha2) a1, mul_pos (mul_pos hk ha2) a2, mul_pos (mul_pos hk ha2) a3, mul_pos (mul_pos hk ha2) a4, mul_pos (mul_pos hk ha3) ha4, mul_pos (mul_pos hk ha3) a1, mul_pos (mul_pos hk ha3) a2, mul_pos (mul_pos hk ha3) a3, mul_pos (mul_pos hk ha3) a4, mul_pos (mul_pos hk ha4) a1, mul_pos (mul_pos hk ha4) a2, mul_pos (mul_pos hk ha4) a3, mul_pos (mul_pos hk ha4) a4, mul_pos (mul_pos hk a1) a2, mul_pos (mul_pos hk a1) a3, mul_pos (mul_pos hk a1) a4, mul_pos (mul_pos hk a2) a3, mul_pos (mul_pos hk a2) a4, mul_pos (mul_pos hk a3) a4, mul_pos hl ha1, mul_pos hl ha2, mul_pos hl ha3, mul_pos hl ha4, mul_pos hl a1, mul_pos hl a2, mul_pos hl a3, mul_pos hl a4, mul_pos (mul_pos hl ha1) ha2, mul_pos (mul_pos hl ha1) ha3, mul_pos (mul_pos hl ha1) ha4, mul_pos (mul_pos hl ha1) a1, mul_pos (mul_pos hl ha1) a2, mul_pos (mul_pos hl ha1) a3, mul_pos (mul_pos hl ha1) a4, mul_pos (mul_pos hl ha2) ha3, mul_pos (mul_pos hl ha2) ha4, mul_pos (mul_pos hl ha2) a1, mul_pos (mul_pos hl ha2) a2, mul_pos (mul_pos hl ha2) a3, mul_pos (mul_pos hl ha2) a4, mul_pos (mul_pos hl ha3) ha4, mul_pos (mul_pos hl ha3) a1, mul_pos (mul_pos hl ha3) a2, mul_pos (mul_pos hl ha3) a3, mul_pos (mul_pos hl ha3) a4, mul_pos (mul_pos hl ha4) a1, mul_pos (mul_pos hl ha4) a2, mul_pos (mul_pos hl ha4) a3, mul_pos (mul_pos hl ha4) a4, mul_pos (mul_pos hl a1) a2, mul_pos (mul_pos hl a1) a3, mul_pos (mul_pos hl a1) a4, mul_pos (mul_pos hl a2) a3, mul_pos (mul_pos hl a2) a4, mul_pos (mul_pos hl a3) a4, mul_pos hk hl, mul_pos hAB ha1, mul_pos hAB ha2, mul_pos hAB ha3, mul_pos hAB ha4, mul_pos hAB a1, mul_pos hAB a2, mul_pos hAB a3, mul_pos hAB a4, mul_pos hk hAB, mul_pos (mul_pos hk hAB) ha1, mul_pos (mul_pos hk hAB) ha2, mul_pos (mul_pos hk hAB) ha3, mul_pos (mul_pos hk hAB) ha4, mul_pos (mul_pos hk hAB) a1, mul_pos (mul_pos hk hAB) a2, mul_pos (mul_pos hk hAB) a3, mul_pos (mul_pos hk hAB) a4, mul_pos hl hAB, mul_pos (mul_pos hl hAB) ha1, mul_pos (mul_pos hl hAB) ha2, mul_pos (mul_pos hl hAB) ha3, mul_pos (mul_pos hl hAB) ha4, mul_pos (mul_pos hl hAB) a1, mul_pos (mul_pos hl hAB) a2, mul_pos (mul_pos hl hAB) a3, mul_pos (mul_pos hl hAB) a4, mul_pos (mul_pos hAB ha1) ha2, mul_pos (mul_pos hAB ha1) ha3, mul_pos (mul_pos hAB ha1) ha4, mul_pos (mul_pos hAB ha1) a1, mul_pos (mul_pos hAB ha1) a2, mul_pos (mul_pos hAB ha1) a3, mul_pos (mul_pos hAB ha1) a4, mul_pos (mul_pos hAB ha2) ha3, mul_pos (mul_pos hAB ha2) ha4, mul_pos (mul_pos hAB ha2) a1, mul_pos (mul_pos hAB ha2) a2, mul_pos (mul_pos hAB ha2) a3, mul_pos (mul_pos hAB ha2) a4, mul_pos (mul_pos hAB ha3) ha4, mul_pos (mul_pos hAB ha3) a1, mul_pos (mul_pos hAB ha3) a2, mul_pos (mul_pos hAB ha3) a3, mul_pos (mul_pos hAB ha3) a4, mul_pos (mul_pos hAB ha4) a1, mul_pos (mul_pos hAB ha4) a2, mul_pos (mul_pos hAB ha4) a3, mul_pos (mul_pos hAB ha4) a4, mul_pos (mul_pos hAB a1) a2, mul_pos (mul_pos hAB a1) a3, mul_pos (mul_pos hAB a1) a4, mul_pos (mul_pos hAB a2) a3, mul_pos (mul_pos hAB a2) a4, mul_pos (mul_pos hAB a3) a4, mul_pos hBB ha1, mul_pos hBB ha2, mul_pos hBB ha3, mul_pos hBB ha4, mul_pos hBB a1, mul_pos hBB a2, mul_pos hBB a3, mul_pos hBB a4, mul_pos hk hBB, mul_pos (mul_pos hk hBB) ha1, mul_pos (mul_pos hk hBB) ha2, mul_pos (mul_pos hk hBB) ha3, mul_pos (mul_pos hk hBB) ha4, mul_pos (mul_pos hk hBB) a1, mul_pos (mul_pos hk hBB) a2, mul_pos (mul_pos hk hBB) a3, mul_pos (mul_pos hk hBB) a4, mul_pos hl hBB, mul_pos (mul_pos hl hBB) ha1, mul_pos (mul_pos hl hBB) ha2, mul_pos (mul_pos hl hBB) ha3, mul_pos (mul_pos hl hBB) ha4, mul_pos (mul_pos hl hBB) a1, mul_pos (mul_pos hl hBB) a2, mul_pos (mul_pos hl hBB) a3, mul_pos (mul_pos hl hBB) a4, mul_pos (mul_pos hBB ha1) ha2, mul_pos (mul_pos hBB ha1) ha3, mul_pos (mul_pos hBB ha1) ha4, mul_pos (mul_pos hBB ha1) a1, mul_pos (mul_pos hBB ha1) a2, mul_pos (mul_pos hBB ha1) a3, mul_pos (mul_pos hBB ha1) a4, mul_pos (mul_pos hBB ha2) ha3, mul_pos (mul_pos hBB ha2) ha4, mul_pos (mul_pos hBB ha2) a1, mul_pos (mul_pos hBB ha2) a2, mul_pos (mul_pos hBB ha2) a3, mul_pos (mul_pos hBB ha2) a4, mul_pos (mul_pos hBB ha3) ha4, mul_pos (mul_pos hBB ha3) a1, mul_pos (mul_pos hBB ha3) a2, mul_pos (mul_pos hBB ha3) a3, mul_pos (mul_pos hBB ha3) a4, mul_pos (mul_pos hBB ha4) a1, mul_pos (mul_pos hBB ha4) a2, mul_pos (mul_pos hBB ha4) a3, mul_pos (mul_pos hBB ha4) a4, mul_pos (mul_pos hBB a1) a2, mul_pos (mul_pos hBB a1) a3, mul_pos (mul_pos hBB a1) a4, mul_pos (mul_pos hBB a2) a3, mul_pos (mul_pos hBB a2) a4, mul_pos (mul_pos hBB a3) a4])))

-- sign test row: strict at `u`, or a tie broken by the tilt
set_option hygiene false in
macro "rowtac5" : tactic => `(tactic| (
  simp only [CaseC09.ST, Dc, C3.sub, Qd, Qn, Pt_0, Pt_1, Pt_2, Pt_3, Pt_4, Pt_5, Pt_6, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
  first
  | (left; linarith [mul_pos ha1 ha2, mul_pos ha1 ha3, mul_pos ha1 ha4, mul_pos ha1 a1, mul_pos ha1 a2, mul_pos ha1 a3, mul_pos ha1 a4, mul_pos ha2 ha3, mul_pos ha2 ha4, mul_pos ha2 a1, mul_pos ha2 a2, mul_pos ha2 a3, mul_pos ha2 a4, mul_pos ha3 ha4, mul_pos ha3 a1, mul_pos ha3 a2, mul_pos ha3 a3, mul_pos ha3 a4, mul_pos ha4 a1, mul_pos ha4 a2, mul_pos ha4 a3, mul_pos ha4 a4, mul_pos a1 a2, mul_pos a1 a3, mul_pos a1 a4, mul_pos a2 a3, mul_pos a2 a4, mul_pos a3 a4, mul_pos hk ha1, mul_pos hk ha2, mul_pos hk ha3, mul_pos hk ha4, mul_pos hk a1, mul_pos hk a2, mul_pos hk a3, mul_pos hk a4, mul_pos (mul_pos hk ha1) ha2, mul_pos (mul_pos hk ha1) ha3, mul_pos (mul_pos hk ha1) ha4, mul_pos (mul_pos hk ha1) a1, mul_pos (mul_pos hk ha1) a2, mul_pos (mul_pos hk ha1) a3, mul_pos (mul_pos hk ha1) a4, mul_pos (mul_pos hk ha2) ha3, mul_pos (mul_pos hk ha2) ha4, mul_pos (mul_pos hk ha2) a1, mul_pos (mul_pos hk ha2) a2, mul_pos (mul_pos hk ha2) a3, mul_pos (mul_pos hk ha2) a4, mul_pos (mul_pos hk ha3) ha4, mul_pos (mul_pos hk ha3) a1, mul_pos (mul_pos hk ha3) a2, mul_pos (mul_pos hk ha3) a3, mul_pos (mul_pos hk ha3) a4, mul_pos (mul_pos hk ha4) a1, mul_pos (mul_pos hk ha4) a2, mul_pos (mul_pos hk ha4) a3, mul_pos (mul_pos hk ha4) a4, mul_pos (mul_pos hk a1) a2, mul_pos (mul_pos hk a1) a3, mul_pos (mul_pos hk a1) a4, mul_pos (mul_pos hk a2) a3, mul_pos (mul_pos hk a2) a4, mul_pos (mul_pos hk a3) a4, mul_pos hl ha1, mul_pos hl ha2, mul_pos hl ha3, mul_pos hl ha4, mul_pos hl a1, mul_pos hl a2, mul_pos hl a3, mul_pos hl a4, mul_pos (mul_pos hl ha1) ha2, mul_pos (mul_pos hl ha1) ha3, mul_pos (mul_pos hl ha1) ha4, mul_pos (mul_pos hl ha1) a1, mul_pos (mul_pos hl ha1) a2, mul_pos (mul_pos hl ha1) a3, mul_pos (mul_pos hl ha1) a4, mul_pos (mul_pos hl ha2) ha3, mul_pos (mul_pos hl ha2) ha4, mul_pos (mul_pos hl ha2) a1, mul_pos (mul_pos hl ha2) a2, mul_pos (mul_pos hl ha2) a3, mul_pos (mul_pos hl ha2) a4, mul_pos (mul_pos hl ha3) ha4, mul_pos (mul_pos hl ha3) a1, mul_pos (mul_pos hl ha3) a2, mul_pos (mul_pos hl ha3) a3, mul_pos (mul_pos hl ha3) a4, mul_pos (mul_pos hl ha4) a1, mul_pos (mul_pos hl ha4) a2, mul_pos (mul_pos hl ha4) a3, mul_pos (mul_pos hl ha4) a4, mul_pos (mul_pos hl a1) a2, mul_pos (mul_pos hl a1) a3, mul_pos (mul_pos hl a1) a4, mul_pos (mul_pos hl a2) a3, mul_pos (mul_pos hl a2) a4, mul_pos (mul_pos hl a3) a4, mul_pos hk hl, mul_pos hAB ha1, mul_pos hAB ha2, mul_pos hAB ha3, mul_pos hAB ha4, mul_pos hAB a1, mul_pos hAB a2, mul_pos hAB a3, mul_pos hAB a4, mul_pos hk hAB, mul_pos (mul_pos hk hAB) ha1, mul_pos (mul_pos hk hAB) ha2, mul_pos (mul_pos hk hAB) ha3, mul_pos (mul_pos hk hAB) ha4, mul_pos (mul_pos hk hAB) a1, mul_pos (mul_pos hk hAB) a2, mul_pos (mul_pos hk hAB) a3, mul_pos (mul_pos hk hAB) a4, mul_pos hl hAB, mul_pos (mul_pos hl hAB) ha1, mul_pos (mul_pos hl hAB) ha2, mul_pos (mul_pos hl hAB) ha3, mul_pos (mul_pos hl hAB) ha4, mul_pos (mul_pos hl hAB) a1, mul_pos (mul_pos hl hAB) a2, mul_pos (mul_pos hl hAB) a3, mul_pos (mul_pos hl hAB) a4, mul_pos (mul_pos hAB ha1) ha2, mul_pos (mul_pos hAB ha1) ha3, mul_pos (mul_pos hAB ha1) ha4, mul_pos (mul_pos hAB ha1) a1, mul_pos (mul_pos hAB ha1) a2, mul_pos (mul_pos hAB ha1) a3, mul_pos (mul_pos hAB ha1) a4, mul_pos (mul_pos hAB ha2) ha3, mul_pos (mul_pos hAB ha2) ha4, mul_pos (mul_pos hAB ha2) a1, mul_pos (mul_pos hAB ha2) a2, mul_pos (mul_pos hAB ha2) a3, mul_pos (mul_pos hAB ha2) a4, mul_pos (mul_pos hAB ha3) ha4, mul_pos (mul_pos hAB ha3) a1, mul_pos (mul_pos hAB ha3) a2, mul_pos (mul_pos hAB ha3) a3, mul_pos (mul_pos hAB ha3) a4, mul_pos (mul_pos hAB ha4) a1, mul_pos (mul_pos hAB ha4) a2, mul_pos (mul_pos hAB ha4) a3, mul_pos (mul_pos hAB ha4) a4, mul_pos (mul_pos hAB a1) a2, mul_pos (mul_pos hAB a1) a3, mul_pos (mul_pos hAB a1) a4, mul_pos (mul_pos hAB a2) a3, mul_pos (mul_pos hAB a2) a4, mul_pos (mul_pos hAB a3) a4, mul_pos hBB ha1, mul_pos hBB ha2, mul_pos hBB ha3, mul_pos hBB ha4, mul_pos hBB a1, mul_pos hBB a2, mul_pos hBB a3, mul_pos hBB a4, mul_pos hk hBB, mul_pos (mul_pos hk hBB) ha1, mul_pos (mul_pos hk hBB) ha2, mul_pos (mul_pos hk hBB) ha3, mul_pos (mul_pos hk hBB) ha4, mul_pos (mul_pos hk hBB) a1, mul_pos (mul_pos hk hBB) a2, mul_pos (mul_pos hk hBB) a3, mul_pos (mul_pos hk hBB) a4, mul_pos hl hBB, mul_pos (mul_pos hl hBB) ha1, mul_pos (mul_pos hl hBB) ha2, mul_pos (mul_pos hl hBB) ha3, mul_pos (mul_pos hl hBB) ha4, mul_pos (mul_pos hl hBB) a1, mul_pos (mul_pos hl hBB) a2, mul_pos (mul_pos hl hBB) a3, mul_pos (mul_pos hl hBB) a4, mul_pos (mul_pos hBB ha1) ha2, mul_pos (mul_pos hBB ha1) ha3, mul_pos (mul_pos hBB ha1) ha4, mul_pos (mul_pos hBB ha1) a1, mul_pos (mul_pos hBB ha1) a2, mul_pos (mul_pos hBB ha1) a3, mul_pos (mul_pos hBB ha1) a4, mul_pos (mul_pos hBB ha2) ha3, mul_pos (mul_pos hBB ha2) ha4, mul_pos (mul_pos hBB ha2) a1, mul_pos (mul_pos hBB ha2) a2, mul_pos (mul_pos hBB ha2) a3, mul_pos (mul_pos hBB ha2) a4, mul_pos (mul_pos hBB ha3) ha4, mul_pos (mul_pos hBB ha3) a1, mul_pos (mul_pos hBB ha3) a2, mul_pos (mul_pos hBB ha3) a3, mul_pos (mul_pos hBB ha3) a4, mul_pos (mul_pos hBB ha4) a1, mul_pos (mul_pos hBB ha4) a2, mul_pos (mul_pos hBB ha4) a3, mul_pos (mul_pos hBB ha4) a4, mul_pos (mul_pos hBB a1) a2, mul_pos (mul_pos hBB a1) a3, mul_pos (mul_pos hBB a1) a4, mul_pos (mul_pos hBB a2) a3, mul_pos (mul_pos hBB a2) a4, mul_pos (mul_pos hBB a3) a4])
  | (right; constructor <;> linarith [mul_pos ha1 ha2, mul_pos ha1 ha3, mul_pos ha1 ha4, mul_pos ha1 a1, mul_pos ha1 a2, mul_pos ha1 a3, mul_pos ha1 a4, mul_pos ha2 ha3, mul_pos ha2 ha4, mul_pos ha2 a1, mul_pos ha2 a2, mul_pos ha2 a3, mul_pos ha2 a4, mul_pos ha3 ha4, mul_pos ha3 a1, mul_pos ha3 a2, mul_pos ha3 a3, mul_pos ha3 a4, mul_pos ha4 a1, mul_pos ha4 a2, mul_pos ha4 a3, mul_pos ha4 a4, mul_pos a1 a2, mul_pos a1 a3, mul_pos a1 a4, mul_pos a2 a3, mul_pos a2 a4, mul_pos a3 a4, mul_pos hk ha1, mul_pos hk ha2, mul_pos hk ha3, mul_pos hk ha4, mul_pos hk a1, mul_pos hk a2, mul_pos hk a3, mul_pos hk a4, mul_pos (mul_pos hk ha1) ha2, mul_pos (mul_pos hk ha1) ha3, mul_pos (mul_pos hk ha1) ha4, mul_pos (mul_pos hk ha1) a1, mul_pos (mul_pos hk ha1) a2, mul_pos (mul_pos hk ha1) a3, mul_pos (mul_pos hk ha1) a4, mul_pos (mul_pos hk ha2) ha3, mul_pos (mul_pos hk ha2) ha4, mul_pos (mul_pos hk ha2) a1, mul_pos (mul_pos hk ha2) a2, mul_pos (mul_pos hk ha2) a3, mul_pos (mul_pos hk ha2) a4, mul_pos (mul_pos hk ha3) ha4, mul_pos (mul_pos hk ha3) a1, mul_pos (mul_pos hk ha3) a2, mul_pos (mul_pos hk ha3) a3, mul_pos (mul_pos hk ha3) a4, mul_pos (mul_pos hk ha4) a1, mul_pos (mul_pos hk ha4) a2, mul_pos (mul_pos hk ha4) a3, mul_pos (mul_pos hk ha4) a4, mul_pos (mul_pos hk a1) a2, mul_pos (mul_pos hk a1) a3, mul_pos (mul_pos hk a1) a4, mul_pos (mul_pos hk a2) a3, mul_pos (mul_pos hk a2) a4, mul_pos (mul_pos hk a3) a4, mul_pos hl ha1, mul_pos hl ha2, mul_pos hl ha3, mul_pos hl ha4, mul_pos hl a1, mul_pos hl a2, mul_pos hl a3, mul_pos hl a4, mul_pos (mul_pos hl ha1) ha2, mul_pos (mul_pos hl ha1) ha3, mul_pos (mul_pos hl ha1) ha4, mul_pos (mul_pos hl ha1) a1, mul_pos (mul_pos hl ha1) a2, mul_pos (mul_pos hl ha1) a3, mul_pos (mul_pos hl ha1) a4, mul_pos (mul_pos hl ha2) ha3, mul_pos (mul_pos hl ha2) ha4, mul_pos (mul_pos hl ha2) a1, mul_pos (mul_pos hl ha2) a2, mul_pos (mul_pos hl ha2) a3, mul_pos (mul_pos hl ha2) a4, mul_pos (mul_pos hl ha3) ha4, mul_pos (mul_pos hl ha3) a1, mul_pos (mul_pos hl ha3) a2, mul_pos (mul_pos hl ha3) a3, mul_pos (mul_pos hl ha3) a4, mul_pos (mul_pos hl ha4) a1, mul_pos (mul_pos hl ha4) a2, mul_pos (mul_pos hl ha4) a3, mul_pos (mul_pos hl ha4) a4, mul_pos (mul_pos hl a1) a2, mul_pos (mul_pos hl a1) a3, mul_pos (mul_pos hl a1) a4, mul_pos (mul_pos hl a2) a3, mul_pos (mul_pos hl a2) a4, mul_pos (mul_pos hl a3) a4, mul_pos hk hl, mul_pos hAB ha1, mul_pos hAB ha2, mul_pos hAB ha3, mul_pos hAB ha4, mul_pos hAB a1, mul_pos hAB a2, mul_pos hAB a3, mul_pos hAB a4, mul_pos hk hAB, mul_pos (mul_pos hk hAB) ha1, mul_pos (mul_pos hk hAB) ha2, mul_pos (mul_pos hk hAB) ha3, mul_pos (mul_pos hk hAB) ha4, mul_pos (mul_pos hk hAB) a1, mul_pos (mul_pos hk hAB) a2, mul_pos (mul_pos hk hAB) a3, mul_pos (mul_pos hk hAB) a4, mul_pos hl hAB, mul_pos (mul_pos hl hAB) ha1, mul_pos (mul_pos hl hAB) ha2, mul_pos (mul_pos hl hAB) ha3, mul_pos (mul_pos hl hAB) ha4, mul_pos (mul_pos hl hAB) a1, mul_pos (mul_pos hl hAB) a2, mul_pos (mul_pos hl hAB) a3, mul_pos (mul_pos hl hAB) a4, mul_pos (mul_pos hAB ha1) ha2, mul_pos (mul_pos hAB ha1) ha3, mul_pos (mul_pos hAB ha1) ha4, mul_pos (mul_pos hAB ha1) a1, mul_pos (mul_pos hAB ha1) a2, mul_pos (mul_pos hAB ha1) a3, mul_pos (mul_pos hAB ha1) a4, mul_pos (mul_pos hAB ha2) ha3, mul_pos (mul_pos hAB ha2) ha4, mul_pos (mul_pos hAB ha2) a1, mul_pos (mul_pos hAB ha2) a2, mul_pos (mul_pos hAB ha2) a3, mul_pos (mul_pos hAB ha2) a4, mul_pos (mul_pos hAB ha3) ha4, mul_pos (mul_pos hAB ha3) a1, mul_pos (mul_pos hAB ha3) a2, mul_pos (mul_pos hAB ha3) a3, mul_pos (mul_pos hAB ha3) a4, mul_pos (mul_pos hAB ha4) a1, mul_pos (mul_pos hAB ha4) a2, mul_pos (mul_pos hAB ha4) a3, mul_pos (mul_pos hAB ha4) a4, mul_pos (mul_pos hAB a1) a2, mul_pos (mul_pos hAB a1) a3, mul_pos (mul_pos hAB a1) a4, mul_pos (mul_pos hAB a2) a3, mul_pos (mul_pos hAB a2) a4, mul_pos (mul_pos hAB a3) a4, mul_pos hBB ha1, mul_pos hBB ha2, mul_pos hBB ha3, mul_pos hBB ha4, mul_pos hBB a1, mul_pos hBB a2, mul_pos hBB a3, mul_pos hBB a4, mul_pos hk hBB, mul_pos (mul_pos hk hBB) ha1, mul_pos (mul_pos hk hBB) ha2, mul_pos (mul_pos hk hBB) ha3, mul_pos (mul_pos hk hBB) ha4, mul_pos (mul_pos hk hBB) a1, mul_pos (mul_pos hk hBB) a2, mul_pos (mul_pos hk hBB) a3, mul_pos (mul_pos hk hBB) a4, mul_pos hl hBB, mul_pos (mul_pos hl hBB) ha1, mul_pos (mul_pos hl hBB) ha2, mul_pos (mul_pos hl hBB) ha3, mul_pos (mul_pos hl hBB) ha4, mul_pos (mul_pos hl hBB) a1, mul_pos (mul_pos hl hBB) a2, mul_pos (mul_pos hl hBB) a3, mul_pos (mul_pos hl hBB) a4, mul_pos (mul_pos hBB ha1) ha2, mul_pos (mul_pos hBB ha1) ha3, mul_pos (mul_pos hBB ha1) ha4, mul_pos (mul_pos hBB ha1) a1, mul_pos (mul_pos hBB ha1) a2, mul_pos (mul_pos hBB ha1) a3, mul_pos (mul_pos hBB ha1) a4, mul_pos (mul_pos hBB ha2) ha3, mul_pos (mul_pos hBB ha2) ha4, mul_pos (mul_pos hBB ha2) a1, mul_pos (mul_pos hBB ha2) a2, mul_pos (mul_pos hBB ha2) a3, mul_pos (mul_pos hBB ha2) a4, mul_pos (mul_pos hBB ha3) ha4, mul_pos (mul_pos hBB ha3) a1, mul_pos (mul_pos hBB ha3) a2, mul_pos (mul_pos hBB ha3) a3, mul_pos (mul_pos hBB ha3) a4, mul_pos (mul_pos hBB ha4) a1, mul_pos (mul_pos hBB ha4) a2, mul_pos (mul_pos hBB ha4) a3, mul_pos (mul_pos hBB ha4) a4, mul_pos (mul_pos hBB a1) a2, mul_pos (mul_pos hBB a1) a3, mul_pos (mul_pos hBB a1) a4, mul_pos (mul_pos hBB a2) a3, mul_pos (mul_pos hBB a2) a4, mul_pos (mul_pos hBB a3) a4])))


theorem Pt_quad (P : Fin 7 → C3) (a b c d : Fin 7) (i : ZMod 4) :
    P (quad a b c d i) = Qd P a b c d i := by
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rfl

theorem Pt_quint (P : Fin 7 → C3) (a b c d e : Fin 7) (i : ZMod 5) :
    P (quint a b c d e i) = Qn P a b c d e i := by
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- glue for 4-cycles at the 34 view -/
theorem glue4 (F : Frame02 x) (hr : gA12 x = gA11 x) {P : Fin 7 → C3} (hP : F.toFrame7.ptC = P)
    (a b c d : Fin 7) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (v : C3)
    (hcyc : ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      ST σ ⟨-1, 1, 0⟩ v ((Qd P a b c d (i + 1)).sub (Qd P a b c d i)) ((Qd P a b c d j).sub (Qd P a b c d i)))
    (hrest : ∀ j' : Fin 7, j' ≠ a → j' ≠ b → j' ≠ c → j' ≠ d → ∀ i : ZMod 4,
      ST σ ⟨-1, 1, 0⟩ v ((Qd P a b c d (i + 1)).sub (Qd P a b c d i)) ((P j').sub (Qd P a b c d i)))
    (hz : IsRobustUnimodal fun i : ZMod 4 => (Qd P a b c d i).y * (gA22 x - gA12 x)) :
    IsRupert (Finset.univ.image x) := by
  refine F.toFrame7.rupert_rim_rob (k := 4) (by norm_num) (quad a b c d) σ hσ ⟨-1, 1, 0⟩ v
    (Or.inl (by norm_num)) ?_ ?_ ?_
  · intro i j h1 h2
    simp only [hP, Pt_quad]
    exact hcyc i j h1 h2
  · intro j' hj' i
    simp only [hP, Pt_quad]
    refine hrest j' ?_ ?_ ?_ ?_ i
    · exact fun h => hj' 0 (by simp [quad_0, h])
    · exact fun h => hj' 1 (by simp [quad_1, h])
    · exact fun h => hj' 2 (by simp [quad_2, h])
    · exact fun h => hj' 3 (by simp [quad_3, h])
  · have e : (fun i : ZMod 4 => F.toFrame7.GG (F.toFrame7.ptC (quad a b c d i)) ⟨-1, 1, 0⟩) =
        fun i : ZMod 4 => (Qd P a b c d i).y * (gA22 x - gA12 x) := by
      funext i
      rw [F.GG_u hr]
      simp only [hP, Pt_quad]
    rw [e]; exact hz

/-- glue for 5-cycles at the 34 view -/
theorem glue5 (F : Frame02 x) (hr : gA12 x = gA11 x) {P : Fin 7 → C3} (hP : F.toFrame7.ptC = P)
    (a b c d e : Fin 7) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (v : C3)
    (hcyc : ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST σ ⟨-1, 1, 0⟩ v ((Qn P a b c d e (i + 1)).sub (Qn P a b c d e i)) ((Qn P a b c d e j).sub (Qn P a b c d e i)))
    (hrest : ∀ j' : Fin 7, j' ≠ a → j' ≠ b → j' ≠ c → j' ≠ d → j' ≠ e → ∀ i : ZMod 5,
      ST σ ⟨-1, 1, 0⟩ v ((Qn P a b c d e (i + 1)).sub (Qn P a b c d e i)) ((P j').sub (Qn P a b c d e i)))
    (hz : IsRobustUnimodal fun i : ZMod 5 => (Qn P a b c d e i).y * (gA22 x - gA12 x)) :
    IsRupert (Finset.univ.image x) := by
  refine F.toFrame7.rupert_rim_rob (k := 5) (by norm_num) (quint a b c d e) σ hσ ⟨-1, 1, 0⟩ v
    (Or.inl (by norm_num)) ?_ ?_ ?_
  · intro i j h1 h2
    simp only [hP, Pt_quint]
    exact hcyc i j h1 h2
  · intro j' hj' i
    simp only [hP, Pt_quint]
    refine hrest j' ?_ ?_ ?_ ?_ ?_ i
    · exact fun h => hj' 0 (by simp [quint_0, h])
    · exact fun h => hj' 1 (by simp [quint_1, h])
    · exact fun h => hj' 2 (by simp [quint_2, h])
    · exact fun h => hj' 3 (by simp [quint_3, h])
    · exact fun h => hj' 4 (by simp [quint_4, h])
  · have e : (fun i : ZMod 5 => F.toFrame7.GG (F.toFrame7.ptC (quint a b c d e i)) ⟨-1, 1, 0⟩) =
        fun i : ZMod 5 => (Qn P a b c d e i).y * (gA22 x - gA12 x) := by
      funext i
      rw [F.GG_u hr]
      simp only [hP, Pt_quint]
    rw [e]; exact hz

section rows
variable (tp sp tm sm k l : ℝ) (ha1 : 0 < tp) (ha2 : 0 < sp) (ha3 : 0 < tm) (ha4 : 0 < sm)
  (hk : 0 < k) (hl : 0 < l) (a1 : 0 < 1 - tp) (a2 : 0 < 1 - sp) (a3 : 0 < 1 - tm) (a4 : 0 < 1 - sm)

set_option maxHeartbeats 4000000 in
include ha1 ha2 ha3 ha4 hk hl a1 a2 a3 a4 in
theorem cyc_A1B6 (hA : sp < tp) (hB : sm < tm) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      ST (-1) ⟨-1, 1, 0⟩ ⟨-1, 0, 0⟩
        ((Qd (Pt tp sp tm sm k l) 2 6 4 1 (i + 1)).sub (Qd (Pt tp sp tm sm k l) 2 6 4 1 i))
        ((Qd (Pt tp sp tm sm k l) 2 6 4 1 j).sub (Qd (Pt tp sp tm sm k l) 2 6 4 1 i)) := by
  have hAB := sub_pos.2 hA
  have hBB := sub_pos.2 hB
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i j h1 h2
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl h1 | exact absurd (by decide) h2 | skip
  all_goals (rowtac4)


set_option maxHeartbeats 4000000 in
include ha1 ha2 ha3 ha4 hk hl a1 a2 a3 a4 in
theorem rest_A1B6 (hA : sp < tp) (hB : sm < tm) (w : Fin 7) (hw : w = 0 ∨ w = 3 ∨ w = 5) :
    ∀ i : ZMod 4,
      ST (-1) ⟨-1, 1, 0⟩ ⟨-1, 0, 0⟩
        ((Qd (Pt tp sp tm sm k l) 2 6 4 1 (i + 1)).sub (Qd (Pt tp sp tm sm k l) 2 6 4 1 i))
        ((Pt tp sp tm sm k l w).sub (Qd (Pt tp sp tm sm k l) 2 6 4 1 i)) := by
  have hAB := sub_pos.2 hA
  have hBB := sub_pos.2 hB
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases hw with rfl | rfl | rfl <;>
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rowtac4


set_option maxHeartbeats 4000000 in
include ha1 ha2 ha3 ha4 hk hl a1 a2 a3 a4 in
theorem cyc_A1B5 (hA : sp < tp) (hB : tm < sm) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST (-1) ⟨-1, 1, 0⟩ ⟨-1, 0, 0⟩
        ((Qn (Pt tp sp tm sm k l) 2 5 6 4 1 (i + 1)).sub (Qn (Pt tp sp tm sm k l) 2 5 6 4 1 i))
        ((Qn (Pt tp sp tm sm k l) 2 5 6 4 1 j).sub (Qn (Pt tp sp tm sm k l) 2 5 6 4 1 i)) := by
  have hAB := sub_pos.2 hA
  have hBB := sub_pos.2 hB
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i j h1 h2
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl h1 | exact absurd (by decide) h2 | skip
  all_goals rowtac5

set_option maxHeartbeats 4000000 in
include ha1 ha2 ha3 ha4 hk hl a1 a2 a3 a4 in
theorem rest_A1B5 (hA : sp < tp) (hB : tm < sm) (w : Fin 7) (hw : w = 0 ∨ w = 3) :
    ∀ i : ZMod 5,
      ST (-1) ⟨-1, 1, 0⟩ ⟨-1, 0, 0⟩
        ((Qn (Pt tp sp tm sm k l) 2 5 6 4 1 (i + 1)).sub (Qn (Pt tp sp tm sm k l) 2 5 6 4 1 i))
        ((Pt tp sp tm sm k l w).sub (Qn (Pt tp sp tm sm k l) 2 5 6 4 1 i)) := by
  have hAB := sub_pos.2 hA
  have hBB := sub_pos.2 hB
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases hw with rfl | rfl <;>
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;> rowtac5

set_option maxHeartbeats 4000000 in
include ha1 ha2 ha3 ha4 hk hl a1 a2 a3 a4 in
theorem cyc_V1B6 (hA : sp = tp) (hB : sm < tm) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST (-1) ⟨-1, 1, 0⟩ ⟨-1, 0, 0⟩
        ((Qn (Pt tp sp tm sm k l) 0 2 6 4 1 (i + 1)).sub (Qn (Pt tp sp tm sm k l) 0 2 6 4 1 i))
        ((Qn (Pt tp sp tm sm k l) 0 2 6 4 1 j).sub (Qn (Pt tp sp tm sm k l) 0 2 6 4 1 i)) := by
  subst hA
  have hAB : (0:ℝ) < 1 := one_pos
  have hBB := sub_pos.2 hB
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i j h1 h2
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl h1 | exact absurd (by decide) h2 | skip
  all_goals rowtac5

set_option maxHeartbeats 4000000 in
include ha1 ha2 ha3 ha4 hk hl a1 a2 a3 a4 in
theorem rest_V1B6 (hA : sp = tp) (hB : sm < tm) (w : Fin 7) (hw : w = 3 ∨ w = 5) :
    ∀ i : ZMod 5,
      ST (-1) ⟨-1, 1, 0⟩ ⟨-1, 0, 0⟩
        ((Qn (Pt tp sp tm sm k l) 0 2 6 4 1 (i + 1)).sub (Qn (Pt tp sp tm sm k l) 0 2 6 4 1 i))
        ((Pt tp sp tm sm k l w).sub (Qn (Pt tp sp tm sm k l) 0 2 6 4 1 i)) := by
  subst hA
  have hAB : (0:ℝ) < 1 := one_pos
  have hBB := sub_pos.2 hB
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases hw with rfl | rfl <;>
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;> rowtac5

set_option maxHeartbeats 4000000 in
include ha1 ha2 ha3 ha4 hk hl a1 a2 a3 a4 in
theorem cyc_A0B5 (hA : tp < sp) (hB : tm < sm) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      ST (-1) ⟨-1, 1, 0⟩ ⟨1, 0, 0⟩
        ((Qd (Pt tp sp tm sm k l) 5 3 0 2 (i + 1)).sub (Qd (Pt tp sp tm sm k l) 5 3 0 2 i))
        ((Qd (Pt tp sp tm sm k l) 5 3 0 2 j).sub (Qd (Pt tp sp tm sm k l) 5 3 0 2 i)) := by
  have hAB := sub_pos.2 hA
  have hBB := sub_pos.2 hB
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i j h1 h2
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl h1 | exact absurd (by decide) h2 | skip
  all_goals rowtac4

set_option maxHeartbeats 4000000 in
include ha1 ha2 ha3 ha4 hk hl a1 a2 a3 a4 in
theorem rest_A0B5 (hA : tp < sp) (hB : tm < sm) (w : Fin 7) (hw : w = 1 ∨ w = 4 ∨ w = 6) :
    ∀ i : ZMod 4,
      ST (-1) ⟨-1, 1, 0⟩ ⟨1, 0, 0⟩
        ((Qd (Pt tp sp tm sm k l) 5 3 0 2 (i + 1)).sub (Qd (Pt tp sp tm sm k l) 5 3 0 2 i))
        ((Pt tp sp tm sm k l w).sub (Qd (Pt tp sp tm sm k l) 5 3 0 2 i)) := by
  have hAB := sub_pos.2 hA
  have hBB := sub_pos.2 hB
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases hw with rfl | rfl | rfl <;>
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rowtac4

end rows

theorem Qd_y (P : Fin 7 → C3) (a b c d : Fin 7) (D : ℝ) :
    (fun i : ZMod 4 => (Qd P a b c d i).y * D) = quad ((P a).y * D) ((P b).y * D) ((P c).y * D) ((P d).y * D) := by
  funext i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rfl

theorem Qn_y (P : Fin 7 → C3) (a b c d e : Fin 7) (D : ℝ) :
    (fun i : ZMod 5 => (Qn P a b c d e i).y * D) =
      quint ((P a).y * D) ((P b).y * D) ((P c).y * D) ((P d).y * D) ((P e).y * D) := by
  funext i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- generic rims, `(A,B) = (1,6)`. -/
theorem right_A1B6_pf (F : Frame02 x) (hr : gA12 x = gA11 x)
    (hA : F.S.sp < F.S.tp) (hB : F.S.sm < F.S.tm) : IsRupert (Finset.univ.image x) := by
  obtain ⟨k, l, hk, hl, h1, h2, h3, h4⟩ := exists_kl F.S
  have hD := F.D_pos hr
  have a1 := sub_pos.2 F.S.tp_lt
  have a2 := sub_pos.2 F.S.sp_lt
  have a3 := sub_pos.2 F.S.tm_lt
  have a4 := sub_pos.2 F.S.sm_lt
  refine F.glue4 hr (F.ptC_eq h1 h2 h3 h4) 2 6 4 1 (-1) (Or.inr rfl) ⟨-1, 0, 0⟩
    (cyc_A1B6 _ _ _ _ k l F.S.tp_pos F.S.sp_pos F.S.tm_pos F.S.sm_pos hk hl a1 a2 a3 a4 hA hB) ?_ ?_
  · intro j' c0 c1 c2 c3 i
    have hj : j' = 0 ∨ j' = 3 ∨ j' = 5 := by
      revert j' c0 c1 c2 c3; decide
    exact rest_A1B6 _ _ _ _ k l F.S.tp_pos F.S.sp_pos F.S.tm_pos F.S.sm_pos hk hl a1 a2 a3 a4 hA hB j' hj i
  · rw [Qd_y]
    simp only [Pt_1, Pt_2, Pt_4, Pt_6]
    refine robust_quad_of_nws ?_ ?_
    · left; simp only [zero_mul]; exact mul_pos F.S.sm_pos hD
    · right; right; left
      simp only [Pt_6, one_mul]; nlinarith [F.S.sm_lt]
/-- `(A,B) = (1,5)`: `Σ_W = (5,6,4,1,2)`, one level edge `2–5`. (0,6) = α. -/
theorem right_A1B5_pf (F : Frame02 x) (hr : gA12 x = gA11 x)
    (hA : F.S.sp < F.S.tp) (hB : F.S.tm < F.S.sm) : IsRupert (Finset.univ.image x) := by
  obtain ⟨k, l, hk, hl, h1, h2, h3, h4⟩ := exists_kl F.S
  have hD := F.D_pos hr
  have a1 := sub_pos.2 F.S.tp_lt
  have a2 := sub_pos.2 F.S.sp_lt
  have a3 := sub_pos.2 F.S.tm_lt
  have a4 := sub_pos.2 F.S.sm_lt
  refine F.glue5 hr (F.ptC_eq h1 h2 h3 h4) 2 5 6 4 1 (-1) (Or.inr rfl) ⟨-1, 0, 0⟩
    (cyc_A1B5 _ _ _ _ k l F.S.tp_pos F.S.sp_pos F.S.tm_pos F.S.sm_pos hk hl a1 a2 a3 a4 hA hB) ?_ ?_
  · intro j' c0 c1 c2 c3 c4 i
    have hj : j' = 0 ∨ j' = 3 := by
      revert j' c0 c1 c2 c3 c4; decide
    exact rest_A1B5 _ _ _ _ k l F.S.tp_pos F.S.sp_pos F.S.tm_pos F.S.sm_pos hk hl a1 a2 a3 a4 hA hB j' hj i
  · rw [Qn_y]
    simp only [Pt_1, Pt_2, Pt_4, Pt_5, Pt_6]
    exact rob5 (by simp only [zero_mul, one_mul]; exact mul_pos F.S.sm_pos hD)
      (by nlinarith [F.S.sm_lt]) (by nlinarith [F.S.sp_lt]) (by simp only [zero_mul]; exact mul_pos F.S.sp_pos hD)

/-- `A` vertical, `B = 6`. -/
theorem right_V1B6_pf (F : Frame02 x) (hr : gA12 x = gA11 x)
    (hA : F.S.tp = F.S.sp) (hB : F.S.sm < F.S.tm) : IsRupert (Finset.univ.image x) := by
  obtain ⟨k, l, hk, hl, h1, h2, h3, h4⟩ := exists_kl F.S
  have hD := F.D_pos hr
  have a1 := sub_pos.2 F.S.tp_lt
  have a2 := sub_pos.2 F.S.sp_lt
  have a3 := sub_pos.2 F.S.tm_lt
  have a4 := sub_pos.2 F.S.sm_lt
  refine F.glue5 hr (F.ptC_eq h1 h2 h3 h4) 0 2 6 4 1 (-1) (Or.inr rfl) ⟨-1, 0, 0⟩
    (cyc_V1B6 _ _ _ _ k l F.S.tp_pos F.S.sp_pos F.S.tm_pos F.S.sm_pos hk hl a1 a2 a3 a4 hA.symm hB) ?_ ?_
  · intro j' c0 c1 c2 c3 c4 i
    have hj : j' = 3 ∨ j' = 5 := by
      revert j' c0 c1 c2 c3 c4; decide
    exact rest_V1B6 _ _ _ _ k l F.S.tp_pos F.S.sp_pos F.S.tm_pos F.S.sm_pos hk hl a1 a2 a3 a4 hA.symm hB j' hj i
  · rw [Qn_y]
    simp only [Pt_0, Pt_1, Pt_2, Pt_4, Pt_6]
    exact rob5 (by simp only [zero_mul, one_mul]; exact mul_pos F.S.sm_pos hD)
      (by nlinarith [F.S.sm_lt]) (by nlinarith [F.S.sp_lt]) (by simp only [zero_mul]; exact mul_pos F.S.sp_pos hD)
/-- `(A,B) = (0,5)`: the rim is the face `F1 = (5,3,0,2)` itself, all depths 0; Lemma FN (iii). -/
theorem right_A0B5_pf (F : Frame02 x) (hr : gA12 x = gA11 x)
    (hA : F.S.tp < F.S.sp) (hB : F.S.tm < F.S.sm) : IsRupert (Finset.univ.image x) := by
  obtain ⟨k, l, hk, hl, h1, h2, h3, h4⟩ := exists_kl F.S
  have hD := F.D_pos hr
  have hP := F.ptC_eq h1 h2 h3 h4
  have a1 := sub_pos.2 F.S.tp_lt
  have a2 := sub_pos.2 F.S.sp_lt
  have a3 := sub_pos.2 F.S.tm_lt
  have a4 := sub_pos.2 F.S.sm_lt
  have ha : 0 < gA11 x := hr ▸ F.A12_pos
  refine F.toFrame7.rupert_rim4 5 3 0 2 (Pt F.S.tp F.S.sp F.S.tm F.S.sm k l 5) (Pt F.S.tp F.S.sp F.S.tm F.S.sm k l 3)
    (Pt F.S.tp F.S.sp F.S.tm F.S.sm k l 0) (Pt F.S.tp F.S.sp F.S.tm F.S.sm k l 2)
    (by rw [hP]) (by rw [hP]) (by rw [hP]) (by rw [hP]) (-1) (Or.inr rfl) ⟨-1, 1, 0⟩ ⟨1, 0, 0⟩
    (Or.inl (by norm_num))
    (cyc_A0B5 _ _ _ _ k l F.S.tp_pos F.S.sp_pos F.S.tm_pos F.S.sm_pos hk hl a1 a2 a3 a4 hA hB) ?_ ?_
  · intro j' c0 c1 c2 c3 i
    have hj : j' = 1 ∨ j' = 4 ∨ j' = 6 := by
      revert j' c0 c1 c2 c3; decide
    rw [hP]
    exact rest_A0B5 _ _ _ _ k l F.S.tp_pos F.S.sp_pos F.S.tm_pos F.S.sm_pos hk hl a1 a2 a3 a4 hA hB j' hj i
  · have e : ∀ (P : C3) , F.toFrame7.GG P ⟨-1, 1, 0⟩ = P.y * (gA22 x - gA12 x) := fun P => F.GG_u hr P
    have e2 : ∀ (P : C3) , F.toFrame7.GG P ⟨1, 0, 0⟩ = gA11 x * (P.x + P.y) := by
      intro P
      have : F.toFrame7.GG P ⟨1, 0, 0⟩ = Gf (gA11 x) (gA12 x) (gA22 x) F.toFrame7.gg P ⟨1, 0, 0⟩ := rfl
      rw [this]; simp only [Gf]; rw [hr]; ring
    simp only [e, e2, Pt_5, Pt_3, Pt_0, Pt_2, quad_0, quad_1, quad_2, quad_3]
    have hz0 : ∀ i : ZMod 4, (quad (⟨F.S.tm, 0, -(l * (1 - F.S.tm))⟩ : C3) ⟨1, 0, 0⟩
        ⟨F.S.tp, 0, k * (1 - F.S.tp)⟩ ⟨0, 0, 0⟩ i).y = 0 := by
      intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rfl
    have := Q4_eventually (z := fun i : ZMod 4 => (quad (⟨F.S.tm, 0, -(l * (1 - F.S.tm))⟩ : C3) ⟨1, 0, 0⟩
        ⟨F.S.tp, 0, k * (1 - F.S.tp)⟩ ⟨0, 0, 0⟩ i).y * (gA22 x - gA12 x))
      (w := fun i : ZMod 4 => gA11 x * ((quad (⟨F.S.tm, 0, -(l * (1 - F.S.tm))⟩ : C3) ⟨1, 0, 0⟩
        ⟨F.S.tp, 0, k * (1 - F.S.tp)⟩ ⟨0, 0, 0⟩ i).x + (quad (⟨F.S.tm, 0, -(l * (1 - F.S.tm))⟩ : C3) ⟨1, 0, 0⟩
        ⟨F.S.tp, 0, k * (1 - F.S.tp)⟩ ⟨0, 0, 0⟩ i).y)) ?_ ?_
    · exact this
    · left; right
      refine ⟨by simp only [hz0], ?_⟩
      simp only [quad_0, quad_1]
      nlinarith [F.S.tm_lt, mul_pos ha (sub_pos.2 F.S.tm_lt)]
    · right; left; right
      refine ⟨by simp only [hz0], ?_⟩
      simp only [quad_0, quad_3]
      nlinarith [mul_pos ha F.S.tm_pos]
end Frame02
end Minimality.CaseC18
