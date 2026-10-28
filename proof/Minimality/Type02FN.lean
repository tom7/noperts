module

public import Minimality.Type02R

@[expose] public section

/-! # sp02 Lean, group FN: Lemma FN (iv) as sign-cell tables (face-normal view 34, `A12 = A11`).

Screen coordinates `(s, c) = (x + y, z)`.  Tilts `v = ⟨vx, 0, vz⟩` (screen displacement `(vx, vz)`).
For `V1B5` the four side covectors of `F1 = (5,3,0,2)` are
`m1 = (l, -1)`, `m2 = (k, 1)`, `m3 = (-k(1-tp), tp)`, `m4 = (-l(1-tm), -tm)`; `a = m1·w`, etc. -/

namespace Minimality.CaseC18
open Finset Filter Minimality.CaseC09
open scoped RealInnerProductSpace Topology

namespace Frame02
variable {x : Fin 7 → ℝ³}

section rows
variable (tp sm tm k l : ℝ) (ha1 : 0 < tp) (ha3 : 0 < tm) (ha4 : 0 < sm)
  (hk : 0 < k) (hl : 0 < l) (a1 : 0 < 1 - tp) (a3 : 0 < 1 - tm) (a4 : 0 < 1 - sm)

set_option maxHeartbeats 4000000 in
include ha1 ha3 hk hl a1 a3 in
theorem cycF_B (vx vz : ℝ) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      ST (-1) ⟨-1, 1, 0⟩ ⟨vx, 0, vz⟩
        ((Qd (Pt tp tp tm sm k l) 5 3 0 2 (i + 1)).sub (Qd (Pt tp tp tm sm k l) 5 3 0 2 i))
        ((Qd (Pt tp tp tm sm k l) 5 3 0 2 j).sub (Qd (Pt tp tp tm sm k l) 5 3 0 2 i)) := by
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i j h1 h2
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl h1 | exact absurd (by decide) h2 | skip
  all_goals (
    simp only [CaseC09.ST, Dc, C3.sub, Qd, Pt_0, Pt_1, Pt_2, Pt_3, Pt_4, Pt_5, Pt_6, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    left
    nlinarith [mul_pos ha1 hk, mul_pos ha1 hl, mul_pos ha3 hk, mul_pos ha3 hl, mul_pos ha1 ha3, mul_pos a1 a3,
      mul_pos (mul_pos ha1 hk) a1, mul_pos (mul_pos ha3 hl) a3, mul_pos (mul_pos ha1 hl) a3, mul_pos (mul_pos ha3 hk) a1,
      mul_pos (mul_pos ha1 hk) a3, mul_pos (mul_pos ha3 hl) a1, mul_pos (mul_pos ha1 hl) a1, mul_pos (mul_pos ha3 hk) a3,
      mul_pos (mul_pos hk hl) (mul_pos ha1 a3), mul_pos (mul_pos hk hl) (mul_pos ha3 a1), mul_pos (mul_pos hk hl) (mul_pos ha1 ha3),
      mul_pos (mul_pos hk hl) (mul_pos a1 a3), mul_pos hk a1, mul_pos hl a3, mul_pos hk a3, mul_pos hl a1])

set_option maxHeartbeats 4000000 in
include ha1 ha3 ha4 hk hl a1 a3 a4 in
theorem restF_B (hB : tm < sm) (hd : 0 < l * tp - k * (1 - tp)) (w : Fin 7) (hw : w = 1 ∨ w = 4 ∨ w = 6) :
    ∀ i : ZMod 4,
      ST (-1) ⟨-1, 1, 0⟩ ⟨2 * tp, 0, k * (1 - tp) + l * tp⟩
        ((Qd (Pt tp tp tm sm k l) 5 3 0 2 (i + 1)).sub (Qd (Pt tp tp tm sm k l) 5 3 0 2 i))
        ((Pt tp tp tm sm k l w).sub (Qd (Pt tp tp tm sm k l) 5 3 0 2 i)) := by
  have hBB := sub_pos.2 hB
  have hb : 0 < k * (1 + tp) + l * tp := by nlinarith [mul_pos hk ha1, mul_pos hl ha1]
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases hw with rfl | rfl | rfl <;>
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  (simp only [CaseC09.ST, Dc, C3.sub, Qd, Pt_0, Pt_1, Pt_2, Pt_3, Pt_4, Pt_5, Pt_6, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
   first
   | (left; linarith [ha1, ha3, ha4, hk, hl, a1, a3, a4, hBB, (mul_pos ha1 ha1), (mul_pos ha1 ha3), (mul_pos ha1 ha4), (mul_pos ha1 hk), (mul_pos ha1 hl), (mul_pos ha1 a1), (mul_pos ha1 a3), (mul_pos ha1 a4), (mul_pos ha1 hBB), (mul_pos ha3 ha3), (mul_pos ha3 ha4), (mul_pos ha3 hk), (mul_pos ha3 hl), (mul_pos ha3 a1), (mul_pos ha3 a3), (mul_pos ha3 a4), (mul_pos ha3 hBB), (mul_pos ha4 ha4), (mul_pos ha4 hk), (mul_pos ha4 hl), (mul_pos ha4 a1), (mul_pos ha4 a3), (mul_pos ha4 a4), (mul_pos ha4 hBB), (mul_pos hk a1), (mul_pos hk a3), (mul_pos hk a4), (mul_pos hk hBB), (mul_pos hl a1), (mul_pos hl a3), (mul_pos hl a4), (mul_pos hl hBB), (mul_pos a1 a1), (mul_pos a1 a3), (mul_pos a1 a4), (mul_pos a1 hBB), (mul_pos a3 a3), (mul_pos a3 a4), (mul_pos a3 hBB), (mul_pos a4 a4), (mul_pos a4 hBB), (mul_pos hBB hBB), (mul_pos (mul_pos ha1 ha1) ha1), (mul_pos (mul_pos ha1 ha1) ha3), (mul_pos (mul_pos ha1 ha1) ha4), (mul_pos (mul_pos ha1 ha1) hk), (mul_pos (mul_pos ha1 ha1) hl), (mul_pos (mul_pos ha1 ha1) a1), (mul_pos (mul_pos ha1 ha1) a3), (mul_pos (mul_pos ha1 ha1) a4), (mul_pos (mul_pos ha1 ha1) hBB), (mul_pos (mul_pos ha1 ha3) ha3), (mul_pos (mul_pos ha1 ha3) ha4), (mul_pos (mul_pos ha1 ha3) hk), (mul_pos (mul_pos ha1 ha3) hl), (mul_pos (mul_pos ha1 ha3) a1), (mul_pos (mul_pos ha1 ha3) a3), (mul_pos (mul_pos ha1 ha3) a4), (mul_pos (mul_pos ha1 ha3) hBB), (mul_pos (mul_pos ha1 ha4) ha4), (mul_pos (mul_pos ha1 ha4) hk), (mul_pos (mul_pos ha1 ha4) hl), (mul_pos (mul_pos ha1 ha4) a1), (mul_pos (mul_pos ha1 ha4) a3), (mul_pos (mul_pos ha1 ha4) a4), (mul_pos (mul_pos ha1 ha4) hBB), (mul_pos (mul_pos ha1 hk) a1), (mul_pos (mul_pos ha1 hk) a3), (mul_pos (mul_pos ha1 hk) a4), (mul_pos (mul_pos ha1 hk) hBB), (mul_pos (mul_pos ha1 hl) a1), (mul_pos (mul_pos ha1 hl) a3), (mul_pos (mul_pos ha1 hl) a4), (mul_pos (mul_pos ha1 hl) hBB), (mul_pos (mul_pos ha1 a1) a1), (mul_pos (mul_pos ha1 a1) a3), (mul_pos (mul_pos ha1 a1) a4), (mul_pos (mul_pos ha1 a1) hBB), (mul_pos (mul_pos ha1 a3) a3), (mul_pos (mul_pos ha1 a3) a4), (mul_pos (mul_pos ha1 a3) hBB), (mul_pos (mul_pos ha1 a4) a4), (mul_pos (mul_pos ha1 a4) hBB), (mul_pos (mul_pos ha1 hBB) hBB), (mul_pos (mul_pos ha3 ha3) ha3), (mul_pos (mul_pos ha3 ha3) ha4), (mul_pos (mul_pos ha3 ha3) hk), (mul_pos (mul_pos ha3 ha3) hl), (mul_pos (mul_pos ha3 ha3) a1), (mul_pos (mul_pos ha3 ha3) a3), (mul_pos (mul_pos ha3 ha3) a4), (mul_pos (mul_pos ha3 ha3) hBB), (mul_pos (mul_pos ha3 ha4) ha4), (mul_pos (mul_pos ha3 ha4) hk), (mul_pos (mul_pos ha3 ha4) hl), (mul_pos (mul_pos ha3 ha4) a1), (mul_pos (mul_pos ha3 ha4) a3), (mul_pos (mul_pos ha3 ha4) a4), (mul_pos (mul_pos ha3 ha4) hBB), (mul_pos (mul_pos ha3 hk) a1), (mul_pos (mul_pos ha3 hk) a3), (mul_pos (mul_pos ha3 hk) a4), (mul_pos (mul_pos ha3 hk) hBB), (mul_pos (mul_pos ha3 hl) a1), (mul_pos (mul_pos ha3 hl) a3), (mul_pos (mul_pos ha3 hl) a4), (mul_pos (mul_pos ha3 hl) hBB), (mul_pos (mul_pos ha3 a1) a1), (mul_pos (mul_pos ha3 a1) a3), (mul_pos (mul_pos ha3 a1) a4), (mul_pos (mul_pos ha3 a1) hBB), (mul_pos (mul_pos ha3 a3) a3), (mul_pos (mul_pos ha3 a3) a4), (mul_pos (mul_pos ha3 a3) hBB), (mul_pos (mul_pos ha3 a4) a4), (mul_pos (mul_pos ha3 a4) hBB), (mul_pos (mul_pos ha3 hBB) hBB), (mul_pos (mul_pos ha4 ha4) ha4), (mul_pos (mul_pos ha4 ha4) hk), (mul_pos (mul_pos ha4 ha4) hl), (mul_pos (mul_pos ha4 ha4) a1), (mul_pos (mul_pos ha4 ha4) a3), (mul_pos (mul_pos ha4 ha4) a4), (mul_pos (mul_pos ha4 ha4) hBB), (mul_pos (mul_pos ha4 hk) a1), (mul_pos (mul_pos ha4 hk) a3), (mul_pos (mul_pos ha4 hk) a4), (mul_pos (mul_pos ha4 hk) hBB), (mul_pos (mul_pos ha4 hl) a1), (mul_pos (mul_pos ha4 hl) a3), (mul_pos (mul_pos ha4 hl) a4), (mul_pos (mul_pos ha4 hl) hBB), (mul_pos (mul_pos ha4 a1) a1), (mul_pos (mul_pos ha4 a1) a3), (mul_pos (mul_pos ha4 a1) a4), (mul_pos (mul_pos ha4 a1) hBB), (mul_pos (mul_pos ha4 a3) a3), (mul_pos (mul_pos ha4 a3) a4), (mul_pos (mul_pos ha4 a3) hBB), (mul_pos (mul_pos ha4 a4) a4), (mul_pos (mul_pos ha4 a4) hBB), (mul_pos (mul_pos ha4 hBB) hBB), (mul_pos (mul_pos hk a1) a1), (mul_pos (mul_pos hk a1) a3), (mul_pos (mul_pos hk a1) a4), (mul_pos (mul_pos hk a1) hBB), (mul_pos (mul_pos hk a3) a3), (mul_pos (mul_pos hk a3) a4), (mul_pos (mul_pos hk a3) hBB), (mul_pos (mul_pos hk a4) a4), (mul_pos (mul_pos hk a4) hBB), (mul_pos (mul_pos hk hBB) hBB), (mul_pos (mul_pos hl a1) a1), (mul_pos (mul_pos hl a1) a3), (mul_pos (mul_pos hl a1) a4), (mul_pos (mul_pos hl a1) hBB), (mul_pos (mul_pos hl a3) a3), (mul_pos (mul_pos hl a3) a4), (mul_pos (mul_pos hl a3) hBB), (mul_pos (mul_pos hl a4) a4), (mul_pos (mul_pos hl a4) hBB), (mul_pos (mul_pos hl hBB) hBB), (mul_pos (mul_pos a1 a1) a1), (mul_pos (mul_pos a1 a1) a3), (mul_pos (mul_pos a1 a1) a4), (mul_pos (mul_pos a1 a1) hBB), (mul_pos (mul_pos a1 a3) a3), (mul_pos (mul_pos a1 a3) a4), (mul_pos (mul_pos a1 a3) hBB), (mul_pos (mul_pos a1 a4) a4), (mul_pos (mul_pos a1 a4) hBB), (mul_pos (mul_pos a1 hBB) hBB), (mul_pos (mul_pos a3 a3) a3), (mul_pos (mul_pos a3 a3) a4), (mul_pos (mul_pos a3 a3) hBB), (mul_pos (mul_pos a3 a4) a4), (mul_pos (mul_pos a3 a4) hBB), (mul_pos (mul_pos a3 hBB) hBB), (mul_pos (mul_pos a4 a4) a4), (mul_pos (mul_pos a4 a4) hBB), (mul_pos (mul_pos a4 hBB) hBB), (mul_pos (mul_pos hBB hBB) hBB)])
   | (right; constructor <;> linarith [mul_pos a3 hd, mul_pos (mul_pos ha4 a3) hd, mul_pos (mul_pos ha1 a1) hb, mul_pos a1 hb, mul_pos (mul_pos ha1 ha1) hd, ha1, ha3, ha4, hk, hl, a1, a3, a4, hBB, (mul_pos ha1 ha1), (mul_pos ha1 ha3), (mul_pos ha1 ha4), (mul_pos ha1 hk), (mul_pos ha1 hl), (mul_pos ha1 a1), (mul_pos ha1 a3), (mul_pos ha1 a4), (mul_pos ha1 hBB), (mul_pos ha3 ha3), (mul_pos ha3 ha4), (mul_pos ha3 hk), (mul_pos ha3 hl), (mul_pos ha3 a1), (mul_pos ha3 a3), (mul_pos ha3 a4), (mul_pos ha3 hBB), (mul_pos ha4 ha4), (mul_pos ha4 hk), (mul_pos ha4 hl), (mul_pos ha4 a1), (mul_pos ha4 a3), (mul_pos ha4 a4), (mul_pos ha4 hBB), (mul_pos hk a1), (mul_pos hk a3), (mul_pos hk a4), (mul_pos hk hBB), (mul_pos hl a1), (mul_pos hl a3), (mul_pos hl a4), (mul_pos hl hBB), (mul_pos a1 a1), (mul_pos a1 a3), (mul_pos a1 a4), (mul_pos a1 hBB), (mul_pos a3 a3), (mul_pos a3 a4), (mul_pos a3 hBB), (mul_pos a4 a4), (mul_pos a4 hBB), (mul_pos hBB hBB), (mul_pos (mul_pos ha1 ha1) ha1), (mul_pos (mul_pos ha1 ha1) ha3), (mul_pos (mul_pos ha1 ha1) ha4), (mul_pos (mul_pos ha1 ha1) hk), (mul_pos (mul_pos ha1 ha1) hl), (mul_pos (mul_pos ha1 ha1) a1), (mul_pos (mul_pos ha1 ha1) a3), (mul_pos (mul_pos ha1 ha1) a4), (mul_pos (mul_pos ha1 ha1) hBB), (mul_pos (mul_pos ha1 ha3) ha3), (mul_pos (mul_pos ha1 ha3) ha4), (mul_pos (mul_pos ha1 ha3) hk), (mul_pos (mul_pos ha1 ha3) hl), (mul_pos (mul_pos ha1 ha3) a1), (mul_pos (mul_pos ha1 ha3) a3), (mul_pos (mul_pos ha1 ha3) a4), (mul_pos (mul_pos ha1 ha3) hBB), (mul_pos (mul_pos ha1 ha4) ha4), (mul_pos (mul_pos ha1 ha4) hk), (mul_pos (mul_pos ha1 ha4) hl), (mul_pos (mul_pos ha1 ha4) a1), (mul_pos (mul_pos ha1 ha4) a3), (mul_pos (mul_pos ha1 ha4) a4), (mul_pos (mul_pos ha1 ha4) hBB), (mul_pos (mul_pos ha1 hk) a1), (mul_pos (mul_pos ha1 hk) a3), (mul_pos (mul_pos ha1 hk) a4), (mul_pos (mul_pos ha1 hk) hBB), (mul_pos (mul_pos ha1 hl) a1), (mul_pos (mul_pos ha1 hl) a3), (mul_pos (mul_pos ha1 hl) a4), (mul_pos (mul_pos ha1 hl) hBB), (mul_pos (mul_pos ha1 a1) a1), (mul_pos (mul_pos ha1 a1) a3), (mul_pos (mul_pos ha1 a1) a4), (mul_pos (mul_pos ha1 a1) hBB), (mul_pos (mul_pos ha1 a3) a3), (mul_pos (mul_pos ha1 a3) a4), (mul_pos (mul_pos ha1 a3) hBB), (mul_pos (mul_pos ha1 a4) a4), (mul_pos (mul_pos ha1 a4) hBB), (mul_pos (mul_pos ha1 hBB) hBB), (mul_pos (mul_pos ha3 ha3) ha3), (mul_pos (mul_pos ha3 ha3) ha4), (mul_pos (mul_pos ha3 ha3) hk), (mul_pos (mul_pos ha3 ha3) hl), (mul_pos (mul_pos ha3 ha3) a1), (mul_pos (mul_pos ha3 ha3) a3), (mul_pos (mul_pos ha3 ha3) a4), (mul_pos (mul_pos ha3 ha3) hBB), (mul_pos (mul_pos ha3 ha4) ha4), (mul_pos (mul_pos ha3 ha4) hk), (mul_pos (mul_pos ha3 ha4) hl), (mul_pos (mul_pos ha3 ha4) a1), (mul_pos (mul_pos ha3 ha4) a3), (mul_pos (mul_pos ha3 ha4) a4), (mul_pos (mul_pos ha3 ha4) hBB), (mul_pos (mul_pos ha3 hk) a1), (mul_pos (mul_pos ha3 hk) a3), (mul_pos (mul_pos ha3 hk) a4), (mul_pos (mul_pos ha3 hk) hBB), (mul_pos (mul_pos ha3 hl) a1), (mul_pos (mul_pos ha3 hl) a3), (mul_pos (mul_pos ha3 hl) a4), (mul_pos (mul_pos ha3 hl) hBB), (mul_pos (mul_pos ha3 a1) a1), (mul_pos (mul_pos ha3 a1) a3), (mul_pos (mul_pos ha3 a1) a4), (mul_pos (mul_pos ha3 a1) hBB), (mul_pos (mul_pos ha3 a3) a3), (mul_pos (mul_pos ha3 a3) a4), (mul_pos (mul_pos ha3 a3) hBB), (mul_pos (mul_pos ha3 a4) a4), (mul_pos (mul_pos ha3 a4) hBB), (mul_pos (mul_pos ha3 hBB) hBB), (mul_pos (mul_pos ha4 ha4) ha4), (mul_pos (mul_pos ha4 ha4) hk), (mul_pos (mul_pos ha4 ha4) hl), (mul_pos (mul_pos ha4 ha4) a1), (mul_pos (mul_pos ha4 ha4) a3), (mul_pos (mul_pos ha4 ha4) a4), (mul_pos (mul_pos ha4 ha4) hBB), (mul_pos (mul_pos ha4 hk) a1), (mul_pos (mul_pos ha4 hk) a3), (mul_pos (mul_pos ha4 hk) a4), (mul_pos (mul_pos ha4 hk) hBB), (mul_pos (mul_pos ha4 hl) a1), (mul_pos (mul_pos ha4 hl) a3), (mul_pos (mul_pos ha4 hl) a4), (mul_pos (mul_pos ha4 hl) hBB), (mul_pos (mul_pos ha4 a1) a1), (mul_pos (mul_pos ha4 a1) a3), (mul_pos (mul_pos ha4 a1) a4), (mul_pos (mul_pos ha4 a1) hBB), (mul_pos (mul_pos ha4 a3) a3), (mul_pos (mul_pos ha4 a3) a4), (mul_pos (mul_pos ha4 a3) hBB), (mul_pos (mul_pos ha4 a4) a4), (mul_pos (mul_pos ha4 a4) hBB), (mul_pos (mul_pos ha4 hBB) hBB), (mul_pos (mul_pos hk a1) a1), (mul_pos (mul_pos hk a1) a3), (mul_pos (mul_pos hk a1) a4), (mul_pos (mul_pos hk a1) hBB), (mul_pos (mul_pos hk a3) a3), (mul_pos (mul_pos hk a3) a4), (mul_pos (mul_pos hk a3) hBB), (mul_pos (mul_pos hk a4) a4), (mul_pos (mul_pos hk a4) hBB), (mul_pos (mul_pos hk hBB) hBB), (mul_pos (mul_pos hl a1) a1), (mul_pos (mul_pos hl a1) a3), (mul_pos (mul_pos hl a1) a4), (mul_pos (mul_pos hl a1) hBB), (mul_pos (mul_pos hl a3) a3), (mul_pos (mul_pos hl a3) a4), (mul_pos (mul_pos hl a3) hBB), (mul_pos (mul_pos hl a4) a4), (mul_pos (mul_pos hl a4) hBB), (mul_pos (mul_pos hl hBB) hBB), (mul_pos (mul_pos a1 a1) a1), (mul_pos (mul_pos a1 a1) a3), (mul_pos (mul_pos a1 a1) a4), (mul_pos (mul_pos a1 a1) hBB), (mul_pos (mul_pos a1 a3) a3), (mul_pos (mul_pos a1 a3) a4), (mul_pos (mul_pos a1 a3) hBB), (mul_pos (mul_pos a1 a4) a4), (mul_pos (mul_pos a1 a4) hBB), (mul_pos (mul_pos a1 hBB) hBB), (mul_pos (mul_pos a3 a3) a3), (mul_pos (mul_pos a3 a3) a4), (mul_pos (mul_pos a3 a3) hBB), (mul_pos (mul_pos a3 a4) a4), (mul_pos (mul_pos a3 a4) hBB), (mul_pos (mul_pos a3 hBB) hBB), (mul_pos (mul_pos a4 a4) a4), (mul_pos (mul_pos a4 a4) hBB), (mul_pos (mul_pos a4 hBB) hBB), (mul_pos (mul_pos hBB hBB) hBB)]))

theorem gg_pos (F : Frame02 x) : 0 < F.toFrame7.gg := real_inner_self_pos.2 F.e_ne

theorem GG_v (F : Frame02 x) (hr : gA12 x = gA11 x) (p : C3) (vx vz : ℝ) :
    F.toFrame7.GG p ⟨vx, 0, vz⟩ = gA11 x * (vx * (p.x + p.y)) + F.toFrame7.gg * (vz * p.z) := by
  have : F.toFrame7.GG p ⟨vx, 0, vz⟩ = Gf (gA11 x) (gA12 x) (gA22 x) F.toFrame7.gg p ⟨vx, 0, vz⟩ := rfl
  rw [this]; simp only [Gf]; rw [hr]; ring

/-- **Case I of `V1B5`**: `k (1 - tp) < l tp`; tilt `w = (2 tp, k (1 - tp) + l tp)`, rim `F1 = (5,3,0,2)`, all positives hidden. -/
theorem fnB_I (F : Frame02 x) (hr : gA12 x = gA11 x)
    (hA : F.S.tp = F.S.sp) (hB : F.S.tm < F.S.sm) (k l : ℝ) (hk : 0 < k) (hl : 0 < l)
    (h1 : F.S.hp = k * (1 - F.S.tp)) (h2 : F.S.kp = k * (1 - F.S.sp))
    (h3 : F.S.hm = l * (1 - F.S.tm)) (h4 : F.S.km = l * (1 - F.S.sm))
    (hd : 0 < l * F.S.tp - k * (1 - F.S.tp)) : IsRupert (Finset.univ.image x) := by
  have hP := F.ptC_eq h1 h2 h3 h4
  have a1 := sub_pos.2 F.S.tp_lt
  have a3 := sub_pos.2 F.S.tm_lt
  have a4 := sub_pos.2 F.S.sm_lt
  have ha : 0 < gA11 x := hr ▸ F.A12_pos
  have hg := F.gg_pos
  rw [← hA] at hP
  have hvz : 0 < k * (1 - F.S.tp) + l * F.S.tp := by nlinarith [mul_pos hk a1, mul_pos hl F.S.tp_pos]
  refine F.toFrame7.rupert_rim4 5 3 0 2 (Pt F.S.tp F.S.tp F.S.tm F.S.sm k l 5) (Pt F.S.tp F.S.tp F.S.tm F.S.sm k l 3)
    (Pt F.S.tp F.S.tp F.S.tm F.S.sm k l 0) (Pt F.S.tp F.S.tp F.S.tm F.S.sm k l 2)
    (by rw [hP]) (by rw [hP]) (by rw [hP]) (by rw [hP]) (-1) (Or.inr rfl) ⟨-1, 1, 0⟩
    ⟨2 * F.S.tp, 0, k * (1 - F.S.tp) + l * F.S.tp⟩ (Or.inl (by norm_num))
    (cycF_B _ _ _ _ _ F.S.tp_pos F.S.tm_pos hk hl a1 a3 _ _) ?_ ?_
  · intro j' c0 c1 c2 c3 i
    have hj : j' = 1 ∨ j' = 4 ∨ j' = 6 := by
      revert j' c0 c1 c2 c3; decide
    rw [hP]
    exact restF_B _ _ _ _ _ F.S.tp_pos F.S.tm_pos F.S.sm_pos hk hl a1 a3 a4 hB hd j' hj i
  · set Pt5 : C3 := ⟨F.S.tm, 0, -(l * (1 - F.S.tm))⟩ with hP5
    set Pt0 : C3 := ⟨F.S.tp, 0, k * (1 - F.S.tp)⟩ with hP0
    have hz0 : ∀ i : ZMod 4, (quad Pt5 ⟨1, 0, 0⟩ Pt0 ⟨0, 0, 0⟩ i).y = 0 := by
      intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rfl
    simp only [F.GG_u hr, F.GG_v hr, Pt_5, Pt_3, Pt_0, Pt_2]
    refine Q4_eventually (z := fun i : ZMod 4 => (quad Pt5 ⟨1, 0, 0⟩ Pt0 ⟨0, 0, 0⟩ i).y * (gA22 x - gA12 x))
      (w := fun i : ZMod 4 => gA11 x * (2 * F.S.tp * ((quad Pt5 ⟨1, 0, 0⟩ Pt0 ⟨0, 0, 0⟩ i).x + (quad Pt5 ⟨1, 0, 0⟩ Pt0 ⟨0, 0, 0⟩ i).y)) +
        F.toFrame7.gg * ((k * (1 - F.S.tp) + l * F.S.tp) * (quad Pt5 ⟨1, 0, 0⟩ Pt0 ⟨0, 0, 0⟩ i).z)) ?_ ?_
    · left; right
      refine ⟨by simp only [hz0], ?_⟩
      simp only [quad_0, quad_1, hP5, hP0]
      nlinarith [mul_pos ha (mul_pos F.S.tp_pos a3), mul_pos hg (mul_pos hvz (mul_pos hl a3))]
    · right; right; right; right
      refine ⟨by simp only [hz0], ?_⟩
      simp only [quad_0, quad_1, quad_2, quad_3, hP5, hP0]
      nlinarith [mul_pos ha F.S.tp_pos, mul_pos hg (mul_pos hvz (mul_pos hk a1)), mul_pos ha (mul_pos F.S.tp_pos F.S.tp_pos)]
end rows
end Frame02
end Minimality.CaseC18
