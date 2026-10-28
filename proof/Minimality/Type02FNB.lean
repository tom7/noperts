module

public import Minimality.Type02FN

@[expose] public section

/-! # sp02 Lean, group FN (part B): `right_V1B5` for `δ ≤ 0` (cases II-IV) and the assembly. -/

namespace Minimality.CaseC18
open Finset Filter Minimality.CaseC09
open scoped RealInnerProductSpace Topology

/-- depth predicate: every index except `t` has a strictly larger neighbour -/
def Qtop {k : ℕ} (t : ZMod k) (z : ZMod k → ℝ) : Prop :=
  ∀ i, i ≠ t → z i < z (i - 1) ∨ z i < z (i + 1)

theorem Qtop_open {k : ℕ} [NeZero k] (t : ZMod k) : IsOpen {z : ZMod k → ℝ | Qtop t z} := by
  have hlt : ∀ i j : ZMod k, IsOpen {z : ZMod k → ℝ | z i < z j} := fun i j =>
    isOpen_lt (continuous_apply i) (continuous_apply j)
  have : {z : ZMod k → ℝ | Qtop t z} = ⋂ i : ZMod k, {z | i ≠ t → z i < z (i - 1) ∨ z i < z (i + 1)} := by
    ext z; simp [Qtop]
  rw [this]
  refine isOpen_iInter_of_finite fun i => ?_
  by_cases h : i = t
  · simp [h]
  · simp only [h, ne_eq, not_false_eq_true, forall_const]
    exact (hlt _ _).union (hlt _ _)

theorem Qtop_eventually {k : ℕ} [NeZero k] (t : ZMod k) {z w : ZMod k → ℝ}
    (h : ∀ i, i ≠ t → (z i < z (i - 1) ∨ (z i = z (i - 1) ∧ w i < w (i - 1))) ∨
      (z i < z (i + 1) ∨ (z i = z (i + 1) ∧ w i < w (i + 1)))) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), Qtop t fun i => z i + s * w i := by
  unfold Qtop
  refine Filter.eventually_all.2 fun i => ?_
  by_cases hi : i = t
  · exact Filter.Eventually.of_forall fun s h' => absurd hi h'
  · rcases h i hi with h1 | h1
    · filter_upwards [ev_lt h1] with s hs _ using Or.inl hs
    · filter_upwards [ev_lt h1] with s hs _ using Or.inr hs


namespace Frame02
variable {x : Fin 7 → ℝ³}

def c1 : ZMod 6 → Fin 7 := ![5, 3, 4, 1, 0, 2]
def c3 : ZMod 6 → Fin 7 := ![5, 6, 4, 1, 0, 2]
def c2 : ZMod 5 → Fin 7 := ![5, 3, 4, 1, 2]
theorem c1_0 : c1 0 = 5 := rfl
theorem c1_1 : c1 1 = 3 := rfl
theorem c1_2 : c1 2 = 4 := rfl
theorem c1_3 : c1 3 = 1 := rfl
theorem c1_4 : c1 4 = 0 := rfl
theorem c1_5 : c1 5 = 2 := rfl
theorem c3_0 : c3 0 = 5 := rfl
theorem c3_1 : c3 1 = 6 := rfl
theorem c3_2 : c3 2 = 4 := rfl
theorem c3_3 : c3 3 = 1 := rfl
theorem c3_4 : c3 4 = 0 := rfl
theorem c3_5 : c3 5 = 2 := rfl
theorem c2_0 : c2 0 = 5 := rfl
theorem c2_1 : c2 1 = 3 := rfl
theorem c2_2 : c2 2 = 4 := rfl
theorem c2_3 : c2 3 = 1 := rfl
theorem c2_4 : c2 4 = 2 := rfl

theorem exc_row (tp m k l vx vz : ℝ) (hp : 0 < tp) (a1 : 0 < 1 - tp) (hm : 0 < m) (a3 : 0 < 1 - m)
    (hk : 0 < k) (hl : 0 < l) (hb : 0 < -(k * vx + vz)) (hc : 0 < tp * vz - k * (1 - tp) * vx) :
    0 < tp * ((tp - m) * vz - (k * (1 - tp) + l * (1 - m)) * vx) := by
  have key : k * ((tp - m) * vz - (k * (1 - tp) + l * (1 - m)) * vx) =
      (k * (1 - tp) * m + (1 - m) * l * tp) * (-(k * vx + vz)) +
        (1 - m) * (k + l) * (tp * vz - k * (1 - tp) * vx) := by ring
  have h1 : 0 < k * (1 - tp) * m + (1 - m) * l * tp := by positivity
  have h2 : 0 < k * ((tp - m) * vz - (k * (1 - tp) + l * (1 - m)) * vx) := by
    rw [key]; have := mul_pos h1 hb; nlinarith [mul_pos (mul_pos a3 (add_pos hk hl)) hc]
  have h3 := pos_of_mul_pos_right h2 hk.le
  exact mul_pos hp h3

set_option hygiene false in
macro "fnbpre" : tactic => `(tactic| (
  have q1 := a3
  have q2 := mul_pos ha4 a3
  have q3 := a4
  have q4 := a1
  have q5 := mul_pos ha1 a1
  have q6 := ha1
  have q7 := mul_pos ha3 a4
  have f1 := mul_pos (mul_pos (add_pos hk hl) a3) a1
  have f2 := add_pos (mul_pos (mul_pos hk ha3) a1) (mul_pos (mul_pos hl ha1) a3)
  have f3 := mul_pos hk a1
  have f4 := mul_pos hl a3
  have f5 := mul_pos hl a4
  have f6 := mul_pos (mul_pos (add_pos hk hl) a4) a1
  have f7 := add_pos (mul_pos (mul_pos hk ha4) a1) (mul_pos (mul_pos hl ha1) a4)
  have f8 := mul_pos hl hBB
  have f9 := mul_pos (mul_pos (add_pos hk hl) hBB) a1))

set_option hygiene false in
macro "rowfnb" : tactic => `(tactic| (
  simp only [CaseC09.ST, Dc, C3.sub, Pt_0, Pt_1, Pt_2, Pt_3, Pt_4, Pt_5, Pt_6, c1_0, c1_1, c1_2, c1_3, c1_4, c1_5,
    c2_0, c2_1, c2_2, c2_3, c2_4, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, b0, b1, b2, b3, b4, b5]
  first
  | (left; linarith [f1, f2, f3, f4, f5, f6, f7, f8, f9])
  | (right; constructor
     · linarith
     · linarith [mul_pos q1 hsa, mul_pos q1 hsb, mul_pos q1 hsc, mul_pos q2 hsa, mul_pos q2 hsb, mul_pos q2 hsc,
         mul_pos q3 hsa, mul_pos q3 hsb, mul_pos q3 hsc, mul_pos q4 hsa, mul_pos q4 hsb, mul_pos q4 hsc,
         mul_pos q5 hsa, mul_pos q5 hsb, mul_pos q5 hsc, mul_pos q6 hsa, mul_pos q6 hsb, mul_pos q6 hsc,
         mul_pos q7 hsa, mul_pos q7 hsb, mul_pos q7 hsc, e2, e3, ev]))) 


section rowsB
variable (tp tm sm k l vx vz : ℝ) (ha1 : 0 < tp) (ha3 : 0 < tm) (ha4 : 0 < sm)
  (hk : 0 < k) (hl : 0 < l) (a1 : 0 < 1 - tp) (a3 : 0 < 1 - tm) (a4 : 0 < 1 - sm) (hBB : 0 < sm - tm)

set_option maxHeartbeats 4000000 in
include ha1 ha3 ha4 hk hl a1 a3 a4 hBB in
theorem cyc_R1 (hsa : 0 < l * vx - vz) (hsb : 0 < -(k * vx + vz)) (hsc : 0 < tp * vz - k * (1 - tp) * vx) :
    ∀ i j : ZMod 6, j ≠ i → j ≠ i + 1 →
      ST (-1) ⟨-1, 1, 0⟩ ⟨vx, 0, vz⟩
        ((Pt tp tp tm sm k l (c1 (i + 1))).sub (Pt tp tp tm sm k l (c1 i)))
        ((Pt tp tp tm sm k l (c1 j)).sub (Pt tp tp tm sm k l (c1 i))) := by
  fnbpre
  have ev : 0 < -vz := by nlinarith [mul_pos hk hsa, mul_pos hl hsb]
  have e2 := exc_row tp tm k l vx vz ha1 a1 ha3 a3 hk hl hsb hsc
  have e3 := exc_row tp sm k l vx vz ha1 a1 ha4 a4 hk hl hsb hsc
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := zmod6_add_one
  intro i j h1 h2
  rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl h1 | exact absurd (by decide) h2 | skip
  all_goals rowfnb

set_option maxHeartbeats 4000000 in
include ha1 ha3 ha4 hk hl a1 a3 a4 hBB in
theorem rest_R1 (hsa : 0 < l * vx - vz) (hsb : 0 < -(k * vx + vz)) (hsc : 0 < tp * vz - k * (1 - tp) * vx) (w : Fin 7) (hw : w = 6 ∨ w = 6) :
    ∀ i : ZMod 6,
      ST (-1) ⟨-1, 1, 0⟩ ⟨vx, 0, vz⟩
        ((Pt tp tp tm sm k l (c1 (i + 1))).sub (Pt tp tp tm sm k l (c1 i)))
        ((Pt tp tp tm sm k l w).sub (Pt tp tp tm sm k l (c1 i))) := by
  fnbpre
  have ev : 0 < -vz := by nlinarith [mul_pos hk hsa, mul_pos hl hsb]
  have e2 := exc_row tp tm k l vx vz ha1 a1 ha3 a3 hk hl hsb hsc
  have e3 := exc_row tp sm k l vx vz ha1 a1 ha4 a4 hk hl hsb hsc
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := zmod6_add_one
  intro i
  rcases hw with rfl | rfl <;>
  rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;> rowfnb

set_option maxHeartbeats 4000000 in
include ha1 ha3 ha4 hk hl a1 a3 a4 hBB in
theorem cyc_R2 (hsa : 0 < l * vx - vz) (hsb : 0 < -(k * vx + vz)) (hsc : 0 < -(tp * vz - k * (1 - tp) * vx)) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST (-1) ⟨-1, 1, 0⟩ ⟨vx, 0, vz⟩
        ((Pt tp tp tm sm k l (c2 (i + 1))).sub (Pt tp tp tm sm k l (c2 i)))
        ((Pt tp tp tm sm k l (c2 j)).sub (Pt tp tp tm sm k l (c2 i))) := by
  fnbpre
  have ev : 0 < -vz := by nlinarith [mul_pos hk hsa, mul_pos hl hsb]
  have e2 : (0:ℝ) < 1 := one_pos
  have e3 : (0:ℝ) < 1 := one_pos
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  have b5 : (0:ℕ) = 0 := rfl
  intro i j h1 h2
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl h1 | exact absurd (by decide) h2 | skip
  all_goals rowfnb

set_option maxHeartbeats 4000000 in
include ha1 ha3 ha4 hk hl a1 a3 a4 hBB in
theorem rest_R2 (hsa : 0 < l * vx - vz) (hsb : 0 < -(k * vx + vz)) (hsc : 0 < -(tp * vz - k * (1 - tp) * vx)) (w : Fin 7) (hw : w = 0 ∨ w = 6) :
    ∀ i : ZMod 5,
      ST (-1) ⟨-1, 1, 0⟩ ⟨vx, 0, vz⟩
        ((Pt tp tp tm sm k l (c2 (i + 1))).sub (Pt tp tp tm sm k l (c2 i)))
        ((Pt tp tp tm sm k l w).sub (Pt tp tp tm sm k l (c2 i))) := by
  fnbpre
  have ev : 0 < -vz := by nlinarith [mul_pos hk hsa, mul_pos hl hsb]
  have e2 : (0:ℝ) < 1 := one_pos
  have e3 : (0:ℝ) < 1 := one_pos
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  have b5 : (0:ℕ) = 0 := rfl
  intro i
  rcases hw with rfl | rfl <;>
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;> rowfnb

set_option maxHeartbeats 4000000 in
include ha1 ha3 ha4 hk hl a1 a3 a4 hBB in
theorem cyc_R3 (hsa : 0 < -(l * vx - vz)) (hsb : 0 < -(k * vx + vz)) (hsc : 0 < tp * vz - k * (1 - tp) * vx) :
    ∀ i j : ZMod 6, j ≠ i → j ≠ i + 1 →
      ST (-1) ⟨-1, 1, 0⟩ ⟨vx, 0, vz⟩
        ((Pt tp tp tm sm k l (c3 (i + 1))).sub (Pt tp tp tm sm k l (c3 i)))
        ((Pt tp tp tm sm k l (c3 j)).sub (Pt tp tp tm sm k l (c3 i))) := by
  fnbpre
  have ev : (0:ℝ) < 1 := one_pos
  have e2 := exc_row tp tm k l vx vz ha1 a1 ha3 a3 hk hl hsb hsc
  have e3 := exc_row tp sm k l vx vz ha1 a1 ha4 a4 hk hl hsb hsc
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := zmod6_add_one
  intro i j h1 h2
  rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl h1 | exact absurd (by decide) h2 | skip
  all_goals rowfnb

set_option maxHeartbeats 4000000 in
include ha1 ha3 ha4 hk hl a1 a3 a4 hBB in
theorem rest_R3 (hsa : 0 < -(l * vx - vz)) (hsb : 0 < -(k * vx + vz)) (hsc : 0 < tp * vz - k * (1 - tp) * vx) (w : Fin 7) (hw : w = 3 ∨ w = 3) :
    ∀ i : ZMod 6,
      ST (-1) ⟨-1, 1, 0⟩ ⟨vx, 0, vz⟩
        ((Pt tp tp tm sm k l (c3 (i + 1))).sub (Pt tp tp tm sm k l (c3 i)))
        ((Pt tp tp tm sm k l w).sub (Pt tp tp tm sm k l (c3 i))) := by
  fnbpre
  have ev : (0:ℝ) < 1 := one_pos
  have e2 := exc_row tp tm k l vx vz ha1 a1 ha3 a3 hk hl hsb hsc
  have e3 := exc_row tp sm k l vx vz ha1 a1 ha4 a4 hk hl hsb hsc
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := zmod6_add_one
  intro i
  rcases hw with rfl | rfl <;>
  rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;> rowfnb

end rowsB


theorem rim_top {k : ℕ} [NeZero k] (F : Frame02 x) (hr : gA12 x = gA11 x) {P : Fin 7 → C3}
    (hP : F.toFrame7.ptC = P) (hk : 3 ≤ k) (c : ZMod k → Fin 7) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (vx vz : ℝ) (t : ZMod k)
    (hcyc : ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 →
      ST σ ⟨-1, 1, 0⟩ ⟨vx, 0, vz⟩ ((P (c (i + 1))).sub (P (c i))) ((P (c j)).sub (P (c i))))
    (hrest : ∀ j' : Fin 7, (∀ jj, j' ≠ c jj) → ∀ i : ZMod k,
      ST σ ⟨-1, 1, 0⟩ ⟨vx, 0, vz⟩ ((P (c (i + 1))).sub (P (c i))) ((P j').sub (P (c i))))
    (hlex : ∀ i, i ≠ t →
      (((P (c i)).y * (gA22 x - gA12 x) < (P (c (i - 1))).y * (gA22 x - gA12 x)) ∨
        ((P (c i)).y * (gA22 x - gA12 x) = (P (c (i - 1))).y * (gA22 x - gA12 x) ∧
          gA11 x * (vx * ((P (c i)).x + (P (c i)).y)) + F.toFrame7.gg * (vz * (P (c i)).z) <
          gA11 x * (vx * ((P (c (i - 1))).x + (P (c (i - 1))).y)) + F.toFrame7.gg * (vz * (P (c (i - 1))).z))) ∨
      (((P (c i)).y * (gA22 x - gA12 x) < (P (c (i + 1))).y * (gA22 x - gA12 x)) ∨
        ((P (c i)).y * (gA22 x - gA12 x) = (P (c (i + 1))).y * (gA22 x - gA12 x) ∧
          gA11 x * (vx * ((P (c i)).x + (P (c i)).y)) + F.toFrame7.gg * (vz * (P (c i)).z) <
          gA11 x * (vx * ((P (c (i + 1))).x + (P (c (i + 1))).y)) + F.toFrame7.gg * (vz * (P (c (i + 1))).z)))) :
    IsRupert (Finset.univ.image x) := by
  refine F.toFrame7.rupert_rim hk c σ hσ ⟨-1, 1, 0⟩ ⟨vx, 0, vz⟩ (Or.inl (by norm_num)) ?_ ?_
    (Qtop t) (Qtop_open t) ?_ ?_ ?_ ?_
  · intro i j h1 h2; simpa [hP] using hcyc i j h1 h2
  · intro j' hj' i; simpa [hP] using hrest j' hj' i
  · intro z a ha hq i hi
    rcases hq i hi with h | h
    · exact Or.inl (mul_lt_mul_of_pos_left h ha)
    · exact Or.inr (mul_lt_mul_of_pos_left h ha)
  · intro z a hq i hi
    rcases hq i hi with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · have := Qtop_eventually t (z := fun i => (P (c i)).y * (gA22 x - gA12 x))
      (w := fun i => gA11 x * (vx * ((P (c i)).x + (P (c i)).y)) + F.toFrame7.gg * (vz * (P (c i)).z)) hlex
    refine this.mono fun s hs => ?_
    convert hs using 3 with i
    · rw [F.GG_u hr, hP]
    · rw [F.GG_v hr, hP]
  · intro z hinj hq
    exact isCyclicUnimodal_of_top (by omega) hinj t hq



set_option hygiene false in
macro "lexclose" : tactic => `(tactic| (
  first
  | (rcases hL1 with hL | hL <;> first
      | (left; right; first | (constructor <;> first | trivial | ring1 | linarith) | linarith) | (right; right; first | (constructor <;> first | trivial | ring1 | linarith) | linarith))
  | (rcases hL2 with hL | hL <;> first
      | (left; right; first | (constructor <;> first | trivial | ring1 | linarith) | linarith) | (right; right; first | (constructor <;> first | trivial | ring1 | linarith) | linarith))
  | (first
      | (left; left; nlinarith [mul_pos ha1 hD, mul_pos a1 hD, mul_pos ha4 hD, mul_pos a4 hD, mul_pos ha3 hD, mul_pos a3 hD])
      | (right; left; nlinarith [mul_pos ha1 hD, mul_pos a1 hD, mul_pos ha4 hD, mul_pos a4 hD, mul_pos ha3 hD, mul_pos a3 hD]))))

set_option maxHeartbeats 4000000 in
theorem rimR1 (F : Frame02 x) (hr : gA12 x = gA11 x)
    (hA : F.S.tp = F.S.sp) (hB : F.S.tm < F.S.sm) (k l : ℝ) (hk : 0 < k) (hl : 0 < l)
    (h1 : F.S.hp = k * (1 - F.S.tp)) (h2 : F.S.kp = k * (1 - F.S.sp))
    (h3 : F.S.hm = l * (1 - F.S.tm)) (h4 : F.S.km = l * (1 - F.S.sm)) (vx vz : ℝ) (hsa : 0 < l * vx - vz) (hsb : 0 < -(k * vx + vz)) (hsc : 0 < F.S.tp * vz - k * (1 - F.S.tp) * vx)
    (hL1 : gA11 x * vx * F.S.tm - F.toFrame7.gg * vz * (l * (1 - F.S.tm)) < 0 ∨
      gA11 x * vx * F.S.tm - F.toFrame7.gg * vz * (l * (1 - F.S.tm)) < gA11 x * vx)
    (hL2 : 0 < gA11 x * vx * F.S.tp + F.toFrame7.gg * vz * (k * (1 - F.S.tp)) ∨
      0 < gA11 x * vx * F.S.tm - F.toFrame7.gg * vz * (l * (1 - F.S.tm))) : IsRupert (Finset.univ.image x) := by
  have hP := F.ptC_eq h1 h2 h3 h4
  rw [← hA] at hP
  have a1 := sub_pos.2 F.S.tp_lt
  have a3 := sub_pos.2 F.S.tm_lt
  have a4 := sub_pos.2 F.S.sm_lt
  have hBB := sub_pos.2 hB
  have hD := F.D_pos hr
  have ha1 := F.S.tp_pos
  have ha3 := F.S.tm_pos
  have ha4 := F.S.sm_pos
  have hj : ∀ j' : Fin 7, (∀ jj, j' ≠ c1 jj) → j' = 6 := by intro j' hj'; fin_cases j' <;> first | rfl | exact absurd rfl (hj' 0) | exact absurd rfl (hj' 1) | exact absurd rfl (hj' 2) | exact absurd rfl (hj' 3) | exact absurd rfl (hj' 4) | exact absurd rfl (hj' 5)
  refine F.rim_top hr hP (k := 6) (by norm_num) c1 (-1) (Or.inr rfl) vx vz 2 ?_ ?_ ?_
  · exact cyc_R1 _ _ _ _ _ _ _ ha1 ha3 ha4 hk hl a1 a3 a4 hBB hsa hsb hsc
  · intro j' hj' i
    rcases hj j' hj' with rfl
    all_goals exact rest_R1 _ _ _ _ _ _ _ ha1 ha3 ha4 hk hl a1 a3 a4 hBB hsa hsb hsc _ (by simp) i
  · intro i hi
    obtain ⟨b0, b1, b2, b3, b4, b5⟩ := zmod6_add_one
    obtain ⟨d0, d1, d2, d3, d4, d5⟩ := zmod6_sub_one
    rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Pt_0, Pt_1, Pt_2, Pt_3, Pt_4, Pt_5, Pt_6, c1_0, c1_1, c1_2, c1_3, c1_4, c1_5, b0, b1, b2, b3, b4, b5, d0, d1, d2, d3, d4, d5] at hi ⊢ <;>
      first | exact absurd rfl hi | skip
    all_goals lexclose

set_option maxHeartbeats 4000000 in
theorem rimR2 (F : Frame02 x) (hr : gA12 x = gA11 x)
    (hA : F.S.tp = F.S.sp) (hB : F.S.tm < F.S.sm) (k l : ℝ) (hk : 0 < k) (hl : 0 < l)
    (h1 : F.S.hp = k * (1 - F.S.tp)) (h2 : F.S.kp = k * (1 - F.S.sp))
    (h3 : F.S.hm = l * (1 - F.S.tm)) (h4 : F.S.km = l * (1 - F.S.sm)) (vx vz : ℝ) (hsa : 0 < l * vx - vz) (hsb : 0 < -(k * vx + vz)) (hsc : 0 < -(F.S.tp * vz - k * (1 - F.S.tp) * vx))
    (hL1 : gA11 x * vx * F.S.tm - F.toFrame7.gg * vz * (l * (1 - F.S.tm)) < 0 ∨
      gA11 x * vx * F.S.tm - F.toFrame7.gg * vz * (l * (1 - F.S.tm)) < gA11 x * vx) : IsRupert (Finset.univ.image x) := by
  have hP := F.ptC_eq h1 h2 h3 h4
  rw [← hA] at hP
  have a1 := sub_pos.2 F.S.tp_lt
  have a3 := sub_pos.2 F.S.tm_lt
  have a4 := sub_pos.2 F.S.sm_lt
  have hBB := sub_pos.2 hB
  have hD := F.D_pos hr
  have ha1 := F.S.tp_pos
  have ha3 := F.S.tm_pos
  have ha4 := F.S.sm_pos
  have hj : ∀ j' : Fin 7, (∀ jj, j' ≠ c2 jj) → j' = 0 ∨ j' = 6 := by intro j' hj'; fin_cases j' <;> first | exact Or.inl rfl | exact Or.inr rfl | exact absurd rfl (hj' 0) | exact absurd rfl (hj' 1) | exact absurd rfl (hj' 2) | exact absurd rfl (hj' 3) | exact absurd rfl (hj' 4)
  refine F.rim_top hr hP (k := 5) (by norm_num) c2 (-1) (Or.inr rfl) vx vz 2 ?_ ?_ ?_
  · exact cyc_R2 _ _ _ _ _ _ _ ha1 ha3 ha4 hk hl a1 a3 a4 hBB hsa hsb hsc
  · intro j' hj' i
    rcases hj j' hj' with rfl | rfl
    all_goals exact rest_R2 _ _ _ _ _ _ _ ha1 ha3 ha4 hk hl a1 a3 a4 hBB hsa hsb hsc _ (by simp) i
  · intro i hi
    obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
    obtain ⟨d0, d1, d2, d3, d4⟩ := zmod5_sub_one
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;> simp only [Pt_0, Pt_1, Pt_2, Pt_3, Pt_4, Pt_5, Pt_6, c2_0, c2_1, c2_2, c2_3, c2_4, b0, b1, b2, b3, b4, d0, d1, d2, d3, d4] at hi ⊢ <;>
      first | exact absurd rfl hi | skip
    all_goals lexclose

set_option maxHeartbeats 4000000 in
theorem rimR3 (F : Frame02 x) (hr : gA12 x = gA11 x)
    (hA : F.S.tp = F.S.sp) (hB : F.S.tm < F.S.sm) (k l : ℝ) (hk : 0 < k) (hl : 0 < l)
    (h1 : F.S.hp = k * (1 - F.S.tp)) (h2 : F.S.kp = k * (1 - F.S.sp))
    (h3 : F.S.hm = l * (1 - F.S.tm)) (h4 : F.S.km = l * (1 - F.S.sm)) (vx vz : ℝ) (hsa : 0 < -(l * vx - vz)) (hsb : 0 < -(k * vx + vz)) (hsc : 0 < F.S.tp * vz - k * (1 - F.S.tp) * vx)
    (hL2 : 0 < gA11 x * vx * F.S.tp + F.toFrame7.gg * vz * (k * (1 - F.S.tp)) ∨
      0 < gA11 x * vx * F.S.tm - F.toFrame7.gg * vz * (l * (1 - F.S.tm))) : IsRupert (Finset.univ.image x) := by
  have hP := F.ptC_eq h1 h2 h3 h4
  rw [← hA] at hP
  have a1 := sub_pos.2 F.S.tp_lt
  have a3 := sub_pos.2 F.S.tm_lt
  have a4 := sub_pos.2 F.S.sm_lt
  have hBB := sub_pos.2 hB
  have hD := F.D_pos hr
  have ha1 := F.S.tp_pos
  have ha3 := F.S.tm_pos
  have ha4 := F.S.sm_pos
  have hj : ∀ j' : Fin 7, (∀ jj, j' ≠ c3 jj) → j' = 3 := by intro j' hj'; fin_cases j' <;> first | rfl | exact absurd rfl (hj' 0) | exact absurd rfl (hj' 1) | exact absurd rfl (hj' 2) | exact absurd rfl (hj' 3) | exact absurd rfl (hj' 4) | exact absurd rfl (hj' 5)
  refine F.rim_top hr hP (k := 6) (by norm_num) c3 (-1) (Or.inr rfl) vx vz 2 ?_ ?_ ?_
  · exact cyc_R3 _ _ _ _ _ _ _ ha1 ha3 ha4 hk hl a1 a3 a4 hBB hsa hsb hsc
  · intro j' hj' i
    rcases hj j' hj' with rfl
    all_goals exact rest_R3 _ _ _ _ _ _ _ ha1 ha3 ha4 hk hl a1 a3 a4 hBB hsa hsb hsc _ (by simp) i
  · intro i hi
    obtain ⟨b0, b1, b2, b3, b4, b5⟩ := zmod6_add_one
    obtain ⟨d0, d1, d2, d3, d4, d5⟩ := zmod6_sub_one
    rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Pt_0, Pt_1, Pt_2, Pt_3, Pt_4, Pt_5, Pt_6, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, b0, b1, b2, b3, b4, b5, d0, d1, d2, d3, d4, d5] at hi ⊢ <;>
      first | exact absurd rfl hi | skip
    all_goals lexclose


/-! ### The tilt choice: gradient `Γ = (Gx, Gz)`, `w = (Gx p, Gz q)` with `p = 1/A11`, `q = 1/gg`. -/

def FL1 (l tm Gx Gz : ℝ) : Prop := tm * Gx - l * (1 - tm) * Gz < 0 ∨ 0 < Gx + l * Gz
def FL2 (k l tp tm Gx Gz : ℝ) : Prop :=
  0 < tp * Gx + k * (1 - tp) * Gz ∨ 0 < tm * Gx - l * (1 - tm) * Gz

def GR1 (p q k l tp tm Gx Gz : ℝ) : Prop :=
  0 < l * Gx * p - Gz * q ∧ 0 < -(k * Gx * p + Gz * q) ∧ 0 < tp * Gz * q - k * (1 - tp) * Gx * p ∧
    FL1 l tm Gx Gz ∧ FL2 k l tp tm Gx Gz
def GR2 (p q k l tp tm Gx Gz : ℝ) : Prop :=
  0 < l * Gx * p - Gz * q ∧ 0 < -(k * Gx * p + Gz * q) ∧ 0 < -(tp * Gz * q - k * (1 - tp) * Gx * p) ∧
    FL1 l tm Gx Gz
def GR3 (p q k l tp tm Gx Gz : ℝ) : Prop :=
  0 < -(l * Gx * p - Gz * q) ∧ 0 < -(k * Gx * p + Gz * q) ∧ 0 < tp * Gz * q - k * (1 - tp) * Gx * p ∧
    FL2 k l tp tm Gx Gz
def GRany (p q k l tp tm : ℝ) : Prop :=
  ∃ Gx Gz, GR1 p q k l tp tm Gx Gz ∨ GR2 p q k l tp tm Gx Gz ∨ GR3 p q k l tp tm Gx Gz

theorem cs_pos (g11 g22 g12 lam : ℝ) (h22 : 0 < g22) (hd : g12 ^ 2 < g11 * g22) (hg : g12 ≤ 0)
    (hl : 2 * lam * g22 ≤ -g12) : 0 < g11 + lam * g12 := by
  have h1 : 2 * lam * g22 * (-g12) ≤ (-g12) * (-g12) := mul_le_mul_of_nonneg_right hl (by linarith)
  have h2 : 0 < 2 * g22 * (g11 + lam * g12) := by nlinarith [sq_nonneg g12]
  exact pos_of_mul_pos_right h2 (by positivity)

theorem pick_lam (g22 e g13 h : ℝ) (h22 : 0 < g22) (he : e < 0) (h13 : g13 < 0) :
    ∃ lam : ℝ, 0 < lam ∧ 2 * lam * g22 ≤ -e ∧ g13 + lam * h ≠ 0 := by
  have h0 : 0 < -e / (2 * g22) := div_pos (by linarith) (by positivity)
  have h0e : 2 * (-e / (2 * g22)) * g22 = -e := by field_simp
  by_cases hc : g13 + (-e / (2 * g22)) * h = 0
  · refine ⟨-e / (2 * g22) / 2, by positivity, by nlinarith, ?_⟩
    intro hh; nlinarith
  · exact ⟨-e / (2 * g22), h0, h0e.le, hc⟩

theorem caseII (p q k l tp tm lam : ℝ) (hp : 0 < p) (hq : 0 < q) (hk : 0 < k) (hl : 0 < l)
    (ha1 : 0 < tp) (a1 : 0 < 1 - tp) (ha3 : 0 < tm) (a3 : 0 < 1 - tm)
    (hlam : 0 < lam) (hl1 : 2 * lam * (k ^ 2 * p + q) ≤ -(l * k * p - q)) (hg : l * k * p - q < 0)
    (hc : (-l * k * (1 - tp) * p - tp * q) + lam * (-k ^ 2 * (1 - tp) * p + tp * q) ≠ 0) :
    GR1 p q k l tp tm (l + lam * k) (lam - 1) ∨ GR2 p q k l tp tm (l + lam * k) (lam - 1) := by
  have hg22 : 0 < k ^ 2 * p + q := by positivity
  have hsb : 0 < -(k * (l + lam * k) * p + (lam - 1) * q) := by nlinarith
  have hsa : 0 < l * (l + lam * k) * p - (lam - 1) * q := by
    have := cs_pos (l ^ 2 * p + q) (k ^ 2 * p + q) (l * k * p - q) lam hg22
      (by nlinarith [mul_pos (mul_pos hp hq) (sq_pos_of_pos (add_pos hk hl))]) hg.le hl1
    nlinarith
  have hlam2 : lam < 1 / 2 := by
    have : 2 * lam * (k ^ 2 * p + q) < (k ^ 2 * p + q) := by nlinarith [mul_pos (mul_pos hk hl) hp]
    by_contra hh; push_neg at hh; nlinarith
  have hL1 : FL1 l tm (l + lam * k) (lam - 1) := Or.inr (by nlinarith [mul_pos hlam (add_pos hk hl)])
  have hL2 : FL2 k l tp tm (l + lam * k) (lam - 1) := Or.inr (by
    nlinarith [mul_pos hk ha3, mul_pos hl a3, mul_pos (mul_pos hl a3) hlam, mul_pos hlam (mul_pos hk ha3)])
  have hceq : tp * (lam - 1) * q - k * (1 - tp) * (l + lam * k) * p =
      (-l * k * (1 - tp) * p - tp * q) + lam * (-k ^ 2 * (1 - tp) * p + tp * q) := by ring
  rcases lt_or_gt_of_ne hc with h | h
  · right; refine ⟨hsa, hsb, ?_, hL1⟩; nlinarith
  · left; refine ⟨hsa, hsb, ?_, hL1, hL2⟩; nlinarith

theorem caseIII (p q k l tp tm lam : ℝ) (hp : 0 < p) (hq : 0 < q) (hk : 0 < k) (hl : 0 < l)
    (ha1 : 0 < tp) (a1 : 0 < 1 - tp) (ha3 : 0 < tm) (a3 : 0 < 1 - tm)
    (hlam : 0 < lam) (hl1 : 2 * lam * (k ^ 2 * p + q) ≤ -(-k ^ 2 * (1 - tp) * p + tp * q))
    (hg : -k ^ 2 * (1 - tp) * p + tp * q < 0)
    (hc : (-l * k * (1 - tp) * p - tp * q) + lam * (l * k * p - q) ≠ 0) :
    GR1 p q k l tp tm (-k * (1 - tp) + lam * k) (tp + lam) ∨ GR3 p q k l tp tm (-k * (1 - tp) + lam * k) (tp + lam) := by
  have hg22 : 0 < k ^ 2 * p + q := by positivity
  have hsb : 0 < -(k * (-k * (1 - tp) + lam * k) * p + (tp + lam) * q) := by nlinarith
  have hsc : 0 < tp * (tp + lam) * q - k * (1 - tp) * (-k * (1 - tp) + lam * k) * p := by
    have := cs_pos (tp ^ 2 * q + k ^ 2 * (1 - tp) ^ 2 * p) (k ^ 2 * p + q) (-k ^ 2 * (1 - tp) * p + tp * q) lam hg22
      (by nlinarith [mul_pos (mul_pos hp hq) (sq_pos_of_pos hk)]) hg.le hl1
    nlinarith
  have hlam2 : lam < (1 - tp) / 2 := by
    have : 2 * lam * (k ^ 2 * p + q) < (1 - tp) * (k ^ 2 * p + q) := by nlinarith [mul_pos a1 hq, mul_pos ha1 hq]
    by_contra hh; push_neg at hh; nlinarith
  have hL2 : FL2 k l tp tm (-k * (1 - tp) + lam * k) (tp + lam) := Or.inl (by nlinarith [mul_pos hlam hk])
  have hL1 : FL1 l tm (-k * (1 - tp) + lam * k) (tp + lam) := Or.inl (by
    nlinarith [mul_pos (mul_pos hk ha3) (sub_pos.2 hlam2), mul_pos (mul_pos hl a3) hlam,
      mul_pos (mul_pos hl ha1) a3, mul_pos (mul_pos hk a1) ha3])
  have hceq : l * (-k * (1 - tp) + lam * k) * p - (tp + lam) * q =
      (-l * k * (1 - tp) * p - tp * q) + lam * (l * k * p - q) := by ring
  rcases lt_or_gt_of_ne hc with h | h
  · right; refine ⟨?_, hsb, hsc, hL2⟩; nlinarith
  · left; refine ⟨?_, hsb, hsc, hL1, hL2⟩; nlinarith

theorem caseIV (p q k l tp tm : ℝ) (hp : 0 < p) (hq : 0 < q) (hk : 0 < k) (hl : 0 < l)
    (ha1 : 0 < tp) (a1 : 0 < 1 - tp) (ha3 : 0 < tm) (a3 : 0 < 1 - tm)
    (e1 : q = l * k * p) (e2 : l * tp = k * (1 - tp)) (hρ : k * tm - l * (1 - tm) ≠ 0) :
    GRany p q k l tp tm := by
  refine ⟨-l * (1 - tm) - k, -tm - 1, ?_⟩
  have hsb : 0 < -(k * (-l * (1 - tm) - k) * p + (-tm - 1) * q) := by
    rw [e1]; nlinarith [mul_pos (mul_pos hk hp) hl, mul_pos (mul_pos hk hp) hk, mul_pos (mul_pos (mul_pos hk hp) hl) ha3,
      mul_pos (mul_pos (mul_pos hk hp) hl) a3]
  have ea : l * (-l * (1 - tm) - k) * p - (-tm - 1) * q = l * p * (k * tm - l * (1 - tm)) := by rw [e1]; ring
  have ec : tp * (-tm - 1) * q - k * (1 - tp) * (-l * (1 - tm) - k) * p =
      -(tp * (l * p * (k * tm - l * (1 - tm)))) := by rw [e1, ← e2]; ring
  rcases lt_or_gt_of_ne hρ with h | h
  · right; right
    refine ⟨?_, hsb, ?_, Or.inr ?_⟩
    · rw [ea]; nlinarith [mul_pos hl hp]
    · rw [ec]; nlinarith [mul_pos hl hp, mul_pos (mul_pos hl hp) ha1]
    · nlinarith
  · right; left
    refine ⟨?_, hsb, ?_, Or.inl ?_⟩
    · rw [ea]; exact mul_pos (mul_pos hl hp) h
    · rw [ec]; nlinarith [mul_pos (mul_pos hl hp) ha1, mul_pos (mul_pos (mul_pos hl hp) ha1) h]
    · nlinarith

theorem exists_GR (p q k l tp tm : ℝ) (hp : 0 < p) (hq : 0 < q) (hk : 0 < k) (hl : 0 < l)
    (ha1 : 0 < tp) (a1 : 0 < 1 - tp) (ha3 : 0 < tm) (a3 : 0 < 1 - tm)
    (hd : l * tp - k * (1 - tp) ≤ 0)
    (hnr : ¬ (tm = 1 - tp ∧ l * (1 - tm) = k * (1 - tp) ∧ q = l * k * p)) :
    GRany p q k l tp tm := by
  have hg22 : 0 < k ^ 2 * p + q := by positivity
  have h13 : -l * k * (1 - tp) * p - tp * q < 0 := by
    nlinarith [mul_pos (mul_pos (mul_pos hl hk) a1) hp, mul_pos ha1 hq]
  by_cases h12 : l * k * p - q < 0
  · obtain ⟨lam, hlam, hl1, hc⟩ := pick_lam (k ^ 2 * p + q) (l * k * p - q) _ (-k ^ 2 * (1 - tp) * p + tp * q) hg22 h12 h13
    rcases caseII p q k l tp tm lam hp hq hk hl ha1 a1 ha3 a3 hlam (by linarith) h12 hc with h | h
    · exact ⟨_, _, Or.inl h⟩
    · exact ⟨_, _, Or.inr (Or.inl h)⟩
  · push_neg at h12
    by_cases h23 : -k ^ 2 * (1 - tp) * p + tp * q < 0
    · obtain ⟨lam, hlam, hl1, hc⟩ := pick_lam (k ^ 2 * p + q) (-k ^ 2 * (1 - tp) * p + tp * q) _ (l * k * p - q) hg22 h23 h13
      rcases caseIII p q k l tp tm lam hp hq hk hl ha1 a1 ha3 a3 hlam hl1 h23 hc with h | h
      · exact ⟨_, _, Or.inl h⟩
      · exact ⟨_, _, Or.inr (Or.inr h)⟩
    · push_neg at h23
      -- right trapezoid
      have kp : 0 < k * p := mul_pos hk hp
      have s1 : k * p * (k * (1 - tp) - tp * l) ≤ 0 := by nlinarith [mul_nonneg ha1.le h12]
      have s2 : k * (1 - tp) - tp * l ≤ 0 := by
        by_contra hh; push_neg at hh; nlinarith [mul_pos kp hh]
      have e2 : l * tp = k * (1 - tp) := by linarith
      have e1 : q = l * k * p := by
        have hh : k * p * (l * tp) = k * p * (k * (1 - tp)) := by rw [e2]
        have h5 : 0 ≤ tp * (q - l * k * p) := by nlinarith
        have h6 := (mul_nonneg_iff_of_pos_left ha1).1 h5
        linarith
      refine caseIV p q k l tp tm hp hq hk hl ha1 a1 ha3 a3 e1 e2 ?_
      intro hρ
      apply hnr
      have h7 : (tm - (1 - tp)) * (k * l) = 0 := by
        linear_combination (k * tm) * e2 + (k * (1 - tp)) * hρ
      have hkl : k * l ≠ 0 := (mul_pos hk hl).ne'
      have h8 := (mul_eq_zero.mp h7).resolve_right hkl
      refine ⟨by linarith, by rw [show tm = 1 - tp by linarith] at hρ ⊢; linarith, e1⟩

theorem conv_L1 (A Gg p q l tm Gx Gz : ℝ) (a3 : 0 < 1 - tm) (hAp : A * p = 1) (hGq : Gg * q = 1)
    (h : FL1 l tm Gx Gz) :
    A * (Gx * p) * tm - Gg * (Gz * q) * (l * (1 - tm)) < 0 ∨
      A * (Gx * p) * tm - Gg * (Gz * q) * (l * (1 - tm)) < A * (Gx * p) := by
  have e1 : A * (Gx * p) = Gx := by linear_combination Gx * hAp
  have e2 : Gg * (Gz * q) = Gz := by linear_combination Gz * hGq
  rw [e1, e2]
  rcases h with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by nlinarith [mul_pos a3 h])

theorem conv_L2 (A Gg p q k l tp tm Gx Gz : ℝ) (hAp : A * p = 1) (hGq : Gg * q = 1)
    (h : FL2 k l tp tm Gx Gz) :
    0 < A * (Gx * p) * tp + Gg * (Gz * q) * (k * (1 - tp)) ∨
      0 < A * (Gx * p) * tm - Gg * (Gz * q) * (l * (1 - tm)) := by
  have e1 : A * (Gx * p) = Gx := by linear_combination Gx * hAp
  have e2 : Gg * (Gz * q) = Gz := by linear_combination Gz * hGq
  rw [e1, e2]
  rcases h with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

theorem rect_of_data (F : Frame02 x) (h1 : F.S.tm = 1 - F.S.tp) (h2 : F.S.hm = F.S.hp)
    (h3 : F.toFrame7.gg * (F.S.hp * F.S.hm) = gA11 x * (F.S.tp * F.S.tm)) : F1Rect x := by
  have hue := F.inner_u1_e
  have heu : ⟪F.e, x 3 - x 2⟫ = 0 := by rw [real_inner_comm]; exact hue
  have h3' : ⟪F.e, F.e⟫ * (F.S.hp * F.S.hm) = ⟪x 3 - x 2, x 3 - x 2⟫ * (F.S.tp * F.S.tm) := h3
  set u := x 3 - x 2 with hu_def
  set a := ⟪u, u⟫ with ha_def
  set g := ⟪F.e, F.e⟫ with hg_def
  have e0 : x 0 - x 2 = F.S.tp • u + F.S.hp • F.e := by rw [F.x0_eq]; abel
  have e5 : x 5 - x 2 = F.S.tm • u - F.S.hm • F.e := by rw [F.x5_eq]; abel
  refine ⟨?_, ?_⟩
  · rw [e0, e5, h1, h2]; module
  · rw [e0, e5]
    simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      inner_smul_left, inner_smul_right, hue, heu, RCLike.conj_to_real, ← ha_def, ← hg_def]
    linarith

theorem right_V1B5_pf (F : Frame02 x) (hr : gA12 x = gA11 x)
    (hA : F.S.tp = F.S.sp) (hB : F.S.tm < F.S.sm) (hRect : ¬ F1Rect x) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨k, l, hk, hl, h1, h2, h3, h4⟩ := exists_kl F.S
  by_cases hd : 0 < l * F.S.tp - k * (1 - F.S.tp)
  · exact F.fnB_I hr hA hB k l hk hl h1 h2 h3 h4 hd
  push_neg at hd
  have a1 := sub_pos.2 F.S.tp_lt
  have a3 := sub_pos.2 F.S.tm_lt
  have ha : 0 < gA11 x := hr ▸ F.A12_pos
  have hg := F.gg_pos
  have hAp : gA11 x * (gA11 x)⁻¹ = 1 := mul_inv_cancel₀ ha.ne'
  have hGq : F.toFrame7.gg * (F.toFrame7.gg)⁻¹ = 1 := mul_inv_cancel₀ hg.ne'
  have hnr : ¬ (F.S.tm = 1 - F.S.tp ∧ l * (1 - F.S.tm) = k * (1 - F.S.tp) ∧
      (F.toFrame7.gg)⁻¹ = l * k * (gA11 x)⁻¹) := by
    rintro ⟨e1, e2, e3⟩
    apply hRect
    have hA' : gA11 x = l * k * F.toFrame7.gg := by
      have h5 : F.toFrame7.gg * (l * k * (gA11 x)⁻¹) = 1 := by rw [← e3]; exact hGq
      linear_combination (-gA11 x) * h5 + (l * k * F.toFrame7.gg) * hAp
    refine F.rect_of_data e1 (by rw [h3, h1]; exact e2) ?_
    rw [h1, h3, e1, hA']; ring
  obtain ⟨Gx, Gz, hG⟩ := exists_GR (gA11 x)⁻¹ (F.toFrame7.gg)⁻¹ k l F.S.tp F.S.tm (inv_pos.2 ha) (inv_pos.2 hg)
    hk hl F.S.tp_pos a1 F.S.tm_pos a3 hd hnr
  rcases hG with ⟨ha1, hb1, hc1, hL1, hL2⟩ | ⟨ha1, hb1, hc1, hL1⟩ | ⟨ha1, hb1, hc1, hL2⟩
  · exact rimR1 F hr hA hB k l hk hl h1 h2 h3 h4 (Gx * (gA11 x)⁻¹) (Gz * (F.toFrame7.gg)⁻¹)
      (by linarith) (by linarith) (by linarith) (conv_L1 _ _ _ _ _ _ _ _ a3 hAp hGq hL1) (conv_L2 _ _ _ _ _ _ _ _ _ _ hAp hGq hL2)
  · exact rimR2 F hr hA hB k l hk hl h1 h2 h3 h4 (Gx * (gA11 x)⁻¹) (Gz * (F.toFrame7.gg)⁻¹)
      (by linarith) (by linarith) (by linarith) (conv_L1 _ _ _ _ _ _ _ _ a3 hAp hGq hL1)
  · exact rimR3 F hr hA hB k l hk hl h1 h2 h3 h4 (Gx * (gA11 x)⁻¹) (Gz * (F.toFrame7.gg)⁻¹)
      (by linarith) (by linarith) (by linarith) (conv_L2 _ _ _ _ _ _ _ _ _ _ hAp hGq hL2)

end Frame02
end Minimality.CaseC18
