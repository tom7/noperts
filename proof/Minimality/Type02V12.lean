module

public import Minimality.Type02FN

@[expose] public section

/-! # sp02 Lean, group FN (iv)(a): `right_V12_pf` (both far edges vertical, doubles 6, 4, 1 over F1 = (5,3,0,2)).

Covectors of the sides of `F1` against the screen tilt `w = (vx, vz)`:
`a = l vx - vz`, `b = k vx + vz`, `c = -k(1-tp) vx + tp vz`, `d = -l(1-tm) vx - tm vz`.
Rims (all with `a < 0 < c`): A `(b<0, d<0)` rim `0,2,6,4,1`; B `(b>0, d<0)` rim `2,6,4,3,0`;
C `(b<0, d>0)` rim `2,5,6,4,1,0`.  (The other cells of the paper's table never occur for the tilts of the tree.) -/

namespace Minimality.CaseC18
open Finset Filter Minimality.CaseC09
open scoped RealInnerProductSpace Topology

namespace Frame02
variable {x : Fin 7 → ℝ³}

def vA : ZMod 5 → Fin 7 := ![0, 2, 6, 4, 1]
def vB : ZMod 5 → Fin 7 := ![2, 6, 4, 3, 0]
def vC : ZMod 6 → Fin 7 := ![2, 5, 6, 4, 1, 0]
theorem vA_0 : vA 0 = 0 := rfl
theorem vA_1 : vA 1 = 2 := rfl
theorem vA_2 : vA 2 = 6 := rfl
theorem vA_3 : vA 3 = 4 := rfl
theorem vA_4 : vA 4 = 1 := rfl
theorem vB_0 : vB 0 = 2 := rfl
theorem vB_1 : vB 1 = 6 := rfl
theorem vB_2 : vB 2 = 4 := rfl
theorem vB_3 : vB 3 = 3 := rfl
theorem vB_4 : vB 4 = 0 := rfl
theorem vC_0 : vC 0 = 2 := rfl
theorem vC_1 : vC 1 = 5 := rfl
theorem vC_2 : vC 2 = 6 := rfl
theorem vC_3 : vC 3 = 4 := rfl
theorem vC_4 : vC 4 = 1 := rfl
theorem vC_5 : vC 5 = 0 := rfl

section rows
variable (tp tm k l vx vz : ℝ) (ha1 : 0 < tp) (ha3 : 0 < tm) (hk : 0 < k) (hl : 0 < l)
  (a1 : 0 < 1 - tp) (a3 : 0 < 1 - tm)
  (pa : 0 < vz - l * vx) (pc : 0 < tp * vz - k * (1 - tp) * vx)

/-- the tie-row hint products and the four screen areas -/
macro "v12hints" pb:term "," pd:term : tactic => `(tactic| (
  have hU1 : 0 < k * tm * (1 - tp) + l * tp * (1 - tm) := by positivity
  have hU2 : 0 < l * (1 - tm) := by positivity
  have hU3 : 0 < (k + l) * (1 - tm) * (1 - tp) := by positivity
  have hU4 : 0 < k * (1 - tp) := by positivity
  have f1 := mul_pos ha1 pa; have f2 := mul_pos a1 pa; have f3 := mul_pos ha3 pa; have f4 := mul_pos a3 pa
  have f5 := mul_pos (mul_pos ha1 a1) pa; have f6 := mul_pos (mul_pos ha3 a3) pa; have f7 := mul_pos (mul_pos ha1 a3) pa
  have g1 := mul_pos ha1 $pb; have g2 := mul_pos a1 $pb; have g3 := mul_pos ha3 $pb; have g4 := mul_pos a3 $pb
  have g5 := mul_pos (mul_pos ha1 a1) $pb; have g6 := mul_pos (mul_pos ha3 a3) $pb; have g7 := mul_pos (mul_pos ha1 a3) $pb
  have h1 := mul_pos ha1 pc; have h2 := mul_pos a1 pc; have h3 := mul_pos ha3 pc; have h4 := mul_pos a3 pc
  have i1 := mul_pos ha1 $pd; have i2 := mul_pos a1 $pd; have i3 := mul_pos ha3 $pd; have i4 := mul_pos a3 $pd))

set_option maxHeartbeats 4000000 in
include ha1 ha3 hk hl a1 a3 pa pc in
theorem v12_cycA (pb : 0 < -(k * vx + vz)) (pd : 0 < l * (1 - tm) * vx + tm * vz) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST (-1) ⟨-1, 1, 0⟩ ⟨vx, 0, vz⟩
        ((Pt tp tp tm tm k l (vA (i + 1))).sub (Pt tp tp tm tm k l (vA i)))
        ((Pt tp tp tm tm k l (vA j)).sub (Pt tp tp tm tm k l (vA i))) := by
  v12hints pb, pd
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i j h1 h2
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl h1 | exact absurd (by decide) h2 | skip
  all_goals (
    simp only [CaseC09.ST, Dc, C3.sub, Pt_0, Pt_1, Pt_2, Pt_3, Pt_4, Pt_5, Pt_6, b0, b1, b2, b3, b4,
      vA_0, vA_1, vA_2, vA_3, vA_4]
    first
    | (left; linarith)
    | (right; constructor
       · ring
       · linarith))

set_option maxHeartbeats 4000000 in
include ha1 ha3 hk hl a1 a3 pa pc in
theorem v12_restA (pb : 0 < -(k * vx + vz)) (pd : 0 < l * (1 - tm) * vx + tm * vz)
    (j' : Fin 7) (hj : j' = 3 ∨ j' = 5) :
    ∀ i : ZMod 5,
      ST (-1) ⟨-1, 1, 0⟩ ⟨vx, 0, vz⟩
        ((Pt tp tp tm tm k l (vA (i + 1))).sub (Pt tp tp tm tm k l (vA i)))
        ((Pt tp tp tm tm k l j').sub (Pt tp tp tm tm k l (vA i))) := by
  v12hints pb, pd
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases hj with rfl | rfl <;>
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  (simp only [CaseC09.ST, Dc, C3.sub, Pt_0, Pt_1, Pt_2, Pt_3, Pt_4, Pt_5, Pt_6, b0, b1, b2, b3, b4,
      vA_0, vA_1, vA_2, vA_3, vA_4]
   first
   | (left; linarith)
   | (right; constructor
      · ring
      · linarith))

set_option maxHeartbeats 4000000 in
include ha1 ha3 hk hl a1 a3 pa pc in
theorem v12_cycB (pb : 0 < k * vx + vz) (pd : 0 < l * (1 - tm) * vx + tm * vz) (hvz : 0 < vz) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST (-1) ⟨-1, 1, 0⟩ ⟨vx, 0, vz⟩
        ((Pt tp tp tm tm k l (vB (i + 1))).sub (Pt tp tp tm tm k l (vB i)))
        ((Pt tp tp tm tm k l (vB j)).sub (Pt tp tp tm tm k l (vB i))) := by
  v12hints pb, pd
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i j h1 h2
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl h1 | exact absurd (by decide) h2 | skip
  all_goals (
    simp only [CaseC09.ST, Dc, C3.sub, Pt_0, Pt_1, Pt_2, Pt_3, Pt_4, Pt_5, Pt_6, b0, b1, b2, b3, b4,
      vB_0, vB_1, vB_2, vB_3, vB_4]
    first
    | (left; linarith)
    | (right; constructor
       · ring
       · linarith))

set_option maxHeartbeats 4000000 in
include ha1 ha3 hk hl a1 a3 pa pc in
theorem v12_restB (pb : 0 < k * vx + vz) (pd : 0 < l * (1 - tm) * vx + tm * vz) (hvz : 0 < vz)
    (j' : Fin 7) (hj : j' = 1 ∨ j' = 5) :
    ∀ i : ZMod 5,
      ST (-1) ⟨-1, 1, 0⟩ ⟨vx, 0, vz⟩
        ((Pt tp tp tm tm k l (vB (i + 1))).sub (Pt tp tp tm tm k l (vB i)))
        ((Pt tp tp tm tm k l j').sub (Pt tp tp tm tm k l (vB i))) := by
  v12hints pb, pd
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases hj with rfl | rfl <;>
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  (simp only [CaseC09.ST, Dc, C3.sub, Pt_0, Pt_1, Pt_2, Pt_3, Pt_4, Pt_5, Pt_6, b0, b1, b2, b3, b4,
      vB_0, vB_1, vB_2, vB_3, vB_4]
   first
   | (left; linarith)
   | (right; constructor
      · ring
      · linarith))

set_option maxHeartbeats 4000000 in
include ha1 ha3 hk hl a1 a3 pa pc in
theorem v12_cycC (pb : 0 < -(k * vx + vz)) (pd : 0 < -(l * (1 - tm) * vx) - tm * vz) :
    ∀ i j : ZMod 6, j ≠ i → j ≠ i + 1 →
      ST (-1) ⟨-1, 1, 0⟩ ⟨vx, 0, vz⟩
        ((Pt tp tp tm tm k l (vC (i + 1))).sub (Pt tp tp tm tm k l (vC i)))
        ((Pt tp tp tm tm k l (vC j)).sub (Pt tp tp tm tm k l (vC i))) := by
  v12hints pb, pd
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := zmod6_add_one
  intro i j h1 h2
  rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl h1 | exact absurd (by decide) h2 | skip
  all_goals (
    simp only [CaseC09.ST, Dc, C3.sub, Pt_0, Pt_1, Pt_2, Pt_3, Pt_4, Pt_5, Pt_6, b0, b1, b2, b3, b4, b5,
      vC_0, vC_1, vC_2, vC_3, vC_4, vC_5]
    first
    | (left; linarith)
    | (right; constructor
       · ring
       · linarith))

set_option maxHeartbeats 4000000 in
include ha1 ha3 hk hl a1 a3 pa pc in
theorem v12_restC (pb : 0 < -(k * vx + vz)) (pd : 0 < -(l * (1 - tm) * vx) - tm * vz) :
    ∀ i : ZMod 6,
      ST (-1) ⟨-1, 1, 0⟩ ⟨vx, 0, vz⟩
        ((Pt tp tp tm tm k l (vC (i + 1))).sub (Pt tp tp tm tm k l (vC i)))
        ((Pt tp tp tm tm k l 3).sub (Pt tp tp tm tm k l (vC i))) := by
  v12hints pb, pd
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := zmod6_add_one
  intro i
  rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
  (simp only [CaseC09.ST, Dc, C3.sub, Pt_0, Pt_1, Pt_2, Pt_3, Pt_4, Pt_5, Pt_6, b0, b1, b2, b3, b4, b5,
      vC_0, vC_1, vC_2, vC_3, vC_4, vC_5]
   first
   | (left; linarith)
   | (right; constructor
      · ring
      · linarith))
end rows

theorem zmod5_sub_one' : (0 : ZMod 5) - 1 = 4 ∧ (1 : ZMod 5) - 1 = 0 ∧ (2 : ZMod 5) - 1 = 1 ∧
    (3 : ZMod 5) - 1 = 2 ∧ (4 : ZMod 5) - 1 = 3 := by decide

/-- depth predicate: every index except `t` has a strictly larger neighbour -/
def QtV {k : ℕ} (t : ZMod k) (z : ZMod k → ℝ) : Prop :=
  ∀ i, i ≠ t → z i < z (i - 1) ∨ z i < z (i + 1)

theorem QtV_open {k : ℕ} [NeZero k] (t : ZMod k) : IsOpen {z : ZMod k → ℝ | QtV t z} := by
  have hlt : ∀ i j : ZMod k, IsOpen {z : ZMod k → ℝ | z i < z j} := fun i j =>
    isOpen_lt (continuous_apply i) (continuous_apply j)
  have : {z : ZMod k → ℝ | QtV t z} = ⋂ i : ZMod k, {z | i ≠ t → z i < z (i - 1) ∨ z i < z (i + 1)} := by
    ext z; simp [QtV]
  rw [this]
  refine isOpen_iInter_of_finite fun i => ?_
  by_cases h : i = t
  · simp [h]
  · simp only [h, ne_eq, not_false_eq_true, forall_const]
    exact (hlt _ _).union (hlt _ _)

theorem QtV_eventually {k : ℕ} [NeZero k] (t : ZMod k) {z w : ZMod k → ℝ}
    (h : ∀ i, i ≠ t → (z i < z (i - 1) ∨ (z i = z (i - 1) ∧ w i < w (i - 1))) ∨
      (z i < z (i + 1) ∨ (z i = z (i + 1) ∧ w i < w (i + 1)))) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), QtV t fun i => z i + s * w i := by
  unfold QtV
  refine Filter.eventually_all.2 fun i => ?_
  by_cases hi : i = t
  · exact Filter.Eventually.of_forall fun s h' => absurd hi h'
  · rcases h i hi with h1 | h1
    · filter_upwards [ev_lt h1] with s hs _ using Or.inl hs
    · filter_upwards [ev_lt h1] with s hs _ using Or.inr hs

variable (F : Frame02 x)

/-- the rim bridge with the depth predicate `QtV` (top vertex at index `t`). -/
theorem v12_rimT {k : ℕ} [NeZero k] (hk3 : 3 ≤ k) (c : ZMod k → Fin 7) (v : C3)
    (hcyc : ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 →
      ST (-1) ⟨-1, 1, 0⟩ v ((F.toFrame7.ptC (c (i + 1))).sub (F.toFrame7.ptC (c i)))
        ((F.toFrame7.ptC (c j)).sub (F.toFrame7.ptC (c i))))
    (hrest : ∀ j' : Fin 7, (∀ jj, j' ≠ c jj) → ∀ i : ZMod k,
      ST (-1) ⟨-1, 1, 0⟩ v ((F.toFrame7.ptC (c (i + 1))).sub (F.toFrame7.ptC (c i)))
        ((F.toFrame7.ptC j').sub (F.toFrame7.ptC (c i))))
    (t : ZMod k)
    (hev : ∀ i, i ≠ t →
      (F.toFrame7.GG (F.toFrame7.ptC (c i)) ⟨-1, 1, 0⟩ < F.toFrame7.GG (F.toFrame7.ptC (c (i - 1))) ⟨-1, 1, 0⟩ ∨
        (F.toFrame7.GG (F.toFrame7.ptC (c i)) ⟨-1, 1, 0⟩ = F.toFrame7.GG (F.toFrame7.ptC (c (i - 1))) ⟨-1, 1, 0⟩ ∧
          F.toFrame7.GG (F.toFrame7.ptC (c i)) v < F.toFrame7.GG (F.toFrame7.ptC (c (i - 1))) v)) ∨
      (F.toFrame7.GG (F.toFrame7.ptC (c i)) ⟨-1, 1, 0⟩ < F.toFrame7.GG (F.toFrame7.ptC (c (i + 1))) ⟨-1, 1, 0⟩ ∨
        (F.toFrame7.GG (F.toFrame7.ptC (c i)) ⟨-1, 1, 0⟩ = F.toFrame7.GG (F.toFrame7.ptC (c (i + 1))) ⟨-1, 1, 0⟩ ∧
          F.toFrame7.GG (F.toFrame7.ptC (c i)) v < F.toFrame7.GG (F.toFrame7.ptC (c (i + 1))) v))) :
    IsRupert (Finset.univ.image x) := by
  refine F.toFrame7.rupert_rim hk3 c (-1) (Or.inr rfl) ⟨-1, 1, 0⟩ v (Or.inl (by norm_num)) hcyc hrest
    (QtV t) (QtV_open t) ?_ ?_ ?_ ?_
  · intro z a ha h i hi
    rcases h i hi with h1 | h1
    · exact Or.inl (by simpa using mul_lt_mul_of_pos_left h1 ha)
    · exact Or.inr (by simpa using mul_lt_mul_of_pos_left h1 ha)
  · intro z a h i hi
    rcases h i hi with h1 | h1
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · exact QtV_eventually t hev
  · intro z hz hq
    exact isCyclicUnimodal_of_top (by have := NeZero.pos k; omega) hz t hq


theorem v12_hjA : ∀ j' : Fin 7, (∀ jj : ZMod 5, j' ≠ vA jj) → j' = 3 ∨ j' = 5 := by decide
theorem v12_hjB : ∀ j' : Fin 7, (∀ jj : ZMod 5, j' ≠ vB jj) → j' = 1 ∨ j' = 5 := by decide
theorem v12_hjC : ∀ j' : Fin 7, (∀ jj : ZMod 6, j' ≠ vC jj) → j' = 3 := by decide

/-- Rim A: `a < 0, b < 0, c > 0, d < 0`. -/
theorem v12_mA (hr : gA12 x = gA11 x) (hA : F.S.tp = F.S.sp) (hB : F.S.tm = F.S.sm) (k l : ℝ)
    (hk : 0 < k) (hl : 0 < l)
    (h1 : F.S.hp = k * (1 - F.S.tp)) (h2 : F.S.kp = k * (1 - F.S.sp))
    (h3 : F.S.hm = l * (1 - F.S.tm)) (h4 : F.S.km = l * (1 - F.S.sm)) (vx vz : ℝ)
    (pa : 0 < vz - l * vx) (pb : 0 < -(k * vx + vz)) (pc : 0 < F.S.tp * vz - k * (1 - F.S.tp) * vx)
    (pd : 0 < l * (1 - F.S.tm) * vx + F.S.tm * vz) : IsRupert (Finset.univ.image x) := by
  have hP := F.ptC_eq h1 h2 h3 h4
  rw [← hA, ← hB] at hP
  have a1 := sub_pos.2 F.S.tp_lt
  have a3 := sub_pos.2 F.S.tm_lt
  have hD := F.D_pos hr
  refine F.toFrame7.rupert_rim_rob (k := 5) (by norm_num) vA (-1) (Or.inr rfl) ⟨-1, 1, 0⟩ ⟨vx, 0, vz⟩
    (Or.inl (by norm_num)) ?_ ?_ ?_
  · intro i j hi hj
    rw [hP]
    exact v12_cycA _ _ _ _ _ _ F.S.tp_pos F.S.tm_pos hk hl a1 a3 pa pc pb pd i j hi hj
  · intro j' hj' i
    rw [hP]
    exact v12_restA _ _ _ _ _ _ F.S.tp_pos F.S.tm_pos hk hl a1 a3 pa pc pb pd j' (v12_hjA j' hj') i
  · have e : (fun i : ZMod 5 => F.toFrame7.GG (F.toFrame7.ptC (vA i)) ⟨-1, 1, 0⟩) =
        fun i : ZMod 5 => ![0, 0, F.S.tm * (gA22 x - gA12 x), gA22 x - gA12 x, F.S.tp * (gA22 x - gA12 x)] i := by
      funext i
      rw [F.GG_u hr, hP]
      rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
        simp [vA_0, vA_1, vA_2, vA_3, vA_4, Pt_0, Pt_1, Pt_2, Pt_3, Pt_4, Pt_5, Pt_6]
    rw [e]
    exact rob5 (mul_pos F.S.tm_pos hD) (by nlinarith [mul_pos a3 hD]) (by nlinarith [mul_pos a1 hD])
      (mul_pos F.S.tp_pos hD)


theorem zmod6_sub_one_V : (0 : ZMod 6) - 1 = 5 ∧ (1 : ZMod 6) - 1 = 0 ∧ (2 : ZMod 6) - 1 = 1 ∧
    (3 : ZMod 6) - 1 = 2 ∧ (4 : ZMod 6) - 1 = 3 ∧ (5 : ZMod 6) - 1 = 4 := by decide

/-- Rim B: `a < 0, b > 0, c > 0, d < 0`, and `φ(0) < φ(3) ∨ φ(0) < φ(2)` (`φ(P) = A11 vx (x+y) + g vz z`). -/
theorem v12_mB (hr : gA12 x = gA11 x) (hA : F.S.tp = F.S.sp) (hB : F.S.tm = F.S.sm) (k l : ℝ)
    (hk : 0 < k) (hl : 0 < l)
    (h1 : F.S.hp = k * (1 - F.S.tp)) (h2 : F.S.kp = k * (1 - F.S.sp))
    (h3 : F.S.hm = l * (1 - F.S.tm)) (h4 : F.S.km = l * (1 - F.S.sm)) (vx vz : ℝ)
    (pa : 0 < vz - l * vx) (pb : 0 < k * vx + vz) (pc : 0 < F.S.tp * vz - k * (1 - F.S.tp) * vx)
    (pd : 0 < l * (1 - F.S.tm) * vx + F.S.tm * vz)
    (hR : gA11 x * (vx * F.S.tp) + F.toFrame7.gg * (vz * (k * (1 - F.S.tp))) < gA11 x * vx ∨
      gA11 x * (vx * F.S.tp) + F.toFrame7.gg * (vz * (k * (1 - F.S.tp))) < 0) :
    IsRupert (Finset.univ.image x) := by
  have hP := F.ptC_eq h1 h2 h3 h4
  rw [← hA, ← hB] at hP
  have a1 := sub_pos.2 F.S.tp_lt
  have a3 := sub_pos.2 F.S.tm_lt
  have hD := F.D_pos hr
  have hvz : 0 < vz := by
    have : 0 < (k + l) * vz := by nlinarith [mul_pos hl pb, mul_pos hk pa]
    exact (mul_pos_iff_of_pos_left (add_pos hk hl)).1 this
  refine F.v12_rimT (by norm_num) vB ⟨vx, 0, vz⟩ ?_ ?_ 2 ?_
  · intro i j hi hj
    rw [hP]
    exact v12_cycB _ _ _ _ _ _ F.S.tp_pos F.S.tm_pos hk hl a1 a3 pa pc pb pd hvz i j hi hj
  · intro j' hj' i
    rw [hP]
    exact v12_restB _ _ _ _ _ _ F.S.tp_pos F.S.tm_pos hk hl a1 a3 pa pc pb pd hvz j' (v12_hjB j' hj') i
  · obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
    obtain ⟨c0, c1, c2, c3, c4⟩ := zmod5_sub_one'
    intro i hi
    simp only [F.GG_u hr, GG_v F hr, hP]
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [b0, b1, b2, b3, b4, c0, c1, c2, c3, c4, vB_0, vB_1, vB_2, vB_3, vB_4, Pt_0, Pt_1, Pt_2, Pt_3, Pt_4, Pt_5, Pt_6]
      right; left; have := mul_pos F.S.tm_pos hD; linarith
    · simp only [b0, b1, b2, b3, b4, c0, c1, c2, c3, c4, vB_0, vB_1, vB_2, vB_3, vB_4, Pt_0, Pt_1, Pt_2, Pt_3, Pt_4, Pt_5, Pt_6]
      right; left; nlinarith [mul_pos a3 hD]
    · exact absurd rfl hi
    · simp only [b0, b1, b2, b3, b4, c0, c1, c2, c3, c4, vB_0, vB_1, vB_2, vB_3, vB_4, Pt_0, Pt_1, Pt_2, Pt_3, Pt_4, Pt_5, Pt_6]
      left; left; linarith
    · simp only [b0, b1, b2, b3, b4, c0, c1, c2, c3, c4, vB_0, vB_1, vB_2, vB_3, vB_4, Pt_0, Pt_1, Pt_2, Pt_3, Pt_4, Pt_5, Pt_6]
      rcases hR with h | h
      · left; right; exact ⟨trivial, by linarith⟩
      · right; right; exact ⟨trivial, by linarith⟩

/-- Rim C: `a < 0, b < 0, c > 0, d > 0`, and `φ(2) < φ(0) ∨ φ(2) < φ(5)`. -/
theorem v12_mC (hr : gA12 x = gA11 x) (hA : F.S.tp = F.S.sp) (hB : F.S.tm = F.S.sm) (k l : ℝ)
    (hk : 0 < k) (hl : 0 < l)
    (h1 : F.S.hp = k * (1 - F.S.tp)) (h2 : F.S.kp = k * (1 - F.S.sp))
    (h3 : F.S.hm = l * (1 - F.S.tm)) (h4 : F.S.km = l * (1 - F.S.sm)) (vx vz : ℝ)
    (pa : 0 < vz - l * vx) (pb : 0 < -(k * vx + vz)) (pc : 0 < F.S.tp * vz - k * (1 - F.S.tp) * vx)
    (pd : 0 < -(l * (1 - F.S.tm) * vx) - F.S.tm * vz)
    (hR : 0 < gA11 x * (vx * F.S.tp) + F.toFrame7.gg * (vz * (k * (1 - F.S.tp))) ∨
      0 < gA11 x * (vx * F.S.tm) + F.toFrame7.gg * (vz * -(l * (1 - F.S.tm)))) :
    IsRupert (Finset.univ.image x) := by
  have hP := F.ptC_eq h1 h2 h3 h4
  rw [← hA, ← hB] at hP
  have a1 := sub_pos.2 F.S.tp_lt
  have a3 := sub_pos.2 F.S.tm_lt
  have hD := F.D_pos hr
  refine F.v12_rimT (by norm_num) vC ⟨vx, 0, vz⟩ ?_ ?_ 3 ?_
  · intro i j hi hj
    rw [hP]
    exact v12_cycC _ _ _ _ _ _ F.S.tp_pos F.S.tm_pos hk hl a1 a3 pa pc pb pd i j hi hj
  · intro j' hj' i
    rw [hP]
    rw [v12_hjC j' hj']
    exact v12_restC _ _ _ _ _ _ F.S.tp_pos F.S.tm_pos hk hl a1 a3 pa pc pb pd i
  · obtain ⟨b0, b1, b2, b3, b4, b5⟩ := zmod6_add_one
    obtain ⟨c0, c1, c2, c3, c4, c5⟩ := zmod6_sub_one_V
    intro i hi
    simp only [F.GG_u hr, GG_v F hr, hP]
    rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [b0, b1, b2, b3, b4, b5, c0, c1, c2, c3, c4, c5, vC_0, vC_1, vC_2, vC_3, vC_4, vC_5, Pt_0, Pt_1, Pt_2, Pt_3, Pt_4, Pt_5, Pt_6]
    · rcases hR with h | h
      · left; right; exact ⟨trivial, by linarith⟩
      · right; right; exact ⟨trivial, by linarith⟩
    · right; left; have := mul_pos F.S.tm_pos hD; linarith
    · right; left; nlinarith [mul_pos a3 hD]
    · exact absurd rfl hi
    · left; left; nlinarith [mul_pos a1 hD]
    · left; left; have := mul_pos F.S.tp_pos hD; linarith

end Frame02

/-! ### The pure-real part: existence of a good tilt -/

/-- a good tilt `(vx, vz)` in one of the cells A, B, C (see the master lemmas `v12_mA`, `v12_mB`, `v12_mC`). -/
def V12Good (tp tm k l α g : ℝ) : Prop :=
  ∃ vx vz : ℝ, 0 < vz - l * vx ∧ 0 < tp * vz - k * (1 - tp) * vx ∧
   ((0 < -(k * vx + vz) ∧ 0 < l * (1 - tm) * vx + tm * vz) ∨
    (0 < k * vx + vz ∧ 0 < l * (1 - tm) * vx + tm * vz ∧
      (α * (vx * tp) + g * (vz * (k * (1 - tp))) < α * vx ∨
        α * (vx * tp) + g * (vz * (k * (1 - tp))) < 0)) ∨
    (0 < -(k * vx + vz) ∧ 0 < -(l * (1 - tm) * vx) - tm * vz ∧
      (0 < α * (vx * tp) + g * (vz * (k * (1 - tp))) ∨
        0 < α * (vx * tm) + g * (vz * -(l * (1 - tm))))))

/-- reduction to the gradient `u = (ux, uz)`: `s_i = Q'(m_i, u)`, `vx = g ux`, `vz = α uz`. -/
theorem v12_good_of_u {tp tm k l α g : ℝ} (hα : 0 < α) (hg : 0 < g) (ux uz s1 s2 s3 s4 : ℝ)
    (e1 : s1 = g * (l * ux) - α * uz) (e2 : s2 = g * (k * ux) + α * uz)
    (e3 : s3 = α * (tp * uz) - g * (k * (1 - tp) * ux))
    (e4 : s4 = -(g * (l * (1 - tm) * ux)) - α * (tm * uz))
    (h1 : s1 < 0) (h3 : 0 < s3)
    (H : (s2 < 0 ∧ s4 < 0) ∨
      (0 < s2 ∧ s4 < 0 ∧ (tp * ux + k * (1 - tp) * uz < ux ∨ tp * ux + k * (1 - tp) * uz < 0)) ∨
      (s2 < 0 ∧ 0 < s4 ∧ (0 < tp * ux + k * (1 - tp) * uz ∨ 0 < tm * ux + -(l * (1 - tm)) * uz))) :
    V12Good tp tm k l α g := by
  have hag : 0 < α * g := mul_pos hα hg
  refine ⟨g * ux, α * uz, by nlinarith, by nlinarith, ?_⟩
  rcases H with ⟨h2, h4⟩ | ⟨h2, h4, hR⟩ | ⟨h2, h4, hR⟩
  · exact Or.inl ⟨by nlinarith, by nlinarith⟩
  · refine Or.inr (Or.inl ⟨by nlinarith, by nlinarith, ?_⟩)
    rcases hR with hR | hR
    · left; nlinarith [mul_lt_mul_of_pos_left hR hag]
    · right; nlinarith [mul_lt_mul_of_pos_left hR hag]
  · refine Or.inr (Or.inr ⟨by nlinarith, by nlinarith, ?_⟩)
    rcases hR with hR | hR
    · left; nlinarith [mul_pos hag hR]
    · right; nlinarith [mul_pos hag hR]

set_option maxHeartbeats 1000000 in
/-- Leaf 1: `G34 < 0` (angle at `x2` acute): `u = Q44 m3 + μ m4`, cells A (`μ = -G34/2`) or B (`μ = -G34/4`). -/
theorem v12_ex1 {tp tm k l α g : ℝ} (hp : 0 < tp) (a1 : 0 < 1 - tp) (hm : 0 < tm) (a3 : 0 < 1 - tm)
    (hk : 0 < k) (hl : 0 < l) (hα : 0 < α) (hg : 0 < g)
    (hG : g * (k * (1 - tp)) * (l * (1 - tm)) - α * tp * tm < 0) : V12Good tp tm k l α g := by
  obtain ⟨Q44, hQ44⟩ : ∃ Q : ℝ, Q = g * (l * (1 - tm)) ^ 2 + α * tm ^ 2 := ⟨_, rfl⟩
  obtain ⟨Q33, hQ33⟩ : ∃ Q : ℝ, Q = g * (k * (1 - tp)) ^ 2 + α * tp ^ 2 := ⟨_, rfl⟩
  obtain ⟨G34, hG34⟩ : ∃ G : ℝ, G = g * (k * (1 - tp)) * (l * (1 - tm)) - α * tp * tm := ⟨_, rfl⟩
  obtain ⟨G13, hG13⟩ : ∃ G : ℝ, G = -(g * (k * (1 - tp)) * l) - α * tp := ⟨_, rfl⟩
  obtain ⟨G41, hG41⟩ : ∃ G : ℝ, G = α * tm - g * l * (l * (1 - tm)) := ⟨_, rfl⟩
  obtain ⟨G23, hG23⟩ : ∃ G : ℝ, G = α * tp - g * k * (k * (1 - tp)) := ⟨_, rfl⟩
  obtain ⟨G24, hG24⟩ : ∃ G : ℝ, G = -(g * k * (l * (1 - tm))) - α * tm := ⟨_, rfl⟩
  have hG' : G34 < 0 := by rw [hG34]; exact hG
  have hQ44p : 0 < Q44 := by rw [hQ44]; positivity
  have hG13n : G13 < 0 := by rw [hG13]; nlinarith [mul_pos (mul_pos hg hk) (mul_pos a1 hl), mul_pos hα hp]
  have hG24n : G24 < 0 := by rw [hG24]; nlinarith [mul_pos (mul_pos hg hk) (mul_pos a3 hl), mul_pos hα hm]
  have lag3 : Q44 * Q33 - G34 ^ 2 = α * g * (k * (1 - tp) * tm + tp * l * (1 - tm)) ^ 2 := by
    rw [hQ44, hQ33, hG34]; ring
  have lag1 : Q44 * G13 - G41 * G34 = -(α * g * l * (k * (1 - tp) * tm + tp * l * (1 - tm))) := by
    rw [hQ44, hG13, hG41, hG34]; ring
  have hD : 0 < k * (1 - tp) * tm + tp * l * (1 - tm) := by positivity
  have hlag3 : 0 < Q44 * Q33 - G34 ^ 2 := by rw [lag3]; positivity
  have hlag1 : Q44 * G13 - G41 * G34 < 0 := by rw [lag1]; have := mul_pos (mul_pos (mul_pos hα hg) hl) hD; linarith
  -- the family
  have fam : ∀ μ : ℝ, 0 < μ → μ < -G34 →
      ∃ s1 s2 s3 s4 : ℝ,
        s1 = g * (l * (Q44 * -(k * (1 - tp)) + μ * -(l * (1 - tm)))) - α * (Q44 * tp + μ * -tm) ∧
        s2 = g * (k * (Q44 * -(k * (1 - tp)) + μ * -(l * (1 - tm)))) + α * (Q44 * tp + μ * -tm) ∧
        s3 = α * (tp * (Q44 * tp + μ * -tm)) - g * (k * (1 - tp) * (Q44 * -(k * (1 - tp)) + μ * -(l * (1 - tm)))) ∧
        s4 = -(g * (l * (1 - tm) * (Q44 * -(k * (1 - tp)) + μ * -(l * (1 - tm))))) - α * (tm * (Q44 * tp + μ * -tm)) ∧
        s1 < 0 ∧ 0 < s3 ∧ s4 < 0 ∧ s2 = Q44 * G23 + μ * G24 := by
    intro μ hμ hμ2
    refine ⟨_, _, _, _, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · have e : g * (l * (Q44 * -(k * (1 - tp)) + μ * -(l * (1 - tm)))) - α * (Q44 * tp + μ * -tm) =
          Q44 * G13 + μ * G41 := by rw [hG13, hG41]; ring
      rw [e]
      have key : (-G34) * (Q44 * G13 + μ * G41) =
          (-G34 - μ) * (Q44 * G13) + μ * (Q44 * G13 - G41 * G34) := by ring
      have t1 : (-G34 - μ) * (Q44 * G13) < 0 :=
        mul_neg_of_pos_of_neg (by linarith) (mul_neg_of_pos_of_neg hQ44p hG13n)
      have t2 : μ * (Q44 * G13 - G41 * G34) < 0 := mul_neg_of_pos_of_neg hμ hlag1
      have t3 : (-G34) * (Q44 * G13 + μ * G41) < 0 := by rw [key]; linarith
      exact neg_of_mul_neg_right t3 (by linarith)
    · have e : α * (tp * (Q44 * tp + μ * -tm)) - g * (k * (1 - tp) * (Q44 * -(k * (1 - tp)) + μ * -(l * (1 - tm)))) =
          Q44 * Q33 + μ * G34 := by rw [hQ33, hG34]; ring
      rw [e]
      have := mul_pos (sub_pos.2 hμ2) (neg_pos.2 hG')
      nlinarith [this, hlag3]
    · have e : -(g * (l * (1 - tm) * (Q44 * -(k * (1 - tp)) + μ * -(l * (1 - tm))))) - α * (tm * (Q44 * tp + μ * -tm)) =
          Q44 * (G34 + μ) := by rw [hQ44, hG34]; ring
      rw [e]; exact mul_neg_of_pos_of_neg hQ44p (by linarith)
    · rw [hG23, hG24]; ring
  obtain ⟨s1, s2, s3, s4, e1, e2, e3, e4, h1, h3, h4, hs2⟩ := fam (-G34 / 2) (by linarith) (by linarith)
  by_cases hc : s2 < 0
  · exact v12_good_of_u hα hg _ _ s1 s2 s3 s4 e1 e2 e3 e4 h1 h3 (Or.inl ⟨hc, h4⟩)
  · push_neg at hc
    obtain ⟨t1, t2, t3, t4, f1, f2, f3, f4, k1, k3, k4, ks2⟩ := fam (-G34 / 4) (by linarith) (by linarith)
    have h2 : 0 < t2 := by
      rw [ks2]; rw [hs2] at hc; nlinarith [mul_pos_of_neg_of_neg hG' hG24n]
    refine v12_good_of_u hα hg _ _ t1 t2 t3 t4 f1 f2 f3 f4 k1 k3 (Or.inr (Or.inl ⟨h2, k4, Or.inr ?_⟩))
    have : tp * (Q44 * -(k * (1 - tp)) + (-G34 / 4) * -(l * (1 - tm))) + k * (1 - tp) * (Q44 * tp + (-G34 / 4) * -tm) =
        -((-G34 / 4) * (l * (1 - tm) * tp + k * (1 - tp) * tm)) := by ring
    rw [this]
    have hq : 0 < (-G34 / 4) * (l * (1 - tm) * tp + k * (1 - tp) * tm) :=
      mul_pos (by linarith) (by positivity)
    linarith

set_option maxHeartbeats 1000000 in
/-- Leaf 2: `G23 < 0` (angle at `x0` obtuse... exterior angle at `x0` obtuse): `u = Q22 m3 + μ m2`, cells A or C. -/
theorem v12_ex2 {tp tm k l α g : ℝ} (hp : 0 < tp) (a1 : 0 < 1 - tp) (hm : 0 < tm) (a3 : 0 < 1 - tm)
    (hk : 0 < k) (hl : 0 < l) (hα : 0 < α) (hg : 0 < g)
    (hG : α * tp - g * k * (k * (1 - tp)) < 0) : V12Good tp tm k l α g := by
  obtain ⟨Q22, hQ22⟩ : ∃ Q : ℝ, Q = g * k ^ 2 + α := ⟨_, rfl⟩
  obtain ⟨Q33, hQ33⟩ : ∃ Q : ℝ, Q = g * (k * (1 - tp)) ^ 2 + α * tp ^ 2 := ⟨_, rfl⟩
  obtain ⟨G34, hG34⟩ : ∃ G : ℝ, G = g * (k * (1 - tp)) * (l * (1 - tm)) - α * tp * tm := ⟨_, rfl⟩
  obtain ⟨G13, hG13⟩ : ∃ G : ℝ, G = -(g * (k * (1 - tp)) * l) - α * tp := ⟨_, rfl⟩
  obtain ⟨G12, hG12⟩ : ∃ G : ℝ, G = g * l * k - α := ⟨_, rfl⟩
  obtain ⟨G23, hG23⟩ : ∃ G : ℝ, G = α * tp - g * k * (k * (1 - tp)) := ⟨_, rfl⟩
  obtain ⟨G24, hG24⟩ : ∃ G : ℝ, G = -(g * k * (l * (1 - tm))) - α * tm := ⟨_, rfl⟩
  have hG' : G23 < 0 := by rw [hG23]; exact hG
  have hQ22p : 0 < Q22 := by rw [hQ22]; positivity
  have hG13n : G13 < 0 := by rw [hG13]; nlinarith [mul_pos (mul_pos hg hk) (mul_pos a1 hl), mul_pos hα hp]
  have hG24n : G24 < 0 := by rw [hG24]; nlinarith [mul_pos (mul_pos hg hk) (mul_pos a3 hl), mul_pos hα hm]
  have lag3 : Q22 * Q33 - G23 ^ 2 = α * g * k ^ 2 := by rw [hQ22, hQ33, hG23]; ring
  have lag1 : Q22 * G13 - G12 * G23 = -(α * g * k * (k + l)) := by rw [hQ22, hG13, hG12, hG23]; ring
  have hlag3 : 0 < Q22 * Q33 - G23 ^ 2 := by rw [lag3]; positivity
  have hlag1 : Q22 * G13 - G12 * G23 < 0 := by
    rw [lag1]; have := mul_pos (mul_pos (mul_pos hα hg) hk) (add_pos hk hl); linarith
  have fam : ∀ μ : ℝ, 0 < μ → μ < -G23 →
      ∃ s1 s2 s3 s4 : ℝ,
        s1 = g * (l * (Q22 * -(k * (1 - tp)) + μ * k)) - α * (Q22 * tp + μ * 1) ∧
        s2 = g * (k * (Q22 * -(k * (1 - tp)) + μ * k)) + α * (Q22 * tp + μ * 1) ∧
        s3 = α * (tp * (Q22 * tp + μ * 1)) - g * (k * (1 - tp) * (Q22 * -(k * (1 - tp)) + μ * k)) ∧
        s4 = -(g * (l * (1 - tm) * (Q22 * -(k * (1 - tp)) + μ * k))) - α * (tm * (Q22 * tp + μ * 1)) ∧
        s1 < 0 ∧ 0 < s3 ∧ s2 < 0 ∧ s4 = Q22 * G34 + μ * G24 := by
    intro μ hμ hμ2
    refine ⟨_, _, _, _, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · have e : g * (l * (Q22 * -(k * (1 - tp)) + μ * k)) - α * (Q22 * tp + μ * 1) =
          Q22 * G13 + μ * G12 := by rw [hG13, hG12]; ring
      rw [e]
      have key : (-G23) * (Q22 * G13 + μ * G12) =
          (-G23 - μ) * (Q22 * G13) + μ * (Q22 * G13 - G12 * G23) := by ring
      have t1 : (-G23 - μ) * (Q22 * G13) < 0 :=
        mul_neg_of_pos_of_neg (by linarith) (mul_neg_of_pos_of_neg hQ22p hG13n)
      have t2 : μ * (Q22 * G13 - G12 * G23) < 0 := mul_neg_of_pos_of_neg hμ hlag1
      have t3 : (-G23) * (Q22 * G13 + μ * G12) < 0 := by rw [key]; linarith
      exact neg_of_mul_neg_right t3 (by linarith)
    · have e : α * (tp * (Q22 * tp + μ * 1)) - g * (k * (1 - tp) * (Q22 * -(k * (1 - tp)) + μ * k)) =
          Q22 * Q33 + μ * G23 := by rw [hQ33, hG23]; ring
      rw [e]
      have := mul_pos (sub_pos.2 hμ2) (neg_pos.2 hG')
      nlinarith [this, hlag3]
    · have e : g * (k * (Q22 * -(k * (1 - tp)) + μ * k)) + α * (Q22 * tp + μ * 1) =
          Q22 * (G23 + μ) := by rw [hQ22, hG23]; ring
      rw [e]; exact mul_neg_of_pos_of_neg hQ22p (by linarith)
    · rw [hG34, hG24]; ring
  obtain ⟨s1, s2, s3, s4, e1, e2, e3, e4, h1, h3, h2, hs4⟩ := fam (-G23 / 2) (by linarith) (by linarith)
  by_cases hc : s4 < 0
  · exact v12_good_of_u hα hg _ _ s1 s2 s3 s4 e1 e2 e3 e4 h1 h3 (Or.inl ⟨h2, hc⟩)
  · push_neg at hc
    obtain ⟨t1, t2, t3, t4, f1, f2, f3, f4, k1, k3, k2, kt4⟩ := fam (-G23 / 4) (by linarith) (by linarith)
    have h4 : 0 < t4 := by
      rw [kt4]; rw [hs4] at hc; nlinarith [mul_pos_of_neg_of_neg hG' hG24n]
    refine v12_good_of_u hα hg _ _ t1 t2 t3 t4 f1 f2 f3 f4 k1 k3 (Or.inr (Or.inr ⟨k2, h4, Or.inl ?_⟩))
    have : tp * (Q22 * -(k * (1 - tp)) + (-G23 / 4) * k) + k * (1 - tp) * (Q22 * tp + (-G23 / 4) * 1) =
        (-G23 / 4) * k := by ring
    rw [this]
    exact mul_pos (by linarith) hk

set_option maxHeartbeats 1000000 in
/-- Leaf 5: `G12 < 0 < G23`, `0 ≤ G41`: `u = Q11 m2 + μ m1`, cell B. -/
theorem v12_ex5 {tp tm k l α g : ℝ} (hp : 0 < tp) (a1 : 0 < 1 - tp) (hm : 0 < tm) (a3 : 0 < 1 - tm)
    (hk : 0 < k) (hl : 0 < l) (hα : 0 < α) (hg : 0 < g)
    (h12 : g * l * k - α < 0) (h23 : 0 < α * tp - g * k * (k * (1 - tp)))
    (h41 : 0 ≤ α * tm - g * l * (l * (1 - tm))) : V12Good tp tm k l α g := by
  obtain ⟨Q11, hQ11⟩ : ∃ Q : ℝ, Q = g * l ^ 2 + α := ⟨_, rfl⟩
  obtain ⟨Q22, hQ22⟩ : ∃ Q : ℝ, Q = g * k ^ 2 + α := ⟨_, rfl⟩
  obtain ⟨G13, hG13⟩ : ∃ G : ℝ, G = -(g * (k * (1 - tp)) * l) - α * tp := ⟨_, rfl⟩
  obtain ⟨G12, hG12⟩ : ∃ G : ℝ, G = g * l * k - α := ⟨_, rfl⟩
  obtain ⟨G23, hG23⟩ : ∃ G : ℝ, G = α * tp - g * k * (k * (1 - tp)) := ⟨_, rfl⟩
  obtain ⟨G24, hG24⟩ : ∃ G : ℝ, G = -(g * k * (l * (1 - tm))) - α * tm := ⟨_, rfl⟩
  obtain ⟨G41, hG41⟩ : ∃ G : ℝ, G = α * tm - g * l * (l * (1 - tm)) := ⟨_, rfl⟩
  have hG12n : G12 < 0 := by rw [hG12]; exact h12
  have hG23p : 0 < G23 := by rw [hG23]; exact h23
  have hG41p : 0 ≤ G41 := by rw [hG41]; exact h41
  have hQ11p : 0 < Q11 := by rw [hQ11]; positivity
  have hG13n : G13 < 0 := by rw [hG13]; nlinarith [mul_pos (mul_pos hg hk) (mul_pos a1 hl), mul_pos hα hp]
  have hG24n : G24 < 0 := by rw [hG24]; nlinarith [mul_pos (mul_pos hg hk) (mul_pos a3 hl), mul_pos hα hm]
  have lag2 : Q11 * Q22 - G12 ^ 2 = α * g * (k + l) ^ 2 := by rw [hQ11, hQ22, hG12]; ring
  have hlag2 : 0 < Q11 * Q22 - G12 ^ 2 := by rw [lag2]; positivity
  have hB1 : 0 < -G12 := by linarith
  have hN3 : 0 < Q11 * G23 := mul_pos hQ11p hG23p
  have hC3 : 0 < -G13 := by linarith
  have hN4 : 0 < -(Q11 * G24) := by nlinarith [mul_pos hQ11p (neg_pos.2 hG24n)]
  have hT : 0 < 1 / (-G12) + (-G13) / (Q11 * G23) + G41 / (-(Q11 * G24)) := by
    have := div_pos hC3 hN3
    have := div_nonneg hG41p hN4.le
    have := one_div_pos.2 hB1
    linarith
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = 1 / (1 / (-G12) + (-G13) / (Q11 * G23) + G41 / (-(Q11 * G24))) := ⟨_, rfl⟩
  have hμp : 0 < μ := by rw [hμ]; exact one_div_pos.2 hT
  have hμT : μ * (1 / (-G12) + (-G13) / (Q11 * G23) + G41 / (-(Q11 * G24))) = 1 := by
    rw [hμ]; exact one_div_mul_cancel hT.ne'
  have c1 : 0 < μ * (1 / (-G12)) := mul_pos hμp (one_div_pos.2 hB1)
  have c3 : 0 < μ * ((-G13) / (Q11 * G23)) := mul_pos hμp (div_pos hC3 hN3)
  have c4 : 0 ≤ μ * (G41 / (-(Q11 * G24))) := mul_nonneg hμp.le (div_nonneg hG41p hN4.le)
  have hμ1 : μ < -G12 := by
    have : μ * (1 / (-G12)) < 1 := by nlinarith
    rw [mul_one_div, div_lt_one hB1] at this; exact this
  have hμ3 : μ * (-G13) < Q11 * G23 := by
    have : μ * ((-G13) / (Q11 * G23)) < 1 := by nlinarith
    rw [← mul_div_assoc, div_lt_one hN3] at this; exact this
  have hμ4 : μ * G41 < -(Q11 * G24) := by
    have : μ * (G41 / (-(Q11 * G24))) < 1 := by nlinarith
    rw [← mul_div_assoc, div_lt_one hN4] at this; exact this
  refine v12_good_of_u hα hg (Q11 * k + μ * l) (Q11 * 1 + μ * -1) (Q11 * (G12 + μ)) (Q11 * Q22 + μ * G12)
    (Q11 * G23 + μ * G13) (Q11 * G24 + μ * G41) ?_ ?_ ?_ ?_ ?_ ?_ (Or.inr (Or.inl ⟨?_, ?_, Or.inl ?_⟩))
  · rw [hQ11, hG12]; ring
  · rw [hQ11, hQ22, hG12]; ring
  · rw [hG23, hG13, hQ11]; ring
  · rw [hG24, hG41, hQ11]; ring
  · exact mul_neg_of_pos_of_neg hQ11p (by linarith)
  · nlinarith
  · have := mul_pos (sub_pos.2 hμ1) hB1
    nlinarith [this, hlag2]
  · nlinarith
  · have : (Q11 * k + μ * l) - (tp * (Q11 * k + μ * l) + k * (1 - tp) * (Q11 * 1 + μ * -1)) =
        (1 - tp) * (μ * (k + l)) := by ring
    have h2 : 0 < (1 - tp) * (μ * (k + l)) := by positivity
    linarith

/-! ### The frame level -/

namespace Frame02
variable {x : Fin 7 → ℝ³} (F : Frame02 x)

theorem v12_comp_perm (π : Equiv.Perm (Fin 7)) (h : IsRupert (Finset.univ.image (x ∘ π))) :
    IsRupert (Finset.univ.image x) := by
  rwa [isRupert_image_comp_perm] at h

/-- combine the three masters -/
theorem v12_of_good (hr : gA12 x = gA11 x) (hA : F.S.tp = F.S.sp) (hB : F.S.tm = F.S.sm) (k l : ℝ)
    (hk : 0 < k) (hl : 0 < l)
    (h1 : F.S.hp = k * (1 - F.S.tp)) (h2 : F.S.kp = k * (1 - F.S.sp))
    (h3 : F.S.hm = l * (1 - F.S.tm)) (h4 : F.S.km = l * (1 - F.S.sm))
    (hG : V12Good F.S.tp F.S.tm k l (gA11 x) F.toFrame7.gg) : IsRupert (Finset.univ.image x) := by
  obtain ⟨vx, vz, pa, pc, H⟩ := hG
  rcases H with ⟨pb, pd⟩ | ⟨pb, pd, hR⟩ | ⟨pb, pd, hR⟩
  · exact F.v12_mA hr hA hB k l hk hl h1 h2 h3 h4 vx vz pa pb pc pd
  · exact F.v12_mB hr hA hB k l hk hl h1 h2 h3 h4 vx vz pa pb pc pd hR
  · exact F.v12_mC hr hA hB k l hk hl h1 h2 h3 h4 vx vz pa pb pc pd hR

/-- the four inner products of `F1` in terms of `A11`, `g`, `k`, `l`, `tp`, `tm` -/
theorem v12_inner {k l : ℝ} (h1 : F.S.hp = k * (1 - F.S.tp)) (h3 : F.S.hm = l * (1 - F.S.tm)) :
    ⟪x 2 - x 0, x 3 - x 0⟫ = -(1 - F.S.tp) * (gA11 x * F.S.tp - F.toFrame7.gg * k * (k * (1 - F.S.tp))) ∧
    ⟪x 2 - x 5, x 3 - x 5⟫ = -(1 - F.S.tm) * (gA11 x * F.S.tm - F.toFrame7.gg * l * (l * (1 - F.S.tm))) ∧
    ⟪x 0 - x 2, x 5 - x 2⟫ =
      -(F.toFrame7.gg * (k * (1 - F.S.tp)) * (l * (1 - F.S.tm)) - gA11 x * F.S.tp * F.S.tm) ∧
    ⟪x 0 - x 3, x 5 - x 3⟫ = -(1 - F.S.tp) * (1 - F.S.tm) * (F.toFrame7.gg * l * k - gA11 x) := by
  have hue := F.inner_u1_e
  have heu : ⟪F.e, x 3 - x 2⟫ = 0 := by rw [real_inner_comm]; exact hue
  have e0 : x 0 - x 2 = F.S.tp • (x 3 - x 2) + F.S.hp • F.e := by rw [F.x0_eq]; abel
  have e5 : x 5 - x 2 = F.S.tm • (x 3 - x 2) - F.S.hm • F.e := by rw [F.x5_eq]; abel
  have e20 : x 2 - x 0 = -(F.S.tp • (x 3 - x 2) + F.S.hp • F.e) := by rw [← e0]; abel
  have e25 : x 2 - x 5 = -(F.S.tm • (x 3 - x 2) - F.S.hm • F.e) := by rw [← e5]; abel
  have e30 : x 3 - x 0 = (1 - F.S.tp) • (x 3 - x 2) - F.S.hp • F.e := by
    have : x 3 - x 0 = (x 3 - x 2) - (x 0 - x 2) := by abel
    rw [this, e0]; module
  have e35 : x 3 - x 5 = (1 - F.S.tm) • (x 3 - x 2) + F.S.hm • F.e := by
    have : x 3 - x 5 = (x 3 - x 2) - (x 5 - x 2) := by abel
    rw [this, e5]; module
  have e03 : x 0 - x 3 = (F.S.tp - 1) • (x 3 - x 2) + F.S.hp • F.e := by
    have : x 0 - x 3 = (x 0 - x 2) - (x 3 - x 2) := by abel
    rw [this, e0]; module
  have e53 : x 5 - x 3 = (F.S.tm - 1) • (x 3 - x 2) - F.S.hm • F.e := by
    have : x 5 - x 3 = (x 5 - x 2) - (x 3 - x 2) := by abel
    rw [this, e5]; module
  have hA11 : gA11 x = ⟪x 3 - x 2, x 3 - x 2⟫ := rfl
  have hgg : F.toFrame7.gg = ⟪F.e, F.e⟫ := rfl
  rw [hA11, hgg]
  generalize x 3 - x 2 = u at *
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e20, e30]
    simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, inner_neg_left,
      inner_smul_left, inner_smul_right, hue, heu, RCLike.conj_to_real]
    rw [h1]; ring
  · rw [e25, e35]
    simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, inner_neg_left,
      inner_smul_left, inner_smul_right, hue, heu, RCLike.conj_to_real]
    rw [h3]; ring
  · rw [e0, e5]
    simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      inner_smul_left, inner_smul_right, hue, heu, RCLike.conj_to_real]
    rw [h1, h3]; ring
  · rw [e03, e53]
    simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      inner_smul_left, inner_smul_right, hue, heu, RCLike.conj_to_real]
    rw [h1, h3]; ring

theorem v12_noall {tp tm k l α g : ℝ} (hp : 0 < tp) (hm : 0 < tm) (hk : 0 < k) (hl : 0 < l)
    (hg : 0 < g) (a1 : 0 < 1 - tp) (a3 : 0 < 1 - tm)
    (h12 : 0 ≤ g * l * k - α) (h23 : 0 ≤ α * tp - g * k * (k * (1 - tp)))
    (h34 : 0 ≤ g * (k * (1 - tp)) * (l * (1 - tm)) - α * tp * tm)
    (h41 : 0 ≤ α * tm - g * l * (l * (1 - tm))) :
    α * tp - g * k * (k * (1 - tp)) = 0 ∧ α * tm - g * l * (l * (1 - tm)) = 0 := by
  have e1 : g * l * (1 - tm) * (k * (1 - tp) - tp * l) =
      (g * (k * (1 - tp)) * (l * (1 - tm)) - α * tp * tm) + tp * (α * tm - g * l * (l * (1 - tm))) := by ring
  have e2 : g * k * (k * (1 - tp) - tp * l) = -(tp * (g * l * k - α) + (α * tp - g * k * (k * (1 - tp)))) := by ring
  have p1 : 0 < g * l * (1 - tm) := by positivity
  have p2 : 0 < g * k := by positivity
  have t1 := mul_nonneg hp.le h41
  have t2 := mul_nonneg hp.le h12
  have hX0 : 0 ≤ k * (1 - tp) - tp * l := by
    by_contra h
    push_neg at h
    have := mul_neg_of_pos_of_neg p1 h
    linarith
  have hX1 : k * (1 - tp) - tp * l ≤ 0 := by
    by_contra h
    push_neg at h
    have := mul_pos p2 h
    linarith
  have hX : k * (1 - tp) - tp * l = 0 := le_antisymm hX1 hX0
  rw [hX, mul_zero] at e1 e2
  constructor
  · linarith
  · nlinarith

/-- Leaf 1 at frame level: acute angle at `x2`. -/
theorem v12_fl1 (hr : gA12 x = gA11 x) (hA : F.S.tp = F.S.sp) (hB : F.S.tm = F.S.sm)
    (h : 0 < ⟪x 0 - x 2, x 5 - x 2⟫) : IsRupert (Finset.univ.image x) := by
  obtain ⟨k, l, hk, hl, h1, h2, h3, h4⟩ := exists_kl F.S
  have hI := (F.v12_inner h1 h3).2.2.1
  have ha : 0 < gA11 x := hr ▸ F.A12_pos
  have hg := F.gg_pos
  have a1 := sub_pos.2 F.S.tp_lt
  have a3 := sub_pos.2 F.S.tm_lt
  refine F.v12_of_good hr hA hB k l hk hl h1 h2 h3 h4
    (v12_ex1 F.S.tp_pos a1 F.S.tm_pos a3 hk hl ha hg ?_)
  rw [hI] at h; linarith

/-- Leaf 2 at frame level: obtuse exterior... `⟪x2 - x0, x3 - x0⟫ > 0`. -/
theorem v12_fl2 (hr : gA12 x = gA11 x) (hA : F.S.tp = F.S.sp) (hB : F.S.tm = F.S.sm)
    (h : 0 < ⟪x 2 - x 0, x 3 - x 0⟫) : IsRupert (Finset.univ.image x) := by
  obtain ⟨k, l, hk, hl, h1, h2, h3, h4⟩ := exists_kl F.S
  have hI := (F.v12_inner h1 h3).1
  have ha : 0 < gA11 x := hr ▸ F.A12_pos
  have hg := F.gg_pos
  have a1 := sub_pos.2 F.S.tp_lt
  have a3 := sub_pos.2 F.S.tm_lt
  refine F.v12_of_good hr hA hB k l hk hl h1 h2 h3 h4
    (v12_ex2 F.S.tp_pos a1 F.S.tm_pos a3 hk hl ha hg ?_)
  rw [hI] at h
  have : 0 < (1 - F.S.tp) * -(gA11 x * F.S.tp - F.toFrame7.gg * k * (k * (1 - F.S.tp))) := by linarith
  have := (mul_pos_iff_of_pos_left a1).1 this
  linarith

/-- Leaf 5 at frame level. -/
theorem v12_fl5 (hr : gA12 x = gA11 x) (hA : F.S.tp = F.S.sp) (hB : F.S.tm = F.S.sm)
    (h0 : ⟪x 2 - x 0, x 3 - x 0⟫ < 0) (h5 : ⟪x 2 - x 5, x 3 - x 5⟫ ≤ 0)
    (h3 : 0 < ⟪x 0 - x 3, x 5 - x 3⟫) : IsRupert (Finset.univ.image x) := by
  obtain ⟨k, l, hk, hl, h1, h2, h3', h4⟩ := exists_kl F.S
  obtain ⟨i0, i5, -, i3⟩ := F.v12_inner h1 h3'
  have ha : 0 < gA11 x := hr ▸ F.A12_pos
  have hg := F.gg_pos
  have a1 := sub_pos.2 F.S.tp_lt
  have a3 := sub_pos.2 F.S.tm_lt
  refine F.v12_of_good hr hA hB k l hk hl h1 h2 h3' h4
    (v12_ex5 F.S.tp_pos a1 F.S.tm_pos a3 hk hl ha hg ?_ ?_ ?_)
  · rw [i3] at h3
    have : 0 < ((1 - F.S.tp) * (1 - F.S.tm)) * -(F.toFrame7.gg * l * k - gA11 x) := by linarith
    have := (mul_pos_iff_of_pos_left (mul_pos a1 a3)).1 this
    linarith
  · rw [i0] at h0
    have : 0 < (1 - F.S.tp) * (gA11 x * F.S.tp - F.toFrame7.gg * k * (k * (1 - F.S.tp))) := by linarith
    have := (mul_pos_iff_of_pos_left a1).1 this
    linarith
  · rw [i5] at h5
    have : 0 ≤ (1 - F.S.tm) * (gA11 x * F.S.tm - F.toFrame7.gg * l * (l * (1 - F.S.tm))) := by linarith
    have := nonneg_of_mul_nonneg_right this a3
    linarith

/-- **Lemma FN (iv)(a)**: both far edges vertical, doubles 6, 4, 1 over `F1 = (5,3,0,2)`; closed off X2. -/
theorem right_V12_pf (hr : gA12 x = gA11 x)
    (hA : F.S.tp = F.S.sp) (hB : F.S.tm = F.S.sm) (hX2 : ¬ X2Set x) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨G, g1, g2, g3, g4, e1, e2, e3⟩ := F.alpha_spec
  have hr' : gA12 (x ∘ permAlpha) = gA11 (x ∘ permAlpha) := by rw [e2, e1]; exact hr
  have hA' : G.S.tp = G.S.sp := by rw [g1, g3]; exact hB
  have hB' : G.S.tm = G.S.sm := by rw [g2, g4]; exact hA
  have hx0 : (x ∘ permAlpha) 0 = x 5 := by simp [Function.comp, pA0]
  have hx2 : (x ∘ permAlpha) 2 = x 2 := by simp [Function.comp, pA2]
  have hx3 : (x ∘ permAlpha) 3 = x 3 := by simp [Function.comp, pA3]
  have hx5 : (x ∘ permAlpha) 5 = x 0 := by simp [Function.comp, pA5]
  by_cases c2 : 0 < ⟪x 0 - x 2, x 5 - x 2⟫
  · exact F.v12_fl1 hr hA hB c2
  by_cases c0 : 0 < ⟪x 2 - x 0, x 3 - x 0⟫
  · exact F.v12_fl2 hr hA hB c0
  by_cases c5 : 0 < ⟪x 2 - x 5, x 3 - x 5⟫
  · refine v12_comp_perm permAlpha (G.v12_fl2 hr' hA' hB' ?_)
    rw [hx2, hx0, hx3]; exact c5
  push_neg at c2 c0 c5
  have h3pos : (⟪x 2 - x 0, x 3 - x 0⟫ < 0 ∨ ⟪x 2 - x 5, x 3 - x 5⟫ < 0) →
      0 < ⟪x 0 - x 3, x 5 - x 3⟫ := by
    intro hlt
    by_contra h3
    push_neg at h3
    obtain ⟨k, l, hk, hl, h1, h2, h3', h4⟩ := exists_kl F.S
    obtain ⟨i0, i5, i2, i3⟩ := F.v12_inner h1 h3'
    have hg := F.gg_pos
    have a1 := sub_pos.2 F.S.tp_lt
    have a3 := sub_pos.2 F.S.tm_lt
    have hZ : 0 ≤ F.toFrame7.gg * l * k - gA11 x := by
      rw [i3] at h3
      exact nonneg_of_mul_nonneg_right (by linarith : 0 ≤ ((1 - F.S.tp) * (1 - F.S.tm)) *
        (F.toFrame7.gg * l * k - gA11 x)) (mul_pos a1 a3)
    have hX : 0 ≤ gA11 x * F.S.tp - F.toFrame7.gg * k * (k * (1 - F.S.tp)) := by
      rw [i0] at c0
      exact nonneg_of_mul_nonneg_right (by linarith : 0 ≤ (1 - F.S.tp) *
        (gA11 x * F.S.tp - F.toFrame7.gg * k * (k * (1 - F.S.tp)))) a1
    have hY : 0 ≤ gA11 x * F.S.tm - F.toFrame7.gg * l * (l * (1 - F.S.tm)) := by
      rw [i5] at c5
      exact nonneg_of_mul_nonneg_right (by linarith : 0 ≤ (1 - F.S.tm) *
        (gA11 x * F.S.tm - F.toFrame7.gg * l * (l * (1 - F.S.tm)))) a3
    have hW : 0 ≤ F.toFrame7.gg * (k * (1 - F.S.tp)) * (l * (1 - F.S.tm)) - gA11 x * F.S.tp * F.S.tm := by
      rw [i2] at c2; linarith
    obtain ⟨hx, hy⟩ := v12_noall F.S.tp_pos F.S.tm_pos hk hl hg a1 a3 hZ hX hW hY
    rcases hlt with h | h
    · rw [i0, hx] at h; simp at h
    · rw [i5, hy] at h; simp at h
  by_cases d0 : ⟪x 2 - x 0, x 3 - x 0⟫ < 0
  · exact F.v12_fl5 hr hA hB d0 c5 (h3pos (Or.inl d0))
  by_cases d5 : ⟪x 2 - x 5, x 3 - x 5⟫ < 0
  · refine v12_comp_perm permAlpha (G.v12_fl5 hr' hA' hB' ?_ ?_ ?_)
    · rw [hx2, hx0, hx3]; exact d5
    · rw [hx2, hx5, hx3]; exact c0
    · rw [hx0, hx3, hx5, real_inner_comm]; exact h3pos (Or.inr d5)
  exact absurd ⟨le_antisymm c0 (not_lt.1 d0), le_antisymm c5 (not_lt.1 d5), c2⟩ hX2

end Frame02
end Minimality.CaseC18
