module

public import Minimality.Type24Circle

@[expose] public section

/-!
# Type 24 link edge, five-cycle unimodality and edge-rim tests (nopert229 reports LINKVIEW24, TAIL24-IDEAS-FABLE section 2.3).
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace

namespace Minimality
namespace Link24

/-- The cyclic depth sequence of five reals. -/
def cyc5 (a b c d e : ℝ) : ZMod 5 → ℝ := ![a, b, c, d, e]

/-- A 5-cycle of distinct reals is unimodal when no two non-adjacent corners are both local maxima. -/
theorem uni5 {a b c d e : ℝ} (hinj : Function.Injective (cyc5 a b c d e))
    (h02 : ¬ ((e < a ∧ b < a) ∧ (b < c ∧ d < c)))
    (h03 : ¬ ((e < a ∧ b < a) ∧ (c < d ∧ e < d)))
    (h13 : ¬ ((a < b ∧ c < b) ∧ (c < d ∧ e < d)))
    (h14 : ¬ ((a < b ∧ c < b) ∧ (d < e ∧ a < e)))
    (h24 : ¬ ((b < c ∧ d < c) ∧ (d < e ∧ a < e))) :
    IsCyclicUnimodal (cyc5 a b c d e) := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_sub_one
  refine isCyclicUnimodal_of_atMostOne (by norm_num) hinj fun i j hi hj => ?_
  have v0 : cyc5 a b c d e 0 = a := rfl
  have v1 : cyc5 a b c d e 1 = b := rfl
  have v2 : cyc5 a b c d e 2 = c := rfl
  have v3 : cyc5 a b c d e 3 = d := rfl
  have v4 : cyc5 a b c d e 4 = e := rfl
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
  simp only [a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, v0, v1, v2, v3, v4] at hi hj <;>
  obtain ⟨hi1, hi2⟩ := hi <;> obtain ⟨hj1, hj2⟩ := hj <;>
  first
  | rfl
  | (exfalso; linarith)
  | exact (h02 ⟨⟨hi1, hi2⟩, ⟨hj1, hj2⟩⟩).elim
  | exact (h02 ⟨⟨hj1, hj2⟩, ⟨hi1, hi2⟩⟩).elim
  | exact (h03 ⟨⟨hi1, hi2⟩, ⟨hj1, hj2⟩⟩).elim
  | exact (h03 ⟨⟨hj1, hj2⟩, ⟨hi1, hi2⟩⟩).elim
  | exact (h13 ⟨⟨hi1, hi2⟩, ⟨hj1, hj2⟩⟩).elim
  | exact (h13 ⟨⟨hj1, hj2⟩, ⟨hi1, hi2⟩⟩).elim
  | exact (h14 ⟨⟨hi1, hi2⟩, ⟨hj1, hj2⟩⟩).elim
  | exact (h14 ⟨⟨hj1, hj2⟩, ⟨hi1, hi2⟩⟩).elim
  | exact (h24 ⟨⟨hi1, hi2⟩, ⟨hj1, hj2⟩⟩).elim
  | exact (h24 ⟨⟨hj1, hj2⟩, ⟨hi1, hi2⟩⟩).elim

/-- The rim `(X, 4, 3, 2, 1)` of the link edge `06`. -/
def rim06 (X : Fin 7) : ZMod 5 → Fin 7 := ![X, 4, 3, 2, 1]

/-- Failure of the path-closing lemma at the link edge `06` (path `4, 3, 2, 1`). -/
def Fail06 (z : Fin 7 → ℝ) : Prop :=
  (z 4 < z 3 ∧ z 2 < z 3 ∧ z 2 < z 1 ∧ z 4 < z 6) ∨ (z 3 < z 4 ∧ z 3 < z 2 ∧ z 1 < z 2 ∧ z 0 < z 4)

/-! ### Abstract path-closing lemma on five reals -/

/-- Path-closing lemma, known order against the LAST path end: the cycle `(X, p, q, r, s)`
with `xl < s < xh`.  Fails exactly in the two zigzag patterns. -/
theorem coreF {xl xh p q r s : ℝ} (hl : xl < s) (hh : s < xh)
    (i1 : Function.Injective (cyc5 xh p q r s)) (i2 : Function.Injective (cyc5 xl p q r s))
    (hF : ¬ ((p < q ∧ r < q ∧ r < s ∧ p < xh) ∨ (q < p ∧ q < r ∧ s < r ∧ xl < p))) :
    IsCyclicUnimodal (cyc5 xh p q r s) ∨ IsCyclicUnimodal (cyc5 xl p q r s) := by
  have n1 : p ≠ q := i1.ne (show (1 : ZMod 5) ≠ 2 by decide)
  have n2 : q ≠ r := i1.ne (show (2 : ZMod 5) ≠ 3 by decide)
  have n3 : r ≠ s := i1.ne (show (3 : ZMod 5) ≠ 4 by decide)
  have n4 : p ≠ xl := i2.ne (show (1 : ZMod 5) ≠ 0 by decide)
  have n5 : p ≠ xh := i1.ne (show (1 : ZMod 5) ≠ 0 by decide)
  simp only [not_or, not_and, not_lt] at hF
  obtain ⟨hF1, hF2⟩ := hF
  rcases lt_or_gt_of_ne n1 with c1 | c1 <;> rcases lt_or_gt_of_ne n2 with c2 | c2 <;>
  rcases lt_or_gt_of_ne n3 with c3 | c3 <;> rcases lt_or_gt_of_ne n4 with c4 | c4 <;>
  rcases lt_or_gt_of_ne n5 with c5 | c5 <;>
  first
  | (left; refine uni5 i1 ?_ ?_ ?_ ?_ ?_ <;> rintro ⟨⟨_, _⟩, ⟨_, _⟩⟩ <;> linarith)
  | (right; refine uni5 i2 ?_ ?_ ?_ ?_ ?_ <;> rintro ⟨⟨_, _⟩, ⟨_, _⟩⟩ <;> linarith)
  | (exfalso; first
      | exact absurd (hF1 c1 (by assumption) (by assumption)) (by linarith)
      | exact absurd (hF2 c1 (by assumption) (by assumption)) (by linarith))

/-- Path-closing lemma, known order against the FIRST path end: `(X, p, q, r, s)` with
`xl < p < xh`. -/
theorem coreB {xl xh p q r s : ℝ} (hl : xl < p) (hh : p < xh)
    (i1 : Function.Injective (cyc5 xh p q r s)) (i2 : Function.Injective (cyc5 xl p q r s))
    (hF : ¬ ((s < r ∧ q < r ∧ q < p ∧ s < xh) ∨ (r < s ∧ r < q ∧ p < q ∧ xl < s))) :
    IsCyclicUnimodal (cyc5 xh p q r s) ∨ IsCyclicUnimodal (cyc5 xl p q r s) := by
  have n1 : p ≠ q := i1.ne (show (1 : ZMod 5) ≠ 2 by decide)
  have n2 : q ≠ r := i1.ne (show (2 : ZMod 5) ≠ 3 by decide)
  have n3 : r ≠ s := i1.ne (show (3 : ZMod 5) ≠ 4 by decide)
  have n4 : s ≠ xl := i2.ne (show (4 : ZMod 5) ≠ 0 by decide)
  have n5 : s ≠ xh := i1.ne (show (4 : ZMod 5) ≠ 0 by decide)
  simp only [not_or, not_and, not_lt] at hF
  obtain ⟨hF1, hF2⟩ := hF
  rcases lt_or_gt_of_ne n1 with c1 | c1 <;> rcases lt_or_gt_of_ne n2 with c2 | c2 <;>
  rcases lt_or_gt_of_ne n3 with c3 | c3 <;> rcases lt_or_gt_of_ne n4 with c4 | c4 <;>
  rcases lt_or_gt_of_ne n5 with c5 | c5 <;>
  first
  | (left; refine uni5 i1 ?_ ?_ ?_ ?_ ?_ <;> rintro ⟨⟨_, _⟩, ⟨_, _⟩⟩ <;> linarith)
  | (right; refine uni5 i2 ?_ ?_ ?_ ?_ ?_ <;> rintro ⟨⟨_, _⟩, ⟨_, _⟩⟩ <;> linarith)
  | (exfalso; first
      | exact absurd (hF2 c3 (by assumption) (by assumption)) (by linarith)
      | exact absurd (hF1 c3 (by assumption) (by assumption)) (by linarith))


/-! ### Geometric glue -/

theorem cyc5_cyc (z : Fin 7 → ℝ) (r : ZMod 5 → Fin 7) :
    (fun i => z (r i)) = cyc5 (z (r 0)) (z (r 1)) (z (r 2)) (z (r 3)) (z (r 4)) := by
  funext i; fin_cases i <;> rfl

theorem cyc5_inj {z : Fin 7 → ℝ} (hz : Function.Injective z) {r : ZMod 5 → Fin 7}
    (hr : Function.Injective r) :
    Function.Injective (cyc5 (z (r 0)) (z (r 1)) (z (r 2)) (z (r 3)) (z (r 4))) := by
  rw [← cyc5_cyc]; exact hz.comp hr

/-- Two edge-crossing rims at one view, one of them unimodal: Rupert. -/
theorem link_glue {x : Fin 7 → ℝ³} {u : ℝ³} (z : Fin 7 → ℝ) (hzd : ∀ v, z v = ⟪x v, u⟫)
    (hu : u ≠ 0) {d1 d2 : Fin 7} {h1 h2 : ℝ}
    {r1 r2 : ZMod 5 → Fin 7} (hR1 : EdgeRim x u d1 h1 5 r1) (hR2 : EdgeRim x u d2 h2 5 r2)
    (h : IsCyclicUnimodal (cyc5 (z (r1 0)) (z (r1 1)) (z (r1 2)) (z (r1 3)) (z (r1 4))) ∨
      IsCyclicUnimodal (cyc5 (z (r2 0)) (z (r2 1)) (z (r2 2)) (z (r2 3)) (z (r2 4)))) :
    IsRupert (Finset.univ.image x) := by
  have e : ∀ r : ZMod 5 → Fin 7, (fun i => ⟪x (r i), u⟫) = fun i => z (r i) := fun r => by
    funext i; exact (hzd _).symm
  rw [← cyc5_cyc, ← cyc5_cyc] at h
  rcases h with h | h
  · exact isRupert_edgeRim hu hR1 (Or.inl (by rw [e]; exact h))
  · exact isRupert_edgeRim hu hR2 (Or.inl (by rw [e]; exact h))

theorem ne_zero_of_inj {x : Fin 7 → ℝ³} {u : ℝ³} (hz : Function.Injective fun v => ⟪x v, u⟫)
    {a b : Fin 7} (hab : a ≠ b) : u ≠ 0 := by
  rintro rfl
  exact hab (hz (by simp))

/-! ### Link edge 06 -/

/-- **Link edge `06` at its exact edge view**: the rims `(6,4,3,2,1)` and `(0,4,3,2,1)` (EdgeRim
hypotheses, shape-only), the angles of `016` at `0`, `6` acute, no zigzag failure: Rupert. -/
theorem link06_good {x : Fin 7 → ℝ³}
    (hR6 : EdgeRim x (x 6 - x 0) 0 1 5 (rim06 6)) (hR0 : EdgeRim x (x 6 - x 0) 6 (-1) 5 (rim06 0))
    (hz : Function.Injective fun v => ⟪x v, x 6 - x 0⟫)
    (h016 : ⟪x 0 - x 1, x 6 - x 0⟫ < 0 ∧ 0 < ⟪x 6 - x 1, x 6 - x 0⟫)
    (hF : ¬ Fail06 fun v => ⟪x v, x 6 - x 0⟫) : IsRupert (Finset.univ.image x) := by
  have hu : x 6 - x 0 ≠ 0 := ne_zero_of_inj hz (show (0 : Fin 7) ≠ 1 by decide)
  refine link_glue (fun v => ⟪x v, x 6 - x 0⟫) (fun _ => rfl) hu hR6 hR0 ?_
  rw [inner_sub_left] at h016
  obtain ⟨a, b⟩ := h016
  rw [inner_sub_left] at b
  have i6 : Function.Injective (cyc5 ⟪x 6, x 6 - x 0⟫ ⟪x 4, x 6 - x 0⟫ ⟪x 3, x 6 - x 0⟫
      ⟪x 2, x 6 - x 0⟫ ⟪x 1, x 6 - x 0⟫) := cyc5_inj (r := rim06 6) hz (by decide)
  have i0 : Function.Injective (cyc5 ⟪x 0, x 6 - x 0⟫ ⟪x 4, x 6 - x 0⟫ ⟪x 3, x 6 - x 0⟫
      ⟪x 2, x 6 - x 0⟫ ⟪x 1, x 6 - x 0⟫) := cyc5_inj (r := rim06 0) hz (by decide)
  have key := coreF (xl := _) (xh := _) (by linarith) (by linarith) i6 i0 hF
  exact key

/-! ### Link edge 26 -/

def Fail26 (q : Fin 7) (z : Fin 7 → ℝ) : Prop :=
  (z 3 < z q ∧ z 0 < z q ∧ z 0 < z 1 ∧ z 3 < z 6) ∨ (z q < z 3 ∧ z q < z 0 ∧ z 1 < z 0 ∧ z 2 < z 3)

def rim26 (q X : Fin 7) : ZMod 5 → Fin 7 := ![X, 1, 0, q, 3]

theorem link26_good {x : Fin 7 → ℝ³} {q : Fin 7} (hq : q = 4 ∨ q = 5)
    (hR6 : EdgeRim x (x 6 - x 2) 2 1 5 (rim26 q 6)) (hR2 : EdgeRim x (x 6 - x 2) 6 (-1) 5 (rim26 q 2))
    (hz : Function.Injective fun v => ⟪x v, x 6 - x 2⟫)
    (h126 : ⟪x 2 - x 1, x 6 - x 2⟫ < 0 ∧ 0 < ⟪x 6 - x 1, x 6 - x 2⟫)
    (hF : ¬ Fail26 q fun v => ⟪x v, x 6 - x 2⟫) : IsRupert (Finset.univ.image x) := by
  have hu : x 6 - x 2 ≠ 0 := ne_zero_of_inj hz (show (0 : Fin 7) ≠ 1 by decide)
  refine link_glue (fun v => ⟪x v, x 6 - x 2⟫) (fun _ => rfl) hu hR6 hR2 ?_
  rw [inner_sub_left] at h126
  obtain ⟨a, b⟩ := h126
  rw [inner_sub_left] at b
  have i6 : Function.Injective (cyc5 ⟪x 6, x 6 - x 2⟫ ⟪x 1, x 6 - x 2⟫ ⟪x 0, x 6 - x 2⟫
      ⟪x q, x 6 - x 2⟫ ⟪x 3, x 6 - x 2⟫) := cyc5_inj (r := rim26 q 6) hz (by rcases hq with rfl | rfl <;> decide)
  have i2 : Function.Injective (cyc5 ⟪x 2, x 6 - x 2⟫ ⟪x 1, x 6 - x 2⟫ ⟪x 0, x 6 - x 2⟫
      ⟪x q, x 6 - x 2⟫ ⟪x 3, x 6 - x 2⟫) := cyc5_inj (r := rim26 q 2) hz (by rcases hq with rfl | rfl <;> decide)
  have key := coreB (xl := _) (xh := _) (by linarith) (by linarith) i6 i2 hF
  exact key

/-! ### Link edge 02 -/

def Fail02 (z : Fin 7 → ℝ) : Prop :=
  (z 5 < z 3 ∧ z 6 < z 3 ∧ z 6 < z 1 ∧ z 5 < z 2) ∨ (z 3 < z 5 ∧ z 3 < z 6 ∧ z 1 < z 6 ∧ z 0 < z 5)

def rim02 (X : Fin 7) : ZMod 5 → Fin 7 := ![X, 1, 6, 3, 5]

theorem link02_good {x : Fin 7 → ℝ³}
    (hR2 : EdgeRim x (x 2 - x 0) 0 1 5 (rim02 2)) (hR0 : EdgeRim x (x 2 - x 0) 2 (-1) 5 (rim02 0))
    (hz : Function.Injective fun v => ⟪x v, x 2 - x 0⟫)
    (h012 : ⟪x 0 - x 1, x 2 - x 0⟫ < 0 ∧ 0 < ⟪x 2 - x 1, x 2 - x 0⟫)
    (hF : ¬ Fail02 fun v => ⟪x v, x 2 - x 0⟫) : IsRupert (Finset.univ.image x) := by
  have hu : x 2 - x 0 ≠ 0 := ne_zero_of_inj hz (show (0 : Fin 7) ≠ 1 by decide)
  refine link_glue (fun v => ⟪x v, x 2 - x 0⟫) (fun _ => rfl) hu hR2 hR0 ?_
  rw [inner_sub_left] at h012
  obtain ⟨a, b⟩ := h012
  rw [inner_sub_left] at b
  have i2 : Function.Injective (cyc5 ⟪x 2, x 2 - x 0⟫ ⟪x 1, x 2 - x 0⟫ ⟪x 6, x 2 - x 0⟫
      ⟪x 3, x 2 - x 0⟫ ⟪x 5, x 2 - x 0⟫) := cyc5_inj (r := rim02 2) hz (by decide)
  have i0 : Function.Injective (cyc5 ⟪x 0, x 2 - x 0⟫ ⟪x 1, x 2 - x 0⟫ ⟪x 6, x 2 - x 0⟫
      ⟪x 3, x 2 - x 0⟫ ⟪x 5, x 2 - x 0⟫) := cyc5_inj (r := rim02 0) hz (by decide)
  have key := coreB (xl := _) (xh := _) (by linarith) (by linarith) i2 i0 hF
  exact key


/-! ### Six-corner rims -/

/-- The cyclic depth sequence of six reals. -/
def cyc6 (a b c d e f : ℝ) : ZMod 6 → ℝ := ![a, b, c, d, e, f]

theorem zmod6_cases (i : ZMod 6) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
  revert i; decide

theorem cyc6_0 (a b c d e f : ℝ) : cyc6 a b c d e f 0 = a := rfl
theorem cyc6_1 (a b c d e f : ℝ) : cyc6 a b c d e f 1 = b := rfl
theorem cyc6_2 (a b c d e f : ℝ) : cyc6 a b c d e f 2 = c := rfl
theorem cyc6_3 (a b c d e f : ℝ) : cyc6 a b c d e f 3 = d := rfl
theorem cyc6_4 (a b c d e f : ℝ) : cyc6 a b c d e f 4 = e := rfl
theorem cyc6_5 (a b c d e f : ℝ) : cyc6 a b c d e f 5 = f := rfl

/-- Peak test at `i` in a 6-cycle. -/
def Pk6 (z : ZMod 6 → ℝ) (i : ZMod 6) : Prop := z (i - 1) < z i ∧ z (i + 1) < z i

theorem uni6 {z : ZMod 6 → ℝ} (hinj : Function.Injective z)
    (h : ∀ i j : ZMod 6, i ≠ j → Pk6 z i → Pk6 z j → False) : IsCyclicUnimodal z :=
  isCyclicUnimodal_of_atMostOne (by norm_num) hinj fun i j hi hj => by
    by_contra hij; exact h i j hij hi hj

theorem uni6_cyc {a b c d e f : ℝ} (hinj : Function.Injective (cyc6 a b c d e f))
    (hlin : (∀ i j : ZMod 6, i ≠ j → Pk6 (cyc6 a b c d e f) i → Pk6 (cyc6 a b c d e f) j → False)) :
    IsCyclicUnimodal (cyc6 a b c d e f) := uni6 hinj hlin

set_option hygiene false in
macro "uni6_tac" hinj:term : tactic => `(tactic| (
  refine uni6_cyc $hinj ?_
  intro i j hij hi hj
  have s0 : (0 : ZMod 6) - 1 = 5 := by decide
  have s1 : (1 : ZMod 6) - 1 = 0 := by decide
  have s2 : (2 : ZMod 6) - 1 = 1 := by decide
  have s3 : (3 : ZMod 6) - 1 = 2 := by decide
  have s4 : (4 : ZMod 6) - 1 = 3 := by decide
  have s5 : (5 : ZMod 6) - 1 = 4 := by decide
  have t0 : (0 : ZMod 6) + 1 = 1 := by decide
  have t1 : (1 : ZMod 6) + 1 = 2 := by decide
  have t2 : (2 : ZMod 6) + 1 = 3 := by decide
  have t3 : (3 : ZMod 6) + 1 = 4 := by decide
  have t4 : (4 : ZMod 6) + 1 = 5 := by decide
  have t5 : (5 : ZMod 6) + 1 = 0 := by decide
  rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [Pk6, s0, s1, s2, s3, s4, s5, t0, t1, t2, t3, t4, t5, cyc6_0, cyc6_1, cyc6_2, cyc6_3, cyc6_4, cyc6_5] at hi hj hij <;>
  first | exact hij rfl | (obtain ⟨hi1, hi2⟩ := hi; obtain ⟨hj1, hj2⟩ := hj; linarith)))


set_option maxHeartbeats 0 in
theorem coreF6 {xl xh p q r t s : ℝ} (hl : xl < s) (hh : s < xh)
    (i1 : Function.Injective (cyc6 xh p q r t s)) (i2 : Function.Injective (cyc6 xl p q r t s))
    (hF1 : ¬ (((p<q ∧ r<q ∧ t<r ∧ t<s) ∨ (p<q ∧ q<r ∧ t<r ∧ t<s) ∨ (p<q ∧ r<q ∧ r<t ∧ t<s)) ∧ p < xh)) (hF2 : ¬ (((q<p ∧ q<r ∧ r<t ∧ s<t) ∨ (q<p ∧ r<q ∧ r<t ∧ s<t) ∨ (q<p ∧ q<r ∧ t<r ∧ s<t)) ∧ xl < p))
    (hF3 : ¬ ((p<q ∧ r<q ∧ r<t ∧ s<t) ∨ (q<p ∧ q<r ∧ t<r ∧ t<s))) :
    IsCyclicUnimodal (cyc6 xh p q r t s) ∨ IsCyclicUnimodal (cyc6 xl p q r t s) := by
  have n1 : p ≠ q := i1.ne (show (1 : ZMod 6) ≠ 2 by decide)
  have n2 : q ≠ r := i1.ne (show (2 : ZMod 6) ≠ 3 by decide)
  have n3 : r ≠ t := i1.ne (show (3 : ZMod 6) ≠ 4 by decide)
  have n4 : t ≠ s := i1.ne (show (4 : ZMod 6) ≠ 5 by decide)
  have n5 : p ≠ xl := i2.ne (show (1 : ZMod 6) ≠ 0 by decide)
  have n6 : p ≠ xh := i1.ne (show (1 : ZMod 6) ≠ 0 by decide)
  rcases lt_or_gt_of_ne n1 with c1 | c1 <;> rcases lt_or_gt_of_ne n2 with c2 | c2 <;>
  rcases lt_or_gt_of_ne n3 with c3 | c3 <;> rcases lt_or_gt_of_ne n4 with c4 | c4 <;>
  rcases lt_or_gt_of_ne n5 with c5 | c5 <;> rcases lt_or_gt_of_ne n6 with c6 | c6 <;>
  first
  | (left; uni6_tac i1)
  | (right; uni6_tac i2)
  | (exfalso; first
      | (refine hF1 ⟨Or.inl ⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> assumption)
      | (refine hF1 ⟨Or.inr (Or.inl ⟨?_, ?_, ?_, ?_⟩), ?_⟩ <;> assumption)
      | (refine hF1 ⟨Or.inr (Or.inr ⟨?_, ?_, ?_, ?_⟩), ?_⟩ <;> assumption)
      | (refine hF2 ⟨Or.inl ⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> assumption)
      | (refine hF2 ⟨Or.inr (Or.inl ⟨?_, ?_, ?_, ?_⟩), ?_⟩ <;> assumption)
      | (refine hF2 ⟨Or.inr (Or.inr ⟨?_, ?_, ?_, ?_⟩), ?_⟩ <;> assumption)
      | (refine hF3 (Or.inl ⟨?_, ?_, ?_, ?_⟩) <;> assumption)
      | (refine hF3 (Or.inr ⟨?_, ?_, ?_, ?_⟩)) <;> assumption)

set_option maxHeartbeats 0 in
theorem coreB6 {xl xh p q r t s : ℝ} (hl : xl < p) (hh : p < xh)
    (i1 : Function.Injective (cyc6 xh p q r t s)) (i2 : Function.Injective (cyc6 xl p q r t s))
    (hF1 : ¬ (((p<q ∧ r<q ∧ t<r ∧ t<s) ∨ (p<q ∧ q<r ∧ t<r ∧ t<s) ∨ (p<q ∧ r<q ∧ r<t ∧ t<s)) ∧ xl < s)) (hF2 : ¬ (((q<p ∧ q<r ∧ r<t ∧ s<t) ∨ (q<p ∧ r<q ∧ r<t ∧ s<t) ∨ (q<p ∧ q<r ∧ t<r ∧ s<t)) ∧ s < xh))
    (hF3 : ¬ ((p<q ∧ r<q ∧ r<t ∧ s<t) ∨ (q<p ∧ q<r ∧ t<r ∧ t<s))) :
    IsCyclicUnimodal (cyc6 xh p q r t s) ∨ IsCyclicUnimodal (cyc6 xl p q r t s) := by
  have n1 : p ≠ q := i1.ne (show (1 : ZMod 6) ≠ 2 by decide)
  have n2 : q ≠ r := i1.ne (show (2 : ZMod 6) ≠ 3 by decide)
  have n3 : r ≠ t := i1.ne (show (3 : ZMod 6) ≠ 4 by decide)
  have n4 : t ≠ s := i1.ne (show (4 : ZMod 6) ≠ 5 by decide)
  have n5 : s ≠ xl := i2.ne (show (5 : ZMod 6) ≠ 0 by decide)
  have n6 : s ≠ xh := i1.ne (show (5 : ZMod 6) ≠ 0 by decide)
  rcases lt_or_gt_of_ne n1 with c1 | c1 <;> rcases lt_or_gt_of_ne n2 with c2 | c2 <;>
  rcases lt_or_gt_of_ne n3 with c3 | c3 <;> rcases lt_or_gt_of_ne n4 with c4 | c4 <;>
  rcases lt_or_gt_of_ne n5 with c5 | c5 <;> rcases lt_or_gt_of_ne n6 with c6 | c6 <;>
  first
  | (left; uni6_tac i1)
  | (right; uni6_tac i2)
  | (exfalso; first
      | (refine hF1 ⟨Or.inl ⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> assumption)
      | (refine hF1 ⟨Or.inr (Or.inl ⟨?_, ?_, ?_, ?_⟩), ?_⟩ <;> assumption)
      | (refine hF1 ⟨Or.inr (Or.inr ⟨?_, ?_, ?_, ?_⟩), ?_⟩ <;> assumption)
      | (refine hF2 ⟨Or.inl ⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> assumption)
      | (refine hF2 ⟨Or.inr (Or.inl ⟨?_, ?_, ?_, ?_⟩), ?_⟩ <;> assumption)
      | (refine hF2 ⟨Or.inr (Or.inr ⟨?_, ?_, ?_, ?_⟩), ?_⟩ <;> assumption)
      | (refine hF3 (Or.inl ⟨?_, ?_, ?_, ?_⟩) <;> assumption)
      | (refine hF3 (Or.inr ⟨?_, ?_, ?_, ?_⟩)) <;> assumption)


/-! ### Six-corner glue and the 6-rim link theorems -/

def PV6 (p q r t s : ℝ) : Prop :=
  (p<q ∧ r<q ∧ t<r ∧ t<s) ∨ (p<q ∧ q<r ∧ t<r ∧ t<s) ∨ (p<q ∧ r<q ∧ r<t ∧ t<s)
def VP6 (p q r t s : ℝ) : Prop :=
  (q<p ∧ q<r ∧ r<t ∧ s<t) ∨ (q<p ∧ r<q ∧ r<t ∧ s<t) ∨ (q<p ∧ q<r ∧ t<r ∧ s<t)
def K36 (p q r t s : ℝ) : Prop :=
  (p<q ∧ r<q ∧ r<t ∧ s<t) ∨ (q<p ∧ q<r ∧ t<r ∧ t<s)

theorem cyc6_cyc (z : Fin 7 → ℝ) (r : ZMod 6 → Fin 7) :
    (fun i => z (r i)) = cyc6 (z (r 0)) (z (r 1)) (z (r 2)) (z (r 3)) (z (r 4)) (z (r 5)) := by
  funext i; fin_cases i <;> rfl

theorem cyc6_inj {z : Fin 7 → ℝ} (hz : Function.Injective z) {r : ZMod 6 → Fin 7}
    (hr : Function.Injective r) :
    Function.Injective (cyc6 (z (r 0)) (z (r 1)) (z (r 2)) (z (r 3)) (z (r 4)) (z (r 5))) := by
  rw [← cyc6_cyc]; exact hz.comp hr

theorem link_glue6 {x : Fin 7 → ℝ³} {u : ℝ³} (z : Fin 7 → ℝ) (hzd : ∀ v, z v = ⟪x v, u⟫)
    (hu : u ≠ 0) {d1 d2 : Fin 7} {h1 h2 : ℝ}
    {r1 r2 : ZMod 6 → Fin 7} (hR1 : EdgeRim x u d1 h1 6 r1) (hR2 : EdgeRim x u d2 h2 6 r2)
    (h : IsCyclicUnimodal (cyc6 (z (r1 0)) (z (r1 1)) (z (r1 2)) (z (r1 3)) (z (r1 4)) (z (r1 5))) ∨
      IsCyclicUnimodal (cyc6 (z (r2 0)) (z (r2 1)) (z (r2 2)) (z (r2 3)) (z (r2 4)) (z (r2 5)))) :
    IsRupert (Finset.univ.image x) := by
  have e : ∀ r : ZMod 6 → Fin 7, (fun i => ⟪x (r i), u⟫) = fun i => z (r i) := fun r => by
    funext i; exact (hzd _).symm
  rw [← cyc6_cyc, ← cyc6_cyc] at h
  rcases h with h | h
  · exact isRupert_edgeRim hu hR1 (Or.inl (by rw [e]; exact h))
  · exact isRupert_edgeRim hu hR2 (Or.inl (by rw [e]; exact h))

def Fail06' (z : Fin 7 → ℝ) : Prop :=
  (PV6 (z 4) (z 3) (z 5) (z 2) (z 1) ∧ z 4 < z 6) ∨ (VP6 (z 4) (z 3) (z 5) (z 2) (z 1) ∧ z 0 < z 4) ∨
    K36 (z 4) (z 3) (z 5) (z 2) (z 1)

def rim06' (X : Fin 7) : ZMod 6 → Fin 7 := ![X, 4, 3, 5, 2, 1]

/-- **Link edge `06`, six-corner rims `(X, 4, 3, 5, 2, 1)`**. -/
theorem link06_good6 {x : Fin 7 → ℝ³}
    (hR6 : EdgeRim x (x 6 - x 0) 0 1 6 (rim06' 6)) (hR0 : EdgeRim x (x 6 - x 0) 6 (-1) 6 (rim06' 0))
    (hz : Function.Injective fun v => ⟪x v, x 6 - x 0⟫)
    (h016 : ⟪x 0 - x 1, x 6 - x 0⟫ < 0 ∧ 0 < ⟪x 6 - x 1, x 6 - x 0⟫)
    (hF : ¬ Fail06' fun v => ⟪x v, x 6 - x 0⟫) : IsRupert (Finset.univ.image x) := by
  have hu : x 6 - x 0 ≠ 0 := ne_zero_of_inj hz (show (0 : Fin 7) ≠ 1 by decide)
  refine link_glue6 (fun v => ⟪x v, x 6 - x 0⟫) (fun _ => rfl) hu hR6 hR0 ?_
  rw [inner_sub_left] at h016
  obtain ⟨a, b⟩ := h016
  rw [inner_sub_left] at b
  have i6 : Function.Injective (cyc6 ⟪x 6, x 6 - x 0⟫ ⟪x 4, x 6 - x 0⟫ ⟪x 3, x 6 - x 0⟫
      ⟪x 5, x 6 - x 0⟫ ⟪x 2, x 6 - x 0⟫ ⟪x 1, x 6 - x 0⟫) := cyc6_inj (r := rim06' 6) hz (by decide)
  have i0 : Function.Injective (cyc6 ⟪x 0, x 6 - x 0⟫ ⟪x 4, x 6 - x 0⟫ ⟪x 3, x 6 - x 0⟫
      ⟪x 5, x 6 - x 0⟫ ⟪x 2, x 6 - x 0⟫ ⟪x 1, x 6 - x 0⟫) := cyc6_inj (r := rim06' 0) hz (by decide)
  simp only [Fail06', not_or] at hF
  obtain ⟨hF1, hF2, hF3⟩ := hF
  have key := coreF6 (xl := _) (xh := _) (by linarith) (by linarith) i6 i0 hF1 hF2 hF3
  exact key

def Fail02' (z : Fin 7 → ℝ) : Prop :=
  (PV6 (z 1) (z 6) (z 4) (z 3) (z 5) ∧ z 0 < z 5) ∨ (VP6 (z 1) (z 6) (z 4) (z 3) (z 5) ∧ z 5 < z 2) ∨
    K36 (z 1) (z 6) (z 4) (z 3) (z 5)

def rim02' (X : Fin 7) : ZMod 6 → Fin 7 := ![X, 1, 6, 4, 3, 5]

/-- **Link edge `02`, six-corner rims `(X, 1, 6, 4, 3, 5)`**. -/
theorem link02_good6 {x : Fin 7 → ℝ³}
    (hR2 : EdgeRim x (x 2 - x 0) 0 1 6 (rim02' 2)) (hR0 : EdgeRim x (x 2 - x 0) 2 (-1) 6 (rim02' 0))
    (hz : Function.Injective fun v => ⟪x v, x 2 - x 0⟫)
    (h012 : ⟪x 0 - x 1, x 2 - x 0⟫ < 0 ∧ 0 < ⟪x 2 - x 1, x 2 - x 0⟫)
    (hF : ¬ Fail02' fun v => ⟪x v, x 2 - x 0⟫) : IsRupert (Finset.univ.image x) := by
  have hu : x 2 - x 0 ≠ 0 := ne_zero_of_inj hz (show (0 : Fin 7) ≠ 1 by decide)
  refine link_glue6 (fun v => ⟪x v, x 2 - x 0⟫) (fun _ => rfl) hu hR2 hR0 ?_
  rw [inner_sub_left] at h012
  obtain ⟨a, b⟩ := h012
  rw [inner_sub_left] at b
  have i2 : Function.Injective (cyc6 ⟪x 2, x 2 - x 0⟫ ⟪x 1, x 2 - x 0⟫ ⟪x 6, x 2 - x 0⟫
      ⟪x 4, x 2 - x 0⟫ ⟪x 3, x 2 - x 0⟫ ⟪x 5, x 2 - x 0⟫) := cyc6_inj (r := rim02' 2) hz (by decide)
  have i0 : Function.Injective (cyc6 ⟪x 0, x 2 - x 0⟫ ⟪x 1, x 2 - x 0⟫ ⟪x 6, x 2 - x 0⟫
      ⟪x 4, x 2 - x 0⟫ ⟪x 3, x 2 - x 0⟫ ⟪x 5, x 2 - x 0⟫) := cyc6_inj (r := rim02' 0) hz (by decide)
  simp only [Fail02', not_or] at hF
  obtain ⟨hF1, hF2, hF3⟩ := hF
  have key := coreB6 (xl := _) (xh := _) (by linarith) (by linarith) i2 i0 hF1 hF2 hF3
  exact key

end Link24
end Minimality
