module

public import Minimality.Type08S.GT_Wrap16

@[expose] public section

set_option relaxedAutoImplicit true

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- 4-cycle `(w, a, r, g)` with two adjacent low and two adjacent high vertices. -/
def Q4A (z : ZMod 4 → ℝ) : Prop := z 0 < z 2 ∧ z 0 < z 3 ∧ z 1 < z 2 ∧ z 1 < z 3

theorem Q4A_open : IsOpen {z : ZMod 4 → ℝ | Q4A z} := by
  have h : ∀ i j : ZMod 4, IsOpen {z : ZMod 4 → ℝ | z i < z j} :=
    fun i j => isOpen_lt (continuous_apply i) (continuous_apply j)
  exact (h 0 2).inter ((h 0 3).inter ((h 1 2).inter (h 1 3)))

theorem Q4A_smul {z : ZMod 4 → ℝ} {c : ℝ} (hc : 0 < c) (h : Q4A z) : Q4A (fun i => c * z i) :=
  ⟨mul_lt_mul_of_pos_left h.1 hc, mul_lt_mul_of_pos_left h.2.1 hc,
    mul_lt_mul_of_pos_left h.2.2.1 hc, mul_lt_mul_of_pos_left h.2.2.2 hc⟩

theorem Q4A_shift {z : ZMod 4 → ℝ} (k : ℝ) (h : Q4A z) : Q4A (fun i => z i + k) :=
  ⟨by linarith [h.1], by linarith [h.2.1], by linarith [h.2.2.1], by linarith [h.2.2.2]⟩

theorem Q4A_unimodal {z : ZMod 4 → ℝ} (hinj : Function.Injective z) (h : Q4A z) :
    IsCyclicUnimodal z := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have n01 : z 0 ≠ z 1 := fun e => by have := hinj e; revert this; decide
  have n23 : z 2 ≠ z 3 := fun e => by have := hinj e; revert this; decide
  have c1 : (0 : ZMod 4) - 1 = 3 := by decide
  have c2 : (1 : ZMod 4) - 1 = 0 := by decide
  have c3 : (2 : ZMod 4) - 1 = 1 := by decide
  have c4 : (3 : ZMod 4) - 1 = 2 := by decide
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  rcases lt_or_gt_of_ne n23 with l | l
  · refine isCyclicUnimodal_of_top (by norm_num) hinj 3 ?_
    intro i hi
    rcases zmod4_cases i with rfl | rfl | rfl | rfl
    · left; rw [c1]; exact h2
    · right; rw [a1]; exact h3
    · right; rw [a2]; exact l
    · exact absurd rfl hi
  · refine isCyclicUnimodal_of_top (by norm_num) hinj 2 ?_
    intro i hi
    rcases zmod4_cases i with rfl | rfl | rfl | rfl
    · left; rw [c1]; exact h2
    · right; rw [a1]; exact h3
    · exact absurd rfl hi
    · left; rw [c4]; exact l


/-- The cycle `(w, a, r, g)` of case A (the shadow polygon, `a` above the corner `f`). -/
def aPts (zw b1 b2 a3 r1 r2 A : ℝ) : ZMod 4 → V3 :=
  quad ⟨0, 0, zw⟩ ⟨b1, b2, a3⟩ ⟨r1, r2, 0⟩ ⟨A, 0, 0⟩

section ATests
variable {px py t zv zw mp b1 b2 a3 r1 r2 A : ℝ}

theorem ta_cyc (q1 : 0 < r1 * b2 - r2 * b1) (q2 : 0 < (r1 - b1) * b2 + (r2 - b2) * (A - b1))
    (q3 : 0 < A * r2) (q4 : 0 < b2 * A) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      LexTest (-1) ⟨0, 0, 1⟩ ⟨px, py, 0⟩ (aPts zw b1 b2 a3 r1 r2 A i)
        (aPts zw b1 b2 a3 r1 r2 A (i + 1)) (aPts zw b1 b2 a3 r1 r2 A j) := by
  intro i j h1 h2
  obtain ⟨b0, b1', b2', b3⟩ := zmod4_add_one
  rcases zmod4_pairs i j h1 h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [aPts, b0, b1', b2', b3, quad_0, quad_1, quad_2, quad_3, LexTest, tst, hdet] <;>
    left <;> nlinarith

theorem ta_b (hzv : 0 ≤ zv) (hzw : zw < 0)
    (t1 : 0 < py * b1 - px * b2) (t2 : 0 < -(py * A))
    (q1 : 0 < r1 * b2 - r2 * b1) (q3 : 0 < A * r2) :
    ∀ i : ZMod 4, LexTest (-1) ⟨0, 0, 1⟩ ⟨px, py, 0⟩ (aPts zw b1 b2 a3 r1 r2 A i)
        (aPts zw b1 b2 a3 r1 r2 A (i + 1)) ⟨0, 0, zv⟩ := by
  have hU : 0 < zv - zw := by linarith
  have a1 := mul_pos hU t1
  have a2 := mul_pos hU t2
  obtain ⟨b0, b1', b2', b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    simp only [aPts, b0, b1', b2', b3, quad_0, quad_1, quad_2, quad_3, LexTest, tst, hdet] <;>
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem ta_a' (ht0 : 0 < t) (ht1 : t < 1) (hzv : 0 ≤ zv) (hzw : zw < 0) (hmp : (1 - t) * zv < mp)
    (t2 : 0 < -(py * A)) (hA : 0 < A) (hb2 : 0 < b2)
    (q1 : 0 < r1 * b2 - r2 * b1) (q2 : 0 < (r1 - b1) * b2 + (r2 - b2) * (A - b1))
    (q3 : 0 < A * r2) :
    ∀ i : ZMod 4, LexTest (-1) ⟨0, 0, 1⟩ ⟨px, py, 0⟩ (aPts zw b1 b2 a3 r1 r2 A i)
        (aPts zw b1 b2 a3 r1 r2 A (i + 1)) ⟨t * A, 0, mp⟩ := by
  have ht1' : 0 < 1 - t := by linarith
  have h0 : 0 ≤ (1 - t) * zv := mul_nonneg ht1'.le hzv
  have hK : 0 < mp - (1 - t) * zw := by nlinarith
  have a1 := mul_pos hK t2
  have a2 := mul_pos (mul_pos ht0 hA) hb2
  have a3' := mul_pos ht0 q2
  have a4 := mul_pos ht1' q1
  have a5 := mul_pos ht1' q3
  obtain ⟨b0, b1', b2', b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    simp only [aPts, b0, b1', b2', b3, quad_0, quad_1, quad_2, quad_3, LexTest, tst, hdet] <;>
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem ta_c' (ha3 : a3 < 0)
    (t1 : 0 < py * b1 - px * b2) (t3 : 0 < (r1 - b1) * py - (r2 - b2) * px)
    (q2 : 0 < (r1 - b1) * b2 + (r2 - b2) * (A - b1)) (q4 : 0 < b2 * A) :
    ∀ i : ZMod 4, LexTest (-1) ⟨0, 0, 1⟩ ⟨px, py, 0⟩ (aPts zw b1 b2 a3 r1 r2 A i)
        (aPts zw b1 b2 a3 r1 r2 A (i + 1)) ⟨b1, b2, 0⟩ := by
  have a1 := mul_pos_of_neg_of_neg ha3 (neg_neg_of_pos t1)
  have a2 := mul_neg_of_neg_of_pos ha3 t1
  have a3' := mul_neg_of_neg_of_pos ha3 t3
  obtain ⟨b0, b1', b2', b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    simp only [aPts, b0, b1', b2', b3, quad_0, quad_1, quad_2, quad_3, LexTest, tst, hdet] <;>
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

end ATests


end Type08Sp

namespace HFrame
open Type08Sp
variable {vb g u0 N : ℝ³} {fG : ℝ³ → ℝ} (Fr : HFrame vb g u0 N fG)
include Fr

/-- **Case A core** (`T'`, `r2 > b2`): cycle `(w, a, r, g)` = `(d, a, b', c)`, the tilt `(px, py)` in `-int T_p`
with `(r - f) x (px, py) > 0` (`t3`); `b`, `c'`, `a'` are hidden. -/
theorem tp_A {V : Finset ℝ³} {bP aP' fP rP gP wP aP : ℝ³}
    {px py t zv zw mp A b1 b2 r1 r2 a3 : ℝ}
    (hV : ∀ y ∈ V, y = bP ∨ y = aP' ∨ y = fP ∨ y = rP ∨ y = gP ∨ y = wP ∨ y = aP)
    (hw : wP ∈ V) (ha : aP ∈ V) (hr : rP ∈ V) (hg : gP ∈ V)
    (Φb : hfΦ vb g u0 fG bP = ⟨0, 0, zv⟩) (Φa' : hfΦ vb g u0 fG aP' = ⟨t * A, 0, mp⟩)
    (Φf : hfΦ vb g u0 fG fP = ⟨b1, b2, 0⟩) (Φr : hfΦ vb g u0 fG rP = ⟨r1, r2, 0⟩)
    (Φg : hfΦ vb g u0 fG gP = ⟨A, 0, 0⟩) (Φw : hfΦ vb g u0 fG wP = ⟨0, 0, zw⟩)
    (Φa : hfΦ vb g u0 fG aP = ⟨b1, b2, a3⟩)
    (hA : 0 < A) (hb2 : 0 < b2) (hr2 : 0 < r2) (ht0 : 0 < t) (ht1 : t < 1) (hzv : 0 ≤ zv)
    (hzw : zw < 0) (ha3 : a3 < 0) (hmp : (1 - t) * zv < mp)
    (q1 : 0 < r1 * b2 - r2 * b1) (q2 : 0 < (r1 - b1) * b2 + (r2 - b2) * (A - b1))
    (t1 : 0 < py * b1 - px * b2) (t2 : 0 < -(py * A))
    (t3 : 0 < (r1 - b1) * py - (r2 - b2) * px) :
    IsRupert V := by
  have q3 : 0 < A * r2 := mul_pos hA hr2
  have q4 : 0 < b2 * A := mul_pos hb2 hA
  have himg : ∀ i : ZMod 4, hfΦ vb g u0 fG (quad wP aP rP gP i) = aPts zw b1 b2 a3 r1 r2 A i := by
    intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl
    · rw [quad_0, Φw]; rfl
    · rw [quad_1, Φa]; rfl
    · rw [quad_2, Φr]; rfl
    · rw [quad_3, Φg]; rfl
  have hE := Fr.hee
  have hM := Fr.hNN
  have hU := Fr.hu
  refine Fr.rupert_coords V (k := 4) (by norm_num) (quad wP aP rP gP) ?_ (-1) ⟨0, 0, 1⟩ ⟨px, py, 0⟩
    (Or.inr (Or.inr one_ne_zero)) ?_ ?_ Q4A Q4A_open (fun z c hc => Q4A_smul hc)
    (fun z K => Q4A_shift K) (fun z hinj => Q4A_unimodal hinj) ?_
  · intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl
    exacts [hw, ha, hr, hg]
  · intro i j h1 h2
    rw [himg i, himg (i + 1), himg j]
    exact ta_cyc q1 q2 q3 q4 i j h1 h2
  · intro y hy hyx i
    rw [himg i, himg (i + 1)]
    rcases hV y hy with h | h | h | h | h | h | h
    · rw [h, Φb]; exact ta_b hzv hzw t1 t2 q1 q3 i
    · rw [h, Φa']; exact ta_a' ht0 ht1 hzv hzw hmp t2 hA hb2 q1 q2 q3 i
    · rw [h, Φf]; exact ta_c' ha3 t1 t3 q2 q4 i
    · exact absurd h (hyx 2)
    · exact absurd h (hyx 3)
    · exact absurd h (hyx 0)
    · exact absurd h (hyx 1)
  · set E := ⟪hfE vb g u0, hfE vb g u0⟫ with hEd
    set M := ⟪N, N⟫ with hMd
    set U := ⟪u0, u0⟫ with hUd
    have hL : ∀ (c : V3) (i : ZMod 4), lin E M U c (hfΦ vb g u0 fG (quad wP aP rP gP i)) =
        c.x / E * (aPts zw b1 b2 a3 r1 r2 A i).x + c.y / M * (aPts zw b1 b2 a3 r1 r2 A i).y +
          c.z / U * (aPts zw b1 b2 a3 r1 r2 A i).z := by
      intro c i; rw [himg i]; rfl
    have s0 : aPts zw b1 b2 a3 r1 r2 A 0 = ⟨0, 0, zw⟩ := rfl
    have s1 : aPts zw b1 b2 a3 r1 r2 A 1 = ⟨b1, b2, a3⟩ := rfl
    have s2 : aPts zw b1 b2 a3 r1 r2 A 2 = ⟨r1, r2, 0⟩ := rfl
    have s3 : aPts zw b1 b2 a3 r1 r2 A 3 = ⟨A, 0, 0⟩ := rfl
    have hzU : zw / U < 0 := div_neg_of_neg_of_pos hzw hU
    have haU : a3 / U < 0 := div_neg_of_neg_of_pos ha3 hU
    have k1 := eventually_pos_affine (A := 0 - zw / U) (B := (px / E * r1 + py / M * r2) -
      (px / E * 0 + py / M * 0)) (Or.inl (by linarith))
    have k2 := eventually_pos_affine (A := 0 - zw / U) (B := (px / E * A + py / M * 0) -
      (px / E * 0 + py / M * 0)) (Or.inl (by linarith))
    have k3 := eventually_pos_affine (A := 0 - a3 / U) (B := (px / E * r1 + py / M * r2) -
      (px / E * b1 + py / M * b2)) (Or.inl (by linarith))
    have k4 := eventually_pos_affine (A := 0 - a3 / U) (B := (px / E * A + py / M * 0) -
      (px / E * b1 + py / M * b2)) (Or.inl (by linarith))
    filter_upwards [k1, k2, k3, k4] with t' a1' a2' a3' a4'
    simp only [Q4A, hL, s0, s1, s2, s3]
    refine ⟨by (ring_nf at *; linarith), by (ring_nf at *; linarith), by (ring_nf at *; linarith),
      by (ring_nf at *; linarith)⟩

end HFrame

end Minimality
