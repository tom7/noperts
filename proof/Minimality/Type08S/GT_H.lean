module

public import Minimality.Type08S.GT_Facts

@[expose] public section

set_option autoImplicit true

/-!
# GT, group D: Proposition H (sp08b §3) in frame coordinates

Base view `e` (frame coordinates `cu = (1,0,0)`), tilt `d = -e_y ∓ t e_z` (`cw = (0,-1,∓t)`,
`t > 0` small, chosen by the proof).  Screen of the base view: `(y, z)`; depth: first `x`, then the
tilt value.  Frame (`HFrame vb g u0 N fG`, vertices as in `sPts`): `v = (0,0,zv)`, `w = (0,0,zw)`,
`zw < 0 ≤ zv`, `G`'s far corner `g = (A, 0, 0)`, `A > 0`, `h = (b1, b2, 0)`, `b2 > 0`,
`r = (r1, r2, 0)`, `r2 > 0`.  Statements are given per cycle of the table of §3; the picture
hypotheses are exactly the strict facts of P_N2 / P_T4 (and Lemmas 1.1, 1.2 as hypotheses).
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- The 2D orientation test of the base view `e`: screen `(y, z)`. -/
def crossYZ (P Q S : V3) : ℝ := (Q.y - P.y) * (S.z - P.z) - (Q.z - P.z) * (S.y - P.y)

/-- Open depth condition of the cycle `(a', c, 2, a, c')`: `c' > a' > c` and `a > 2`. -/
def QH5 (z : ZMod 5 → ℝ) : Prop := z 0 < z 4 ∧ z 1 < z 0 ∧ z 2 < z 3

/-- Open depth condition of the 4-cycle `(a', c, 2, b)`: `c` below `a'` and `2`, `b` above both. -/
def QH4 (z : ZMod 4 → ℝ) : Prop := z 1 < z 0 ∧ z 1 < z 2 ∧ z 0 < z 3 ∧ z 2 < z 3

/-- `(2, b, a', b', a)`: increasing `2 < b < a' < b'`, `a < b'`. -/
def QT5a (z : ZMod 5 → ℝ) : Prop := z 0 < z 1 ∧ z 1 < z 2 ∧ z 2 < z 3 ∧ z 4 < z 3
/-- `(2, b, a', c', a)`: `2 < b < a'`, `2 < a < c'`. -/
def QT5b (z : ZMod 5 → ℝ) : Prop := z 0 < z 1 ∧ z 1 < z 2 ∧ z 0 < z 4 ∧ z 4 < z 3
/-- `(2, b, c', a)`: `2 < b < c'`, `2 < a < c'`. -/
def QT4 (z : ZMod 4 → ℝ) : Prop := z 0 < z 1 ∧ z 1 < z 2 ∧ z 3 < z 2 ∧ z 0 < z 3

section Qlemmas

theorem QH5_open : IsOpen {z : ZMod 5 → ℝ | QH5 z} := by
  have h : ∀ i j : ZMod 5, IsOpen {z : ZMod 5 → ℝ | z i < z j} :=
    fun i j => isOpen_lt (continuous_apply i) (continuous_apply j)
  exact (h 0 4).inter ((h 1 0).inter (h 2 3))
theorem QH4_open : IsOpen {z : ZMod 4 → ℝ | QH4 z} := by
  have h : ∀ i j : ZMod 4, IsOpen {z : ZMod 4 → ℝ | z i < z j} :=
    fun i j => isOpen_lt (continuous_apply i) (continuous_apply j)
  exact (h 1 0).inter ((h 1 2).inter ((h 0 3).inter (h 2 3)))
theorem QT5a_open : IsOpen {z : ZMod 5 → ℝ | QT5a z} := by
  have h : ∀ i j : ZMod 5, IsOpen {z : ZMod 5 → ℝ | z i < z j} :=
    fun i j => isOpen_lt (continuous_apply i) (continuous_apply j)
  exact (h 0 1).inter ((h 1 2).inter ((h 2 3).inter (h 4 3)))
theorem QT5b_open : IsOpen {z : ZMod 5 → ℝ | QT5b z} := by
  have h : ∀ i j : ZMod 5, IsOpen {z : ZMod 5 → ℝ | z i < z j} :=
    fun i j => isOpen_lt (continuous_apply i) (continuous_apply j)
  exact (h 0 1).inter ((h 1 2).inter ((h 0 4).inter (h 4 3)))
theorem QT4_open : IsOpen {z : ZMod 4 → ℝ | QT4 z} := by
  have h : ∀ i j : ZMod 4, IsOpen {z : ZMod 4 → ℝ | z i < z j} :=
    fun i j => isOpen_lt (continuous_apply i) (continuous_apply j)
  exact (h 0 1).inter ((h 1 2).inter ((h 3 2).inter (h 0 3)))

theorem QH5_smul {z : ZMod 5 → ℝ} {c : ℝ} (hc : 0 < c) (h : QH5 z) : QH5 (fun i => c * z i) :=
  ⟨mul_lt_mul_of_pos_left h.1 hc, mul_lt_mul_of_pos_left h.2.1 hc, mul_lt_mul_of_pos_left h.2.2 hc⟩
theorem QH4_smul {z : ZMod 4 → ℝ} {c : ℝ} (hc : 0 < c) (h : QH4 z) : QH4 (fun i => c * z i) :=
  ⟨mul_lt_mul_of_pos_left h.1 hc, mul_lt_mul_of_pos_left h.2.1 hc,
    mul_lt_mul_of_pos_left h.2.2.1 hc, mul_lt_mul_of_pos_left h.2.2.2 hc⟩
theorem QT5a_smul {z : ZMod 5 → ℝ} {c : ℝ} (hc : 0 < c) (h : QT5a z) : QT5a (fun i => c * z i) :=
  ⟨mul_lt_mul_of_pos_left h.1 hc, mul_lt_mul_of_pos_left h.2.1 hc,
    mul_lt_mul_of_pos_left h.2.2.1 hc, mul_lt_mul_of_pos_left h.2.2.2 hc⟩
theorem QT5b_smul {z : ZMod 5 → ℝ} {c : ℝ} (hc : 0 < c) (h : QT5b z) : QT5b (fun i => c * z i) :=
  ⟨mul_lt_mul_of_pos_left h.1 hc, mul_lt_mul_of_pos_left h.2.1 hc,
    mul_lt_mul_of_pos_left h.2.2.1 hc, mul_lt_mul_of_pos_left h.2.2.2 hc⟩
theorem QT4_smul {z : ZMod 4 → ℝ} {c : ℝ} (hc : 0 < c) (h : QT4 z) : QT4 (fun i => c * z i) :=
  ⟨mul_lt_mul_of_pos_left h.1 hc, mul_lt_mul_of_pos_left h.2.1 hc,
    mul_lt_mul_of_pos_left h.2.2.1 hc, mul_lt_mul_of_pos_left h.2.2.2 hc⟩

theorem QH5_shift {z : ZMod 5 → ℝ} (k : ℝ) (h : QH5 z) : QH5 (fun i => z i + k) :=
  ⟨by linarith [h.1], by linarith [h.2.1], by linarith [h.2.2]⟩
theorem QH4_shift {z : ZMod 4 → ℝ} (k : ℝ) (h : QH4 z) : QH4 (fun i => z i + k) :=
  ⟨by linarith [h.1], by linarith [h.2.1], by linarith [h.2.2.1], by linarith [h.2.2.2]⟩
theorem QT5a_shift {z : ZMod 5 → ℝ} (k : ℝ) (h : QT5a z) : QT5a (fun i => z i + k) :=
  ⟨by linarith [h.1], by linarith [h.2.1], by linarith [h.2.2.1], by linarith [h.2.2.2]⟩
theorem QT5b_shift {z : ZMod 5 → ℝ} (k : ℝ) (h : QT5b z) : QT5b (fun i => z i + k) :=
  ⟨by linarith [h.1], by linarith [h.2.1], by linarith [h.2.2.1], by linarith [h.2.2.2]⟩
theorem QT4_shift {z : ZMod 4 → ℝ} (k : ℝ) (h : QT4 z) : QT4 (fun i => z i + k) :=
  ⟨by linarith [h.1], by linarith [h.2.1], by linarith [h.2.2.1], by linarith [h.2.2.2]⟩

theorem QH4_unimodal {z : ZMod 4 → ℝ} (hinj : Function.Injective z) (h : QH4 z) :
    IsCyclicUnimodal z := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have c1 : (0 : ZMod 4) - 1 = 3 := by decide
  have c2 : (1 : ZMod 4) - 1 = 0 := by decide
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  refine isCyclicUnimodal_of_top (by norm_num) hinj 3 ?_
  intro i hi
  rcases zmod4_cases i with rfl | rfl | rfl | rfl
  · left; rw [c1]; exact h3
  · left; rw [c2]; exact h1
  · right; rw [a2]; exact h4
  · exact absurd rfl hi

theorem QT4_unimodal {z : ZMod 4 → ℝ} (hinj : Function.Injective z) (h : QT4 z) :
    IsCyclicUnimodal z := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have c4 : (3 : ZMod 4) - 1 = 2 := by decide
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  refine isCyclicUnimodal_of_top (by norm_num) hinj 2 ?_
  intro i hi
  rcases zmod4_cases i with rfl | rfl | rfl | rfl
  · right; rw [a0]; exact h1
  · right; rw [a1]; exact h2
  · exact absurd rfl hi
  · left; rw [c4]; exact h3

theorem QT5a_unimodal {z : ZMod 5 → ℝ} (hinj : Function.Injective z) (h : QT5a z) :
    IsCyclicUnimodal z := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_sub_one
  obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
  refine isCyclicUnimodal_of_top (by norm_num) hinj 3 ?_
  intro i hi
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
  · right; rw [a0]; exact h1
  · right; rw [a1]; exact h2
  · right; rw [a2]; exact h3
  · exact absurd rfl hi
  · left; rw [b4]; exact h4

theorem QT5b_unimodal {z : ZMod 5 → ℝ} (hinj : Function.Injective z) (h : QT5b z) :
    IsCyclicUnimodal z := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_sub_one
  obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
  have n23 : z 2 ≠ z 3 := fun e => by have := hinj e; revert this; decide
  rcases lt_or_gt_of_ne n23 with l | l
  · refine isCyclicUnimodal_of_top (by norm_num) hinj 3 ?_
    intro i hi
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
    · right; rw [a0]; exact h1
    · right; rw [a1]; exact h2
    · right; rw [a2]; exact l
    · exact absurd rfl hi
    · left; rw [b4]; exact h4
  · refine isCyclicUnimodal_of_top (by norm_num) hinj 2 ?_
    intro i hi
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
    · right; rw [a0]; exact h1
    · right; rw [a1]; exact h2
    · exact absurd rfl hi
    · left; rw [b3]; exact l
    · left; rw [b4]; exact h4

theorem QH5_unimodal {z : ZMod 5 → ℝ} (hinj : Function.Injective z) (h : QH5 z) :
    IsCyclicUnimodal z := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_sub_one
  obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
  have n34 : z 3 ≠ z 4 := fun e => by have := hinj e; revert this; decide
  rcases lt_or_gt_of_ne n34 with l | l
  · refine isCyclicUnimodal_of_top (by norm_num) hinj 4 ?_
    intro i hi
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
    · left; rw [b0]; exact h1
    · left; rw [b1]; exact h2
    · right; rw [a2]; exact h3
    · right; rw [a3]; exact l
    · exact absurd rfl hi
  · refine isCyclicUnimodal_of_top (by norm_num) hinj 3 ?_
    intro i hi
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
    · left; rw [b0]; exact h1
    · left; rw [b1]; exact h2
    · right; rw [a2]; exact h3
    · exact absurd rfl hi
    · left; rw [b4]; exact l

end Qlemmas

section N2lt
variable {zv zw s b1 b2 z2 A r1 r2 t : ℝ}

/-- The cycle `(a', c, 2, b)` of Proposition H (N2, `b2 > r2`) in frame coordinates. -/
def h4Pts (zv zw s b1 b2 z2 : ℝ) : ZMod 4 → V3 :=
  quad ⟨0, 0, zw⟩ ⟨0, 0, zv⟩ ⟨s * b1, s * b2, z2⟩ ⟨b1, b2, 0⟩

theorem h4_cyc (hs0 : 0 < s) (hs1 : s < 1) (hzv : 0 ≤ zv) (hzw : zw < 0) (hb2 : 0 < b2)
    (hz2 : (1 - s) * zv < z2) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, -t⟩ (h4Pts zv zw s b1 b2 z2 i)
        (h4Pts zv zw s b1 b2 z2 (i + 1)) (h4Pts zv zw s b1 b2 z2 j) := by
  have hs1' : 0 < 1 - s := by linarith
  have h0 : 0 ≤ (1 - s) * zv := mul_nonneg hs1'.le hzv
  have hz2' : 0 < z2 := by linarith
  have a1 := mul_pos (mul_pos hs0 hb2) (sub_pos.mpr (lt_of_lt_of_le hzw hzv))
  have a2 := mul_pos hb2 (sub_pos.mpr (lt_of_lt_of_le hzw hzv))
  have a3 := mul_pos hb2 (sub_pos.mpr hz2)
  have a4 := mul_pos (mul_pos hs0 hb2) (sub_pos.mpr (lt_of_lt_of_le hzw hzv))
  have a5 := mul_pos hb2 (mul_pos hs1' (neg_pos.mpr hzw))
  have a6 := mul_pos hb2 hz2'
  intro i j h1 h2
  obtain ⟨b0, b1', b2', b3⟩ := zmod4_add_one
  rcases zmod4_pairs i j h1 h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [h4Pts, b0, b1', b2', b3, quad_0, quad_1, quad_2, quad_3, LexTest, tst, hdet] <;>
    left <;> nlinarith

theorem h4_bp (hA : 0 < A) (hs0 : 0 < s) (hs1 : s < 1) (hzv : 0 ≤ zv) (hzw : zw < 0) (hb2 : 0 < b2)
    (hz2 : (1 - s) * zv < z2) (ht : t * (s * b2) < z2) :
    ∀ i : ZMod 4,
      LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, -t⟩ (h4Pts zv zw s b1 b2 z2 i)
        (h4Pts zv zw s b1 b2 z2 (i + 1)) ⟨A, 0, 0⟩ := by
  have hs1' : 0 < 1 - s := by linarith
  have h0 : 0 ≤ (1 - s) * zv := mul_nonneg hs1'.le hzv
  have hz2' : 0 < z2 := by linarith
  have hD : 0 < zv - zw := by linarith
  have a1 := mul_pos hA hD
  have a2 := mul_pos hb2 hz2'
  have a3 := mul_pos hb2 (neg_pos.mpr hzw)
  obtain ⟨b0, b1', b2', b3⟩ := zmod4_add_one
  intro i
  rcases lt_or_eq_of_le hzv with hz | hz
  · have a4 := mul_pos (mul_pos hs0 hb2) hz
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp only [h4Pts, b0, b1', b2', b3, quad_0, quad_1, quad_2, quad_3, LexTest, tst, hdet] <;>
      first
      | (left; nlinarith)
      | (right; refine ⟨by ring, by nlinarith⟩)
  · subst hz
    have a4 := mul_pos hA (sub_pos.mpr ht)
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp only [h4Pts, b0, b1', b2', b3, quad_0, quad_1, quad_2, quad_3, LexTest, tst, hdet] <;>
      first
      | (left; nlinarith)
      | (right; refine ⟨by ring, by nlinarith⟩)

theorem h4_cp (hs0 : 0 < s) (hs1 : s < 1) (hzv : 0 ≤ zv) (hzw : zw < 0) (hb2 : 0 < b2)
    (hr2 : 0 < r2) (hrb : r2 < b2) (hz2 : (1 - s) * zv < z2) :
    ∀ i : ZMod 4,
      LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, -t⟩ (h4Pts zv zw s b1 b2 z2 i)
        (h4Pts zv zw s b1 b2 z2 (i + 1)) ⟨r1, r2, 0⟩ := by
  have hs1' : 0 < 1 - s := by linarith
  have h0 : 0 ≤ (1 - s) * zv := mul_nonneg hs1'.le hzv
  have hz2' : 0 < z2 := by linarith
  have hD : 0 < zv - zw := by linarith
  have a1 := mul_pos hr2 hD
  have a2 := mul_pos hz2' (sub_pos.mpr hrb)
  have a3 := mul_neg_of_neg_of_pos hzw (sub_pos.mpr hrb)
  have a5 := mul_pos hr2 (sub_pos.mpr hz2)
  have a6 := mul_nonneg (mul_nonneg hs0.le hzv) (sub_pos.mpr hrb).le
  obtain ⟨b0, b1', b2', b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    simp only [h4Pts, b0, b1', b2', b3, quad_0, quad_1, quad_2, quad_3, LexTest, tst, hdet] <;>
    left <;> nlinarith

theorem h4_a {a1 a2 a3 : ℝ}
    (u0 : 0 < -(crossYZ (h4Pts zv zw s b1 b2 z2 0) (h4Pts zv zw s b1 b2 z2 1) ⟨a1, a2, a3⟩))
    (u1 : 0 < -(crossYZ (h4Pts zv zw s b1 b2 z2 1) (h4Pts zv zw s b1 b2 z2 2) ⟨a1, a2, a3⟩))
    (u2 : 0 < -(crossYZ (h4Pts zv zw s b1 b2 z2 2) (h4Pts zv zw s b1 b2 z2 3) ⟨a1, a2, a3⟩))
    (u3 : 0 < -(crossYZ (h4Pts zv zw s b1 b2 z2 3) (h4Pts zv zw s b1 b2 z2 0) ⟨a1, a2, a3⟩)) :
    ∀ i : ZMod 4,
      LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, -t⟩ (h4Pts zv zw s b1 b2 z2 i)
        (h4Pts zv zw s b1 b2 z2 (i + 1)) ⟨a1, a2, a3⟩ := by
  obtain ⟨b0, b1', b2', b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl
  · rw [b0]; left; simp only [LexTest, tst, hdet, crossYZ] at u0 ⊢; nlinarith
  · rw [b1']; left; simp only [LexTest, tst, hdet, crossYZ] at u1 ⊢; nlinarith
  · rw [b2']; left; simp only [LexTest, tst, hdet, crossYZ] at u2 ⊢; nlinarith
  · rw [b3]; left; simp only [LexTest, tst, hdet, crossYZ] at u3 ⊢; nlinarith

end N2lt

end Type08Sp

namespace HFrame
open Type08Sp
variable {vb g u0 N : ℝ³} {fG : ℝ³ → ℝ} (Fr : HFrame vb g u0 N fG)
include Fr

/-- **Proposition H, N2, `b2 > r2`** (cycle `(a', c, 2, b)`).  `r` weakly beyond enters only
through `b1 > 0` (Lemma 1.1 (B2')); `c'` and `b'` are hidden by the strict picture, `a` by the four
strict tests `u0`–`u3` (it lies strictly inside the screen quadrilateral). -/
theorem propH_n2_lt {V : Finset ℝ³} {cP mP fP rP gP wP aP : ℝ³}
    {s zv zw b1 b2 z2 A r1 r2 a1 a2 a3 : ℝ}
    (hV : ∀ y ∈ V, y = cP ∨ y = mP ∨ y = fP ∨ y = rP ∨ y = gP ∨ y = wP ∨ y = aP)
    (hc : cP ∈ V) (hm : mP ∈ V) (hf : fP ∈ V) (hw : wP ∈ V)
    (Φc : hfΦ vb g u0 fG cP = ⟨0, 0, zv⟩) (Φm : hfΦ vb g u0 fG mP = ⟨s * b1, s * b2, z2⟩)
    (Φf : hfΦ vb g u0 fG fP = ⟨b1, b2, 0⟩) (Φr : hfΦ vb g u0 fG rP = ⟨r1, r2, 0⟩)
    (Φg : hfΦ vb g u0 fG gP = ⟨A, 0, 0⟩) (Φw : hfΦ vb g u0 fG wP = ⟨0, 0, zw⟩)
    (Φa : hfΦ vb g u0 fG aP = ⟨a1, a2, a3⟩)
    (hA : 0 < A) (hs0 : 0 < s) (hs1 : s < 1) (hzv : 0 ≤ zv) (hzw : zw < 0) (hb2 : 0 < b2)
    (hb1 : 0 < b1) (hr2 : 0 < r2) (hrb : r2 < b2) (hz2 : (1 - s) * zv < z2)
    (u0' : 0 < -(crossYZ (h4Pts zv zw s b1 b2 z2 0) (h4Pts zv zw s b1 b2 z2 1) ⟨a1, a2, a3⟩))
    (u1 : 0 < -(crossYZ (h4Pts zv zw s b1 b2 z2 1) (h4Pts zv zw s b1 b2 z2 2) ⟨a1, a2, a3⟩))
    (u2 : 0 < -(crossYZ (h4Pts zv zw s b1 b2 z2 2) (h4Pts zv zw s b1 b2 z2 3) ⟨a1, a2, a3⟩))
    (u3 : 0 < -(crossYZ (h4Pts zv zw s b1 b2 z2 3) (h4Pts zv zw s b1 b2 z2 0) ⟨a1, a2, a3⟩)) :
    IsRupert V := by
  have hs1' : 0 < 1 - s := by linarith
  have h0 : 0 ≤ (1 - s) * zv := mul_nonneg hs1'.le hzv
  have hz2' : 0 < z2 := by linarith
  have himg : ∀ i : ZMod 4, hfΦ vb g u0 fG (quad wP cP mP fP i) = h4Pts zv zw s b1 b2 z2 i := by
    intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl
    · rw [quad_0, Φw]; rfl
    · rw [quad_1, Φc]; rfl
    · rw [quad_2, Φm]; rfl
    · rw [quad_3, Φf]; rfl
  have hE := Fr.hee
  have hM := Fr.hNN
  have hU := Fr.hu
  set tt : ℝ := z2 / (2 * (s * b2)) with htt
  have htt0 : 0 < tt := by positivity
  have htt1 : tt * (s * b2) < z2 := by
    have : tt * (s * b2) = z2 / 2 := by rw [htt]; field_simp
    rw [this]; linarith
  refine Fr.rupert_coords V (k := 4) (by norm_num) (quad wP cP mP fP) ?_ (-1) ⟨1, 0, 0⟩
    ⟨0, -1, -tt⟩ (Or.inl one_ne_zero) ?_ ?_ QH4 QH4_open (fun z c hc => QH4_smul hc)
    (fun z K => QH4_shift K) (fun z hinj => QH4_unimodal hinj) ?_
  · intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl
    exacts [hw, hc, hm, hf]
  · intro i j h1 h2
    rw [himg i, himg (i + 1), himg j]
    exact h4_cyc hs0 hs1 hzv hzw hb2 hz2 i j h1 h2
  · intro y hy hyx i
    rw [himg i, himg (i + 1)]
    rcases hV y hy with h | h | h | h | h | h | h
    · exact absurd h (hyx 1)
    · exact absurd h (hyx 2)
    · exact absurd h (hyx 3)
    · rw [h, Φr]; exact h4_cp hs0 hs1 hzv hzw hb2 hr2 hrb hz2 i
    · rw [h, Φg]; exact h4_bp hA hs0 hs1 hzv hzw hb2 hz2 htt1 i
    · exact absurd h (hyx 0)
    · rw [h, Φa]; exact h4_a u0' u1 u2 u3 i
  · set E := ⟪hfE vb g u0, hfE vb g u0⟫ with hEd
    set M := ⟪N, N⟫ with hMd
    set U := ⟪u0, u0⟫ with hUd
    have hL : ∀ (c : V3) (i : ZMod 4), lin E M U c (hfΦ vb g u0 fG (quad wP cP mP fP i)) =
        lin E M U c (h4Pts zv zw s b1 b2 z2 i) := by
      intro c i; rw [himg i]
    have s0 : h4Pts zv zw s b1 b2 z2 0 = ⟨0, 0, zw⟩ := rfl
    have s1 : h4Pts zv zw s b1 b2 z2 1 = ⟨0, 0, zv⟩ := rfl
    have s2 : h4Pts zv zw s b1 b2 z2 2 = ⟨s * b1, s * b2, z2⟩ := rfl
    have s3 : h4Pts zv zw s b1 b2 z2 3 = ⟨b1, b2, 0⟩ := rfl
    set L := fun i => lin E M U ⟨1, 0, 0⟩ (h4Pts zv zw s b1 b2 z2 i) with hLd
    set W := fun i => lin E M U ⟨0, -1, -tt⟩ (h4Pts zv zw s b1 b2 z2 i) with hWd
    have l10 : L 1 - L 0 = 0 := by
      simp only [hLd, s0, s1, lin]; ring
    have w10 : 0 < W 0 - W 1 := by
      simp only [hWd, s0, s1, lin]
      have : 0 < tt * (zv - zw) / U := div_pos (mul_pos htt0 (by linarith)) hU
      have e : 0 / E * 0 + (-1) / M * 0 + (-tt) / U * zw - (0 / E * 0 + (-1) / M * 0 + (-tt) / U * zv)
          = tt * (zv - zw) / U := by field_simp; ring
      linarith
    have l21 : 0 < L 2 - L 1 := by
      simp only [hLd, s1, s2, lin]
      have := div_pos (mul_pos hs0 hb1) hE
      have e : 1 / E * (s * b1) + 0 / M * (s * b2) + 0 / U * z2 - (1 / E * 0 + 0 / M * 0 + 0 / U * zv)
          = s * b1 / E := by field_simp; ring
      rw [e]; exact this
    have l30 : 0 < L 3 - L 0 := by
      simp only [hLd, s0, s3, lin]
      have := div_pos hb1 hE
      have e : 1 / E * b1 + 0 / M * b2 + 0 / U * 0 - (1 / E * 0 + 0 / M * 0 + 0 / U * zw) = b1 / E := by
        field_simp; ring
      rw [e]; exact this
    have l32 : 0 < L 3 - L 2 := by
      simp only [hLd, s2, s3, lin]
      have := div_pos (mul_pos hs1' hb1) hE
      have e : 1 / E * b1 + 0 / M * b2 + 0 / U * 0 -
          (1 / E * (s * b1) + 0 / M * (s * b2) + 0 / U * z2) = (1 - s) * b1 / E := by
        field_simp; ring
      rw [e]; exact this
    have k1 := eventually_pos_affine (A := L 0 - L 1) (B := W 0 - W 1) (Or.inr ⟨by linarith, w10⟩)
    have k2 := eventually_pos_affine (A := L 2 - L 1) (B := W 2 - W 1) (Or.inl l21)
    have k3 := eventually_pos_affine (A := L 3 - L 0) (B := W 3 - W 0) (Or.inl l30)
    have k4 := eventually_pos_affine (A := L 3 - L 2) (B := W 3 - W 2) (Or.inl l32)
    filter_upwards [k1, k2, k3, k4] with t' a1' a2' a3' a4'
    simp only [QH4, hL]
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩

end HFrame

end Minimality
