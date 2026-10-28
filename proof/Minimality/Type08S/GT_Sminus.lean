module

public import Minimality.Type08S.GT_Gen

@[expose] public section

set_option autoImplicit true

/-!
# GT, group B: Lemma S− (sp08b §2) in frame coordinates

Frame (`HFrame`): `p = (0,0,0)`, apex `v = (0,0,zv)`, its partner `w = (0,0,zw)` (same screen
point, `zw < 0 ≤ zv`), the far triple `f, r, g` at depth `0` (`g = (E, 0, 0)` in a real frame, kept
general here), a tilt `(px, py)` in the open sector `-int T_p` (`t1`, `t2` negative), and
`r` lexicographically not the minimum of `f, r, g` (`hlex`, tilt value `px/E x + py/M y`).
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- 4-cycle `(w, f, r, g)`: `w` below `f` and `g`, `r` above `f` or `g`. -/
def Q4 (z : ZMod 4 → ℝ) : Prop := z 0 < z 1 ∧ z 0 < z 3 ∧ (z 1 < z 2 ∨ z 3 < z 2)

theorem Q4_open : IsOpen {z : ZMod 4 → ℝ | Q4 z} := by
  have h1 : IsOpen {z : ZMod 4 → ℝ | z 0 < z 1} := isOpen_lt (continuous_apply 0) (continuous_apply 1)
  have h2 : IsOpen {z : ZMod 4 → ℝ | z 0 < z 3} := isOpen_lt (continuous_apply 0) (continuous_apply 3)
  have h3 : IsOpen {z : ZMod 4 → ℝ | z 1 < z 2} := isOpen_lt (continuous_apply 1) (continuous_apply 2)
  have h4 : IsOpen {z : ZMod 4 → ℝ | z 3 < z 2} := isOpen_lt (continuous_apply 3) (continuous_apply 2)
  exact h1.inter (h2.inter (h3.union h4))

theorem Q4_smul {z : ZMod 4 → ℝ} {c : ℝ} (hc : 0 < c) (h : Q4 z) : Q4 (fun i => c * z i) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨mul_lt_mul_of_pos_left h1 hc, mul_lt_mul_of_pos_left h2 hc, ?_⟩
  rcases h3 with h | h
  · exact Or.inl (mul_lt_mul_of_pos_left h hc)
  · exact Or.inr (mul_lt_mul_of_pos_left h hc)

theorem Q4_shift {z : ZMod 4 → ℝ} (k : ℝ) (h : Q4 z) : Q4 (fun i => z i + k) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by linarith, by linarith, ?_⟩
  rcases h3 with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

theorem Q4_unimodal {z : ZMod 4 → ℝ} (hinj : Function.Injective z) (h : Q4 z) :
    IsCyclicUnimodal z := by
  obtain ⟨h1, h2, h3⟩ := h
  have n12 : z 1 ≠ z 2 := fun e => by have := hinj e; revert this; decide
  have n32 : z 3 ≠ z 2 := fun e => by have := hinj e; revert this; decide
  have n13 : z 1 ≠ z 3 := fun e => by have := hinj e; revert this; decide
  have c1 : (0 : ZMod 4) - 1 = 3 := by decide
  have c2 : (1 : ZMod 4) - 1 = 0 := by decide
  have c3 : (2 : ZMod 4) - 1 = 1 := by decide
  have c4 : (3 : ZMod 4) - 1 = 2 := by decide
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  rcases lt_or_gt_of_ne n12 with l12 | l12 <;> rcases lt_or_gt_of_ne n32 with l32 | l32
  · -- z1 < z2, z3 < z2 : top 2
    refine isCyclicUnimodal_of_top (by norm_num) hinj 2 ?_
    intro i hi
    rcases zmod4_cases i with rfl | rfl | rfl | rfl
    · right; rw [a0]; exact h1
    · right; rw [a1]; exact l12
    · exact absurd rfl hi
    · left; rw [c4]; exact l32
  · -- z1 < z2 < z3 : top 3
    refine isCyclicUnimodal_of_top (by norm_num) hinj 3 ?_
    intro i hi
    rcases zmod4_cases i with rfl | rfl | rfl | rfl
    · left; rw [c1]; exact h2
    · right; rw [a1]; exact l12
    · right; rw [a2]; exact l32
    · exact absurd rfl hi
  · -- z2 < z1, z3 < z2 : top 1
    refine isCyclicUnimodal_of_top (by norm_num) hinj 1 ?_
    intro i hi
    rcases zmod4_cases i with rfl | rfl | rfl | rfl
    · right; rw [a0]; exact h1
    · exact absurd rfl hi
    · left; rw [c3]; exact l12
    · left; rw [c4]; exact l32
  · -- z2 < z1, z2 < z3 : excluded by h3
    exfalso
    rcases h3 with h | h <;> linarith


/-- The N2 cycle `(w, f, r, g)` in frame coordinates. -/
def sPts (zw f1 f2 r1 r2 g1 g2 : ℝ) : ZMod 4 → V3 :=
  quad ⟨0, 0, zw⟩ ⟨f1, f2, 0⟩ ⟨r1, r2, 0⟩ ⟨g1, g2, 0⟩

section Tests
variable {σ px py s zv zw m f1 f2 r1 r2 g1 g2 : ℝ}

theorem sm_cyc (q1 : 0 < σ * (f1 * r2 - f2 * r1))
    (q2 : 0 < σ * ((r1 - f1) * (g2 - f2) - (r2 - f2) * (g1 - f1)))
    (q3 : 0 < σ * (r1 * g2 - g1 * r2)) (q4 : 0 < σ * (f1 * g2 - f2 * g1)) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      LexTest σ ⟨0, 0, 1⟩ ⟨px, py, 0⟩ (sPts zw f1 f2 r1 r2 g1 g2 i) (sPts zw f1 f2 r1 r2 g1 g2 (i + 1))
        (sPts zw f1 f2 r1 r2 g1 g2 j) := by
  intro i j h1 h2
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  rcases zmod4_pairs i j h1 h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [sPts, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3, LexTest, tst, hdet] <;>
    left <;> linarith

theorem sm_c (hzv : 0 ≤ zv) (hzw : zw < 0)
    (t1 : σ * (py * f1 - px * f2) < 0) (t2 : σ * (px * g2 - py * g1) < 0)
    (q1 : 0 < σ * (f1 * r2 - f2 * r1)) (q3 : 0 < σ * (r1 * g2 - g1 * r2)) :
    ∀ i : ZMod 4,
      LexTest σ ⟨0, 0, 1⟩ ⟨px, py, 0⟩ (sPts zw f1 f2 r1 r2 g1 g2 i) (sPts zw f1 f2 r1 r2 g1 g2 (i + 1))
        ⟨0, 0, zv⟩ := by
  have hU : 0 < zv - zw := by linarith
  have a1 := mul_neg_of_pos_of_neg hU t1
  have a3 := mul_neg_of_pos_of_neg hU t2
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    simp only [sPts, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3, LexTest, tst, hdet] <;>
    first
    | (left; linarith)
    | (right; refine ⟨by ring, by linarith⟩)

theorem sm_m (hs0 : 0 < s) (hs1 : s < 1) (hzv : 0 ≤ zv) (hzw : zw < 0) (hm : (1 - s) * zv < m)
    (t1 : σ * (py * f1 - px * f2) < 0)
    (q1 : 0 < σ * (f1 * r2 - f2 * r1))
    (q2 : 0 < σ * ((r1 - f1) * (g2 - f2) - (r2 - f2) * (g1 - f1)))
    (q3 : 0 < σ * (r1 * g2 - g1 * r2)) (q4 : 0 < σ * (f1 * g2 - f2 * g1)) :
    ∀ i : ZMod 4,
      LexTest σ ⟨0, 0, 1⟩ ⟨px, py, 0⟩ (sPts zw f1 f2 r1 r2 g1 g2 i) (sPts zw f1 f2 r1 r2 g1 g2 (i + 1))
        ⟨s * f1, s * f2, m⟩ := by
  have hs1' : 0 < 1 - s := by linarith
  have h0 : 0 ≤ (1 - s) * zv := mul_nonneg hs1'.le hzv
  have hK : 0 < m - (1 - s) * zw := by nlinarith
  have a1 := mul_neg_of_pos_of_neg hK t1
  have a2 := mul_pos hs1' q1
  have a3 := mul_pos hs0 q4
  have a4 := mul_pos hs1' q3
  have a5 := mul_pos hs0 q2
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    simp only [sPts, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3, LexTest, tst, hdet] <;>
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem sm_a {a1 a2 a3 : ℝ}
    (u1 : 0 < σ * (f1 * a2 - f2 * a1))
    (u2 : 0 < σ * ((r1 - f1) * (a2 - f2) - (r2 - f2) * (a1 - f1)))
    (u3 : 0 < σ * ((g1 - r1) * (a2 - r2) - (g2 - r2) * (a1 - r1)))
    (u4 : 0 < σ * (g2 * a1 - g1 * a2)) :
    ∀ i : ZMod 4,
      LexTest σ ⟨0, 0, 1⟩ ⟨px, py, 0⟩ (sPts zw f1 f2 r1 r2 g1 g2 i) (sPts zw f1 f2 r1 r2 g1 g2 (i + 1))
        ⟨a1, a2, a3⟩ := by
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    simp only [sPts, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3, LexTest, tst, hdet] <;>
    left <;> linarith

end Tests

/-- The T4 cycle `(w, a, f, r, g)` (`= (2, a, c', b', c)`) in frame coordinates. -/
def tPts (zw s m f1 f2 r1 r2 g1 g2 : ℝ) : ZMod 5 → V3 :=
  quint ⟨0, 0, zw⟩ ⟨s * f1, s * f2, m⟩ ⟨f1, f2, 0⟩ ⟨r1, r2, 0⟩ ⟨g1, g2, 0⟩

/-- Negated Q5: low arc `(w, a)`, high arc `(f, r, g)`, `r` above `f` or `g`. -/
def Q5n (z : ZMod 5 → ℝ) : Prop := Q5 fun i => -z i

theorem Q5n_open : IsOpen {z : ZMod 5 → ℝ | Q5n z} :=
  Q5_open.preimage (f := fun z : ZMod 5 → ℝ => fun i => -z i) (by fun_prop)

theorem Q5n_smul {z : ZMod 5 → ℝ} {c : ℝ} (hc : 0 < c) (h : Q5n z) : Q5n (fun i => c * z i) := by
  have e : (fun i => -(c * z i)) = fun i => c * -z i := by funext i; ring
  unfold Q5n; rw [e]; exact Q5_smul hc h

theorem Q5n_shift {z : ZMod 5 → ℝ} (k : ℝ) (h : Q5n z) : Q5n (fun i => z i + k) := by
  have e : (fun i => -(z i + k)) = fun i => -z i + -k := by funext i; ring
  unfold Q5n; rw [e]; exact Q5_shift (-k) h

theorem Q5n_unimodal {z : ZMod 5 → ℝ} (hinj : Function.Injective z) (h : Q5n z) :
    IsCyclicUnimodal z := by
  have h1 := Q5_unimodal (fun i j hij => hinj (by simpa using hij)) h
  have h2 := h1.affine_sign (by norm_num) (Or.inr rfl : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1) 0
  convert h2 using 2 with i
  simp

section TTests
variable {σ px py s t zv zw m mp f1 f2 r1 r2 g1 g2 : ℝ}

theorem st_cyc (hs0 : 0 < s) (hs1 : s < 1) (hzw : zw < 0) (hm : m < (1 - s) * zw)
    (t1 : σ * (py * f1 - px * f2) < 0)
    (q1 : 0 < σ * (f1 * r2 - f2 * r1))
    (q2 : 0 < σ * ((r1 - f1) * (g2 - f2) - (r2 - f2) * (g1 - f1)))
    (q3 : 0 < σ * (r1 * g2 - g1 * r2)) (q4 : 0 < σ * (f1 * g2 - f2 * g1)) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      LexTest σ ⟨0, 0, 1⟩ ⟨px, py, 0⟩ (tPts zw s m f1 f2 r1 r2 g1 g2 i)
        (tPts zw s m f1 f2 r1 r2 g1 g2 (i + 1)) (tPts zw s m f1 f2 r1 r2 g1 g2 j) := by
  have hs1' : 0 < 1 - s := by linarith
  have hK : m - (1 - s) * zw < 0 := by linarith
  have a1 := mul_pos_of_neg_of_neg hK t1
  have a2 := mul_pos hs1' q1
  have a3 := mul_pos hs0 q4
  have a4 := mul_pos hs1' q3
  have a5 := mul_pos hs0 q2
  have a6 := mul_pos hs1' q4
  have a7 := mul_pos hs0 q1
  have a8 := mul_pos hs0 q3
  have a9 := mul_pos hs1' q2
  intro i j h1 h2
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [tPts, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, LexTest,
      tst, hdet]
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem st_b (hs0 : 0 < s) (hs1 : s < 1) (hzv : 0 ≤ zv) (hzw : zw < 0) (hm : m < (1 - s) * zw)
    (t1 : σ * (py * f1 - px * f2) < 0) (t2 : σ * (px * g2 - py * g1) < 0)
    (q1 : 0 < σ * (f1 * r2 - f2 * r1)) (q3 : 0 < σ * (r1 * g2 - g1 * r2)) :
    ∀ i : ZMod 5,
      LexTest σ ⟨0, 0, 1⟩ ⟨px, py, 0⟩ (tPts zw s m f1 f2 r1 r2 g1 g2 i)
        (tPts zw s m f1 f2 r1 r2 g1 g2 (i + 1)) ⟨0, 0, zv⟩ := by
  have hs1' : 0 < 1 - s := by linarith
  have hU : 0 < zv - zw := by linarith
  have hK : 0 < zv * (1 - s) - m := by nlinarith
  have a1 := mul_neg_of_pos_of_neg hU t1
  have a2 := mul_neg_of_pos_of_neg hU t2
  have a3 := mul_neg_of_pos_of_neg hK t1
  have a4 := mul_neg_of_pos_of_neg (mul_pos hs0 hU) t1
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    simp only [tPts, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, LexTest,
      tst, hdet] <;>
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem st_a' (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1) (hzv : 0 ≤ zv)
    (hzw : zw < 0) (hmp : (1 - t) * zv < mp)
    (t2 : σ * (px * g2 - py * g1) < 0)
    (q1 : 0 < σ * (f1 * r2 - f2 * r1))
    (q2 : 0 < σ * ((r1 - f1) * (g2 - f2) - (r2 - f2) * (g1 - f1)))
    (q3 : 0 < σ * (r1 * g2 - g1 * r2)) (q4 : 0 < σ * (f1 * g2 - f2 * g1)) :
    ∀ i : ZMod 5,
      LexTest σ ⟨0, 0, 1⟩ ⟨px, py, 0⟩ (tPts zw s m f1 f2 r1 r2 g1 g2 i)
        (tPts zw s m f1 f2 r1 r2 g1 g2 (i + 1)) ⟨t * g1, t * g2, mp⟩ := by
  have ht1' : 0 < 1 - t := by linarith
  have h0 : 0 ≤ (1 - t) * zv := mul_nonneg ht1'.le hzv
  have hK : 0 < mp - (1 - t) * zw := by nlinarith
  have a1 := mul_neg_of_pos_of_neg hK t2
  have a2 := mul_pos (mul_pos hs0 ht0) q4
  have a3 := mul_pos (mul_pos ht0 (sub_pos.mpr hs1)) q4
  have a4 := mul_pos ht1' q1
  have a5 := mul_pos ht0 q2
  have a6 := mul_pos ht1' q3
  have a7 := mul_pos ht0 q3
  have a8 := mul_pos ht0 q4
  have a9 := mul_pos hs0 ht0
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    simp only [tPts, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, LexTest,
      tst, hdet] <;>
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

end TTests

section Tilt
variable {σ E M f1 f2 r1 r2 g1 g2 : ℝ}

theorem tilt_aux (hE : 0 < E) (hM : 0 < M) {a1 a2 b1 b2 : ℝ}
    (h : a1 * b1 / E + a2 * b2 / M < 0) (c1 c2 : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ a1 * (b1 + κ * c1) / E + a2 * (b2 + κ * c2) / M < 0 := by
  obtain ⟨κ, hκ, hpos⟩ := sec_small_pos (f0 := -(a1 * b1 / E + a2 * b2 / M))
    (f1 := -(a1 * c1 / E + a2 * c2 / M)) (by linarith)
  refine ⟨κ, hκ, ?_⟩
  have : a1 * (b1 + κ * c1) / E + a2 * (b2 + κ * c2) / M =
      -(-(a1 * b1 / E + a2 * b2 / M) + κ * -(a1 * c1 / E + a2 * c2 / M)) := by
    field_simp; ring
  linarith

/-- **The sector tilt from "strictly not beyond"** (frame form): if one of
`(r - F)·y < 0` (`F, y ∈ {f, g}`, weighted inner product), there is a tilt `(px, py)` in
`-int T_p` along which `r` is lexicographically above `F`. -/
theorem tilt_sminus (hE : 0 < E) (hM : 0 < M) (q4 : 0 < σ * (f1 * g2 - f2 * g1))
    (hnb : (r1 - f1) * f1 / E + (r2 - f2) * f2 / M < 0 ∨
      (r1 - f1) * g1 / E + (r2 - f2) * g2 / M < 0 ∨
      (r1 - g1) * f1 / E + (r2 - g2) * f2 / M < 0 ∨
      (r1 - g1) * g1 / E + (r2 - g2) * g2 / M < 0) :
    ∃ px py : ℝ, σ * (py * f1 - px * f2) < 0 ∧ σ * (px * g2 - py * g1) < 0 ∧
      (px / E * f1 + py / M * f2 < px / E * r1 + py / M * r2 ∨
        px / E * g1 + py / M * g2 < px / E * r1 + py / M * r2) := by
  -- y = f, y' = g
  have key1 : ∀ (F1 F2 : ℝ), (r1 - F1) * f1 / E + (r2 - F2) * f2 / M < 0 →
      ∃ κ : ℝ, 0 < κ ∧ (r1 - F1) * (f1 + κ * g1) / E + (r2 - F2) * (f2 + κ * g2) / M < 0 :=
    fun F1 F2 h => tilt_aux hE hM h g1 g2
  have key2 : ∀ (F1 F2 : ℝ), (r1 - F1) * g1 / E + (r2 - F2) * g2 / M < 0 →
      ∃ κ : ℝ, 0 < κ ∧ (r1 - F1) * (g1 + κ * f1) / E + (r2 - F2) * (g2 + κ * f2) / M < 0 :=
    fun F1 F2 h => tilt_aux hE hM h f1 f2
  have fin1 : ∀ (F1 F2 : ℝ) (κ : ℝ), 0 < κ →
      (r1 - F1) * (f1 + κ * g1) / E + (r2 - F2) * (f2 + κ * g2) / M < 0 →
      ∃ px py : ℝ, σ * (py * f1 - px * f2) < 0 ∧ σ * (px * g2 - py * g1) < 0 ∧
        px / E * F1 + py / M * F2 < px / E * r1 + py / M * r2 := by
    intro F1 F2 κ hκ h
    refine ⟨-(f1 + κ * g1), -(f2 + κ * g2), by nlinarith [mul_pos hκ q4], by nlinarith [q4], ?_⟩
    have : (r1 - F1) * (f1 + κ * g1) / E + (r2 - F2) * (f2 + κ * g2) / M =
        -(((-(f1 + κ * g1)) / E * r1 + (-(f2 + κ * g2)) / M * r2) -
          ((-(f1 + κ * g1)) / E * F1 + (-(f2 + κ * g2)) / M * F2)) := by
      field_simp; ring
    linarith
  have fin2 : ∀ (F1 F2 : ℝ) (κ : ℝ), 0 < κ →
      (r1 - F1) * (g1 + κ * f1) / E + (r2 - F2) * (g2 + κ * f2) / M < 0 →
      ∃ px py : ℝ, σ * (py * f1 - px * f2) < 0 ∧ σ * (px * g2 - py * g1) < 0 ∧
        px / E * F1 + py / M * F2 < px / E * r1 + py / M * r2 := by
    intro F1 F2 κ hκ h
    refine ⟨-(g1 + κ * f1), -(g2 + κ * f2), by nlinarith [q4], by nlinarith [mul_pos hκ q4], ?_⟩
    have : (r1 - F1) * (g1 + κ * f1) / E + (r2 - F2) * (g2 + κ * f2) / M =
        -(((-(g1 + κ * f1)) / E * r1 + (-(g2 + κ * f2)) / M * r2) -
          ((-(g1 + κ * f1)) / E * F1 + (-(g2 + κ * f2)) / M * F2)) := by
      field_simp; ring
    linarith
  rcases hnb with h | h | h | h
  · obtain ⟨κ, hκ, h'⟩ := key1 f1 f2 h
    obtain ⟨px, py, a, b, c⟩ := fin1 f1 f2 κ hκ h'
    exact ⟨px, py, a, b, Or.inl c⟩
  · obtain ⟨κ, hκ, h'⟩ := key2 f1 f2 h
    obtain ⟨px, py, a, b, c⟩ := fin2 f1 f2 κ hκ h'
    exact ⟨px, py, a, b, Or.inl c⟩
  · obtain ⟨κ, hκ, h'⟩ := key1 g1 g2 h
    obtain ⟨px, py, a, b, c⟩ := fin1 g1 g2 κ hκ h'
    exact ⟨px, py, a, b, Or.inr c⟩
  · obtain ⟨κ, hκ, h'⟩ := key2 g1 g2 h
    obtain ⟨px, py, a, b, c⟩ := fin2 g1 g2 κ hκ h'
    exact ⟨px, py, a, b, Or.inr c⟩

end Tilt

end Type08Sp

namespace HFrame
open Type08Sp
variable {vb g u0 N : ℝ³} {fG : ℝ³ → ℝ} (Fr : HFrame vb g u0 N fG)
include Fr

/-- **Lemma S− (N2), frame form.**  Cycle `(w, f, r, g)` (`= (a', b, c', b')`); `c` (apex), `2`
(upper middle over `(p, f)`) and `a` (strictly inside the shadow) are hidden; the tilt `(px, py)`
is in `-int T_p` (`t1`, `t2`); `r` is lexicographically not the minimum of `f, r, g` (`hlex`). -/
theorem sminus_n2 {V : Finset ℝ³} {cP mP fP rP gP wP aP : ℝ³}
    {σ px py s zv zw m f1 f2 r1 r2 g1 g2 a1 a2 a3 : ℝ}
    (hV : ∀ y ∈ V, y = cP ∨ y = mP ∨ y = fP ∨ y = rP ∨ y = gP ∨ y = wP ∨ y = aP)
    (hf : fP ∈ V) (hr : rP ∈ V) (hg : gP ∈ V) (hw : wP ∈ V)
    (Φc : hfΦ vb g u0 fG cP = ⟨0, 0, zv⟩) (Φm : hfΦ vb g u0 fG mP = ⟨s * f1, s * f2, m⟩)
    (Φf : hfΦ vb g u0 fG fP = ⟨f1, f2, 0⟩) (Φr : hfΦ vb g u0 fG rP = ⟨r1, r2, 0⟩)
    (Φg : hfΦ vb g u0 fG gP = ⟨g1, g2, 0⟩) (Φw : hfΦ vb g u0 fG wP = ⟨0, 0, zw⟩)
    (Φa : hfΦ vb g u0 fG aP = ⟨a1, a2, a3⟩)
    (hs0 : 0 < s) (hs1 : s < 1) (hzv : 0 ≤ zv) (hzw : zw < 0) (hm : (1 - s) * zv < m)
    (q1 : 0 < σ * (f1 * r2 - f2 * r1))
    (q2 : 0 < σ * ((r1 - f1) * (g2 - f2) - (r2 - f2) * (g1 - f1)))
    (q3 : 0 < σ * (r1 * g2 - g1 * r2)) (q4 : 0 < σ * (f1 * g2 - f2 * g1))
    (u1 : 0 < σ * (f1 * a2 - f2 * a1))
    (u2 : 0 < σ * ((r1 - f1) * (a2 - f2) - (r2 - f2) * (a1 - f1)))
    (u3 : 0 < σ * ((g1 - r1) * (a2 - r2) - (g2 - r2) * (a1 - r1)))
    (u4 : 0 < σ * (g2 * a1 - g1 * a2))
    (t1 : σ * (py * f1 - px * f2) < 0) (t2 : σ * (px * g2 - py * g1) < 0)
    (hlex : px / ⟪hfE vb g u0, hfE vb g u0⟫ * f1 + py / ⟪N, N⟫ * f2 <
        px / ⟪hfE vb g u0, hfE vb g u0⟫ * r1 + py / ⟪N, N⟫ * r2 ∨
      px / ⟪hfE vb g u0, hfE vb g u0⟫ * g1 + py / ⟪N, N⟫ * g2 <
        px / ⟪hfE vb g u0, hfE vb g u0⟫ * r1 + py / ⟪N, N⟫ * r2) :
    IsRupert V := by
  have himg : ∀ i : ZMod 4, hfΦ vb g u0 fG (quad wP fP rP gP i) = sPts zw f1 f2 r1 r2 g1 g2 i := by
    intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl
    · rw [quad_0, Φw]; rfl
    · rw [quad_1, Φf]; rfl
    · rw [quad_2, Φr]; rfl
    · rw [quad_3, Φg]; rfl
  have hE := Fr.hee
  have hM := Fr.hNN
  have hU := Fr.hu
  refine Fr.rupert_coords V (k := 4) (by norm_num) (quad wP fP rP gP) ?_ σ ⟨0, 0, 1⟩ ⟨px, py, 0⟩
    (Or.inr (Or.inr one_ne_zero)) ?_ ?_ Q4 Q4_open (fun z c hc => Q4_smul hc)
    (fun z K => Q4_shift K) (fun z hinj => Q4_unimodal hinj) ?_
  · intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl
    exacts [hw, hf, hr, hg]
  · intro i j h1 h2
    rw [himg i, himg (i + 1), himg j]
    exact sm_cyc q1 q2 q3 q4 i j h1 h2
  · intro y hy hyx i
    rw [himg i, himg (i + 1)]
    rcases hV y hy with h | h | h | h | h | h | h
    · rw [h, Φc]; exact sm_c hzv hzw t1 t2 q1 q3 i
    · rw [h, Φm]; exact sm_m hs0 hs1 hzv hzw hm t1 q1 q2 q3 q4 i
    · exact absurd h (hyx 1)
    · exact absurd h (hyx 2)
    · exact absurd h (hyx 3)
    · exact absurd h (hyx 0)
    · rw [h, Φa]; exact sm_a u1 u2 u3 u4 i
  · set E := ⟪hfE vb g u0, hfE vb g u0⟫ with hEd
    set M := ⟪N, N⟫ with hMd
    set U := ⟪u0, u0⟫ with hUd
    have hL : ∀ (c : V3) (i : ZMod 4), lin E M U c (hfΦ vb g u0 fG (quad wP fP rP gP i)) =
        c.x / E * (sPts zw f1 f2 r1 r2 g1 g2 i).x + c.y / M * (sPts zw f1 f2 r1 r2 g1 g2 i).y +
          c.z / U * (sPts zw f1 f2 r1 r2 g1 g2 i).z := by
      intro c i; rw [himg i]; rfl
    have s0 : sPts zw f1 f2 r1 r2 g1 g2 0 = ⟨0, 0, zw⟩ := rfl
    have s1 : sPts zw f1 f2 r1 r2 g1 g2 1 = ⟨f1, f2, 0⟩ := rfl
    have s2 : sPts zw f1 f2 r1 r2 g1 g2 2 = ⟨r1, r2, 0⟩ := rfl
    have s3 : sPts zw f1 f2 r1 r2 g1 g2 3 = ⟨g1, g2, 0⟩ := rfl
    have hzU : zw / U < 0 := div_neg_of_neg_of_pos hzw hU
    have k1 := eventually_pos_affine (A := 0 - zw / U) (B := (px / E * f1 + py / M * f2) -
      (px / E * 0 + py / M * 0)) (Or.inl (by linarith))
    have k2 := eventually_pos_affine (A := 0 - zw / U) (B := (px / E * g1 + py / M * g2) -
      (px / E * 0 + py / M * 0)) (Or.inl (by linarith))
    have k3 : ∀ᶠ t in 𝓝[>] (0 : ℝ), (0 < (0:ℝ) + t * ((px / E * r1 + py / M * r2) - (px / E * f1 + py / M * f2))) ∨
        (0 < (0:ℝ) + t * ((px / E * r1 + py / M * r2) - (px / E * g1 + py / M * g2))) := by
      rcases hlex with h | h
      · exact (eventually_pos_affine (A := 0) (B := (px / E * r1 + py / M * r2) - (px / E * f1 + py / M * f2))
          (Or.inr ⟨rfl, by linarith⟩)).mono fun t ht => Or.inl ht
      · exact (eventually_pos_affine (A := 0) (B := (px / E * r1 + py / M * r2) - (px / E * g1 + py / M * g2))
          (Or.inr ⟨rfl, by linarith⟩)).mono fun t ht => Or.inr ht
    filter_upwards [k1, k2, k3] with t a1' a2' a3'
    simp only [Q4, hL, s0, s1, s2, s3]
    refine ⟨by (ring_nf at *; linarith), by (ring_nf at *; linarith), ?_⟩
    rcases a3' with h | h
    · left; (ring_nf at *; linarith)
    · right; (ring_nf at *; linarith)

/-- **Lemma S− (T4), frame form.**  Cycle `(w, a, f, r, g)` (`= (2, a, c', b', c)`), `a` the lower
middle over `(p, f)`; the apex `b = (0,0,zv)` and the upper middle `a' = t·g` over `(p, g)` are
hidden; tilt `(px, py)` in `-int T_p`; `r` lexicographically not the minimum of `f, r, g`. -/
theorem sminus_t4 {V : Finset ℝ³} {bP aP' fP rP gP wP aP : ℝ³}
    {σ px py s t zv zw m mp f1 f2 r1 r2 g1 g2 : ℝ}
    (hV : ∀ y ∈ V, y = bP ∨ y = aP' ∨ y = fP ∨ y = rP ∨ y = gP ∨ y = wP ∨ y = aP)
    (hw : wP ∈ V) (ha : aP ∈ V) (hf : fP ∈ V) (hr : rP ∈ V) (hg : gP ∈ V)
    (Φb : hfΦ vb g u0 fG bP = ⟨0, 0, zv⟩) (Φa' : hfΦ vb g u0 fG aP' = ⟨t * g1, t * g2, mp⟩)
    (Φf : hfΦ vb g u0 fG fP = ⟨f1, f2, 0⟩) (Φr : hfΦ vb g u0 fG rP = ⟨r1, r2, 0⟩)
    (Φg : hfΦ vb g u0 fG gP = ⟨g1, g2, 0⟩) (Φw : hfΦ vb g u0 fG wP = ⟨0, 0, zw⟩)
    (Φa : hfΦ vb g u0 fG aP = ⟨s * f1, s * f2, m⟩)
    (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1) (hzv : 0 ≤ zv) (hzw : zw < 0)
    (hm : m < (1 - s) * zw) (hmp : (1 - t) * zv < mp)
    (q1 : 0 < σ * (f1 * r2 - f2 * r1))
    (q2 : 0 < σ * ((r1 - f1) * (g2 - f2) - (r2 - f2) * (g1 - f1)))
    (q3 : 0 < σ * (r1 * g2 - g1 * r2)) (q4 : 0 < σ * (f1 * g2 - f2 * g1))
    (t1 : σ * (py * f1 - px * f2) < 0) (t2 : σ * (px * g2 - py * g1) < 0)
    (hlex : px / ⟪hfE vb g u0, hfE vb g u0⟫ * f1 + py / ⟪N, N⟫ * f2 <
        px / ⟪hfE vb g u0, hfE vb g u0⟫ * r1 + py / ⟪N, N⟫ * r2 ∨
      px / ⟪hfE vb g u0, hfE vb g u0⟫ * g1 + py / ⟪N, N⟫ * g2 <
        px / ⟪hfE vb g u0, hfE vb g u0⟫ * r1 + py / ⟪N, N⟫ * r2) :
    IsRupert V := by
  have himg : ∀ i : ZMod 5, hfΦ vb g u0 fG (quint wP aP fP rP gP i) =
      tPts zw s m f1 f2 r1 r2 g1 g2 i := by
    intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
    · rw [quint_0, Φw]; rfl
    · rw [quint_1, Φa]; rfl
    · rw [quint_2, Φf]; rfl
    · rw [quint_3, Φr]; rfl
    · rw [quint_4, Φg]; rfl
  have hE := Fr.hee
  have hM := Fr.hNN
  have hU := Fr.hu
  refine Fr.rupert_coords V (k := 5) (by norm_num) (quint wP aP fP rP gP) ?_ σ ⟨0, 0, 1⟩
    ⟨px, py, 0⟩ (Or.inr (Or.inr one_ne_zero)) ?_ ?_ Q5n Q5n_open (fun z c hc => Q5n_smul hc)
    (fun z K => Q5n_shift K) (fun z hinj => Q5n_unimodal hinj) ?_
  · intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
    exacts [hw, ha, hf, hr, hg]
  · intro i j h1 h2
    rw [himg i, himg (i + 1), himg j]
    exact st_cyc hs0 hs1 hzw hm t1 q1 q2 q3 q4 i j h1 h2
  · intro y hy hyx i
    rw [himg i, himg (i + 1)]
    rcases hV y hy with h | h | h | h | h | h | h
    · rw [h, Φb]; exact st_b hs0 hs1 hzv hzw hm t1 t2 q1 q3 i
    · rw [h, Φa']; exact st_a' hs0 hs1 ht0 ht1 hzv hzw hmp t2 q1 q2 q3 q4 i
    · exact absurd h (hyx 2)
    · exact absurd h (hyx 3)
    · exact absurd h (hyx 4)
    · exact absurd h (hyx 0)
    · exact absurd h (hyx 1)
  · set E := ⟪hfE vb g u0, hfE vb g u0⟫ with hEd
    set M := ⟪N, N⟫ with hMd
    set U := ⟪u0, u0⟫ with hUd
    have hL : ∀ (c : V3) (i : ZMod 5), lin E M U c (hfΦ vb g u0 fG (quint wP aP fP rP gP i)) =
        c.x / E * (tPts zw s m f1 f2 r1 r2 g1 g2 i).x + c.y / M * (tPts zw s m f1 f2 r1 r2 g1 g2 i).y +
          c.z / U * (tPts zw s m f1 f2 r1 r2 g1 g2 i).z := by
      intro c i; rw [himg i]; rfl
    have s0 : tPts zw s m f1 f2 r1 r2 g1 g2 0 = ⟨0, 0, zw⟩ := rfl
    have s1 : tPts zw s m f1 f2 r1 r2 g1 g2 1 = ⟨s * f1, s * f2, m⟩ := rfl
    have s2 : tPts zw s m f1 f2 r1 r2 g1 g2 2 = ⟨f1, f2, 0⟩ := rfl
    have s3 : tPts zw s m f1 f2 r1 r2 g1 g2 3 = ⟨r1, r2, 0⟩ := rfl
    have s4 : tPts zw s m f1 f2 r1 r2 g1 g2 4 = ⟨g1, g2, 0⟩ := rfl
    have hm0 : m < 0 := by nlinarith
    have hzU : zw / U < 0 := div_neg_of_neg_of_pos hzw hU
    have hmU : m / U < 0 := div_neg_of_neg_of_pos hm0 hU
    have k1 := eventually_pos_affine (A := 0 - m / U) (B := (px / E * (s * f1) + py / M * (s * f2)) * (-1) +
      (px / E * f1 + py / M * f2)) (Or.inl (by linarith))
    have k2 := eventually_pos_affine (A := 0 - zw / U) (B := (px / E * 0 + py / M * 0) * (-1) +
      (px / E * g1 + py / M * g2)) (Or.inl (by linarith))
    have k3 : ∀ᶠ t in 𝓝[>] (0 : ℝ), (0 < (0:ℝ) + t * ((px / E * r1 + py / M * r2) - (px / E * f1 + py / M * f2))) ∨
        (0 < (0:ℝ) + t * ((px / E * r1 + py / M * r2) - (px / E * g1 + py / M * g2))) := by
      rcases hlex with h | h
      · exact (eventually_pos_affine (A := 0) (B := (px / E * r1 + py / M * r2) - (px / E * f1 + py / M * f2))
          (Or.inr ⟨rfl, by linarith⟩)).mono fun t ht => Or.inl ht
      · exact (eventually_pos_affine (A := 0) (B := (px / E * r1 + py / M * r2) - (px / E * g1 + py / M * g2))
          (Or.inr ⟨rfl, by linarith⟩)).mono fun t ht => Or.inr ht
    filter_upwards [k1, k2, k3] with t' a1' a2' a3'
    simp only [Q5n, Q5, hL, s0, s1, s2, s3, s4]
    refine ⟨by (ring_nf at *; linarith), by (ring_nf at *; linarith), ?_⟩
    rcases a3' with h | h
    · left; (ring_nf at *; linarith)
    · right; (ring_nf at *; linarith)

end HFrame
end Minimality
