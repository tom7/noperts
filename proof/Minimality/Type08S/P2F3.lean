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

/-- The cycle `(w, a, f, r, g)` of case B: `a` and `f` over the same screen point. -/
def bPts (zw m b1 b2 r1 r2 A : ℝ) : ZMod 5 → V3 :=
  quint ⟨0, 0, zw⟩ ⟨b1, b2, m⟩ ⟨b1, b2, 0⟩ ⟨r1, r2, 0⟩ ⟨A, 0, 0⟩

section BTests
variable {px py t zv zw mp m b1 b2 r1 r2 A : ℝ}

theorem tb_cyc (hm : m < 0) (t1 : 0 < py * b1 - px * b2) (t2 : 0 < -(py * A))
    (t3 : 0 < (r2 - b2) * px - (r1 - b1) * py)
    (q1 : 0 < r1 * b2 - r2 * b1) (q2 : 0 < (r1 - b1) * b2 + (r2 - b2) * (A - b1))
    (q3 : 0 < A * r2) (q4 : 0 < b2 * A) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      LexTest (-1) ⟨0, 0, 1⟩ ⟨px, py, 0⟩ (bPts zw m b1 b2 r1 r2 A i)
        (bPts zw m b1 b2 r1 r2 A (i + 1)) (bPts zw m b1 b2 r1 r2 A j) := by
  have a1 := mul_neg_of_neg_of_pos hm t1
  have a2 := mul_neg_of_neg_of_pos hm t2
  have a3 := mul_neg_of_neg_of_pos hm t3
  intro i j h1 h2
  obtain ⟨b0, b1', b2', b3, b4⟩ := zmod5_add_one
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [bPts, b0, b1', b2', b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, LexTest,
      tst, hdet]
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem tb_b (hm : m < 0) (hzv : 0 ≤ zv) (hzw : zw < 0)
    (t1 : 0 < py * b1 - px * b2) (t2 : 0 < -(py * A))
    (q1 : 0 < r1 * b2 - r2 * b1) (q3 : 0 < A * r2) (q4 : 0 < b2 * A) :
    ∀ i : ZMod 5, LexTest (-1) ⟨0, 0, 1⟩ ⟨px, py, 0⟩ (bPts zw m b1 b2 r1 r2 A i)
        (bPts zw m b1 b2 r1 r2 A (i + 1)) ⟨0, 0, zv⟩ := by
  have hU : 0 < zv - zw := by linarith
  have a1 := mul_pos hU t1
  have a2 := mul_pos hU t2
  have a3 := mul_neg_of_neg_of_pos hm t1
  obtain ⟨b0, b1', b2', b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    simp only [bPts, b0, b1', b2', b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, LexTest,
      tst, hdet] <;>
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem tb_a' (hm : m < 0) (ht0 : 0 < t) (ht1 : t < 1) (hzv : 0 ≤ zv) (hzw : zw < 0)
    (hmp : (1 - t) * zv < mp) (hA : 0 < A) (hb2 : 0 < b2)
    (t1 : 0 < py * b1 - px * b2) (t2 : 0 < -(py * A))
    (q1 : 0 < r1 * b2 - r2 * b1) (q2 : 0 < (r1 - b1) * b2 + (r2 - b2) * (A - b1))
    (q3 : 0 < A * r2) (q4 : 0 < b2 * A) :
    ∀ i : ZMod 5, LexTest (-1) ⟨0, 0, 1⟩ ⟨px, py, 0⟩ (bPts zw m b1 b2 r1 r2 A i)
        (bPts zw m b1 b2 r1 r2 A (i + 1)) ⟨t * A, 0, mp⟩ := by
  have ht1' : 0 < 1 - t := by linarith
  have h0 : 0 ≤ (1 - t) * zv := mul_nonneg ht1'.le hzv
  have hK : 0 < mp - (1 - t) * zw := by nlinarith
  have a1 := mul_pos hK t2
  have a2 := mul_pos (mul_pos ht0 hA) hb2
  have a3 := mul_pos ht0 q2
  have a4 := mul_pos ht1' q1
  have a5 := mul_pos ht1' q3
  have a6 := mul_neg_of_neg_of_pos hm t1
  have a7 := mul_neg_of_neg_of_pos hm t2
  have a8 := mul_pos (mul_pos ht0 hA) t2
  obtain ⟨b0, b1', b2', b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    simp only [bPts, b0, b1', b2', b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, LexTest,
      tst, hdet] <;>
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

end BTests


end Type08Sp

namespace HFrame
open Type08Sp
variable {vb g u0 N : ℝ³} {fG : ℝ³ → ℝ} (Fr : HFrame vb g u0 N fG)
include Fr

/-- **Case B core** (`T'`, strictly not beyond): cycle `(w, a, f, r, g)` = `(d, a, c', b', c)` with `a`, `f`
over one screen point; `b`, `a'` hidden; `r` lexicographically not the minimum of `f, r, g`. -/
theorem tp_B {V : Finset ℝ³} {bP aP' fP rP gP wP aP : ℝ³}
    {px py t zv zw mp A b1 b2 r1 r2 m : ℝ}
    (hV : ∀ y ∈ V, y = bP ∨ y = aP' ∨ y = fP ∨ y = rP ∨ y = gP ∨ y = wP ∨ y = aP)
    (hw : wP ∈ V) (ha : aP ∈ V) (hf : fP ∈ V) (hr : rP ∈ V) (hg : gP ∈ V)
    (Φb : hfΦ vb g u0 fG bP = ⟨0, 0, zv⟩) (Φa' : hfΦ vb g u0 fG aP' = ⟨t * A, 0, mp⟩)
    (Φf : hfΦ vb g u0 fG fP = ⟨b1, b2, 0⟩) (Φr : hfΦ vb g u0 fG rP = ⟨r1, r2, 0⟩)
    (Φg : hfΦ vb g u0 fG gP = ⟨A, 0, 0⟩) (Φw : hfΦ vb g u0 fG wP = ⟨0, 0, zw⟩)
    (Φa : hfΦ vb g u0 fG aP = ⟨b1, b2, m⟩)
    (hA : 0 < A) (hb2 : 0 < b2) (hr2 : 0 < r2) (ht0 : 0 < t) (ht1 : t < 1) (hzv : 0 ≤ zv)
    (hzw : zw < 0) (hm : m < 0) (hmp : (1 - t) * zv < mp)
    (q1 : 0 < r1 * b2 - r2 * b1) (q2 : 0 < (r1 - b1) * b2 + (r2 - b2) * (A - b1))
    (t1 : 0 < py * b1 - px * b2) (t2 : 0 < -(py * A))
    (t3 : 0 < (r2 - b2) * px - (r1 - b1) * py)
    (hlex : px / ⟪hfE vb g u0, hfE vb g u0⟫ * b1 + py / ⟪N, N⟫ * b2 <
        px / ⟪hfE vb g u0, hfE vb g u0⟫ * r1 + py / ⟪N, N⟫ * r2 ∨
      px / ⟪hfE vb g u0, hfE vb g u0⟫ * A + py / ⟪N, N⟫ * 0 <
        px / ⟪hfE vb g u0, hfE vb g u0⟫ * r1 + py / ⟪N, N⟫ * r2) :
    IsRupert V := by
  have q3 : 0 < A * r2 := mul_pos hA hr2
  have q4 : 0 < b2 * A := mul_pos hb2 hA
  have himg : ∀ i : ZMod 5, hfΦ vb g u0 fG (quint wP aP fP rP gP i) = bPts zw m b1 b2 r1 r2 A i := by
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
  refine Fr.rupert_coords V (k := 5) (by norm_num) (quint wP aP fP rP gP) ?_ (-1) ⟨0, 0, 1⟩
    ⟨px, py, 0⟩ (Or.inr (Or.inr one_ne_zero)) ?_ ?_ Q5n Q5n_open (fun z c hc => Q5n_smul hc)
    (fun z K => Q5n_shift K) (fun z hinj => Q5n_unimodal hinj) ?_
  · intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
    exacts [hw, ha, hf, hr, hg]
  · intro i j h1 h2
    rw [himg i, himg (i + 1), himg j]
    exact tb_cyc hm t1 t2 t3 q1 q2 q3 q4 i j h1 h2
  · intro y hy hyx i
    rw [himg i, himg (i + 1)]
    rcases hV y hy with h | h | h | h | h | h | h
    · rw [h, Φb]; exact tb_b hm hzv hzw t1 t2 q1 q3 q4 i
    · rw [h, Φa']; exact tb_a' hm ht0 ht1 hzv hzw hmp hA hb2 t1 t2 q1 q2 q3 q4 i
    · exact absurd h (hyx 2)
    · exact absurd h (hyx 3)
    · exact absurd h (hyx 4)
    · exact absurd h (hyx 0)
    · exact absurd h (hyx 1)
  · set E := ⟪hfE vb g u0, hfE vb g u0⟫ with hEd
    set M := ⟪N, N⟫ with hMd
    set U := ⟪u0, u0⟫ with hUd
    have hL : ∀ (c : V3) (i : ZMod 5), lin E M U c (hfΦ vb g u0 fG (quint wP aP fP rP gP i)) =
        c.x / E * (bPts zw m b1 b2 r1 r2 A i).x + c.y / M * (bPts zw m b1 b2 r1 r2 A i).y +
          c.z / U * (bPts zw m b1 b2 r1 r2 A i).z := by
      intro c i; rw [himg i]; rfl
    have s0 : bPts zw m b1 b2 r1 r2 A 0 = ⟨0, 0, zw⟩ := rfl
    have s1 : bPts zw m b1 b2 r1 r2 A 1 = ⟨b1, b2, m⟩ := rfl
    have s2 : bPts zw m b1 b2 r1 r2 A 2 = ⟨b1, b2, 0⟩ := rfl
    have s3 : bPts zw m b1 b2 r1 r2 A 3 = ⟨r1, r2, 0⟩ := rfl
    have s4 : bPts zw m b1 b2 r1 r2 A 4 = ⟨A, 0, 0⟩ := rfl
    have hzU : zw / U < 0 := div_neg_of_neg_of_pos hzw hU
    have hmU : m / U < 0 := div_neg_of_neg_of_pos hm hU
    have k1 := eventually_pos_affine (A := 0 - m / U) (B := (px / E * b1 + py / M * b2) * (-1) +
      (px / E * b1 + py / M * b2)) (Or.inl (by linarith))
    have k2 := eventually_pos_affine (A := 0 - zw / U) (B := (px / E * 0 + py / M * 0) * (-1) +
      (px / E * A + py / M * 0)) (Or.inl (by linarith))
    have k3 : ∀ᶠ t in 𝓝[>] (0 : ℝ), (0 < (0:ℝ) + t * ((px / E * r1 + py / M * r2) - (px / E * b1 + py / M * b2))) ∨
        (0 < (0:ℝ) + t * ((px / E * r1 + py / M * r2) - (px / E * A + py / M * 0))) := by
      rcases hlex with h | h
      · exact (eventually_pos_affine (A := 0) (B := (px / E * r1 + py / M * r2) - (px / E * b1 + py / M * b2))
          (Or.inr ⟨rfl, by linarith⟩)).mono fun t ht => Or.inl ht
      · exact (eventually_pos_affine (A := 0) (B := (px / E * r1 + py / M * r2) - (px / E * A + py / M * 0))
          (Or.inr ⟨rfl, by linarith⟩)).mono fun t ht => Or.inr ht
    filter_upwards [k1, k2, k3] with t' a1' a2' a3'
    simp only [Q5n, Q5, hL, s0, s1, s2, s3, s4]
    refine ⟨by (ring_nf at *; linarith), by (ring_nf at *; linarith), ?_⟩
    rcases a3' with h | h
    · left; (ring_nf at *; linarith)
    · right; (ring_nf at *; linarith)

end HFrame

end Minimality
