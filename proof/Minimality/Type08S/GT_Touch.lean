module

public import Minimality.Type08S.GT_H2

@[expose] public section

set_option autoImplicit true

/-!
# GT (replaces G7): the far triple tie family by lexicographic sector tilts (sp08b)

Files: `GT_Gen` (generic frame lemma `HFrame.rupert_coords`, proved), `GT_Sminus` (Lemma S−: cores
`sminus_n2`, `sminus_t4`, tilt choice `tilt_sminus`, proved), `GT_Facts` (Lemma 1.1, 1.2: proved),
`GT_H` (Proposition H: depth conditions `QH4 QH5 QT5a QT5b QT4` proved, test lemmas and core
`propH_n2_lt` proved), `GT_H2` (`propH_t4_c` proved), and this file: the S− assembly (proved) and the remaining statements of
Proposition H (proved), and the picture/wrapper statements.
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- Weighted horizontal inner products `(r - F)·y` of the four tests defining "strictly not beyond"
(`F, y ∈ {f, g}`), frame coordinates, metric weights `E, M`. -/
def NotBeyondW (E M f1 f2 r1 r2 g1 g2 : ℝ) : Prop :=
  (r1 - f1) * f1 / E + (r2 - f2) * f2 / M < 0 ∨ (r1 - f1) * g1 / E + (r2 - f2) * g2 / M < 0 ∨
  (r1 - g1) * f1 / E + (r2 - g2) * f2 / M < 0 ∨ (r1 - g1) * g1 / E + (r2 - g2) * g2 / M < 0

end Type08Sp

namespace HFrame
open Type08Sp
variable {vb g u0 N : ℝ³} {fG : ℝ³ → ℝ} (Fr : HFrame vb g u0 N fG)
include Fr

/-- **Lemma S− (N2), strictly not beyond, assembled** (sp08b §2): the picture data of
`sminus_n2` (shadow quadrilateral `(p, f, r, g)` strictly convex, `a` strictly inside, `2` upper
middle over `(p, f)`, `zw < 0 ≤ zv`) and `NotBeyondW` give `IsRupert`. -/
theorem close_sminus_n2 {V : Finset ℝ³} {cP mP fP rP gP wP aP : ℝ³}
    {σ s zv zw m f1 f2 r1 r2 g1 g2 a1 a2 a3 : ℝ}
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
    (hnb : NotBeyondW ⟪hfE vb g u0, hfE vb g u0⟫ ⟪N, N⟫ f1 f2 r1 r2 g1 g2) :
    IsRupert V := by
  obtain ⟨px, py, t1, t2, hlex⟩ := tilt_sminus Fr.hee Fr.hNN q4 hnb
  exact Fr.sminus_n2 hV hf hr hg hw Φc Φm Φf Φr Φg Φw Φa hs0 hs1 hzv hzw hm q1 q2 q3 q4 u1 u2 u3 u4
    (by linarith [t1]) (by linarith [t2]) hlex

/-- **Lemma S− (T4), strictly not beyond, assembled.** -/
theorem close_sminus_t4 {V : Finset ℝ³} {bP aP' fP rP gP wP aP : ℝ³}
    {σ s t zv zw m mp f1 f2 r1 r2 g1 g2 : ℝ}
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
    (hnb : NotBeyondW ⟪hfE vb g u0, hfE vb g u0⟫ ⟪N, N⟫ f1 f2 r1 r2 g1 g2) :
    IsRupert V := by
  obtain ⟨px, py, t1, t2, hlex⟩ := tilt_sminus Fr.hee Fr.hNN q4 hnb
  exact Fr.sminus_t4 hV hw ha hf hr hg Φb Φa' Φf Φr Φg Φw Φa hs0 hs1 ht0 ht1 hzv hzw hm hmp
    q1 q2 q3 q4 t1 t2 hlex

end HFrame

/-! ### Proposition H: the remaining cycles -/

namespace Type08Sp

/-- A strictly negative screen cross product is a (primary) lexicographic test, any tilt. -/
theorem lex_of_cross (cw : V3) {P Q S : V3} (h : crossYZ P Q S < 0) :
    LexTest (-1) ⟨1, 0, 0⟩ cw P Q S := by
  left; simp only [tst, hdet, crossYZ] at *; nlinarith

/-- A point of the screen axis `y = 0, z = 0` between `w` (`z = zw < 0`) and `c` (`z = zv ≥ 0`) is
strictly right of an edge if both ends are. -/
theorem cross_comb_axis {P Q : V3} {wx cx gx zv zw : ℝ} (hzv : 0 ≤ zv) (hzw : zw < 0)
    (hW : crossYZ P Q ⟨wx, 0, zw⟩ < 0) (hC : crossYZ P Q ⟨cx, 0, zv⟩ < 0) :
    crossYZ P Q ⟨gx, 0, 0⟩ < 0 := by
  have key : (zv - zw) * crossYZ P Q ⟨gx, 0, 0⟩ =
      zv * crossYZ P Q ⟨wx, 0, zw⟩ - zw * crossYZ P Q ⟨cx, 0, zv⟩ := by
    simp only [crossYZ]; ring
  by_contra h
  push Not at h
  nlinarith [mul_nonneg (by linarith : 0 ≤ zv - zw) h, mul_nonneg hzv (neg_nonneg.mpr hW.le),
    mul_pos (neg_pos.mpr hzw) (neg_pos.mpr hC)]

/-- The point `(b2, 0)` of the screen axis `z = 0` between `(0,0)` and `(r2, 0)`. -/
theorem cross_comb_row {P Q : V3} {gx fx rx b2 r2 : ℝ} (hb2 : 0 < b2) (hbr : b2 < r2)
    (hG : crossYZ P Q ⟨gx, 0, 0⟩ < 0) (hR : crossYZ P Q ⟨rx, r2, 0⟩ < 0) :
    crossYZ P Q ⟨fx, b2, 0⟩ < 0 := by
  have key : r2 * crossYZ P Q ⟨fx, b2, 0⟩ =
      (r2 - b2) * crossYZ P Q ⟨gx, 0, 0⟩ + b2 * crossYZ P Q ⟨rx, r2, 0⟩ := by
    simp only [crossYZ]; ring
  by_contra h
  push Not at h
  nlinarith [mul_nonneg (by linarith : 0 ≤ r2) h, mul_pos (sub_pos.mpr hbr) (neg_pos.mpr hG),
    mul_pos hb2 (neg_pos.mpr hR)]

/-- The cycle `(a', c, 2, a, c')` of Proposition H (N2, `r2 > b2`). -/
def h5Pts (zv zw s b1 b2 z2 a1 a2 a3 r1 r2 : ℝ) : ZMod 5 → V3 :=
  quint ⟨0, 0, zw⟩ ⟨0, 0, zv⟩ ⟨s * b1, s * b2, z2⟩ ⟨a1, a2, a3⟩ ⟨r1, r2, 0⟩

section N2ge
variable {zv zw s b1 b2 z2 A r1 r2 a1 a2 a3 t : ℝ}

theorem n2g_g (hA : 0 < A) (hs0 : 0 < s) (hs1 : s < 1) (hzv : 0 ≤ zv) (hzw : zw < 0)
    (hb2 : 0 < b2) (hr2 : 0 < r2) (ha3 : 0 < a3) (hz2 : (1 - s) * zv < z2)
    (ht : t * (s * b2) < z2) (hma : crossYZ ⟨s * b1, s * b2, z2⟩ ⟨a1, a2, a3⟩ ⟨A, 0, 0⟩ < 0) :
    ∀ i : ZMod 5,
      LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, -t⟩ (h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 r2 i)
        (h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 r2 (i + 1)) ⟨A, 0, 0⟩ := by
  have hs1' : 0 < 1 - s := by linarith
  have h0 : 0 ≤ (1 - s) * zv := mul_nonneg hs1'.le hzv
  have hz2' : 0 < z2 := by linarith
  have hD : 0 < zv - zw := by linarith
  have a1' := mul_pos hA hD
  have a2' := mul_pos hA hr2
  have a3' := mul_pos ha3 hr2
  have a4' := mul_pos hr2 (neg_pos.mpr hzw)
  have a5' := mul_pos hA (sub_pos.mpr ht)
  have a6' := mul_pos (mul_pos hs0 hb2) hD
  obtain ⟨b0, b1', b2', b3, b4⟩ := zmod5_add_one
  intro i
  have hma' := hma
  simp only [crossYZ] at hma'
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    simp only [h5Pts, b0, b1', b2', b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, LexTest,
      tst, hdet]
  · right; refine ⟨by ring, by nlinarith⟩
  · rcases lt_or_eq_of_le hzv with hz | hz
    · left; nlinarith [mul_pos (mul_pos hs0 hb2) hz]
    · subst hz
      right; refine ⟨by ring, by nlinarith⟩
  · left; nlinarith
  · left; nlinarith
  · left; nlinarith

theorem n2g_f (hs0 : 0 < s) (hs1 : s < 1) (hzv : 0 ≤ zv) (hzw : zw < 0)
    (hb2 : 0 < b2) (hbr : b2 < r2) (ha3 : 0 < a3) (hz2 : (1 - s) * zv < z2)
    (hma : crossYZ ⟨s * b1, s * b2, z2⟩ ⟨a1, a2, a3⟩ ⟨b1, b2, 0⟩ < 0) :
    ∀ i : ZMod 5,
      LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, -t⟩ (h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 r2 i)
        (h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 r2 (i + 1)) ⟨b1, b2, 0⟩ := by
  have hs1' : 0 < 1 - s := by linarith
  have h0 : 0 ≤ (1 - s) * zv := mul_nonneg hs1'.le hzv
  have hz2' : 0 < z2 := by linarith
  have hD : 0 < zv - zw := by linarith
  have a1' := mul_pos hb2 hD
  have a2' := mul_pos hb2 (sub_pos.mpr hz2)
  have a3' := mul_pos ha3 (sub_pos.mpr hbr)
  have a4' := mul_pos (neg_pos.mpr hzw) (sub_pos.mpr hbr)
  obtain ⟨b0, b1', b2', b3, b4⟩ := zmod5_add_one
  intro i
  have hma' := hma
  simp only [crossYZ] at hma'
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    simp only [h5Pts, b0, b1', b2', b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, LexTest,
      tst, hdet] <;>
    left <;> nlinarith

end N2ge

/-- The cycle `(2, b, a', b', a)` (T4a), also `(2, b, a', c', a)` (T4b) with `r := (b1, b2)`. -/
def t5aPts (zv zw s t A b1 b2 za' za r1 r2 : ℝ) : ZMod 5 → V3 :=
  quint ⟨0, 0, zw⟩ ⟨0, 0, zv⟩ ⟨t * A, 0, za'⟩ ⟨r1, r2, 0⟩ ⟨s * b1, s * b2, za⟩

section T4gen
variable {zv zw s t A b1 b2 za' za r1 r2 q : ℝ}

set_option maxHeartbeats 1000000 in
theorem t5_cyc (hA : 0 < A) (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (hzv : 0 ≤ zv)
    (hzw : zw < 0) (hza : za < (1 - s) * zw) (hzz : zv ≤ za') (hb2 : 0 < b2)
    (hsr : s * b2 < r2) (hq0 : 0 < q) (hqq : zv < za' ∨ q * r2 < za')
    (hq1 : crossYZ (t5aPts zv zw s t A b1 b2 za' za r1 r2 2) (t5aPts zv zw s t A b1 b2 za' za r1 r2 3)
      (t5aPts zv zw s t A b1 b2 za' za r1 r2 4) < 0)
    (hq2 : crossYZ (t5aPts zv zw s t A b1 b2 za' za r1 r2 3) (t5aPts zv zw s t A b1 b2 za' za r1 r2 4)
      (t5aPts zv zw s t A b1 b2 za' za r1 r2 0) < 0) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, q⟩ (t5aPts zv zw s t A b1 b2 za' za r1 r2 i)
        (t5aPts zv zw s t A b1 b2 za' za r1 r2 (i + 1)) (t5aPts zv zw s t A b1 b2 za' za r1 r2 j) := by
  have hs1' : 0 < 1 - s := by linarith
  have hza0 : za < 0 := by nlinarith
  have hD : 0 < zv - zw := by linarith
  have hr2 : 0 < r2 := by nlinarith
  have hsb : 0 < s * b2 := mul_pos hs0 hb2
  have htA : 0 < t * A := mul_pos ht0 hA
  have hzw' : zw < za' := by linarith
  have a1 := mul_pos hD hr2
  have a2 := mul_pos hD hsb
  have a3 := mul_pos hr2 (sub_pos.mpr hzw')
  have a4 := mul_pos hsb (sub_pos.mpr hzw')
  have a5 := mul_nonneg (sub_pos.mpr hsr).le hzv
  have a6 := mul_pos (neg_pos.mpr hza0) hr2
  have a7 := mul_pos htA hD
  have a8 := mul_pos hsb hD
  obtain ⟨b0, b1', b2', b3, b4⟩ := zmod5_add_one
  have hq1' := hq1
  have hq2' := hq2
  simp only [t5aPts, quint_2, quint_3, quint_4, quint_0, crossYZ] at hq1' hq2'
  intro i j h1 h2
  rcases lt_or_eq_of_le hzz with hz | hz
  · have c1 := mul_pos (sub_pos.mpr hz) hr2
    have c2 := mul_pos (sub_pos.mpr hz) hsb
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact absurd (by decide) h2
      | skip
    all_goals
      simp only [t5aPts, b0, b1', b2', b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, LexTest,
        tst, hdet]
      first
      | (left; linarith)
      | (right; refine ⟨by ring, by linarith⟩)
      | (left; nlinarith)
      | (right; refine ⟨by ring, by nlinarith⟩)
  · subst hz
    have hqr : q * r2 < zv := by
      rcases hqq with h | h
      · exact absurd h (lt_irrefl _)
      · exact h
    have hqs : q * (s * b2) < q * r2 := mul_lt_mul_of_pos_left hsr hq0
    have c1 := mul_pos htA (sub_pos.mpr hqr)
    have c2 := mul_pos htA (show 0 < zv - za - q * (s * b2) by linarith)
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact absurd (by decide) h2
      | skip
    all_goals
      simp only [t5aPts, b0, b1', b2', b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, LexTest,
        tst, hdet]
      first
      | (left; linarith)
      | (right; refine ⟨by ring, by linarith⟩)
      | (left; nlinarith)
      | (right; refine ⟨by ring, by nlinarith⟩)

/-- The axis point `g` (screen `(0,0)`) is hidden. -/
theorem t5_g (hA : 0 < A) (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1) (hzv : 0 ≤ zv)
    (hzw : zw < 0) (hza : za < (1 - s) * zw) (hza' : (1 - t) * zv < za') (hzz : zv ≤ za')
    (hb2 : 0 < b2) (hsr : s * b2 < r2) (hq0 : 0 < q) :
    ∀ i : ZMod 5,
      LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, q⟩ (t5aPts zv zw s t A b1 b2 za' za r1 r2 i)
        (t5aPts zv zw s t A b1 b2 za' za r1 r2 (i + 1)) ⟨A, 0, 0⟩ := by
  have hs1' : 0 < 1 - s := by linarith
  have hza0 : za < 0 := by nlinarith
  have hD : 0 < zv - zw := by linarith
  have hr2 : 0 < r2 := by nlinarith
  have hsb : 0 < s * b2 := mul_pos hs0 hb2
  have ht1' : 0 < 1 - t := by linarith
  have hza'0 : 0 < za' := by nlinarith [mul_nonneg ht1'.le hzv]
  have a1 := mul_pos hA hD
  have a2 := mul_pos hA (sub_pos.mpr hza')
  have a3 := mul_pos hr2 hza'0
  have a4 := mul_pos (neg_pos.mpr hza0) hr2
  have a5 := mul_pos hsb (neg_pos.mpr hzw)
  have a6 := mul_nonneg ht0.le hzv
  have a7 := mul_pos (mul_pos ht0 hA) hD
  obtain ⟨b0, b1', b2', b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    simp only [t5aPts, b0, b1', b2', b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, LexTest,
      tst, hdet] <;>
    first
    | (left; linarith)
    | (right; refine ⟨by ring, by linarith⟩)
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

/-- A hidden point strictly inside the screen row `z = 0` (screen `(y0, 0)`, `0 < y0 < r2`). -/
theorem t5_row {x0 y0 : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1) (hA : 0 < A)
    (hzv : 0 ≤ zv) (hzw : zw < 0) (hza : za < (1 - s) * zw) (hza' : (1 - t) * zv < za')
    (hzz : zv ≤ za') (hb2 : 0 < b2) (hsr : s * b2 < r2) (hq0 : 0 < q) (hy0 : 0 < y0)
    (hyr : y0 < r2) (hqy : zv < za' ∨ q * y0 < za')
    (hq2 : crossYZ (t5aPts zv zw s t A b1 b2 za' za r1 r2 3) (t5aPts zv zw s t A b1 b2 za' za r1 r2 4)
      (t5aPts zv zw s t A b1 b2 za' za r1 r2 0) < 0) :
    ∀ i : ZMod 5,
      LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, q⟩ (t5aPts zv zw s t A b1 b2 za' za r1 r2 i)
        (t5aPts zv zw s t A b1 b2 za' za r1 r2 (i + 1)) ⟨x0, y0, 0⟩ := by
  have hs1' : 0 < 1 - s := by linarith
  have hza0 : za < 0 := by nlinarith
  have hD : 0 < zv - zw := by linarith
  have hr2 : 0 < r2 := by linarith
  have hsb : 0 < s * b2 := mul_pos hs0 hb2
  have ht1' : 0 < 1 - t := by linarith
  have hza'0 : 0 < za' := by nlinarith [mul_nonneg ht1'.le hzv]
  have a1 := mul_pos hD hy0
  have a2 := mul_pos hza'0 (sub_pos.mpr hyr)
  have a3 := mul_pos (neg_pos.mpr hza0) (sub_pos.mpr hyr)
  have a4 := mul_pos hy0 (neg_pos.mpr hq2)
  have a5 := mul_pos (sub_pos.mpr hyr) (mul_pos hsb (neg_pos.mpr hzw))
  have a7 := mul_pos (mul_pos ht0 hA) hD
  obtain ⟨b0, b1', b2', b3, b4⟩ := zmod5_add_one
  simp only [t5aPts, quint_3, quint_4, quint_0, crossYZ] at hq2 a4
  intro i
  rcases lt_or_eq_of_le hzz with hz | hz
  · have c1 := mul_pos (sub_pos.mpr hz) hy0
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp only [t5aPts, b0, b1', b2', b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, LexTest,
        tst, hdet] <;>
      first
      | (left; linarith)
      | (right; refine ⟨by ring, by linarith⟩)
      | (left; nlinarith)
      | (right; refine ⟨by ring, by nlinarith⟩)
  · subst hz
    have hqr : q * y0 < zv := by
      rcases hqy with h | h
      · exact absurd h (lt_irrefl _)
      · exact h
    have c1 := mul_pos (mul_pos ht0 hA) (sub_pos.mpr hqr)
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp only [t5aPts, b0, b1', b2', b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, LexTest,
        tst, hdet] <;>
      first
      | (left; linarith)
      | (right; refine ⟨by ring, by linarith⟩)
      | (left; nlinarith)
      | (right; refine ⟨by ring, by nlinarith⟩)

end T4gen
end Type08Sp

namespace HFrame
open Type08Sp
variable {vb g u0 N : ℝ³} {fG : ℝ³ → ℝ} (Fr : HFrame vb g u0 N fG)
include Fr

/-- Core of Proposition H for N2 (cycle `(a', c, 2, a, c')`, `QH5`): the tests of the cycle and of
the hidden points `b`, `b'` are hypotheses; the depth condition needs `r1 > 0`, `s b1 < a1`. -/
theorem n2_core {V : Finset ℝ³} {cP mP fP rP gP wP aP : ℝ³}
    {s zv zw b1 b2 z2 A r1 r2 a1 a2 a3 : ℝ}
    (hV : ∀ y ∈ V, y = cP ∨ y = mP ∨ y = fP ∨ y = rP ∨ y = gP ∨ y = wP ∨ y = aP)
    (hc : cP ∈ V) (hm : mP ∈ V) (ha : aP ∈ V) (hr : rP ∈ V) (hw : wP ∈ V)
    (Φc : hfΦ vb g u0 fG cP = ⟨0, 0, zv⟩) (Φm : hfΦ vb g u0 fG mP = ⟨s * b1, s * b2, z2⟩)
    (Φf : hfΦ vb g u0 fG fP = ⟨b1, b2, 0⟩) (Φr : hfΦ vb g u0 fG rP = ⟨r1, r2, 0⟩)
    (Φg : hfΦ vb g u0 fG gP = ⟨A, 0, 0⟩) (Φw : hfΦ vb g u0 fG wP = ⟨0, 0, zw⟩)
    (Φa : hfΦ vb g u0 fG aP = ⟨a1, a2, a3⟩)
    (hA : 0 < A) (hs0 : 0 < s) (hs1 : s < 1) (hzv : 0 ≤ zv) (hzw : zw < 0) (hb2 : 0 < b2)
    (hz2 : (1 - s) * zv < z2) (hr1 : 0 < r1) (ha3 : 0 < a3) (hxa : s * b1 < a1)
    (tt : ℝ) (htt0 : 0 < tt)
    (hcyc : ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, -tt⟩ (h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 r2 i)
        (h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 r2 (i + 1)) (h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 r2 j))
    (hfT : ∀ i : ZMod 5,
      LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, -tt⟩ (h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 r2 i)
        (h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 r2 (i + 1)) ⟨b1, b2, 0⟩)
    (hgT : ∀ i : ZMod 5,
      LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, -tt⟩ (h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 r2 i)
        (h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 r2 (i + 1)) ⟨A, 0, 0⟩) :
    IsRupert V := by
  have himg : ∀ i : ZMod 5, hfΦ vb g u0 fG (quint wP cP mP aP rP i) =
      h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 r2 i := by
    intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
    · rw [quint_0, Φw]; rfl
    · rw [quint_1, Φc]; rfl
    · rw [quint_2, Φm]; rfl
    · rw [quint_3, Φa]; rfl
    · rw [quint_4, Φr]; rfl
  have hE := Fr.hee
  have hM := Fr.hNN
  have hU := Fr.hu
  refine Fr.rupert_coords V (k := 5) (by norm_num) (quint wP cP mP aP rP) ?_ (-1) ⟨1, 0, 0⟩
    ⟨0, -1, -tt⟩ (Or.inl one_ne_zero) ?_ ?_ QH5 QH5_open (fun z c hc => QH5_smul hc)
    (fun z K => QH5_shift K) (fun z hinj => QH5_unimodal hinj) ?_
  · intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
    exacts [hw, hc, hm, ha, hr]
  · intro i j h1 h2
    rw [himg i, himg (i + 1), himg j]
    exact hcyc i j h1 h2
  · intro y hy hyx i
    rw [himg i, himg (i + 1)]
    rcases hV y hy with h | h | h | h | h | h | h
    · exact absurd h (hyx 1)
    · exact absurd h (hyx 2)
    · rw [h, Φf]; exact hfT i
    · exact absurd h (hyx 4)
    · rw [h, Φg]; exact hgT i
    · exact absurd h (hyx 0)
    · exact absurd h (hyx 3)
  · set E := ⟪hfE vb g u0, hfE vb g u0⟫ with hEd
    set M := ⟪N, N⟫ with hMd
    set U := ⟪u0, u0⟫ with hUd
    have hL : ∀ (c : V3) (i : ZMod 5), lin E M U c (hfΦ vb g u0 fG (quint wP cP mP aP rP i)) =
        lin E M U c (h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 r2 i) := by
      intro c i; rw [himg i]
    have s0 : h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 r2 0 = ⟨0, 0, zw⟩ := rfl
    have s1 : h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 r2 1 = ⟨0, 0, zv⟩ := rfl
    have s2 : h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 r2 2 = ⟨s * b1, s * b2, z2⟩ := rfl
    have s3 : h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 r2 3 = ⟨a1, a2, a3⟩ := rfl
    have s4 : h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 r2 4 = ⟨r1, r2, 0⟩ := rfl
    set L := fun i => lin E M U ⟨1, 0, 0⟩ (h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 r2 i) with hLd
    set W := fun i => lin E M U ⟨0, -1, -tt⟩ (h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 r2 i) with hWd
    have l10 : L 1 - L 0 = 0 := by
      simp only [hLd, s0, s1, lin]; ring
    have w10 : 0 < W 0 - W 1 := by
      simp only [hWd, s0, s1, lin]
      have : 0 < tt * (zv - zw) / U := div_pos (mul_pos htt0 (by linarith)) hU
      have e : 0 / E * 0 + (-1) / M * 0 + (-tt) / U * zw - (0 / E * 0 + (-1) / M * 0 + (-tt) / U * zv)
          = tt * (zv - zw) / U := by field_simp; ring
      linarith
    have l40 : 0 < L 4 - L 0 := by
      simp only [hLd, s0, s4, lin]
      have := div_pos hr1 hE
      have e : 1 / E * r1 + 0 / M * r2 + 0 / U * 0 - (1 / E * 0 + 0 / M * 0 + 0 / U * zw) = r1 / E := by
        field_simp; ring
      rw [e]; exact this
    have l32 : 0 < L 3 - L 2 := by
      simp only [hLd, s2, s3, lin]
      have := div_pos (sub_pos.mpr hxa) hE
      have e : 1 / E * a1 + 0 / M * a2 + 0 / U * a3 -
          (1 / E * (s * b1) + 0 / M * (s * b2) + 0 / U * z2) = (a1 - s * b1) / E := by
        field_simp; ring
      rw [e]; exact this
    have k1 := eventually_pos_affine (A := L 0 - L 1) (B := W 0 - W 1) (Or.inr ⟨by linarith, w10⟩)
    have k2 := eventually_pos_affine (A := L 4 - L 0) (B := W 4 - W 0) (Or.inl l40)
    have k3 := eventually_pos_affine (A := L 3 - L 2) (B := W 3 - W 2) (Or.inl l32)
    filter_upwards [k1, k2, k3] with t' a1' a2' a3'
    simp only [QH5, hL]
    refine ⟨by linarith, by linarith, by linarith⟩

/-- **Proposition H, N2, `r2 > b2`** (cycle `(a', c, 2, a, c')`; Lemma 1.1 gives `r1 ≥ A, b1`;
Lemma 1.2 gives `s b1 < a1`, and `a3 > 0`).  The picture hypothesis `hcv` is the strict convex
position of the screen pentagon `(a', c, 2, a, c')` (all `crossYZ < 0`); `b` and `b'` are hidden
(`b'` ties with `c` at `zv = 0`, resolved by the tilt). -/
theorem propH_n2_ge {V : Finset ℝ³} {cP mP fP rP gP wP aP : ℝ³}
    {s zv zw b1 b2 z2 A r1 r2 a1 a2 a3 : ℝ}
    (hV : ∀ y ∈ V, y = cP ∨ y = mP ∨ y = fP ∨ y = rP ∨ y = gP ∨ y = wP ∨ y = aP)
    (hc : cP ∈ V) (hm : mP ∈ V) (ha : aP ∈ V) (hr : rP ∈ V) (hw : wP ∈ V)
    (Φc : hfΦ vb g u0 fG cP = ⟨0, 0, zv⟩) (Φm : hfΦ vb g u0 fG mP = ⟨s * b1, s * b2, z2⟩)
    (Φf : hfΦ vb g u0 fG fP = ⟨b1, b2, 0⟩) (Φr : hfΦ vb g u0 fG rP = ⟨r1, r2, 0⟩)
    (Φg : hfΦ vb g u0 fG gP = ⟨A, 0, 0⟩) (Φw : hfΦ vb g u0 fG wP = ⟨0, 0, zw⟩)
    (Φa : hfΦ vb g u0 fG aP = ⟨a1, a2, a3⟩)
    (hA : 0 < A) (hs0 : 0 < s) (hs1 : s < 1) (hzv : 0 ≤ zv) (hzw : zw < 0) (hb2 : 0 < b2)
    (hrb : b2 < r2) (hz2 : (1 - s) * zv < z2) (hr1 : 0 < r1) (ha3 : 0 < a3) (hxa : s * b1 < a1)
    (hcv : ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      crossYZ (h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 r2 i)
        (h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 r2 (i + 1))
        (h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 r2 j) < 0) :
    IsRupert V := by
  have hs1' : 0 < 1 - s := by linarith
  have h0 : 0 ≤ (1 - s) * zv := mul_nonneg hs1'.le hzv
  have hz2' : 0 < z2 := by linarith
  have hr2 : 0 < r2 := by linarith
  -- crossing facts for the edge `(2, a)` against `g` and `b`
  have c20 := hcv 2 0 (by decide) (by decide)
  have c21 := hcv 2 1 (by decide) (by decide)
  have c24 := hcv 2 4 (by decide) (by decide)
  obtain ⟨b0, b1', b2', b3, b4⟩ := zmod5_add_one
  simp only [h5Pts, b2', quint_0, quint_1, quint_2, quint_3, quint_4, b3] at c20 c21 c24
  have hmaG := cross_comb_axis (gx := A) hzv hzw c20 c21
  have hmaF := cross_comb_row (fx := b1) hb2 hrb hmaG c24
  set tt : ℝ := z2 / (2 * (s * b2)) with htt
  have htt0 : 0 < tt := by positivity
  have htt1 : tt * (s * b2) < z2 := by
    have : tt * (s * b2) = z2 / 2 := by rw [htt]; field_simp
    rw [this]; linarith
  exact Fr.n2_core hV hc hm ha hr hw Φc Φm Φf Φr Φg Φw Φa hA hs0 hs1 hzv hzw hb2 hz2 hr1 ha3 hxa tt htt0
    (fun i j h1 h2 => lex_of_cross _ (hcv i j h1 h2))
    (n2g_f hs0 hs1 hzv hzw hb2 hrb ha3 hz2 hmaF) (n2g_g hA hs0 hs1 hzv hzw hb2 hr2 ha3 hz2 htt1 hmaG)

end HFrame

namespace Type08Sp
theorem lin_u {E M U : ℝ} (P : V3) : lin E M U ⟨1, 0, 0⟩ P = P.x / E := by simp only [lin]; ring
theorem lin_diff {E M U : ℝ} (hE : 0 < E) {P Q : V3} (h : P.x < Q.x) :
    0 < lin E M U ⟨1, 0, 0⟩ Q - lin E M U ⟨1, 0, 0⟩ P := by
  rw [lin_u, lin_u, ← sub_div]; exact div_pos (by linarith) hE
theorem lin_eq {E M U : ℝ} {P Q : V3} (h : P.x = Q.x) :
    lin E M U ⟨1, 0, 0⟩ Q - lin E M U ⟨1, 0, 0⟩ P = 0 := by
  rw [lin_u, lin_u, h]; ring
theorem lin_tilt {E M U q : ℝ} (hU : 0 < U) (hq : 0 < q) {P Q : V3} (hy : P.y = Q.y)
    (h : P.z < Q.z) :
    0 < lin E M U ⟨0, -1, q⟩ Q - lin E M U ⟨0, -1, q⟩ P := by
  have e : lin E M U ⟨0, -1, q⟩ Q - lin E M U ⟨0, -1, q⟩ P = q / U * (Q.z - P.z) := by
    simp only [lin, hy]; ring
  rw [e]; exact mul_pos (div_pos hq hU) (by linarith)
end Type08Sp

namespace HFrame
open Type08Sp
variable {vb g u0 N : ℝ³} {fG : ℝ³ → ℝ} (Fr : HFrame vb g u0 N fG)
include Fr

/-- Core of Proposition H for T4 `(2, b, a', r, a)`, `QT5a`, tilt `-e_y + q e_z`: cycle and hidden-point
tests are hypotheses. -/
theorem t4a_core {V : Finset ℝ³} {bP aP' fP rP gP wP aP : ℝ³}
    {s t zv zw A b1 b2 za' za r1 r2 : ℝ}
    (hV : ∀ y ∈ V, y = bP ∨ y = aP' ∨ y = fP ∨ y = rP ∨ y = gP ∨ y = wP ∨ y = aP)
    (hw : wP ∈ V) (hb : bP ∈ V) (ha' : aP' ∈ V) (hr : rP ∈ V) (ha : aP ∈ V)
    (Φb : hfΦ vb g u0 fG bP = ⟨0, 0, zv⟩) (Φa' : hfΦ vb g u0 fG aP' = ⟨t * A, 0, za'⟩)
    (Φf : hfΦ vb g u0 fG fP = ⟨b1, b2, 0⟩) (Φr : hfΦ vb g u0 fG rP = ⟨r1, r2, 0⟩)
    (Φg : hfΦ vb g u0 fG gP = ⟨A, 0, 0⟩) (Φw : hfΦ vb g u0 fG wP = ⟨0, 0, zw⟩)
    (Φa : hfΦ vb g u0 fG aP = ⟨s * b1, s * b2, za⟩)
    (hA : 0 < A) (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1) (hzv : 0 ≤ zv)
    (hzw : zw < 0) (hza : za < (1 - s) * zw) (hza' : (1 - t) * zv < za') (hzz : zv < za')
    (hb2 : 0 < b2) (hr1 : A ≤ r1) (hr1b : b1 ≤ r1)
    (q : ℝ) (hq0 : 0 < q)
    (hcyc : ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, q⟩ (t5aPts zv zw s t A b1 b2 za' za r1 r2 i)
        (t5aPts zv zw s t A b1 b2 za' za r1 r2 (i + 1)) (t5aPts zv zw s t A b1 b2 za' za r1 r2 j))
    (hfT : ∀ i : ZMod 5,
      LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, q⟩ (t5aPts zv zw s t A b1 b2 za' za r1 r2 i)
        (t5aPts zv zw s t A b1 b2 za' za r1 r2 (i + 1)) ⟨b1, b2, 0⟩)
    (hgT : ∀ i : ZMod 5,
      LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, q⟩ (t5aPts zv zw s t A b1 b2 za' za r1 r2 i)
        (t5aPts zv zw s t A b1 b2 za' za r1 r2 (i + 1)) ⟨A, 0, 0⟩) :
    IsRupert V := by
  have hD : zw < zv := by linarith
  have htA : 0 < t * A := mul_pos ht0 hA
  have himg : ∀ i : ZMod 5, hfΦ vb g u0 fG (quint wP bP aP' rP aP i) =
      t5aPts zv zw s t A b1 b2 za' za r1 r2 i := by
    intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
    · rw [quint_0, Φw]; rfl
    · rw [quint_1, Φb]; rfl
    · rw [quint_2, Φa']; rfl
    · rw [quint_3, Φr]; rfl
    · rw [quint_4, Φa]; rfl
  have hE := Fr.hee
  have hM := Fr.hNN
  have hU := Fr.hu
  refine Fr.rupert_coords V (k := 5) (by norm_num) (quint wP bP aP' rP aP) ?_ (-1) ⟨1, 0, 0⟩
    ⟨0, -1, q⟩ (Or.inl one_ne_zero) ?_ ?_ QT5a QT5a_open (fun z c hc => QT5a_smul hc)
    (fun z K => QT5a_shift K) (fun z hinj => QT5a_unimodal hinj) ?_
  · intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
    exacts [hw, hb, ha', hr, ha]
  · intro i j h1 h2
    rw [himg i, himg (i + 1), himg j]
    exact hcyc i j h1 h2
  · intro y hy hyx i
    rw [himg i, himg (i + 1)]
    rcases hV y hy with h | h | h | h | h | h | h
    · exact absurd h (hyx 1)
    · exact absurd h (hyx 2)
    · rw [h, Φf]; exact hfT i
    · exact absurd h (hyx 3)
    · rw [h, Φg]; exact hgT i
    · exact absurd h (hyx 0)
    · exact absurd h (hyx 4)
  · set E := ⟪hfE vb g u0, hfE vb g u0⟫ with hEd
    set M := ⟪N, N⟫ with hMd
    set U := ⟪u0, u0⟫ with hUd
    have hL : ∀ (c : V3) (i : ZMod 5), lin E M U c (hfΦ vb g u0 fG (quint wP bP aP' rP aP i)) =
        lin E M U c (t5aPts zv zw s t A b1 b2 za' za r1 r2 i) := by
      intro c i; rw [himg i]
    have s0 : t5aPts zv zw s t A b1 b2 za' za r1 r2 0 = ⟨0, 0, zw⟩ := rfl
    have s1 : t5aPts zv zw s t A b1 b2 za' za r1 r2 1 = ⟨0, 0, zv⟩ := rfl
    have s2 : t5aPts zv zw s t A b1 b2 za' za r1 r2 2 = ⟨t * A, 0, za'⟩ := rfl
    have s3 : t5aPts zv zw s t A b1 b2 za' za r1 r2 3 = ⟨r1, r2, 0⟩ := rfl
    have s4 : t5aPts zv zw s t A b1 b2 za' za r1 r2 4 = ⟨s * b1, s * b2, za⟩ := rfl
    have l32 : (t * A) < r1 := by nlinarith
    have l34 : s * b1 < r1 := by
      rcases le_or_gt b1 0 with h | h
      · nlinarith
      · nlinarith
    set P := t5aPts zv zw s t A b1 b2 za' za r1 r2 with hP
    have k1 := eventually_pos_affine (A := lin E M U ⟨1, 0, 0⟩ (P 1) - lin E M U ⟨1, 0, 0⟩ (P 0))
      (B := lin E M U ⟨0, -1, q⟩ (P 1) - lin E M U ⟨0, -1, q⟩ (P 0))
      (Or.inr ⟨lin_eq (by rw [s0, s1]), lin_tilt hU hq0 (by rw [s0, s1]) (by rw [s0, s1]; exact hD)⟩)
    have k2 := eventually_pos_affine (A := lin E M U ⟨1, 0, 0⟩ (P 2) - lin E M U ⟨1, 0, 0⟩ (P 1))
      (B := lin E M U ⟨0, -1, q⟩ (P 2) - lin E M U ⟨0, -1, q⟩ (P 1))
      (Or.inl (lin_diff hE (by rw [s1, s2]; exact htA)))
    have k3 := eventually_pos_affine (A := lin E M U ⟨1, 0, 0⟩ (P 3) - lin E M U ⟨1, 0, 0⟩ (P 2))
      (B := lin E M U ⟨0, -1, q⟩ (P 3) - lin E M U ⟨0, -1, q⟩ (P 2))
      (Or.inl (lin_diff hE (by rw [s2, s3]; exact l32)))
    have k4 := eventually_pos_affine (A := lin E M U ⟨1, 0, 0⟩ (P 3) - lin E M U ⟨1, 0, 0⟩ (P 4))
      (B := lin E M U ⟨0, -1, q⟩ (P 3) - lin E M U ⟨0, -1, q⟩ (P 4))
      (Or.inl (lin_diff hE (by rw [s4, s3]; exact l34)))
    filter_upwards [k1, k2, k3, k4] with t' a1' a2' a3' a4'
    simp only [QT5a, hL]
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩


/-- **Proposition H, T4, `z_a' > z_v`, `r2 > b2`** (cycle `(2, b, a', b', a)`, `QT5a`; Lemma 1.1
gives `A ≤ r1`, `b1 ≤ r1`).  The picture hypotheses `hq1`, `hq2` are the strict turns of the
screen quadrilateral `(2, a', b', a)` at `b'` and at `a`; its turns at `2` and `a'` are automatic,
and `b` lies on the edge `2 a'` (the screen line `y = 0`), where the three collinear vertices are
ordered by the tilt (`hturn` of the plan is false for T4: `2, b, a'` are collinear). -/
theorem propH_t4_a {V : Finset ℝ³} {bP aP' fP rP gP wP aP : ℝ³}
    {s t zv zw A b1 b2 za' za r1 r2 : ℝ}
    (hV : ∀ y ∈ V, y = bP ∨ y = aP' ∨ y = fP ∨ y = rP ∨ y = gP ∨ y = wP ∨ y = aP)
    (hw : wP ∈ V) (hb : bP ∈ V) (ha' : aP' ∈ V) (hr : rP ∈ V) (ha : aP ∈ V)
    (Φb : hfΦ vb g u0 fG bP = ⟨0, 0, zv⟩) (Φa' : hfΦ vb g u0 fG aP' = ⟨t * A, 0, za'⟩)
    (Φf : hfΦ vb g u0 fG fP = ⟨b1, b2, 0⟩) (Φr : hfΦ vb g u0 fG rP = ⟨r1, r2, 0⟩)
    (Φg : hfΦ vb g u0 fG gP = ⟨A, 0, 0⟩) (Φw : hfΦ vb g u0 fG wP = ⟨0, 0, zw⟩)
    (Φa : hfΦ vb g u0 fG aP = ⟨s * b1, s * b2, za⟩)
    (hA : 0 < A) (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1) (hzv : 0 ≤ zv)
    (hzw : zw < 0) (hza : za < (1 - s) * zw) (hza' : (1 - t) * zv < za') (hzz : zv < za')
    (hb2 : 0 < b2) (hrb : b2 < r2) (hr1 : A ≤ r1) (hr1b : b1 ≤ r1)
    (hq1 : crossYZ (t5aPts zv zw s t A b1 b2 za' za r1 r2 2) (t5aPts zv zw s t A b1 b2 za' za r1 r2 3)
      (t5aPts zv zw s t A b1 b2 za' za r1 r2 4) < 0)
    (hq2 : crossYZ (t5aPts zv zw s t A b1 b2 za' za r1 r2 3) (t5aPts zv zw s t A b1 b2 za' za r1 r2 4)
      (t5aPts zv zw s t A b1 b2 za' za r1 r2 0) < 0) :
    IsRupert V := by
  have hsr : s * b2 < r2 := by nlinarith
  have hD : zw < zv := by linarith
  have htA : 0 < t * A := mul_pos ht0 hA
  exact Fr.t4a_core hV hw hb ha' hr ha Φb Φa' Φf Φr Φg Φw Φa hA hs0 hs1 ht0 ht1 hzv hzw hza hza' hzz hb2 hr1 hr1b
    1 one_pos (t5_cyc hA hs0 hs1 ht0 hzv hzw hza hzz.le hb2 hsr one_pos (Or.inl hzz) hq1 hq2)
    (t5_row hs0 hs1 ht0 ht1 hA hzv hzw hza hza' hzz.le hb2 hsr one_pos hb2 hrb (Or.inl hzz) hq2)
    (t5_g hA hs0 hs1 ht0 ht1 hzv hzw hza hza' hzz.le hb2 hsr one_pos)

/-- **Proposition H, T4, `z_a' ≥ z_v`, `b2 > r2`** (cycle `(2, b, a', c', a)`, `QT5b`, `b1 > 0`).
Same picture hypotheses as `propH_t4_a` for the screen quadrilateral `(2, a', c', a)`
(`hq1`, `hq2`: its turns at `c'` and `a`).  At `z_a' = z_v` the edge `b a'` is parallel to the base
view; the tilt `-e_y + q e_z`, `q = z_a'/(2 b2)`, then orders the edge consistently. -/
theorem propH_t4_b {V : Finset ℝ³} {bP aP' fP rP gP wP aP : ℝ³}
    {s t zv zw A b1 b2 za' za r1 r2 : ℝ}
    (hV : ∀ y ∈ V, y = bP ∨ y = aP' ∨ y = fP ∨ y = rP ∨ y = gP ∨ y = wP ∨ y = aP)
    (hw : wP ∈ V) (hb : bP ∈ V) (ha' : aP' ∈ V) (hf : fP ∈ V) (ha : aP ∈ V)
    (Φb : hfΦ vb g u0 fG bP = ⟨0, 0, zv⟩) (Φa' : hfΦ vb g u0 fG aP' = ⟨t * A, 0, za'⟩)
    (Φf : hfΦ vb g u0 fG fP = ⟨b1, b2, 0⟩) (Φr : hfΦ vb g u0 fG rP = ⟨r1, r2, 0⟩)
    (Φg : hfΦ vb g u0 fG gP = ⟨A, 0, 0⟩) (Φw : hfΦ vb g u0 fG wP = ⟨0, 0, zw⟩)
    (Φa : hfΦ vb g u0 fG aP = ⟨s * b1, s * b2, za⟩)
    (hA : 0 < A) (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1) (hzv : 0 ≤ zv)
    (hzw : zw < 0) (hza : za < (1 - s) * zw) (hza' : (1 - t) * zv < za') (hzz : zv ≤ za')
    (hb2 : 0 < b2) (hbr : r2 < b2) (hb1 : 0 < b1) (hr2 : 0 < r2) (hr1 : A ≤ r1) (hr1b : b1 ≤ r1)
    (hq1 : crossYZ (t5aPts zv zw s t A b1 b2 za' za b1 b2 2) (t5aPts zv zw s t A b1 b2 za' za b1 b2 3)
      (t5aPts zv zw s t A b1 b2 za' za b1 b2 4) < 0)
    (hq2 : crossYZ (t5aPts zv zw s t A b1 b2 za' za b1 b2 3) (t5aPts zv zw s t A b1 b2 za' za b1 b2 4)
      (t5aPts zv zw s t A b1 b2 za' za b1 b2 0) < 0) :
    IsRupert V := by
  have hsr : s * b2 < b2 := by nlinarith
  have hD : zw < zv := by linarith
  have htA : 0 < t * A := mul_pos ht0 hA
  have ht1' : 0 < 1 - t := by linarith
  have hza'0 : 0 < za' := by nlinarith [mul_nonneg ht1'.le hzv]
  set q : ℝ := za' / (2 * b2) with hqd
  have hq0 : 0 < q := by positivity
  have hqb : q * b2 < za' := by
    have : q * b2 = za' / 2 := by rw [hqd]; field_simp
    rw [this]; linarith
  have hqr : q * r2 < za' := by nlinarith
  have himg : ∀ i : ZMod 5, hfΦ vb g u0 fG (quint wP bP aP' fP aP i) =
      t5aPts zv zw s t A b1 b2 za' za b1 b2 i := by
    intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
    · rw [quint_0, Φw]; rfl
    · rw [quint_1, Φb]; rfl
    · rw [quint_2, Φa']; rfl
    · rw [quint_3, Φf]; rfl
    · rw [quint_4, Φa]; rfl
  have hE := Fr.hee
  have hM := Fr.hNN
  have hU := Fr.hu
  refine Fr.rupert_coords V (k := 5) (by norm_num) (quint wP bP aP' fP aP) ?_ (-1) ⟨1, 0, 0⟩
    ⟨0, -1, q⟩ (Or.inl one_ne_zero) ?_ ?_ QT5b QT5b_open (fun z c hc => QT5b_smul hc)
    (fun z K => QT5b_shift K) (fun z hinj => QT5b_unimodal hinj) ?_
  · intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
    exacts [hw, hb, ha', hf, ha]
  · intro i j h1 h2
    rw [himg i, himg (i + 1), himg j]
    exact t5_cyc hA hs0 hs1 ht0 hzv hzw hza hzz hb2 hsr hq0 (Or.inr hqb) hq1 hq2 i j h1 h2
  · intro y hy hyx i
    rw [himg i, himg (i + 1)]
    rcases hV y hy with h | h | h | h | h | h | h
    · exact absurd h (hyx 1)
    · exact absurd h (hyx 2)
    · exact absurd h (hyx 3)
    · rw [h, Φr]
      exact t5_row hs0 hs1 ht0 ht1 hA hzv hzw hza hza' hzz hb2 hsr hq0 hr2 hbr (Or.inr hqr) hq2 i
    · rw [h, Φg]; exact t5_g hA hs0 hs1 ht0 ht1 hzv hzw hza hza' hzz hb2 hsr hq0 i
    · exact absurd h (hyx 0)
    · exact absurd h (hyx 4)
  · set E := ⟪hfE vb g u0, hfE vb g u0⟫ with hEd
    set M := ⟪N, N⟫ with hMd
    set U := ⟪u0, u0⟫ with hUd
    have hL : ∀ (c : V3) (i : ZMod 5), lin E M U c (hfΦ vb g u0 fG (quint wP bP aP' fP aP i)) =
        lin E M U c (t5aPts zv zw s t A b1 b2 za' za b1 b2 i) := by
      intro c i; rw [himg i]
    have s0 : t5aPts zv zw s t A b1 b2 za' za b1 b2 0 = ⟨0, 0, zw⟩ := rfl
    have s1 : t5aPts zv zw s t A b1 b2 za' za b1 b2 1 = ⟨0, 0, zv⟩ := rfl
    have s2 : t5aPts zv zw s t A b1 b2 za' za b1 b2 2 = ⟨t * A, 0, za'⟩ := rfl
    have s3 : t5aPts zv zw s t A b1 b2 za' za b1 b2 3 = ⟨b1, b2, 0⟩ := rfl
    have s4 : t5aPts zv zw s t A b1 b2 za' za b1 b2 4 = ⟨s * b1, s * b2, za⟩ := rfl
    have l40 : 0 < s * b1 := mul_pos hs0 hb1
    have l43 : s * b1 < b1 := by nlinarith
    set P := t5aPts zv zw s t A b1 b2 za' za b1 b2 with hP
    have k1 := eventually_pos_affine (A := lin E M U ⟨1, 0, 0⟩ (P 1) - lin E M U ⟨1, 0, 0⟩ (P 0))
      (B := lin E M U ⟨0, -1, q⟩ (P 1) - lin E M U ⟨0, -1, q⟩ (P 0))
      (Or.inr ⟨lin_eq (by rw [s0, s1]), lin_tilt hU hq0 (by rw [s0, s1]) (by rw [s0, s1]; exact hD)⟩)
    have k2 := eventually_pos_affine (A := lin E M U ⟨1, 0, 0⟩ (P 2) - lin E M U ⟨1, 0, 0⟩ (P 1))
      (B := lin E M U ⟨0, -1, q⟩ (P 2) - lin E M U ⟨0, -1, q⟩ (P 1))
      (Or.inl (lin_diff hE (by rw [s1, s2]; exact htA)))
    have k3 := eventually_pos_affine (A := lin E M U ⟨1, 0, 0⟩ (P 4) - lin E M U ⟨1, 0, 0⟩ (P 0))
      (B := lin E M U ⟨0, -1, q⟩ (P 4) - lin E M U ⟨0, -1, q⟩ (P 0))
      (Or.inl (lin_diff hE (by rw [s0, s4]; exact l40)))
    have k4 := eventually_pos_affine (A := lin E M U ⟨1, 0, 0⟩ (P 3) - lin E M U ⟨1, 0, 0⟩ (P 4))
      (B := lin E M U ⟨0, -1, q⟩ (P 3) - lin E M U ⟨0, -1, q⟩ (P 4))
      (Or.inl (lin_diff hE (by rw [s4, s3]; exact l43)))
    filter_upwards [k1, k2, k3, k4] with t' a1' a2' a3' a4'
    simp only [QT5b, hL]
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩

end HFrame
end Minimality
