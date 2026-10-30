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

/-- The cycle `(w, b, a', c', a)` of case C2 (`T'`, `r2 < b2`, `za' ≥ zv`). -/
def c2Pts (zv zw t A b1 b2 za' za : ℝ) : ZMod 5 → V3 :=
  quint ⟨0, 0, zw⟩ ⟨0, 0, zv⟩ ⟨t * A, 0, za'⟩ ⟨b1, b2, 0⟩ ⟨b1, b2, za⟩

section C2Tests
variable {zv zw t A b1 b2 za' za r1 r2 q : ℝ}

theorem tc2_cyc (hA : 0 < A) (ht0 : 0 < t) (hzv : 0 ≤ zv) (hzw : zw < 0) (hza : za < 0)
    (hzz : zv ≤ za') (hb2 : 0 < b2) (hq0 : 0 < q) (hqq : zv < za' ∨ q * b2 < za') :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, q⟩ (c2Pts zv zw t A b1 b2 za' za i)
        (c2Pts zv zw t A b1 b2 za' za (i + 1)) (c2Pts zv zw t A b1 b2 za' za j) := by
  have hD : 0 < zv - zw := by linarith
  have htA : 0 < t * A := mul_pos ht0 hA
  have hzw' : zw < za' := by linarith
  have a1 := mul_pos hD hb2
  have a3 := mul_pos hb2 (sub_pos.mpr hzw')
  have a6 := mul_pos (neg_pos.mpr hza) hb2
  have a7 := mul_pos htA hD
  obtain ⟨b0, b1', b2', b3, b4⟩ := zmod5_add_one
  intro i j h1 h2
  rcases lt_or_eq_of_le hzz with hz | hz
  · have c1 := mul_pos (sub_pos.mpr hz) hb2
    have c3 := mul_pos htA (sub_pos.mpr hz)
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact absurd (by decide) h2
      | skip
    all_goals
      simp only [c2Pts, b0, b1', b2', b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, LexTest,
        tst, hdet]
      first
      | (left; linarith)
      | (right; refine ⟨by ring, by linarith⟩)
      | (left; nlinarith)
      | (right; refine ⟨by ring, by nlinarith⟩)
  · subst hz
    have hqr : q * b2 < zv := by
      rcases hqq with h | h
      · exact absurd h (lt_irrefl _)
      · exact h
    have c1 := mul_pos htA (sub_pos.mpr hqr)
    have c2 := mul_pos htA (mul_pos hq0 (neg_pos.mpr hza))
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact absurd (by decide) h2
      | skip
    all_goals
      simp only [c2Pts, b0, b1', b2', b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, LexTest,
        tst, hdet]
      first
      | (left; linarith)
      | (right; refine ⟨by ring, by linarith⟩)
      | (left; nlinarith)
      | (right; refine ⟨by ring, by nlinarith⟩)

theorem tc2_g (hA : 0 < A) (ht0 : 0 < t) (ht1 : t < 1) (hzv : 0 ≤ zv) (hzw : zw < 0) (hza : za < 0)
    (hza' : (1 - t) * zv < za') (hzz : zv ≤ za') (hb2 : 0 < b2) (hq0 : 0 < q) :
    ∀ i : ZMod 5, LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, q⟩ (c2Pts zv zw t A b1 b2 za' za i)
        (c2Pts zv zw t A b1 b2 za' za (i + 1)) ⟨A, 0, 0⟩ := by
  have hD : 0 < zv - zw := by linarith
  have ht1' : 0 < 1 - t := by linarith
  have hza'0 : 0 < za' := by nlinarith [mul_nonneg ht1'.le hzv]
  have a1 := mul_pos hA hD
  have a2 := mul_pos hA (sub_pos.mpr hza')
  have a3 := mul_pos hb2 hza'0
  have a4 := mul_pos (neg_pos.mpr hza) hb2
  have a5 := mul_pos hb2 (neg_pos.mpr hzw)
  have a6 := mul_nonneg ht0.le hzv
  have a7 := mul_pos (mul_pos ht0 hA) hD
  obtain ⟨b0, b1', b2', b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    simp only [c2Pts, b0, b1', b2', b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, LexTest,
      tst, hdet] <;>
    first
    | (left; linarith)
    | (right; refine ⟨by ring, by linarith⟩)
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem tc2_row {x0 y0 : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hA : 0 < A)
    (hzv : 0 ≤ zv) (hzw : zw < 0) (hza : za < 0) (hza' : (1 - t) * zv < za')
    (hzz : zv ≤ za') (hb2 : 0 < b2) (hq0 : 0 < q) (hy0 : 0 < y0)
    (hyr : y0 < b2) (hqy : zv < za' ∨ q * y0 < za') :
    ∀ i : ZMod 5, LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, q⟩ (c2Pts zv zw t A b1 b2 za' za i)
        (c2Pts zv zw t A b1 b2 za' za (i + 1)) ⟨x0, y0, 0⟩ := by
  have hD : 0 < zv - zw := by linarith
  have ht1' : 0 < 1 - t := by linarith
  have hza'0 : 0 < za' := by nlinarith [mul_nonneg ht1'.le hzv]
  have a1 := mul_pos hD hy0
  have a2 := mul_pos hza'0 (sub_pos.mpr hyr)
  have a3 := mul_pos (neg_pos.mpr hza) (sub_pos.mpr hyr)
  have a4 := mul_pos hy0 (neg_pos.mpr hza)
  have a5 := mul_pos (sub_pos.mpr hyr) (neg_pos.mpr hzw)
  have a7 := mul_pos (mul_pos ht0 hA) hD
  obtain ⟨b0, b1', b2', b3, b4⟩ := zmod5_add_one
  intro i
  rcases lt_or_eq_of_le hzz with hz | hz
  · have c1 := mul_pos (sub_pos.mpr hz) hy0
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp only [c2Pts, b0, b1', b2', b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, LexTest,
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
      simp only [c2Pts, b0, b1', b2', b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, LexTest,
        tst, hdet] <;>
      first
      | (left; linarith)
      | (right; refine ⟨by ring, by linarith⟩)
      | (left; nlinarith)
      | (right; refine ⟨by ring, by nlinarith⟩)

end C2Tests


end Type08Sp

namespace HFrame
open Type08Sp
variable {vb g u0 N : ℝ³} {fG : ℝ³ → ℝ} (Fr : HFrame vb g u0 N fG)
include Fr

/-- **Case C2 core** (`T'`, `r2 < b2`, `z_a' ≥ z_v`, `b1 > 0`): cycle `(d, b, a', c', a)` at the base view `e`,
tilt `-e_y + q e_z`; `b'`, `c` hidden. -/
theorem tp_C2 {V : Finset ℝ³} {bP aP' fP rP gP wP aP : ℝ³}
    {t zv zw A b1 b2 za' za r1 r2 : ℝ}
    (hV : ∀ y ∈ V, y = bP ∨ y = aP' ∨ y = fP ∨ y = rP ∨ y = gP ∨ y = wP ∨ y = aP)
    (hw : wP ∈ V) (hb : bP ∈ V) (ha' : aP' ∈ V) (hf : fP ∈ V) (ha : aP ∈ V)
    (Φb : hfΦ vb g u0 fG bP = ⟨0, 0, zv⟩) (Φa' : hfΦ vb g u0 fG aP' = ⟨t * A, 0, za'⟩)
    (Φf : hfΦ vb g u0 fG fP = ⟨b1, b2, 0⟩) (Φr : hfΦ vb g u0 fG rP = ⟨r1, r2, 0⟩)
    (Φg : hfΦ vb g u0 fG gP = ⟨A, 0, 0⟩) (Φw : hfΦ vb g u0 fG wP = ⟨0, 0, zw⟩)
    (Φa : hfΦ vb g u0 fG aP = ⟨b1, b2, za⟩)
    (hA : 0 < A) (ht0 : 0 < t) (ht1 : t < 1) (hzv : 0 ≤ zv)
    (hzw : zw < 0) (hza : za < 0) (hza' : (1 - t) * zv < za') (hzz : zv ≤ za')
    (hb2 : 0 < b2) (hbr : r2 < b2) (hb1 : 0 < b1) (hr2 : 0 < r2) :
    IsRupert V := by
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
      c2Pts zv zw t A b1 b2 za' za i := by
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
    exact tc2_cyc hA ht0 hzv hzw hza hzz hb2 hq0 (Or.inr hqb) i j h1 h2
  · intro y hy hyx i
    rw [himg i, himg (i + 1)]
    rcases hV y hy with h | h | h | h | h | h | h
    · exact absurd h (hyx 1)
    · exact absurd h (hyx 2)
    · exact absurd h (hyx 3)
    · rw [h, Φr]
      exact tc2_row ht0 ht1 hA hzv hzw hza hza' hzz hb2 hq0 hr2 hbr (Or.inr hqr) i
    · rw [h, Φg]; exact tc2_g hA ht0 ht1 hzv hzw hza hza' hzz hb2 hq0 i
    · exact absurd h (hyx 0)
    · exact absurd h (hyx 4)
  · set E := ⟪hfE vb g u0, hfE vb g u0⟫ with hEd
    set M := ⟪N, N⟫ with hMd
    set U := ⟪u0, u0⟫ with hUd
    have hL : ∀ (c : V3) (i : ZMod 5), lin E M U c (hfΦ vb g u0 fG (quint wP bP aP' fP aP i)) =
        lin E M U c (c2Pts zv zw t A b1 b2 za' za i) := by
      intro c i; rw [himg i]
    have s0 : c2Pts zv zw t A b1 b2 za' za 0 = ⟨0, 0, zw⟩ := rfl
    have s1 : c2Pts zv zw t A b1 b2 za' za 1 = ⟨0, 0, zv⟩ := rfl
    have s2 : c2Pts zv zw t A b1 b2 za' za 2 = ⟨t * A, 0, za'⟩ := rfl
    have s3 : c2Pts zv zw t A b1 b2 za' za 3 = ⟨b1, b2, 0⟩ := rfl
    have s4 : c2Pts zv zw t A b1 b2 za' za 4 = ⟨b1, b2, za⟩ := rfl
    have l40 : 0 < b1 := hb1
    have l43 : lin E M U ⟨1, 0, 0⟩ (c2Pts zv zw t A b1 b2 za' za 3) -
        lin E M U ⟨1, 0, 0⟩ (c2Pts zv zw t A b1 b2 za' za 4) = 0 := by
      simp only [s3, s4, lin]; ring
    have w43 : 0 < lin E M U ⟨0, -1, q⟩ (c2Pts zv zw t A b1 b2 za' za 3) -
        lin E M U ⟨0, -1, q⟩ (c2Pts zv zw t A b1 b2 za' za 4) := by
      simp only [s3, s4, lin]
      have : 0 < q * (-za) / U := div_pos (mul_pos hq0 (by linarith)) hU
      have e : 0 / E * b1 + (-1) / M * b2 + q / U * 0 -
          (0 / E * b1 + (-1) / M * b2 + q / U * za) = q * (-za) / U := by field_simp; ring
      linarith
    set P := c2Pts zv zw t A b1 b2 za' za with hP
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
      (Or.inr ⟨l43, w43⟩)
    filter_upwards [k1, k2, k3, k4] with t' a1' a2' a3' a4'
    simp only [QT5b, hL]
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩

end HFrame

end Minimality
