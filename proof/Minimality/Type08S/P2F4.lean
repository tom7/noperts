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

/-- The cycle `(w, b, c', a)` of case C1 (`T'`, `r2 < b2`, `za' < zv`): `a` directly below `c'`. -/
def c1Pts (zv zw b1 b2 za : ℝ) : ZMod 4 → V3 :=
  quad ⟨0, 0, zw⟩ ⟨0, 0, zv⟩ ⟨b1, b2, 0⟩ ⟨b1, b2, za⟩

section C1Tests
variable {zv zw b1 b2 za A tA za' r1 r2 : ℝ}

theorem tc1_cyc (hzv : 0 < zv) (hzw : zw < 0) (hb2 : 0 < b2) (hza : za < 0) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, 1⟩ (c1Pts zv zw b1 b2 za i) (c1Pts zv zw b1 b2 za (i + 1))
        (c1Pts zv zw b1 b2 za j) := by
  have hD : 0 < zv - zw := by linarith
  have a1 := mul_pos hb2 hD
  have a3 := mul_pos hb2 (neg_pos.mpr hza)
  have a4 := mul_pos hb2 hzv
  intro i j h1 h2
  obtain ⟨b0, b1', b2', b3⟩ := zmod4_add_one
  rcases zmod4_pairs i j h1 h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [c1Pts, b0, b1', b2', b3, quad_0, quad_1, quad_2, quad_3, LexTest, tst, hdet] <;>
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem tc1_c (hzv : 0 < zv) (hzw : zw < 0) (hb2 : 0 < b2) (hza : za < 0) (hA : 0 < A) :
    ∀ i : ZMod 4, LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, 1⟩ (c1Pts zv zw b1 b2 za i)
        (c1Pts zv zw b1 b2 za (i + 1)) ⟨A, 0, 0⟩ := by
  have hD : 0 < zv - zw := by linarith
  have a1 := mul_pos hA hD
  have a2 := mul_pos hb2 hzv
  have a3 := mul_pos hb2 (neg_pos.mpr hza)
  have a4 := mul_pos hb2 (neg_pos.mpr hzw)
  obtain ⟨b0, b1', b2', b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    simp only [c1Pts, b0, b1', b2', b3, quad_0, quad_1, quad_2, quad_3, LexTest, tst, hdet] <;>
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem tc1_a' (hzv : 0 < zv) (hzw : zw < 0) (hb2 : 0 < b2) (hza : za < 0) (htA : 0 < tA)
    (hza'0 : 0 ≤ za') (hza'v : za' < zv) :
    ∀ i : ZMod 4, LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, 1⟩ (c1Pts zv zw b1 b2 za i)
        (c1Pts zv zw b1 b2 za (i + 1)) ⟨tA, 0, za'⟩ := by
  have hD : 0 < zv - zw := by linarith
  have a1 := mul_pos htA hD
  have a2 := mul_pos hb2 (sub_pos.mpr hza'v)
  have a3 := mul_nonneg hb2.le hza'0
  have a4 := mul_pos hb2 (neg_pos.mpr hza)
  have a5 := mul_pos hb2 (sub_pos.mpr (lt_of_lt_of_le hzw hza'0))
  obtain ⟨b0, b1', b2', b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    simp only [c1Pts, b0, b1', b2', b3, quad_0, quad_1, quad_2, quad_3, LexTest, tst, hdet] <;>
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem tc1_b' (hzv : 0 < zv) (hzw : zw < 0) (hb2 : 0 < b2) (hza : za < 0) (hr2 : 0 < r2)
    (hrb : r2 < b2) :
    ∀ i : ZMod 4, LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, 1⟩ (c1Pts zv zw b1 b2 za i)
        (c1Pts zv zw b1 b2 za (i + 1)) ⟨r1, r2, 0⟩ := by
  have hD : 0 < zv - zw := by linarith
  have a1 := mul_pos hr2 hD
  have a2 := mul_pos hzv (sub_pos.mpr hrb)
  have a3 := mul_pos (neg_pos.mpr hza) (sub_pos.mpr hrb)
  have a4 := mul_pos (sub_pos.mpr hrb) (neg_pos.mpr hzw)
  have a5 := mul_pos hr2 (neg_pos.mpr hza)
  have a6 := mul_pos hr2 hb2
  obtain ⟨b0, b1', b2', b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    simp only [c1Pts, b0, b1', b2', b3, quad_0, quad_1, quad_2, quad_3, LexTest, tst, hdet] <;>
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

end C1Tests


end Type08Sp

namespace HFrame
open Type08Sp
variable {vb g u0 N : ℝ³} {fG : ℝ³ → ℝ} (Fr : HFrame vb g u0 N fG)
include Fr

/-- **Case C1 core** (`T'`, `r2 < b2`, `z_a' < z_v`, `b1 > 0`): cycle `(d, b, c', a)` at the base view `e`,
tilt `-e_y + e_z`; `a'`, `b'`, `c` hidden. -/
theorem tp_C1 {V : Finset ℝ³} {bP aP' fP rP gP wP aP : ℝ³}
    {t zv zw A b1 b2 za' za r1 r2 : ℝ}
    (hV : ∀ y ∈ V, y = bP ∨ y = aP' ∨ y = fP ∨ y = rP ∨ y = gP ∨ y = wP ∨ y = aP)
    (hw : wP ∈ V) (hb : bP ∈ V) (hf : fP ∈ V) (ha : aP ∈ V)
    (Φb : hfΦ vb g u0 fG bP = ⟨0, 0, zv⟩) (Φa' : hfΦ vb g u0 fG aP' = ⟨t * A, 0, za'⟩)
    (Φf : hfΦ vb g u0 fG fP = ⟨b1, b2, 0⟩) (Φr : hfΦ vb g u0 fG rP = ⟨r1, r2, 0⟩)
    (Φg : hfΦ vb g u0 fG gP = ⟨A, 0, 0⟩) (Φw : hfΦ vb g u0 fG wP = ⟨0, 0, zw⟩)
    (Φa : hfΦ vb g u0 fG aP = ⟨b1, b2, za⟩)
    (hA : 0 < A) (ht0 : 0 < t) (ht1 : t < 1) (hzv : 0 ≤ zv)
    (hzw : zw < 0) (hza : za < 0) (hza' : (1 - t) * zv < za') (hzz : za' < zv)
    (hb2 : 0 < b2) (hrb : r2 < b2) (hb1 : 0 < b1) (hr2 : 0 < r2) :
    IsRupert V := by
  have ht1' : 0 < 1 - t := by linarith
  have hza'0 : 0 ≤ za' := by nlinarith [mul_nonneg ht1'.le hzv]
  have hzv0 : 0 < zv := by linarith
  have himg : ∀ i : ZMod 4, hfΦ vb g u0 fG (quad wP bP fP aP i) = c1Pts zv zw b1 b2 za i := by
    intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl
    · rw [quad_0, Φw]; rfl
    · rw [quad_1, Φb]; rfl
    · rw [quad_2, Φf]; rfl
    · rw [quad_3, Φa]; rfl
  have hE := Fr.hee
  have hM := Fr.hNN
  have hU := Fr.hu
  refine Fr.rupert_coords V (k := 4) (by norm_num) (quad wP bP fP aP) ?_ (-1) ⟨1, 0, 0⟩
    ⟨0, -1, 1⟩ (Or.inl one_ne_zero) ?_ ?_ QT4 QT4_open (fun z c hc => QT4_smul hc)
    (fun z K => QT4_shift K) (fun z hinj => QT4_unimodal hinj) ?_
  · intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl
    exacts [hw, hb, hf, ha]
  · intro i j h1 h2
    rw [himg i, himg (i + 1), himg j]
    exact tc1_cyc hzv0 hzw hb2 hza i j h1 h2
  · intro y hy hyx i
    rw [himg i, himg (i + 1)]
    rcases hV y hy with h | h | h | h | h | h | h
    · exact absurd h (hyx 1)
    · rw [h, Φa']; exact tc1_a' hzv0 hzw hb2 hza (mul_pos ht0 hA) hza'0 hzz i
    · exact absurd h (hyx 2)
    · rw [h, Φr]; exact tc1_b' hzv0 hzw hb2 hza hr2 hrb i
    · rw [h, Φg]; exact tc1_c hzv0 hzw hb2 hza hA i
    · exact absurd h (hyx 0)
    · exact absurd h (hyx 3)
  · set E := ⟪hfE vb g u0, hfE vb g u0⟫ with hEd
    set M := ⟪N, N⟫ with hMd
    set U := ⟪u0, u0⟫ with hUd
    have hL : ∀ (c : V3) (i : ZMod 4), lin E M U c (hfΦ vb g u0 fG (quad wP bP fP aP i)) =
        lin E M U c (c1Pts zv zw b1 b2 za i) := by
      intro c i; rw [himg i]
    have s0 : c1Pts zv zw b1 b2 za 0 = ⟨0, 0, zw⟩ := rfl
    have s1 : c1Pts zv zw b1 b2 za 1 = ⟨0, 0, zv⟩ := rfl
    have s2 : c1Pts zv zw b1 b2 za 2 = ⟨b1, b2, 0⟩ := rfl
    have s3 : c1Pts zv zw b1 b2 za 3 = ⟨b1, b2, za⟩ := rfl
    set L := fun i => lin E M U ⟨1, 0, 0⟩ (c1Pts zv zw b1 b2 za i) with hLd
    set W := fun i => lin E M U ⟨0, -1, 1⟩ (c1Pts zv zw b1 b2 za i) with hWd
    have l01 : L 0 - L 1 = 0 := by
      simp only [hLd, s0, s1, lin]; ring
    have w01 : 0 < W 1 - W 0 := by
      simp only [hWd, s0, s1, lin]
      have : 0 < (zv - zw) / U := div_pos (by linarith) hU
      have e : 0 / E * 0 + (-1) / M * 0 + 1 / U * zv - (0 / E * 0 + (-1) / M * 0 + 1 / U * zw)
          = (zv - zw) / U := by field_simp; ring
      linarith
    have l21 : 0 < L 2 - L 1 := by
      simp only [hLd, s1, s2, lin]
      have := div_pos hb1 hE
      have e : 1 / E * b1 + 0 / M * b2 + 0 / U * 0 - (1 / E * 0 + 0 / M * 0 + 0 / U * zv) = b1 / E := by
        field_simp; ring
      rw [e]; exact this
    have l23 : L 2 - L 3 = 0 := by
      simp only [hLd, s2, s3, lin]; ring
    have w23 : 0 < W 2 - W 3 := by
      simp only [hWd, s2, s3, lin]
      have : 0 < (-za) / U := div_pos (by linarith) hU
      have e : 1 * 0 / E * 0 + 0 = 0 := by ring
      have e2 : 0 / E * b1 + (-1) / M * b2 + 1 / U * 0 -
          (0 / E * b1 + (-1) / M * b2 + 1 / U * za) = (-za) / U := by field_simp; ring
      linarith
    have l30 : 0 < L 3 - L 0 := by
      simp only [hLd, s0, s3, lin]
      have := div_pos hb1 hE
      have e : 1 / E * b1 + 0 / M * b2 + 0 / U * za -
          (1 / E * 0 + 0 / M * 0 + 0 / U * zw) = b1 / E := by
        field_simp; ring
      rw [e]; exact this
    have k1 := eventually_pos_affine (A := L 1 - L 0) (B := W 1 - W 0) (Or.inr ⟨by linarith, w01⟩)
    have k2 := eventually_pos_affine (A := L 2 - L 1) (B := W 2 - W 1) (Or.inl l21)
    have k3 := eventually_pos_affine (A := L 2 - L 3) (B := W 2 - W 3) (Or.inr ⟨l23, w23⟩)
    have k4 := eventually_pos_affine (A := L 3 - L 0) (B := W 3 - W 0) (Or.inl l30)
    filter_upwards [k1, k2, k3, k4] with t' a1' a2' a3' a4'
    simp only [QT4, hL]
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩

end HFrame

end Minimality
