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

/-- The cycle `(w, b, a', b', a)` of case C3 (`T'`, `r2 = b2`, `za' > zv`): `b'` and `c'` over one screen point. -/
def c3Pts (zv zw t A b1 b2 za' za r1 : ℝ) : ZMod 5 → V3 :=
  quint ⟨0, 0, zw⟩ ⟨0, 0, zv⟩ ⟨t * A, 0, za'⟩ ⟨r1, b2, 0⟩ ⟨b1, b2, za⟩

section C3Tests
variable {zv zw t A b1 b2 za' za r1 q : ℝ}

theorem tc3_cyc (hA : 0 < A) (ht0 : 0 < t) (hzv : 0 ≤ zv) (hzw : zw < 0) (hza : za < 0)
    (hzz : zv < za') (hb2 : 0 < b2) (hq0 : 0 < q) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, q⟩ (c3Pts zv zw t A b1 b2 za' za r1 i)
        (c3Pts zv zw t A b1 b2 za' za r1 (i + 1)) (c3Pts zv zw t A b1 b2 za' za r1 j) := by
  have hD : 0 < zv - zw := by linarith
  have htA : 0 < t * A := mul_pos ht0 hA
  have hzw' : zw < za' := by linarith
  have a1 := mul_pos hD hb2
  have a3 := mul_pos hb2 (sub_pos.mpr hzw')
  have a6 := mul_pos (neg_pos.mpr hza) hb2
  have a7 := mul_pos htA hD
  have c1 := mul_pos (sub_pos.mpr hzz) hb2
  have c3 := mul_pos htA (sub_pos.mpr hzz)
  obtain ⟨b0, b1', b2', b3, b4⟩ := zmod5_add_one
  intro i j h1 h2
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [c3Pts, b0, b1', b2', b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, LexTest,
      tst, hdet]
    first
    | (left; linarith)
    | (right; refine ⟨by ring, by linarith⟩)
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem tc3_f (hA : 0 < A) (ht0 : 0 < t) (hzv : 0 ≤ zv) (hzw : zw < 0) (hza : za < 0)
    (hzz : zv < za') (hb2 : 0 < b2) (hq0 : 0 < q) (hqr : q * b2 < za') (hbr : b1 < r1) :
    ∀ i : ZMod 5, LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, q⟩ (c3Pts zv zw t A b1 b2 za' za r1 i)
        (c3Pts zv zw t A b1 b2 za' za r1 (i + 1)) ⟨b1, b2, 0⟩ := by
  have hD : 0 < zv - zw := by linarith
  have hd : 0 < r1 - b1 := by linarith
  have a1 := mul_pos hD hb2
  have a2 := mul_pos (sub_pos.mpr hzz) hb2
  have a3 := mul_pos hd (sub_pos.mpr hqr)
  have a4 := mul_pos hd (neg_pos.mpr hza)
  have a5 := mul_pos hb2 (neg_pos.mpr hza)
  have a6 := mul_pos hd (mul_pos hq0 (neg_pos.mpr hza))
  have a7 := mul_pos hb2 (neg_pos.mpr hzw)
  have a8 := mul_pos hd hb2
  obtain ⟨b0, b1', b2', b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    simp only [c3Pts, b0, b1', b2', b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, LexTest,
      tst, hdet] <;>
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem tc3_g (hA : 0 < A) (ht0 : 0 < t) (ht1 : t < 1) (hzv : 0 ≤ zv) (hzw : zw < 0) (hza : za < 0)
    (hza' : (1 - t) * zv < za') (hzz : zv < za') (hb2 : 0 < b2) (hq0 : 0 < q) :
    ∀ i : ZMod 5, LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, q⟩ (c3Pts zv zw t A b1 b2 za' za r1 i)
        (c3Pts zv zw t A b1 b2 za' za r1 (i + 1)) ⟨A, 0, 0⟩ := by
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
    simp only [c3Pts, b0, b1', b2', b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, LexTest,
      tst, hdet] <;>
    first
    | (left; linarith)
    | (right; refine ⟨by ring, by linarith⟩)
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

end C3Tests


end Type08Sp

namespace HFrame
open Type08Sp
variable {vb g u0 N : ℝ³} {fG : ℝ³ → ℝ} (Fr : HFrame vb g u0 N fG)
include Fr

/-- **Case C3 core** (`T'`, `r2 = b2`, `z_a' > z_v`, `b1 < r1`, `A ≤ r1`): cycle `(d, b, a', b', a)` at the base
view `e`, tilt `-e_y + q e_z`; `c'` (under `b'` in depth) and `c` hidden. -/
theorem tp_C3 {V : Finset ℝ³} {bP aP' fP rP gP wP aP : ℝ³}
    {t zv zw A b1 b2 za' za r1 : ℝ}
    (hV : ∀ y ∈ V, y = bP ∨ y = aP' ∨ y = fP ∨ y = rP ∨ y = gP ∨ y = wP ∨ y = aP)
    (hw : wP ∈ V) (hb : bP ∈ V) (ha' : aP' ∈ V) (hr : rP ∈ V) (ha : aP ∈ V)
    (Φb : hfΦ vb g u0 fG bP = ⟨0, 0, zv⟩) (Φa' : hfΦ vb g u0 fG aP' = ⟨t * A, 0, za'⟩)
    (Φf : hfΦ vb g u0 fG fP = ⟨b1, b2, 0⟩) (Φr : hfΦ vb g u0 fG rP = ⟨r1, b2, 0⟩)
    (Φg : hfΦ vb g u0 fG gP = ⟨A, 0, 0⟩) (Φw : hfΦ vb g u0 fG wP = ⟨0, 0, zw⟩)
    (Φa : hfΦ vb g u0 fG aP = ⟨b1, b2, za⟩)
    (hA : 0 < A) (ht0 : 0 < t) (ht1 : t < 1) (hzv : 0 ≤ zv)
    (hzw : zw < 0) (hza : za < 0) (hza' : (1 - t) * zv < za') (hzz : zv < za')
    (hb2 : 0 < b2) (hr1 : A ≤ r1) (hd : b1 < r1) :
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
  have himg : ∀ i : ZMod 5, hfΦ vb g u0 fG (quint wP bP aP' rP aP i) =
      c3Pts zv zw t A b1 b2 za' za r1 i := by
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
    exact tc3_cyc hA ht0 hzv hzw hza hzz hb2 hq0 i j h1 h2
  · intro y hy hyx i
    rw [himg i, himg (i + 1)]
    rcases hV y hy with h | h | h | h | h | h | h
    · exact absurd h (hyx 1)
    · exact absurd h (hyx 2)
    · rw [h, Φf]; exact tc3_f hA ht0 hzv hzw hza hzz hb2 hq0 hqb hd i
    · exact absurd h (hyx 3)
    · rw [h, Φg]; exact tc3_g hA ht0 ht1 hzv hzw hza hza' hzz hb2 hq0 i
    · exact absurd h (hyx 0)
    · exact absurd h (hyx 4)
  · set E := ⟪hfE vb g u0, hfE vb g u0⟫ with hEd
    set M := ⟪N, N⟫ with hMd
    set U := ⟪u0, u0⟫ with hUd
    have hL : ∀ (c : V3) (i : ZMod 5), lin E M U c (hfΦ vb g u0 fG (quint wP bP aP' rP aP i)) =
        lin E M U c (c3Pts zv zw t A b1 b2 za' za r1 i) := by
      intro c i; rw [himg i]
    have s0 : c3Pts zv zw t A b1 b2 za' za r1 0 = ⟨0, 0, zw⟩ := rfl
    have s1 : c3Pts zv zw t A b1 b2 za' za r1 1 = ⟨0, 0, zv⟩ := rfl
    have s2 : c3Pts zv zw t A b1 b2 za' za r1 2 = ⟨t * A, 0, za'⟩ := rfl
    have s3 : c3Pts zv zw t A b1 b2 za' za r1 3 = ⟨r1, b2, 0⟩ := rfl
    have s4 : c3Pts zv zw t A b1 b2 za' za r1 4 = ⟨b1, b2, za⟩ := rfl
    have l32 : t * A < r1 := by nlinarith
    have l34 : b1 < r1 := hd
    set P := c3Pts zv zw t A b1 b2 za' za r1 with hP
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

end HFrame

end Minimality
