module

public import Minimality.Type08S.GT_Touch

@[expose] public section

set_option autoImplicit true

/-!
# GT: special positions of Proposition H

* `propH_n2_ge_eq`  : N2, `r2 = b2` (`b` over `c'`, `b1 < r1`), cycle `(a', c, 2, a, c')`, `QH5`.
* `propH_n2_flat`   : N2, `zv = 0`, `2̄ = ā` (screen positions of `2` and `a` coincide, `x_2 < x_a`).
* `propH_t4_a_eq`   : T4, `r2 = b2` (`c'` hidden on the side `[a', R]`, `b1 < r1`), cycle `(2,b,a',b',a)`.
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
section Special
variable {zv zw s t A b1 b2 z2 za' za r1 r2 a1 a2 a3 q tt : ℝ}

/-! ### T4, `r2 = b2` -/

theorem t5_fr (hs1 : s < 1)
    (hzv : 0 ≤ zv) (hzw : zw < 0) (hza : za < (1 - s) * zw)
    (hzz : zv < za') (hr2 : 0 < r2) (hsr : s * r2 < r2) (hq0 : 0 < q) (hqr : q * r2 < za')
    (hbr : b1 < r1)
    (hq2 : crossYZ (t5aPts zv zw s t A b1 r2 za' za r1 r2 3) (t5aPts zv zw s t A b1 r2 za' za r1 r2 4)
      (t5aPts zv zw s t A b1 r2 za' za r1 r2 0) < 0) :
    ∀ i : ZMod 5,
      LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, q⟩ (t5aPts zv zw s t A b1 r2 za' za r1 r2 i)
        (t5aPts zv zw s t A b1 r2 za' za r1 r2 (i + 1)) ⟨b1, r2, 0⟩ := by
  have hs1' : 0 < 1 - s := by linarith
  have hza0 : za < 0 := by nlinarith
  have hD : 0 < zv - zw := by linarith
  have hd : 0 < r1 - b1 := by linarith
  have a1 := mul_pos hD hr2
  have a2 := mul_pos (sub_pos.mpr hzz) hr2
  have a3 := mul_pos hd (sub_pos.mpr hqr)
  have a4 := mul_pos hd (show 0 < -za + q * (r2 - s * r2) by nlinarith [mul_pos hq0 (sub_pos.mpr hsr)])
  have a5 := neg_pos.mpr hq2
  simp only [t5aPts, quint_3, quint_4, quint_0, crossYZ] at a5
  obtain ⟨b0, b1', b2', b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    simp only [t5aPts, b0, b1', b2', b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, LexTest,
      tst, hdet] <;>
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

/-! ### N2, `r2 = b2` -/

theorem exists_tt (hs0 : 0 < s) (hb2 : 0 < b2) (hz2 : 0 < z2) (hzw : zw < 0) (hr2 : 0 < r2)
    (ha3 : 0 < a3) :
    ∃ tt : ℝ, 0 < tt ∧ tt * (s * b2) < z2 ∧ tt * r2 < -zw ∧ 0 < a3 + tt * (r2 - a2) := by
  have hsb : 0 < s * b2 := mul_pos hs0 hb2
  have c1 : 0 < z2 / (2 * (s * b2)) := by positivity
  have c2 : 0 < (-zw) / (2 * r2) := div_pos (neg_pos.mpr hzw) (by positivity)
  have c3 : 0 < a3 / (2 * (|r2 - a2| + 1)) := div_pos ha3 (by positivity)
  refine ⟨min (min (z2 / (2 * (s * b2))) ((-zw) / (2 * r2))) (a3 / (2 * (|r2 - a2| + 1))),
    lt_min (lt_min c1 c2) c3, ?_, ?_, ?_⟩
  · have h : min (min (z2 / (2 * (s * b2))) ((-zw) / (2 * r2))) (a3 / (2 * (|r2 - a2| + 1))) ≤
        z2 / (2 * (s * b2)) := (min_le_left _ _).trans (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at h
    nlinarith
  · have h : min (min (z2 / (2 * (s * b2))) ((-zw) / (2 * r2))) (a3 / (2 * (|r2 - a2| + 1))) ≤
        (-zw) / (2 * r2) := (min_le_left _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h
    nlinarith
  · have h : min (min (z2 / (2 * (s * b2))) ((-zw) / (2 * r2))) (a3 / (2 * (|r2 - a2| + 1))) ≤
        a3 / (2 * (|r2 - a2| + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h
    have hm : 0 < min (min (z2 / (2 * (s * b2))) ((-zw) / (2 * r2))) (a3 / (2 * (|r2 - a2| + 1))) :=
      lt_min (lt_min c1 c2) c3
    set m := min (min (z2 / (2 * (s * b2))) ((-zw) / (2 * r2))) (a3 / (2 * (|r2 - a2| + 1)))
    have habs : -(|r2 - a2|) ≤ r2 - a2 := neg_abs_le _
    nlinarith [mul_nonneg hm.le (abs_nonneg (r2 - a2))]

/-! ### N2, `zv = 0`, `2̄ = ā` -/

theorem n2f_cyc (hs0 : 0 < s) (hzw : zw < 0) (hb2 : 0 < b2) (hz2 : 0 < z2) (hsr : s * b2 < r2)
    (hxa : s * b1 < a1) (ht : tt * (s * b2) < z2) (htt0 : 0 < tt) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, -tt⟩ (h5Pts 0 zw s b1 b2 z2 a1 (s * b2) z2 r1 r2 i)
        (h5Pts 0 zw s b1 b2 z2 a1 (s * b2) z2 r1 r2 (i + 1))
        (h5Pts 0 zw s b1 b2 z2 a1 (s * b2) z2 r1 r2 j) := by
  have hr2 : 0 < r2 := by nlinarith [mul_pos hs0 hb2]
  have hsb : 0 < s * b2 := mul_pos hs0 hb2
  have hd : 0 < a1 - s * b1 := by linarith
  have hw : 0 < -zw := neg_pos.mpr hzw
  have p1 := mul_pos hw hsb
  have p2 := mul_pos hw hr2
  have p3 := mul_pos hz2 hr2
  have p4 := mul_pos hz2 hsb
  have p5 := mul_pos (sub_pos.mpr hsr) hz2
  have p6 := mul_pos hw (sub_pos.mpr hsr)
  have tc := mul_pos hd (show 0 < z2 - tt * (s * b2) by linarith)
  have ta := mul_pos hd (show 0 < z2 + tt * (r2 - s * b2) by nlinarith [mul_pos htt0 (sub_pos.mpr hsr)])
  have tw := mul_pos hd (show 0 < z2 - zw - tt * (s * b2) by linarith)
  obtain ⟨b0, b1', b2', b3, b4⟩ := zmod5_add_one
  intro i j h1 h2
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [h5Pts, b0, b1', b2', b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, LexTest,
      tst, hdet]
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem n2f_g (hA : 0 < A) (hs0 : 0 < s) (hzw : zw < 0) (hb2 : 0 < b2) (hz2 : 0 < z2)
    (hsr : s * b2 < r2) (hxa : s * b1 < a1) (ht : tt * (s * b2) < z2) :
    ∀ i : ZMod 5,
      LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, -tt⟩ (h5Pts 0 zw s b1 b2 z2 a1 (s * b2) z2 r1 r2 i)
        (h5Pts 0 zw s b1 b2 z2 a1 (s * b2) z2 r1 r2 (i + 1)) ⟨A, 0, 0⟩ := by
  have hr2 : 0 < r2 := by nlinarith [mul_pos hs0 hb2]
  have hd : 0 < a1 - s * b1 := by linarith
  have hw : 0 < -zw := neg_pos.mpr hzw
  have p1 := mul_pos hA hw
  have p2 := mul_pos hA (show 0 < z2 - tt * (s * b2) by linarith)
  have p3 := mul_pos hz2 hr2
  have p4 := mul_pos hw hr2
  have tc := mul_pos hd (show 0 < z2 - tt * (s * b2) by linarith)
  obtain ⟨b0, b1', b2', b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    simp only [h5Pts, b0, b1', b2', b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, LexTest,
      tst, hdet] <;>
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

end Special
end Type08Sp

namespace HFrame
open Type08Sp
variable {vb g u0 N : ℝ³} {fG : ℝ³ → ℝ} (Fr : HFrame vb g u0 N fG)
include Fr

/-- **Proposition H, T4, `r2 = b2`** (special position; `c'` over `b'`, `b1 < r1` by (B1′)): the
hidden `c'` coincides with `b'` on the screen and is ordered below it by the base view. -/
theorem propH_t4_a_eq {V : Finset ℝ³} {bP aP' fP rP gP wP aP : ℝ³}
    {s t zv zw A b1 b2 za' za r1 : ℝ}
    (hV : ∀ y ∈ V, y = bP ∨ y = aP' ∨ y = fP ∨ y = rP ∨ y = gP ∨ y = wP ∨ y = aP)
    (hw : wP ∈ V) (hb : bP ∈ V) (ha' : aP' ∈ V) (hr : rP ∈ V) (ha : aP ∈ V)
    (Φb : hfΦ vb g u0 fG bP = ⟨0, 0, zv⟩) (Φa' : hfΦ vb g u0 fG aP' = ⟨t * A, 0, za'⟩)
    (Φf : hfΦ vb g u0 fG fP = ⟨b1, b2, 0⟩) (Φr : hfΦ vb g u0 fG rP = ⟨r1, b2, 0⟩)
    (Φg : hfΦ vb g u0 fG gP = ⟨A, 0, 0⟩) (Φw : hfΦ vb g u0 fG wP = ⟨0, 0, zw⟩)
    (Φa : hfΦ vb g u0 fG aP = ⟨s * b1, s * b2, za⟩)
    (hA : 0 < A) (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1) (hzv : 0 ≤ zv)
    (hzw : zw < 0) (hza : za < (1 - s) * zw) (hza' : (1 - t) * zv < za') (hzz : zv < za')
    (hb2 : 0 < b2) (hr1 : A ≤ r1) (hd : b1 < r1)
    (hq1 : crossYZ (t5aPts zv zw s t A b1 b2 za' za r1 b2 2) (t5aPts zv zw s t A b1 b2 za' za r1 b2 3)
      (t5aPts zv zw s t A b1 b2 za' za r1 b2 4) < 0)
    (hq2 : crossYZ (t5aPts zv zw s t A b1 b2 za' za r1 b2 3) (t5aPts zv zw s t A b1 b2 za' za r1 b2 4)
      (t5aPts zv zw s t A b1 b2 za' za r1 b2 0) < 0) :
    IsRupert V := by
  have hsr : s * b2 < b2 := by nlinarith
  set q : ℝ := za' / (2 * b2) with hqd
  have hq0 : 0 < q := by
    have : 0 < za' := by nlinarith [mul_nonneg (sub_pos.mpr ht1).le hzv]
    positivity
  have hqb : q * b2 < za' := by
    have : q * b2 = za' / 2 := by rw [hqd]; field_simp
    have h' : 0 < za' := by nlinarith [mul_nonneg (sub_pos.mpr ht1).le hzv]
    rw [this]; linarith
  exact Fr.t4a_core hV hw hb ha' hr ha Φb Φa' Φf Φr Φg Φw Φa hA hs0 hs1 ht0 ht1 hzv hzw
    hr1 hd.le q hq0
    (t5_cyc hA hs0 hs1 ht0 hzv hzw hza hzz.le hb2 hsr hq0 (Or.inl hzz) hq1 hq2)
    (t5_fr hs1 hzv hzw hza hzz hb2 (by nlinarith) hq0 hqb hd hq2)
    (t5_g hA hs0 hs1 ht0 ht1 hzv hzw hza hza' hb2 hsr)

end HFrame
end Minimality
