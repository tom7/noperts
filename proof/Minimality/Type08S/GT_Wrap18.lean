module

public import Minimality.Type08S.GT_Wrap17
public import Minimality.Type08S.GT_Special

@[expose] public section

set_option autoImplicit true

/-!
# GT wrapper, part 18: Proposition H, N2, `r2 = b2`, corrected (`propH_n2_ge_eq2`)
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
variable {s zv zw b1 b2 z2 A r1 a1 a2 a3 tt : ℝ}

theorem n2e_f2 (hs0 : 0 < s) (hs1 : s < 1) (hzv : 0 ≤ zv) (hzw : zw < 0)
    (hb2 : 0 < b2) (ha3 : 0 < a3) (hz2 : (1 - s) * zv < z2) (hd : b1 < r1)
    (hbr : tt * b2 < -zw) (hta : 0 < a3 + tt * (b2 - a2))
    (hrow2 : LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, -tt⟩ (h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 b2 2)
        (h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 b2 (2 + 1)) ⟨b1, b2, 0⟩) :
    ∀ i : ZMod 5,
      LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, -tt⟩ (h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 b2 i)
        (h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 b2 (i + 1)) ⟨b1, b2, 0⟩ := by
  have hs1' : 0 < 1 - s := by linarith
  have h0 : 0 ≤ (1 - s) * zv := mul_nonneg hs1'.le hzv
  have hD : 0 < zv - zw := by linarith
  have hd' : 0 < r1 - b1 := by linarith
  have a1' := mul_pos hb2 hD
  have a2' := mul_pos hb2 (sub_pos.mpr hz2)
  have a3' := mul_pos hd' hta
  have a4' := mul_pos hd' (show 0 < -zw - tt * b2 by linarith)
  obtain ⟨b0, b1', b2', b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
  · simp only [h5Pts, b0, b1', b2', b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, LexTest, tst, hdet]
    first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩)
  · simp only [h5Pts, b0, b1', b2', b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, LexTest, tst, hdet]
    first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩)
  · exact hrow2
  · simp only [h5Pts, b0, b1', b2', b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, LexTest, tst, hdet]
    first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩)
  · simp only [h5Pts, b0, b1', b2', b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, LexTest, tst, hdet]
    first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩)

end Type08Sp

namespace HFrame
open Type08Sp
variable {vb g u0 N : ℝ³} {fG : ℝ³ → ℝ} (Fr : HFrame vb g u0 N fG)
include Fr

/-- **Proposition H, N2, `r2 = b2`** (corrected: the triple `(2, a, c')` and `b` are screen-collinear,
ordered by the tilt rows `hl24, hl32, hlb`). -/
theorem propH_n2_ge_eq2 {V : Finset ℝ³} {cP mP fP rP gP wP aP : ℝ³}
    {s zv zw b1 b2 z2 A r1 a1 a2 a3 : ℝ}
    (hV : ∀ y ∈ V, y = cP ∨ y = mP ∨ y = fP ∨ y = rP ∨ y = gP ∨ y = wP ∨ y = aP)
    (hc : cP ∈ V) (hm : mP ∈ V) (ha : aP ∈ V) (hr : rP ∈ V) (hw : wP ∈ V)
    (Φc : hfΦ vb g u0 fG cP = ⟨0, 0, zv⟩) (Φm : hfΦ vb g u0 fG mP = ⟨s * b1, s * b2, z2⟩)
    (Φf : hfΦ vb g u0 fG fP = ⟨b1, b2, 0⟩) (Φr : hfΦ vb g u0 fG rP = ⟨r1, b2, 0⟩)
    (Φg : hfΦ vb g u0 fG gP = ⟨A, 0, 0⟩) (Φw : hfΦ vb g u0 fG wP = ⟨0, 0, zw⟩)
    (Φa : hfΦ vb g u0 fG aP = ⟨a1, a2, a3⟩)
    (hA : 0 < A) (hs0 : 0 < s) (hs1 : s < 1) (hzv : 0 ≤ zv) (hzw : zw < 0) (hb2 : 0 < b2)
    (hz2 : (1 - s) * zv < z2) (hr1 : 0 < r1) (hd : b1 < r1) (ha3 : 0 < a3) (hxa : s * b1 < a1)
    (hcv : ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 → ¬ ((i = 2 ∧ j = 4) ∨ (i = 3 ∧ j = 2)) →
      crossYZ (h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 b2 i)
        (h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 b2 (i + 1))
        (h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 b2 j) < 0)
    (hl24 : ∀ tt : ℝ, 0 < tt →
      LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, -tt⟩ (h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 b2 2)
        (h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 b2 (2 + 1)) (h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 b2 4))
    (hl32 : ∀ tt : ℝ, 0 < tt →
      LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, -tt⟩ (h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 b2 3)
        (h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 b2 (3 + 1)) (h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 b2 2))
    (hlb : ∀ tt : ℝ, 0 < tt →
      LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, -tt⟩ (h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 b2 2)
        (h5Pts zv zw s b1 b2 z2 a1 a2 a3 r1 b2 (2 + 1)) ⟨b1, b2, 0⟩) :
    IsRupert V := by
  have hs1' : 0 < 1 - s := by linarith
  have h0 : 0 ≤ (1 - s) * zv := mul_nonneg hs1'.le hzv
  have hz2' : 0 < z2 := by linarith
  obtain ⟨tt, htt0, htt1, htt2, htt3⟩ := exists_tt (a2 := a2) hs0 hb2 hz2' hzw hb2 ha3
  have c20 := hcv 2 0 (by decide) (by decide) (by decide)
  have c21 := hcv 2 1 (by decide) (by decide) (by decide)
  obtain ⟨b0, b1', b2', b3, b4⟩ := zmod5_add_one
  simp only [h5Pts, b2', quint_0, quint_1, quint_2, quint_3, quint_4, b3] at c20 c21
  have hmaG := cross_comb_axis (gx := A) hzv hzw c20 c21
  exact Fr.n2_core hV hc hm ha hr hw Φc Φm Φf Φr Φg Φw Φa hA hs0 hs1 hzv hzw hb2 hz2 hr1 ha3 hxa tt htt0
    (fun i j h1 h2 => by
      by_cases hsp : (i = 2 ∧ j = 4) ∨ (i = 3 ∧ j = 2)
      · rcases hsp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hl24 tt htt0
        · exact hl32 tt htt0
      · exact lex_of_cross _ (hcv i j h1 h2 hsp))
    (n2e_f2 hs0 hs1 hzv hzw hb2 ha3 hz2 hd htt2 htt3 (hlb tt htt0))
    (n2g_g hA hs0 hs1 hzv hzw hb2 hb2 ha3 hz2 htt1 hmaG)

end HFrame
end Minimality
