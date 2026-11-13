module

public import Minimality.Type24SAT.K24.ParBoxHel

@[expose] public section

/-!
# Type 24 box corner `R₄'`: recipe III

One fixed lexicographic motion at the edge view along `e = x 4 - x 0`, tilted into the hiding cone of the corner `4`.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset
namespace Minimality.T24.Par
open Minimality.Split Minimality.Split.HEL
open Minimality (cross)

theorem iii_mem (L c y2 y6 xi ze b : ℝ) (j : Fin 7) :
    boxCfg L c y2 y6 xi ze b j ∈ univ.image (boxCfg L c y2 y6 xi ze b) :=
  Finset.mem_image.2 ⟨j, mem_univ _, rfl⟩

/-- row at 4: cone (6,3). -/
theorem iii_row4 {L c y2 y6 xi ze b r c0y c0z c1y c1z : ℝ} (hL : 0 < L) (hc : 0 < c) (hy6 : 0 < y6)
    (hm : y6 < c1y) (he : 0 < -c1z) :
    LexTiltCert (univ.image (boxCfg L c y2 y6 xi ze b)) !₂[-L, 0, 0] !₂[0, -r, -1] 0
      !₂[-1, -(c1y - c0y)/L, -(c1z-c0z)/L] !₂[0, -c0z, c0y] (boxCfg L c y2 y6 xi ze b 4) := by
  refine cone_cert L r _ _ _ _ (boxCfg L c y2 y6 xi ze b 6) (boxCfg L c y2 y6 xi ze b 3)
    (iii_mem L c y2 y6 xi ze b 6) (iii_mem L c y2 y6 xi ze b 3) ?_ ?_ ?_
  · left; simp [boxCfg]; positivity
  · left; simp [boxCfg]; field_simp; nlinarith [mul_pos (mul_pos hL hc) he]
  · left; simp [boxCfg]; field_simp; nlinarith [mul_pos (mul_pos hL hy6) (sub_pos.2 hm)]

/-- row at 3: cone (4,5). -/
theorem iii_row3 {L c y2 y6 xi ze b r c0y c0z c1y c1z : ℝ} (hL : 0 < L) (hc : 0 < c) (hr : 0 < r)
    (he : 0 < -c1z) (h3 : r * c1y < c - c1z) :
    LexTiltCert (univ.image (boxCfg L c y2 y6 xi ze b)) !₂[-L, 0, 0] !₂[0, -r, -1] 0
      !₂[-1, -(c1y - c0y)/L, -(c1z-c0z)/L] !₂[0, -c0z, c0y] (boxCfg L c y2 y6 xi ze b 3) := by
  refine cone_cert L r _ _ _ _ (boxCfg L c y2 y6 xi ze b 4) (boxCfg L c y2 y6 xi ze b 5)
    (iii_mem L c y2 y6 xi ze b 4) (iii_mem L c y2 y6 xi ze b 5) ?_ ?_ ?_
  · right; refine ⟨by simp [boxCfg], ?_⟩; simp [boxCfg]; positivity
  · right; refine ⟨by simp [boxCfg], ?_⟩; simp [boxCfg]; field_simp
    nlinarith [mul_pos hL (sub_pos.2 h3)]
  · left; simp [boxCfg]; field_simp; nlinarith [mul_pos (mul_pos hL hc) (by linarith : 0 < c - c1z)]

/-- row at 5: cone (3,2). -/
theorem iii_row5 {L c y2 y6 xi ze b r c0y c0z c1y c1z : ℝ} (hL : 0 < L) (hc : 0 < c) (hy6 : 0 < y6)
    (hy : y6 ≤ y2) (hc0y : c0y < 0) (h5 : 0 < (c - c0z) - r * c0y) :
    LexTiltCert (univ.image (boxCfg L c y2 y6 xi ze b)) !₂[-L, 0, 0] !₂[0, -r, -1] 0
      !₂[-1, -(c1y - c0y)/L, -(c1z-c0z)/L] !₂[0, -c0z, c0y] (boxCfg L c y2 y6 xi ze b 5) := by
  have hy2 : 0 < y2 := by linarith
  refine cone_cert L r _ _ _ _ (boxCfg L c y2 y6 xi ze b 3) (boxCfg L c y2 y6 xi ze b 2)
    (iii_mem L c y2 y6 xi ze b 3) (iii_mem L c y2 y6 xi ze b 2) ?_ ?_ ?_
  · right; refine ⟨by simp [boxCfg], ?_⟩; simp [boxCfg]; positivity
  · left; simp [boxCfg]; field_simp; nlinarith [mul_pos (mul_pos hL hy2) (neg_pos.2 hc0y)]
  · right; refine ⟨by simp [boxCfg], ?_⟩; simp [boxCfg]; field_simp
    nlinarith [mul_pos hL h5]

/-- row at 2: cone (5,1). -/
theorem iii_row2 {L c y2 y6 xi ze b r c0y c0z c1y c1z : ℝ} (hL : 0 < L) (hc : 0 < c) (hy6 : 0 < y6)
    (hy : y6 ≤ y2) (hze : ze < 1) (hb : y2 ≤ b) (hc0y : c0y < 0) (hc0z : c < c0z) :
    LexTiltCert (univ.image (boxCfg L c y2 y6 xi ze b)) !₂[-L, 0, 0] !₂[0, -r, -1] 0
      !₂[-1, -(c1y - c0y)/L, -(c1z-c0z)/L] !₂[0, -c0z, c0y] (boxCfg L c y2 y6 xi ze b 2) := by
  have hy2 : 0 < y2 := by linarith
  have hcd : 0 < c - ze * c := by nlinarith
  refine cone_cert L r _ _ _ _ (boxCfg L c y2 y6 xi ze b 5) (boxCfg L c y2 y6 xi ze b 1)
    (iii_mem L c y2 y6 xi ze b 5) (iii_mem L c y2 y6 xi ze b 1) ?_ ?_ ?_
  · left; simp [boxCfg]; nlinarith [mul_pos (mul_pos hL hy2) hcd]
  · left; simp [boxCfg]; field_simp
    nlinarith [mul_nonneg hL.le (mul_nonneg (sub_nonneg.2 hb) (by linarith : (0:ℝ) ≤ y2 - c0y)),
      mul_pos hL (mul_pos (sub_pos.2 hc0z) hcd)]
  · left; simp [boxCfg]; field_simp; nlinarith [mul_pos (mul_pos hL hy2) (by linarith : (0:ℝ) < y2 - c0y)]

/-- row at 6: cone (1,4). -/
theorem iii_row6 {L c y2 y6 xi ze b r c0y c0z c1y c1z : ℝ} (hL : 0 < L) (hc : 0 < c) (hy6 : 0 < y6)
    (hze : 0 < ze) (hm : y6 < c1y) (h6 : 0 < (c1y - y6) * (b - y6) + ze * c * c1z) :
    LexTiltCert (univ.image (boxCfg L c y2 y6 xi ze b)) !₂[-L, 0, 0] !₂[0, -r, -1] 0
      !₂[-1, -(c1y - c0y)/L, -(c1z-c0z)/L] !₂[0, -c0z, c0y] (boxCfg L c y2 y6 xi ze b 6) := by
  refine cone_cert L r _ _ _ _ (boxCfg L c y2 y6 xi ze b 1) (boxCfg L c y2 y6 xi ze b 4)
    (iii_mem L c y2 y6 xi ze b 1) (iii_mem L c y2 y6 xi ze b 4) ?_ ?_ ?_
  · left; simp [boxCfg]; nlinarith [mul_pos (mul_pos hL hy6) (mul_pos hze hc)]
  · left; simp [boxCfg]; field_simp; nlinarith [mul_pos (mul_pos hL hy6) (sub_pos.2 hm)]
  · left; simp [boxCfg]; field_simp; nlinarith [mul_pos hL h6]

/-- row at 1: cone (2,6). -/
theorem iii_row1 {L c y2 y6 xi ze b r c0y c0z c1y c1z : ℝ} (hL : 0 < L) (hc : 0 < c) (hy6 : 0 < y6)
    (hze : 0 < ze) (hze1 : ze < 1) (hy : y6 ≤ y2) (hb : y2 ≤ b) (hby : y6 < b)
    (hE1 : 0 < (b - y6) * ((1 - xi) * c0y + xi * c1y - b) + ze * c * ((1 - xi) * c0z + xi * c1z - ze * c))
    (hE2 : 0 < (b - y2) * (b - ((1 - xi) * c0y + xi * c1y)) + (c - ze * c) * ((1 - xi) * c0z + xi * c1z - ze * c)) :
    LexTiltCert (univ.image (boxCfg L c y2 y6 xi ze b)) !₂[-L, 0, 0] !₂[0, -r, -1] 0
      !₂[-1, -(c1y - c0y)/L, -(c1z-c0z)/L] !₂[0, -c0z, c0y] (boxCfg L c y2 y6 xi ze b 1) := by
  have hcd : 0 < c - ze * c := by nlinarith
  refine cone_cert L r _ _ _ _ (boxCfg L c y2 y6 xi ze b 2) (boxCfg L c y2 y6 xi ze b 6)
    (iii_mem L c y2 y6 xi ze b 2) (iii_mem L c y2 y6 xi ze b 6) ?_ ?_ ?_
  · left; simp [boxCfg]
    nlinarith [mul_nonneg hL.le (mul_nonneg (sub_nonneg.2 hb) (mul_pos hze hc).le), mul_nonneg hL.le (mul_nonneg hcd.le (sub_pos.2 hby).le),
      mul_pos hL (mul_pos hcd (sub_pos.2 hby)), mul_nonneg (mul_nonneg hL.le (sub_nonneg.2 (le_trans hy hb))) (mul_pos hze hc).le]
  · left; simp [boxCfg]; field_simp; nlinarith [mul_pos hL hE1]
  · left; simp [boxCfg]; field_simp; nlinarith [mul_pos hL hE2]

set_option maxHeartbeats 1000000 in
/-- Recipe III: `y6 ≤ y2 ≤ b`, `b (b - y6) ≤ d (c - d)` with `d = ze c`; also `y6 < b`
(added hypothesis: at `b = y6` the rows at 4 and 3 vanish identically). -/
theorem rec_III {L c y2 y6 xi ze b : ℝ} (hL : 0 < L) (hc : 0 < c) (hy6 : 0 < y6) (hy : y6 ≤ y2)
    (hxi : 0 < xi) (hze : 0 < ze) (hlo : y6 * xi + y2 * ze < b) (hhi : b < y2 * (1 - xi) + y6 * (1 - ze))
    (hb : y2 ≤ b) (hby : y6 < b) (hiii : b * (b - y6) ≤ ze * c * (c - ze * c)) :
    IsRupert (univ.image (boxCfg L c y2 y6 xi ze b)) := by
  have hsum : xi + ze < 1 := by
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ y2 + y6) (sub_nonneg.2 hcon)]
  have hxi1 : xi < 1 := by linarith
  have hze1 : ze < 1 := by linarith
  have ht1 : 0 < 1 - xi := by linarith
  have hd : 0 < ze * c := mul_pos hze hc
  have hcd : 0 < c - ze * c := by nlinarith
  have hbd : 0 < b - y6 := sub_pos.2 hby
  -- the slopes
  obtain ⟨lo, hlo_def⟩ : ∃ lo, lo = (b - y6) / (ze * c) := ⟨_, rfl⟩
  obtain ⟨hi, hhi_def⟩ : ∃ hi, hi = c / y6 := ⟨_, rfl⟩
  have hlo0 : 0 < lo := by rw [hlo_def]; positivity
  have hlo_d : lo * (ze * c) = b - y6 := by rw [hlo_def]; field_simp
  have hhi_y : hi * y6 = c := by rw [hhi_def]; field_simp
  have hlohi : lo < hi := by
    by_contra hcon
    push_neg at hcon
    have h1 : hi * y6 * (ze * c) ≤ lo * (ze * c) * y6 := by
      have := mul_le_mul_of_nonneg_right hcon (mul_pos hd hy6).le
      nlinarith
    rw [hhi_y, hlo_d] at h1
    nlinarith [mul_nonneg hbd.le (sub_nonneg.2 (le_trans hy hb)), mul_pos hd hd]
  obtain ⟨k, hk_def⟩ : ∃ k, k = (2 * lo + hi) / 3 := ⟨_, rfl⟩
  obtain ⟨r, hr_def⟩ : ∃ r, r = (lo + 2 * hi) / 3 := ⟨_, rfl⟩
  have hlok : lo < k := by rw [hk_def]; linarith
  have hkr : k < r := by rw [hk_def, hr_def]; linarith
  have hrhi : r < hi := by rw [hr_def]; linarith
  have hr0 : 0 < r := by linarith
  have hk0 : 0 < k := by linarith
  have hdk : b - y6 < ze * c * k := by nlinarith
  have hry : r * y6 < c := by nlinarith
  obtain ⟨m, hm_def⟩ : ∃ m, m = (c / r - y6) / 2 := ⟨_, rfl⟩
  have hrc : r * (c / r) = c := by field_simp
  have hrm : r * m * 2 = c - r * y6 := by rw [hm_def]; nlinarith
  have hm0 : 0 < m := by nlinarith
  obtain ⟨eps, he_def⟩ : ∃ eps, eps = (b - y6) * m / (2 * (ze * c)) := ⟨_, rfl⟩
  have hde : 2 * (ze * c) * eps = (b - y6) * m := by rw [he_def]; field_simp
  have he0 : 0 < eps := by rw [he_def]; positivity
  -- the far centre
  obtain ⟨g1, hg1⟩ : ∃ g1, g1 = (b - y6) * (xi * (y6 + m) - b) + ze * c * ((1 - xi) * c + xi * (-eps) - ze * c) := ⟨_, rfl⟩
  obtain ⟨g2, hg2⟩ : ∃ g2, g2 = (b - y2) * (b - xi * (y6 + m)) + (c - ze * c) * ((1 - xi) * c + xi * (-eps) - ze * c) := ⟨_, rfl⟩
  obtain ⟨h1, hh1⟩ : ∃ h1, h1 = (1 - xi) * (ze * c * k - (b - y6)) := ⟨_, rfl⟩
  obtain ⟨h2, hh2⟩ : ∃ h2, h2 = (1 - xi) * ((b - y2) + (c - ze * c) * k) := ⟨_, rfl⟩
  have hh1p : 0 < h1 := by rw [hh1]; exact mul_pos ht1 (by linarith)
  have hh2p : 0 < h2 := by
    rw [hh2]; exact mul_pos ht1 (by have := mul_pos hcd hk0; linarith)
  obtain ⟨M, hM_def⟩ : ∃ M, M = max 1 (max (-2 * g1 / h1) (-2 * g2 / h2)) := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by rw [hM_def]; exact le_max_left _ _
  have hM2 : -2 * g1 / h1 ≤ M := by rw [hM_def]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hM3 : -2 * g2 / h2 ≤ M := by rw [hM_def]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hM0 : 0 < M := by linarith
  have hMg1 : -2 * g1 ≤ M * h1 := (div_le_iff₀ hh1p).1 hM2
  have hMg2 : -2 * g2 ≤ M * h2 := (div_le_iff₀ hh2p).1 hM3
  have hMh1 : 0 < M * h1 := mul_pos hM0 hh1p
  have hMh2 : 0 < M * h2 := mul_pos hM0 hh2p
  have hbox := box_hel (L := L) (c := c) (y2 := y2) (y6 := y6) (xi := xi) (ze := ze) (b := b) (r := r)
    hL hc hy6 hr0 !₂[-1, -((y6 + m) - (-M))/L, -((-eps)-(c + k * M))/L] !₂[0, -(c + k * M), -M]
  refine hbox ?_
  intro i hi0
  fin_cases i
  · exact absurd rfl hi0
  · exact iii_row1 (c0y := -M) (c0z := c + k * M) (c1y := y6 + m) (c1z := -eps) hL hc hy6 hze hze1 hy hb hby
      (by rw [show (b - y6) * ((1 - xi) * -M + xi * (y6 + m) - b) + ze * c * ((1 - xi) * (c + k * M) + xi * -eps - ze * c)
            = M * h1 + g1 by rw [hh1, hg1]; ring]; linarith)
      (by rw [show (b - y2) * (b - ((1 - xi) * -M + xi * (y6 + m))) + (c - ze * c) * ((1 - xi) * (c + k * M) + xi * -eps - ze * c)
            = M * h2 + g2 by rw [hh2, hg2]; ring]; linarith)
  · exact iii_row2 (c0y := -M) (c0z := c + k * M) (c1y := y6 + m) (c1z := -eps) hL hc hy6 hy hze1 hb
      (by linarith) (by nlinarith [mul_pos hk0 hM0])
  · exact iii_row3 (c0y := -M) (c0z := c + k * M) (c1y := y6 + m) (c1z := -eps) hL hc hr0
      (by linarith) (by nlinarith)
  · exact iii_row4 (c0y := -M) (c0z := c + k * M) (c1y := y6 + m) (c1z := -eps) hL hc hy6
      (by linarith) (by linarith)
  · exact iii_row5 (c0y := -M) (c0z := c + k * M) (c1y := y6 + m) (c1z := -eps) hL hc hy6 hy
      (by linarith) (by nlinarith [mul_pos (sub_pos.2 hkr) hM0])
  · exact iii_row6 (c0y := -M) (c0z := c + k * M) (c1y := y6 + m) (c1z := -eps) hL hc hy6 hze
      (by linarith) (by nlinarith [mul_pos hm0 hbd])

end Minimality.T24.Par
