module

public import Minimality.Type24SAT.K24.ParBoxHel

@[expose] public section

/-!
# Type 24 box corner `R₄'`: recipe L

One fixed lexicographic motion at the edge view along `e = x 4 - x 0`, tilted into the hiding cone of the corner `4`.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset
namespace Minimality.T24.Par
open Minimality.Split Minimality.Split.HEL
open Minimality (cross)

theorem recL_pt4 {L c y xi ze b p q r B4 : ℝ} (hL : 0 < L) (hc : 0 < c) (hy : 0 < y) (hr : 0 < r)
    (hB4 : 0 < B4) (hBy : 0 < B4 - y) (hpL : p * L = -(1 + B4)) (hqL : q * L = r / 2 + c) (hrB : r * B4 < c)
    (hxi : 0 < xi) (hze : 0 < ze) (hxz : 0 < 1 - xi - ze) (hrc : r < c)
    (hB6 : 0 < L * (B4 - y) - c * (q * y + 1)) :
    LexTiltCert (univ.image (boxCfg L c y y xi ze b)) !₂[-L, 0, 0] !₂[0, -r, -1] 0
      !₂[-1, p, q] !₂[-1, -(r/2) - c, -1] (boxCfg L c y y xi ze b 4) := by
  apply cone_cert L r _ _ _ _ (boxCfg L c y y xi ze b 6) (boxCfg L c y y xi ze b 3)
    (Finset.mem_image_of_mem _ (mem_univ _)) (Finset.mem_image_of_mem _ (mem_univ _))
  · simp [boxCfg, Minimality.cross]
    left
    positivity
  · simp [boxCfg, Minimality.cross]
    right
    refine ⟨by linear_combination (L*c)*hqL, by positivity⟩
  · simp [boxCfg, Minimality.cross]
    have h1 : -(p * L) + -1 = B4 := by linarith
    left
    rw [h1]
    positivity

theorem recL_pt6 {L c y xi ze b p q r B4 : ℝ} (hL : 0 < L) (hc : 0 < c) (hy : 0 < y) (hr : 0 < r)
    (hB4 : 0 < B4) (hBy : 0 < B4 - y) (hpL : p * L = -(1 + B4)) (hqL : q * L = r / 2 + c) (hrB : r * B4 < c)
    (hxi : 0 < xi) (hze : 0 < ze) (hxz : 0 < 1 - xi - ze) (hrc : r < c)
    (hB6 : 0 < L * (B4 - y) - c * (q * y + 1)) :
    LexTiltCert (univ.image (boxCfg L c y y xi ze b)) !₂[-L, 0, 0] !₂[0, -r, -1] 0
      !₂[-1, p, q] !₂[-1, -(r/2) - c, -1] (boxCfg L c y y xi ze b 6) := by
  apply cone_cert L r _ _ _ _ (boxCfg L c y y xi ze b 2) (boxCfg L c y y xi ze b 4)
    (Finset.mem_image_of_mem _ (mem_univ _)) (Finset.mem_image_of_mem _ (mem_univ _))
  · simp [boxCfg, Minimality.cross]
    left
    positivity
  · simp [boxCfg, Minimality.cross]
    have h1 : -y - p * L + -1 = B4 - y := by linarith
    left
    rw [h1]
    exact mul_pos hL (mul_pos hy hBy)
  · simp [boxCfg, Minimality.cross]
    right
    refine ⟨by linear_combination (-(L*c))*hqL, by
      have := mul_pos hr hB6
      have e : -(r * (-(c * (-(q * y) + -1)) - L * (-y - p * L + -1))) - L * (q * L + (-(r / 2) - c))
          = r * (L * (B4 - y) - c * (q * y + 1)) := by
        linear_combination (-(r*L))*hpL + (-L)*hqL
      rw [e]; exact this⟩

theorem recL_pt3 {L c y xi ze b p q r B4 : ℝ} (hL : 0 < L) (hc : 0 < c) (hy : 0 < y) (hr : 0 < r)
    (hB4 : 0 < B4) (hBy : 0 < B4 - y) (hpL : p * L = -(1 + B4)) (hqL : q * L = r / 2 + c) (hrB : r * B4 < c)
    (hxi : 0 < xi) (hze : 0 < ze) (hxz : 0 < 1 - xi - ze) (hrc : r < c)
    (hB6 : 0 < L * (B4 - y) - c * (q * y + 1)) :
    LexTiltCert (univ.image (boxCfg L c y y xi ze b)) !₂[-L, 0, 0] !₂[0, -r, -1] 0
      !₂[-1, p, q] !₂[-1, -(r/2) - c, -1] (boxCfg L c y y xi ze b 3) := by
  apply cone_cert L r _ _ _ _ (boxCfg L c y y xi ze b 4) (boxCfg L c y y xi ze b 5)
    (Finset.mem_image_of_mem _ (mem_univ _)) (Finset.mem_image_of_mem _ (mem_univ _))
  · simp [boxCfg, Minimality.cross]
    right
    refine ⟨rfl, by positivity⟩
  · simp [boxCfg, Minimality.cross]
    right
    refine ⟨rfl, ?_⟩
    have e : -(r * (L * (-(p * L) + -1))) + L * (q * L + -(r / 2)) = L * (c - r * B4) := by linear_combination (r*L)*hpL + L*hqL
    rw [e]
    exact mul_pos hL (by linarith)
  · simp [boxCfg, Minimality.cross]
    have h1 : q * L + -(r / 2) = c := by linarith
    left
    rw [h1]
    positivity

theorem recL_pt5 {L c y xi ze b p q r B4 : ℝ} (hL : 0 < L) (hc : 0 < c) (hy : 0 < y) (hr : 0 < r)
    (hB4 : 0 < B4) (hBy : 0 < B4 - y) (hpL : p * L = -(1 + B4)) (hqL : q * L = r / 2 + c) (hrB : r * B4 < c)
    (hxi : 0 < xi) (hze : 0 < ze) (hxz : 0 < 1 - xi - ze) (hrc : r < c)
    (hB6 : 0 < L * (B4 - y) - c * (q * y + 1)) :
    LexTiltCert (univ.image (boxCfg L c y y xi ze b)) !₂[-L, 0, 0] !₂[0, -r, -1] 0
      !₂[-1, p, q] !₂[-1, -(r/2) - c, -1] (boxCfg L c y y xi ze b 5) := by
  apply cone_cert L r _ _ _ _ (boxCfg L c y y xi ze b 3) (boxCfg L c y y xi ze b 2)
    (Finset.mem_image_of_mem _ (mem_univ _)) (Finset.mem_image_of_mem _ (mem_univ _))
  · simp [boxCfg, Minimality.cross]
    right
    refine ⟨rfl, by positivity⟩
  · simp [boxCfg, Minimality.cross]
    left
    positivity
  · simp [boxCfg, Minimality.cross]
    right
    refine ⟨rfl, by nlinarith [mul_pos hL hr]⟩

theorem recL_pt2 {L c y xi ze b p q r B4 : ℝ} (hL : 0 < L) (hc : 0 < c) (hy : 0 < y) (hr : 0 < r)
    (hB4 : 0 < B4) (hBy : 0 < B4 - y) (hpL : p * L = -(1 + B4)) (hqL : q * L = r / 2 + c) (hrB : r * B4 < c)
    (hxi : 0 < xi) (hze : 0 < ze) (hxz : 0 < 1 - xi - ze) (hrc : r < c)
    (hB6 : 0 < L * (B4 - y) - c * (q * y + 1)) :
    LexTiltCert (univ.image (boxCfg L c y y xi ze b)) !₂[-L, 0, 0] !₂[0, -r, -1] 0
      !₂[-1, p, q] !₂[-1, -(r/2) - c, -1] (boxCfg L c y y xi ze b 2) := by
  apply cone_cert L r _ _ _ _ (boxCfg L c y y xi ze b 5) (boxCfg L c y y xi ze b 6)
    (Finset.mem_image_of_mem _ (mem_univ _)) (Finset.mem_image_of_mem _ (mem_univ _))
  · simp [boxCfg, Minimality.cross]
    left
    positivity
  · simp [boxCfg, Minimality.cross]
    left
    positivity
  · simp [boxCfg, Minimality.cross]
    left
    nlinarith [mul_pos hL hy, mul_pos (mul_pos hL hy) hy]

theorem recL_pt1t {L c y xi ze b p q r B4 : ℝ} (hL : 0 < L) (hc : 0 < c) (hy : 0 < y) (hr : 0 < r)
    (hB4 : 0 < B4) (hpL : p * L = -(1 + B4)) (hqL : q * L = r / 2 + c)
    (hxi : 0 < xi) (hze : 0 < ze) (hlo : y * xi + y * ze < b) (hb : b < y) :
    LexTiltCert (univ.image (boxCfg L c y y xi ze b)) !₂[-L, 0, 0] !₂[0, -r, -1] 0
      !₂[-1, p, q] !₂[-1, -(r/2) - c, -1] (boxCfg L c y y xi ze b 1) := by
  apply tri_cert L r _ _ _ _ (boxCfg L c y y xi ze b 0) (boxCfg L c y y xi ze b 2) (boxCfg L c y y xi ze b 6)
    (Finset.mem_image_of_mem _ (mem_univ _)) (Finset.mem_image_of_mem _ (mem_univ _)) (Finset.mem_image_of_mem _ (mem_univ _))
  · simp [boxCfg, Minimality.cross]
    left
    positivity
  · simp [boxCfg, Minimality.cross]
    left
    nlinarith [mul_pos hy hxi, mul_pos hL hc, mul_pos (mul_pos hL hc) (mul_pos hy hxi), mul_pos (mul_pos hL hc) (sub_pos.2 hlo)]
  · simp [boxCfg, Minimality.cross]
    left
    have : 0 < y - b := by linarith
    nlinarith [mul_pos (mul_pos hL hc) this]
  · simp [boxCfg, Minimality.cross]
    left
    positivity

theorem recL_pt1b {L c y xi ze p q r B4 : ℝ} (hL : 0 < L) (hc : 0 < c) (hy : 0 < y) (hr : 0 < r)
    (hB4 : 0 < B4) (hpL : p * L = -(1 + B4)) (hqL : q * L = r / 2 + c)
    (hxi : 0 < xi) (hze : 0 < ze) (hxz : 0 < 1 - xi - ze) :
    LexTiltCert (univ.image (boxCfg L c y y xi ze y)) !₂[-L, 0, 0] !₂[0, -r, -1] 0
      !₂[-1, p, q] !₂[-1, -(r/2) - c, -1] (boxCfg L c y y xi ze y 1) := by
  have hxi1 : xi < 1 := by linarith
  have hze1 : ze < 1 := by linarith
  have hP : 0 < (1 - xi) * (r / 2 + c) - ze * c := by
    nlinarith [mul_pos hxz hc, mul_pos hr (sub_pos.2 hxi1)]
  have hX : q * (xi * L) + ze * c + (-(r / 2) - c) = -((1 - xi) * (r / 2 + c) - ze * c) := by
    linear_combination xi * hqL
  apply cone_cert L r _ _ _ _ (boxCfg L c y y xi ze y 2) (boxCfg L c y y xi ze y 6)
    (Finset.mem_image_of_mem _ (mem_univ _)) (Finset.mem_image_of_mem _ (mem_univ _))
  · simp [boxCfg, Minimality.cross]
    right
    refine ⟨rfl, ?_⟩
    nlinarith [mul_pos (mul_pos (mul_pos hr hL) hc) hxz]
  · simp [boxCfg, Minimality.cross]
    left
    rw [hX]
    nlinarith [mul_pos (mul_pos hL (mul_pos hze hc)) hP]
  · simp [boxCfg, Minimality.cross]
    left
    rw [hX]
    nlinarith [mul_pos (mul_pos hL (mul_pos hc (sub_pos.2 hze1))) hP]


/-- Recipe L: `y2 = y6`, `b ≤ y2`. -/
theorem rec_L {L c y2 y6 xi ze b : ℝ} (hL : 0 < L) (hc : 0 < c) (hy6 : 0 < y6) (hy : y2 = y6)
    (hxi : 0 < xi) (hze : 0 < ze) (hlo : y6 * xi + y2 * ze < b) (hhi : b < y2 * (1 - xi) + y6 * (1 - ze))
    (hb : b ≤ y2) : IsRupert (univ.image (boxCfg L c y2 y6 xi ze b)) := by
  rw [← hy] at hy6 hlo hhi ⊢
  set y := y2 with hydef
  obtain ⟨B4, hB4d⟩ : ∃ B4 : ℝ, B4 = y + c * (1 + 2 * c * y / L) / L + 1 := ⟨_, rfl⟩
  have hBy : 0 < B4 - y := by
    rw [hB4d]
    have : 0 < c * (1 + 2 * c * y / L) / L := by positivity
    linarith
  have hB1 : 1 < B4 := by
    rw [hB4d]
    have : 0 < c * (1 + 2 * c * y / L) / L := by positivity
    linarith
  have hB4 : 0 < B4 := by linarith
  obtain ⟨r, hrd⟩ : ∃ r : ℝ, r = c / (2 * B4) := ⟨_, rfl⟩
  have hr : 0 < r := by rw [hrd]; positivity
  have hrB : r * B4 < c := by
    rw [hrd]; field_simp; linarith
  have hrc : r < c := by nlinarith
  obtain ⟨p, hpd⟩ : ∃ p : ℝ, p = -(1 + B4) / L := ⟨_, rfl⟩
  obtain ⟨q, hqd⟩ : ∃ q : ℝ, q = (r / 2 + c) / L := ⟨_, rfl⟩
  have hpL : p * L = -(1 + B4) := by rw [hpd]; field_simp
  have hqL : q * L = r / 2 + c := by rw [hqd]; field_simp
  have hB6 : 0 < L * (B4 - y) - c * (q * y + 1) := by
    have e : L * (B4 - y) - c * (q * y + 1) = L + c * y * (c - r / 2) / L := by
      rw [hqd, hB4d]; field_simp; ring
    rw [e]
    have : 0 < c * y * (c - r / 2) / L := by
      apply div_pos _ hL
      exact mul_pos (mul_pos hc hy6) (by linarith)
    linarith
  have hxz : 0 < 1 - xi - ze := by
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_nonneg hy6.le (neg_nonneg.2 hcon)]
  refine box_hel (r := r) hL hc hy6 hr !₂[-1, p, q] !₂[-1, -(r/2) - c, -1] ?_
  intro i hi
  fin_cases i
  · exact absurd rfl hi
  · rcases lt_or_eq_of_le hb with hlt | heq
    · exact recL_pt1t hL hc hy6 hr hB4 hpL hqL hxi hze hlo hlt
    · subst heq
      exact recL_pt1b hL hc hy6 hr hB4 hpL hqL hxi hze hxz
  · exact recL_pt2 hL hc hy6 hr hB4 hBy hpL hqL hrB hxi hze hxz hrc hB6
  · exact recL_pt3 hL hc hy6 hr hB4 hBy hpL hqL hrB hxi hze hxz hrc hB6
  · exact recL_pt4 hL hc hy6 hr hB4 hBy hpL hqL hrB hxi hze hxz hrc hB6
  · exact recL_pt5 hL hc hy6 hr hB4 hBy hpL hqL hrB hxi hze hxz hrc hB6
  · exact recL_pt6 hL hc hy6 hr hB4 hBy hpL hqL hrB hxi hze hxz hrc hB6

end Minimality.T24.Par
