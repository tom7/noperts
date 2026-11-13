module

public import Minimality.Type24SAT.K24.ParBoxHel

@[expose] public section

/-!
# Type 24 box corner `R₄'`: recipe IV

One fixed lexicographic motion at the edge view along `e = x 4 - x 0`, tilted into the hiding cone of the corner `4`.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset
namespace Minimality.T24.Par
open Minimality.Split Minimality.Split.HEL
open Minimality (cross)



theorem iv_c4 {L c y2 y6 xi ze b r c0y c0z p q : ℝ} (hL : 0 < L) (hc : 0 < c) (hy6 : 0 < y6) (hy2 : 0 < y2)
    (hxi : 0 < xi) (hb0 : 0 < b) (hd : 0 < ze * c) (hcd : 0 < c - ze * c) (hr : 0 < r) (hby : y2 ≤ b)
    (h1 : 0 < c0z + q * L) (h2 : c0y + p * L < 0) :
    LexTiltCert (univ.image (boxCfg L c y2 y6 xi ze b)) !₂[-L, 0, 0] !₂[0, -r, -1] 0
      !₂[1, p, q] !₂[0, c0z, -c0y] ((boxCfg L c y2 y6 xi ze b) 4) := by
  refine cone_cert L r _ _ _ _ ((boxCfg L c y2 y6 xi ze b) 6) ((boxCfg L c y2 y6 xi ze b) 3) (by simp) (by simp) ?_ ?_ ?_
  · left; simp [boxCfg, Minimality.cross]; nlinarith [mul_pos (mul_pos hL hc) hy6]
  · left; simp [boxCfg, Minimality.cross]; nlinarith [mul_pos (mul_pos hL hc) h1]
  · left; simp [boxCfg, Minimality.cross]; nlinarith [mul_pos (mul_pos hL hy6) (neg_pos.2 h2)]

theorem iv_c3 {L c y2 y6 xi ze b r c0y c0z p q : ℝ} (hL : 0 < L) (hc : 0 < c) (hy6 : 0 < y6) (hy2 : 0 < y2)
    (hxi : 0 < xi) (hb0 : 0 < b) (hd : 0 < ze * c) (hcd : 0 < c - ze * c) (hr : 0 < r) (hby : y2 ≤ b)
    (h1 : c < c0z + q * L) (h2 : 0 < c0z + q * L - c + r * (c0y + p * L)) :
    LexTiltCert (univ.image (boxCfg L c y2 y6 xi ze b)) !₂[-L, 0, 0] !₂[0, -r, -1] 0
      !₂[1, p, q] !₂[0, c0z, -c0y] ((boxCfg L c y2 y6 xi ze b) 3) := by
  refine cone_cert L r _ _ _ _ ((boxCfg L c y2 y6 xi ze b) 4) ((boxCfg L c y2 y6 xi ze b) 5) (by simp) (by simp) ?_ ?_ ?_
  · right; refine ⟨by simp [boxCfg, Minimality.cross] <;> ring, ?_⟩; simp [boxCfg, Minimality.cross]; nlinarith [mul_pos hr (mul_pos hL hc)]
  · right; refine ⟨by simp [boxCfg, Minimality.cross] <;> ring, ?_⟩; simp [boxCfg, Minimality.cross]; nlinarith [mul_pos hL h2]
  · left; simp [boxCfg, Minimality.cross]; nlinarith [mul_pos (mul_pos hL hc) (sub_pos.2 h1)]

theorem iv_c5 {L c y2 y6 xi ze b r c0y c0z p q : ℝ} (hL : 0 < L) (hc : 0 < c) (hy6 : 0 < y6) (hy2 : 0 < y2)
    (hxi : 0 < xi) (hb0 : 0 < b) (hd : 0 < ze * c) (hcd : 0 < c - ze * c) (hr : 0 < r) (hby : y2 ≤ b)
    (h1 : 0 < c0y) (h2 : 0 < r * c0y + c0z - c) :
    LexTiltCert (univ.image (boxCfg L c y2 y6 xi ze b)) !₂[-L, 0, 0] !₂[0, -r, -1] 0
      !₂[1, p, q] !₂[0, c0z, -c0y] ((boxCfg L c y2 y6 xi ze b) 5) := by
  refine cone_cert L r _ _ _ _ ((boxCfg L c y2 y6 xi ze b) 3) ((boxCfg L c y2 y6 xi ze b) 2) (by simp) (by simp) ?_ ?_ ?_
  · right; refine ⟨by simp [boxCfg, Minimality.cross] <;> ring, ?_⟩; simp [boxCfg, Minimality.cross]; nlinarith [mul_pos hy2 hL]
  · left; simp [boxCfg, Minimality.cross]; nlinarith [mul_pos (mul_pos hL hy2) h1]
  · right; refine ⟨by simp [boxCfg, Minimality.cross] <;> ring, ?_⟩; simp [boxCfg, Minimality.cross]; nlinarith [mul_pos hL h2]

theorem iv_c6 {L c y2 y6 xi ze b r c0y c0z p q : ℝ} (hL : 0 < L) (hc : 0 < c) (hy6 : 0 < y6) (hy2 : 0 < y2)
    (hxi : 0 < xi) (hb0 : 0 < b) (hd : 0 < ze * c) (hcd : 0 < c - ze * c) (hr : 0 < r) (hby : y2 ≤ b)
    (h1 : c0y + p * L < y6) (h2 : (b - y6) * (c0y + p * L) + ze * c * (c0z + q * L) < (b - y6) * y6) :
    LexTiltCert (univ.image (boxCfg L c y2 y6 xi ze b)) !₂[-L, 0, 0] !₂[0, -r, -1] 0
      !₂[1, p, q] !₂[0, c0z, -c0y] ((boxCfg L c y2 y6 xi ze b) 6) := by
  refine cone_cert L r _ _ _ _ ((boxCfg L c y2 y6 xi ze b) 1) ((boxCfg L c y2 y6 xi ze b) 4) (by simp) (by simp) ?_ ?_ ?_
  · left; simp [boxCfg, Minimality.cross]; nlinarith [mul_pos (mul_pos hL hy6) hd]
  · left; simp [boxCfg, Minimality.cross]; nlinarith [mul_pos (mul_pos hL hy6) (sub_pos.2 h1)]
  · left; simp [boxCfg, Minimality.cross]; nlinarith [mul_pos hL (sub_pos.2 h2)]

theorem iv_c2 {L c y2 y6 xi ze b r c0y c0z p q : ℝ} (hL : 0 < L) (hc : 0 < c) (hy6 : 0 < y6) (hy2 : 0 < y2)
    (hxi : 0 < xi) (hb0 : 0 < b) (hd : 0 < ze * c) (hcd : 0 < c - ze * c) (hr : 0 < r) (hby : y2 ≤ b)
    (h1 : y2 < c0y) (h2 : (b - y2) * (y2 - c0y) + (c - ze * c) * (c0z - c) < 0) :
    LexTiltCert (univ.image (boxCfg L c y2 y6 xi ze b)) !₂[-L, 0, 0] !₂[0, -r, -1] 0
      !₂[1, p, q] !₂[0, c0z, -c0y] ((boxCfg L c y2 y6 xi ze b) 2) := by
  refine cone_cert L r _ _ _ _ ((boxCfg L c y2 y6 xi ze b) 5) ((boxCfg L c y2 y6 xi ze b) 1) (by simp) (by simp) ?_ ?_ ?_
  · left; simp [boxCfg, Minimality.cross]; nlinarith [mul_pos (mul_pos hL hcd) hy2]
  · left; simp [boxCfg, Minimality.cross]; nlinarith [mul_pos hL (neg_pos.2 h2)]
  · left; simp [boxCfg, Minimality.cross]; nlinarith [mul_pos (mul_pos hL hy2) (sub_pos.2 h1)]

theorem iv_c1 {L c y2 y6 xi ze b r c0y c0z p q : ℝ} (hL : 0 < L) (hc : 0 < c) (hy6 : 0 < y6) (hy2 : 0 < y2)
    (hxi : 0 < xi) (hb0 : 0 < b) (hd : 0 < ze * c) (hcd : 0 < c - ze * c) (hr : 0 < r) (hby : y2 ≤ b)
    (hy : 0 < b * (c - ze * c) + ze * c * (b - y2)) (h1 : b * (c0y + xi * (p * L)) + ze * c * (c0z + xi * (q * L)) < b * b + ze * c * (ze * c)) (h2 : (y2 - b) * (c0y + xi * (p * L)) + (c - ze * c) * (c0z + xi * (q * L)) < (y2 - b) * b + (c - ze * c) * (ze * c)) :
    LexTiltCert (univ.image (boxCfg L c y2 y6 xi ze b)) !₂[-L, 0, 0] !₂[0, -r, -1] 0
      !₂[1, p, q] !₂[0, c0z, -c0y] ((boxCfg L c y2 y6 xi ze b) 1) := by
  refine cone_cert L r _ _ _ _ ((boxCfg L c y2 y6 xi ze b) 2) ((boxCfg L c y2 y6 xi ze b) 0) (by simp) (by simp) ?_ ?_ ?_
  · left; simp [boxCfg, Minimality.cross]; nlinarith [mul_pos hL hy]
  · left; simp [boxCfg, Minimality.cross]; nlinarith [mul_pos hL (sub_pos.2 h1)]
  · left; simp [boxCfg, Minimality.cross]; nlinarith [mul_pos hL (sub_pos.2 h2)]

set_option maxHeartbeats 1000000 in
/-- Recipe IV: `y6 ≤ y2 ≤ b`, `d (c - d) < b (b - y6)` with `d = ze c`. -/
theorem rec_IV {L c y2 y6 xi ze b : ℝ} (hL : 0 < L) (hc : 0 < c) (hy6 : 0 < y6) (hy : y6 ≤ y2)
    (hxi : 0 < xi) (hze : 0 < ze) (hlo : y6 * xi + y2 * ze < b) (hhi : b < y2 * (1 - xi) + y6 * (1 - ze))
    (hb : y2 ≤ b) (hiv : ze * c * (c - ze * c) < b * (b - y6)) :
    IsRupert (univ.image (boxCfg L c y2 y6 xi ze b)) := by
  have hy2 : 0 < y2 := lt_of_lt_of_le hy6 hy
  have hxs : xi + ze < 1 := by
    by_contra h
    push_neg at h
    nlinarith [mul_nonneg (add_pos hy2 hy6).le (sub_nonneg.2 h)]
  have hb0 : 0 < b := by nlinarith [mul_pos hy6 hxi, mul_pos hy2 hze]
  have hd : 0 < ze * c := mul_pos hze hc
  have hcd : 0 < c - ze * c := by nlinarith
  have hx1 : 0 < 1 - xi := by linarith
  set d := ze * c with hd_def
  have hby6 : 0 < b - y6 := by
    by_contra h
    push_neg at h
    nlinarith [mul_pos hd hcd, mul_nonneg hb0.le (neg_nonneg.2 h)]
  obtain ⟨u, hu⟩ : ∃ u, u * b = c - d := ⟨(c - d) / b, by field_simp⟩
  obtain ⟨v, hv⟩ : ∃ v, v * d = b - y6 := ⟨(b - y6) / d, by field_simp⟩
  have hu0 : 0 < u := by
    by_contra h; push_neg at h; nlinarith [mul_nonneg (neg_nonneg.2 h) hb0.le]
  have hv0 : 0 < v := by
    by_contra h; push_neg at h; nlinarith [mul_nonneg (neg_nonneg.2 h) hd.le]
  have huv : u < v := by
    by_contra h; push_neg at h
    nlinarith [mul_nonneg (sub_nonneg.2 h) (mul_pos hb0 hd).le]
  obtain ⟨r, hr⟩ : ∃ r, r = (u + v) / 2 := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; linarith
  obtain ⟨eta, het⟩ : ∃ eta, eta = b * (v - u) / 4 := ⟨_, rfl⟩
  have het0 : 0 < eta := by rw [het]; nlinarith [mul_pos hb0 (sub_pos.2 huv)]
  obtain ⟨eps, hep⟩ : ∃ eps, eps * (5 * (1 + xi)) = eta := ⟨eta / (5 * (1 + xi)), by field_simp⟩
  have hep0 : 0 < eps := by
    by_contra h; push_neg at h; nlinarith [mul_nonneg (neg_nonneg.2 h) (by linarith : (0:ℝ) ≤ 5 * (1 + xi))]
  have hDp : 0 < d * (v - u) / 2 := by nlinarith [mul_pos hd (sub_pos.2 huv)]
  obtain ⟨m, hm1, hm⟩ : ∃ m, 1 ≤ m ∧ d * c - (b - y6) * y6 + d * eps < m * (d * (v - u) / 2) := by
    refine ⟨1 + |d * c - (b - y6) * y6 + d * eps| / (d * (v - u) / 2), ?_, ?_⟩
    · have := div_nonneg (abs_nonneg (d * c - (b - y6) * y6 + d * eps)) hDp.le
      linarith
    · have : (1 + |d * c - (b - y6) * y6 + d * eps| / (d * (v - u) / 2)) * (d * (v - u) / 2)
          = d * (v - u) / 2 + |d * c - (b - y6) * y6 + d * eps| := by field_simp
      rw [this]
      nlinarith [le_abs_self (d * c - (b - y6) * y6 + d * eps)]
  obtain ⟨c0y, hc0y⟩ : ∃ c0y, c0y * (1 - xi) = b + xi * m := ⟨(b + xi * m) / (1 - xi), by field_simp⟩
  obtain ⟨c0z, hc0z⟩ : ∃ c0z, c0z * (1 - xi) = d - eta - xi * (c + r * m + eps) :=
    ⟨(d - eta - xi * (c + r * m + eps)) / (1 - xi), by field_simp⟩
  obtain ⟨p, hp⟩ : ∃ p, p * L = -m - c0y := ⟨(-m - c0y) / L, by field_simp⟩
  obtain ⟨q, hq⟩ : ∃ q, q * L = c + r * m + eps - c0z := ⟨(c + r * m + eps - c0z) / L, by field_simp⟩
  have e1 : c0y + p * L = -m := by linarith
  have e2 : c0z + q * L = c + r * m + eps := by linarith
  have e3 : c0y + xi * (p * L) = b := by rw [hp]; linear_combination hc0y
  have e4 : c0z + xi * (q * L) = d - eta := by rw [hq]; linear_combination hc0z
  have hc0yy : y2 < c0y := by
    have h : (c0y - y2) * (1 - xi) = (b - y2) + xi * (m + y2) := by linear_combination hc0y
    have h2 : 0 < (c0y - y2) * (1 - xi) := by
      rw [h]; nlinarith [mul_pos hxi (by linarith : (0:ℝ) < m + y2)]
    have := (mul_pos_iff_of_pos_right hx1).1 h2
    linarith
  have hc0y0 : 0 < c0y := lt_trans hy2 hc0yy
  have hcz : c0z < c := by
    have h : (c0z - c) * (1 - xi) = d - eta - c - xi * (r * m + eps) := by linear_combination hc0z
    have h2 : d - eta - c < 0 := by nlinarith [mul_pos hb0 hu0]
    have h3 : 0 < xi * (r * m + eps) := mul_pos hxi (by nlinarith [mul_pos hr0 (by linarith : (0:ℝ) < m)])
    have h4 : (c0z - c) * (1 - xi) < 0 := by rw [h]; linarith
    by_contra hh; push_neg at hh
    nlinarith [mul_nonneg (sub_nonneg.2 hh) hx1.le]
  have hc5 : 0 < r * c0y + c0z - c := by
    have h : (r * c0y + c0z - c) * (1 - xi) = eta - xi * eps := by
      have hbr : r * b - u * b = b * (v - u) / 2 := by rw [hr]; ring
      linear_combination r * hc0y + hc0z + hbr + hu - 2 * het
    have h2 : 0 < eta - xi * eps := by nlinarith [mul_pos hxi hep0]
    by_contra hh; push_neg at hh
    nlinarith [mul_nonneg (neg_nonneg.2 hh) hx1.le]
  have key6 : (b - y6) * (-m) + d * (c + r * m + eps) < (b - y6) * y6 := by
    have : (b - y6) * y6 - ((b - y6) * (-m) + d * (c + r * m + eps))
        = m * (d * (v - u) / 2) - (d * c - (b - y6) * y6 + d * eps) := by
      rw [hr]; linear_combination (-m) * hv
    linarith
  have hr1 : 0 < b * (c - d) + d * (b - y2) := by nlinarith [mul_pos hb0 hcd, mul_nonneg hd.le (sub_nonneg.2 hb)]
  have hmp : 0 < m := by linarith
  refine box_hel hL hc hy6 hr0 !₂[1, p, q] !₂[0, c0z, -c0y] ?_
  intro i hi
  fin_cases i
  · exact absurd rfl hi
  · exact iv_c1 hL hc hy6 hy2 hxi hb0 hd hcd hr0 hb hr1 (by rw [e3, e4]; nlinarith) (by rw [e3, e4]; nlinarith)
  · exact iv_c2 hL hc hy6 hy2 hxi hb0 hd hcd hr0 hb hc0yy (by nlinarith [mul_nonneg (sub_nonneg.2 hb) (sub_pos.2 hc0yy).le, mul_pos hcd (sub_pos.2 hcz)])
  · have hmr : 0 < r * m := mul_pos hr0 hmp
    exact iv_c3 hL hc hy6 hy2 hxi hb0 hd hcd hr0 hb (by rw [e2]; linarith)
      (by rw [e1, e2]; have : c + r * m + eps - c + r * -m = eps := by ring
          linarith)
  · have hmr : 0 < r * m := mul_pos hr0 hmp
    exact iv_c4 hL hc hy6 hy2 hxi hb0 hd hcd hr0 hb (by rw [e2]; linarith) (by rw [e1]; linarith)
  · exact iv_c5 hL hc hy6 hy2 hxi hb0 hd hcd hr0 hb hc0y0 hc5
  · exact iv_c6 hL hc hy6 hy2 hxi hb0 hd hcd hr0 hb (by rw [e1]; linarith) (by rw [e1, e2]; linarith)

end Minimality.T24.Par
