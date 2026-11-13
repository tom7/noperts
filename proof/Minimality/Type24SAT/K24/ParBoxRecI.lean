module

public import Minimality.Type24SAT.K24.ParBoxHel

@[expose] public section

/-!
# Type 24 box corner `R₄'`: recipe I

One fixed lexicographic motion at the edge view along `e = x 4 - x 0`, tilted into the hiding cone of the corner `4`.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset
namespace Minimality.T24.Par
open Minimality.Split Minimality.Split.HEL
open Minimality (cross)

theorem recI_LPpos {A B A' : ℝ} (h : 0 < A') (e : A = A') : LP A B := Or.inl (e ▸ h)
theorem recI_LPzero {A B B' : ℝ} (hA : A = 0) (hB : 0 < B') (e : B = B') : LP A B :=
  Or.inr ⟨hA, e ▸ hB⟩

macro "rowtac" : tactic => `(tactic| (simp [boxCfg, Minimality.cross] <;> field_simp <;> ring))

theorem recI_core {L c y2 y6 xi ze b r dl M : ℝ} (hL : 0 < L) (hc : 0 < c) (hy6 : 0 < y6)
    (hy : y6 < y2) (hxi : 0 < xi) (hze : 0 < ze) (hlo : y6 * xi + y2 * ze < b)
    (hhi : b < y2 * (1 - xi) + y6 * (1 - ze)) (hb : b < y2)
    (hr : 0 < r) (hdl : 0 < dl) (hdl2 : 2 * (y2 - y6) * dl = r * c * y2) (hM : 1 ≤ M)
    (hM6 : c ^ 2 - (y2 - y6) * y6 < M * ((y2 - y6) - 2 * r * c))
    (hM0 : (1 - xi) * (b * (y2 + dl) + ze * c * (c - r * y2)) + xi * (ze * c * c) - (b * b + ze * c * (ze * c))
        < M * (xi * (b - ze * c * 2 * r)))
    (hM2 : (1 - xi) * ((y2 - b) * (y2 + dl) + (c - ze * c) * (c - r * y2)) + xi * ((c - ze * c) * c)
        - ((y2 - b) * b + (c - ze * c) * (ze * c))
        < M * (xi * ((y2 - b) - (c - ze * c) * 2 * r))) :
    IsRupert (univ.image (boxCfg L c y2 y6 xi ze b)) := by
  have hy2 : 0 < y2 := by linarith
  have hM0' : 0 < M := by linarith
  have hb2 : 0 < b - ze * y2 := by nlinarith [mul_pos hy6 hxi]
  refine box_hel hL hc hy6 hr (!₂[1, (-M - (y2 + dl)) / L, ((c + 2 * r * M) - (c - r * y2)) / L])
    (!₂[0, c - r * y2, -(y2 + dl)]) ?_
  intro i hi
  fin_cases i
  · exact absurd rfl hi
  · -- point 1, cone (2, 0)
    refine cone_cert L r _ _ _ _ (boxCfg L c y2 y6 xi ze b 2) (boxCfg L c y2 y6 xi ze b 0)
      (Finset.mem_image_of_mem _ (Finset.mem_univ _)) (Finset.mem_image_of_mem _ (Finset.mem_univ _)) ?_ ?_ ?_
    · refine recI_LPpos (A' := L * c * (b - ze * y2)) (by positivity) ?_
      simp [boxCfg, Minimality.cross]; ring
    · refine recI_LPpos (A' := L * (M * (xi * (b - ze * c * 2 * r)) - ((1 - xi) * (b * (y2 + dl) + ze * c * (c - r * y2)) + xi * (ze * c * c) - (b * b + ze * c * (ze * c))))) (mul_pos hL (sub_pos.2 hM0)) ?_
      simp [boxCfg, Minimality.cross]; field_simp; ring
    · refine recI_LPpos (A' := L * (M * (xi * ((y2 - b) - (c - ze * c) * 2 * r)) - ((1 - xi) * ((y2 - b) * (y2 + dl) + (c - ze * c) * (c - r * y2)) + xi * ((c - ze * c) * c)
        - ((y2 - b) * b + (c - ze * c) * (ze * c))))) (mul_pos hL (sub_pos.2 hM2)) ?_
      simp [boxCfg, Minimality.cross]; field_simp; ring
  · -- point 2, cone (5, 6)
    refine cone_cert L r _ _ _ _ (boxCfg L c y2 y6 xi ze b 5) (boxCfg L c y2 y6 xi ze b 6)
      (Finset.mem_image_of_mem _ (Finset.mem_univ _)) (Finset.mem_image_of_mem _ (Finset.mem_univ _)) ?_ ?_ ?_
    · refine recI_LPpos (A' := L * c * y2) (by positivity) ?_
      rowtac
    · refine recI_LPpos (A' := L * (c * r * y2 / 2)) (by positivity) ?_
      simp [boxCfg, Minimality.cross]; field_simp; linear_combination (-1 : ℝ) * hdl2
    · refine recI_LPpos (A' := L * y2 * dl) (by positivity) ?_
      rowtac
  · -- point 3, cone (4, 5)
    refine cone_cert L r _ _ _ _ (boxCfg L c y2 y6 xi ze b 4) (boxCfg L c y2 y6 xi ze b 5)
      (Finset.mem_image_of_mem _ (Finset.mem_univ _)) (Finset.mem_image_of_mem _ (Finset.mem_univ _)) ?_ ?_ ?_
    · refine recI_LPzero (B' := L * c * r) (by rowtac) (by positivity) ?_
      rowtac
    · refine recI_LPzero (B' := L * r * M) (by rowtac) (by positivity) ?_
      rowtac
    · refine recI_LPpos (A' := 2 * L * c * r * M) (by positivity) ?_
      rowtac
  · -- point 4, cone (6, 3)
    refine cone_cert L r _ _ _ _ (boxCfg L c y2 y6 xi ze b 6) (boxCfg L c y2 y6 xi ze b 3)
      (Finset.mem_image_of_mem _ (Finset.mem_univ _)) (Finset.mem_image_of_mem _ (Finset.mem_univ _)) ?_ ?_ ?_
    · refine recI_LPpos (A' := L * c * y6) (by positivity) ?_
      rowtac
    · refine recI_LPpos (A' := L * c * (c + 2 * r * M)) (by positivity) ?_
      rowtac
    · refine recI_LPpos (A' := L * y6 * M) (by positivity) ?_
      rowtac
  · -- point 5, cone (3, 2)
    refine cone_cert L r _ _ _ _ (boxCfg L c y2 y6 xi ze b 3) (boxCfg L c y2 y6 xi ze b 2)
      (Finset.mem_image_of_mem _ (Finset.mem_univ _)) (Finset.mem_image_of_mem _ (Finset.mem_univ _)) ?_ ?_ ?_
    · refine recI_LPzero (B' := L * y2) (by rowtac) (by positivity) ?_
      rowtac
    · refine recI_LPpos (A' := L * y2 * (y2 + dl)) (by positivity) ?_
      rowtac
    · refine recI_LPzero (B' := L * r * dl) (by rowtac) (by positivity) ?_
      rowtac
  · -- point 6, cone (2, 4)
    refine cone_cert L r _ _ _ _ (boxCfg L c y2 y6 xi ze b 2) (boxCfg L c y2 y6 xi ze b 4)
      (Finset.mem_image_of_mem _ (Finset.mem_univ _)) (Finset.mem_image_of_mem _ (Finset.mem_univ _)) ?_ ?_ ?_
    · refine recI_LPpos (A' := L * c * y6) (by positivity) ?_
      rowtac
    · refine recI_LPpos (A' := L * y6 * (y6 + M)) (by positivity) ?_
      rowtac
    · refine recI_LPpos (A' := L * (M * ((y2 - y6) - 2 * r * c) - (c ^ 2 - (y2 - y6) * y6)))
        (mul_pos hL (sub_pos.2 hM6)) ?_
      rowtac

theorem recI_exM {g1 D1 g2 D2 g3 D3 : ℝ} (h1 : 0 < D1) (h2 : 0 < D2) (h3 : 0 < D3) :
    ∃ M : ℝ, 1 ≤ M ∧ g1 < M * D1 ∧ g2 < M * D2 ∧ g3 < M * D3 := by
  refine ⟨1 + |g1| / D1 + |g2| / D2 + |g3| / D3, ?_, ?_, ?_, ?_⟩
  · have := div_nonneg (abs_nonneg g1) h1.le
    have := div_nonneg (abs_nonneg g2) h2.le
    have := div_nonneg (abs_nonneg g3) h3.le
    linarith
  all_goals
    rw [← div_lt_iff₀ (by assumption)]
    first
    | (have e1 := div_le_div_of_nonneg_right (le_abs_self g1) h1.le
       have := div_nonneg (abs_nonneg g2) h2.le
       have := div_nonneg (abs_nonneg g3) h3.le
       linarith)
    | (have e1 := div_le_div_of_nonneg_right (le_abs_self g2) h2.le
       have := div_nonneg (abs_nonneg g1) h1.le
       have := div_nonneg (abs_nonneg g3) h3.le
       linarith)
    | (have e1 := div_le_div_of_nonneg_right (le_abs_self g3) h3.le
       have := div_nonneg (abs_nonneg g1) h1.le
       have := div_nonneg (abs_nonneg g2) h2.le
       linarith)

/-- Recipe I: `y6 < y2`, `b < y2`. -/
theorem rec_I {L c y2 y6 xi ze b : ℝ} (hL : 0 < L) (hc : 0 < c) (hy6 : 0 < y6) (hy : y6 < y2)
    (hxi : 0 < xi) (hze : 0 < ze) (hlo : y6 * xi + y2 * ze < b) (hhi : b < y2 * (1 - xi) + y6 * (1 - ze))
    (hb : b < y2) : IsRupert (univ.image (boxCfg L c y2 y6 xi ze b)) := by
  have hy2 : 0 < y2 := by linarith
  have hsum : xi + ze < 1 := by
    by_contra h
    push_neg at h
    nlinarith [mul_pos hy2 hy6, mul_nonneg hy2.le (sub_nonneg.2 h), mul_nonneg hy6.le (sub_nonneg.2 h)]
  have hcd : 0 < c - ze * c := by nlinarith
  have hd : 0 < ze * c := mul_pos hze hc
  have hb0 : 0 < b := by nlinarith [mul_pos hy6 hxi, mul_pos hy2 hze]
  have hyb : 0 < y2 - b := by linarith
  have hdy : 0 < y2 - y6 := by linarith
  obtain ⟨r, hr, hr1, hr2, hr3⟩ : ∃ r : ℝ, 0 < r ∧ 3 * r * c ≤ y2 - y6 ∧ 3 * r * (c - ze * c) ≤ y2 - b ∧
      3 * r * (ze * c) ≤ b := by
    obtain ⟨m, hm, m1, m2, m3⟩ : ∃ m : ℝ, 0 < m ∧ m ≤ (y2 - y6) / c ∧ m ≤ (y2 - b) / (c - ze * c) ∧
        m ≤ b / (ze * c) :=
      ⟨min (min ((y2 - y6) / c) ((y2 - b) / (c - ze * c))) (b / (ze * c)), by positivity,
        (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
        min_le_right _ _⟩
    have h1 := (le_div_iff₀ hc).1 m1
    have h2 := (le_div_iff₀ hcd).1 m2
    have h3 := (le_div_iff₀ hd).1 m3
    refine ⟨m / 3, by positivity, ?_, ?_, ?_⟩ <;> nlinarith
  have hdl : 0 < r * c * y2 / (2 * (y2 - y6)) := by positivity
  obtain ⟨dl, hdl_eq⟩ : ∃ dl, dl = r * c * y2 / (2 * (y2 - y6)) := ⟨_, rfl⟩
  have hdl' : 0 < dl := hdl_eq ▸ hdl
  have hdl2 : 2 * (y2 - y6) * dl = r * c * y2 := by
    rw [hdl_eq]; field_simp
  have hD6 : 0 < (y2 - y6) - 2 * r * c := by nlinarith
  have hD0 : 0 < xi * (b - ze * c * 2 * r) := by
    apply mul_pos hxi; nlinarith
  have hD2 : 0 < xi * ((y2 - b) - (c - ze * c) * 2 * r) := by
    apply mul_pos hxi; nlinarith
  obtain ⟨M, hM, hM6, hM0, hM2⟩ := recI_exM (g1 := c ^ 2 - (y2 - y6) * y6) hD6
    (g2 := (1 - xi) * (b * (y2 + dl) + ze * c * (c - r * y2)) + xi * (ze * c * c) - (b * b + ze * c * (ze * c))) hD0
    (g3 := (1 - xi) * ((y2 - b) * (y2 + dl) + (c - ze * c) * (c - r * y2)) + xi * ((c - ze * c) * c)
        - ((y2 - b) * b + (c - ze * c) * (ze * c))) hD2
  exact recI_core hL hc hy6 hy hxi hze hlo hhi hb hr hdl' hdl2 hM hM6 hM0 hM2

end Minimality.T24.Par
#print axioms Minimality.T24.Par.rec_I
