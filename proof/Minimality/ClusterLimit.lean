module

public import Mathlib
public import Minimality.Prism

@[expose] public section

/-!
# Lemma CL (the cluster limit)

Let `x₀ x₁ x₂ p` be affinely independent, `g` the centroid of `x₀ x₁ x₂` and `u = g - p`.
Choose a view `R` (a rotation with `R u = r e_z`), so that the screen position
`viewPt R v = proj_xy (R v)` is the orthogonal projection along `u`.  Then `π g = π p`, and the
projected triangle `π x₀ π x₁ π x₂` has the point `π g` at distance at least `ρ` from each edge
line, where `ρ = clusterRadius R x₀ x₁ x₂`.

If every other vertex of `V` lies within distance `ρ` of `p`, then (orthogonal projection being
1-Lipschitz) it projects strictly inside the triangle, so the silhouette of `conv V` at this view
is the triangle `x₀ x₁ x₂`, and a triangle silhouette is cyclically unimodal for any depths
(`isCyclicUnimodal_three`).  Hence `V` is Rupert (`isRupert_of_open_unimodal`, depth ties are
allowed since the view is perturbed).

* `cluster_core`    — the statement at a given view `R` with the projected triangle
                      counterclockwise.
* `clusterLimit`    — the self-contained form: a non-degenerate `x₀ x₁ x₂ p` gives a view `R`
                      and a radius `ρ > 0` with the conclusion.
-/

set_option autoImplicit false

namespace Minimality

open scoped RealInnerProductSpace Matrix
open Finset

/-! ### Screen positions -/

/-- Screen position of `v` at the view `R`. -/
noncomputable def viewPt (R : Matrix (Fin 3) (Fin 3) ℝ) (v : ℝ³) : ℝ² :=
  proj_xy (R.toEuclideanLin v)

theorem proj_xy_sub (a b : ℝ³) : proj_xy (a - b) = proj_xy a - proj_xy b := by
  ext i; fin_cases i <;> simp [proj_xy]

theorem viewPt_sub (R : Matrix (Fin 3) (Fin 3) ℝ) (a b : ℝ³) :
    viewPt R (a - b) = viewPt R a - viewPt R b := by
  simp [viewPt, map_sub, proj_xy_sub]

theorem norm_proj_xy_le (y : ℝ³) : ‖proj_xy y‖ ≤ ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  simp only [Fin.sum_univ_two, Fin.sum_univ_three, proj_xy, Real.norm_eq_abs, sq_abs]
  simp
  nlinarith [sq_nonneg (y 2)]

/-- Orthogonal projection along a view direction is 1-Lipschitz. -/
theorem norm_viewPt_le {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO3) (v : ℝ³) :
    ‖viewPt R v‖ ≤ ‖v‖ := by
  have h1 := norm_proj_xy_le (R.toEuclideanLin v)
  have h2 : ‖R.toEuclideanLin v‖ = ‖v‖ := (so3Isometry hR).norm_map v
  unfold viewPt
  linarith

theorem abs_cross2_le (a b : ℝ²) : |cross2 a b| ≤ ‖a‖ * ‖b‖ := by
  have ha : ‖a‖ = Real.sqrt (a 0 ^ 2 + a 1 ^ 2) := by
    rw [EuclideanSpace.norm_eq]; simp [Fin.sum_univ_two]
  have hb : ‖b‖ = Real.sqrt (b 0 ^ 2 + b 1 ^ 2) := by
    rw [EuclideanSpace.norm_eq]; simp [Fin.sum_univ_two]
  rw [ha, hb, ← Real.sqrt_mul (by positivity)]
  apply Real.abs_le_sqrt
  simp only [cross2]
  nlinarith [sq_nonneg (a 0 * b 0 + a 1 * b 1)]

/-! ### The radius -/

/-- Distance from the point `q` to the line through `a ≠ b` (planar). -/
noncomputable def edgeDist (a b q : ℝ²) : ℝ := |cross2 (b - a) (q - a)| / ‖b - a‖

/-- The centroid of the triangle `x₀ x₁ x₂`. -/
noncomputable def centroid3 (x₀ x₁ x₂ : ℝ³) : ℝ³ := (1 / 3 : ℝ) • (x₀ + x₁ + x₂)

/-- **The cluster radius** `ρ`: the distance from the projected centroid to the three edge lines
of the projected triangle `π x₀ π x₁ π x₂`. -/
noncomputable def clusterRadius (R : Matrix (Fin 3) (Fin 3) ℝ) (x₀ x₁ x₂ : ℝ³) : ℝ :=
  min (min (edgeDist (viewPt R x₀) (viewPt R x₁) (viewPt R (centroid3 x₀ x₁ x₂)))
      (edgeDist (viewPt R x₁) (viewPt R x₂) (viewPt R (centroid3 x₀ x₁ x₂))))
    (edgeDist (viewPt R x₂) (viewPt R x₀) (viewPt R (centroid3 x₀ x₁ x₂)))

theorem cross2_zero_left (b : ℝ²) : cross2 0 b = 0 := by simp [cross2]

theorem planar_left (a b g q : ℝ²) (hc : 0 < cross2 (b - a) (g - a))
    (hq : ‖q - g‖ < edgeDist a b g) : 0 < cross2 (b - a) (q - a) := by
  have hne : b - a ≠ 0 := by
    intro h; rw [h, cross2_zero_left] at hc; exact lt_irrefl _ hc
  have hb : 0 < ‖b - a‖ := norm_pos_iff.mpr hne
  rw [edgeDist, abs_of_pos hc, lt_div_iff₀ hb] at hq
  have e : q - a = (g - a) + (q - g) := by abel
  rw [e, cross2_add_right]
  have h1 := abs_cross2_le (b - a) (q - g)
  have h2 := neg_abs_le (cross2 (b - a) (q - g))
  nlinarith

theorem edgeDist_pos (a b g : ℝ²) (hc : 0 < cross2 (b - a) (g - a)) : 0 < edgeDist a b g := by
  have hne : b - a ≠ 0 := by
    intro h; rw [h, cross2_zero_left] at hc; exact lt_irrefl _ hc
  have hb : 0 < ‖b - a‖ := norm_pos_iff.mpr hne
  rw [edgeDist, abs_of_pos hc]
  positivity

/-! ### Triangles as 3-cycles -/

/-- The 3-cycle `a b c`. -/
def tri3 {α : Type*} (a b c : α) : ZMod 3 → α := ![a, b, c]

theorem cl_zmod3_cases (i : ZMod 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  revert i; decide

theorem zmod3_succ_zero : (0 : ZMod 3) + 1 = 1 := by decide
theorem zmod3_succ_one : (1 : ZMod 3) + 1 = 2 := by decide
theorem zmod3_succ_two : (2 : ZMod 3) + 1 = 0 := by decide
theorem zmod3_pred_zero : (0 : ZMod 3) - 1 = 2 := by decide
theorem zmod3_pred_one : (1 : ZMod 3) - 1 = 0 := by decide
theorem zmod3_pred_two : (2 : ZMod 3) - 1 = 1 := by decide

theorem isCcwPolygon_three (p : ZMod 3 → ℝ²) (h : 0 < cross2 (p 1 - p 0) (p 2 - p 0)) :
    IsCcwPolygon p := by
  refine ⟨by norm_num, ?_⟩
  intro i j hji hji1
  rcases cl_zmod3_cases i with rfl | rfl | rfl <;> rcases cl_zmod3_cases j with rfl | rfl | rfl <;>
    simp only [zmod3_succ_zero, zmod3_succ_one, zmod3_succ_two] at hji1 ⊢ <;>
    first
    | exact absurd rfl hji
    | exact absurd rfl hji1
    | (simp only [cross2, PiLp.sub_apply] at h ⊢; nlinarith [h])

/-- A silhouette triangle is cyclically unimodal for any three distinct depths. -/
theorem isCyclicUnimodal_three (z : ZMod 3 → ℝ) (hz : Function.Injective z) :
    IsCyclicUnimodal z := by
  refine ⟨hz, ?_⟩
  have h01 : z 0 ≠ z 1 := fun h => absurd (hz h) (by decide)
  have h12 : z 1 ≠ z 2 := fun h => absurd (hz h) (by decide)
  have h02 : z 0 ≠ z 2 := fun h => absurd (hz h) (by decide)
  have hmax : (z 1 < z 0 ∧ z 2 < z 0) ∨ (z 0 < z 1 ∧ z 2 < z 1) ∨ (z 0 < z 2 ∧ z 1 < z 2) := by
    rcases lt_or_gt_of_ne h01 with h | h <;> rcases lt_or_gt_of_ne h12 with h' | h' <;>
      rcases lt_or_gt_of_ne h02 with h'' | h'' <;>
      first
      | (left; exact ⟨by linarith, by linarith⟩)
      | (right; left; exact ⟨by linarith, by linarith⟩)
      | (right; right; exact ⟨by linarith, by linarith⟩)
  rw [Finset.card_eq_one]
  rcases hmax with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · refine ⟨0, ?_⟩
    ext i
    rcases cl_zmod3_cases i with rfl | rfl | rfl <;>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        zmod3_succ_zero, zmod3_succ_one, zmod3_succ_two, zmod3_pred_zero, zmod3_pred_one,
        zmod3_pred_two] <;>
      constructor <;> intro h
    all_goals first
      | trivial
      | (exfalso; obtain ⟨h1, h2⟩ := h; linarith)
  · refine ⟨1, ?_⟩
    ext i
    rcases cl_zmod3_cases i with rfl | rfl | rfl <;>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        zmod3_succ_zero, zmod3_succ_one, zmod3_succ_two, zmod3_pred_zero, zmod3_pred_one,
        zmod3_pred_two] <;>
      constructor <;> intro h
    all_goals first
      | trivial
      | (exfalso; obtain ⟨h1, h2⟩ := h; linarith)
  · refine ⟨2, ?_⟩
    ext i
    rcases cl_zmod3_cases i with rfl | rfl | rfl <;>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        zmod3_succ_zero, zmod3_succ_one, zmod3_succ_two, zmod3_pred_zero, zmod3_pred_one,
        zmod3_pred_two] <;>
      constructor <;> intro h
    all_goals first
      | trivial
      | (exfalso; obtain ⟨h1, h2⟩ := h; linarith)

/-! ### The core statement at a given view -/

theorem viewPt_smul_add (R : Matrix (Fin 3) (Fin 3) ℝ) (x₀ x₁ x₂ : ℝ³) :
    viewPt R (centroid3 x₀ x₁ x₂) = (1 / 3 : ℝ) • (viewPt R x₀ + viewPt R x₁ + viewPt R x₂) := by
  ext i; fin_cases i <;>
    simp [viewPt, centroid3, proj_xy, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three] <;> ring

theorem viewPt_centroid_eq {R : Matrix (Fin 3) (Fin 3) ℝ} {x₀ x₁ x₂ p : ℝ³} {r : ℝ}
    (hu : R.toEuclideanLin (centroid3 x₀ x₁ x₂ - p) = r • ez) :
    viewPt R (centroid3 x₀ x₁ x₂) = viewPt R p := by
  have h : viewPt R (centroid3 x₀ x₁ x₂ - p) = 0 := by
    unfold viewPt; rw [hu]; ext i; fin_cases i <;> simp [proj_xy, ez]
  rw [viewPt_sub] at h
  exact sub_eq_zero.mp h

/-- The projected centroid is strictly left of each edge of a counterclockwise projected
triangle. -/
theorem centroid_cross_pos (R : Matrix (Fin 3) (Fin 3) ℝ) (x₀ x₁ x₂ : ℝ³)
    (hD : 0 < cross2 (viewPt R x₁ - viewPt R x₀) (viewPt R x₂ - viewPt R x₀)) :
    0 < cross2 (viewPt R x₁ - viewPt R x₀) (viewPt R (centroid3 x₀ x₁ x₂) - viewPt R x₀) ∧
    0 < cross2 (viewPt R x₂ - viewPt R x₁) (viewPt R (centroid3 x₀ x₁ x₂) - viewPt R x₁) ∧
    0 < cross2 (viewPt R x₀ - viewPt R x₂) (viewPt R (centroid3 x₀ x₁ x₂) - viewPt R x₂) := by
  rw [viewPt_smul_add]
  simp only [cross2, PiLp.sub_apply, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul] at hD ⊢
  refine ⟨by nlinarith [hD], by nlinarith [hD], by nlinarith [hD]⟩

theorem clusterRadius_pos {R : Matrix (Fin 3) (Fin 3) ℝ} {x₀ x₁ x₂ : ℝ³}
    (hD : 0 < cross2 (viewPt R x₁ - viewPt R x₀) (viewPt R x₂ - viewPt R x₀)) :
    0 < clusterRadius R x₀ x₁ x₂ := by
  obtain ⟨h0, h1, h2⟩ := centroid_cross_pos R x₀ x₁ x₂ hD
  unfold clusterRadius
  exact lt_min (lt_min (edgeDist_pos _ _ _ h0) (edgeDist_pos _ _ _ h1)) (edgeDist_pos _ _ _ h2)

theorem ne_of_cross_pos {R : Matrix (Fin 3) (Fin 3) ℝ} {x₀ x₁ x₂ : ℝ³}
    (hD : 0 < cross2 (viewPt R x₁ - viewPt R x₀) (viewPt R x₂ - viewPt R x₀)) :
    x₀ ≠ x₁ ∧ x₁ ≠ x₂ ∧ x₀ ≠ x₂ := by
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> subst h <;>
    simp [cross2] at hD
  all_goals nlinarith [hD]

/-- **Lemma CL at a given view.**  Let `R` be a view with `R (g - p) = r e_z`, so that `π`
is the projection along `u = g - p`, and let the projected triangle `π x₀ π x₁ π x₂` be
counterclockwise (non-degenerate).  If every vertex of `V` other than `x₀, x₁, x₂` lies within
`clusterRadius` of `p`, then `V` is Rupert: the silhouette of `conv V` at this view is the
triangle `x₀ x₁ x₂`, all other vertices project into its interior, and a triangle is
unimodal. -/
theorem cluster_core {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO3) (x₀ x₁ x₂ p : ℝ³) (r : ℝ)
    (hu : R.toEuclideanLin (centroid3 x₀ x₁ x₂ - p) = r • ez)
    (hD : 0 < cross2 (viewPt R x₁ - viewPt R x₀) (viewPt R x₂ - viewPt R x₀))
    (V : Finset ℝ³) (h0 : x₀ ∈ V) (h1 : x₁ ∈ V) (h2 : x₂ ∈ V)
    (hV : ∀ v ∈ V, v ≠ x₀ → v ≠ x₁ → v ≠ x₂ → dist v p < clusterRadius R x₀ x₁ x₂) :
    IsRupert V := by
  obtain ⟨c0, c1, c2⟩ := centroid_cross_pos R x₀ x₁ x₂ hD
  obtain ⟨n01, n12, n02⟩ := ne_of_cross_pos hD
  have hg := viewPt_centroid_eq hu
  have hxV : ∀ i, tri3 x₀ x₁ x₂ i ∈ V := by
    intro i; rcases cl_zmod3_cases i with rfl | rfl | rfl <;> assumption
  have hxinj : Function.Injective (tri3 x₀ x₁ x₂) := by
    intro i j hij
    rcases cl_zmod3_cases i with rfl | rfl | rfl <;> rcases cl_zmod3_cases j with rfl | rfl | rfl
    all_goals first
      | rfl
      | exact absurd hij n01
      | exact absurd hij.symm n01
      | exact absurd hij n12
      | exact absurd hij.symm n12
      | exact absurd hij n02
      | exact absurd hij.symm n02
  have hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (tri3 x₀ x₁ x₂ i))) :=
    isCcwPolygon_three (fun i => viewPt R (tri3 x₀ x₁ x₂ i)) hD
  have hin : ∀ v ∈ V, (∀ i, v ≠ tri3 x₀ x₁ x₂ i) → ∀ i,
      0 < cross2 (proj_xy (R.toEuclideanLin (tri3 x₀ x₁ x₂ (i + 1))) -
          proj_xy (R.toEuclideanLin (tri3 x₀ x₁ x₂ i)))
        (proj_xy (R.toEuclideanLin v) - proj_xy (R.toEuclideanLin (tri3 x₀ x₁ x₂ i))) := by
    intro v hv hvx i
    have hv0 : v ≠ x₀ := hvx 0
    have hv1 : v ≠ x₁ := hvx 1
    have hv2 : v ≠ x₂ := hvx 2
    have hlt := hV v hv hv0 hv1 hv2
    have hq : ‖viewPt R v - viewPt R (centroid3 x₀ x₁ x₂)‖ < clusterRadius R x₀ x₁ x₂ := by
      rw [hg, ← viewPt_sub]
      exact lt_of_le_of_lt ((norm_viewPt_le hR _).trans_eq (dist_eq_norm v p).symm) hlt
    unfold clusterRadius at hq
    rcases cl_zmod3_cases i with rfl | rfl | rfl <;>
      simp only [zmod3_succ_zero, zmod3_succ_one, zmod3_succ_two]
    · exact planar_left _ _ _ _ c0 (lt_of_lt_of_le hq (le_trans (min_le_left _ _) (min_le_left _ _)))
    · exact planar_left _ _ _ _ c1 (lt_of_lt_of_le hq (le_trans (min_le_left _ _) (min_le_right _ _)))
    · exact planar_left _ _ _ _ c2 (lt_of_lt_of_le hq (min_le_right _ _))
  refine isRupert_of_open_unimodal V hR (tri3 x₀ x₁ x₂) hxV hxinj hp hin (fun _ => True)
    (by simp) trivial (fun z hz _ => isCyclicUnimodal_three z hz)

/-! ### Non-degeneracy and the choice of the view -/

theorem inner_cross_eq_det (a b c : ℝ³) :
    ⟪cross a b, c⟫ = Matrix.det !![a 0, a 1, a 2; b 0, b 1, b 2; c 0, c 1, c 2] := by
  simp [cross, PiLp.inner_apply, Fin.sum_univ_three, Matrix.det_fin_three]; ring

/-- The triple product is invariant under rotations. -/
theorem inner_cross_rot {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO3) (a b c : ℝ³) :
    ⟪cross (R.toEuclideanLin a) (R.toEuclideanLin b), R.toEuclideanLin c⟫ =
      ⟪cross a b, c⟫ := by
  have hdet : R.det = 1 := (Matrix.mem_specialOrthogonalGroup_iff.mp hR).2
  have e : (!![(R.toEuclideanLin a) 0, (R.toEuclideanLin a) 1, (R.toEuclideanLin a) 2;
      (R.toEuclideanLin b) 0, (R.toEuclideanLin b) 1, (R.toEuclideanLin b) 2;
      (R.toEuclideanLin c) 0, (R.toEuclideanLin c) 1, (R.toEuclideanLin c) 2] :
        Matrix (Fin 3) (Fin 3) ℝ) =
      !![a 0, a 1, a 2; b 0, b 1, b 2; c 0, c 1, c 2] * Rᵀ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.toLpLin_apply, Matrix.mulVec,
        dotProduct] <;> ring
  rw [inner_cross_eq_det, inner_cross_eq_det, e, Matrix.det_mul, Matrix.det_transpose, hdet,
    mul_one]

theorem toEuclideanLin_mul_apply (A B : Matrix (Fin 3) (Fin 3) ℝ) (v : ℝ³) :
    (A * B).toEuclideanLin v = A.toEuclideanLin (B.toEuclideanLin v) := by
  simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

/-- Flipping the view by a half turn about the x-axis reverses the screen orientation. -/
theorem viewPt_flip (R : Matrix (Fin 3) (Fin 3) ℝ) (v : ℝ³) :
    viewPt (rotX (-1) 0 * R) v = !₂[(viewPt R v) 0, -(viewPt R v) 1] := by
  ext i
  simp only [viewPt, toEuclideanLin_mul_apply]
  fin_cases i <;>
    simp [proj_xy, rotX, Matrix.toLpLin_apply,
      Matrix.mulVec, Matrix.vecMul, dotProduct, Fin.sum_univ_three]

/-- A view with `R (g - p) = r e_z` and counterclockwise projected triangle. -/
theorem exists_ccw_view (x₀ x₁ x₂ p : ℝ³)
    (hT : ⟪cross (x₁ - x₀) (x₂ - x₀), p - x₀⟫ ≠ 0) :
    ∃ R ∈ SO3, (∃ r : ℝ, R.toEuclideanLin (centroid3 x₀ x₁ x₂ - p) = r • ez) ∧
      0 < cross2 (viewPt R x₁ - viewPt R x₀) (viewPt R x₂ - viewPt R x₀) := by
  set a := x₁ - x₀ with ha
  set b := x₂ - x₀ with hb
  have hp : p - x₀ = (1 / 3 : ℝ) • (a + b) - (centroid3 x₀ x₁ x₂ - p) := by
    ext i; simp [centroid3, ha, hb]; ring
  have hu0 : centroid3 x₀ x₁ x₂ - p ≠ 0 := by
    intro h
    apply hT
    rw [hp, h, sub_zero, inner_smul_right, inner_add_right, inner_cross_left,
      inner_cross_right]; simp
  obtain ⟨R, hR, r, hr, hRu⟩ := exists_rotation_to_ez_pos _ hu0
  -- the sign of the projected area
  have hD : cross2 (viewPt R x₁ - viewPt R x₀) (viewPt R x₂ - viewPt R x₀) ≠ 0 := by
    intro hz
    apply hT
    have hz' : cross2 (viewPt R a) (viewPt R b) = 0 := by
      rw [ha, hb, viewPt_sub, viewPt_sub]; exact hz
    rw [← inner_cross_rot hR]
    have e1 : R.toEuclideanLin (p - x₀) = (1 / 3 : ℝ) • (R.toEuclideanLin a +
        R.toEuclideanLin b) - r • ez := by
      rw [hp, map_sub, map_smul, map_add, hRu]
    rw [e1, inner_sub_right, inner_smul_right, inner_add_right, inner_cross_left,
      inner_cross_right, inner_smul_right, inner_cross_ez]
    have hz'' : cross2 (proj_xy (R.toEuclideanLin a)) (proj_xy (R.toEuclideanLin b)) = 0 := hz'
    rw [hz'']; simp
  rcases lt_or_gt_of_ne hD with hneg | hpos
  · refine ⟨rotX (-1) 0 * R, mul_mem (rotX_mem_SO3 (by norm_num)) hR, ⟨-r, ?_⟩, ?_⟩
    · rw [toEuclideanLin_mul_apply, hRu]
      ext i; fin_cases i <;> simp [rotX, ez, Matrix.toLpLin_apply]
    · simp only [viewPt_flip, cross2, PiLp.sub_apply] at hneg ⊢
      simp at hneg ⊢
      nlinarith [hneg]
  · exact ⟨R, hR, ⟨r, hRu⟩, hpos⟩

/-- **Lemma CL (the cluster limit).**  Let `x₀ x₁ x₂ p` be non-degenerate (`p` off the plane of
`x₀ x₁ x₂`), `g` the centroid of `x₀ x₁ x₂` and `u = g - p`.  Then there is a view `R` along `u`
(`R u = r e_z`) with `ρ = clusterRadius R x₀ x₁ x₂ > 0` (the distance from `π g = π p` to the
edge lines of the projected triangle `π x₀ π x₁ π x₂`; it depends only on the four points) such
that every finite vertex set `V ∋ x₀, x₁, x₂` whose other points lie within `ρ` of `p` is Rupert.
The silhouette of `conv V` along `u` is the triangle `x₀ x₁ x₂`, and the cluster projects
strictly inside it. -/
theorem clusterLimit (x₀ x₁ x₂ p : ℝ³) (hT : ⟪cross (x₁ - x₀) (x₂ - x₀), p - x₀⟫ ≠ 0) :
    ∃ R ∈ SO3, (∃ r : ℝ, R.toEuclideanLin (centroid3 x₀ x₁ x₂ - p) = r • ez) ∧
      0 < clusterRadius R x₀ x₁ x₂ ∧
      ∀ V : Finset ℝ³, x₀ ∈ V → x₁ ∈ V → x₂ ∈ V →
        (∀ v ∈ V, v ≠ x₀ → v ≠ x₁ → v ≠ x₂ → dist v p < clusterRadius R x₀ x₁ x₂) →
        IsRupert V := by
  obtain ⟨R, hR, ⟨r, hu⟩, hD⟩ := exists_ccw_view x₀ x₁ x₂ p hT
  exact ⟨R, hR, ⟨r, hu⟩, clusterRadius_pos hD, fun V h0 h1 h2 hV =>
    cluster_core hR x₀ x₁ x₂ p r hu hD V h0 h1 h2 hV⟩


end Minimality
