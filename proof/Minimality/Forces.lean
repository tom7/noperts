module

public import Minimality.Unimodal
public import Minimality.Tilt

@[expose] public section

/-!
# Lemma 7.1 at a view, frame-free

`isRupert_of_no_forces`: the force side of Lemma 7.1 (corner forces) stated at
a view `w` without a rotation or an explicit silhouette. A force system is a
family `F v` (`v ∈ V`) of vectors orthogonal to `w` with `⟪F v, y - v⟫ ≤ 0`
for every `y ∈ V` (so `F v` lies in the normal cone of the shadow at the
image of `v`; points inside the shadow get `F v = 0`), in equilibrium:
`Σ F v = 0`, `Σ ⟪v, w⟫ F v = 0` and the torque about `w`,
`Σ ⟪v × F v, w⟫`, vanishes. If every such system is zero, `V` is Rupert
(first-order free at `w`). Arguments by force estimates (as in "Lemma T at
the tie, robust form" of `FEWER-FACES-PROOFS.md` §7) only need these
inequalities at test points of `V`.
-/

namespace Minimality

open scoped RealInnerProductSpace
open Finset

theorem inner_liftH (n : ℝ²) (x : ℝ³) : ⟪liftH n, x⟫ = ⟪n, proj_xy x⟫ := by
  simp [liftH, proj_xy, PiLp.inner_apply, Fin.sum_univ_three, Fin.sum_univ_two]

theorem proj_liftH (n : ℝ²) : proj_xy (liftH n) = n := by
  ext i; fin_cases i <;> simp [liftH, proj_xy]

theorem inner_liftH_ez (n : ℝ²) : ⟪liftH n, ez⟫ = 0 := by
  rw [inner_ez]; simp [liftH]

/-- A solid has a shadow with nonempty interior at every rotation. -/
theorem interior_proj_convexHull_nonempty (V : Finset ℝ³) {R : Matrix (Fin 3) (Fin 3) ℝ}
    (hR : R ∈ SO3) (hsol : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty) :
    (interior (proj_xy '' convexHull ℝ ((V.image R.toEuclideanLin : Finset ℝ³) : Set ℝ³))).Nonempty := by
  classical
  obtain ⟨c, hc⟩ := hsol
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior c hc
  refine ⟨proj_xy (R.toEuclideanLin c), mem_interior.mpr ⟨Metric.ball _ r, ?_, Metric.isOpen_ball,
    Metric.mem_ball_self hr⟩⟩
  intro q hq
  set g := so3Isometry hR
  set x := g.symm (R.toEuclideanLin c + liftH (q - proj_xy (R.toEuclideanLin c)))
  have hx : g x = R.toEuclideanLin c + liftH (q - proj_xy (R.toEuclideanLin c)) := g.apply_symm_apply _
  have hdist : dist x c < r := by
    have e : dist x c = dist (g x) (g c) := (g.dist_map x c).symm
    rw [e, hx, so3Isometry_apply, dist_eq_norm, add_sub_cancel_left]
    have : ‖liftH (q - proj_xy (R.toEuclideanLin c))‖ = ‖q - proj_xy (R.toEuclideanLin c)‖ := by
      simp [liftH, EuclideanSpace.norm_eq, Fin.sum_univ_three, Fin.sum_univ_two]
    rw [this, ← dist_eq_norm]; exact hq
  have hxV : x ∈ convexHull ℝ (V : Set ℝ³) := interior_subset (hball hdist)
  refine ⟨g x, ?_, ?_⟩
  · have himg : R.toEuclideanLin '' convexHull ℝ (V : Set ℝ³) =
        convexHull ℝ ((V.image R.toEuclideanLin : Finset ℝ³) : Set ℝ³) := by
      rw [LinearMap.image_convexHull, coe_image]
    rw [← himg]; exact ⟨x, hxV, rfl⟩
  · rw [hx]
    ext i; fin_cases i <;> simp [proj_xy, liftH]

/-- Cramer's identity in `ℝ³`: four vectors are linearly dependent. -/
theorem det3_cramer (a b c w : ℝ³) :
    det3 b c w • a - det3 a c w • b + det3 a b w • c = det3 a b c • w := by
  ext i; fin_cases i <;>
    simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three] <;> ring

theorem det3_swap (x y w : ℝ³) : det3 x y w = -det3 y x w := by
  simp only [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]
  simp; ring

/-- A vector is determined by its inner products with a basis `a, b, w`. -/
theorem det3_smul_eq (a b w F : ℝ³) :
    det3 a b w • F = ⟪F, a⟫ • cross b w + ⟪F, b⟫ • cross w a + ⟪F, w⟫ • cross a b := by
  ext i; fin_cases i <;>
    simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three] <;> ring

/-- **A point inside the shadow carries no force.** If `v` projects (along
`w`) strictly inside the triangle `a b c` (counterclockwise), a force `F ⊥ w`
with `⟪F, y - v⟫ ≤ 0` at the three test points `y = a, b, c` is zero. -/
theorem force_eq_zero_of_inside {a b c v w F : ℝ³} (ha : 0 < det3 (b - v) (c - v) w)
    (hb : 0 < det3 (c - v) (a - v) w) (hc : 0 < det3 (a - v) (b - v) w)
    (hw : ⟪F, w⟫ = 0) (fa : ⟪F, a - v⟫ ≤ 0) (fb : ⟪F, b - v⟫ ≤ 0) (fc : ⟪F, c - v⟫ ≤ 0) :
    F = 0 := by
  have key := congrArg (fun z => ⟪F, z⟫) (det3_cramer (a - v) (b - v) (c - v) w)
  simp only [inner_add_right, inner_sub_right, real_inner_smul_right, hw, mul_zero] at key
  have hb' : det3 (a - v) (c - v) w = -det3 (c - v) (a - v) w := det3_swap _ _ _
  rw [hb'] at key
  rw [inner_sub_right] at fa fb fc
  have p1 : det3 (b - v) (c - v) w * (⟪F, a⟫ - ⟪F, v⟫) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha.le fa
  have p2 : det3 (c - v) (a - v) w * (⟪F, b⟫ - ⟪F, v⟫) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb.le fb
  have p3 : det3 (a - v) (b - v) w * (⟪F, c⟫ - ⟪F, v⟫) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc.le fc
  have q1 : det3 (b - v) (c - v) w * (⟪F, a⟫ - ⟪F, v⟫) = 0 := by linarith
  have q2 : det3 (c - v) (a - v) w * (⟪F, b⟫ - ⟪F, v⟫) = 0 := by linarith
  have e1 : ⟪F, a - v⟫ = 0 := by
    rw [inner_sub_right]; exact (mul_eq_zero.mp q1).resolve_left ha.ne'
  have e2 : ⟪F, b - v⟫ = 0 := by
    rw [inner_sub_right]; exact (mul_eq_zero.mp q2).resolve_left hb.ne'
  have h := det3_smul_eq (a - v) (b - v) w F
  rw [e1, e2, hw, zero_smul, zero_smul, zero_smul, add_zero, add_zero] at h
  exact (smul_eq_zero.mp h).resolve_left hc.ne'

/-- **A force at a corner lies in its normal cone.** At a convex corner `v`
with neighbours `y₀` (before) and `y₁` (after) in the projection along `w`
(`0 < det3 (y₁ - v) (y₀ - v) w`), a force `F ⊥ w` with `⟪F, y - v⟫ ≤ 0` at
the two test points is a nonnegative combination of the outward edge normals
`w × (y₀ - v)` and `(y₁ - v) × w`. -/
theorem force_mem_cone {v y₀ y₁ w F : ℝ³} (hD : 0 < det3 (y₁ - v) (y₀ - v) w)
    (hw : ⟪F, w⟫ = 0) (f1 : ⟪F, y₁ - v⟫ ≤ 0) (f0 : ⟪F, y₀ - v⟫ ≤ 0) :
    ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ F = s • cross w (y₀ - v) + t • cross (y₁ - v) w := by
  set D := det3 (y₁ - v) (y₀ - v) w
  have h := det3_smul_eq (y₁ - v) (y₀ - v) w F
  rw [hw, zero_smul, add_zero] at h
  refine ⟨-⟪F, y₁ - v⟫ / D, -⟪F, y₀ - v⟫ / D, div_nonneg (by linarith) hD.le,
    div_nonneg (by linarith) hD.le, ?_⟩
  have hc1 : cross (y₀ - v) w = -cross w (y₀ - v) := by
    ext i; fin_cases i <;> simp [cross] <;> ring
  have hc2 : cross w (y₁ - v) = -cross (y₁ - v) w := by
    ext i; fin_cases i <;> simp [cross] <;> ring
  rw [hc1, hc2] at h
  apply smul_right_injective ℝ³ hD.ne'
  simp only [smul_add, smul_smul]
  rw [h, mul_div_cancel₀ _ hD.ne', mul_div_cancel₀ _ hD.ne']
  simp only [smul_neg, neg_smul, neg_neg]

/-- **Lemma 7.1 at a view, frame-free.** If every force system at the view `w`
(see the module docstring) vanishes, `V` is Rupert. -/
theorem isRupert_of_no_forces (V : Finset ℝ³) (hsol : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty)
    (w : ℝ³) (hw : w ≠ 0)
    (h : ∀ F : ℝ³ → ℝ³, (∀ v ∈ V, ⟪F v, w⟫ = 0) → (∀ v ∈ V, ∀ y ∈ V, ⟪F v, y - v⟫ ≤ 0) →
      ∑ v ∈ V, F v = 0 → ∑ v ∈ V, ⟪v, w⟫ • F v = 0 → ∑ v ∈ V, ⟪cross v (F v), w⟫ = 0 →
      ∀ v ∈ V, F v = 0) :
    IsRupert V := by
  classical
  obtain ⟨R, hR, r, hr, hRw⟩ := exists_rotation_to_ez_pos w hw
  set g := so3Isometry hR
  by_contra hnot
  have hno : ∀ ω τ : ℝ³, ¬ FirstOrderInward (V.image R.toEuclideanLin) ω τ := fun ω τ hfo =>
    hnot (isRupert_of_firstOrderInward_image V R hR ω τ hfo)
  obtain ⟨f, hfN, ⟨v₀, hv₀, hf₀⟩, hE1, hE2, hE3⟩ :=
    exists_forces_of_not_firstOrderInward (V.image R.toEuclideanLin)
      (interior_proj_convexHull_nonempty V hR hsol) hno
  -- pull the forces back to the original frame
  set F : ℝ³ → ℝ³ := fun v => g.symm (liftH (f (R.toEuclideanLin v))) with hF
  have hgF : ∀ v, g (F v) = liftH (f (R.toEuclideanLin v)) := fun v => g.apply_symm_apply _
  have hinj : Set.InjOn R.toEuclideanLin (V : Set ℝ³) := fun a _ b _ h => g.injective h
  have inner_F : ∀ v x, ⟪F v, x⟫ = ⟪f (R.toEuclideanLin v), proj_xy (R.toEuclideanLin x)⟫ := by
    intro v x
    rw [← g.inner_map_map, hgF, so3Isometry_apply, inner_liftH]
  have inner_w : ∀ x, ⟪x, w⟫ = r * (g x) 2 := by
    intro x
    rw [← g.inner_map_map, so3Isometry_apply hR w, hRw, real_inner_smul_right, inner_ez]
  have liftH_sum : ∀ (s : Finset ℝ³) (c : ℝ³ → ℝ),
      ∑ x ∈ s, c x • liftH (f x) = liftH (∑ x ∈ s, c x • f x) := by
    intro s c; ext i; fin_cases i <;> simp [liftH, Finset.sum_apply]
  have hFw : ∀ v ∈ V, ⟪F v, w⟫ = 0 := by
    intro v _; rw [inner_w, hgF]; simp [liftH]
  have hFn : ∀ v ∈ V, ∀ y ∈ V, ⟪F v, y - v⟫ ≤ 0 := by
    intro v hv y hy
    rw [inner_F, map_sub, proj_xy_sub']
    exact hfN _ (mem_image_of_mem _ hv) _ ⟨R.toEuclideanLin y,
      subset_convexHull ℝ _ (by simp; exact ⟨y, hy, rfl⟩), rfl⟩
  have hF1 : ∑ v ∈ V, F v = 0 := by
    apply g.injective
    have e : g (∑ v ∈ V, F v) = ∑ x ∈ V.image R.toEuclideanLin, (1 : ℝ) • liftH (f x) := by
      rw [map_sum, sum_image (fun a ha b hb e => hinj ha hb e)]
      exact sum_congr rfl fun v _ => by rw [hgF, one_smul]
    rw [e, liftH_sum]; simp_rw [one_smul]; rw [hE1, map_zero]; ext i; fin_cases i <;> simp [liftH]
  have hF2 : ∑ v ∈ V, ⟪v, w⟫ • F v = 0 := by
    apply g.injective
    have e : g (∑ v ∈ V, ⟪v, w⟫ • F v) = r • ∑ x ∈ V.image R.toEuclideanLin, x 2 • liftH (f x) := by
      rw [map_sum, sum_image (fun a ha b hb e => hinj ha hb e), smul_sum]
      exact sum_congr rfl fun v _ => by
        rw [map_smul, hgF, inner_w, so3Isometry_apply, smul_smul]
    rw [e, liftH_sum, hE2, map_zero]
    ext i; fin_cases i <;> simp [liftH]
  have hF3 : ∑ v ∈ V, ⟪cross v (F v), w⟫ = 0 := by
    have e : ∀ v, ⟪cross v (F v), w⟫ = r * cross2 (proj_xy (R.toEuclideanLin v))
        (f (R.toEuclideanLin v)) := by
      intro v
      rw [inner_w, so3Isometry_apply, cross_toEuclideanLin hR, ← so3Isometry_apply hR (F v), hgF,
        ← inner_ez, inner_cross_ez, proj_liftH]
    simp_rw [e]
    rw [← mul_sum, ← sum_image (f := fun x => cross2 (proj_xy x) (f x))
      (fun a ha b hb e => hinj ha hb e), hE3, mul_zero]
  have hvanish := h F hFw hFn hF1 hF2 hF3
  obtain ⟨v, hv, rfl⟩ := mem_image.mp hv₀
  apply hf₀
  have h2 : liftH (f (R.toEuclideanLin v)) = 0 := by rw [← hgF, hvanish v hv, map_zero]
  have h20 := congrArg (fun z : ℝ³ => z 0) h2
  have h21 := congrArg (fun z : ℝ³ => z 1) h2
  simp [liftH] at h20 h21
  ext i; fin_cases i
  · simpa using h20
  · simpa using h21

end Minimality

end
