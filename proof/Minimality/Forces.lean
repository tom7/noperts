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
