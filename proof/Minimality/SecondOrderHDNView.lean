module

public import Minimality.SecondOrderHDN
public import Minimality.PolygonHalfPlanes
public import Minimality.LimitRim

@[expose] public section

/-!
# Theorem H2 with a rim, and at a general view (plan specpos A3b)

`isRupert_of_levelHDN_rim`: `isRupert_of_levelHDN` with the shadow given as a strictly convex ccw rim
`x : ZMod k → V` (half-planes from `halfPlanes_of_ccwPolygon`) and every projected point in the rim's hull.
`isRupert_of_levelHDN_view`: the same at a view `u ≠ 0`, with `det3 · · u` in place of `cross2`, depths `⟪v, u⟫`,
and an axis `w ⊥ u` (rotate `u` to `e_z`).
-/
namespace Minimality
open scoped RealInnerProductSpace

/-- Outward edge normal of the rim polygon `c` at edge `e` (from `c e` to `c (e+1)`). -/
noncomputable def levelHDNv_n {k : ℕ} (c : ZMod k → ℝ²) (e : ZMod k) : ℝ² := -rot90 (c (e + 1) - c e)
/-- Edge offset. -/
noncomputable def levelHDNv_h {k : ℕ} (c : ZMod k → ℝ²) (e : ZMod k) : ℝ := ⟪levelHDNv_n c e, c e⟫

/-- Theorem H2 at the view `e_z`, with the shadow given as a strictly convex ccw rim `x` of points of `V`
(whose projection contains the projection of every point of `V`). -/
theorem isRupert_of_levelHDN_rim (V : Finset ℝ³) {k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : ZMod k → ℝ³)
    (hxV : ∀ i, x i ∈ V)
    (hccw : ∀ i j, j ≠ i → j ≠ i + 1 →
      0 < cross2 (proj_xy (x (i + 1)) - proj_xy (x i)) (proj_xy (x j) - proj_xy (x i)))
    (hhull : ∀ v ∈ V, proj_xy v ∈ convexHull ℝ (Set.range fun i => proj_xy (x i)))
    (i j : ZMod k) (hlev : (x i) 2 = (x j) 2)
    (w : ℝ²) (hax : cross2 (proj_xy (x i) - proj_xy (x j)) w ≠ 0)
    (hsepP : ∀ e, ⟪levelHDNv_n (fun t => proj_xy (x t)) e, proj_xy (x i)⟫ = levelHDNv_h (fun t => proj_xy (x t)) e →
      ⟪levelHDNv_n (fun t => proj_xy (x t)) e, proj_xy (x j)⟫ < levelHDNv_h (fun t => proj_xy (x t)) e)
    (hsepM : ∀ e, ⟪levelHDNv_n (fun t => proj_xy (x t)) e, proj_xy (x j)⟫ = levelHDNv_h (fun t => proj_xy (x t)) e →
      ⟪levelHDNv_n (fun t => proj_xy (x t)) e, proj_xy (x i)⟫ < levelHDNv_h (fun t => proj_xy (x t)) e)
    (hdrift : ∀ v ∈ V, v ≠ x i → v ≠ x j → ∀ e,
      ⟪levelHDNv_n (fun t => proj_xy (x t)) e, proj_xy v⟫ = levelHDNv_h (fun t => proj_xy (x t)) e →
      (v 2 - (x i) 2) * cross2 (levelHDNv_n (fun t => proj_xy (x t)) e) w < 0) :
    IsRupert V := by
  classical
  set c : ZMod k → ℝ² := fun t => proj_xy (x t) with hc
  obtain ⟨h1, h2⟩ := halfPlanes_of_ccwPolygon c hk hccw
  have hsub : convexHull ℝ (Set.range c) ⊆ proj_xy '' convexHull ℝ (V : Set ℝ³) := by
    have : Set.range c = proj_xy '' Set.range x := by
      rw [← Set.range_comp]; rfl
    rw [this, show (proj_xy : ℝ³ → ℝ²) = projL from rfl, ← LinearMap.image_convexHull]
    refine Set.image_mono (convexHull_mono ?_)
    rintro _ ⟨t, rfl⟩; exact hxV t
  exact isRupert_of_levelHDN V (levelHDNv_n c) (levelHDNv_h c) (fun y hy => hsub (h1 hy))
    (fun v hv e => h2 _ (hhull v hv) e) (x i) (x j) (hxV i) (hxV j) hlev w hax hsepP hsepM hdrift


lemma levelHDNv_inner_sub {k : ℕ} (c : ZMod k → ℝ²) (e : ZMod k) (y : ℝ²) :
    ⟪levelHDNv_n c e, y⟫ - levelHDNv_h c e = -cross2 (c (e + 1) - c e) (y - c e) := by
  rw [levelHDNv_h, levelHDNv_n]; exact poly_inner _ _ _

lemma levelHDNv_cross2_n {k : ℕ} (c : ZMod k → ℝ²) (e : ZMod k) (w : ℝ²) :
    cross2 (levelHDNv_n c e) w = ⟪c (e + 1) - c e, w⟫ := by
  simp [levelHDNv_n, rot90, cross2, PiLp.inner_apply, Fin.sum_univ_two]; ring

/-- Theorem H2 at a general view `u`: all hypotheses in terms of `u`-depths `⟪·, u⟫`, triple products
`det3 · · u` and a tilt axis `w ⟂ u`. -/
theorem isRupert_of_levelHDN_view (V : Finset ℝ³) {k : ℕ} [NeZero k] (hk : 3 ≤ k) (u : ℝ³) (hu : u ≠ 0)
    (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hccw : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (x (i + 1) - x i) (x j - x i) u)
    (hleft : ∀ v ∈ V, ∀ e, 0 ≤ det3 (x (e + 1) - x e) (v - x e) u)
    (i j : ZMod k) (hlev : ⟪x i, u⟫ = ⟪x j, u⟫)
    (w : ℝ³) (hwu : ⟪w, u⟫ = 0) (hax : det3 (x i - x j) w u ≠ 0)
    (hsepP : ∀ e, det3 (x (e + 1) - x e) (x i - x e) u = 0 → 0 < det3 (x (e + 1) - x e) (x j - x e) u)
    (hsepM : ∀ e, det3 (x (e + 1) - x e) (x j - x e) u = 0 → 0 < det3 (x (e + 1) - x e) (x i - x e) u)
    (hdrift : ∀ v ∈ V, v ≠ x i → v ≠ x j → ∀ e, det3 (x (e + 1) - x e) (v - x e) u = 0 →
      (⟪v, u⟫ - ⟪x i, u⟫) * ⟪x (e + 1) - x e, w⟫ < 0) :
    IsRupert V := by
  classical
  obtain ⟨R, hR, r, hr, hRu⟩ := exists_rotation_to_ez_pos u hu
  apply isRupert_of_isRupert_image_rotation R hR V
  have hz : ∀ a, r * (R.toEuclideanLin a) 2 = ⟪a, u⟫ := by
    intro a
    have := inner_toEuclideanLin_SO3 hR a u
    rw [hRu, real_inner_smul_right, inner_ez, ← this] at *
  have hcr : ∀ a b y : ℝ³, r * cross2 (proj_xy (R.toEuclideanLin a) - proj_xy (R.toEuclideanLin b))
      (proj_xy (R.toEuclideanLin y) - proj_xy (R.toEuclideanLin b)) = det3 (a - b) (y - b) u := by
    intro a b y
    rw [proj_rot_sub, proj_rot_sub]; exact cross2_proj_rot hR hRu _ _
  have hpos : ∀ a b y : ℝ³, 0 < det3 (a - b) (y - b) u →
      0 < cross2 (proj_xy (R.toEuclideanLin a) - proj_xy (R.toEuclideanLin b))
        (proj_xy (R.toEuclideanLin y) - proj_xy (R.toEuclideanLin b)) := fun a b y h => by
    rw [← hcr] at h; exact pos_of_mul_pos_right h hr.le
  have hnn : ∀ a b y : ℝ³, 0 ≤ det3 (a - b) (y - b) u →
      0 ≤ cross2 (proj_xy (R.toEuclideanLin a) - proj_xy (R.toEuclideanLin b))
        (proj_xy (R.toEuclideanLin y) - proj_xy (R.toEuclideanLin b)) := fun a b y h => by
    rw [← hcr] at h; exact nonneg_of_mul_nonneg_right h hr
  have hzero : ∀ a b y : ℝ³, det3 (a - b) (y - b) u = 0 →
      cross2 (proj_xy (R.toEuclideanLin a) - proj_xy (R.toEuclideanLin b))
        (proj_xy (R.toEuclideanLin y) - proj_xy (R.toEuclideanLin b)) = 0 := fun a b y h => by
    rw [← hcr] at h; exact (mul_eq_zero.1 h).resolve_left hr.ne'
  have hzero' : ∀ a b y : ℝ³, cross2 (proj_xy (R.toEuclideanLin a) - proj_xy (R.toEuclideanLin b))
        (proj_xy (R.toEuclideanLin y) - proj_xy (R.toEuclideanLin b)) = 0 → det3 (a - b) (y - b) u = 0 :=
    fun a b y h => by rw [← hcr, h, mul_zero]
  set c : ZMod k → ℝ² := fun t => proj_xy (R.toEuclideanLin (x t)) with hc
  have hccw' : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < cross2 (c (i + 1) - c i) (c j - c i) :=
    fun i j h1 h2 => hpos _ _ _ (hccw i j h1 h2)
  refine isRupert_of_levelHDN_rim (V.image R.toEuclideanLin) hk (fun t => R.toEuclideanLin (x t))
    (fun t => Finset.mem_image.2 ⟨_, hxV t, rfl⟩) hccw' ?_ i j ?_ (proj_xy (R.toEuclideanLin w)) ?_ ?_ ?_ ?_
  · intro v' hv'
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hv'
    exact (show IsCcwPolygon c from ⟨hk, hccw'⟩).mem_convexHull_of_left fun e => hnn _ _ _ (hleft v hv e)
  · have := hz (x i); have := hz (x j); rw [hlev] at *
    exact mul_left_cancel₀ hr.ne' (by linarith)
  · rw [proj_rot_sub]
    intro h; apply hax
    rw [← cross2_proj_rot hR hRu, h, mul_zero]
  · intro e he
    have h1 := levelHDNv_inner_sub c e (c i)
    have h2 := levelHDNv_inner_sub c e (c j)
    have := hsepP e (hzero' _ _ _ (by rw [he] at h1; linarith [h1]))
    have := hpos _ _ _ this
    linarith
  · intro e he
    have h1 := levelHDNv_inner_sub c e (c i)
    have h2 := levelHDNv_inner_sub c e (c j)
    have := hsepM e (hzero' _ _ _ (by rw [he] at h2; linarith [h2]))
    have := hpos _ _ _ this
    linarith
  · intro v' hv' a b e he
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hv'
    have h1 := levelHDNv_inner_sub c e (proj_xy (R.toEuclideanLin v))
    have h0 := hzero' _ _ _ (by rw [he] at h1; linarith [h1] : cross2 (c (e + 1) - c e) _ = 0)
    have hd := hdrift v hv (fun h => a (by rw [h])) (fun h => b (by rw [h])) e h0
    have hin : ⟪c (e + 1) - c e, proj_xy (R.toEuclideanLin w)⟫ = ⟪x (e + 1) - x e, w⟫ := by
      rw [hc]; simp only []
      rw [proj_rot_sub, real_inner_comm, ← inner_eq_proj_of_perp hR hr.ne' hRu hwu, real_inner_comm]
    show ((R.toEuclideanLin v) 2 - (R.toEuclideanLin (x i)) 2) *
      cross2 (levelHDNv_n c e) (proj_xy (R.toEuclideanLin w)) < 0
    rw [levelHDNv_cross2_n, hin]
    have e1 := hz v; have e2 := hz (x i)
    have hD : ⟪v, u⟫ - ⟪x i, u⟫ = r * ((R.toEuclideanLin v) 2 - (R.toEuclideanLin (x i)) 2) := by
      linarith
    rw [hD, mul_assoc] at hd
    by_contra hcon
    exact absurd hd (not_lt.2 (mul_nonneg hr.le (not_lt.1 hcon)))

end Minimality
