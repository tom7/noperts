module

public import Minimality.SecondOrderSpin
public import Minimality.SecondOrderHDNView

@[expose] public section

/-!
# Theorem CE′: a corner–edge level double normal is removed by tilt plus spin (plan specpos A5)

At the view `e_z`, `vp ∈ V` is a shadow corner, and `y = (1-t) a + t b` lies on the shadow edge `e0` at the
same depth as `vp`, with the chord `D = P y - P vp` parallel to the normal of `e0`.  The explicit motion
`ω = σ (D, 0) + β (b - a)`, `τ = -ω × vp` has screen velocity `vel(x) = P (ω × (x - vp))`, and
`⟪n e, vel x⟫ = cornerEdge_c (n e) D (b - a) vp x σ β` (closed form).  The four chord pairs `(vp, ·)`, `(a, e0)`,
`(b, e0)` have margin 0 for all `σ, β`; spin is `ω 2 = β (b 2 - a 2) ≠ 0`.  So `isRupert_of_secondOrder_spin`
(A1) applies to any `σ, β` that is weakly inward at the remaining tight pairs.
-/
namespace Minimality
open scoped RealInnerProductSpace

/-- First-order margin `⟪m, vel x⟫` of the motion `ω = σ (D, 0) + β d`, `τ = -ω × vp`, in closed form. -/
def cornerEdge_c (m D : ℝ²) (d vp x : ℝ³) (σ β : ℝ) : ℝ :=
  σ * (x 2 - vp 2) * cross2 m D +
    β * (m 1 * d 2 * (x 0 - vp 0) - m 0 * d 2 * (x 1 - vp 1) + (m 0 * d 1 - m 1 * d 0) * (x 2 - vp 2))

/-- The motion of CE′. -/
noncomputable def cornerEdge_omega (D : ℝ²) (d : ℝ³) (σ β : ℝ) : ℝ³ :=
  !₂[σ * D 0 + β * d 0, σ * D 1 + β * d 1, β * d 2]

theorem cornerEdge_key (m D : ℝ²) (d vp x : ℝ³) (σ β : ℝ) :
    ⟪m, screenVel (cornerEdge_omega D d σ β) (-((crossMatrix (cornerEdge_omega D d σ β)).toEuclideanLin vp)) x⟫
      = cornerEdge_c m D d vp x σ β := by
  simp [screenVel, cornerEdge_omega, cornerEdge_c, proj_xy, crossMatrix, cross2, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two, PiLp.inner_apply]
  ring

/-- The margin at the chord ends of the edge (`a`, `b`) vanishes. -/
theorem cornerEdge_exempt (m D : ℝ²) (a b y vp : ℝ³) (t σ β : ℝ) (hy : y = (1 - t) • a + t • b)
    (hD : D = proj_xy y - proj_xy vp) (hlev : y 2 = vp 2) (hnorm : cross2 m D = 0) :
    cornerEdge_c m D (b - a) vp a σ β = 0 ∧ cornerEdge_c m D (b - a) vp b σ β = 0 := by
  have h0 : y 0 = (1 - t) * a 0 + t * b 0 := by rw [hy]; simp
  have h1 : y 1 = (1 - t) * a 1 + t * b 1 := by rw [hy]; simp
  have h2 : y 2 = (1 - t) * a 2 + t * b 2 := by rw [hy]; simp
  have hD0 : D 0 = y 0 - vp 0 := by rw [hD]; simp [proj_xy]
  have hD1 : D 1 = y 1 - vp 1 := by rw [hD]; simp [proj_xy]
  have hn : m 0 * D 1 - m 1 * D 0 = 0 := hnorm
  rw [hD0, hD1] at hn
  constructor <;>
  · simp only [cornerEdge_c, PiLp.sub_apply, hnorm, mul_zero, zero_add]
    linear_combination (-β * m 1 * (b 2 - a 2)) * h0 + (β * m 0 * (b 2 - a 2)) * h1
      + (-β * (m 0 * (b 1 - a 1) - m 1 * (b 0 - a 0))) * h2
      + (-β * (b 2 - a 2)) * hn + (β * (m 0 * (b 1 - a 1) - m 1 * (b 0 - a 0))) * hlev

/-- Theorem CE′ (corner–edge level HDN, explicit tilt + spin motion) at the view `e_z`. -/
theorem isRupert_of_cornerEdgeHDN (V : Finset ℝ³) {ι : Type*} [Fintype ι] (n : ι → ℝ²) (h : ι → ℝ)
    (hpoly : {y : ℝ² | ∀ e, ⟪n e, y⟫ < h e} ⊆ proj_xy '' convexHull ℝ (V : Set ℝ³))
    (hS : ∀ y ∈ proj_xy '' convexHull ℝ (V : Set ℝ³), ∀ e, ⟪n e, y⟫ ≤ h e)
    (o : ℝ²) (ho : ∀ e, ⟪n e, o⟫ < h e)
    (vp a b y : ℝ³) (e0 : ι) (t : ℝ) (D : ℝ²)
    (hy : y = (1 - t) • a + t • b) (hD : D = proj_xy y - proj_xy vp)
    (hlev : y 2 = vp 2) (hnorm : cross2 (n e0) D = 0) (hab : a 2 ≠ b 2)
    (σ β : ℝ) (hβ : β ≠ 0)
    (hweak : ∀ v ∈ V, ∀ e, ⟪n e, proj_xy v⟫ = h e →
      v = vp ∨ (e = e0 ∧ (v = a ∨ v = b)) ∨ cornerEdge_c (n e) D (b - a) vp v σ β ≤ 0) :
    IsRupert V := by
  have hspin : (cornerEdge_omega D (b - a) σ β) 2 ≠ 0 := by
    simp only [cornerEdge_omega, PiLp.sub_apply]
    exact mul_ne_zero hβ (sub_ne_zero.2 (Ne.symm hab))
  refine isRupert_of_secondOrder_spin V n h hpoly hS o ho (cornerEdge_omega D (b - a) σ β)
    (-((crossMatrix (cornerEdge_omega D (b - a) σ β)).toEuclideanLin vp)) hspin ?_
  intro v hv e
  rcases lt_or_eq_of_le (hS _ ⟨v, subset_convexHull ℝ _ hv, rfl⟩ e) with h1 | h1
  · exact Or.inl h1
  · right
    refine ⟨h1, ?_⟩
    rw [cornerEdge_key]
    rcases hweak v hv e h1 with hv' | ⟨he, hv' | hv'⟩ | hw
    · rw [hv']; simp [cornerEdge_c]
    · rw [hv', he]; exact (cornerEdge_exempt _ D a b y vp t σ β hy hD hlev hnorm).1.le
    · rw [hv', he]; exact (cornerEdge_exempt _ D a b y vp t σ β hy hD hlev hnorm).2.le
    · exact hw

/-- Rim form of CE′: the shadow is a strictly convex ccw rim `x`, `vp = x i`, and the edge `e0` runs from
`a = x e0` to `b = x (e0+1)`. -/
theorem isRupert_of_cornerEdgeHDN_rim (V : Finset ℝ³) {k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : ZMod k → ℝ³)
    (hxV : ∀ i, x i ∈ V)
    (hccw : ∀ i j, j ≠ i → j ≠ i + 1 →
      0 < cross2 (proj_xy (x (i + 1)) - proj_xy (x i)) (proj_xy (x j) - proj_xy (x i)))
    (hhull : ∀ v ∈ V, proj_xy v ∈ convexHull ℝ (Set.range fun i => proj_xy (x i)))
    (o : ℝ²) (ho : ∀ e, ⟪levelHDNv_n (fun s => proj_xy (x s)) e, o⟫ < levelHDNv_h (fun s => proj_xy (x s)) e)
    (i e0 : ZMod k) (t : ℝ) (D : ℝ²)
    (hD : D = proj_xy ((1 - t) • x e0 + t • x (e0 + 1)) - proj_xy (x i))
    (hlev : ((1 - t) • x e0 + t • x (e0 + 1)) 2 = (x i) 2)
    (hnorm : cross2 (levelHDNv_n (fun s => proj_xy (x s)) e0) D = 0) (hab : x e0 2 ≠ x (e0 + 1) 2)
    (σ β : ℝ) (hβ : β ≠ 0)
    (hweak : ∀ v ∈ V, ∀ e,
      ⟪levelHDNv_n (fun s => proj_xy (x s)) e, proj_xy v⟫ = levelHDNv_h (fun s => proj_xy (x s)) e →
      v = x i ∨ (e = e0 ∧ (v = x e0 ∨ v = x (e0 + 1))) ∨
        cornerEdge_c (levelHDNv_n (fun s => proj_xy (x s)) e) D (x (e0 + 1) - x e0) (x i) v σ β ≤ 0) :
    IsRupert V := by
  classical
  set c : ZMod k → ℝ² := fun s => proj_xy (x s) with hc
  obtain ⟨h1, h2⟩ := halfPlanes_of_ccwPolygon c hk hccw
  have hsub : convexHull ℝ (Set.range c) ⊆ proj_xy '' convexHull ℝ (V : Set ℝ³) := by
    have : Set.range c = proj_xy '' Set.range x := by
      rw [← Set.range_comp]; rfl
    rw [this, show (proj_xy : ℝ³ → ℝ²) = projL from rfl, ← LinearMap.image_convexHull]
    refine Set.image_mono (convexHull_mono ?_)
    rintro _ ⟨s, rfl⟩; exact hxV s
  have hS : ∀ y ∈ proj_xy '' convexHull ℝ (V : Set ℝ³), ∀ e, ⟪levelHDNv_n c e, y⟫ ≤ levelHDNv_h c e := by
    rintro _ ⟨z, hz, rfl⟩ e
    refine h2 _ ?_ e
    have : proj_xy '' convexHull ℝ (V : Set ℝ³) ⊆ convexHull ℝ (Set.range c) := by
      rw [show (proj_xy : ℝ³ → ℝ²) = projL from rfl, LinearMap.image_convexHull]
      refine convexHull_min ?_ (convex_convexHull ℝ _)
      rintro _ ⟨v, hv, rfl⟩
      exact hhull v hv
    exact this ⟨z, hz, rfl⟩
  exact isRupert_of_cornerEdgeHDN V (levelHDNv_n c) (levelHDNv_h c) (fun y hy => hsub (h1 hy)) hS o ho
    (x i) (x e0) (x (e0 + 1)) _ e0 t D rfl hD hlev hnorm hab σ β hβ hweak

open Filter Topology in
/-- Corollary CE (strict, `(σ, β)`-free form).  `drift`: every tight pair off `vp` and off `e0` drifts strictly
inward under the pure tilt `σ (D, 0)`; `side`: the spin margins `cornerEdge_c (n e0) D (b-a) vp v 0 1` over the
points `v ≠ vp` tight on `e0` do not change sign.  Then a small `β` of the allowed sign works. -/
theorem isRupert_of_cornerEdgeHDN_strict (V : Finset ℝ³) {ι : Type*} [Fintype ι] (n : ι → ℝ²) (h : ι → ℝ)
    (hpoly : {y : ℝ² | ∀ e, ⟪n e, y⟫ < h e} ⊆ proj_xy '' convexHull ℝ (V : Set ℝ³))
    (hS : ∀ y ∈ proj_xy '' convexHull ℝ (V : Set ℝ³), ∀ e, ⟪n e, y⟫ ≤ h e)
    (o : ℝ²) (ho : ∀ e, ⟪n e, o⟫ < h e)
    (vp a b y : ℝ³) (e0 : ι) (t : ℝ) (D : ℝ²)
    (hy : y = (1 - t) • a + t • b) (hD : D = proj_xy y - proj_xy vp)
    (hlev : y 2 = vp 2) (hnorm : cross2 (n e0) D = 0) (hab : a 2 ≠ b 2) (σ : ℝ)
    (hdrift : ∀ v ∈ V, v ≠ vp → ∀ e, e ≠ e0 → ⟪n e, proj_xy v⟫ = h e →
      σ * (v 2 - vp 2) * cross2 (n e) D < 0)
    (hside : (∀ v ∈ V, v ≠ vp → ⟪n e0, proj_xy v⟫ = h e0 →
        0 ≤ cornerEdge_c (n e0) D (b - a) vp v 0 1) ∨
      (∀ v ∈ V, v ≠ vp → ⟪n e0, proj_xy v⟫ = h e0 → cornerEdge_c (n e0) D (b - a) vp v 0 1 ≤ 0)) :
    IsRupert V := by
  classical
  have lin : ∀ m v (β : ℝ), cornerEdge_c m D (b - a) vp v σ β =
      σ * (v 2 - vp 2) * cross2 m D + β * cornerEdge_c m D (b - a) vp v 0 1 := by
    intro m v β; simp only [cornerEdge_c]; ring
  obtain ⟨s, hs, hsg⟩ : ∃ s : ℝ, s ≠ 0 ∧ ∀ v ∈ V, v ≠ vp → ⟪n e0, proj_xy v⟫ = h e0 →
      s * cornerEdge_c (n e0) D (b - a) vp v 0 1 ≤ 0 := by
    rcases hside with H | H
    · exact ⟨-1, by norm_num, fun v hv hne ht => by linarith [H v hv hne ht]⟩
    · exact ⟨1, by norm_num, fun v hv hne ht => by linarith [H v hv hne ht]⟩
  have hev : ∀ p : V × ι, ∀ᶠ δ in 𝓝[>] (0 : ℝ), ((p.1 : ℝ³) ≠ vp ∧ p.2 ≠ e0 ∧
      ⟪n p.2, proj_xy (p.1 : ℝ³)⟫ = h p.2) →
      σ * ((p.1 : ℝ³) 2 - vp 2) * cross2 (n p.2) D +
        (s * δ) * cornerEdge_c (n p.2) D (b - a) vp p.1 0 1 < 0 := by
    intro p
    by_cases hc : (p.1 : ℝ³) ≠ vp ∧ p.2 ≠ e0 ∧ ⟪n p.2, proj_xy (p.1 : ℝ³)⟫ = h p.2
    · have hA := hdrift p.1 p.1.2 hc.1 p.2 hc.2.1 hc.2.2
      have hcont : Continuous fun δ : ℝ => σ * ((p.1 : ℝ³) 2 - vp 2) * cross2 (n p.2) D +
          (s * δ) * cornerEdge_c (n p.2) D (b - a) vp p.1 0 1 := by fun_prop
      have := (hcont.tendsto 0).eventually (gt_mem_nhds (by simpa using hA))
      exact (this.filter_mono nhdsWithin_le_nhds).mono fun δ hδ _ => hδ
    · exact Eventually.of_forall fun δ hh => absurd hh hc
  obtain ⟨δ, hpos, hδ⟩ := ((eventually_all.2 hev).and self_mem_nhdsWithin).exists
  have hδ0 : (0 : ℝ) < δ := hδ
  refine isRupert_of_cornerEdgeHDN V n h hpoly hS o ho vp a b y e0 t D hy hD hlev hnorm hab σ (s * δ)
    (mul_ne_zero hs hδ0.ne') ?_
  intro v hv e ht
  by_cases hvp : v = vp
  · exact Or.inl hvp
  right; right
  rw [lin]
  by_cases he : e = e0
  · subst he
    rw [hnorm, mul_zero, zero_add,
      show s * δ * cornerEdge_c (n e) D (b - a) vp v 0 1 = δ * (s * cornerEdge_c (n e) D (b - a) vp v 0 1) by ring]
    exact mul_nonpos_of_nonneg_of_nonpos hδ0.le (hsg v hv hvp ht)
  · exact (hpos (⟨v, hv⟩, e) ⟨hvp, he, ht⟩).le

end Minimality
