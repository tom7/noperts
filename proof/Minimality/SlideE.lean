module

public import Minimality.SlideDS

@[expose] public section

/-!
# Slides with the persistent double normal only (`FEWER-FACES-PROOFS.md` §22.3, §22.6 (a))

`isRupert_of_slideG` (Lemma C) excludes every *bad direction* normal to the plane of the face
circle, with feet on the two edges (`NoBadNormalR`).  Lemma 22.3 needs less: along the circle a
horizontal double normal of the slid rim along a direction `l` normal to the circle's plane is
a double normal of the rim *in space*: a point `Y'` of one edge and `Y` of another with
`Y' − Y ∥ l`, `Y'` maximal and `Y` minimal for `⟪Y' − Y, ·⟫` over the rim.  That condition does
not depend on the view on the circle (the screen inner product of a horizontal vector is the
inner product in space), so it holds along the whole circle or nowhere.  This file states the
slide with exactly that exclusion (`NoPersistHDN`).

* `exists_pairDir_of_hdnE`: Lemma 7.4 by edges with extremal feet.
* `NoPersistHDN x u₀ e`: no double normal of the cycle in space perpendicular to `u₀` and `e`.
* `isRupert_of_slideP`: the slide along `u₀ + t e` (`t → 0⁺`) from the tests at `u₀`
  (`SlideTest`, a vertex may poke out), distinct depths at `u₀`, a strictly unimodal rim or a
  depth-separated pair at `u₀`, and `NoPersistHDN`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- **Lemma 7.4 by edges, with extremal feet.**  As `exists_pairDir_of_hdn'`; moreover the
feet `Y ∈ [x i, x (i+1)]`, `Y' ∈ [x j, x (j+1)]` with `Y' − Y = r l` (`r ≠ 0`) are extremal:
`Y'` maximizes and `Y` minimizes `⟪Y' − Y, ·⟫` over the vertices of the cycle. -/
theorem exists_pairDir_of_hdnE {k : ℕ} [NeZero k] (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : R ∈ SO3)
    (x : ZMod k → ℝ³)
    (h : HasHorizontalDoubleNormal (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2)) :
    ∃ i j, ¬ EdgesApart (fun m => (R.toEuclideanLin (x m)) 2) i j ∧
      ∃ l ∈ pairDirs x i j, (R.toEuclideanLin l) 2 = 0 ∧
        ∃ Y ∈ segment ℝ (x i) (x (i + 1)), ∃ Y' ∈ segment ℝ (x j) (x (j + 1)), ∃ r : ℝ,
          r ≠ 0 ∧ Y' - Y = r • l ∧ ∀ m, ⟪Y' - Y, x m - Y'⟫ ≤ 0 ∧ ⟪Y - Y', x m - Y⟫ ≤ 0 := by
  set L := R.toEuclideanLin with hL
  obtain ⟨y, y', ⟨i, hy⟩, ⟨j, hy'⟩, hz, hne, hn1, hn2⟩ := h
  have hov : ¬ EdgesApart (fun m => (R.toEuclideanLin (x m)) 2) i j := by
    have h1 := between_of_segment hy
    have h2 := between_of_segment hy'
    rw [liftPt_two, liftPt_two] at h1 h2
    rw [← hz] at h2
    exact not_apart_of_between h1 h2
  refine ⟨i, j, hov, ?_⟩
  simp only [liftPt_proj_xy] at hy hy'
  have hseg : ∀ {a b w : ℝ³}, w ∈ segment ℝ (L a) (L b) → ∃ W ∈ segment ℝ a b, w = L W := by
    intro a b w hw
    obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hw
    exact ⟨α • a + β • b, ⟨α, β, hα, hβ, hαβ, rfl⟩, by simp [L, map_add, map_smul]⟩
  obtain ⟨Y, hY, rfl⟩ := hseg hy
  obtain ⟨Y', hY', rfl⟩ := hseg hy'
  have hhor : (L (Y' - Y)) 2 = 0 := by
    rw [map_sub, PiLp.sub_apply]; linarith
  have hmem : ∀ m, proj_xy (L (x m)) ∈
      convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i))) :=
    fun m => subset_convexHull ℝ _ ⟨m, rfl⟩
  have G : ∀ {A B : ℝ³}, (L (A - B)) 2 = 0 →
      proj_xy (L A) - proj_xy (L B) ∈ normalConeAt
        (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))) (proj_xy (L A)) →
      ∀ m, ⟪A - B, x m - A⟫ ≤ 0 := by
    intro A B hAB hn m
    have := hn _ (hmem m)
    rwa [← proj_xy_sub', ← proj_xy_sub', inner_proj_xy_of_horizontal (by rw [← map_sub]; exact hAB),
      ← map_sub, ← map_sub, hL, inner_toEuclideanLin_SO3 hR] at this
  have hhor' : (L (Y - Y')) 2 = 0 := by rw [← neg_sub, map_neg, PiLp.neg_apply, hhor, neg_zero]
  have GY := G hhor' hn2
  have GY' := G hhor hn1
  have hext : ∀ m, ⟪Y' - Y, x m - Y'⟫ ≤ 0 ∧ ⟪Y - Y', x m - Y⟫ ≤ 0 := fun m => ⟨GY' m, GY m⟩
  have hYs := hY
  have hY's := hY'
  obtain ⟨a, b, ha, hb, s, hYeq, hs⟩ := endpoint_cases hY (GY i) (GY (i + 1))
  obtain ⟨c, d, hc, hd, t, hY'eq, ht⟩ := endpoint_cases hY' (GY' j) (GY' (j + 1))
  have hfe : ∀ l : ℝ³, ∀ r : ℝ, r ≠ 0 → Y' - Y = r • l →
      ∃ Y₀ ∈ segment ℝ (x i) (x (i + 1)), ∃ Y₀' ∈ segment ℝ (x j) (x (j + 1)), ∃ r : ℝ,
        r ≠ 0 ∧ Y₀' - Y₀ = r • l ∧ ∀ m, ⟪Y₀' - Y₀, x m - Y₀'⟫ ≤ 0 ∧
          ⟪Y₀ - Y₀', x m - Y₀⟫ ≤ 0 :=
    fun l r hr hl => ⟨Y, hYs, Y', hY's, r, hr, hl, hext⟩
  subst hYeq hY'eq
  set h := c + t • (d - c) - (a + s • (b - a)) with hhdef
  have hh0 : h ≠ 0 := by
    intro h0; apply hne; rw [sub_eq_zero.mp h0]
  have ht' : ⟪h, d - c⟫ = 0 := by
    rw [hhdef, ← neg_sub, inner_neg_left, ht, neg_zero]
  have hrow : ∀ l : ℝ³, (L l) 2 = ⟪l, !₂[R 2 0, R 2 1, R 2 2]⟫ := fun l => by
    rw [hL, toEuclideanLin_two]; simp [PiLp.inner_apply, Fin.sum_univ_three]
  obtain ⟨σ₁, hσ₁⟩ := edge_diff ha hb
  obtain ⟨σ₂, hσ₂⟩ := edge_diff hc hd
  obtain ⟨n, hn, rfl⟩ : ∃ n, (n = j ∨ n = j + 1) ∧ c = x n := by
    rcases hc with rfl | rfl
    exacts [⟨j, Or.inl rfl, rfl⟩, ⟨j + 1, Or.inr rfl, rfl⟩]
  obtain ⟨m, hm, rfl⟩ : ∃ m, (m = i ∨ m = i + 1) ∧ a = x m := by
    rcases ha with rfl | rfl
    exacts [⟨i, Or.inl rfl, rfl⟩, ⟨i + 1, Or.inr rfl, rfl⟩]
  by_cases hcr : cross (b - x m) (d - x n) = 0
  · by_cases hba : b - x m = 0
    · have hp : h = perpTo (x n - x m) (d - x n) :=
        perpTo_eq t (by rw [hhdef, hba, smul_zero, add_zero]; abel) ht'
      by_cases hdc : d - x n = 0
      · rw [hdc, perpTo_zero_right] at hp
        rw [hp] at hh0
        exact ⟨x n - x m, mem_pairDirs_of x hm hn (Or.inr (Or.inr rfl)) hh0,
          by rw [← hp]; exact hhor, hfe _ 1 one_ne_zero (by rw [hp, one_smul])⟩
      · have hσ₂0 : σ₂ ≠ 0 := by rintro rfl; rw [zero_smul] at hσ₂; exact hdc hσ₂
        rw [hσ₂, perpTo_smul_right _ _ hσ₂0] at hp
        rw [hp] at hh0
        exact ⟨_, mem_pairDirs_of x hm hn (Or.inl rfl) hh0, by rw [← hp]; exact hhor,
          hfe _ 1 one_ne_zero (by rw [hp, one_smul])⟩
    · have hσ₁0 : σ₁ ≠ 0 := by rintro rfl; rw [zero_smul] at hσ₁; exact hba hσ₁
      obtain ⟨κ, hk⟩ : ∃ κ : ℝ, d - x n = κ • (b - x m) := ⟨_, eq_smul_of_cross_eq_zero hba hcr⟩
      have hp : h = perpTo (x n - x m) (b - x m) := perpTo_eq (t * κ - s)
        (by rw [hhdef, hk]; module) hs
      rw [hσ₁, perpTo_smul_right _ _ hσ₁0] at hp
      have hp' : -h = perpTo (x m - x n) (x (i + 1) - x i) := by
        rw [hp, ← perpTo_neg_left, neg_sub]
      refine ⟨-h, mem_pairDirs_of x hm hn (Or.inr (Or.inl hp')) (neg_ne_zero.mpr hh0), ?_,
        hfe _ (-1) (by norm_num) (by rw [neg_one_smul, neg_neg])⟩
      rw [map_neg, PiLp.neg_apply, hhor, neg_zero]
  · have hσ : σ₁ * σ₂ ≠ 0 := by
      intro h0; apply hcr; rw [hσ₁, hσ₂, cross_smul_smul, h0, zero_smul]
    have hcr' : cross (b - x m) (d - x n) =
        (σ₁ * σ₂) • cross (x (i + 1) - x i) (x (j + 1) - x j) := by
      rw [hσ₁, hσ₂, cross_smul_smul]
    have hcr0 : cross (x (i + 1) - x i) (x (j + 1) - x j) ≠ 0 := by
      intro h0; apply hcr; rw [hcr', h0, smul_zero]
    obtain ⟨κ, hκ⟩ := eq_smul_cross_of_perp hcr hs ht'
    have hκ0 : κ * (σ₁ * σ₂) ≠ 0 := by
      intro h0
      apply hh0
      rw [hκ, hcr', smul_smul, h0, zero_smul]
    refine ⟨cross (x (i + 1) - x i) (x (j + 1) - x j), cross_mem_pairDirs x i j hcr0, ?_,
      hfe _ _ hκ0 (by rw [hκ, hcr', smul_smul])⟩
    have h1 := inner_cross_eq_zero_of_perp hh0 hs ht' (by rw [← hrow]; exact hhor)
    rw [hcr', real_inner_smul_left] at h1
    rw [hrow]
    exact (mul_eq_zero.mp h1).resolve_left hσ

/-- **No persistent double normal along the circle of `u₀` and `e`**: no point `Y` of an edge
and `Y'` of an edge of the cycle with `Y' − Y ≠ 0` perpendicular to `u₀` and to `e` (normal to
the circle's plane) such that `Y'` maximizes and `Y` minimizes `⟪Y' − Y, ·⟫` over the cycle's
vertices.  Such a pair is a horizontal double normal at every view of the circle, and
conversely (`exists_pairDir_of_hdnE`) every horizontal double normal near `u₀` on the circle
that persists is one. -/
def NoPersistHDN {k : ℕ} (x : ZMod k → ℝ³) (u₀ e : ℝ³) : Prop :=
  ∀ i j : ZMod k, ∀ Y ∈ segment ℝ (x i) (x (i + 1)), ∀ Y' ∈ segment ℝ (x j) (x (j + 1)),
    Y' ≠ Y → ⟪Y' - Y, u₀⟫ = 0 → ⟪Y' - Y, e⟫ = 0 →
      ¬ ∀ m, ⟪Y' - Y, x m - Y'⟫ ≤ 0 ∧ ⟪Y - Y', x m - Y⟫ ≤ 0

/-- **The slide with the persistent double normal only** (Lemmas 22.3, 22.4, 22.6 (a)).  Along
the views `u₀ + t e` (`t → 0⁺`): the cycle's own tests and every other point's tests hold
strictly at `u₀` or vanish there with a positive derivative along `e` (`SlideTest`), the
middles `M` lie over edges for small `t`, the depths at `u₀` are distinct, and the rim is
strictly unimodal or has a depth-separated pair at `u₀`.  If no double normal of the cycle in
space is perpendicular to the circle's plane (`NoPersistHDN`), `V` is Rupert. -/
theorem isRupert_of_slideP (V M : Finset ℝ³) (u₀ e : ℝ³) (hu₀ : u₀ ≠ 0) {k : ℕ} [NeZero k]
    (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V) (hxM : ∀ i, x i ∉ M)
    (hk : 3 ≤ k) (ρ : ℝ) (hρ : ρ ≠ 0)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → SlideTest ρ (x (i + 1) - x i) (x j - x i) u₀ e)
    (hrest : ∀ y ∈ V, y ∉ M → (∀ j, y ≠ x j) → ∀ i,
      SlideTest ρ (x (i + 1) - x i) (y - x i) u₀ e)
    (hM : ∀ m ∈ M, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = x i + s • (x (i + 1) - x i) + δ • (u₀ + t • e))
    (hinj0 : Function.Injective (fun i => ⟪x i, u₀⟫))
    (hz : UniOrSep x u₀) (hbad : NoPersistHDN x u₀ e) : IsRupert V := by
  classical
  have hlin : ∀ l : ℝ³, ∀ t : ℝ, ⟪l, u₀ + t • e⟫ = ⟪l, u₀⟫ + t * ⟪l, e⟫ := by
    intro l t; rw [inner_add_right, real_inner_smul_right]
  have hev1 : ∀ l : ℝ³, ⟪l, u₀⟫ ≠ 0 ∨ ⟪l, e⟫ ≠ 0 →
      ∀ᶠ t in 𝓝[>] (0 : ℝ), ⟪l, u₀ + t • e⟫ ≠ 0 := by
    intro l h
    simp only [hlin]
    rcases h with h | h
    · by_cases he : ⟪l, e⟫ = 0
      · filter_upwards with t; rw [he, mul_zero, add_zero]; exact h
      · exact eventually_ne_affine he
    · exact eventually_ne_affine h
  -- every bad direction off the circle's normal is eventually not horizontal
  have hpair : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i j : ZMod k, ∀ l ∈ pairDirs x i j,
      (⟪l, u₀⟫ ≠ 0 ∨ ⟪l, e⟫ ≠ 0) → ⟪l, u₀ + t • e⟫ ≠ 0 := by
    refine eventually_all.mpr fun i => eventually_all.mpr fun j => ?_
    refine (eventually_all_finset _).mpr fun l _ => ?_
    by_cases hl : ⟪l, u₀⟫ ≠ 0 ∨ ⟪l, e⟫ ≠ 0
    · filter_upwards [hev1 l hl] with t ht _ using ht
    · filter_upwards with t h using absurd h hl
  have hne : ∀ᶠ t in 𝓝[>] (0 : ℝ), u₀ + t • e ≠ 0 := by
    have hc : Continuous fun t : ℝ => u₀ + t • e := by fun_prop
    exact (hc.continuousAt.eventually (isOpen_ne.mem_nhds
      (show u₀ + (0 : ℝ) • e ≠ 0 by simpa using hu₀))).filter_mono nhdsWithin_le_nhds
  have hinj : ∀ᶠ t in 𝓝[>] (0 : ℝ), Function.Injective (fun i => ⟪x i, u₀ + t • e⟫) := by
    have : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i j : ZMod k, i ≠ j → ⟪x i - x j, u₀ + t • e⟫ ≠ 0 := by
      refine eventually_all.mpr fun i => eventually_all.mpr fun j => ?_
      by_cases hij : i = j
      · filter_upwards with t h using absurd hij h
      · have h0 : ⟪x i - x j, u₀⟫ ≠ 0 := by
          rw [inner_sub_left, sub_ne_zero]; exact fun h => hij (hinj0 h)
        filter_upwards [hev1 _ (Or.inl h0)] with t ht _ using ht
    filter_upwards [this] with t ht i j hij
    by_contra hne'
    exact ht i j hne' (by rw [inner_sub_left]; exact sub_eq_zero.mpr hij)
  have h1 := eventually_forall_cycle fun i j hi hj => eventually_det3_slide (hcyc i j hi hj)
  have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ y ∈ V, ∀ i : ZMod k, y ∉ M → (∀ j, y ≠ x j) →
      0 < ρ * det3 (x (i + 1) - x i) (y - x i) (u₀ + t • e) := by
    refine (eventually_all_finset V).mpr fun y hy => eventually_all.mpr fun i => ?_
    by_cases hyM : y ∉ M
    · by_cases hyx : ∀ j, y ≠ x j
      · filter_upwards [eventually_det3_slide (hrest y hy hyM hyx i)] with t ht _ _ using ht
      · filter_upwards with t _ h using absurd h hyx
    · filter_upwards with t h using absurd h hyM
  have h3 := (eventually_all_finset M).mpr hM
  have h4 : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (Function.Injective (fun i => ⟪x i, u₀ + t • e⟫) →
          IsCyclicUnimodal (fun i => ⟪x i, u₀ + t • e⟫)) ∨
        ∃ a c : ZMod k, DepthSepAt x (u₀ + t • e) a c := by
    rcases hz with hz | ⟨a, c, hds⟩
    · filter_upwards [eventually_unimodal_of_strict x u₀ e hz] with t ht using Or.inl ht
    · filter_upwards [eventually_depthSepAt (e := e) hds] with t ht using Or.inr ⟨a, c, ht⟩
  obtain ⟨t, ⟨⟨⟨⟨hcyc', hrest'⟩, hM'⟩, hz'⟩, hu⟩, hdi, hnd⟩ :=
    ((((h1.and h2).and h3).and h4).and hne).and (hinj.and hpair) |>.exists
  -- the view `u = u₀ + t e`, in either orientation
  set u := u₀ + t • e with hu_def
  have key : ∀ (σ : ℝ), (σ = 1 ∨ σ = -1) → 0 < σ * ρ → IsRupert V := by
    intro σ hσ hσρ
    have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
    have hsu : σ • u ≠ 0 := smul_ne_zero hσ0 hu
    obtain ⟨R, hR, r, hr, hRu⟩ := exists_rotation_to_ez_pos (σ • u) hsu
    have hds : ∀ X Y : ℝ³, det3 X Y (σ • u) = σ * det3 X Y u := by
      intro X Y; simp only [det3_expand, PiLp.smul_apply, smul_eq_mul]; ring
    have hpos : ∀ X Y : ℝ³, 0 < ρ * det3 X Y u → 0 < det3 X Y (σ • u) := by
      intro X Y hXY
      rw [hds]
      have : 0 < (σ * ρ) * (ρ * det3 X Y u) := mul_pos hσρ hXY
      have hρρ : 0 < ρ * ρ := mul_self_pos.mpr hρ
      nlinarith
    have hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))) := by
      refine ⟨hk, fun i j hi hj => ?_⟩
      simp only [proj_rot_sub]
      exact cross2_proj_rot_pos hR hr hRu (hpos _ _ (hcyc' i j hi hj))
    have hdepth := depth_rot hR hr.ne' hRu
    have hin : ∀ v ∈ V, v ∉ M → (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
        interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))) := by
      intro y hy hyM hyx
      refine hp.mem_interior_of_left fun i => ?_
      simp only [proj_rot_sub]
      exact cross2_proj_rot_pos hR hr hRu (hpos _ _ (hrest' y hy i hyM hyx))
    have hrow : ∀ l : ℝ³, (R.toEuclideanLin l) 2 = r⁻¹ * (σ * ⟪l, u⟫) := by
      intro l; rw [hdepth, real_inner_smul_right]
    have hhdn : ¬ HasHorizontalDoubleNormal (fun i => proj_xy (R.toEuclideanLin (x i)))
        (fun i => (R.toEuclideanLin (x i)) 2) := by
      intro h
      obtain ⟨i, j, -, l, hl, hl0, Y, hY, Y', hY', r', hr', hYl, hext⟩ :=
        exists_pairDir_of_hdnE R hR x h
      rw [hrow] at hl0
      have hlu : ⟪l, u⟫ = 0 := by
        rcases mul_eq_zero.mp hl0 with h0 | h0
        · exact absurd h0 (inv_ne_zero hr.ne')
        · exact (mul_eq_zero.mp h0).resolve_left hσ0
      by_cases hl' : ⟪l, u₀⟫ ≠ 0 ∨ ⟪l, e⟫ ≠ 0
      · exact hnd i j l hl hl' hlu
      · push Not at hl'
        have hYY : Y' ≠ Y := by
          intro hc
          rw [hc, sub_self] at hYl
          exact (mem_filter.mp hl).2 ((smul_eq_zero.mp hYl.symm).resolve_left hr')
        refine hbad i j Y hY Y' hY' hYY ?_ ?_ hext
        · rw [hYl, real_inner_smul_left, hl'.1, mul_zero]
        · rw [hYl, real_inner_smul_left, hl'.2, mul_zero]
    have hM'' : ∀ m ∈ M, ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
        m = x i + s • (x (i + 1) - x i) + δ • (σ • u) := by
      intro m hm
      obtain ⟨i, s, δ, hs0, hs1, hδ, hmeq⟩ := hM' m hm
      refine ⟨i, s, δ * σ, hs0, hs1, mul_ne_zero hδ hσ0, ?_⟩
      rw [hmeq, smul_smul, mul_assoc]
      rcases hσ with rfl | rfl <;> norm_num
    rcases hz' with hz' | ⟨a, c, hds'⟩
    · refine isRupert_of_chords_unimodal V M R hR hr hRu x hxV hxM hp hin ?_ hhdn hM''
      have hu' := hz' hdi
      simp only [hdepth, real_inner_smul_right]
      rcases hσ with rfl | rfl
      · simp only [one_mul]; exact hu'.smul (inv_pos.mpr hr)
      · have := (hu'.neg' (by omega)).smul (inv_pos.mpr hr)
        simpa only [neg_one_mul, mul_neg] using this
    · have hds2 : DepthSepAt x (σ • u) a c := by
        rcases hσ with rfl | rfl
        · rwa [one_smul]
        · rw [neg_one_smul]; exact hds'.neg
      have hcyc2 : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (x (i + 1) - x i) (x j - x i) (σ • u) :=
        fun i j hi hj => hpos _ _ (hcyc' i j hi hj)
      exact isRupert_of_chords_depthSeparated V M R hR hr hRu x hxV hxM hp hin
        (isDepthSeparatedPair_of_depthSepAt hR hr hRu x hk hcyc2 hds2) hhdn hM''
  rcases lt_or_gt_of_ne hρ with hn | hp
  · exact key (-1) (Or.inr rfl) (by nlinarith)
  · exact key 1 (Or.inl rfl) (by linarith)

end Minimality

end
