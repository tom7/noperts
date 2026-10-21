module

public import Minimality.Type08Cases
public import Minimality.Oct9Weak
public import Minimality.EdgeView

@[expose] public section

/-!
# Sliding along a face circle (`FEWER-FACES-PROOFS.md` §10 addendum, (T1) and Lemma C)

At an edge view `u₀` of an edge crossing, a depth tie or a horizontal double normal
of the named reduced polygon `K_v` blocks Theorem 7.3.  The addendum moves the view
along the great circle of one face `F` through the crossing: at the views
`u₀ + t e` (`e` in `F`'s plane) `F` projects onto a segment, its other vertices are
*middles* over that segment, and Proposition 8.8 with one face (`isRupert_of_chords`)
applies to the rest.  Along the circle, depths and horizontal double normals change:

* two rim corners tie only at isolated `t`, unless their difference is normal to `F`;
* by Lemma 7.4 by edges (`exists_pairDir_of_hdn`), a horizontal double normal at
  `u₀ + t e` joins two rim edges whose depth intervals meet (not `EdgesApart`) and needs
  `⟪l, u₀ + t e⟫ = 0` for one of finitely many directions `l` of that pair of edges
  (`pairDirs`: the cross product of the edges, a vertex difference made perpendicular
  to one of the edges, a vertex difference), which happens at isolated `t` unless `l`
  is normal to `F`.  Edges whose depth intervals are apart at `u₀` stay apart.

So if, for every two rim edges whose depth intervals meet at `u₀`, no direction of the
pair is normal to `F` (`NoBadNormal`; on a face circle it fails on the class H1 of the
addendum and in codimension 2), every small `t > 0` except finitely many has strict
depths and no horizontal double normal.

* `isRupert_of_chordView`: Proposition 8.8 with a unimodal rest at a view `u`, from
  determinant tests (counterclockwise), with the double-normal exclusion through
  `pairDirs`; `isRupert_of_chordView_or`, the same for either orientation
  (`0 < ρ · test`; the clockwise case is the view `−u`).
* `isRupert_of_slide`: the same eventually along `u₀ + t e`, `t → 0⁺`, with
  `NoBadNormal` in place of strict depths and of the double-normal exclusion;
  `isRupert_of_slide'`, `isRupert_of_slide''` from the tests at `u₀` (`SlideTest`: positive,
  or zero with a positive derivative along `e`; in `''` also for the rim itself, for a
  vertex that pokes out along the slide).
* Unimodality along the slide: `eventually_NWS4_slide`, `eventually_unimodal_quad_slide`
  (a 4-rim without a weak saddle at `u₀`, ties allowed), `eventually_unimodal_of_strict`
  (any rim, `StrictUnimodal` at `u₀`).
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- **The bad directions of a pair of edges** `i`, `j` of a cycle (Lemma 7.4 by edges):
the cross product of the two edges, the components of a vertex difference (a vertex of
one edge to a vertex of the other) perpendicular to either edge, and the vertex
differences (nonzero ones).  A horizontal double normal between the two edges puts the
view on the great circle of one of them (`exists_pairDir_of_hdn`). -/
noncomputable def pairDirs {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (i j : ZMod k) : Finset ℝ³ :=
  (insert (cross (x (i + 1) - x i) (x (j + 1) - x j))
    ((({i, i + 1} : Finset (ZMod k)) ×ˢ ({j, j + 1} : Finset (ZMod k))).biUnion fun q =>
      ({perpTo (x q.2 - x q.1) (x (j + 1) - x j), perpTo (x q.1 - x q.2) (x (i + 1) - x i),
        x q.2 - x q.1} : Finset ℝ³))).filter (· ≠ 0)

theorem cross_mem_pairDirs {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (i j : ZMod k)
    (h : cross (x (i + 1) - x i) (x (j + 1) - x j) ≠ 0) :
    cross (x (i + 1) - x i) (x (j + 1) - x j) ∈ pairDirs x i j := by
  classical
  exact mem_filter.mpr ⟨mem_insert_self _ _, h⟩

theorem mem_pairDirs_of {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) {i j m n : ZMod k}
    (hm : m = i ∨ m = i + 1) (hn : n = j ∨ n = j + 1) {l : ℝ³}
    (hl : l = perpTo (x n - x m) (x (j + 1) - x j) ∨ l = perpTo (x m - x n) (x (i + 1) - x i) ∨
      l = x n - x m) (h : l ≠ 0) : l ∈ pairDirs x i j := by
  classical
  refine mem_filter.mpr ⟨mem_insert_of_mem (mem_biUnion.mpr ⟨(m, n), ?_, ?_⟩), h⟩
  · simp only [mem_product, mem_insert, mem_singleton]; exact ⟨hm, hn⟩
  · simp only [mem_insert, mem_singleton]; exact hl

/-- The depths of the edge `j` lie strictly on one side of those of the edge `i` (the
depth intervals of the two edges are disjoint). -/
def EdgesApart {k : ℕ} [NeZero k] (z : ZMod k → ℝ) (i j : ZMod k) : Prop :=
  (z j < z i ∧ z j < z (i + 1) ∧ z (j + 1) < z i ∧ z (j + 1) < z (i + 1)) ∨
    (z i < z j ∧ z i < z (j + 1) ∧ z (i + 1) < z j ∧ z (i + 1) < z (j + 1))

theorem EdgesApart.smul_iff {k : ℕ} [NeZero k] {z : ZMod k → ℝ} {i j : ZMod k} {c : ℝ}
    (hc : c ≠ 0) : EdgesApart (fun m => c * z m) i j ↔ EdgesApart z i j := by
  simp only [EdgesApart]
  rcases lt_or_gt_of_ne hc with hn | hp
  · simp only [mul_lt_mul_left_of_neg hn]; tauto
  · simp only [mul_lt_mul_iff_right₀ hp]

theorem between_of_segment {a b w : ℝ³} (hw : w ∈ segment ℝ a b) :
    (a 2 ≤ w 2 ∧ w 2 ≤ b 2) ∨ (b 2 ≤ w 2 ∧ w 2 ≤ a 2) := by
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hw
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hα' : α = 1 - β := by linarith
  subst hα'
  rcases le_total (a 2) (b 2) with h | h
  · left; constructor <;> nlinarith [mul_nonneg hβ (sub_nonneg.mpr h)]
  · right; constructor <;> nlinarith [mul_nonneg hβ (sub_nonneg.mpr h)]

theorem not_apart_of_between {k : ℕ} [NeZero k] {z : ZMod k → ℝ} {i j : ZMod k} {w : ℝ}
    (hi : (z i ≤ w ∧ w ≤ z (i + 1)) ∨ (z (i + 1) ≤ w ∧ w ≤ z i))
    (hj : (z j ≤ w ∧ w ≤ z (j + 1)) ∨ (z (j + 1) ≤ w ∧ w ≤ z j)) : ¬ EdgesApart z i j := by
  simp only [EdgesApart]
  rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hj with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    (rintro (⟨g1, g2, g3, g4⟩ | ⟨g1, g2, g3, g4⟩) <;> linarith)

theorem perpTo_neg_left (w e : ℝ³) : perpTo (-w) e = -perpTo w e := by
  simp only [perpTo, inner_neg_left, neg_div, neg_smul, sub_neg_eq_add]; abel

theorem perpTo_smul_right (w e : ℝ³) {σ : ℝ} (hσ : σ ≠ 0) : perpTo w (σ • e) = perpTo w e := by
  simp only [perpTo, real_inner_smul_left, real_inner_smul_right, smul_smul]
  by_cases he : ⟪e, e⟫ = 0
  · rw [inner_self_eq_zero.mp he]; simp
  · congr 1; congr 1; field_simp

theorem perpTo_zero_right (w : ℝ³) : perpTo w 0 = w := by simp [perpTo]

theorem cross_smul_smul (σ τ : ℝ) (e f : ℝ³) : cross (σ • e) (τ • f) = (σ * τ) • cross e f := by
  ext m; fin_cases m <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, cross_apply_zero, cross_apply_one,
      cross_apply_two, PiLp.smul_apply, smul_eq_mul] <;> ring

/-- An endpoint difference on an edge is a multiple of the edge. -/
theorem edge_diff {X X' a b : ℝ³} (ha : a = X ∨ a = X') (hb : b = X ∨ b = X') :
    ∃ σ : ℝ, b - a = σ • (X' - X) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  exacts [⟨0, by simp⟩, ⟨1, by simp⟩, ⟨-1, by simp⟩, ⟨0, by simp⟩]

/-- **Lemma 7.4 by edges.**  A horizontal double normal of the silhouette cycle `x` at
the view of `R` joins two edges `i`, `j` whose depth intervals meet, and puts the view
on the great circle `(R l) 2 = 0` of some `l ∈ pairDirs x i j`. -/
theorem exists_pairDir_of_hdn {k : ℕ} [NeZero k] (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : R ∈ SO3)
    (x : ZMod k → ℝ³)
    (h : HasHorizontalDoubleNormal (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2)) :
    ∃ i j, ¬ EdgesApart (fun m => (R.toEuclideanLin (x m)) 2) i j ∧
      ∃ l ∈ pairDirs x i j, (R.toEuclideanLin l) 2 = 0 := by
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
  obtain ⟨a, b, ha, hb, s, rfl, hs⟩ := endpoint_cases hY (GY i) (GY (i + 1))
  obtain ⟨c, d, hc, hd, t, rfl, ht⟩ := endpoint_cases hY' (GY' j) (GY' (j + 1))
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
          by rw [← hp]; exact hhor⟩
      · have hσ₂0 : σ₂ ≠ 0 := by rintro rfl; rw [zero_smul] at hσ₂; exact hdc hσ₂
        rw [hσ₂, perpTo_smul_right _ _ hσ₂0] at hp
        rw [hp] at hh0
        exact ⟨_, mem_pairDirs_of x hm hn (Or.inl rfl) hh0, by rw [← hp]; exact hhor⟩
    · have hσ₁0 : σ₁ ≠ 0 := by rintro rfl; rw [zero_smul] at hσ₁; exact hba hσ₁
      obtain ⟨κ, hk⟩ : ∃ κ : ℝ, d - x n = κ • (b - x m) := ⟨_, eq_smul_of_cross_eq_zero hba hcr⟩
      have hp : h = perpTo (x n - x m) (b - x m) := perpTo_eq (t * κ - s)
        (by rw [hhdef, hk]; module) hs
      rw [hσ₁, perpTo_smul_right _ _ hσ₁0] at hp
      have hp' : -h = perpTo (x m - x n) (x (i + 1) - x i) := by
        rw [hp, ← perpTo_neg_left, neg_sub]
      refine ⟨-h, mem_pairDirs_of x hm hn (Or.inr (Or.inl hp')) (neg_ne_zero.mpr hh0), ?_⟩
      rw [map_neg, PiLp.neg_apply, hhor, neg_zero]
  · have hσ : σ₁ * σ₂ ≠ 0 := by
      intro h0; apply hcr; rw [hσ₁, hσ₂, cross_smul_smul, h0, zero_smul]
    have hcr' : cross (b - x m) (d - x n) =
        (σ₁ * σ₂) • cross (x (i + 1) - x i) (x (j + 1) - x j) := by
      rw [hσ₁, hσ₂, cross_smul_smul]
    have hcr0 : cross (x (i + 1) - x i) (x (j + 1) - x j) ≠ 0 := by
      intro h0; apply hcr; rw [hcr', h0, smul_zero]
    refine ⟨cross (x (i + 1) - x i) (x (j + 1) - x j), cross_mem_pairDirs x i j hcr0, ?_⟩
    have h1 := inner_cross_eq_zero_of_perp hh0 hs ht' (by rw [← hrow]; exact hhor)
    rw [hcr', real_inner_smul_left] at h1
    rw [hrow]
    exact (mul_eq_zero.mp h1).resolve_left hσ

/-- **No persistent horizontal double normal along a face circle** (Lemma C (b), Lean
form).  For every two edges of the cycle `x` whose depth intervals meet at the view
`u₀`, no bad direction of the pair (`pairDirs`, Lemma 7.4 by edges) is normal to the
plane of `u₀` and `e`.  Then along the views `u₀ + t e` the rim's depths tie and its
horizontal double normals occur only at isolated `t` (`isRupert_of_slide`).  It fails
only when two edges of the rim with meeting depth intervals are both parallel to the
plane, or a vertex and an edge of such a pair span a perpendicular to the plane, or two
vertices at one depth differ by a normal of the plane. -/
def NoBadNormal {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (u₀ e : ℝ³) : Prop :=
  ∀ i j, ¬ EdgesApart (fun m => ⟪x m, u₀⟫) i j → ∀ l ∈ pairDirs x i j,
    ⟪l, u₀⟫ ≠ 0 ∨ ⟪l, e⟫ ≠ 0

/-- `NoBadNormal` depends only on the plane of `u₀` and `e`. -/
theorem NoBadNormal.of_span {k : ℕ} [NeZero k] {x : ZMod k → ℝ³} {u₀ e e' : ℝ³}
    (h : NoBadNormal x u₀ e) (α β : ℝ) (he : e = α • u₀ + β • e') : NoBadNormal x u₀ e' := by
  intro i j hov l hl
  by_contra hc
  push Not at hc
  rcases h i j hov l hl with h1 | h1
  · exact h1 hc.1
  · apply h1; rw [he, inner_add_right, real_inner_smul_right, real_inner_smul_right, hc.1, hc.2]
    ring

/-- The depth along the view `u` after a rotation taking `u` to `r e_z`. -/
theorem depth_rot {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO3) {u : ℝ³} {r : ℝ} (hr : r ≠ 0)
    (hRu : R.toEuclideanLin u = r • ez) (y : ℝ³) : (R.toEuclideanLin y) 2 = r⁻¹ * ⟪y, u⟫ := by
  have : r * (R.toEuclideanLin y) 2 = ⟪y, u⟫ := by
    rw [← inner_ez, ← real_inner_smul_right, ← hRu, inner_toEuclideanLin_SO3 hR]
  rw [← this]; field_simp

/-- **Proposition 8.8 with a unimodal rest, at a view given by determinant tests.**
The cycle `x` passes all determinant tests at `u` (strictly convex,
counterclockwise), every point off `x` and off the middles `M` is strictly inside,
each middle lies over an edge of `x` (`m = x i + s (x (i + 1) − x i) + δ u`), the
depths are cyclically unimodal, and no bad direction of the rim (Lemma 7.4) is
orthogonal to `u` (so there is no horizontal double normal).  Then `V` is Rupert. -/
theorem isRupert_of_chordView (V M : Finset ℝ³) (u : ℝ³) (hu : u ≠ 0) {k : ℕ} [NeZero k]
    (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V) (hxM : ∀ i, x i ∉ M) (hk : 3 ≤ k)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (x (i + 1) - x i) (x j - x i) u)
    (hrest : ∀ y ∈ V, y ∉ M → (∀ j, y ≠ x j) → ∀ i, 0 < det3 (x (i + 1) - x i) (y - x i) u)
    (hz : IsCyclicUnimodal (fun i => ⟪x i, u⟫))
    (hnd : ∀ i j, ¬ EdgesApart (fun m => ⟪x m, u⟫) i j → ∀ l ∈ pairDirs x i j, ⟪l, u⟫ ≠ 0)
    (hM : ∀ m ∈ M, ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = x i + s • (x (i + 1) - x i) + δ • u) : IsRupert V := by
  classical
  obtain ⟨R, hR, r, hr, hRu⟩ := exists_rotation_to_ez_pos u hu
  have hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))) := by
    refine ⟨hk, fun i j hi hj => ?_⟩
    simp only [proj_rot_sub]
    exact cross2_proj_rot_pos hR hr hRu (hcyc i j hi hj)
  have hdepth := depth_rot hR hr.ne' hRu
  refine isRupert_of_chords_unimodal V M R hR hr hRu x hxV hxM hp ?_ ?_ ?_ hM
  · intro y hy hyM hyx
    refine hp.mem_interior_of_left fun i => ?_
    simp only [proj_rot_sub]
    exact cross2_proj_rot_pos hR hr hRu (hrest y hy hyM hyx i)
  · simp only [hdepth]; exact hz.smul (inv_pos.mpr hr)
  · intro h
    obtain ⟨i, j, hov, l, hl, hl0⟩ := exists_pairDir_of_hdn R hR x h
    simp only [hdepth] at hov
    rw [hdepth] at hl0
    exact hnd i j (fun h' => hov ((EdgesApart.smul_iff (inv_ne_zero hr.ne')).mpr h')) l hl
      ((mul_eq_zero.mp hl0).resolve_left (inv_ne_zero hr.ne'))

/-- A unimodal cyclic sequence stays unimodal when negated (its unique local maximum
becomes the unique local minimum). -/
theorem IsCyclicUnimodal.neg' {k : ℕ} [NeZero k] (hk : 2 ≤ k) {z : ZMod k → ℝ}
    (hz : IsCyclicUnimodal z) : IsCyclicUnimodal (fun i => -z i) := by
  classical
  refine isCyclicUnimodal_of_localMin_unique hk _ (fun a b e => hz.1 (neg_injective e)) ?_
  intro a b h1 h2 h3 h4
  have hc := Finset.card_le_one.mp hz.2.le
  exact hc a (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; constructor <;> linarith)
    b (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; constructor <;> linarith)

/-- **`isRupert_of_chordView` in either orientation**: all tests have the sign of
`ρ ≠ 0` (`ρ < 0`: the cycle is clockwise at `u`, and counterclockwise at `−u`). -/
theorem isRupert_of_chordView_or (V M : Finset ℝ³) (u : ℝ³) (hu : u ≠ 0) {k : ℕ} [NeZero k]
    (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V) (hxM : ∀ i, x i ∉ M) (hk : 3 ≤ k) (ρ : ℝ)
    (hρ : ρ ≠ 0)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < ρ * det3 (x (i + 1) - x i) (x j - x i) u)
    (hrest : ∀ y ∈ V, y ∉ M → (∀ j, y ≠ x j) → ∀ i,
      0 < ρ * det3 (x (i + 1) - x i) (y - x i) u)
    (hz : IsCyclicUnimodal (fun i => ⟪x i, u⟫))
    (hnd : ∀ i j, ¬ EdgesApart (fun m => ⟪x m, u⟫) i j → ∀ l ∈ pairDirs x i j, ⟪l, u⟫ ≠ 0)
    (hM : ∀ m ∈ M, ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = x i + s • (x (i + 1) - x i) + δ • u) : IsRupert V := by
  classical
  rcases lt_or_gt_of_ne hρ with hn | hp
  · -- clockwise at `u`: view along `−u`
    refine isRupert_of_chordView V M (-u) (neg_ne_zero.mpr hu) x hxV hxM hk ?_ ?_ ?_ ?_ ?_
    · intro i j hi hj
      rw [det3_neg_right]; have := hcyc i j hi hj; nlinarith
    · intro y hy hyM hyx i
      rw [det3_neg_right]; have := hrest y hy hyM hyx i; nlinarith
    · simp only [inner_neg_right]; exact hz.neg' (by omega)
    · intro i j hov l hl
      rw [inner_neg_right, neg_ne_zero]
      refine hnd i j (fun h' => hov ?_) l hl
      have := (EdgesApart.smul_iff (z := fun m => ⟪x m, u⟫) (i := i) (j := j)
        (c := -1) (by norm_num)).mpr h'
      simpa only [inner_neg_right, neg_one_mul] using this
    · intro m hm
      obtain ⟨i, s, δ, hs0, hs1, hδ, rfl⟩ := hM m hm
      exact ⟨i, s, -δ, hs0, hs1, neg_ne_zero.mpr hδ, by rw [neg_smul, smul_neg, neg_neg]⟩
  · exact isRupert_of_chordView V M u hu x hxV hxM hk
      (fun i j hi hj => pos_of_mul_pos_right (hcyc i j hi hj) hp.le)
      (fun y hy hyM hyx i => pos_of_mul_pos_right (hrest y hy hyM hyx i) hp.le) hz hnd hM

/-- **Sliding along a face circle (Lemma C of the §10 addendum, Lean form).**  Suppose
that at the views `u₀ + t e`, for all small `t > 0`, the cycle `x` passes all
determinant tests (orientation `ρ`), every point off `x` and off `M` is strictly
inside, each middle lies over an edge of `x`, and distinct depths are unimodal.  If no
bad direction of the rim is normal to the plane of `u₀` and `e` (`NoBadNormal`), then
`V` is Rupert: some such `t` has distinct depths and no horizontal double normal. -/
theorem isRupert_of_slide (V M : Finset ℝ³) (u₀ e : ℝ³) (hu₀ : u₀ ≠ 0) {k : ℕ} [NeZero k]
    (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V) (hxM : ∀ i, x i ∉ M) (hxinj : Function.Injective x)
    (hk : 3 ≤ k) (ρ : ℝ) (hρ : ρ ≠ 0)
    (hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (∀ i j, j ≠ i → j ≠ i + 1 → 0 < ρ * det3 (x (i + 1) - x i) (x j - x i) (u₀ + t • e)) ∧
      (∀ y ∈ V, y ∉ M → (∀ j, y ≠ x j) → ∀ i,
        0 < ρ * det3 (x (i + 1) - x i) (y - x i) (u₀ + t • e)) ∧
      (∀ m ∈ M, ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
        m = x i + s • (x (i + 1) - x i) + δ • (u₀ + t • e)) ∧
      (Function.Injective (fun i => ⟪x i, u₀ + t • e⟫) →
        IsCyclicUnimodal (fun i => ⟪x i, u₀ + t • e⟫)))
    (hbad : NoBadNormal x u₀ e) : IsRupert V := by
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
  have hlt : ∀ p q : ℝ³, ⟪p, u₀⟫ < ⟪q, u₀⟫ →
      ∀ᶠ t in 𝓝[>] (0 : ℝ), ⟪p, u₀ + t • e⟫ < ⟪q, u₀ + t • e⟫ := by
    intro p q h
    filter_upwards [eventually_pos_affine (A := ⟪q, u₀⟫ - ⟪p, u₀⟫) (B := ⟪q, e⟫ - ⟪p, e⟫)
      (Or.inl (by linarith))] with t ht
    rw [hlin, hlin]; linarith
  -- pairs of edges: either their depth intervals stay apart, or no bad direction vanishes
  have hpair : ∀ i j : ZMod k, ∀ᶠ t in 𝓝[>] (0 : ℝ),
      EdgesApart (fun m => ⟪x m, u₀ + t • e⟫) i j ∨
        ∀ l ∈ pairDirs x i j, ⟪l, u₀ + t • e⟫ ≠ 0 := by
    intro i j
    by_cases hov : EdgesApart (fun m => ⟪x m, u₀⟫) i j
    · simp only [EdgesApart] at hov
      rcases hov with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
      · filter_upwards [hlt _ _ h1, hlt _ _ h2, hlt _ _ h3, hlt _ _ h4] with t g1 g2 g3 g4
        exact Or.inl (Or.inl ⟨g1, g2, g3, g4⟩)
      · filter_upwards [hlt _ _ h1, hlt _ _ h2, hlt _ _ h3, hlt _ _ h4] with t g1 g2 g3 g4
        exact Or.inl (Or.inr ⟨g1, g2, g3, g4⟩)
    · filter_upwards [(eventually_all_finset _).mpr fun l hl => hev1 l (hbad i j hov l hl)]
        with t ht using Or.inr ht
  have hne : ∀ᶠ t in 𝓝[>] (0 : ℝ), u₀ + t • e ≠ 0 := by
    have hc : Continuous fun t : ℝ => u₀ + t • e := by fun_prop
    exact (hc.continuousAt.eventually (isOpen_ne.mem_nhds
      (show u₀ + (0 : ℝ) • e ≠ 0 by simpa using hu₀))).filter_mono nhdsWithin_le_nhds
  have hinj : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i j : ZMod k, i ≠ j →
      ⟪x i - x j, u₀ + t • e⟫ ≠ 0 := by
    refine eventually_all.mpr fun i => eventually_all.mpr fun j => ?_
    by_cases hij : i = j
    · filter_upwards with t h; exact absurd hij h
    · by_cases h0 : ⟪x i - x j, u₀⟫ = 0
      · -- a depth tie at `u₀`: the edges at `j` and `i` share that depth
        have hov : ¬ EdgesApart (fun m => ⟪x m, u₀⟫) j i := by
          have hz : ⟪x i, u₀⟫ = ⟪x j, u₀⟫ := by rw [inner_sub_left] at h0; linarith
          simp only [EdgesApart]
          rintro (⟨g1, -, -, -⟩ | ⟨g1, -, -, -⟩) <;> linarith
        have hmem := mem_pairDirs_of x (i := j) (j := i) (m := j) (n := i) (Or.inl rfl) (Or.inl rfl)
          (Or.inr (Or.inr rfl)) (sub_ne_zero.mpr (hxinj.ne hij))
        filter_upwards [hev1 _ (hbad j i hov _ hmem)] with t ht _ using ht
      · filter_upwards [hev1 _ (Or.inl h0)] with t ht _ using ht
  obtain ⟨t, ⟨⟨hcyc, hrest, hM, hz⟩, hu, hdi⟩, hnd⟩ :=
    ((hev.and (hne.and hinj)).and (eventually_all.mpr fun i => eventually_all.mpr
      fun j => hpair i j)).exists
  refine isRupert_of_chordView_or V M (u₀ + t • e) hu x hxV hxM hk ρ hρ hcyc hrest
    (hz fun i j hij => ?_) (fun i j hov => (hnd i j).resolve_left hov) hM
  by_contra hne'
  exact hdi i j hne' (by rw [inner_sub_left]; exact sub_eq_zero.mpr hij)

/-- A determinant test along the slide: positive at `u₀`, or zero there with a
positive derivative along `e`. -/
theorem eventually_det3_slide {X Y u₀ e : ℝ³} {ρ : ℝ}
    (h : 0 < ρ * det3 X Y u₀ ∨ (det3 X Y u₀ = 0 ∧ 0 < ρ * det3 X Y e)) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < ρ * det3 X Y (u₀ + t • e) := by
  have e1 : ∀ t : ℝ, ρ * det3 X Y (u₀ + t • e) = ρ * det3 X Y u₀ + t * (ρ * det3 X Y e) := by
    intro t; rw [det3_add_smul]; ring
  simp only [e1]
  refine eventually_pos_affine ?_
  rcases h with h | ⟨h0, h1⟩
  · exact Or.inl h
  · exact Or.inr ⟨by rw [h0, mul_zero], h1⟩

/-- A 4-rim whose depths at `u₀` have no weak saddle (`NWS4`; ties allowed) keeps none
at the views `u₀ + t e` for small `t`. -/
theorem eventually_NWS4_slide {p₀ p₁ p₂ p₃ u₀ e : ℝ³}
    (h : NWS4 (quad ⟪p₀, u₀⟫ ⟪p₁, u₀⟫ ⟪p₂, u₀⟫ ⟪p₃, u₀⟫)) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      NWS4 (quad ⟪p₀, u₀ + t • e⟫ ⟪p₁, u₀ + t • e⟫ ⟪p₂, u₀ + t • e⟫ ⟪p₃, u₀ + t • e⟫) := by
  have hc : Continuous fun t : ℝ =>
      quad ⟪p₀, u₀ + t • e⟫ ⟪p₁, u₀ + t • e⟫ ⟪p₂, u₀ + t • e⟫ ⟪p₃, u₀ + t • e⟫ := by
    refine continuous_pi fun i => ?_
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp only [quad_0, quad_1, quad_2, quad_3] <;> fun_prop
  have h0 : quad ⟪p₀, u₀ + (0 : ℝ) • e⟫ ⟪p₁, u₀ + (0 : ℝ) • e⟫ ⟪p₂, u₀ + (0 : ℝ) • e⟫
      ⟪p₃, u₀ + (0 : ℝ) • e⟫ ∈ {z : ZMod 4 → ℝ | NWS4 z} := by
    simp only [zero_smul, add_zero, Set.mem_ofPred_eq]; exact h
  exact (hc.continuousAt.eventually (isOpen_NWS4.mem_nhds h0)).filter_mono nhdsWithin_le_nhds

/-- Unimodality of distinct depths along the slide for a 4-rim without a weak saddle
at `u₀`. -/
theorem eventually_unimodal_quad_slide {p₀ p₁ p₂ p₃ u₀ e : ℝ³}
    (h : NWS4 (quad ⟪p₀, u₀⟫ ⟪p₁, u₀⟫ ⟪p₂, u₀⟫ ⟪p₃, u₀⟫)) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      Function.Injective (fun i => ⟪quad p₀ p₁ p₂ p₃ i, u₀ + t • e⟫) →
        IsCyclicUnimodal (fun i => ⟪quad p₀ p₁ p₂ p₃ i, u₀ + t • e⟫) := by
  filter_upwards [eventually_NWS4_slide (e := e) h] with t ht hinj
  rw [quad_inner] at hinj ⊢
  exact isCyclicUnimodal_of_NWS4 hinj ht

/-- A determinant test along the slide, in the form used by `isRupert_of_slide'`:
positive at `u₀`, or zero there with a positive derivative along `e` (orientation
`ρ`). -/
def SlideTest (ρ : ℝ) (X Y u₀ e : ℝ³) : Prop :=
  0 < ρ * det3 X Y u₀ ∨ (det3 X Y u₀ = 0 ∧ 0 < ρ * det3 X Y e)

theorem eventually_forall_cycle {k : ℕ} [NeZero k] {P : ZMod k → ZMod k → ℝ → Prop}
    (h : ∀ i j, j ≠ i → j ≠ i + 1 → ∀ᶠ t in 𝓝[>] (0 : ℝ), P i j t) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i j, j ≠ i → j ≠ i + 1 → P i j t := by
  refine eventually_all.mpr fun i => eventually_all.mpr fun j => ?_
  by_cases h1 : j ≠ i
  · by_cases h2 : j ≠ i + 1
    · filter_upwards [h i j h1 h2] with t ht _ _ using ht
    · filter_upwards with t _ h2' using absurd h2' h2
  · filter_upwards with t h1' using absurd h1' h1

/-- **`isRupert_of_slide` from the tests at `u₀`.**  The cycle's tests are strict at
`u₀`; every other point off the middles passes each edge test strictly at `u₀`, or
with value zero and a positive derivative along `e` (`SlideTest`); the middles lie
over edges of `x` at all small `t > 0`; distinct depths are eventually unimodal; and no
bad direction of the rim is normal to the plane of `u₀` and `e`. -/
theorem isRupert_of_slide' (V M : Finset ℝ³) (u₀ e : ℝ³) (hu₀ : u₀ ≠ 0) {k : ℕ} [NeZero k]
    (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V) (hxM : ∀ i, x i ∉ M) (hxinj : Function.Injective x)
    (hk : 3 ≤ k) (ρ : ℝ) (hρ : ρ ≠ 0)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < ρ * det3 (x (i + 1) - x i) (x j - x i) u₀)
    (hrest : ∀ y ∈ V, y ∉ M → (∀ j, y ≠ x j) → ∀ i,
      SlideTest ρ (x (i + 1) - x i) (y - x i) u₀ e)
    (hM : ∀ m ∈ M, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = x i + s • (x (i + 1) - x i) + δ • (u₀ + t • e))
    (hz : ∀ᶠ t in 𝓝[>] (0 : ℝ), Function.Injective (fun i => ⟪x i, u₀ + t • e⟫) →
      IsCyclicUnimodal (fun i => ⟪x i, u₀ + t • e⟫))
    (hbad : NoBadNormal x u₀ e) : IsRupert V := by
  classical
  refine isRupert_of_slide V M u₀ e hu₀ x hxV hxM hxinj hk ρ hρ ?_ hbad
  have h1 := eventually_forall_cycle fun i j hi hj =>
    eventually_det3_slide (e := e) (Or.inl (hcyc i j hi hj))
  have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ y ∈ V, ∀ i : ZMod k, y ∉ M → (∀ j, y ≠ x j) →
      0 < ρ * det3 (x (i + 1) - x i) (y - x i) (u₀ + t • e) := by
    refine (eventually_all_finset V).mpr fun y hy => eventually_all.mpr fun i => ?_
    by_cases hyM : y ∉ M
    · by_cases hyx : ∀ j, y ≠ x j
      · filter_upwards [eventually_det3_slide (hrest y hy hyM hyx i)] with t ht _ _ using ht
      · filter_upwards with t _ h using absurd h hyx
    · filter_upwards with t h using absurd h hyM
  have h3 := (eventually_all_finset M).mpr hM
  filter_upwards [h1, h2, h3, hz] with t ht1 ht2 ht3 ht4
  exact ⟨ht1, fun y hy hyM hyx i => ht2 y hy i hyM hyx, ht3, ht4⟩

theorem image_quad (p₀ p₁ p₂ p₃ : ℝ³) :
    (univ.image (quad p₀ p₁ p₂ p₃) : Finset ℝ³) = {p₀, p₁, p₂, p₃} := by
  classical
  ext z
  simp only [mem_image, mem_univ, true_and, mem_insert, mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simp [quad_0, quad_1, quad_2, quad_3]
  · rintro (rfl | rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]

/-- **Strictly unimodal**: neighbouring values differ and there is exactly one local
maximum.  This is an open condition on the values. -/
def StrictUnimodal {k : ℕ} [NeZero k] (z : ZMod k → ℝ) : Prop :=
  (∀ i, z i ≠ z (i + 1)) ∧ (univ.filter fun i => z (i - 1) < z i ∧ z (i + 1) < z i).card = 1

/-- A rim whose depths at `u₀` are strictly unimodal has unimodal distinct depths at the
views `u₀ + t e` for small `t > 0`. -/
theorem eventually_unimodal_of_strict {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (u₀ e : ℝ³)
    (h : StrictUnimodal (fun i => ⟪x i, u₀⟫)) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), Function.Injective (fun i => ⟪x i, u₀ + t • e⟫) →
      IsCyclicUnimodal (fun i => ⟪x i, u₀ + t • e⟫) := by
  classical
  obtain ⟨hne, hcard⟩ := h
  have hlin : ∀ (i j : ZMod k) (t : ℝ), ⟪x i, u₀ + t • e⟫ - ⟪x j, u₀ + t • e⟫ =
      (⟪x i, u₀⟫ - ⟪x j, u₀⟫) + t * (⟪x i, e⟫ - ⟪x j, e⟫) := by
    intro i j t; simp only [inner_add_right, real_inner_smul_right]; ring
  have hsign : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i : ZMod k,
      (⟪x i, u₀⟫ < ⟪x (i + 1), u₀⟫ ↔ ⟪x i, u₀ + t • e⟫ < ⟪x (i + 1), u₀ + t • e⟫) ∧
      (⟪x (i + 1), u₀⟫ < ⟪x i, u₀⟫ ↔ ⟪x (i + 1), u₀ + t • e⟫ < ⟪x i, u₀ + t • e⟫) := by
    refine eventually_all.mpr fun i => ?_
    rcases lt_or_gt_of_ne (hne i) with h1 | h1
    · filter_upwards [eventually_pos_affine (A := ⟪x (i + 1), u₀⟫ - ⟪x i, u₀⟫)
        (B := ⟪x (i + 1), e⟫ - ⟪x i, e⟫) (Or.inl (by linarith))] with t ht
      have := hlin (i + 1) i t
      constructor
      · exact ⟨fun _ => by linarith, fun _ => h1⟩
      · exact ⟨fun h2 => absurd h2 (not_lt.mpr h1.le), fun h2 => by linarith⟩
    · filter_upwards [eventually_pos_affine (A := ⟪x i, u₀⟫ - ⟪x (i + 1), u₀⟫)
        (B := ⟪x i, e⟫ - ⟪x (i + 1), e⟫) (Or.inl (by linarith))] with t ht
      have := hlin i (i + 1) t
      constructor
      · exact ⟨fun h2 => absurd h2 (not_lt.mpr h1.le), fun h2 => by linarith⟩
      · exact ⟨fun _ => by linarith, fun _ => h1⟩
  filter_upwards [hsign] with t ht hinj
  refine ⟨hinj, ?_⟩
  show (univ.filter fun i => ⟪x (i - 1), u₀ + t • e⟫ < ⟪x i, u₀ + t • e⟫ ∧
    ⟪x (i + 1), u₀ + t • e⟫ < ⟪x i, u₀ + t • e⟫).card = 1
  have hfe : (univ.filter fun i => ⟪x (i - 1), u₀ + t • e⟫ < ⟪x i, u₀ + t • e⟫ ∧
      ⟪x (i + 1), u₀ + t • e⟫ < ⟪x i, u₀ + t • e⟫) =
      (univ.filter fun i => ⟪x (i - 1), u₀⟫ < ⟪x i, u₀⟫ ∧ ⟪x (i + 1), u₀⟫ < ⟪x i, u₀⟫) := by
    ext i
    simp only [mem_filter, mem_univ, true_and]
    have e1 := (ht (i - 1)).1
    have e2 := (ht i).2
    rw [sub_add_cancel] at e1
    rw [e1, e2]
  rw [hfe]; exact hcard


/-- **`isRupert_of_slide'` with the cycle's own tests allowed to vanish at `u₀`** (with
a positive derivative along `e`): a vertex that is a middle at `u₀` and pokes out
along the slide is a corner of the rim. -/
theorem isRupert_of_slide'' (V M : Finset ℝ³) (u₀ e : ℝ³) (hu₀ : u₀ ≠ 0) {k : ℕ} [NeZero k]
    (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V) (hxM : ∀ i, x i ∉ M) (hxinj : Function.Injective x)
    (hk : 3 ≤ k) (ρ : ℝ) (hρ : ρ ≠ 0)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → SlideTest ρ (x (i + 1) - x i) (x j - x i) u₀ e)
    (hrest : ∀ y ∈ V, y ∉ M → (∀ j, y ≠ x j) → ∀ i,
      SlideTest ρ (x (i + 1) - x i) (y - x i) u₀ e)
    (hM : ∀ m ∈ M, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = x i + s • (x (i + 1) - x i) + δ • (u₀ + t • e))
    (hz : ∀ᶠ t in 𝓝[>] (0 : ℝ), Function.Injective (fun i => ⟪x i, u₀ + t • e⟫) →
      IsCyclicUnimodal (fun i => ⟪x i, u₀ + t • e⟫))
    (hbad : NoBadNormal x u₀ e) : IsRupert V := by
  classical
  refine isRupert_of_slide V M u₀ e hu₀ x hxV hxM hxinj hk ρ hρ ?_ hbad
  have h1 := eventually_forall_cycle fun i j hi hj =>
    eventually_det3_slide (hcyc i j hi hj)
  have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ y ∈ V, ∀ i : ZMod k, y ∉ M → (∀ j, y ≠ x j) →
      0 < ρ * det3 (x (i + 1) - x i) (y - x i) (u₀ + t • e) := by
    refine (eventually_all_finset V).mpr fun y hy => eventually_all.mpr fun i => ?_
    by_cases hyM : y ∉ M
    · by_cases hyx : ∀ j, y ≠ x j
      · filter_upwards [eventually_det3_slide (hrest y hy hyM hyx i)] with t ht _ _ using ht
      · filter_upwards with t _ h using absurd h hyx
    · filter_upwards with t h using absurd h hyM
  have h3 := (eventually_all_finset M).mpr hM
  filter_upwards [h1, h2, h3, hz] with t ht1 ht2 ht3 ht4
  exact ⟨ht1, fun y hy hyM hyx i => ht2 y hy i hyM hyx, ht3, ht4⟩

end Minimality

end
