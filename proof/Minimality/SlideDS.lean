module

public import Minimality.Slide
public import Minimality.DepthSeparated

@[expose] public section

/-!
# Sliding along a face circle: depth-separated pairs and persistent double normals
(`FEWER-FACES-PROOFS.md` §10 addendum, Lemma H (c), Lemma X; Theorem 8.10)

`Slide.lean` slides the view along a face circle with a rim that is unimodal along the
slide (Theorem 7.3), and excludes horizontal double normals through the bad directions of
pairs of rim edges (`NoBadNormal`).  Two refinements, both used in type 08:

* **Depth-separated pairs (Lemma H (c)).**  The five-corner rim `K_v ∪ {m}` of Lemma H may
  be two-peaked but have a depth-separated parallel pair `(e, x)`; then Theorem 8.10 replaces
  Theorem 7.3.  The pair is stated in space at the view `u` (`DepthSepAt`), orientation-free
  and strict, so a pair at the edge view `u₀` persists along the slide
  (`eventually_depthSepAt`).
* **Persistent double normals (Lemma X).**  A bad direction `l` of a pair of rim edges that
  is normal to the face (both edges parallel to it, say) only matters if a horizontal double
  normal along `l` can occur at all: a point `Y'` of one edge minus a point `Y` of the other
  is a nonzero multiple of `l` (the feet of the double normal lie on the edges).  Lemma 7.4 by
  edges gives these feet (`exists_pairDir_of_hdn'`), and `NoBadNormalR` asks, for each bad
  direction normal to the face, only that there are none (`NoFeet`).  For two edges parallel
  to the face this is exactly the paper's "the double normal persists along the circle": the
  feet exist iff the orthogonal projections of the two edges onto the face meet.

* `DepthSepAt`, `DepthSepAt.neg`, `isDepthSeparatedPair_of_depthSepAt`: the pair in space
  and on the screen (`IsDepthSeparatedPair`).
* `NoFeet`, `exists_pairDir_of_hdn'`, `NoBadNormalR`, `NoBadNormal.toR`,
  `NoBadNormalR.of_span`.
* `isRupert_of_chordViewG`, `isRupert_of_chordViewG_or`: Proposition 8.8 at a view from
  determinant tests, with a unimodal rest (Theorem 7.3) or a depth-separated pair (Theorem
  8.10), double normals excluded through `pairDirs` and `NoFeet`.
* `isRupert_of_slideG`: the slide with `NoBadNormalR`, unimodal along the slide or with a
  depth-separated pair (no distinct depths needed for the latter).
* `UniOrSep` (strictly unimodal at `u₀`, or a depth-separated pair at `u₀`) and
  `isRupert_of_slide_uos`: the slide from the tests at `u₀` (as `isRupert_of_slide''`).
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### Depth-separated pairs in space -/

/-- **A depth-separated parallel pair at the view `u`, in space** (Theorem 8.10, strict
form).  For the edge `e = [x a, x (a + 1)]` of the cycle `x`, the vertex `x c` is strictly
the farthest from the line of `e` on the screen (every other vertex `x j` gives
`det3 e (x j − x c) u` of the sign opposite to `det3 e (x c − x a) u`; this is
`−n_e ∈ int N_c`), and the corners from `c` to `a` lie strictly on one side of the depth
`⟪x c, u⟫`, those from `a + 1` back to `c` strictly on the other.  Orientation-free; strict,
hence open. -/
def DepthSepAt {k : ℕ} (x : ZMod k → ℝ³) (u : ℝ³) (a c : ZMod k) : Prop :=
  (∀ j, j ≠ c →
    det3 (x (a + 1) - x a) (x j - x c) u * det3 (x (a + 1) - x a) (x c - x a) u < 0) ∧
  (((∀ s : ℕ, 0 < s → s ≤ (a - c).val → ⟪x c, u⟫ < ⟪x (c + s), u⟫) ∧
      ∀ s : ℕ, (a - c).val < s → s < k → ⟪x (c + s), u⟫ < ⟪x c, u⟫) ∨
    ((∀ s : ℕ, 0 < s → s ≤ (a - c).val → ⟪x (c + s), u⟫ < ⟪x c, u⟫) ∧
      ∀ s : ℕ, (a - c).val < s → s < k → ⟪x c, u⟫ < ⟪x (c + s), u⟫))

theorem det3_neg_right' (a b c : ℝ³) : det3 a b (-c) = -det3 a b c := by
  simp only [det3_expand, PiLp.neg_apply]; ring

/-- The pair at `−u` (the screen mirrored, the depths negated). -/
theorem DepthSepAt.neg {k : ℕ} {x : ZMod k → ℝ³} {u : ℝ³} {a c : ZMod k}
    (h : DepthSepAt x u a c) : DepthSepAt x (-u) a c := by
  obtain ⟨hn, hz⟩ := h
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [det3_neg_right', det3_neg_right', neg_mul_neg]; exact hn j hj
  · simp only [inner_neg_right, neg_lt_neg_iff]
    rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩

/-- **The pair on the screen.**  At a rotation `R` with `R u = r e_z` (`r > 0`), if the
cycle `x` passes its determinant tests counterclockwise, a `DepthSepAt` pair is an
`IsDepthSeparatedPair` of the projected polygon with the rotated depths. -/
theorem isDepthSeparatedPair_of_depthSepAt {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO3)
    {u : ℝ³} {r : ℝ} (hr : 0 < r) (hRu : R.toEuclideanLin u = r • ez) {k : ℕ} [NeZero k]
    (x : ZMod k → ℝ³) (hk : 3 ≤ k)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (x (i + 1) - x i) (x j - x i) u)
    {a c : ZMod k} (hds : DepthSepAt x u a c) :
    IsDepthSeparatedPair (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2) a c := by
  classical
  obtain ⟨hn, hz⟩ := hds
  have hc1 : c + 1 ≠ c := by
    intro h
    have : Fact (1 < k) := ⟨by omega⟩
    have h1 : c + 1 - c = c - c := by rw [h]
    simp at h1
  have hca : c ≠ a := by
    rintro rfl
    have := hn (c + 1) hc1
    rw [sub_self, show det3 (x (c + 1) - x c) 0 u = 0 by simp [det3_expand], mul_zero] at this
    exact lt_irrefl _ this
  have hca1 : c ≠ a + 1 := by
    rintro rfl
    have := hn (a + 1 + 1) hc1
    rw [show det3 (x (a + 1) - x a) (x (a + 1) - x a) u = 0 by simp only [det3_expand]; ring,
      mul_zero] at this
    exact lt_irrefl _ this
  have hpos := hcyc a c hca hca1
  have hle : ∀ j, det3 (x (a + 1) - x a) (x j - x c) u ≤ 0 := by
    intro j
    by_cases hj : j = c
    · subst hj; rw [sub_self]; simp [det3_expand]
    · have := hn j hj
      exact (neg_of_mul_neg_left this hpos.le).le
  set p : ZMod k → ℝ² := fun i => proj_xy (R.toEuclideanLin (x i)) with hp
  set n := -outNormal (p a) (p (a + 1)) with hn_def
  have hgen : ∀ j, ⟪n, p j - p c⟫ ≤ 0 := by
    intro j
    have e1 : ⟪n, p j - p c⟫ = cross2 (p (a + 1) - p a) (p j - p c) := by
      rw [hn_def, inner_neg_left, inner_outNormal, neg_neg]
    have e2 := cross2_proj_rot hR hRu (x (a + 1) - x a) (x j - x c)
    rw [← proj_rot_sub, ← proj_rot_sub] at e2
    rw [e1]
    have := hle j
    rw [← e2] at this
    exact nonpos_of_mul_nonpos_right this hr
  refine ⟨?_, ?_⟩
  · intro q hq
    have hconv : Convex ℝ {w : ℝ² | ⟪n, w⟫ ≤ ⟪n, p c⟫} :=
      convex_halfSpace_le (f := fun w : ℝ² => ⟪n, w⟫)
        ⟨fun v w => inner_add_right _ _ _, fun s v => real_inner_smul_right _ _ _⟩ _
    have hsub : Set.range p ⊆ {w : ℝ² | ⟪n, w⟫ ≤ ⟪n, p c⟫} := by
      rintro _ ⟨j, rfl⟩
      have := hgen j
      rw [inner_sub_right] at this
      show ⟪n, p j⟫ ≤ ⟪n, p c⟫
      linarith
    have := convexHull_min hsub hconv hq
    simp only [Set.mem_ofPred_eq] at this
    rw [inner_sub_right]; linarith
  · have hdepth := depth_rot hR hr.ne' hRu
    have hri : 0 < r⁻¹ := inv_pos.mpr hr
    simp only [hdepth]
    rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨fun s hs hs' => mul_lt_mul_of_pos_left (h1 s hs hs') hri,
        fun s hs hs' => mul_lt_mul_of_pos_left (h2 s hs hs') hri⟩
    · exact Or.inr ⟨fun s hs hs' => mul_lt_mul_of_pos_left (h1 s hs hs') hri,
        fun s hs hs' => mul_lt_mul_of_pos_left (h2 s hs hs') hri⟩

/-! ### Lemma 7.4 by edges, with the feet of the double normal -/

/-- **No feet along `l`**: no point of the edge `j` minus a point of the edge `i` is a
nonzero multiple of `l`.  For a direction `l` normal to a plane and two edges parallel to
it, this says that the orthogonal projections of the edges onto the plane are disjoint, so
no horizontal double normal between them along `l` occurs at any view in the plane. -/
def NoFeet {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (i j : ZMod k) (l : ℝ³) : Prop :=
  ¬ ∃ Y ∈ segment ℝ (x i) (x (i + 1)), ∃ Y' ∈ segment ℝ (x j) (x (j + 1)), ∃ r : ℝ,
    r ≠ 0 ∧ Y' - Y = r • l

/-- **Lemma 7.4 by edges, with feet.**  As `exists_pairDir_of_hdn`; moreover the double
normal runs along the bad direction `l`: a point of the edge `j` minus a point of the edge
`i` is a nonzero multiple of `l` (`¬ NoFeet`). -/
theorem exists_pairDir_of_hdn' {k : ℕ} [NeZero k] (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : R ∈ SO3)
    (x : ZMod k → ℝ³)
    (h : HasHorizontalDoubleNormal (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2)) :
    ∃ i j, ¬ EdgesApart (fun m => (R.toEuclideanLin (x m)) 2) i j ∧
      ∃ l ∈ pairDirs x i j, (R.toEuclideanLin l) 2 = 0 ∧ ¬ NoFeet x i j l := by
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
  have hfeet : ∀ l : ℝ³, ∀ r : ℝ, r ≠ 0 → h = r • l → ¬ NoFeet x i j l :=
    fun l r hr hl hnf => hnf ⟨_, hY, _, hY', r, hr, hl⟩
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
          by rw [← hp]; exact hhor, hfeet _ 1 one_ne_zero (by rw [hp, one_smul])⟩
      · have hσ₂0 : σ₂ ≠ 0 := by rintro rfl; rw [zero_smul] at hσ₂; exact hdc hσ₂
        rw [hσ₂, perpTo_smul_right _ _ hσ₂0] at hp
        rw [hp] at hh0
        exact ⟨_, mem_pairDirs_of x hm hn (Or.inl rfl) hh0, by rw [← hp]; exact hhor,
          hfeet _ 1 one_ne_zero (by rw [hp, one_smul])⟩
    · have hσ₁0 : σ₁ ≠ 0 := by rintro rfl; rw [zero_smul] at hσ₁; exact hba hσ₁
      obtain ⟨κ, hk⟩ : ∃ κ : ℝ, d - x n = κ • (b - x m) := ⟨_, eq_smul_of_cross_eq_zero hba hcr⟩
      have hp : h = perpTo (x n - x m) (b - x m) := perpTo_eq (t * κ - s)
        (by rw [hhdef, hk]; module) hs
      rw [hσ₁, perpTo_smul_right _ _ hσ₁0] at hp
      have hp' : -h = perpTo (x m - x n) (x (i + 1) - x i) := by
        rw [hp, ← perpTo_neg_left, neg_sub]
      refine ⟨-h, mem_pairDirs_of x hm hn (Or.inr (Or.inl hp')) (neg_ne_zero.mpr hh0), ?_,
        hfeet _ (-1) (by norm_num) (by rw [neg_one_smul, neg_neg])⟩
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
      hfeet _ _ hκ0 (by rw [hκ, hcr', smul_smul])⟩
    have h1 := inner_cross_eq_zero_of_perp hh0 hs ht' (by rw [← hrow]; exact hhor)
    rw [hcr', real_inner_smul_left] at h1
    rw [hrow]
    exact (mul_eq_zero.mp h1).resolve_left hσ

/-- **No persistent horizontal double normal along a face circle, refined.**  As
`NoBadNormal`, but a bad direction normal to the plane of `u₀` and `e` is allowed when no
double normal along it can occur between the two edges (`NoFeet`). -/
def NoBadNormalR {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (u₀ e : ℝ³) : Prop :=
  ∀ i j, ¬ EdgesApart (fun m => ⟪x m, u₀⟫) i j → ∀ l ∈ pairDirs x i j,
    ⟪l, u₀⟫ ≠ 0 ∨ ⟪l, e⟫ ≠ 0 ∨ NoFeet x i j l

theorem NoBadNormal.toR {k : ℕ} [NeZero k] {x : ZMod k → ℝ³} {u₀ e : ℝ³}
    (h : NoBadNormal x u₀ e) : NoBadNormalR x u₀ e := fun i j hov l hl =>
  (h i j hov l hl).elim Or.inl fun h' => Or.inr (Or.inl h')

/-- `NoBadNormalR` depends only on the plane of `u₀` and `e`. -/
theorem NoBadNormalR.of_span {k : ℕ} [NeZero k] {x : ZMod k → ℝ³} {u₀ e e' : ℝ³}
    (h : NoBadNormalR x u₀ e) (α β : ℝ) (he : e = α • u₀ + β • e') : NoBadNormalR x u₀ e' := by
  intro i j hov l hl
  rcases h i j hov l hl with h1 | h1 | h1
  · exact Or.inl h1
  · by_cases h0 : ⟪l, u₀⟫ = 0
    · refine Or.inr (Or.inl fun h2 => h1 ?_)
      rw [he, inner_add_right, real_inner_smul_right, real_inner_smul_right, h0, h2]; ring
    · exact Or.inl h0
  · exact Or.inr (Or.inr h1)

/-! ### Proposition 8.8 at a view and along a slide -/

/-- **Proposition 8.8 at a view given by determinant tests, unimodal or depth-separated.**
As `isRupert_of_chordView`, with Theorem 7.3 (distinct unimodal depths) or Theorem 8.10 (a
depth-separated pair, `DepthSepAt`), and double normals excluded through `pairDirs` and
`NoFeet`. -/
theorem isRupert_of_chordViewG (V M : Finset ℝ³) (u : ℝ³) (hu : u ≠ 0) {k : ℕ} [NeZero k]
    (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V) (hxM : ∀ i, x i ∉ M) (hk : 3 ≤ k)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (x (i + 1) - x i) (x j - x i) u)
    (hrest : ∀ y ∈ V, y ∉ M → (∀ j, y ≠ x j) → ∀ i, 0 < det3 (x (i + 1) - x i) (y - x i) u)
    (hshape : IsCyclicUnimodal (fun i => ⟪x i, u⟫) ∨ ∃ a c : ZMod k, DepthSepAt x u a c)
    (hnd : ∀ i j, ¬ EdgesApart (fun m => ⟪x m, u⟫) i j → ∀ l ∈ pairDirs x i j,
      ⟪l, u⟫ ≠ 0 ∨ NoFeet x i j l)
    (hM : ∀ m ∈ M, ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = x i + s • (x (i + 1) - x i) + δ • u) : IsRupert V := by
  classical
  obtain ⟨R, hR, r, hr, hRu⟩ := exists_rotation_to_ez_pos u hu
  have hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))) := by
    refine ⟨hk, fun i j hi hj => ?_⟩
    simp only [proj_rot_sub]
    exact cross2_proj_rot_pos hR hr hRu (hcyc i j hi hj)
  have hdepth := depth_rot hR hr.ne' hRu
  have hin : ∀ v ∈ V, v ∉ M → (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))) := by
    intro y hy hyM hyx
    refine hp.mem_interior_of_left fun i => ?_
    simp only [proj_rot_sub]
    exact cross2_proj_rot_pos hR hr hRu (hrest y hy hyM hyx i)
  have hhdn : ¬ HasHorizontalDoubleNormal (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2) := by
    intro h
    obtain ⟨i, j, hov, l, hl, hl0, hfeet⟩ := exists_pairDir_of_hdn' R hR x h
    simp only [hdepth] at hov
    rw [hdepth] at hl0
    rcases hnd i j (fun h' => hov ((EdgesApart.smul_iff (inv_ne_zero hr.ne')).mpr h')) l hl
      with h1 | h1
    · exact h1 ((mul_eq_zero.mp hl0).resolve_left (inv_ne_zero hr.ne'))
    · exact hfeet h1
  rcases hshape with hz | ⟨a, c, hds⟩
  · refine isRupert_of_chords_unimodal V M R hR hr hRu x hxV hxM hp hin ?_ hhdn hM
    simp only [hdepth]; exact hz.smul (inv_pos.mpr hr)
  · exact isRupert_of_chords_depthSeparated V M R hR hr hRu x hxV hxM hp hin
      (isDepthSeparatedPair_of_depthSepAt hR hr hRu x hk hcyc hds) hhdn hM

/-- **`isRupert_of_chordViewG` in either orientation** (all tests of the sign of `ρ`). -/
theorem isRupert_of_chordViewG_or (V M : Finset ℝ³) (u : ℝ³) (hu : u ≠ 0) {k : ℕ}
    [NeZero k] (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V) (hxM : ∀ i, x i ∉ M) (hk : 3 ≤ k)
    (ρ : ℝ) (hρ : ρ ≠ 0)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < ρ * det3 (x (i + 1) - x i) (x j - x i) u)
    (hrest : ∀ y ∈ V, y ∉ M → (∀ j, y ≠ x j) → ∀ i,
      0 < ρ * det3 (x (i + 1) - x i) (y - x i) u)
    (hshape : IsCyclicUnimodal (fun i => ⟪x i, u⟫) ∨ ∃ a c : ZMod k, DepthSepAt x u a c)
    (hnd : ∀ i j, ¬ EdgesApart (fun m => ⟪x m, u⟫) i j → ∀ l ∈ pairDirs x i j,
      ⟪l, u⟫ ≠ 0 ∨ NoFeet x i j l)
    (hM : ∀ m ∈ M, ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = x i + s • (x (i + 1) - x i) + δ • u) : IsRupert V := by
  classical
  rcases lt_or_gt_of_ne hρ with hn | hp
  · refine isRupert_of_chordViewG V M (-u) (neg_ne_zero.mpr hu) x hxV hxM hk ?_ ?_ ?_ ?_ ?_
    · intro i j hi hj
      rw [det3_neg_right']; have := hcyc i j hi hj; nlinarith
    · intro y hy hyM hyx i
      rw [det3_neg_right']; have := hrest y hy hyM hyx i; nlinarith
    · rcases hshape with hz | ⟨a, c, hds⟩
      · left; simp only [inner_neg_right]; exact hz.neg' (by omega)
      · exact Or.inr ⟨a, c, hds.neg⟩
    · intro i j hov l hl
      rw [inner_neg_right, neg_ne_zero]
      refine hnd i j (fun h' => hov ?_) l hl
      have := (EdgesApart.smul_iff (z := fun m => ⟪x m, u⟫) (i := i) (j := j)
        (c := -1) (by norm_num)).mpr h'
      simpa only [inner_neg_right, neg_one_mul] using this
    · intro m hm
      obtain ⟨i, s, δ, hs0, hs1, hδ, rfl⟩ := hM m hm
      exact ⟨i, s, -δ, hs0, hs1, neg_ne_zero.mpr hδ, by rw [neg_smul, smul_neg, neg_neg]⟩
  · exact isRupert_of_chordViewG V M u hu x hxV hxM hk
      (fun i j hi hj => pos_of_mul_pos_right (hcyc i j hi hj) hp.le)
      (fun y hy hyM hyx i => pos_of_mul_pos_right (hrest y hy hyM hyx i) hp.le) hshape hnd hM

/-- **Sliding along a face circle, general form** (Lemmas C, H (c), X).  As
`isRupert_of_slide`, with `NoBadNormalR` (a double normal along a direction normal to the
plane is excluded by its feet), and along the slide either unimodal distinct depths or a
depth-separated pair. -/
theorem isRupert_of_slideG (V M : Finset ℝ³) (u₀ e : ℝ³) (hu₀ : u₀ ≠ 0) {k : ℕ} [NeZero k]
    (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V) (hxM : ∀ i, x i ∉ M) (hxinj : Function.Injective x)
    (hk : 3 ≤ k) (ρ : ℝ) (hρ : ρ ≠ 0)
    (hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (∀ i j, j ≠ i → j ≠ i + 1 → 0 < ρ * det3 (x (i + 1) - x i) (x j - x i) (u₀ + t • e)) ∧
      (∀ y ∈ V, y ∉ M → (∀ j, y ≠ x j) → ∀ i,
        0 < ρ * det3 (x (i + 1) - x i) (y - x i) (u₀ + t • e)) ∧
      (∀ m ∈ M, ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
        m = x i + s • (x (i + 1) - x i) + δ • (u₀ + t • e)) ∧
      ((Function.Injective (fun i => ⟪x i, u₀ + t • e⟫) →
          IsCyclicUnimodal (fun i => ⟪x i, u₀ + t • e⟫)) ∨
        ∃ a c : ZMod k, DepthSepAt x (u₀ + t • e) a c))
    (hbad : NoBadNormalR x u₀ e) : IsRupert V := by
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
  have hpair : ∀ i j : ZMod k, ∀ᶠ t in 𝓝[>] (0 : ℝ),
      EdgesApart (fun m => ⟪x m, u₀ + t • e⟫) i j ∨
        ∀ l ∈ pairDirs x i j, ⟪l, u₀ + t • e⟫ ≠ 0 ∨ NoFeet x i j l := by
    intro i j
    by_cases hov : EdgesApart (fun m => ⟪x m, u₀⟫) i j
    · simp only [EdgesApart] at hov
      rcases hov with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
      · filter_upwards [hlt _ _ h1, hlt _ _ h2, hlt _ _ h3, hlt _ _ h4] with t g1 g2 g3 g4
        exact Or.inl (Or.inl ⟨g1, g2, g3, g4⟩)
      · filter_upwards [hlt _ _ h1, hlt _ _ h2, hlt _ _ h3, hlt _ _ h4] with t g1 g2 g3 g4
        exact Or.inl (Or.inr ⟨g1, g2, g3, g4⟩)
    · have : ∀ l ∈ pairDirs x i j,
          ∀ᶠ t in 𝓝[>] (0 : ℝ), ⟪l, u₀ + t • e⟫ ≠ 0 ∨ NoFeet x i j l := by
        intro l hl
        rcases hbad i j hov l hl with h | h | h
        · filter_upwards [hev1 l (Or.inl h)] with t ht using Or.inl ht
        · filter_upwards [hev1 l (Or.inr h)] with t ht using Or.inl ht
        · filter_upwards with t using Or.inr h
      filter_upwards [(eventually_all_finset _).mpr this] with t ht using Or.inr ht
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
      · have hov : ¬ EdgesApart (fun m => ⟪x m, u₀⟫) j i := by
          have hz : ⟪x i, u₀⟫ = ⟪x j, u₀⟫ := by rw [inner_sub_left] at h0; linarith
          simp only [EdgesApart]
          rintro (⟨g1, -, -, -⟩ | ⟨g1, -, -, -⟩) <;> linarith
        have hmem := mem_pairDirs_of x (i := j) (j := i) (m := j) (n := i) (Or.inl rfl)
          (Or.inl rfl) (Or.inr (Or.inr rfl)) (sub_ne_zero.mpr (hxinj.ne hij))
        have hfeet : ¬ NoFeet x j i (x i - x j) := fun h =>
          h ⟨x j, left_mem_segment ℝ _ _, x i, left_mem_segment ℝ _ _, 1, one_ne_zero,
            by rw [one_smul]⟩
        rcases hbad j i hov _ hmem with h | h | h
        · filter_upwards [hev1 _ (Or.inl h)] with t ht _ using ht
        · filter_upwards [hev1 _ (Or.inr h)] with t ht _ using ht
        · exact absurd h hfeet
      · filter_upwards [hev1 _ (Or.inl h0)] with t ht _ using ht
  obtain ⟨t, ⟨⟨hcyc, hrest, hM, hz⟩, hu, hdi⟩, hnd⟩ :=
    ((hev.and (hne.and hinj)).and (eventually_all.mpr fun i => eventually_all.mpr
      fun j => hpair i j)).exists
  refine isRupert_of_chordViewG_or V M (u₀ + t • e) hu x hxV hxM hk ρ hρ hcyc hrest ?_
    (fun i j hov => (hnd i j).resolve_left hov) hM
  rcases hz with hz | hds
  · refine Or.inl (hz fun i j hij => ?_)
    by_contra hne'
    exact hdi i j hne' (by rw [inner_sub_left]; exact sub_eq_zero.mpr hij)
  · exact Or.inr hds

/-- A product of two affine functions of `t`, negative at `0`, stays negative for small
`t > 0`. -/
theorem eventually_mul_affine_neg {A B C D : ℝ} (h : A * C < 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), (A + t * B) * (C + t * D) < 0 := by
  have hc : Continuous fun t : ℝ => (A + t * B) * (C + t * D) := by fun_prop
  have h0 : (fun t : ℝ => (A + t * B) * (C + t * D)) 0 < 0 := by simpa using h
  exact ((hc.tendsto 0).eventually_lt_const h0).filter_mono nhdsWithin_le_nhds

/-- **A depth-separated pair at `u₀` persists along the slide** (all its inequalities are
strict). -/
theorem eventually_depthSepAt {k : ℕ} [NeZero k] {x : ZMod k → ℝ³} {u₀ e : ℝ³} {a c : ZMod k}
    (h : DepthSepAt x u₀ a c) : ∀ᶠ t in 𝓝[>] (0 : ℝ), DepthSepAt x (u₀ + t • e) a c := by
  classical
  obtain ⟨hn, hz⟩ := h
  have hlin : ∀ l : ℝ³, ∀ t : ℝ, ⟪l, u₀ + t • e⟫ = ⟪l, u₀⟫ + t * ⟪l, e⟫ := by
    intro l t; rw [inner_add_right, real_inner_smul_right]
  have hlt : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i j : ZMod k, ⟪x i, u₀⟫ < ⟪x j, u₀⟫ →
      ⟪x i, u₀ + t • e⟫ < ⟪x j, u₀ + t • e⟫ := by
    refine eventually_all.mpr fun i => eventually_all.mpr fun j => ?_
    by_cases hij : ⟪x i, u₀⟫ < ⟪x j, u₀⟫
    · filter_upwards [eventually_pos_affine (A := ⟪x j, u₀⟫ - ⟪x i, u₀⟫)
        (B := ⟪x j, e⟫ - ⟪x i, e⟫) (Or.inl (by linarith))] with t ht _
      rw [hlin, hlin]; linarith
    · filter_upwards with t h using absurd h hij
  have hdet : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j, j ≠ c →
      det3 (x (a + 1) - x a) (x j - x c) (u₀ + t • e) *
        det3 (x (a + 1) - x a) (x c - x a) (u₀ + t • e) < 0 := by
    refine eventually_all.mpr fun j => ?_
    by_cases hj : j = c
    · filter_upwards with t h using absurd hj h
    · filter_upwards [eventually_mul_affine_neg (B := det3 (x (a + 1) - x a) (x j - x c) e)
        (D := det3 (x (a + 1) - x a) (x c - x a) e) (hn j hj)] with t ht _
      rw [det3_add_smul, det3_add_smul]; exact ht
  filter_upwards [hlt, hdet] with t ht hd
  refine ⟨hd, ?_⟩
  rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨fun s hs hs' => ht _ _ (h1 s hs hs'), fun s hs hs' => ht _ _ (h2 s hs hs')⟩
  · exact Or.inr ⟨fun s hs hs' => ht _ _ (h1 s hs hs'), fun s hs hs' => ht _ _ (h2 s hs hs')⟩

/-- **The rim condition of the slides of Lemma H**: at the edge view `u₀` the rim is
strictly unimodal (Theorem 7.3 along the slide), or it has a depth-separated pair
(Theorem 8.10 along the slide; Lemma H (c)). -/
def UniOrSep {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (u : ℝ³) : Prop :=
  StrictUnimodal (fun i => ⟪x i, u⟫) ∨ ∃ a c : ZMod k, DepthSepAt x u a c

/-- **The slide from the tests at `u₀`** (as `isRupert_of_slide''`; a vertex may poke out
along the slide): the rim is strictly unimodal or has a depth-separated pair at `u₀`
(`UniOrSep`), and `NoBadNormalR` holds along the circle. -/
theorem isRupert_of_slide_uos (V M : Finset ℝ³) (u₀ e : ℝ³) (hu₀ : u₀ ≠ 0) {k : ℕ} [NeZero k]
    (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V) (hxM : ∀ i, x i ∉ M) (hxinj : Function.Injective x)
    (hk : 3 ≤ k) (ρ : ℝ) (hρ : ρ ≠ 0)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → SlideTest ρ (x (i + 1) - x i) (x j - x i) u₀ e)
    (hrest : ∀ y ∈ V, y ∉ M → (∀ j, y ≠ x j) → ∀ i,
      SlideTest ρ (x (i + 1) - x i) (y - x i) u₀ e)
    (hM : ∀ m ∈ M, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = x i + s • (x (i + 1) - x i) + δ • (u₀ + t • e))
    (hz : UniOrSep x u₀) (hbad : NoBadNormalR x u₀ e) : IsRupert V := by
  classical
  refine isRupert_of_slideG V M u₀ e hu₀ x hxV hxM hxinj hk ρ hρ ?_ hbad
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
  filter_upwards [h1, h2, h3, h4] with t ht1 ht2 ht3 ht4
  exact ⟨ht1, fun y hy hyM hyx i => ht2 y hy i hyM hyx, ht3, ht4⟩

end Minimality

end
