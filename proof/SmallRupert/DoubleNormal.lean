module

public import SmallRupert.Basic

@[expose] public section

/-!
# L3 (and the transfer step of L4): double normals of a convex polygon

LEMMAS.md L3.  `F = convexHull ℝ W` for a finite `W ⊆ ℝ²` with nonempty
interior, and `u ≠ 0` a screen direction.  An affine screen field
`p ↦ M p + b` is *admissible for `u`* if `⟪u, M u⟫ = 0` (LEMMAS.md
`ûᵀMû = 0`, the image of the realizable first-order distortions, L2).

* `exists_admissible_inward_field` (L3, construction direction): if `u` is not
  a double-normal direction of `F`, some admissible field is strictly inward
  at every point of `W`.  **This is the only direction used by the Rupert
  theorems.**
* `not_forall_inward_of_isDoubleNormalDir` (L3, obstruction direction):
  optional, not needed for any Rupert theorem.
* `isDoubleNormalDir_iff_extremes`, `isDoubleNormalDir_iff_ranges` (L3.0).
* `isDoubleNormalDir_convexHull_cases` (L3.0 finiteness, in the form used by
  L4), `exists_isDoubleNormalDir` (diameters).
* `isDoubleNormalDir_proj_iff` (L4): for a planar set not containing the view
  direction, a horizontal direction in the plane is a double-normal direction
  of the set iff its projection is one of the shadow.

Note.  LEMMAS.md Cor. 3.1 (triangles) is wrong as first written: a side whose
two angles are both ≤ π/2 is a vertex–vertex double normal (e.g. every
triangle's longest side).  It is not stated here; the general definition
`IsDoubleNormalDir` covers all cases.
-/

namespace SmallRupert

open scoped RealInnerProductSpace Matrix

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **L3.0.** `u` is a double-normal direction iff some minimizer `a` and some
maximizer `b` of `⟪u, ·⟫` on `F` differ by a multiple of `u`. -/
theorem isDoubleNormalDir_iff_extremes (F : Set E) (u : E) :
    IsDoubleNormalDir F u ↔ ∃ a ∈ F, ∃ b ∈ F, IsMinOn (fun q => ⟪u, q⟫) F a ∧
      IsMaxOn (fun q => ⟪u, q⟫) F b ∧ a ≠ b ∧ ∃ t : ℝ, b - a = t • u := by
  sorry

/-- A point of `conv W` outside `W` minimizing a linear functional `ℓ` over
`W` is a combination of at least two distinct minimizers. -/
theorem exists_two_of_mem_convexHull_of_isMin (W : Finset E) (ℓ : E →ₗ[ℝ] ℝ) {x : E}
    (hx : x ∈ convexHull ℝ (W : Set E)) (hxW : x ∉ W) (hmin : ∀ y ∈ W, ℓ x ≤ ℓ y) :
    ∃ y₁ ∈ W, ∃ y₂ ∈ W, y₁ ≠ y₂ ∧ ℓ y₁ = ℓ x ∧ ℓ y₂ = ℓ x := by
  classical
  obtain ⟨w, hw0, hw1, hwx⟩ := Finset.mem_convexHull.mp hx
  set W₀ := W.filter (fun y => ℓ y = ℓ x) with hW₀
  -- the weights vanish off the level set
  have hsum : ∑ y ∈ W, w y * (ℓ y - ℓ x) = 0 := by
    have h1 : ℓ x = ∑ y ∈ W, w y * ℓ y := by
      rw [← hwx, Finset.centerMass_eq_of_sum_1 _ _ hw1, map_sum]
      simp [map_smul]
    rw [Finset.sum_congr rfl (fun y _ => mul_sub (w y) (ℓ y) (ℓ x)), Finset.sum_sub_distrib,
      ← Finset.sum_mul, hw1, one_mul, ← h1, sub_self]
  have hzero : ∀ y ∈ W, w y * (ℓ y - ℓ x) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun y hy =>
      mul_nonneg (hw0 y hy) (sub_nonneg.mpr (hmin y hy))).mp hsum
  have hoff : ∀ y ∈ W, y ∉ W₀ → w y = 0 := by
    intro y hy hy0
    have hne : ℓ y - ℓ x ≠ 0 := by
      intro h0; exact hy0 (Finset.mem_filter.mpr ⟨hy, by linarith⟩)
    exact (mul_eq_zero.mp (hzero y hy)).resolve_right hne
  have hx0 : x ∈ convexHull ℝ (W₀ : Set E) := by
    refine Finset.mem_convexHull.mpr ⟨w, fun y hy => hw0 y (Finset.filter_subset _ _ hy), ?_, ?_⟩
    · rw [← hw1]; exact Finset.sum_subset (Finset.filter_subset _ _) hoff
    · rw [← hwx]; exact Finset.centerMass_subset _ (Finset.filter_subset _ _) hoff
  by_contra hcon
  push Not at hcon
  have hcard : W₀.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro y₁ h₁ y₂ h₂
    rw [Finset.mem_filter] at h₁ h₂
    by_contra hne
    exact hcon y₁ h₁.1 y₂ h₂.1 hne h₁.2 |>.elim h₂.2
  rcases Finset.card_le_one_iff_subset_singleton.mp hcard with ⟨y, hy⟩
  have : x ∈ convexHull ℝ ({y} : Set E) :=
    convexHull_mono (by rw [← Finset.coe_singleton]; exact Finset.coe_subset.mpr hy) hx0
  rw [convexHull_singleton, Set.mem_singleton_iff] at this
  subst this
  rcases Finset.eq_empty_or_nonempty W₀ with h | h
  · rw [h, Finset.coe_empty, convexHull_empty] at hx0; exact hx0
  · obtain ⟨z, hz⟩ := h
    have := hy hz
    rw [Finset.mem_singleton] at this
    subst this
    exact hxW (Finset.filter_subset _ _ hz)

/-- **L3.0, finiteness (form used in L4).** A double normal of the hull of a
finite set `W` is either parallel to `w' - w`, or perpendicular to `w' - w`,
for two distinct points `w, w'` of `W`: if the chord's end `a` is not in `W`,
the points of `W` carrying `a`'s convex weights all minimize `⟪u, ·⟫`. -/
theorem isDoubleNormalDir_convexHull_cases (W : Finset E) (u : E)
    (h : IsDoubleNormalDir (convexHull ℝ (W : Set E)) u) :
    ∃ w ∈ W, ∃ w' ∈ W, w ≠ w' ∧ ((∃ t : ℝ, w' - w = t • u) ∨ ⟪u, w' - w⟫ = 0) := by
  obtain ⟨a, ha, b, hb, hab, ⟨t, ht⟩, hB, hA⟩ := h
  have ht0 : t ≠ 0 := by
    rintro rfl; apply hab; rw [zero_smul, sub_eq_zero] at ht; exact ht.symm
  -- `ℓ = ⟪b - a, ·⟫` is minimized at `a` and maximized at `b`
  let ℓ : E →ₗ[ℝ] ℝ := (innerₛₗ ℝ (b - a))
  have hℓ : ∀ x, ℓ x = ⟪b - a, x⟫ := fun x => rfl
  have hperp : ∀ y₁ y₂ : E, ℓ y₁ = ℓ y₂ → ⟪u, y₂ - y₁⟫ = 0 := by
    intro y₁ y₂ h
    rw [hℓ, hℓ, ht, inner_smul_left, inner_smul_left] at h
    have : ⟪u, y₂⟫ = ⟪u, y₁⟫ := by
      simpa [ht0] using h.symm
    rw [inner_sub_right, this, sub_self]
  by_cases haW : a ∈ W
  · by_cases hbW : b ∈ W
    · exact ⟨a, haW, b, hbW, hab, Or.inl ⟨t, ht⟩⟩
    · obtain ⟨y₁, h₁, y₂, h₂, hne, e₁, e₂⟩ := exists_two_of_mem_convexHull_of_isMin W (-ℓ) hb hbW
        (fun y hy => by
          have := hB y (subset_convexHull ℝ _ hy)
          simp only [LinearMap.neg_apply, hℓ, neg_le_neg_iff]
          rw [inner_sub_right] at this; linarith)
      exact ⟨y₁, h₁, y₂, h₂, hne, Or.inr (hperp _ _ (by
        simp only [LinearMap.neg_apply, neg_inj] at e₁ e₂; rw [e₁, e₂]))⟩
  · obtain ⟨y₁, h₁, y₂, h₂, hne, e₁, e₂⟩ := exists_two_of_mem_convexHull_of_isMin W ℓ ha haW
      (fun y hy => by
        have := hA y (subset_convexHull ℝ _ hy)
        rw [hℓ, hℓ]
        rw [show a - b = -(b - a) by abel, inner_neg_left, inner_sub_right] at this; linarith)
    exact ⟨y₁, h₁, y₂, h₂, hne, Or.inr (hperp _ _ (by rw [e₁, e₂]))⟩

/-- A diameter is a double normal: every compact set with two points has a
double-normal direction. -/
theorem exists_isDoubleNormalDir {F : Set E} (hF : IsCompact F) (hF2 : F.Nontrivial) :
    ∃ u, IsDoubleNormalDir F u := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hF2
  obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, hmax⟩ := (hF.prod hF).exists_isMaxOn ⟨(x, y), hx, hy⟩
    (continuous_norm.comp (continuous_snd.sub continuous_fst)).continuousOn
  have hmax' : ∀ p ∈ F, ∀ q ∈ F, ‖q - p‖ ≤ ‖b - a‖ := fun p hp q hq =>
    hmax (show (p, q) ∈ F ×ˢ F from ⟨hp, hq⟩)
  have hab : a ≠ b := by
    intro h
    have := hmax' x hx y hy
    rw [h, sub_self, norm_zero] at this
    exact hxy (by rw [← sub_eq_zero, ← norm_eq_zero]; exact le_antisymm (by
      have := norm_nonneg (y - x); linarith [norm_sub_rev x y]) (norm_nonneg _))
  refine ⟨b - a, a, ha, b, hb, hab, ⟨1, by rw [one_smul]⟩, fun q hq => ?_, fun q hq => ?_⟩
  · have h1 := hmax' a ha q hq
    have h2 : ‖q - a‖ ^ 2 = ‖q - b‖ ^ 2 + 2 * ⟪b - a, q - b⟫ + ‖b - a‖ ^ 2 := by
      rw [show q - a = (q - b) + (b - a) by abel, norm_add_sq_real, real_inner_comm]
    nlinarith [norm_nonneg (q - a), norm_nonneg (b - a), sq_nonneg ‖q - b‖]
  · have h1 := hmax' q hq b hb
    have h2 : ‖b - q‖ ^ 2 = ‖a - q‖ ^ 2 + 2 * ⟪a - b, q - a⟫ + ‖b - a‖ ^ 2 := by
      rw [show b - q = (a - q) + (b - a) by abel, norm_add_sq_real]
      rw [show a - q = -(q - a) by abel, inner_neg_left, show a - b = -(b - a) by abel,
        inner_neg_left, real_inner_comm]
    nlinarith [norm_nonneg (b - q), norm_nonneg (b - a), sq_nonneg ‖a - q‖]

end General

/-- **L3.0, planar form.** For a polygon with nonempty interior and `u ≠ 0`:
`u` is a double-normal direction iff the `rot90 u`-ranges of the faces
minimizing and maximizing `⟪u, ·⟫` overlap. -/
theorem isDoubleNormalDir_iff_ranges (W : Finset ℝ²)
    (hW : (interior (convexHull ℝ (W : Set ℝ²))).Nonempty) (u : ℝ²) (hu : u ≠ 0) :
    IsDoubleNormalDir (convexHull ℝ (W : Set ℝ²)) u ↔
      ∃ a ∈ convexHull ℝ (W : Set ℝ²), ∃ b ∈ convexHull ℝ (W : Set ℝ²),
        IsMinOn (fun q => ⟪u, q⟫) (convexHull ℝ (W : Set ℝ²)) a ∧
        IsMaxOn (fun q => ⟪u, q⟫) (convexHull ℝ (W : Set ℝ²)) b ∧
        ⟪rot90 u, a⟫ = ⟪rot90 u, b⟫ := by
  sorry

/-- **Lemma 3 (construction direction).** If `u` is not a double-normal
direction of the polygon `F = conv W`, there is an affine field
`p ↦ M p + b` with `⟪u, M u⟫ = 0` that points strictly into `F` at every
point of `W` (hence, being affine, at every point of `F`).

Construction (LEMMAS.md, coordinates `x = ⟪u, ·⟫`, `y = ⟪rot90 u, ·⟫`): squash
vertically onto a chord `[a, b]` joining the two `x`-extreme faces, plus a
small multiple of a shear `(σ(y), τ(x, y))` with `σ(y) = κ (y₀ - y)`, `y₀`
strictly between the `y`-ranges of the two extreme faces. -/
theorem exists_admissible_inward_field (W : Finset ℝ²)
    (hW : (interior (convexHull ℝ (W : Set ℝ²))).Nonempty) (u : ℝ²) (hu : u ≠ 0)
    (hnd : ¬ IsDoubleNormalDir (convexHull ℝ (W : Set ℝ²)) u) :
    ∃ (M : ℝ² →ₗ[ℝ] ℝ²) (b : ℝ²), ⟪u, M u⟫ = 0 ∧
      ∀ p ∈ W, IsInwardAt (convexHull ℝ (W : Set ℝ²)) p (M p + b) := by
  sorry

/-- **Lemma 3 (obstruction direction; optional, not used by the Rupert
theorems).** Along a double normal `[a, b]` every admissible field has
`⟪b - a, v b - v a⟫ = |b - a|² ⟪u, M u⟫ / |u|² = 0`, while inwardness at `a`
and `b` makes it negative. -/
theorem not_forall_inward_of_isDoubleNormalDir (W : Finset ℝ²)
    (hW : (interior (convexHull ℝ (W : Set ℝ²))).Nonempty) (u : ℝ²)
    (hd : IsDoubleNormalDir (convexHull ℝ (W : Set ℝ²)) u)
    (M : ℝ² →ₗ[ℝ] ℝ²) (b : ℝ²) (hM : ⟪u, M u⟫ = 0) :
    ¬ ∀ p ∈ W, IsInwardAt (convexHull ℝ (W : Set ℝ²)) p (M p + b) := by
  sorry

/-- **L4, transfer step** (standard view).  Let `F` lie in an affine subspace
`L` (LEMMAS.md's plane `Π`) whose direction does not contain the view direction `ez`, and let `δ` be a
horizontal (`δ 2 = 0`) direction of `L`.  Then `δ` is a double-normal
direction of `F` iff `proj_xy δ` is one of the shadow `proj_xy '' F`.
(`proj_xy` is injective on `L` and preserves inner products with horizontal
vectors.) -/
theorem isDoubleNormalDir_proj_iff (L : AffineSubspace ℝ ℝ³) (hL : ez ∉ L.direction)
    (F : Set ℝ³) (hF : F ⊆ (L : Set ℝ³)) (δ : ℝ³) (hδ : δ ∈ L.direction) (hδ2 : δ 2 = 0) :
    IsDoubleNormalDir F δ ↔ IsDoubleNormalDir (proj_xy '' F) (proj_xy δ) := by
  sorry

/-- **L4, transfer step, normal-vector form** (what the proofs use): `F` lies
in the plane `⟪N, x⟫ = h` with `N 2 ≠ 0` (not vertical), and `δ` is a
horizontal direction of that plane. -/
theorem isDoubleNormalDir_proj_iff' (N : ℝ³) (hN : N 2 ≠ 0) (h : ℝ) (F : Set ℝ³)
    (hF : ∀ x ∈ F, ⟪N, x⟫ = h) (δ : ℝ³) (hδ : ⟪N, δ⟫ = 0) (hδ2 : δ 2 = 0) :
    IsDoubleNormalDir F δ ↔ IsDoubleNormalDir (proj_xy '' F) (proj_xy δ) := by
  have hsub : ∀ x ∈ F, ∀ y ∈ F, ⟪N, y - x⟫ = 0 := fun x hx y hy => by
    rw [inner_sub_right, hF x hx, hF y hy, sub_self]
  constructor
  · rintro ⟨a, ha, b, hb, hab, ⟨t, ht⟩, hB, hA⟩
    have hh : (b - a) 2 = 0 := by rw [ht]; simp [hδ2]
    have hh' : (a - b) 2 = 0 := by
      rw [show a - b = -(b - a) by abel]; simp only [PiLp.neg_apply, hh, neg_zero]
    refine ⟨proj_xy a, ⟨a, ha, rfl⟩, proj_xy b, ⟨b, hb, rfl⟩, fun h => hab ?_,
      ⟨t, by rw [← proj_xy_sub', ht, proj_xy_smul']⟩, ?_, ?_⟩
    · have := eq_zero_of_proj_xy_eq_zero hN (hsub a ha b hb)
        (by rw [proj_xy_sub', h, sub_self])
      exact (sub_eq_zero.mp this).symm
    · rintro _ ⟨q, hq, rfl⟩
      rw [← proj_xy_sub', ← proj_xy_sub', inner_proj_xy_of_horizontal hh]; exact hB q hq
    · rintro _ ⟨q, hq, rfl⟩
      rw [← proj_xy_sub', ← proj_xy_sub', inner_proj_xy_of_horizontal hh']; exact hA q hq
  · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, hab, ⟨t, ht⟩, hB, hA⟩
    have hba : b - a = t • δ := by
      have := eq_zero_of_proj_xy_eq_zero (z := b - a - t • δ) hN
        (by rw [inner_sub_right, inner_smul_right, hsub a ha b hb, hδ, mul_zero, sub_zero])
        (by rw [proj_xy_sub', proj_xy_sub', proj_xy_smul', ht, sub_self])
      exact sub_eq_zero.mp this
    have hh : (b - a) 2 = 0 := by rw [hba]; simp [hδ2]
    have hh' : (a - b) 2 = 0 := by
      rw [show a - b = -(b - a) by abel]; simp only [PiLp.neg_apply, hh, neg_zero]
    refine ⟨a, ha, b, hb, fun h => hab (by rw [h]), ⟨t, hba⟩, fun q hq => ?_, fun q hq => ?_⟩
    · have := hB (proj_xy q) ⟨q, hq, rfl⟩
      rwa [← proj_xy_sub', ← proj_xy_sub', inner_proj_xy_of_horizontal hh] at this
    · have := hA (proj_xy q) ⟨q, hq, rfl⟩
      rwa [← proj_xy_sub', ← proj_xy_sub', inner_proj_xy_of_horizontal hh'] at this

end SmallRupert

end
