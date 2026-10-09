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

/-- **L3.0, finiteness (form used in L4).** A double normal of the hull of a
finite set `W` is either parallel to `w' - w`, or perpendicular to `w' - w`,
for two distinct points `w, w'` of `W`: if the chord's end `a` is not in `W`,
the points of `W` carrying `a`'s convex weights all minimize `⟪u, ·⟫`. -/
theorem isDoubleNormalDir_convexHull_cases (W : Finset E) (u : E)
    (h : IsDoubleNormalDir (convexHull ℝ (W : Set E)) u) :
    ∃ w ∈ W, ∃ w' ∈ W, w ≠ w' ∧ ((∃ t : ℝ, w' - w = t • u) ∨ ⟪u, w' - w⟫ = 0) := by
  sorry

/-- A diameter is a double normal: every compact set with two points has a
double-normal direction. -/
theorem exists_isDoubleNormalDir {F : Set E} (hF : IsCompact F) (hF2 : F.Nontrivial) :
    ∃ u, IsDoubleNormalDir F u := by
  sorry

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
  sorry

end SmallRupert

end
