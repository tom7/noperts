module

public import SmallRupert.Crossing
public import Mathlib.Analysis.Convex.Radon

@[expose] public section

/-!
# Corollary 5.6: every convex polyhedron with at most 5 vertices is Rupert

Proof plan (differs from LEMMAS.md, which goes through the combinatorial
types and the cone lemma 5.5): replace `V` by its extreme points (same hull,
`isRupert_congr_hull`); there are 4 or 5 of them.
* 4 points, or 5 points with 4 coplanar: a pyramid (`isRupert_of_pyramid`).
* 5 points, no 4 coplanar: Radon's theorem (`radon_partition`) splits them
  into two parts with intersecting hulls; a 1–4 split contradicts
  extremality, so it is a 2–3 split, the segment `DE` meets the triangle
  `ABC`, and general position puts the crossing point in both relative
  interiors.  Then `isRupert_of_segment_crossing`.
-/

namespace SmallRupert

/-- Radon step: five points in convex position, no four coplanar, contain a
segment crossing the relative interior of the triangle of the other three. -/
theorem exists_segment_crossing_of_card_eq_five (V : Finset ℝ³) (hV : V.card = 5)
    (hext : ∀ v ∈ V, v ∉ convexHull ℝ ((V.erase v : Finset ℝ³) : Set ℝ³))
    (hgen : ∀ v ∈ V, ¬ Coplanar ℝ ((V.erase v : Finset ℝ³) : Set ℝ³)) :
    ∃ D ∈ V, ∃ E ∈ V, D ≠ E ∧
      (segment ℝ D E ∩
        intrinsicInterior ℝ (convexHull ℝ (((V.erase D).erase E : Finset ℝ³) : Set ℝ³))).Nonempty := by
  sorry

/-- **Corollary 5.6.** Every convex polyhedron with at most five vertices is
Rupert.  `V` need not consist of vertices only. -/
theorem isRupert_of_card_le_five (V : Finset ℝ³) (hV : V.card ≤ 5)
    (hint : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty) : IsRupert V := by
  sorry

end SmallRupert

end
