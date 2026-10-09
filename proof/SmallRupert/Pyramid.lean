module

public import SmallRupert.Coplanar

@[expose] public section

/-!
# Corollaries 5.3 and 5.4: pyramids and segments crossing a plane

* `isRupert_of_pyramid` (Cor. 5.3): all points but one coplanar.
* `isRupert_of_segment_crossing` (Cor. 5.4, bipyramid lemma): the points off
  the plane are `D` and `E`, and the segment `DE` crosses the relative
  interior of `F₀`.

Cor. 5.4 is stated with its *conclusion-ready* hypothesis "segment `DE` meets
`relint F₀`" instead of LEMMAS.md's "`D`, `E` on opposite sides of `Π`, not
on a common face of `K`".  The latter implies the former only through two
polytope facts not in Mathlib (a plane section is the hull of the vertices
and edge crossings in it; an open segment on no proper face lies in
`int K`), and the crossing form is what the ≤ 5-vertex proof produces
directly (via Radon's theorem).
-/

namespace SmallRupert

open scoped RealInnerProductSpace

/-- The view `u = c - E` from the apex through a relative-interior point `c`
of the base is admissible. -/
theorem sub_mem_admissibleViews_of_pyramid (V : Finset ℝ³) (E : ℝ³)
    (hE : E ∉ affineSpan ℝ ((V.erase E : Finset ℝ³) : Set ℝ³)) (c : ℝ³)
    (hc : c ∈ intrinsicInterior ℝ (convexHull ℝ ((V.erase E : Finset ℝ³) : Set ℝ³))) :
    c - E ∈ admissibleViews V (V.erase E) := by
  sorry

/-- **Corollary 5.3 (pyramids).** If all points of `V` but one are coplanar
(and `conv V` is solid), `V` is Rupert. -/
theorem isRupert_of_pyramid (V : Finset ℝ³) (E : ℝ³)
    (hint : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty)
    (hplane : Coplanar ℝ ((V.erase E : Finset ℝ³) : Set ℝ³)) :
    IsRupert V := by
  sorry

/-- **Corollary 5.4 (bipyramid lemma), crossing form.** If every point of
`V \ W` is `D` or `E`, `D` is off the plane of `W`, and the segment `DE` meets
`relint (conv W)`, then `u = E - D` is admissible and `V` is Rupert. -/
theorem isRupert_of_segment_crossing (V W : Finset ℝ³) (D E : ℝ³) (hWV : W ⊆ V)
    (hVW : ∀ v ∈ V, v ∉ W → v = D ∨ v = E) (hW : ¬ Collinear ℝ (W : Set ℝ³))
    (hD : D ∉ affineSpan ℝ (W : Set ℝ³))
    (hX : (segment ℝ D E ∩ intrinsicInterior ℝ (convexHull ℝ (W : Set ℝ³))).Nonempty) :
    IsRupert V := by
  sorry

/-- **Bipyramid theorem** (Tom's challenge; Cor. 5.4 with the waist in
`z = 0`).  `P` is a finite set in the plane `z = 0`, `D` is above and `E`
below it, and the point `X = D + (D₂ / (D₂ - E₂)) (E - D)` where the segment
`DE` crosses the plane projects into the interior of the waist polygon
`conv (proj_xy P)`.  Then `insert D (insert E P)` is Rupert, for any number of
waist points.  (The view `E - D` itself may be face-on, `g = 0`; the proof
uses a slightly tilted generic view, via `isRupert_of_segment_crossing`.) -/
theorem isRupert_bipyramid (P : Finset ℝ³) (hP : ∀ p ∈ P, p 2 = 0) (D E : ℝ³)
    (hD : 0 < D 2) (hE : E 2 < 0)
    (hX : proj_xy (D + (D 2 / (D 2 - E 2)) • (E - D)) ∈
      interior (convexHull ℝ ((P.image proj_xy : Finset ℝ²) : Set ℝ²))) :
    IsRupert (insert D (insert E P)) := by
  sorry

end SmallRupert

end
