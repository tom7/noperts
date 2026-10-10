module

public import SmallRupert.Tilt

@[expose] public section

/-!
# Theorem 8.1: right prisms

Every right prism over a strictly convex polygon is Rupert, by an explicit
first-order motion at the views `e_z + εv` next to the axis (LEMMAS.md 8.1;
L7 is not used).  With Theorem 7.7 this covers every translation prism over a
triangle.
-/

namespace SmallRupert

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- The right prism over the polygon `p` (in the plane `z = 0`) of height `h`. -/
noncomputable def rightPrism {k : ℕ} [NeZero k] (p : ZMod k → ℝ²) (h : ℝ) : Finset ℝ³ := by
  classical
  exact (univ.image fun i => liftPt (p i) 0) ∪ (univ.image fun i => liftPt (p i) h)

/-- **Theorem 8.1.**  Every right prism over a strictly convex polygon is
Rupert. -/
theorem isRupert_rightPrism {k : ℕ} [NeZero k] (p : ZMod k → ℝ²) (hp : IsCcwPolygon p) {h : ℝ}
    (hh : 0 < h) : IsRupert (rightPrism p h) := by
  sorry

/-- Right translation prisms over a triangle, in any position. -/
theorem isRupert_translationPrism_right (A B C w : ℝ³)
    (hind : AffineIndependent ℝ ![A, B, C, A + w]) (hB : ⟪w, B - A⟫ = 0) (hC : ⟪w, C - A⟫ = 0) :
    IsRupert {A, B, C, A + w, B + w, C + w} := by
  sorry

/-- **Every translation prism over a triangle is Rupert** (Theorems 7.7 and
8.1). -/
theorem isRupert_translationPrism_all (A B C w : ℝ³)
    (hind : AffineIndependent ℝ ![A, B, C, A + w]) : IsRupert {A, B, C, A + w, B + w, C + w} := by
  by_cases h : ⟪w, B - A⟫ ≠ 0 ∨ ⟪w, C - A⟫ ≠ 0
  · rcases h with h | h
    · exact isRupert_translationPrism A B C w hind (Or.inl h)
    · exact isRupert_translationPrism A B C w hind (Or.inr (Or.inl h))
  · push Not at h
    exact isRupert_translationPrism_right A B C w hind h.1 h.2

end SmallRupert

end
