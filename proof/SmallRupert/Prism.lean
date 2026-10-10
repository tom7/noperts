module

public import SmallRupert.Octahedron

@[expose] public section

/-!
# Theorem 7.7: translation prisms

`K = T + [0, w]` over a triangle `T = ABC`.  At suitable views the silhouette
is the pentagon `X Z Y (Y + w) (X + w)` with `Z + w` hidden, and its depths
`x, ζ, y, y + δ, x + δ` (`δ = u·w > 0`) are unimodal iff `ζ < max(x, y)`.
-/

namespace SmallRupert

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- **Theorem 7.7 (translation prisms).**  `K = T + [0, w]` for a triangle
`T = ABC` and `w` not parallel to its plane.  If `w` is not perpendicular to
the plane of `T`, or `T` has an obtuse angle, `K` is Rupert.  (Right prisms over
non-obtuse triangles remain open.) -/
theorem isRupert_translationPrism (A B C w : ℝ³) (hind : AffineIndependent ℝ ![A, B, C, A + w])
    (h : ⟪w, B - A⟫ ≠ 0 ∨ ⟪w, C - A⟫ ≠ 0 ∨ ⟪B - A, C - A⟫ < 0 ∨ ⟪A - B, C - B⟫ < 0 ∨
      ⟪A - C, B - C⟫ < 0) :
    IsRupert {A, B, C, A + w, B + w, C + w} := by
  sorry

end SmallRupert

end
