module

public import Minimality.Type29Pair

@[expose] public section

/-!
# Type 29: a helper for the TRI29L triple instances

For two facets without a common vertex the rim tilt of a non-edge view `cross a b` needs the Gram
determinant of the two normals. It is nonzero as soon as some vector has a nonzero inner product
with the view (Lagrange identity `‖a × b‖² = ‖a‖² ‖b‖² - ⟪a, b⟫²`).
-/

set_option autoImplicit false

open scoped RealInnerProductSpace
open Minimality

namespace Minimality.PL29

/-- If `w = a × b` has a nonzero inner product with some vector, the Gram determinant of `a`, `b`
is nonzero. -/
theorem gram_ne_of_cross {a b w t : ℝ³} (hw : w = cross a b) (h : ⟪t, w⟫ ≠ 0) :
    ⟪a, a⟫ * ⟪b, b⟫ - ⟪a, b⟫ ^ 2 ≠ 0 := by
  intro hG
  have h1 : ⟪cross a b, cross a b⟫ = ⟪a, a⟫ * ⟪b, b⟫ - ⟪a, b⟫ ^ 2 := by
    simp only [cross, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring
  rw [hG] at h1
  have h2 : cross a b = 0 := inner_self_eq_zero.mp h1
  apply h
  rw [hw, h2, inner_zero_right]

end Minimality.PL29
