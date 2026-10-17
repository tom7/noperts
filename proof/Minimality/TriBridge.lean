module

public import Minimality.TriQuad

@[expose] public section

/-!
# From facets to the oblique frame (Corollary T1)

The bridge from two quadrilateral facets of a 7-point set sharing one vertex to
`isRupert_twoQuads_frame`.  First, planar: four points in a plane, no three
collinear and none in the triangle of the others, are the vertices of a convex
quadrilateral in one of six labelled orders (`convex_four`).
-/

namespace Minimality

open Finset Filter Topology
open scoped RealInnerProductSpace

/-- The orientation of three points of the plane. -/
def orient2 (x0 y0 x1 y1 x2 y2 : ℝ) : ℝ := (x1 - x0) * (y2 - y0) - (y1 - y0) * (x2 - x0)

theorem convQuad_of_orient {x0 y0 x1 y1 x2 y2 x3 y3 : ℝ}
    (h012 : 0 < orient2 x0 y0 x1 y1 x2 y2) (h013 : 0 < orient2 x0 y0 x1 y1 x3 y3)
    (h023 : 0 < orient2 x0 y0 x2 y2 x3 y3) (h123 : 0 < orient2 x1 y1 x2 y2 x3 y3) :
    ConvQuad x0 y0 x1 y1 x2 y2 x3 y3 := by
  unfold orient2 at *
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> nlinarith

/-- No point among four lies in the triangle of the other three. -/
def NotInTri (x0 y0 x1 y1 x2 y2 x3 y3 : ℝ) : Prop :=
  ¬ ∃ t0 t1 t2 : ℝ, 0 ≤ t0 ∧ 0 ≤ t1 ∧ 0 ≤ t2 ∧ t0 + t1 + t2 = 1 ∧
    x3 = t0 * x0 + t1 * x1 + t2 * x2 ∧ y3 = t0 * y0 + t1 * y1 + t2 * y2

/-- If the orientations say that `3` is inside the triangle `0, 1, 2`, it is. -/
theorem inTri_of_orient {x0 y0 x1 y1 x2 y2 x3 y3 : ℝ} (h : orient2 x0 y0 x1 y1 x2 y2 ≠ 0)
    (h0 : 0 ≤ orient2 x1 y1 x2 y2 x3 y3 / orient2 x0 y0 x1 y1 x2 y2)
    (h1 : 0 ≤ -orient2 x0 y0 x2 y2 x3 y3 / orient2 x0 y0 x1 y1 x2 y2)
    (h2 : 0 ≤ orient2 x0 y0 x1 y1 x3 y3 / orient2 x0 y0 x1 y1 x2 y2) :
    ¬ NotInTri x0 y0 x1 y1 x2 y2 x3 y3 := by
  intro hn
  apply hn
  refine ⟨_, _, _, h0, h1, h2, ?_, ?_, ?_⟩ <;> field_simp <;> unfold orient2 at * <;> ring

theorem orient2_identity (x0 y0 x1 y1 x2 y2 x3 y3 : ℝ) :
    orient2 x1 y1 x2 y2 x3 y3 - orient2 x0 y0 x2 y2 x3 y3 + orient2 x0 y0 x1 y1 x3 y3 -
      orient2 x0 y0 x1 y1 x2 y2 = 0 := by
  unfold orient2; ring

set_option maxHeartbeats 4000000 in
/-- **Four points in convex position.**  No three collinear and none in the
triangle of the others: a convex quadrilateral in one of the six labelled
orders starting at `0`. -/
theorem convex_four {x0 y0 x1 y1 x2 y2 x3 y3 : ℝ}
    (hA : orient2 x0 y0 x1 y1 x2 y2 ≠ 0) (hB : orient2 x0 y0 x1 y1 x3 y3 ≠ 0)
    (hC : orient2 x0 y0 x2 y2 x3 y3 ≠ 0) (hD : orient2 x1 y1 x2 y2 x3 y3 ≠ 0)
    (hn3 : NotInTri x0 y0 x1 y1 x2 y2 x3 y3) (hn2 : NotInTri x0 y0 x1 y1 x3 y3 x2 y2)
    (hn1 : NotInTri x0 y0 x2 y2 x3 y3 x1 y1) (hn0 : NotInTri x1 y1 x2 y2 x3 y3 x0 y0) :
    ConvQuad x0 y0 x1 y1 x2 y2 x3 y3 ∨ ConvQuad x0 y0 x3 y3 x2 y2 x1 y1 ∨
    ConvQuad x0 y0 x2 y2 x1 y1 x3 y3 ∨ ConvQuad x0 y0 x3 y3 x1 y1 x2 y2 ∨
    ConvQuad x0 y0 x1 y1 x3 y3 x2 y2 ∨ ConvQuad x0 y0 x2 y2 x3 y3 x1 y1 := by
  have hid := orient2_identity x0 y0 x1 y1 x2 y2 x3 y3
  -- the permuted orientations
  have p021 : orient2 x0 y0 x2 y2 x1 y1 = -orient2 x0 y0 x1 y1 x2 y2 := by unfold orient2; ring
  have p032 : orient2 x0 y0 x3 y3 x2 y2 = -orient2 x0 y0 x2 y2 x3 y3 := by unfold orient2; ring
  have p031 : orient2 x0 y0 x3 y3 x1 y1 = -orient2 x0 y0 x1 y1 x3 y3 := by unfold orient2; ring
  have p321 : orient2 x3 y3 x2 y2 x1 y1 = -orient2 x1 y1 x2 y2 x3 y3 := by unfold orient2; ring
  have p213 : orient2 x2 y2 x1 y1 x3 y3 = -orient2 x1 y1 x2 y2 x3 y3 := by unfold orient2; ring
  have p132 : orient2 x1 y1 x3 y3 x2 y2 = -orient2 x1 y1 x2 y2 x3 y3 := by unfold orient2; ring
  have p231 : orient2 x2 y2 x3 y3 x1 y1 = orient2 x1 y1 x2 y2 x3 y3 := by unfold orient2; ring
  have p230 : orient2 x2 y2 x3 y3 x0 y0 = orient2 x0 y0 x2 y2 x3 y3 := by unfold orient2; ring
  have p130 : orient2 x1 y1 x3 y3 x0 y0 = orient2 x0 y0 x1 y1 x3 y3 := by unfold orient2; ring
  have p120 : orient2 x1 y1 x2 y2 x0 y0 = orient2 x0 y0 x1 y1 x2 y2 := by unfold orient2; ring
  have p312 : orient2 x3 y3 x1 y1 x2 y2 = orient2 x1 y1 x2 y2 x3 y3 := by unfold orient2; ring
  rcases lt_or_gt_of_ne hA with a | a <;> rcases lt_or_gt_of_ne hB with b | b <;>
    rcases lt_or_gt_of_ne hC with c | c <;> rcases lt_or_gt_of_ne hD with d | d
  all_goals first
    | exact Or.inl (convQuad_of_orient (by linarith) (by linarith) (by linarith) (by linarith))
    | exact Or.inr (Or.inl (convQuad_of_orient (by rw [p032]; linarith) (by rw [p031]; linarith)
        (by rw [p021]; linarith) (by rw [p321]; linarith)))
    | exact Or.inr (Or.inr (Or.inl (convQuad_of_orient (by rw [p021]; linarith) (by linarith)
        (by linarith) (by rw [p213]; linarith))))
    | exact Or.inr (Or.inr (Or.inr (Or.inl (convQuad_of_orient (by rw [p031]; linarith)
        (by rw [p032]; linarith) (by linarith) (by rw [p312]; linarith)))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (convQuad_of_orient (by linarith) (by linarith)
        (by rw [p032]; linarith) (by rw [p132]; linarith))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (convQuad_of_orient (by linarith)
        (by rw [p021]; linarith) (by rw [p031]; linarith) (by rw [p231]; linarith))))))
    | exact absurd hn3 (inTri_of_orient hA (by first | exact div_nonneg (by linarith) (by linarith) | exact div_nonneg_of_nonpos (by linarith) (by linarith)) (by first | exact div_nonneg (by linarith) (by linarith) | exact div_nonneg_of_nonpos (by linarith) (by linarith)) (by first | exact div_nonneg (by linarith) (by linarith) | exact div_nonneg_of_nonpos (by linarith) (by linarith)))
    | exact absurd hn2 (inTri_of_orient hB (by rw [p132]; (first | exact div_nonneg (by linarith) (by linarith) | exact div_nonneg_of_nonpos (by linarith) (by linarith))) (by rw [p032]; (first | exact div_nonneg (by linarith) (by linarith) | exact div_nonneg_of_nonpos (by linarith) (by linarith))) (by first | exact div_nonneg (by linarith) (by linarith) | exact div_nonneg_of_nonpos (by linarith) (by linarith)))
    | exact absurd hn1 (inTri_of_orient hC (by rw [p231]; (first | exact div_nonneg (by linarith) (by linarith) | exact div_nonneg_of_nonpos (by linarith) (by linarith))) (by rw [p031]; (first | exact div_nonneg (by linarith) (by linarith) | exact div_nonneg_of_nonpos (by linarith) (by linarith)))
        (by rw [p021]; (first | exact div_nonneg (by linarith) (by linarith) | exact div_nonneg_of_nonpos (by linarith) (by linarith))))
    | exact absurd hn0 (inTri_of_orient hD (by rw [p230]; (first | exact div_nonneg (by linarith) (by linarith) | exact div_nonneg_of_nonpos (by linarith) (by linarith))) (by rw [p130]; (first | exact div_nonneg (by linarith) (by linarith) | exact div_nonneg_of_nonpos (by linarith) (by linarith)))
        (by rw [p120]; (first | exact div_nonneg (by linarith) (by linarith) | exact div_nonneg_of_nonpos (by linarith) (by linarith))))

end Minimality

end
