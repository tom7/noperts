module

public import Minimality.TieFrame
public import Minimality.ParallelFacets

@[expose] public section

/-!
# Lemma T views under either general position

The views of the per-type theorems accept either the tie-tolerant general
position (`TriGenTie`, `EdgeTieR`: no segment parallel to the view line) or
the parallel-tolerant one (`TriGenFarP`, `EdgeFarP`: distinct far depths, one
far end a single vertex). A segment parallel to the view line then matters
only together with a far tie (codimension 3). FEWER-FACES.md §11.
-/

namespace Minimality

/-- **Lemma T over a vertex, either general position.** -/
theorem isRupert_of_facets_vertex_tie_or (V : Finset ℝ³) (hgen : NoThreeCollinear V)
    (Q1 Q2 : Finset ℝ³) (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (h1f : IsFacet V Q1) (h2f : IsFacet V Q2)
    (v : ℝ³) (hint : Q1 ∩ Q2 = {v}) (hne1 : ∃ p ∈ Q1, p ≠ v) (hne2 : ∃ p ∈ Q2, p ≠ v)
    (hT : TriGenTie V Q1 Q2 v ∨ TriGenFarP V Q1 Q2 v)
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ≠ v ∧ xb ≠ v ∧ ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ,
      (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
      (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1) : IsRupert V := by
  rcases hT with hT | hT
  · exact isRupert_of_facets_vertex_tie V hgen Q1 Q2 h1V h2V h1f h2f v hint hne1 hne2 hT hin
  · exact isRupert_of_facets_vertex_par V hgen Q1 Q2 h1V h2V h1f h2f v hint hne1 hne2 hT hin

/-- **Lemma T over an edge, either general position.** -/
theorem isRupert_of_facets_edge_tieR_or (V : Finset ℝ³) (hgen : NoThreeCollinear V)
    (Q1 Q2 : Finset ℝ³) (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (h1f : IsFacet V Q1) (h2f : IsFacet V Q2)
    (v w : ℝ³) (hvw : v ≠ w) (hint : Q1 ∩ Q2 = {v, w})
    (hne1 : ∃ p ∈ Q1, p ∉ Q2) (hne2 : ∃ p ∈ Q2, p ∉ Q1)
    (hfarZ : EdgeTieR V Q1 Q2 v w ∨ EdgeFarP V Q1 Q2 v w)
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ∉ Q2 ∧ xb ∉ Q1 ∧ ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ,
      (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
      (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1)
    (hsol : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty) : IsRupert V := by
  rcases hfarZ with h | h
  · exact isRupert_of_facets_edge_tieR V hgen Q1 Q2 h1V h2V h1f h2f v w hvw hint hne1 hne2 h hin hsol
  · exact isRupert_of_facets_edge_par V hgen Q1 Q2 h1V h2V h1f h2f v w hvw hint hne1 hne2 h hin

/-- **Lemma T over an edge with a triangle face, either general position**
(`EdgePar`: no other segment parallel to the edge; or `EdgeFarP`). -/
theorem isRupert_of_facets_edge_tri_or (V : Finset ℝ³) (hgen : NoThreeCollinear V)
    (Q1 Q2 : Finset ℝ³) (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (h1f : IsFacet V Q1) (h2f : IsFacet V Q2)
    (v w : ℝ³) (hvw : v ≠ w) (hint : Q1 ∩ Q2 = {v, w})
    (hne1 : ∃ p ∈ Q1, p ∉ Q2) (hne2 : ∃ p ∈ Q2, p ∉ Q1)
    (hcard : Q1.card = 3 ∨ Q2.card = 3) (hpar : EdgePar V v w ∨ EdgeFarP V Q1 Q2 v w)
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ∉ Q2 ∧ xb ∉ Q1 ∧ ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ,
      (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
      (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1) : IsRupert V := by
  rcases hpar with h | h
  · exact isRupert_of_facets_edge_tri V hgen Q1 Q2 h1V h2V h1f h2f v w hvw hint hne1 hne2 hcard h hin
  · exact isRupert_of_facets_edge_par V hgen Q1 Q2 h1V h2V h1f h2f v w hvw hint hne1 hne2 h hin

end Minimality

end
