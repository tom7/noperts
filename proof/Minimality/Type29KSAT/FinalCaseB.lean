module

public import Minimality.Type29KSAT.CaseBSlide
public import Minimality.Type29KSAT.FinalZB

@[expose] public section

/-!
# Type 29, class K2 on `Z1` and `σ(Z1)`, case B

Case B is `x1 - x4` orthogonal to the plane of the facet `015` (resp. `x1 - x5` to `124` on `σ(Z1)`): the quadrilateral
`1456` is then a rectangle perpendicular to the two parallel facets.  Split on the slab of the edge `15` (resp. `14`):
if no vertex off the quadrilateral lies over or beyond one end of it, the Slide Lemma leaf applies
(`NF29.isRupert_Z1_caseB_slide`, a first-order motion sliding along the edge); otherwise vertices lie over or beyond
both ends, and the tie view encoding with that residue is unsatisfiable (`NF29.isRupert_K2a_Z1_caseB_residue`, a
kernel-checked core).
-/

open scoped RealInnerProductSpace
open Finset

theorem Minimality.NF29.isRupert_K2a_Z1_caseB {x : Fin 7 → EuclideanSpace ℝ (Fin 3)} (N : Minimality.NF29 x)
    (ha2 : N.a2 < 0) (hb0 : N.b0 < 0) (hV : N.V < 0) (hZ : N.s = 1 ∧ N.t = 1 ∧ N.a0 + N.h0 = 0)
    (hB : ⟪x 1 - x 4, x 0 - x 1⟫ = 0 ∧ ⟪x 1 - x 4, x 0 - x 5⟫ = 0) :
    IsRupert (Finset.univ.image x) := by
  by_cases h : (∀ p ∈ ({0, 2, 3} : Finset (Fin 7)), 0 < ⟪x p - x 1, x 5 - x 1⟫) ∨
      (∀ q ∈ ({0, 2, 3} : Finset (Fin 7)), 0 < ⟪x q - x 5, x 1 - x 5⟫)
  · exact N.isRupert_Z1_caseB_slide hZ hB h
  · push Not at h
    exact N.isRupert_K2a_Z1_caseB_residue ha2 hb0 hV hZ hB h.1 h.2

theorem Minimality.NF29.isRupert_K2b_Z1_caseB {x : Fin 7 → EuclideanSpace ℝ (Fin 3)} (N : Minimality.NF29 x)
    (ha2 : N.a2 < 0) (hb0 : N.b0 < 0) (hV : 0 < N.V) (hZ : N.t = 1 ∧ N.s = 1 ∧ N.b2 + N.h2 = 0)
    (hB : ⟪x 1 - x 5, x 2 - x 1⟫ = 0 ∧ ⟪x 1 - x 5, x 2 - x 4⟫ = 0) :
    IsRupert (Finset.univ.image x) := by
  by_cases h : (∀ p ∈ ({0, 2, 3} : Finset (Fin 7)), 0 < ⟪x p - x 1, x 4 - x 1⟫) ∨
      (∀ q ∈ ({0, 2, 3} : Finset (Fin 7)), 0 < ⟪x q - x 4, x 1 - x 4⟫)
  · exact N.isRupert_sZ1_caseB_slide hZ hB h
  · push Not at h
    exact N.isRupert_K2b_Z1_caseB_residue ha2 hb0 hV hZ hB h.1 h.2

