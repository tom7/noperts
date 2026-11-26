module

public import Minimality.EdgePlaneRim3
public import Minimality.Type24HoleEP

/-!
# A triangular facet cell is an Edge-Plane view; `OpenEP` without `¬ FacetCellF`

L2 and L3 of job L3R (Carbon A75 Lemma 2.1).  For a facet `t ≠ 3` of a type-24 solid (a triangle) with a view `u`
in its open cell (`CellAt F {t} (nb t) u`) the triangle `rim3 t` is a strict 3-rim of `±u` (for all seven
vertices), so `Gen.EdgePlaneAny x` by `Split.Rim3.edgePlaneAny_of_strictRim3`.  The quadrilateral facet `t = 3`
(`0345`) is NOT proved: the missing arrow is `QuadFacetEP` (a facet cell on the quad gives an Edge-Plane view;
A75 Lemma 2.1 cites `lexAny_of_quadCell` plus "`DepthSeparated` / `SplitRows`", but `LexAny` does not give
`SplitRows`, and no Lean arrow `LexAny → EdgePlaneAny` exists).  `OpenEP'` is `OpenEP` without `¬ FacetCellF`;
`openEP_of_openEP'` is unconditional, the converse needs `QuadFacetEP`.
-/

@[expose] public section

set_option autoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.NC Minimality.T24.Z0

namespace Minimality.T24.EPF

variable {x : Fin 7 → ℝ³}

/-- **L2 (triangle facets).**  A view in the open cell of a triangular facet `t ≠ 3` makes `rim3 t` a strict
rim of `u` or `-u`, hence an Edge-Plane view exists. -/
theorem edgePlaneAny_of_triCell (F : S0xFac 9 s0x_S24 x) {t : Fin 9} (ht : t ≠ 3) {u : ℝ³}
    (hu : CellAt F {t} (nb t) u) : Gen.EdgePlaneAny x := by
  have hx := Minimality.H24.SAT.inj_of_fac F
  have hc := rim3_inj t ht
  obtain ⟨D⟩ := silL_of_cell F (rim3_cyc t ht) hu.cellLe hu
  choose μ hμ0 hμ using fun i => h21b_exists_mu (by norm_num) hx hc D i
  have hsign := h21b_sign_agree (by norm_num) hx hc D μ hμ0 hμ
  have Q : ∀ i m, m ≠ rim3 t i → m ≠ rim3 t (i + 1) →
      0 < D.fA i (x m) * ⟪D.B i, u⟫ - D.fB i (x m) * ⟪D.A i, u⟫ := by
    intro i m h0 h1
    have := h21b_Q_pos D i m h0 h1
    rcases this with h | ⟨h0', h⟩
    · exact h
    · rw [h0'] at h; exact absurd h (lt_irrefl _)
  have key : ∀ (i : ZMod 3) (m : Fin 7),
      Split.det3 (x (rim3 t (i + 1)) - x (rim3 t i)) (x m - x (rim3 t i)) u =
        μ i * (D.fA i (x m) * ⟪D.B i, u⟫ - D.fB i (x m) * ⟪D.A i, u⟫) := by
    intro i m
    rw [Split.det3_eq_minimality]
    exact h21b_det_eq D i (μ i) (hμ i) m u
  rcases hsign with h | h
  · refine Split.Rim3.edgePlaneAny_of_strictRim3 x (rim3 t) hc u ?_
    intro m i h0 h1
    rw [key i m]
    exact mul_pos (h i) (Q i m h0 h1)
  · refine Split.Rim3.edgePlaneAny_of_strictRim3 x (rim3 t) hc (-u) ?_
    intro m i h0 h1
    have e : Split.det3 (x (rim3 t (i + 1)) - x (rim3 t i)) (x m - x (rim3 t i)) (-u) =
        -Split.det3 (x (rim3 t (i + 1)) - x (rim3 t i)) (x m - x (rim3 t i)) u := by
      rw [Split.det3_eq_inner_cross, Split.det3_eq_inner_cross, inner_neg_right]
    rw [e, key i m]
    have := Q i m h0 h1
    nlinarith [h i]

/-- The missing arrow for the quadrilateral facet `0345`: a facet cell on `t = 3` gives an Edge-Plane view. -/
def QuadFacetEP : Prop :=
  ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) (u : ℝ³), CellAt F {3} (nb 3) u → Gen.EdgePlaneAny x

/-- `FacetCellF F → Gen.EdgePlaneAny x` given the quadrilateral arrow (the triangular facets are proved). -/
theorem edgePlaneAny_of_facetCellF (hq : QuadFacetEP) (F : S0xFac 9 s0x_S24 x) (h : FacetCellF F) :
    Gen.EdgePlaneAny x := by
  obtain ⟨t, u, hu, hn⟩ := h
  have hcell : CellAt F {t} (nb t) u := ⟨fun s hs => by
    rw [Finset.mem_singleton] at hs; subst hs; exact hu, hn⟩
  by_cases ht : t = 3
  · subst ht; exact hq x F u hcell
  · exact edgePlaneAny_of_triCell F ht hcell

/-- `OpenEP` without the hypothesis `¬ FacetCellF F`. -/
def OpenEP' : Prop :=
  ∀ (x : Fin 7 → ℝ³) (_F : S0xFac 9 s0x_S24 x), CbarIn x → ¬ BoxApplies (Finset.univ.image x) →
    Gen.EdgePlaneAny x

/-- `OpenEP' → OpenEP` (unconditional). -/
theorem openEP_of_openEP' (h : OpenEP') : Stmt.OpenEP := fun x F hc _ hb => h x F hc hb

/-- `OpenEP → OpenEP'` given the quadrilateral arrow. -/
theorem openEP'_of_openEP (hq : QuadFacetEP) (h : Stmt.OpenEP) : OpenEP' := by
  intro x F hc hb
  by_cases hf : FacetCellF F
  · exact edgePlaneAny_of_facetCellF hq F hf
  · exact h x F hc hf hb

theorem openEP_iff_openEP' (hq : QuadFacetEP) : Stmt.OpenEP ↔ OpenEP' :=
  ⟨openEP'_of_openEP hq, openEP_of_openEP'⟩

end Minimality.T24.EPF
