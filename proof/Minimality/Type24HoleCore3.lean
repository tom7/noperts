module

public import Minimality.Type24HoleAtlas
public import Minimality.Type24HoleMin
public import Minimality.Type24EPFacet

/-!
# The core form of `HoleLeaf`: Lex, Edge-Plane and the quad-circle face chord

Assembly of proved lemmas (HOLE24-ROUTES-1126, section 2).  On `HoleLeaf` the conjuncts
`¬ FacetCellF`, `¬ AnyFaceChord`, `¬ SplitAny` are redundant: a triangle facet cell is an Edge-Plane view
(`EPF.edgePlaneAny_of_triCell`), the quad facet cell is a lex cell (`lexAny_of_quadCell`), `SplitAny` implies
`EdgePlaneAny` (`Gen.splitAny_edgePlaneAny`), and off Lex and Split `AnyFaceChord` is `FaceChordView F 3`.
No extra hypotheses are needed.
-/

@[expose] public section

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.Z0

namespace Minimality.T24.Atlas

private theorem s24_sep'' :
    ∀ i j : Fin 7, j ≠ i → ∃ t : Fin 9, i ∈ s0x_S24 t ∧ j ∉ s0x_S24 t := by decide

variable {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x}

/-- A facet cell gives an Edge-Plane view (triangles) or a lex cell (the quad facet). -/
theorem facetCellF_lexAny_or_edgePlane (h : FacetCellF F) : Gen.LexAny F ∨ Gen.EdgePlaneAny x := by
  obtain ⟨t, u, hu, hn⟩ := h
  have hcell : CellAt F {t} (nb t) u := ⟨fun s hs => by
    rw [Finset.mem_singleton] at hs; subst hs; exact hu, hn⟩
  by_cases ht : t = 3
  · subst ht; exact Or.inl (T24.lexAny_of_quadCell F hcell)
  · exact Or.inr (T24.EPF.edgePlaneAny_of_triCell F ht hcell)

/-- **Core form of `HoleLeaf`**: Box, Lex, Edge-Plane and the face chord on the quad circle. -/
theorem holeLeaf_iff_core3 :
    HoleLeaf x F ↔ CbarIn x ∧ ¬ BoxApplies (Finset.univ.image x) ∧ ¬ Gen.LexAny F ∧
      ¬ Gen.EdgePlaneAny x ∧ ¬ FaceChord.FaceChordView F 3 := by
  constructor
  · rintro ⟨h1, _, h3, h4, _, h6, h7⟩
    exact ⟨h1, h6, h4, h7, fun h => h3 ⟨3, h⟩⟩
  · rintro ⟨h1, h6, h4, h7, h5⟩
    have hS : ¬ Gen.SplitAny F := fun hs =>
      h7 (Gen.splitAny_edgePlaneAny F (EdgeViewLink.inj_of_fac24 F) s24_sep'' hs)
    refine ⟨h1, fun h => ?_, fun h => h5 ((anyFaceChord_iff_quad F h4 hS).1 h), h4, hS, h6, h7⟩
    rcases facetCellF_lexAny_or_edgePlane h with h | h
    exacts [h4 h, h7 h]

/-- `HoleLeafMin` in core form. -/
theorem holeLeafMin_iff_core3 :
    HoleLeafMin x F ↔ HoleLeaf x F := (holeLeaf_iff_min x F).symm

/-- `Hole24` implies the core form. -/
theorem hole24_core3 (h : Hole24 x F) :
    CbarIn x ∧ ¬ BoxApplies (Finset.univ.image x) ∧ ¬ Gen.LexAny F ∧
      ¬ Gen.EdgePlaneAny x ∧ ¬ FaceChord.FaceChordView F 3 :=
  holeLeaf_iff_core3.1 h.1

end Minimality.T24.Atlas
