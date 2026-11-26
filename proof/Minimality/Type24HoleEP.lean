module

public import Minimality.Type24HoleMin
public import Minimality.Type24HoleStatement

/-!
# The single-leaf form of the type-24 open problem: Edge-Plane

`OpenEP`: for every type-24 solid with `CbarIn`, no facet cell and non-thin (`¬ BoxApplies`), the Edge-Plane leaf
`Gen.EdgePlaneAny x` fires.  This needs only ONE leaf kind (the other leaves of `HoleLeaf` are then not needed:
`SplitAny => EdgePlaneAny` is `Gen.splitAny_edgePlaneAny`).  [CONJECTURE, nothing here is proved about `OpenEP`
itself]: evidence is data only, an Edge-Plane view exists at all about 19k region points tested (FACENORM24
sections EPCOVER, EPADV).  Proved here: `OpenEP -> OpenLeaf` (hence `-> OpenFull -> Open24`, and
`-> Open24Rupert`-chain of Type24HoleStatement), and `OpenEPNoBox -> OpenEP`.
-/

@[expose] public section

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.NC Minimality.T24.Z0

namespace Minimality.T24.Stmt

/-- [CONJECTURE] **Single-leaf form**: with `CbarIn`, no facet cell and no box rule, an Edge-Plane view exists.
Data only (about 19k region points, FACENORM24 EPCOVER / EPADV); a hypothesis, not proved. -/
def OpenEP : Prop :=
  ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), CbarIn x → ¬ FacetCellF F →
    ¬ BoxApplies (Finset.univ.image x) → Gen.EdgePlaneAny x

/-- [CONJECTURE] The stronger form without the `¬ BoxApplies` hypothesis. -/
def OpenEPNoBox : Prop :=
  ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), CbarIn x → ¬ FacetCellF F → Gen.EdgePlaneAny x

/-- [PROVED] `OpenEPNoBox → OpenEP`. -/
theorem openEP_of_noBox (h : OpenEPNoBox) : OpenEP := fun x F hc hf _ => h x F hc hf

/-- [PROVED] `OpenEP → OpenLeaf` (no `HoleLeaf` point). -/
theorem openLeaf_of_openEP (h : OpenEP) : OpenLeaf := by
  intro x F hL
  obtain ⟨h1, h2, _, _, _, h6, h7⟩ := hL
  exact h7 (h x F h1 h2 h6)

/-- [PROVED] `OpenEP → Open24` (via `OpenLeaf → OpenFull → Open24`). -/
theorem open24_of_openEP (h : OpenEP) : Open24 :=
  open24_of_openFull (openFull_of_openLeaf (openLeaf_of_openEP h))

end Minimality.T24.Stmt
