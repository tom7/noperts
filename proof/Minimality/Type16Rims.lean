module

public import Minimality.Type16NF

@[expose] public section

/-!
# Single tests with explicit rims (type 16, §19.3–19.5)

The two-test and three-test certificates of §19.3–19.5 combine single tests whose rims are
quadrilaterals or pentagons, at an edge view (Theorem 8.9) or at the view along the line of
two faces through a vertex (Proposition 8.8).  These are `isRupert_of_edgeViewσ` and
`isRupert_of_vertexViewσ` with the cycle written out: every determinant test is a separate
hypothesis, and the depths are assumed cyclically unimodal (the pair and triple lemmas decide
which test is unimodal).

* `isRupert_vquadσ`, `isRupert_vquintσ`: vertex views, middles over any side;
* `isRupert_equadσ`, `isRupert_equintσ`: edge views (`w = y₀ − h u`), middles over the sides
  at the apex (`EdgeMiddle`);
* `quad_unimodal`: a 4-cycle with distinct depths is unimodal unless its diagonals are
  depth-separated.
-/

namespace Minimality

open scoped RealInnerProductSpace
open Finset

theorem quad_unimodal {y₀ y₁ y₂ y₃ u : ℝ³} (h : ¬ DepthSep y₀ y₂ y₁ y₃ u)
    (hz : [⟪y₀, u⟫, ⟪y₁, u⟫, ⟪y₂, u⟫, ⟪y₃, u⟫].Nodup) :
    IsCyclicUnimodal (quad ⟪y₀, u⟫ ⟪y₁, u⟫ ⟪y₂, u⟫ ⟪y₃, u⟫) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hz
  obtain ⟨⟨z1, z2, z3⟩, ⟨z4, z5⟩, z6, -⟩ := hz
  exact isCyclicUnimodal_four (quad_injective z1 z2 z3 z4 z5 z6)
    (overlap4_of_not_depthSep h z1 z2 z3 z4 z5 z6)

/-! ### Certificate forms (§18.2): the same rims without the horizontal double normal -/

end Minimality

end
