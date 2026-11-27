module

public import Minimality.Type24GapLemmas2
public import Minimality.RimCellClosed

/-!
# The generic closed-face `RobUni` leaf and its corollaries

The generic leaf (G1 of nopert229 notes/WALL-GENERALIZATION.md item 2) already exists as
`Minimality.T24.Cell.lexAny_of_wall_robUni` (Type24GapLemmas2.lean; its persistence step is
`robUni_eventually_add`, `RobUni` being open in the view): a view `r` on the closed face of a cell `c` (facets
strict, or zero with the push direction `v` pointing into the cell) with strict `RobUni` rim depths gives
`Gen.LexAny F`.  Here the other generic `Lex` leaves are derived from it, so they need no persistence argument:

* `lexAny_of_wall_monoCorners'`: `k - 3` strictly monotone rim corners at the face view (this restates
  `lexAny_of_wall_monoCorners` of Type24GapLemmas.lean, now a corollary: `robUni_of_monoCorners` at `r`).
* `lexAny_of_wall_q4`: a 4-rim cell with a strictly negative and a strictly positive diagonal form at the face
  view ("not a crown"; the `Cell24` form of `wall_q4_lexAny` of Type24WallFoot.lean, which is stated for an
  arbitrary 4-rim and the capView wall line and is not literally an instance).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace Topology
open Finset Filter
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.HC

namespace Minimality.T24.Cell

variable {x : Fin 7 → ℝ³}

/-- `k - 3` strictly monotone rim corners at a closed-face view give `Gen.LexAny`
(`lexAny_of_wall_robUni` after `robUni_of_monoCorners`). -/
theorem lexAny_of_wall_monoCorners' (F : S0xFac 9 s0x_S24 x) (c : Cell24) {r v : ℝ³}
    (hU : ∀ t ∈ c.U, 0 < ⟪F.N t, r⟫ ∨ (⟪F.N t, r⟫ = 0 ∧ 0 < ⟪F.N t, v⟫))
    (hD : ∀ t ∉ c.U, ⟪F.N t, r⟫ < 0 ∨ (⟪F.N t, r⟫ = 0 ∧ ⟪F.N t, v⟫ < 0))
    (S : Finset (ZMod c.k)) (hS : c.k - 3 ≤ S.card)
    (hm : ∀ i ∈ S, 0 < (⟪x (c.r i), r⟫ - ⟪x (c.r (i - 1)), r⟫) * (⟪x (c.r (i + 1)), r⟫ - ⟪x (c.r i), r⟫)) :
    Gen.LexAny F :=
  lexAny_of_wall_robUni F c hU hD (GenPlus.robUni_of_monoCorners c.hk S hS hm)

/-- A 4-rim cell with a strictly negative and a strictly positive diagonal form at a closed-face view gives
`Gen.LexAny` (`lexAny_of_wall_robUni` after `robUni_four_of_mixed`). -/
theorem lexAny_of_wall_q4 (F : S0xFac 9 s0x_S24 x) (c : Cell24) (hk : c.k = 4) {r v : ℝ³}
    (hU : ∀ t ∈ c.U, 0 < ⟪F.N t, r⟫ ∨ (⟪F.N t, r⟫ = 0 ∧ 0 < ⟪F.N t, v⟫))
    (hD : ∀ t ∉ c.U, ⟪F.N t, r⟫ < 0 ∨ (⟪F.N t, r⟫ = 0 ∧ ⟪F.N t, v⟫ < 0))
    (hn : ∃ p ∈ RimCell.diagPairs, ⟪x (c.r (hk ▸ p.1)) - x (c.r (hk ▸ p.2)), r⟫ < 0)
    (hp : ∃ p ∈ RimCell.diagPairs, 0 < ⟪x (c.r (hk ▸ p.1)) - x (c.r (hk ▸ p.2)), r⟫) :
    Gen.LexAny F := by
  cases c with
  | mk k hk4 rr U inj cyc =>
  simp only at hk
  subst hk
  refine lexAny_of_wall_robUni F _ hU hD (robUni_four_of_mixed ?_ ?_)
  · obtain ⟨p, hp, h⟩ := hn
    exact ⟨p, hp, by simpa [inner_sub_left] using h⟩
  · obtain ⟨p, hp, h⟩ := hp
    exact ⟨p, hp, by simpa [inner_sub_left] using h⟩

end Minimality.T24.Cell
