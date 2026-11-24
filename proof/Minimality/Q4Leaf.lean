module

public import Minimality.GenericLeaves
public import Minimality.RimCellClosed
public import Minimality.SlideDS
public import Minimality.Type24SAT.Facets24

/-! Q4 leaf (LEAFPLUS, 2026-11-24): a stronger generic leaf for the type-24 hole (design note: nopert229
tools/genleaves/LEAFPLUS.md).

* `Q4Any`: Lemma Q4 on a closed rim cone (existing proof `isRupert_of_closedCell_q4`, RimCellClosed.lean:224).
  Not limit form: a cell-level (two-view) leaf.  Proved here (wrapper, no sorry).
* (`SepAny`, Theorem 8.10 at an open-cell view, was tested and is never the only closer on the 3219 events: dropped.)
* Type-24 use: `hole24_q4` shows the leaf can be negated in `Hole24` (an IsRupert conclusion for the type-24 facets). -/

set_option autoImplicit false

open scoped RealInnerProductSpace
open Finset

@[expose] public section

namespace Minimality.GenPlus

open Minimality Minimality.H21

/-- **Q4 on a closed rim cone.**  A 4-cycle silhouette `c` of the up facets `U` and down facets `Dn` (only the facets of
the rim edges need be listed, so the cone is the whole region where `c` is the silhouette), a strict cone point `a`,
and closure points `g`, `g'` where some diagonal form is negative resp. positive. -/
def Q4Any {m n : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³} (F : S0xFac m S x) : Prop :=
  ∃ (c : ZMod 4 → Fin n) (U Dn : Finset (Fin m)) (a g g' : ℝ³),
    Function.Injective c ∧ S0xCycUD S c U Dn ∧ CellAt F U Dn a ∧ CellLe F U Dn g ∧ CellLe F U Dn g' ∧
    (∃ p ∈ RimCell.diagPairs, ⟪x (c p.1) - x (c p.2), g⟫ < 0) ∧
    (∃ p ∈ RimCell.diagPairs, 0 < ⟪x (c p.1) - x (c p.2), g'⟫)

theorem q4Any_isRupert {m n : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (hx : Function.Injective x) (h : Q4Any F) : IsRupert (univ.image x) := by
  rcases h with ⟨c, U, Dn, a, g, g', hc, hcyc, ha, hg, hg', hn, hp⟩
  exact isRupert_of_closedCell_q4 F hx hc hcyc ha hg hg' hn hp

/-- Type-24 instance (as a new `Gen.*` leaf of `Hole24`: add `¬ Q4Any F` next to `¬ LexAny F`). -/
theorem hole24_q4 {x : Fin 7 → ℝ³} (F : S0xFac 9 Minimality.T24.SAT.s0x_S24 x) (hx : Function.Injective x) (h : Q4Any F) :
    IsRupert (univ.image x) :=
  q4Any_isRupert F hx h

end Minimality.GenPlus
