module

public import Mathlib
public import MinimalityExtra
public import Minimality.SilS0XC
public import Minimality.RimCellClosed

@[expose] public section

open scoped RealInnerProductSpace

namespace MinimalityExtra

/-- Proof of `ClosedCellQ4` (Lemma Q4 on a closed cell). -/
theorem closedCellQ4 : ClosedCellQ4 := by
  intro n m x hx S N h h_zero h_neg c hc U Dn hcyc a haU haDn g g' hgU hgDn hg'U hg'Dn hneg hpos
  let F : Minimality.H21.S0xFac m S x := {
    f := fun t y => ⟪N t, y⟫ - h t
    N := N
    hN := fun t y z => by
      rw [inner_sub_right]
      ring
    zero := fun t i hi => sub_eq_zero.2 (h_zero t i hi)
    neg := fun t i hi => sub_neg.2 (h_neg t i hi)
  }
  have ha : Minimality.H21.CellAt F U Dn a := ⟨haU, haDn⟩
  have hg : Minimality.H21.CellLe F U Dn g := ⟨hgU, hgDn⟩
  have hg' : Minimality.H21.CellLe F U Dn g' := ⟨hg'U, hg'Dn⟩
  have hd : diagPairs4 = Minimality.RimCell.diagPairs := rfl
  rw [hd] at hneg hpos
  exact Minimality.H21.isRupert_of_closedCell_q4 F hx hc hcyc ha hg hg' hneg hpos

end MinimalityExtra
