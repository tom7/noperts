module

public import Mathlib
public import MinimalityExtra
public import Minimality.RimCell
public import Minimality.RimCellView

@[expose] public section

open Matrix
open scoped Topology

namespace MinimalityExtra

theorem diagPairs4_eq : diagPairs4 = Minimality.RimCell.diagPairs := rfl

/-- Proof of `RimCellUnimodal` (Lemma Q4). -/
theorem rimCellUnimodal : RimCellUnimodal := by
  intro n Γ hΓ y hy hspan A hAo hAc hA0 g g' hg hg' hneg hpos
  rw [diagPairs4_eq] at hspan hneg hpos
  obtain ⟨c, hcA, hcu⟩ := Minimality.RimCell.rimCell_exists_unimodal Γ hΓ y hy hspan hAo hAc hA0 hg hg' hneg hpos
  exact ⟨c, hcA, hcu⟩

/-- Proof of `RimCellRupert` (Lemma Q4 in shape coordinates). -/
theorem rimCellRupert : RimCellRupert := by
  intro E hE y hy Y hyY hspan A hAo hAc hA0 hcell g g' hg hg' hneg hpos
  rw [diagPairs4_eq] at hspan hneg hpos
  exact Minimality.RimCell.isRupert_of_rimCell_coords E hE y hy Y hyY hspan hAo hAc hA0 hcell hg hg' hneg hpos

end MinimalityExtra
