module

public import Minimality.Type21Sl2F

@[expose] public section

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace H21
variable {x : Fin 7 → ℝ³}

/-- None of the edge-view leaves (S2) applies. -/
def h21b_NoSeg (T : Facets21 x) : Prop :=
  (∀ s ∈ h21b_seg4, ¬ h21b_SegCond T s) ∧ (∀ s ∈ h21b_seg5, ¬ h21b_SegCond T s) ∧
  (∀ s ∈ h21b_seg6, ¬ h21b_SegCond T s)

/-- None of the line-view leaves (S2b) applies. -/
def h21b_NoLin (T : Facets21 x) : Prop :=
  (∀ s ∈ h21b_lin4, ¬ h21b_LinCond T s) ∧ (∀ s ∈ h21b_lin5, ¬ h21b_LinCond T s) ∧
  (∀ s ∈ h21b_lin6, ¬ h21b_LinCond T s)

/-- **The refined residual**: `H21Resid` (no split/apex leaf) and no edge-view leaf and no line-view leaf. -/
def H21Resid2 (T : Facets21 x) : Prop := H21Resid T ∧ h21b_NoSeg T ∧ h21b_NoLin T

theorem h21b_rule_isRupert (T : Facets21 x) (h : ¬ H21Resid2 T) : IsRupert (univ.image x) := by
  by_contra hR
  apply h
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · by_contra hn; exact hR (h21_rule_isRupert T hn)
  · exact fun s hs hc => hR (h21b_seg_rupert T s (h21b_seg4_good s hs) hc)
  · exact fun s hs hc => hR (h21b_seg_rupert T s (h21b_seg5_good s hs) hc)
  · exact fun s hs hc => hR (h21b_seg_rupert T s (h21b_seg6_good s hs) hc)
  · exact fun s hs hc => hR (h21b_lin_rupert T s (h21b_lin4_good s hs) hc)
  · exact fun s hs hc => hR (h21b_lin_rupert T s (h21b_lin5_good s hs) hc)
  · exact fun s hs hc => hR (h21b_lin_rupert T s (h21b_lin6_good s hs) hc)

/-- Contradiction form for the skeleton. -/
theorem h21b_rule_false (hN : IsNopert (Finset.univ.image x)) (T : Facets21 x)
    (h : ¬ H21Resid2 T) : False :=
  hN.2 (h21b_rule_isRupert T h)

end H21
end Minimality
