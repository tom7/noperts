module

public import Minimality.Type29SilB

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace H29S
open Minimality.H21

variable {x : Fin 7 → ℝ³}

def H29SL1 (T : Facets29 x) : Prop :=
  Uni (fun i : ZMod 5 => ⟪x (h29s_c1 i), x 3 - x 1⟫)
def H29SL2 (T : Facets29 x) : Prop :=
  0 < T.f015.f (x 6) - T.f015.f (x 2) ∧ 0 < T.f035.f (x 6) - T.f035.f (x 2) ∧ Uni (fun i : ZMod 4 => ⟪x (h29s_c2 i), x 6 - x 2⟫)
def H29SL3 (T : Facets29 x) : Prop :=
  T.f015.f (x 6) - T.f015.f (x 2) < 0 ∧ 0 < T.f035.f (x 6) - T.f035.f (x 2) ∧ Uni (fun i : ZMod 5 => ⟪x (h29s_c3 i), x 6 - x 2⟫)
def H29SL4 (T : Facets29 x) : Prop :=
  T.f015.f (x 6) - T.f015.f (x 2) < 0 ∧ T.f035.f (x 6) - T.f035.f (x 2) < 0 ∧ Uni (fun i : ZMod 4 => ⟪x (h29s_c4 i), x 6 - x 2⟫)
def H29SL5 (T : Facets29 x) : Prop :=
  0 < T.f124.f (x 6) - T.f124.f (x 0) ∧ 0 < T.f234.f (x 6) - T.f234.f (x 0) ∧ Uni (fun i : ZMod 4 => ⟪x (h29s_c5 i), x 6 - x 0⟫)
def H29SL6 (T : Facets29 x) : Prop :=
  T.f124.f (x 6) - T.f124.f (x 0) < 0 ∧ 0 < T.f234.f (x 6) - T.f234.f (x 0) ∧ Uni (fun i : ZMod 5 => ⟪x (h29s_c6 i), x 6 - x 0⟫)
def H29SL7 (T : Facets29 x) : Prop :=
  0 < T.f124.f (x 6) - T.f124.f (x 0) ∧ T.f234.f (x 6) - T.f234.f (x 0) < 0 ∧ Uni (fun i : ZMod 5 => ⟪x (h29s_c7 i), x 6 - x 0⟫)
def H29SL8 (T : Facets29 x) : Prop :=
  T.f124.f (x 6) - T.f124.f (x 0) < 0 ∧ T.f234.f (x 6) - T.f234.f (x 0) < 0 ∧ Uni (fun i : ZMod 4 => ⟪x (h29s_c8 i), x 6 - x 0⟫)
def H29SL9 (T : Facets29 x) : Prop :=
  0 < T.f346.f (x 5) - T.f346.f (x 2) ∧ Uni (fun i : ZMod 4 => ⟪x (h29s_c9 i), x 5 - x 2⟫)
def H29SL10 (T : Facets29 x) : Prop :=
  T.f346.f (x 5) - T.f346.f (x 2) < 0 ∧ Uni (fun i : ZMod 5 => ⟪x (h29s_c10 i), x 5 - x 2⟫)
def H29SL11 (T : Facets29 x) : Prop :=
  0 < T.f356.f (x 4) - T.f356.f (x 0) ∧ Uni (fun i : ZMod 4 => ⟪x (h29s_c11 i), x 4 - x 0⟫)
def H29SL12 (T : Facets29 x) : Prop :=
  T.f356.f (x 4) - T.f356.f (x 0) < 0 ∧ Uni (fun i : ZMod 5 => ⟪x (h29s_c12 i), x 4 - x 0⟫)

/-- The leftover of the segment-view rule: none of the twelve leaves W1-W12 applies. -/
def H29SilResid (T : Facets29 x) : Prop :=
  ¬ H29SL1 T ∧ ¬ H29SL2 T ∧ ¬ H29SL3 T ∧ ¬ H29SL4 T ∧ ¬ H29SL5 T ∧ ¬ H29SL6 T ∧ ¬ H29SL7 T ∧ ¬ H29SL8 T ∧ ¬ H29SL9 T ∧ ¬ H29SL10 T ∧ ¬ H29SL11 T ∧ ¬ H29SL12 T

theorem h29s_rule_isRupert (T : Facets29 x) (h : ¬ H29SilResid T) : IsRupert (univ.image x) := by
  unfold H29SilResid at h
  by_contra hR
  apply h
  unfold H29SL1 H29SL2 H29SL3 H29SL4 H29SL5 H29SL6 H29SL7 H29SL8 H29SL9 H29SL10 H29SL11 H29SL12
  exact ⟨fun e => hR (h29s_W1 T e),
    fun e => hR (h29s_W2 T e.1 e.2.1 e.2.2),
    fun e => hR (h29s_W3 T e.1 e.2.1 e.2.2),
    fun e => hR (h29s_W4 T e.1 e.2.1 e.2.2),
    fun e => hR (h29s_W5 T e.1 e.2.1 e.2.2),
    fun e => hR (h29s_W6 T e.1 e.2.1 e.2.2),
    fun e => hR (h29s_W7 T e.1 e.2.1 e.2.2),
    fun e => hR (h29s_W8 T e.1 e.2.1 e.2.2),
    fun e => hR (h29s_W9 T e.1 e.2),
    fun e => hR (h29s_W10 T e.1 e.2),
    fun e => hR (h29s_W11 T e.1 e.2),
    fun e => hR (h29s_W12 T e.1 e.2)⟩

theorem h29s_rule_false (hN : IsNopert (Finset.univ.image x)) (T : Facets29 x)
    (h : ¬ H29SilResid T) : False :=
  hN.2 (h29s_rule_isRupert T h)

end H29S
end Minimality
