module

public import Minimality.Type21SilG

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace H21

variable {x : Fin 7 → ℝ³}

/-- The six leaves of S1, as conditions (facing literal and strict depth unimodality). -/
def H21L1 (x : Fin 7 → ℝ³) : Prop := Uni (fun i : ZMod 5 => ⟪x (cW1 i), x 3 - x 0⟫)
def H21L2 (x : Fin 7 → ℝ³) : Prop := Uni (fun i : ZMod 5 => ⟪x (cW2 i), x 5 - x 4⟫)
def H21L3 (T : Facets21 x) : Prop :=
  0 < T.f046.f (x 2) - T.f046.f (x 1) ∧ Uni (fun i : ZMod 4 => ⟪x (cW3 i), x 2 - x 1⟫)
def H21L4 (T : Facets21 x) : Prop :=
  T.f046.f (x 2) - T.f046.f (x 1) < 0 ∧ Uni (fun i : ZMod 5 => ⟪x (cW4 i), x 2 - x 1⟫)
def H21L5 (T : Facets21 x) : Prop :=
  0 < T.f235.f (x 6) - T.f235.f (x 1) ∧ Uni (fun i : ZMod 4 => ⟪x (cW3 i), x 6 - x 1⟫)
def H21L6 (T : Facets21 x) : Prop :=
  T.f235.f (x 6) - T.f235.f (x 1) < 0 ∧ Uni (fun i : ZMod 5 => ⟪x (cW6 i), x 6 - x 1⟫)

/-- **The leftover of the S1 rule**: none of the six leaves applies (this includes the ties
`φ_D(1,2) = 0`, `φ_H(1,6) = 0` and every depth tie or non-unimodal order on the cycles). -/
def H21Resid (T : Facets21 x) : Prop :=
  ¬ H21L1 x ∧ ¬ H21L2 x ∧ ¬ H21L3 T ∧ ¬ H21L4 T ∧ ¬ H21L5 T ∧ ¬ H21L6 T

theorem h21_rule_isRupert (T : Facets21 x) (h : ¬ H21Resid T) : IsRupert (univ.image x) := by
  unfold H21Resid at h
  by_contra hR
  apply h
  refine ⟨fun e => hR (h21_W1 T e), fun e => hR (h21_W2 T e),
    fun e => hR (h21_W3 T e.1 e.2), fun e => hR (h21_W4 T e.1 e.2),
    fun e => hR (h21_W5 T e.1 e.2), fun e => hR (h21_W6 T e.1 e.2)⟩

/-- Contradiction form for the skeleton. -/
theorem h21_rule_false (hN : IsNopert (Finset.univ.image x)) (T : Facets21 x)
    (h : ¬ H21Resid T) : False :=
  hN.2 (h21_rule_isRupert T h)

end H21
end Minimality
