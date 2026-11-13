module

public import Minimality.Type21Sl2C

@[expose] public section

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace H21
variable {x : Fin 7 → ℝ³}

/-- The facing pattern `pat` (true = up) gives the cycle `c` as an up/down silhouette: every edge
`c i → c (i+1)` lies in an up facet `a` and a down facet `b` and every other vertex is off one. -/
def h21b_CycOK {k : ℕ} [NeZero k] (c : ZMod k → Fin 7) (pat : Fin 8 → Bool) : Prop :=
  ∀ i, ∃ a b : Fin 8, pat a = true ∧ pat b = false ∧ c i ∈ h21S a ∧ c i ∈ h21S b ∧
    c (i + 1) ∈ h21S a ∧ c (i + 1) ∈ h21S b ∧
    ∀ m : Fin 7, m ≠ c i → m ≠ c (i + 1) → m ∉ h21S a ∨ m ∉ h21S b

instance {k : ℕ} [NeZero k] (c : ZMod k → Fin 7) (pat : Fin 8 → Bool) :
    Decidable (h21b_CycOK c pat) := by unfold h21b_CycOK; infer_instance

end H21
end Minimality
