module

public import Minimality.Type16Arc2B

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace H16A
open Minimality.H21 Minimality.H16U Minimality.V2

variable {x : Fin 7 → ℝ³}

def h16a3_c35 : ZMod 5 → Fin 7 := ![0, 4, 1, 5, 3]
def h16a3_ea35 : ZMod 5 → Fin 8 := ![2, 5, 5, 0, 0]
def h16a3_eb35 : ZMod 5 → Fin 8 := ![4, 6, 1, 1, 3]
noncomputable def h16a3_u35 (T : Type16 x) : ℝ³ :=
  h16a_u (x 3 - x 0) (cross (T.fN 4) (T.fN 5))
    (x 0 - x 3) (cross (x 5 - x 1) (x 3 - x 1))
def H16A3L35 (T : Type16 x) : Prop := H16A2Leaf T h16a3_c35 h16a3_ea35 h16a3_eb35 (h16a3_u35 T)
theorem h16a3_L35 (T : Type16 x) (h : H16A3L35 T) : IsRupert (univ.image x) :=
  h16a2_leaf_gen T (by norm_num) h16a3_c35 (by decide) h16a3_ea35 h16a3_eb35 _
    (by decide) (by decide) (by decide) h
theorem h16a3_L35s (T : Type16 x) (h : H16A3L35 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a3_L35 T.sigma h)

/-- The tree's 34 robust arc leaves plus the round-12 leaf 35. -/
def H16A3Any (T : Type16 x) : Prop :=
  H16A2Any T ∨ H16A3L35 T ∨ H16A3L35 T.sigma

def H16ArcResid3 (T : Type16 x) : Prop := H16VResid T ∧ ¬ H16A3Any T

theorem h16a3_resid3_imp_resid2 (T : Type16 x) (h : H16ArcResid3 T) : H16ArcResid2 T :=
  ⟨h.1, fun ha => h.2 (Or.inl ha)⟩

theorem h16a3_any_isRupert (T : Type16 x) (h : H16A3Any T) : IsRupert (univ.image x) := by
  rcases h with h | h | h
  · exact h16a2_any_isRupert T h
  · exact h16a3_L35 T h
  · exact h16a3_L35s T h

theorem h16a3_rule_isRupert (T : Type16 x) (h : ¬ H16ArcResid3 T) : IsRupert (univ.image x) := by
  by_cases hv : H16VResid T
  · have : H16A3Any T := by
      by_contra hn; exact h ⟨hv, hn⟩
    exact h16a3_any_isRupert T this
  · exact h16v_rule_isRupert T hv

theorem h16a3_rule_false (hN : IsNopert (Finset.univ.image x)) (T : Type16 x)
    (h : ¬ H16ArcResid3 T) : False :=
  hN.2 (h16a3_rule_isRupert T h)

end H16A
end Minimality
