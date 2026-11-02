module

public import Minimality.Type21SilF

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace H21

variable {x : Fin 7 → ℝ³}

/-! ### S1: the six leaves (split views s03, s45; apex views s12, s16)

Facets `A..H = 0..7` (`014, 015, 0256, 046, 134, 135, 2346, 235`).  The depth hypothesis is
`Uni` of the depths `⟪x (c i), r⟫` along the cycle (log `<uni:VIEW:CYC>`). -/

/-- Cycles. -/
def cW1 : ZMod 5 → Fin 7 := ![1, 4, 6, 2, 5]
def cW2 : ZMod 5 → Fin 7 := ![0, 1, 3, 2, 6]
def cW3 : ZMod 4 → Fin 7 := ![0, 4, 3, 5]
def cW4 : ZMod 5 → Fin 7 := ![0, 5, 3, 4, 6]
def cW6 : ZMod 5 → Fin 7 := ![0, 4, 3, 2, 5]

/-- W1, view s03 (every facet contains an endpoint): cycle 1 4 6 2 5. -/
theorem h21_W1 (T : Facets21 x)
    (hU : Uni (fun i : ZMod 5 => ⟪x (cW1 i), x 3 - x 0⟫)) : IsRupert (univ.image x) :=
  leaf_gen T (by norm_num) cW1 (by decide) ![4, 6, 6, 7, 5] ![0, 3, 2, 2, 1] 0 3
    (by decide) (by decide) (by decide)
    (fun i => by fin_cases i <;> exact Fac8.up _ _ (by decide) (by decide))
    (fun i => by fin_cases i <;> exact Fac8.dn _ _ (by decide) (by decide)) hU

/-- W2, view s45: cycle 0 1 3 2 6. -/
theorem h21_W2 (T : Facets21 x)
    (hU : Uni (fun i : ZMod 5 => ⟪x (cW2 i), x 5 - x 4⟫)) : IsRupert (univ.image x) :=
  leaf_gen T (by norm_num) cW2 (by decide) ![1, 5, 7, 2, 2] ![0, 4, 6, 6, 3] 4 5
    (by decide) (by decide) (by decide)
    (fun i => by fin_cases i <;> exact Fac8.up _ _ (by decide) (by decide))
    (fun i => by fin_cases i <;> exact Fac8.dn _ _ (by decide) (by decide)) hU

/-- W3, view s12, D up (`φ_D(1,2) > 0`): cycle 0 4 3 5. -/
theorem h21_W3 (T : Facets21 x) (hD : 0 < T.f046.f (x 2) - T.f046.f (x 1))
    (hU : Uni (fun i : ZMod 4 => ⟪x (cW3 i), x 2 - x 1⟫)) : IsRupert (univ.image x) :=
  leaf_gen T (by norm_num) cW3 (by decide) ![3, 6, 7, 2] ![0, 4, 5, 1] 1 2
    (by decide) (by decide) (by decide)
    (fun i => by
      fin_cases i
      · exact hD
      all_goals exact Fac8.up _ _ (by decide) (by decide))
    (fun i => by fin_cases i <;> exact Fac8.dn _ _ (by decide) (by decide)) hU

/-- W4, view s12, D down (`φ_D(1,2) < 0`): cycle 0 5 3 4 6. -/
theorem h21_W4 (T : Facets21 x) (hD : T.f046.f (x 2) - T.f046.f (x 1) < 0)
    (hU : Uni (fun i : ZMod 5 => ⟪x (cW4 i), x 2 - x 1⟫)) : IsRupert (univ.image x) :=
  leaf_gen T (by norm_num) cW4 (by decide) ![2, 7, 6, 6, 2] ![1, 5, 4, 3, 3] 1 2
    (by decide) (by decide) (by decide)
    (fun i => by fin_cases i <;> exact Fac8.up _ _ (by decide) (by decide))
    (fun i => by
      fin_cases i
      · exact Fac8.dn _ _ (by decide) (by decide)
      · exact Fac8.dn _ _ (by decide) (by decide)
      · exact Fac8.dn _ _ (by decide) (by decide)
      · exact hD
      · exact hD) hU

/-- W5, view s16, H up (`φ_H(1,6) > 0`): cycle 0 4 3 5. -/
theorem h21_W5 (T : Facets21 x) (hH : 0 < T.f235.f (x 6) - T.f235.f (x 1))
    (hU : Uni (fun i : ZMod 4 => ⟪x (cW3 i), x 6 - x 1⟫)) : IsRupert (univ.image x) :=
  leaf_gen T (by norm_num) cW3 (by decide) ![3, 6, 7, 2] ![0, 4, 5, 1] 1 6
    (by decide) (by decide) (by decide)
    (fun i => by
      fin_cases i
      · exact Fac8.up _ _ (by decide) (by decide)
      · exact Fac8.up _ _ (by decide) (by decide)
      · exact hH
      · exact Fac8.up _ _ (by decide) (by decide))
    (fun i => by fin_cases i <;> exact Fac8.dn _ _ (by decide) (by decide)) hU

/-- W6, view s16, H down (`φ_H(1,6) < 0`): cycle 0 4 3 2 5. -/
theorem h21_W6 (T : Facets21 x) (hH : T.f235.f (x 6) - T.f235.f (x 1) < 0)
    (hU : Uni (fun i : ZMod 5 => ⟪x (cW6 i), x 6 - x 1⟫)) : IsRupert (univ.image x) :=
  leaf_gen T (by norm_num) cW6 (by decide) ![3, 6, 6, 2, 2] ![0, 4, 7, 7, 1] 1 6
    (by decide) (by decide) (by decide)
    (fun i => by fin_cases i <;> exact Fac8.up _ _ (by decide) (by decide))
    (fun i => by
      fin_cases i
      · exact Fac8.dn _ _ (by decide) (by decide)
      · exact Fac8.dn _ _ (by decide) (by decide)
      · exact hH
      · exact hH
      · exact Fac8.dn _ _ (by decide) (by decide)) hU

end H21
end Minimality
