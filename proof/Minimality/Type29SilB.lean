module

public import Minimality.Type29SilA

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

def h29s_c1 : ZMod 5 → Fin 7 := ![0, 2, 4, 6, 5]
theorem h29s_W1 (T : Facets29 x) 
    (hU : Uni (fun i : ZMod 5 => ⟪x (h29s_c1 i), x 3 - x 1⟫)) : IsRupert (univ.image x) :=
  h29s_leaf_gen T (by norm_num) h29s_c1 (by decide) ![2, 6, 7, 8, 3] ![0, 4, 5, 5, 1] 1 3
    (by decide) (by decide) (by decide)
    (fun i => by fin_cases i <;> first | exact Fac9.up _ _ (by decide) (by decide) )
    (fun i => by fin_cases i <;> first | exact Fac9.dn _ _ (by decide) (by decide) ) hU

def h29s_c2 : ZMod 4 → Fin 7 := ![0, 1, 4, 3]
theorem h29s_W2 (T : Facets29 x) (hB : 0 < T.f015.f (x 6) - T.f015.f (x 2)) (hD : 0 < T.f035.f (x 6) - T.f035.f (x 2))
    (hU : Uni (fun i : ZMod 4 => ⟪x (h29s_c2 i), x 6 - x 2⟫)) : IsRupert (univ.image x) :=
  h29s_leaf_gen T (by norm_num) h29s_c2 (by decide) ![1, 5, 7, 3] ![0, 4, 6, 2] 2 6
    (by decide) (by decide) (by decide)
    (fun i => by fin_cases i <;> first | exact Fac9.up _ _ (by decide) (by decide) | exact hB | exact hD)
    (fun i => by fin_cases i <;> first | exact Fac9.dn _ _ (by decide) (by decide) | exact hB | exact hD) hU

def h29s_c3 : ZMod 5 → Fin 7 := ![0, 3, 4, 1, 5]
theorem h29s_W3 (T : Facets29 x) (hB : T.f015.f (x 6) - T.f015.f (x 2) < 0) (hD : 0 < T.f035.f (x 6) - T.f035.f (x 2))
    (hU : Uni (fun i : ZMod 5 => ⟪x (h29s_c3 i), x 6 - x 2⟫)) : IsRupert (univ.image x) :=
  h29s_leaf_gen T (by norm_num) h29s_c3 (by decide) ![3, 7, 5, 5, 3] ![2, 6, 4, 1, 1] 2 6
    (by decide) (by decide) (by decide)
    (fun i => by fin_cases i <;> first | exact Fac9.up _ _ (by decide) (by decide) | exact hB | exact hD)
    (fun i => by fin_cases i <;> first | exact Fac9.dn _ _ (by decide) (by decide) | exact hB | exact hD) hU

def h29s_c4 : ZMod 4 → Fin 7 := ![1, 4, 3, 5]
theorem h29s_W4 (T : Facets29 x) (hB : T.f015.f (x 6) - T.f015.f (x 2) < 0) (hD : T.f035.f (x 6) - T.f035.f (x 2) < 0)
    (hU : Uni (fun i : ZMod 4 => ⟪x (h29s_c4 i), x 6 - x 2⟫)) : IsRupert (univ.image x) :=
  h29s_leaf_gen T (by norm_num) h29s_c4 (by decide) ![5, 7, 8, 5] ![4, 6, 3, 1] 2 6
    (by decide) (by decide) (by decide)
    (fun i => by fin_cases i <;> first | exact Fac9.up _ _ (by decide) (by decide) | exact hB | exact hD)
    (fun i => by fin_cases i <;> first | exact Fac9.dn _ _ (by decide) (by decide) | exact hB | exact hD) hU

def h29s_c5 : ZMod 4 → Fin 7 := ![1, 2, 3, 5]
theorem h29s_W5 (T : Facets29 x) (hE : 0 < T.f124.f (x 6) - T.f124.f (x 0)) (hG : 0 < T.f234.f (x 6) - T.f234.f (x 0))
    (hU : Uni (fun i : ZMod 4 => ⟪x (h29s_c5 i), x 6 - x 0⟫)) : IsRupert (univ.image x) :=
  h29s_leaf_gen T (by norm_num) h29s_c5 (by decide) ![4, 6, 8, 5] ![0, 2, 3, 1] 0 6
    (by decide) (by decide) (by decide)
    (fun i => by fin_cases i <;> first | exact Fac9.up _ _ (by decide) (by decide) | exact hE | exact hG)
    (fun i => by fin_cases i <;> first | exact Fac9.dn _ _ (by decide) (by decide) | exact hE | exact hG) hU

def h29s_c6 : ZMod 5 → Fin 7 := ![1, 4, 2, 3, 5]
theorem h29s_W6 (T : Facets29 x) (hE : T.f124.f (x 6) - T.f124.f (x 0) < 0) (hG : 0 < T.f234.f (x 6) - T.f234.f (x 0))
    (hU : Uni (fun i : ZMod 5 => ⟪x (h29s_c6 i), x 6 - x 0⟫)) : IsRupert (univ.image x) :=
  h29s_leaf_gen T (by norm_num) h29s_c6 (by decide) ![5, 6, 6, 8, 5] ![4, 4, 2, 3, 1] 0 6
    (by decide) (by decide) (by decide)
    (fun i => by fin_cases i <;> first | exact Fac9.up _ _ (by decide) (by decide) | exact hE | exact hG)
    (fun i => by fin_cases i <;> first | exact Fac9.dn _ _ (by decide) (by decide) | exact hE | exact hG) hU

def h29s_c7 : ZMod 5 → Fin 7 := ![1, 2, 4, 3, 5]
theorem h29s_W7 (T : Facets29 x) (hE : 0 < T.f124.f (x 6) - T.f124.f (x 0)) (hG : T.f234.f (x 6) - T.f234.f (x 0) < 0)
    (hU : Uni (fun i : ZMod 5 => ⟪x (h29s_c7 i), x 6 - x 0⟫)) : IsRupert (univ.image x) :=
  h29s_leaf_gen T (by norm_num) h29s_c7 (by decide) ![4, 4, 7, 8, 5] ![0, 6, 6, 3, 1] 0 6
    (by decide) (by decide) (by decide)
    (fun i => by fin_cases i <;> first | exact Fac9.up _ _ (by decide) (by decide) | exact hE | exact hG)
    (fun i => by fin_cases i <;> first | exact Fac9.dn _ _ (by decide) (by decide) | exact hE | exact hG) hU

def h29s_c8 : ZMod 4 → Fin 7 := ![1, 4, 3, 5]
theorem h29s_W8 (T : Facets29 x) (hE : T.f124.f (x 6) - T.f124.f (x 0) < 0) (hG : T.f234.f (x 6) - T.f234.f (x 0) < 0)
    (hU : Uni (fun i : ZMod 4 => ⟪x (h29s_c8 i), x 6 - x 0⟫)) : IsRupert (univ.image x) :=
  h29s_leaf_gen T (by norm_num) h29s_c8 (by decide) ![5, 7, 8, 5] ![4, 6, 3, 1] 0 6
    (by decide) (by decide) (by decide)
    (fun i => by fin_cases i <;> first | exact Fac9.up _ _ (by decide) (by decide) | exact hE | exact hG)
    (fun i => by fin_cases i <;> first | exact Fac9.dn _ _ (by decide) (by decide) | exact hE | exact hG) hU

def h29s_c9 : ZMod 4 → Fin 7 := ![0, 1, 4, 3]
theorem h29s_W9 (T : Facets29 x) (hH : 0 < T.f346.f (x 5) - T.f346.f (x 2))
    (hU : Uni (fun i : ZMod 4 => ⟪x (h29s_c9 i), x 5 - x 2⟫)) : IsRupert (univ.image x) :=
  h29s_leaf_gen T (by norm_num) h29s_c9 (by decide) ![1, 5, 7, 3] ![0, 4, 6, 2] 2 5
    (by decide) (by decide) (by decide)
    (fun i => by fin_cases i <;> first | exact Fac9.up _ _ (by decide) (by decide) | exact hH)
    (fun i => by fin_cases i <;> first | exact Fac9.dn _ _ (by decide) (by decide) | exact hH) hU

def h29s_c10 : ZMod 5 → Fin 7 := ![0, 1, 4, 6, 3]
theorem h29s_W10 (T : Facets29 x) (hH : T.f346.f (x 5) - T.f346.f (x 2) < 0)
    (hU : Uni (fun i : ZMod 5 => ⟪x (h29s_c10 i), x 5 - x 2⟫)) : IsRupert (univ.image x) :=
  h29s_leaf_gen T (by norm_num) h29s_c10 (by decide) ![1, 5, 5, 8, 3] ![0, 4, 7, 7, 2] 2 5
    (by decide) (by decide) (by decide)
    (fun i => by fin_cases i <;> first | exact Fac9.up _ _ (by decide) (by decide) | exact hH)
    (fun i => by fin_cases i <;> first | exact Fac9.dn _ _ (by decide) (by decide) | exact hH) hU

def h29s_c11 : ZMod 4 → Fin 7 := ![1, 2, 3, 5]
theorem h29s_W11 (T : Facets29 x) (hI : 0 < T.f356.f (x 4) - T.f356.f (x 0))
    (hU : Uni (fun i : ZMod 4 => ⟪x (h29s_c11 i), x 4 - x 0⟫)) : IsRupert (univ.image x) :=
  h29s_leaf_gen T (by norm_num) h29s_c11 (by decide) ![4, 6, 8, 5] ![0, 2, 3, 1] 0 4
    (by decide) (by decide) (by decide)
    (fun i => by fin_cases i <;> first | exact Fac9.up _ _ (by decide) (by decide) | exact hI)
    (fun i => by fin_cases i <;> first | exact Fac9.dn _ _ (by decide) (by decide) | exact hI) hU

def h29s_c12 : ZMod 5 → Fin 7 := ![1, 2, 3, 6, 5]
theorem h29s_W12 (T : Facets29 x) (hI : T.f356.f (x 4) - T.f356.f (x 0) < 0)
    (hU : Uni (fun i : ZMod 5 => ⟪x (h29s_c12 i), x 4 - x 0⟫)) : IsRupert (univ.image x) :=
  h29s_leaf_gen T (by norm_num) h29s_c12 (by decide) ![4, 6, 7, 5, 5] ![0, 2, 8, 8, 1] 0 4
    (by decide) (by decide) (by decide)
    (fun i => by fin_cases i <;> first | exact Fac9.up _ _ (by decide) (by decide) | exact hI)
    (fun i => by fin_cases i <;> first | exact Fac9.dn _ _ (by decide) (by decide) | exact hI) hU

end H29S
end Minimality
