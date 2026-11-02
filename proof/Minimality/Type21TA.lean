module

public import Minimality.Type21RobA

@[expose] public section

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace H21
variable {x : Fin 7 → ℝ³}

/-! Extra edge-view leaves at s06 s23 s25 s26 (all facing patterns; gen_seg.exe), absent from `h21b_seg4/5/6`. -/
def h21t_segX3 : List (h21b_SegSpec 3) := [
  ⟨2, 6, 2, 6, ![false, false, false, true, false, false, false, false], ![0, 4, 6]⟩,  -- s26 CvGvA-B-E-F-
  ⟨2, 6, 2, 6, ![true, true, true, true, true, true, true, false], ![2, 3, 5]⟩  -- s26 C^G^A+B+E+F+
]

def h21t_segX4 : List (h21b_SegSpec 4) := [
  ⟨0, 6, 2, 3, ![false, false, false, false, false, false, true, false], ![2, 3, 4, 6]⟩,  -- s06 CvDvE-F-H-
  ⟨0, 6, 2, 3, ![false, false, true, true, false, false, true, true], ![0, 4, 3, 5]⟩,  -- s06 C^D^E-F-H+
  ⟨0, 6, 2, 3, ![false, false, true, true, true, true, true, true], ![0, 4, 1, 5]⟩,  -- s06 C^D^E+F+H+
  ⟨2, 3, 6, 7, ![false, false, false, false, true, true, false, false], ![1, 4, 3, 5]⟩,  -- s23 GvHvA-B-D-
  ⟨2, 3, 6, 7, ![true, true, false, false, true, true, false, false], ![0, 4, 3, 5]⟩,  -- s23 GvHvA+B+D-
  ⟨2, 3, 6, 7, ![true, true, false, true, true, true, true, true], ![0, 5, 2, 6]⟩,  -- s23 G^H^A+B+D+
  ⟨2, 5, 2, 7, ![false, true, false, false, false, true, false, false], ![0, 1, 3, 5]⟩,  -- s25 CvHvA-D-E-
  ⟨2, 5, 2, 7, ![true, true, false, false, true, true, false, false], ![0, 4, 3, 5]⟩,  -- s25 CvHvA+D-E+
  ⟨2, 5, 2, 7, ![true, true, true, true, true, true, false, true], ![2, 3, 4, 6]⟩,  -- s25 C^H^A+D+E+
  ⟨2, 6, 2, 6, ![true, false, false, true, false, false, false, false], ![0, 1, 4, 6]⟩,  -- s26 CvGvA+B-E-F-
  ⟨2, 6, 2, 6, ![true, true, true, true, true, false, true, false], ![1, 3, 2, 5]⟩  -- s26 C^G^A+B+E+F-
]

def h21t_segX5 : List (h21b_SegSpec 5) := [
  ⟨0, 6, 2, 3, ![false, false, true, true, false, false, true, false], ![0, 4, 3, 2, 5]⟩,  -- s06 C^D^E-F-H-
  ⟨0, 6, 2, 3, ![false, false, false, false, true, false, true, false], ![1, 3, 2, 6, 4]⟩,  -- s06 CvDvE+F-H-
  ⟨0, 6, 2, 3, ![false, false, false, false, false, false, true, true], ![2, 5, 3, 4, 6]⟩,  -- s06 CvDvE-F-H+
  ⟨0, 6, 2, 3, ![false, false, true, true, true, false, true, true], ![0, 4, 1, 3, 5]⟩,  -- s06 C^D^E+F-H+
  ⟨0, 6, 2, 3, ![false, false, true, true, false, true, true, true], ![0, 4, 3, 1, 5]⟩,  -- s06 C^D^E-F+H+
  ⟨0, 6, 2, 3, ![false, false, false, false, true, true, true, true], ![1, 4, 6, 2, 5]⟩,  -- s06 CvDvE+F+H+
  ⟨2, 3, 6, 7, ![false, false, false, false, true, true, true, true], ![1, 4, 6, 2, 5]⟩,  -- s23 G^H^A-B-D-
  ⟨2, 3, 6, 7, ![true, false, false, false, true, true, false, false], ![0, 1, 5, 3, 4]⟩,  -- s23 GvHvA+B-D-
  ⟨2, 3, 6, 7, ![false, true, false, false, true, true, false, false], ![0, 1, 4, 3, 5]⟩,  -- s23 GvHvA-B+D-
  ⟨2, 3, 6, 7, ![true, true, false, false, true, true, true, true], ![0, 4, 6, 2, 5]⟩,  -- s23 G^H^A+B+D-
  ⟨2, 3, 6, 7, ![true, false, false, true, true, true, true, true], ![0, 1, 5, 2, 6]⟩,  -- s23 G^H^A+B-D+
  ⟨2, 3, 6, 7, ![true, true, false, true, true, true, false, false], ![0, 5, 3, 4, 6]⟩,  -- s23 GvHvA+B+D+
  ⟨2, 5, 2, 7, ![false, true, true, false, false, true, false, true], ![0, 1, 3, 2, 6]⟩,  -- s25 C^H^A-D-E-
  ⟨2, 5, 2, 7, ![true, true, false, false, false, true, false, false], ![0, 4, 1, 3, 5]⟩,  -- s25 CvHvA+D-E-
  ⟨2, 5, 2, 7, ![true, true, true, true, false, true, false, true], ![1, 3, 2, 6, 4]⟩,  -- s25 C^H^A+D+E-
  ⟨2, 5, 2, 7, ![false, true, false, false, true, true, false, false], ![0, 1, 4, 3, 5]⟩,  -- s25 CvHvA-D-E+
  ⟨2, 5, 2, 7, ![true, true, true, false, true, true, false, true], ![0, 4, 3, 2, 6]⟩,  -- s25 C^H^A+D-E+
  ⟨2, 5, 2, 7, ![true, true, false, true, true, true, false, false], ![0, 5, 3, 4, 6]⟩,  -- s25 CvHvA+D+E+
  ⟨2, 6, 2, 6, ![false, false, true, true, false, false, true, false], ![0, 4, 3, 2, 5]⟩,  -- s26 C^G^A-B-E-F-
  ⟨2, 6, 2, 6, ![true, true, false, true, false, false, false, false], ![0, 5, 1, 4, 6]⟩,  -- s26 CvGvA+B+E-F-
  ⟨2, 6, 2, 6, ![true, true, true, true, false, false, true, false], ![1, 4, 3, 2, 5]⟩,  -- s26 C^G^A+B+E-F-
  ⟨2, 6, 2, 6, ![true, false, false, true, true, false, false, false], ![0, 1, 3, 4, 6]⟩,  -- s26 CvGvA+B-E+F-
  ⟨2, 6, 2, 6, ![true, false, true, true, true, false, true, false], ![0, 1, 3, 2, 5]⟩,  -- s26 C^G^A+B-E+F-
  ⟨2, 6, 2, 6, ![true, true, false, true, true, true, false, false], ![0, 5, 3, 4, 6]⟩  -- s26 CvGvA+B+E+F+
]

def h21t_segX6 : List (h21b_SegSpec 6) := [
  ⟨0, 6, 2, 3, ![false, false, true, true, true, false, true, false], ![0, 4, 1, 3, 2, 5]⟩,  -- s06 C^D^E+F-H-
  ⟨0, 6, 2, 3, ![false, false, false, false, true, true, true, false], ![1, 4, 6, 2, 3, 5]⟩,  -- s06 CvDvE+F+H-
  ⟨0, 6, 2, 3, ![false, false, false, false, true, false, true, true], ![1, 3, 5, 2, 6, 4]⟩,  -- s06 CvDvE+F-H+
  ⟨0, 6, 2, 3, ![false, false, false, false, false, true, true, true], ![1, 3, 4, 6, 2, 5]⟩,  -- s06 CvDvE-F+H+
  ⟨2, 3, 6, 7, ![true, false, false, false, true, true, true, true], ![0, 1, 5, 2, 6, 4]⟩,  -- s23 G^H^A+B-D-
  ⟨2, 3, 6, 7, ![false, true, false, false, true, true, true, true], ![0, 1, 4, 6, 2, 5]⟩,  -- s23 G^H^A-B+D-
  ⟨2, 3, 6, 7, ![false, false, false, true, true, true, true, true], ![0, 4, 1, 5, 2, 6]⟩,  -- s23 G^H^A-B-D+
  ⟨2, 3, 6, 7, ![true, false, false, true, true, true, false, false], ![0, 1, 5, 3, 4, 6]⟩,  -- s23 GvHvA+B-D+
  ⟨2, 5, 2, 7, ![true, true, true, false, false, true, false, true], ![0, 4, 1, 3, 2, 6]⟩,  -- s25 C^H^A+D-E-
  ⟨2, 5, 2, 7, ![false, true, true, true, false, true, false, true], ![0, 1, 3, 2, 6, 4]⟩,  -- s25 C^H^A-D+E-
  ⟨2, 5, 2, 7, ![true, true, false, true, false, true, false, false], ![0, 5, 3, 1, 4, 6]⟩,  -- s25 CvHvA+D+E-
  ⟨2, 5, 2, 7, ![false, true, true, false, true, true, false, true], ![0, 1, 4, 3, 2, 6]⟩,  -- s25 C^H^A-D-E+
  ⟨2, 6, 2, 6, ![true, false, true, true, false, false, true, false], ![0, 1, 4, 3, 2, 5]⟩,  -- s26 C^G^A+B-E-F-
  ⟨2, 6, 2, 6, ![false, true, true, true, false, false, true, false], ![0, 1, 5, 2, 3, 4]⟩,  -- s26 C^G^A-B+E-F-
  ⟨2, 6, 2, 6, ![false, false, true, true, true, false, true, false], ![0, 4, 1, 3, 2, 5]⟩,  -- s26 C^G^A-B-E+F-
  ⟨2, 6, 2, 6, ![true, true, false, true, true, false, false, false], ![0, 5, 1, 3, 4, 6]⟩,  -- s26 CvGvA+B+E+F-
  ⟨2, 6, 2, 6, ![true, true, false, true, false, true, false, false], ![0, 5, 3, 1, 4, 6]⟩,  -- s26 CvGvA+B+E-F+
  ⟨2, 6, 2, 6, ![true, false, false, true, true, true, false, false], ![0, 1, 5, 3, 4, 6]⟩  -- s26 CvGvA+B-E+F+
]


set_option maxRecDepth 100000 in
theorem h21t_segX3_good : ∀ s ∈ h21t_segX3, s.Good := by decide +kernel
set_option maxRecDepth 100000 in
theorem h21t_segX4_good : ∀ s ∈ h21t_segX4, s.Good := by decide +kernel
set_option maxRecDepth 100000 in
theorem h21t_segX5_good : ∀ s ∈ h21t_segX5, s.Good := by decide +kernel
set_option maxRecDepth 100000 in
theorem h21t_segX6_good : ∀ s ∈ h21t_segX6, s.Good := by decide +kernel

def h21t_NoSegX (T : Facets21 x) : Prop :=
  (∀ s ∈ h21t_segX3, ¬ h21rSegCond T s) ∧ (∀ s ∈ h21t_segX4, ¬ h21rSegCond T s) ∧
  (∀ s ∈ h21t_segX5, ¬ h21rSegCond T s) ∧ (∀ s ∈ h21t_segX6, ¬ h21rSegCond T s)

/-- The residual of the robust rule, with the four missing edge views s06 s23 s25 s26 added. -/
def H21Resid4 (T : Facets21 x) : Prop := H21Resid3 T ∧ h21t_NoSegX T

theorem h21t_resid4_imp (T : Facets21 x) (h : H21Resid4 T) : H21Resid3 T := h.1

theorem h21t_rule_isRupert (T : Facets21 x) (h : ¬ H21Resid4 T) : IsRupert (univ.image x) := by
  by_contra hR
  apply h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · by_contra h3
    exact hR (h21r_rule_isRupert T h3)
  · exact fun s hs hc => hR (h21r_seg_rupert T s (h21t_segX3_good s hs) hc)
  · exact fun s hs hc => hR (h21r_seg_rupert T s (h21t_segX4_good s hs) hc)
  · exact fun s hs hc => hR (h21r_seg_rupert T s (h21t_segX5_good s hs) hc)
  · exact fun s hs hc => hR (h21r_seg_rupert T s (h21t_segX6_good s hs) hc)

theorem h21t_rule_false (hN : IsNopert (Finset.univ.image x)) (T : Facets21 x)
    (h : ¬ H21Resid4 T) : False :=
  hN.2 (h21t_rule_isRupert T h)

end H21
end Minimality
