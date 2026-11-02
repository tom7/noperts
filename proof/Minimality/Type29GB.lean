module

public import Minimality.Type29GA

@[expose] public section

/-!
# H29G-B: the 25 edge-view leaves of `Type29SilE` are generic leaves
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace H29S
open Minimality.H21

variable {x : Fin 7 → ℝ³}

theorem h29g_cond1 (T : Facets29 x) (h : H29SilE1 T) : h29s2_L1.Cond (s0x_fac29 T) := by
  obtain ⟨l0, l1, l2, hU⟩ := h
  refine ⟨?_, hU⟩
  intro t h0 h5
  fin_cases t
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact ⟨fun _ => l0, fun h => absurd h (by decide)⟩
  · exact absurd h5 (by decide)
  · exact ⟨fun _ => l1, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => l2, fun h => absurd h (by decide)⟩
  · exact absurd h5 (by decide)

theorem h29g_E1 (T : Facets29 x) (hr : H29GenResid T) : ¬ H29SilE1 T := fun h =>
  hr.1 0 5 h29s2_L1.pat
    ⟨by decide, (h29g_cond1 T h).1,
      h29g_robUni_tr _ (by decide) h29s2_L1.c (by decide) _ (h29g_cond1 T h).2⟩

theorem h29g_cond2 (T : Facets29 x) (h : H29SilE2 T) : h29s2_L2.Cond (s0x_fac29 T) := by
  obtain ⟨l0, l1, l2, hU⟩ := h
  refine ⟨?_, hU⟩
  intro t h0 h5
  fin_cases t
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact ⟨fun h => absurd h (by decide), fun _ => l0⟩
  · exact absurd h5 (by decide)
  · exact ⟨fun h => absurd h (by decide), fun _ => l1⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => l2⟩
  · exact absurd h5 (by decide)

theorem h29g_E2 (T : Facets29 x) (hr : H29GenResid T) : ¬ H29SilE2 T := fun h =>
  hr.1 0 5 h29s2_L2.pat
    ⟨by decide, (h29g_cond2 T h).1,
      h29g_robUni_tr _ (by decide) h29s2_L2.c (by decide) _ (h29g_cond2 T h).2⟩

theorem h29g_cond3 (T : Facets29 x) (h : H29SilE3 T) : h29s2_L3.Cond (s0x_fac29 T) := by
  obtain ⟨l0, l1, l2, hU⟩ := h
  refine ⟨?_, hU⟩
  intro t h0 h5
  fin_cases t
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact ⟨fun h => absurd h (by decide), fun _ => l0⟩
  · exact absurd h5 (by decide)
  · exact ⟨fun h => absurd h (by decide), fun _ => l1⟩
  · exact ⟨fun _ => l2, fun h => absurd h (by decide)⟩
  · exact absurd h5 (by decide)

theorem h29g_E3 (T : Facets29 x) (hr : H29GenResid T) : ¬ H29SilE3 T := fun h =>
  hr.1 0 5 h29s2_L3.pat
    ⟨by decide, (h29g_cond3 T h).1,
      h29g_robUni_tr _ (by decide) h29s2_L3.c (by decide) _ (h29g_cond3 T h).2⟩

theorem h29g_cond4 (T : Facets29 x) (h : H29SilE4 T) : h29s2_L4.Cond (s0x_fac29 T) := by
  obtain ⟨l0, l1, l2, hU⟩ := h
  refine ⟨?_, hU⟩
  intro t h0 h5
  fin_cases t
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact ⟨fun _ => l0, fun h => absurd h (by decide)⟩
  · exact absurd h5 (by decide)
  · exact ⟨fun _ => l1, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => l2, fun h => absurd h (by decide)⟩
  · exact absurd h5 (by decide)

theorem h29g_E4 (T : Facets29 x) (hr : H29GenResid T) : ¬ H29SilE4 T := fun h =>
  hr.1 0 5 h29s2_L4.pat
    ⟨by decide, (h29g_cond4 T h).1,
      h29g_robUni_tr _ (by decide) h29s2_L4.c (by decide) _ (h29g_cond4 T h).2⟩

theorem h29g_cond5 (T : Facets29 x) (h : H29SilE5 T) : h29s2_L5.Cond (s0x_fac29 T) := by
  obtain ⟨l0, l1, l2, hU⟩ := h
  refine ⟨?_, hU⟩
  intro t h0 h5
  fin_cases t
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact ⟨fun h => absurd h (by decide), fun _ => l0⟩
  · exact absurd h5 (by decide)
  · exact ⟨fun _ => l1, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => l2, fun h => absurd h (by decide)⟩
  · exact absurd h5 (by decide)

theorem h29g_E5 (T : Facets29 x) (hr : H29GenResid T) : ¬ H29SilE5 T := fun h =>
  hr.1 0 5 h29s2_L5.pat
    ⟨by decide, (h29g_cond5 T h).1,
      h29g_robUni_tr _ (by decide) h29s2_L5.c (by decide) _ (h29g_cond5 T h).2⟩

theorem h29g_cond6 (T : Facets29 x) (h : H29SilE6 T) : h29s2_L6.Cond (s0x_fac29 T) := by
  obtain ⟨l0, l1, l2, hU⟩ := h
  refine ⟨?_, hU⟩
  intro t h0 h5
  fin_cases t
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact ⟨fun h => absurd h (by decide), fun _ => l0⟩
  · exact absurd h5 (by decide)
  · exact ⟨fun _ => l1, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => l2, fun h => absurd h (by decide)⟩
  · exact absurd h5 (by decide)

theorem h29g_E6 (T : Facets29 x) (hr : H29GenResid T) : ¬ H29SilE6 T := fun h =>
  hr.1 0 5 h29s2_L6.pat
    ⟨by decide, (h29g_cond6 T h).1,
      h29g_robUni_tr _ (by decide) h29s2_L6.c (by decide) _ (h29g_cond6 T h).2⟩

theorem h29g_cond7 (T : Facets29 x) (h : H29SilE7 T) : h29s2_L7.Cond (s0x_fac29 T) := by
  obtain ⟨l0, l1, l2, hU⟩ := h
  refine ⟨?_, hU⟩
  intro t h0 h5
  fin_cases t
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact ⟨fun _ => l0, fun h => absurd h (by decide)⟩
  · exact absurd h5 (by decide)
  · exact ⟨fun h => absurd h (by decide), fun _ => l1⟩
  · exact ⟨fun _ => l2, fun h => absurd h (by decide)⟩
  · exact absurd h5 (by decide)

theorem h29g_E7 (T : Facets29 x) (hr : H29GenResid T) : ¬ H29SilE7 T := fun h =>
  hr.1 0 5 h29s2_L7.pat
    ⟨by decide, (h29g_cond7 T h).1,
      h29g_robUni_tr _ (by decide) h29s2_L7.c (by decide) _ (h29g_cond7 T h).2⟩

theorem h29g_cond8 (T : Facets29 x) (h : H29SilE8 T) : h29s2_L8.Cond (s0x_fac29 T) := by
  obtain ⟨l0, l1, l2, hU⟩ := h
  refine ⟨?_, hU⟩
  intro t h0 h5
  fin_cases t
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact ⟨fun h => absurd h (by decide), fun _ => l0⟩
  · exact absurd h5 (by decide)
  · exact ⟨fun h => absurd h (by decide), fun _ => l1⟩
  · exact ⟨fun _ => l2, fun h => absurd h (by decide)⟩
  · exact absurd h5 (by decide)

theorem h29g_E8 (T : Facets29 x) (hr : H29GenResid T) : ¬ H29SilE8 T := fun h =>
  hr.1 0 5 h29s2_L8.pat
    ⟨by decide, (h29g_cond8 T h).1,
      h29g_robUni_tr _ (by decide) h29s2_L8.c (by decide) _ (h29g_cond8 T h).2⟩

theorem h29g_cond9 (T : Facets29 x) (h : H29SilE9 T) : h29s2_L9.Cond (s0x_fac29 T) := by
  obtain ⟨l0, l1, l2, hU⟩ := h
  refine ⟨?_, hU⟩
  intro t h0 h5
  fin_cases t
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact ⟨fun _ => l0, fun h => absurd h (by decide)⟩
  · exact absurd h5 (by decide)
  · exact ⟨fun h => absurd h (by decide), fun _ => l1⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => l2⟩
  · exact absurd h5 (by decide)

theorem h29g_E9 (T : Facets29 x) (hr : H29GenResid T) : ¬ H29SilE9 T := fun h =>
  hr.1 0 5 h29s2_L9.pat
    ⟨by decide, (h29g_cond9 T h).1,
      h29g_robUni_tr _ (by decide) h29s2_L9.c (by decide) _ (h29g_cond9 T h).2⟩

theorem h29g_cond10 (T : Facets29 x) (h : H29SilE10 T) : h29s2_L10.Cond (s0x_fac29 T) := by
  obtain ⟨l0, l1, l2, hU⟩ := h
  refine ⟨?_, hU⟩
  intro t h0 h5
  fin_cases t
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact ⟨fun h => absurd h (by decide), fun _ => l0⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => l1⟩
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h5 (by decide)
  · exact absurd h5 (by decide)
  · exact ⟨fun h => absurd h (by decide), fun _ => l2⟩

theorem h29g_E10 (T : Facets29 x) (hr : H29GenResid T) : ¬ H29SilE10 T := fun h =>
  hr.1 1 4 h29s2_L10.pat
    ⟨by decide, (h29g_cond10 T h).1,
      h29g_robUni_tr _ (by decide) h29s2_L10.c (by decide) _ (h29g_cond10 T h).2⟩

theorem h29g_cond11 (T : Facets29 x) (h : H29SilE11 T) : h29s2_L11.Cond (s0x_fac29 T) := by
  obtain ⟨l0, l1, l2, hU⟩ := h
  refine ⟨?_, hU⟩
  intro t h0 h5
  fin_cases t
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact ⟨fun _ => l0, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => l1, fun h => absurd h (by decide)⟩
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h5 (by decide)
  · exact absurd h5 (by decide)
  · exact ⟨fun _ => l2, fun h => absurd h (by decide)⟩

theorem h29g_E11 (T : Facets29 x) (hr : H29GenResid T) : ¬ H29SilE11 T := fun h =>
  hr.1 1 4 h29s2_L11.pat
    ⟨by decide, (h29g_cond11 T h).1,
      h29g_robUni_tr _ (by decide) h29s2_L11.c (by decide) _ (h29g_cond11 T h).2⟩

theorem h29g_cond12 (T : Facets29 x) (h : H29SilE12 T) : h29s2_L12.Cond (s0x_fac29 T) := by
  obtain ⟨l0, l1, l2, hU⟩ := h
  refine ⟨?_, hU⟩
  intro t h0 h5
  fin_cases t
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact ⟨fun h => absurd h (by decide), fun _ => l0⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => l1⟩
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h5 (by decide)
  · exact absurd h5 (by decide)
  · exact ⟨fun _ => l2, fun h => absurd h (by decide)⟩

theorem h29g_E12 (T : Facets29 x) (hr : H29GenResid T) : ¬ H29SilE12 T := fun h =>
  hr.1 1 4 h29s2_L12.pat
    ⟨by decide, (h29g_cond12 T h).1,
      h29g_robUni_tr _ (by decide) h29s2_L12.c (by decide) _ (h29g_cond12 T h).2⟩

theorem h29g_cond13 (T : Facets29 x) (h : H29SilE13 T) : h29s2_L13.Cond (s0x_fac29 T) := by
  obtain ⟨l0, l1, l2, hU⟩ := h
  refine ⟨?_, hU⟩
  intro t h0 h5
  fin_cases t
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact ⟨fun _ => l0, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => l1⟩
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h5 (by decide)
  · exact absurd h5 (by decide)
  · exact ⟨fun h => absurd h (by decide), fun _ => l2⟩

theorem h29g_E13 (T : Facets29 x) (hr : H29GenResid T) : ¬ H29SilE13 T := fun h =>
  hr.1 1 4 h29s2_L13.pat
    ⟨by decide, (h29g_cond13 T h).1,
      h29g_robUni_tr _ (by decide) h29s2_L13.c (by decide) _ (h29g_cond13 T h).2⟩

theorem h29g_cond14 (T : Facets29 x) (h : H29SilE14 T) : h29s2_L14.Cond (s0x_fac29 T) := by
  obtain ⟨l0, l1, l2, hU⟩ := h
  refine ⟨?_, hU⟩
  intro t h0 h5
  fin_cases t
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact ⟨fun h => absurd h (by decide), fun _ => l0⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => l1⟩
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h5 (by decide)
  · exact absurd h5 (by decide)
  · exact ⟨fun _ => l2, fun h => absurd h (by decide)⟩

theorem h29g_E14 (T : Facets29 x) (hr : H29GenResid T) : ¬ H29SilE14 T := fun h =>
  hr.1 1 4 h29s2_L14.pat
    ⟨by decide, (h29g_cond14 T h).1,
      h29g_robUni_tr _ (by decide) h29s2_L14.c (by decide) _ (h29g_cond14 T h).2⟩

theorem h29g_cond15 (T : Facets29 x) (h : H29SilE15 T) : h29s2_L15.Cond (s0x_fac29 T) := by
  obtain ⟨l0, l1, l2, hU⟩ := h
  refine ⟨?_, hU⟩
  intro t h0 h5
  fin_cases t
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact ⟨fun h => absurd h (by decide), fun _ => l0⟩
  · exact ⟨fun _ => l1, fun h => absurd h (by decide)⟩
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h5 (by decide)
  · exact absurd h5 (by decide)
  · exact ⟨fun _ => l2, fun h => absurd h (by decide)⟩

theorem h29g_E15 (T : Facets29 x) (hr : H29GenResid T) : ¬ H29SilE15 T := fun h =>
  hr.1 1 4 h29s2_L15.pat
    ⟨by decide, (h29g_cond15 T h).1,
      h29g_robUni_tr _ (by decide) h29s2_L15.c (by decide) _ (h29g_cond15 T h).2⟩

theorem h29g_cond16 (T : Facets29 x) (h : H29SilE16 T) : h29s2_L16.Cond (s0x_fac29 T) := by
  obtain ⟨l0, l1, l2, hU⟩ := h
  refine ⟨?_, hU⟩
  intro t h0 h5
  fin_cases t
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact ⟨fun _ => l0, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => l1⟩
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h5 (by decide)
  · exact absurd h5 (by decide)
  · exact ⟨fun _ => l2, fun h => absurd h (by decide)⟩

theorem h29g_E16 (T : Facets29 x) (hr : H29GenResid T) : ¬ H29SilE16 T := fun h =>
  hr.1 1 4 h29s2_L16.pat
    ⟨by decide, (h29g_cond16 T h).1,
      h29g_robUni_tr _ (by decide) h29s2_L16.c (by decide) _ (h29g_cond16 T h).2⟩

theorem h29g_cond17 (T : Facets29 x) (h : H29SilE17 T) : h29s2_L17.Cond (s0x_fac29 T) := by
  obtain ⟨l0, l1, l2, hU⟩ := h
  refine ⟨?_, hU⟩
  intro t h0 h5
  fin_cases t
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact ⟨fun h => absurd h (by decide), fun _ => l0⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => l1⟩
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h5 (by decide)
  · exact absurd h5 (by decide)
  · exact ⟨fun h => absurd h (by decide), fun _ => l2⟩

theorem h29g_E17 (T : Facets29 x) (hr : H29GenResid T) : ¬ H29SilE17 T := fun h =>
  hr.1 1 4 h29s2_L17.pat
    ⟨by decide, (h29g_cond17 T h).1,
      h29g_robUni_tr _ (by decide) h29s2_L17.c (by decide) _ (h29g_cond17 T h).2⟩

theorem h29g_cond18 (T : Facets29 x) (h : H29SilE18 T) : h29s2_L18.Cond (s0x_fac29 T) := by
  obtain ⟨l0, l1, l2, hU⟩ := h
  refine ⟨?_, hU⟩
  intro t h0 h5
  fin_cases t
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h5 (by decide)
  · exact absurd h5 (by decide)
  · exact ⟨fun _ => l0, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => l1, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => l2⟩

theorem h29g_E18 (T : Facets29 x) (hr : H29GenResid T) : ¬ H29SilE18 T := fun h =>
  hr.1 0 1 h29s2_L18.pat
    ⟨by decide, (h29g_cond18 T h).1,
      h29g_robUni_tr _ (by decide) h29s2_L18.c (by decide) _ (h29g_cond18 T h).2⟩

theorem h29g_cond19 (T : Facets29 x) (h : H29SilE19 T) : h29s2_L19.Cond (s0x_fac29 T) := by
  obtain ⟨l0, l1, l2, hU⟩ := h
  refine ⟨?_, hU⟩
  intro t h0 h5
  fin_cases t
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h5 (by decide)
  · exact absurd h5 (by decide)
  · exact ⟨fun _ => l0, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => l1, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => l2, fun h => absurd h (by decide)⟩

theorem h29g_E19 (T : Facets29 x) (hr : H29GenResid T) : ¬ H29SilE19 T := fun h =>
  hr.1 0 1 h29s2_L19.pat
    ⟨by decide, (h29g_cond19 T h).1,
      h29g_robUni_tr _ (by decide) h29s2_L19.c (by decide) _ (h29g_cond19 T h).2⟩

theorem h29g_cond20 (T : Facets29 x) (h : H29SilE20 T) : h29s2_L20.Cond (s0x_fac29 T) := by
  obtain ⟨l0, l1, l2, hU⟩ := h
  refine ⟨?_, hU⟩
  intro t h0 h5
  fin_cases t
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h5 (by decide)
  · exact absurd h5 (by decide)
  · exact ⟨fun h => absurd h (by decide), fun _ => l0⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => l1⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => l2⟩

theorem h29g_E20 (T : Facets29 x) (hr : H29GenResid T) : ¬ H29SilE20 T := fun h =>
  hr.1 0 1 h29s2_L20.pat
    ⟨by decide, (h29g_cond20 T h).1,
      h29g_robUni_tr _ (by decide) h29s2_L20.c (by decide) _ (h29g_cond20 T h).2⟩

theorem h29g_cond21 (T : Facets29 x) (h : H29SilE21 T) : h29s2_L21.Cond (s0x_fac29 T) := by
  obtain ⟨l0, l1, l2, hU⟩ := h
  refine ⟨?_, hU⟩
  intro t h0 h5
  fin_cases t
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h5 (by decide)
  · exact absurd h5 (by decide)
  · exact ⟨fun _ => l0, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => l1⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => l2⟩

theorem h29g_E21 (T : Facets29 x) (hr : H29GenResid T) : ¬ H29SilE21 T := fun h =>
  hr.1 0 1 h29s2_L21.pat
    ⟨by decide, (h29g_cond21 T h).1,
      h29g_robUni_tr _ (by decide) h29s2_L21.c (by decide) _ (h29g_cond21 T h).2⟩

theorem h29g_cond22 (T : Facets29 x) (h : H29SilE22 T) : h29s2_L22.Cond (s0x_fac29 T) := by
  obtain ⟨l0, l1, hU⟩ := h
  refine ⟨?_, hU⟩
  intro t h0 h5
  fin_cases t
  · exact ⟨fun _ => l0, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => l1, fun h => absurd h (by decide)⟩
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h5 (by decide)
  · exact absurd h5 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)

theorem h29g_E22 (T : Facets29 x) (hr : H29GenResid T) : ¬ H29SilE22 T := fun h =>
  hr.1 3 4 h29s2_L22.pat
    ⟨by decide, (h29g_cond22 T h).1,
      h29g_robUni_tr _ (by decide) h29s2_L22.c (by decide) _ (h29g_cond22 T h).2⟩

theorem h29g_cond23 (T : Facets29 x) (h : H29SilE23 T) : h29s2_L23.Cond (s0x_fac29 T) := by
  obtain ⟨l0, l1, l2, hU⟩ := h
  refine ⟨?_, hU⟩
  intro t h0 h5
  fin_cases t
  · exact absurd h0 (by decide)
  · exact ⟨fun h => absurd h (by decide), fun _ => l0⟩
  · exact absurd h0 (by decide)
  · exact ⟨fun _ => l1, fun h => absurd h (by decide)⟩
  · exact absurd h0 (by decide)
  · exact absurd h5 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h5 (by decide)
  · exact ⟨fun _ => l2, fun h => absurd h (by decide)⟩

theorem h29g_E23 (T : Facets29 x) (hr : H29GenResid T) : ¬ H29SilE23 T := fun h =>
  hr.1 2 4 h29s2_L23.pat
    ⟨by decide, (h29g_cond23 T h).1,
      h29g_robUni_tr _ (by decide) h29s2_L23.c (by decide) _ (h29g_cond23 T h).2⟩

theorem h29g_cond24 (T : Facets29 x) (h : H29SilE24 T) : h29s2_L24.Cond (s0x_fac29 T) := by
  obtain ⟨l0, l1, l2, hU⟩ := h
  refine ⟨?_, hU⟩
  intro t h0 h5
  fin_cases t
  · exact absurd h0 (by decide)
  · exact ⟨fun _ => l0, fun h => absurd h (by decide)⟩
  · exact absurd h0 (by decide)
  · exact ⟨fun _ => l1, fun h => absurd h (by decide)⟩
  · exact absurd h0 (by decide)
  · exact absurd h5 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h5 (by decide)
  · exact ⟨fun _ => l2, fun h => absurd h (by decide)⟩

theorem h29g_E24 (T : Facets29 x) (hr : H29GenResid T) : ¬ H29SilE24 T := fun h =>
  hr.1 2 4 h29s2_L24.pat
    ⟨by decide, (h29g_cond24 T h).1,
      h29g_robUni_tr _ (by decide) h29s2_L24.c (by decide) _ (h29g_cond24 T h).2⟩

theorem h29g_cond25 (T : Facets29 x) (h : H29SilE25 T) : h29s2_L25.Cond (s0x_fac29 T) := by
  obtain ⟨l0, l1, hU⟩ := h
  refine ⟨?_, hU⟩
  intro t h0 h5
  fin_cases t
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact ⟨fun h => absurd h (by decide), fun _ => l0⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => l1⟩
  · exact absurd h5 (by decide)
  · exact absurd h5 (by decide)
  · exact absurd h5 (by decide)

theorem h29g_E25 (T : Facets29 x) (hr : H29GenResid T) : ¬ H29SilE25 T := fun h =>
  hr.1 0 3 h29s2_L25.pat
    ⟨by decide, (h29g_cond25 T h).1,
      h29g_robUni_tr _ (by decide) h29s2_L25.c (by decide) _ (h29g_cond25 T h).2⟩

theorem h29g_gen_imp_E (T : Facets29 x) (hr : H29GenResid T) :
    ¬ H29SilE1 T ∧
    ¬ H29SilE2 T ∧
    ¬ H29SilE3 T ∧
    ¬ H29SilE4 T ∧
    ¬ H29SilE5 T ∧
    ¬ H29SilE6 T ∧
    ¬ H29SilE7 T ∧
    ¬ H29SilE8 T ∧
    ¬ H29SilE9 T ∧
    ¬ H29SilE10 T ∧
    ¬ H29SilE11 T ∧
    ¬ H29SilE12 T ∧
    ¬ H29SilE13 T ∧
    ¬ H29SilE14 T ∧
    ¬ H29SilE15 T ∧
    ¬ H29SilE16 T ∧
    ¬ H29SilE17 T ∧
    ¬ H29SilE18 T ∧
    ¬ H29SilE19 T ∧
    ¬ H29SilE20 T ∧
    ¬ H29SilE21 T ∧
    ¬ H29SilE22 T ∧
    ¬ H29SilE23 T ∧
    ¬ H29SilE24 T ∧
    ¬ H29SilE25 T :=
  ⟨h29g_E1 T hr, h29g_E2 T hr, h29g_E3 T hr, h29g_E4 T hr, h29g_E5 T hr, h29g_E6 T hr, h29g_E7 T hr, h29g_E8 T hr, h29g_E9 T hr, h29g_E10 T hr, h29g_E11 T hr, h29g_E12 T hr, h29g_E13 T hr, h29g_E14 T hr, h29g_E15 T hr, h29g_E16 T hr, h29g_E17 T hr, h29g_E18 T hr, h29g_E19 T hr, h29g_E20 T hr, h29g_E21 T hr, h29g_E22 T hr, h29g_E23 T hr, h29g_E24 T hr, h29g_E25 T hr⟩

end H29S
end Minimality
