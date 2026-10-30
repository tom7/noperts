module

public import Minimality.Type08S.P2TX5

@[expose] public section

set_option relaxedAutoImplicit true
set_option autoImplicit true
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- Prop T* (i): at the touching, `X_ba' = (B, 0, 0, A)` is robust when `z_c < z_b` (`A > 0`, `B > 0`). -/
theorem touchT_Xba_robust {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hT : IsT a' b c d)
    (h : TouchT b b' c c' d) (hlt : ⟪c, b - d⟫ < ⟪b, b - d⟫) :
    ¬ Sep ⟪b, b - d⟫ ⟪b', b - d⟫ ⟪a', b - d⟫ ⟪c', b - d⟫ := by
  obtain ⟨e1, e2, e3, o, ν, v1, C0, w1, ha, w3, α1, α4, β1, γ4, β6, hF, hν, hv1, hha, hα, hα4, hγ4, hβ1,
    hβ6, hE, hu, hd, hb, hc, haa, ha', hb', hc', hv, hdep⟩ := h3_setup N hT
  have i3 := fun X Y z => inner_pt_3 hF o X Y z
  have ez : ∀ (p : ℝ³) (X Y z : ℝ), p = pt e1 e2 e3 o X Y z → ⟪p, b - d⟫ = ν * (z + ⟪o, e3⟫) := by
    intro p X Y z hp; rw [hdep, hp, i3, add_comm]
  have eA := ez a' _ _ _ ha'
  have eC := ez c _ _ _ hc
  have eC' := ez c' _ _ _ hc'
  have eB' := ez b' _ _ _ hb'
  obtain ⟨⟨h1, h2⟩, -, -⟩ := h
  have hAC : ⟪c, b - d⟫ < ⟪a', b - d⟫ := by rw [eA, eC]; nlinarith [mul_pos hβ6 hν, mul_pos hν hν]
  have hcc' : ⟪c', b - d⟫ = ⟪c, b - d⟫ := by rw [h2, h1]
  have hbb' : ⟪b', b - d⟫ = ⟪c, b - d⟫ := h1.symm
  intro hs; unfold Sep at hs; rcases hs with hs | hs
  · have := le_max_left ⟪a', b - d⟫ ⟪c', b - d⟫
    have h3 := min_le_right ⟪b, b - d⟫ ⟪b', b - d⟫
    linarith
  · have := le_max_left ⟪b, b - d⟫ ⟪b', b - d⟫
    have h3 := min_le_right ⟪a', b - d⟫ ⟪c', b - d⟫
    linarith

end Type08Sp
end Minimality
