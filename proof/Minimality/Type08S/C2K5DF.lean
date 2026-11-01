module

public import Minimality.Type08S.C2K5DE

@[expose] public section


/-!
# K5d / F: cell 1 frame lemmas for QPa (`ζ(a,c) < 0`) and QTT (`ζ(a,b') < 0, ζ(a,d) < 0`)
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem k5d_c1_pa_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {α4 γ4 β1 β6 γ6 : ℝ}
    (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hs : 1 < α4 + γ4) (hβ1 : 0 < β1) (hb6 : 0 < β6) (hγ6 : 0 < γ6)
    (hg6 : γ6 < 1 ∨ γ6 = 1) (hκ : α4 * (1 - β1) = 1 - γ4) (hζ : ⟪P, R⟫ < ⟪Q, R⟫)
    (hmem : ∀ i, fpoint P Q R d (k5dX1 α4 γ4 β1 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨
      y = fpoint P Q R d (α4, γ4, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, -1) ∨
      y = fpoint P Q R d (1, 0, -β1) ∨ y = fpoint P Q R d (0, γ6, -β6)) :
    HasLexCellAt V R := by
  have hA := k5d_hA hΔ
  refine k5d_c1_core V P Q R d hΔ hα4 hγ4 hs hβ1 hb6 hγ6 hg6 hmem hVall ?_
  intro k0 U T B hfw hinj
  have hB : 0 < B := by
    have := hfw (0, 0, -1) (by simp [k5dL]) (0, 0, 0) (by simp [k5dL]) (by dsimp only; linarith)
    dsimp only at this; linarith
  have hUT : U < T := by
    have := hfw (1, 0, 0) (by simp [k5dL]) (0, 1, 0) (by simp [k5dL]) (by dsimp only; linarith)
    dsimp only at this; linarith
  exact k5d_c1_real_pa hα4 hγ4 hs hβ1 hκ hB hUT hinj

theorem k5d_c1_tt_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {α4 γ4 β1 β6 γ6 : ℝ}
    (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hs : 1 < α4 + γ4) (hβ1 : 0 < β1) (hb6 : 0 < β6) (hγ6 : 0 < γ6)
    (hg6 : γ6 < 1 ∨ γ6 = 1) (hz1 : ⟪P, R⟫ < α4 * ⟪P, R⟫ + γ4 * ⟪Q, R⟫) (hz2 : ⟪P, R⟫ < 0)
    (hmem : ∀ i, fpoint P Q R d (k5dX1 α4 γ4 β1 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨
      y = fpoint P Q R d (α4, γ4, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, -1) ∨
      y = fpoint P Q R d (1, 0, -β1) ∨ y = fpoint P Q R d (0, γ6, -β6)) :
    HasLexCellAt V R := by
  have hA := k5d_hA hΔ
  refine k5d_c1_core V P Q R d hΔ hα4 hγ4 hs hβ1 hb6 hγ6 hg6 hmem hVall ?_
  intro k0 U T B hfw hinj
  have hB : 0 < B := by
    have := hfw (0, 0, -1) (by simp [k5dL]) (0, 0, 0) (by simp [k5dL]) (by dsimp only; linarith)
    dsimp only at this; linarith
  have hU0 : U < 0 := by
    have := hfw (1, 0, 0) (by simp [k5dL]) (0, 0, 0) (by simp [k5dL]) (by dsimp only; linarith)
    dsimp only at this; linarith
  have hUb : U < α4 * U + γ4 * T := by
    have := hfw (1, 0, 0) (by simp [k5dL]) (α4, γ4, 0) (by simp [k5dL]) (by dsimp only; linarith)
    dsimp only at this; linarith
  exact k5d_c1_real_tt hα4 hγ4 hs hβ1 hB hU0 hUb hinj

end C2
end Type08Sp
end Minimality
