module

public import Minimality.Type08S.P2QWP2PF0

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# P-F infrastructure (plan2/pkB): frame cross products, determinants of normal-form differences,
sign transfer, and the region parameters `θ 5 > 1` / `θ 5 < 1 < θ 0`.
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- The region parameters: N2 has `γ₆ > 1`. -/
theorem theta_N2 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) {o E₁ E₂ E₃ : ℝ³}
    {θ : Fin 6 → ℝ} (hE : det3 E₁ E₂ E₃ ≠ 0) (hθ : ∀ k, 0 < ineq08 θ k)
    (hpts : pts08 a a' b b' c c' d = nfShape08 o E₁ E₂ E₃ θ) (h : RegN2 N.F) : 1 < θ 5 :=
  W5.theta_N2 N.toW hE (Ineq08w.of_pos hθ) hpts h

theorem theta_T4 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) {o E₁ E₂ E₃ : ℝ³}
    {θ : Fin 6 → ℝ} (hE : det3 E₁ E₂ E₃ ≠ 0) (hθ : ∀ k, 0 < ineq08 θ k)
    (hpts : pts08 a a' b b' c c' d = nfShape08 o E₁ E₂ E₃ θ) (h : RegT4 N.F) :
    θ 5 < 1 ∧ 1 < θ 0 :=
  W5.theta_T4 N.toW hE (Ineq08w.of_pos hθ) hpts h

end Type08Sp
end Minimality
