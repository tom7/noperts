module

public import Minimality.Type08S.P2SC2S2

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# Corollary SC2-S, interior case (package G)
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- **Corollary SC2-S** (`f̄ ∈ (ḡ, r̄)` on the top side, `x' ∉ Π'`), frame form.  The rim is
`rim5` with `f = (L,0,σ0+mL)`, `r = (Xr,Y,σ0+mXr)`, `g = (Xg,Y,σ0+mXg)`. -/
theorem lemmaSC2S (hF : Fr e1 e2 e3) (o : ℝ³) (E : Finset ℝ³)
    {σ L zp zx Xr Xg Y m σ0 : ℝ}
    (hL : 0 < L) (hzx : 0 < σ * (zx - zp)) (hY : 0 < Y)
    (hc : ClassS2 σ L zp zx Xr Xg m σ0)
    (hE : ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert
      (rim5 e1 e2 e3 o L zp zx (σ0 + m * L) Xr Y (σ0 + m * Xr) Xg Y (σ0 + m * Xg) E)
      (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * s) (-σ) 0) y) :
    IsRupert (rim5 e1 e2 e3 o L zp zx (σ0 + m * L) Xr Y (σ0 + m * Xr) Xg Y (σ0 + m * Xg) E) := by
  obtain ⟨z0, κ, ρ, hρ, hf, hr, hg, hx, hR2, hR3⟩ := sc2S_params hL hzx hc
  obtain ⟨hXg, hXr, hPi, -⟩ := hc
  exact sc2S_core hF o E hL hzx hY hXg hXr hPi hρ hf hr hg hx hR2 hR3 hE

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.lemmaSC2S
