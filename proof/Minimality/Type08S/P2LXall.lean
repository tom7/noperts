module

public import Minimality.Type08S.P2LXfin

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# SC2-V for both signs (package K): `lemmaSC2V_all`
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- **Corollary SC2-V, all cases**: a top vertex over `f̄` (or `f̄` the near end of a top side), `K_x` robust
(`ClassV2tail`), any position of `x'` on the `x`-side (`hzx`): `h_{x'} ≤ h_f` by `lemmaSC2V`, `h_{x'} > h_f` by
`lemmaSC2V_hi` (Lemma LX (ii)).  `σ = ±1` is needed only for the second case. -/
theorem lemmaSC2V_all (hF : Fr e1 e2 e3) (o : ℝ³) (E : Finset ℝ³)
    {σ L zp zx zf Xr Yr zr Xg Yg zg : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hL : 0 < L) (hzx : 0 < σ * (zx - zp))
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hcg : 0 < Yg * Xr - Xg * Yr) (hc : ClassV2tail L zx zf Xr Yr zr Xg Yg zg)
    (hE : ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E)
      (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * s) (-σ) 0) y) :
    IsRupert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E) := by
  by_cases h : 0 ≤ σ * (zf - zp)
  · exact lemmaSC2V hF o E hL hzx hcr hYr hYg hcg ⟨h, hc⟩ hE
  · exact lemmaSC2V_hi hF o E hσ hL hzx (not_le.1 h) hcr hYr hYg hcg hc hE

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.lemmaSC2V_all
