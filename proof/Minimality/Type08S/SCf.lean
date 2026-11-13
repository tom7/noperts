module

public import Minimality.Type08S.SCe

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- Class (c) package: the top vertex (the higher of `r`, `g` on the screen) projects to the open
chord `x̄ f̄` of the `F`-plane, `f` lies on the other side of its depth from `x`, and the
remaining corner of the closing is on the side it must be (robustness, Lemma 2.1(c)). -/
def ClassC5 (L zx zf Xr Yr zr Xg Yg zg : ℝ) : Prop :=
  (Yr < Yg ∧ 0 < Xg ∧ Xg < L ∧ (zg - zx) * L = (zf - zx) * Xg ∧ (zx - zg) * (zf - zg) < 0 ∧
      (zx - zg) * (zr - zg) < 0) ∨
  (Yg < Yr ∧ 0 < Xr ∧ Xr < L ∧ (zr - zx) * L = (zf - zx) * Xr ∧ (zx - zr) * (zf - zr) < 0 ∧
      0 < (zx - zr) * (zg - zr))

/-- **Corollary SC-c for the five-corner closing `(x', f, r, g, x)`**, any additional vertices `E`. -/
theorem lemmaSCc (hF : Fr e1 e2 e3) (o : ℝ³) (E : Finset ℝ³)
    {σ L zp zx zf Xr Yr zr Xg Yg zg : ℝ}
    (hL : 0 < L) (hzx : 0 < σ * (zx - zp))
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hcg : 0 < Yg * Xr - Xg * Yr) (hc : ClassC5 L zx zf Xr Yr zr Xg Yg zg)
    (hE : ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E)
      (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * s) (-σ) 0) y) :
    IsRupert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E) := by
  rcases hc with ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩
  · exact lemmaSCc_g hF o E hL hzx hcr hYr h1 hcg h2 h3 h4 h5 h6 hE
  · exact lemmaSCc_r hF o E hL hzx hcr hYr hYg h1 hcg h2 h3 h4 h5 h6 hE

section
variable {σ L zp zx zf Xr Yr zr Xg Yg zg : ℝ}

end

end Type08Sp
end Minimality

