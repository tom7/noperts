module

public import Minimality.Type08S.P2SCX1
public import Minimality.Type08S.P2SCX2
public import Minimality.Type08S.P2SCX3
public import Minimality.Type08S.P2SCX4
public import Minimality.Type08S.P2SCX5

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# Lemma SC-X (package 8): chord-end HDN at the apex `x`, frame form (sp08f §3)

`ClassX5` is the frame-coordinate form of "the persistent HDN's foot is `x̄`" (the HDN classification, package P-G,
is taken as this hypothesis).  Five sub-cases: `x̄` in the open top side; `x̄ = t̄` for a top vertex `g`, a top
vertex `r`, the near end `g` or the far end `r` of a top side.
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- **Class SC-X** (chord end at the apex), frame form.  The last component of each clause is robustness
(`f` on one side / opposite sides of `z_x`), and `x ∉ Π'` where needed (`hPi`-clauses). -/
def ClassX5 (σ L zx zf Xr Yr zr Xg Yg zg : ℝ) : Prop :=
  -- `x̄` in the open top side
  (Yg = Yr ∧ Xg < 0 ∧ 0 < Xr ∧ (zg - zx) * Xr = (zr - zx) * Xg ∧ 0 < (zf - zx) * (zr - zx) ∧
      0 < σ * ((zr - zx) * L - (zf - zx) * Xr)) ∨
  -- top vertex `g` over `x̄`
  (Yr < Yg ∧ Xg = 0 ∧ zg = zx ∧ 0 < (zf - zx) * (zr - zx)) ∨
  -- top vertex `r` over `x̄`
  (Yg < Yr ∧ Xr = 0 ∧ zr = zx ∧ (zf - zx) * (zg - zx) < 0) ∨
  -- near end `g` of the top side over `x̄`
  (Yg = Yr ∧ Xg = 0 ∧ zg = zx ∧ 0 < (zf - zx) * (zr - zx) ∧
      0 < σ * ((zr - zx) * L - (zf - zx) * Xr)) ∨
  -- far end `r` of the top side over `x̄`
  (Yg = Yr ∧ Xr = 0 ∧ zr = zx ∧ (zf - zx) * (zg - zx) < 0)

/-- **Lemma SC-X.** -/
theorem lemmaSCX (hF : Fr e1 e2 e3) (o : ℝ³) (E : Finset ℝ³)
    {σ L zp zx zf Xr Yr zr Xg Yg zg : ℝ}
    (hL : 0 < L) (hzx : 0 < σ * (zx - zp))
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hcg : 0 < Yg * Xr - Xg * Yr) (hc : ClassX5 σ L zx zf Xr Yr zr Xg Yg zg)
    (hE : ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E)
      (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * s) (-σ) 0) y) :
    IsRupert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E) := by
  rcases hc with ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ |
    ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4⟩
  · exact lemmaSCX_open hF o E hL hzx hYr h1 h2 h3 h4 h5 h6 hE
  · exact lemmaSCX_gvert hF o E hL hzx hcr hYr h1 hcg h2 h3 h4 hE
  · exact lemmaSCX_rvert hF o E hL hzx hcr hYr hYg h1 hcg h2 h3 h4 hE
  · exact lemmaSCX_gend hF o E hL hzx hcr hYr hYg h1 hcg h2 h3 h4 h5 hE
  · exact lemmaSCX_rend hF o E hL hzx hcr hYr hYg h1 hcg h2 h3 h4 hE

section
variable {σ L zp zx zf Xr Yr zr Xg Yg zg : ℝ}

end

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.lemmaSCX
