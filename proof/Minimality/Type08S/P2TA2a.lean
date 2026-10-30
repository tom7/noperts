module

public import Minimality.Type08S.P2TA1c

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkP / A2a: `triCert_cornerF` (the corner certificate for `a'` over `f̄` at `T`).
-/

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- **Corner middle over `f̄`**: the point `o + pc(L, 0, zd)` over the far end `f` of the F-side, with `σ (zd - zf) > 0`;
certificate in the triangle `(x', f, g)`, for large `s`.  Two rows are ties (`tiltSign_tie`). -/
theorem triCert_cornerF (hF : Fr e1 e2 e3) (o : ℝ³) (V : Finset ℝ³)
    {σ L zp zf Xg Yg zg zd : ℝ} (hL : 0 < L) (hYg : 0 < Yg)
    (h1 : o + pc e1 e2 e3 0 0 zp ∈ V) (h2 : o + pc e1 e2 e3 L 0 zf ∈ V)
    (h3 : o + pc e1 e2 e3 Xg Yg zg ∈ V) (hab : 0 < σ * (zd - zf)) :
    ∀ᶠ s : ℝ in atTop, TriCert V (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * s) (-σ) 0)
      (o + pc e1 e2 e3 L 0 zd) := by
  filter_upwards [ev_aff Yg (Xg - L) hYg] with s hs
  refine ⟨_, h1, _, h2, _, h3, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [add_sub_add_left_eq_sub, pc_sub]
    first
    | exact tiltSign_pos hF (by nlinarith [mul_pos hL hYg])
    | exact tiltSign_tie hF (by ring) (by nlinarith [mul_pos hab hs, mul_pos hab hL])

end Type08Sp
end Minimality
