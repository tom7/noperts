module

public import Minimality.Type08S.P2NP4
public import Minimality.Type08S.P2QWP2NP5

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# P3a, N2 `K_c`: `np_N2` — the slide closes the robust rim `(c, b, c', b')` when its HDNs do not persist.
-/

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

theorem np_N2 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hreg : RegN2 N.F)
    (hF : Fr e1 e2 e3) {κ κv : ℝ} (hκ : κ ≠ 0) (hκv : κv = κ ∨ κv = -κ) (hce : c - a' = κ • e3)
    (hb2 : ⟪b - a', e2⟫ = 0) (hL : 0 < ⟪b - a', e1⟫) (hr : 0 < ⟪c' - a', e2⟫)
    {k' : ℕ} [NeZero k'] (hk3 : 3 ≤ k') (σ : ZMod k' → ZMod 4) (u e : ℝ³)
    (hu : u = κv • e3) (he : e = ⟪b - a', e1⟫ • e1)
    (hcyc : ∀ i j : ZMod k', j ≠ i → j ≠ i + 1 → 0 < det3 (quad c b c' b' (σ (i + 1)) - quad c b c' b' (σ i))
      (quad c b c' b' (σ j) - quad c b c' b' (σ i)) u)
    (hleft : ∀ (i : ZMod k') (a_ : ZMod 4), 0 ≤ det3 (quad c b c' b' (σ (i + 1)) - quad c b c' b' (σ i))
      (quad c b c' b' a_ - quad c b c' b' (σ i)) u)
    (hz : IsRobustUnimodal (fun i => ⟪quad c b c' b' (σ i), u⟫))
    (hbad : NoPersistHDN (fun i => quad c b c' b' (σ i)) u e) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) :=
  W5.np_N2 N.toW hreg hF hκ hκv hce hb2 hL hr hk3 σ u e hu he hcyc hleft hz hbad

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.np_N2
