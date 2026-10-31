module

public import Minimality.Type08S.P2NP5
public import Minimality.Type08S.P2QWP2NP6

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# P3a, T4 `K_b` and `K_2`: `np_Kb`, `np_K2`.
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

theorem np_Kb {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hreg : RegT4 N.F)
    (hF : Fr e1 e2 e3) {κ κv : ℝ} (hκ : κ ≠ 0) (hκv : κv = κ ∨ κv = -κ) (hxe : b - d = κ • e3)
    (hf2 : ⟪c - d, e2⟫ = 0) (hL : 0 < ⟪c - d, e1⟫) (hr : 0 < ⟪b' - d, e2⟫)
    {k' : ℕ} [NeZero k'] (hk3 : 3 ≤ k') (σ : ZMod k' → ZMod 4) (u e : ℝ³)
    (hu : u = κv • e3) (he : e = ⟪c - d, e1⟫ • e1)
    (hcyc : ∀ i j : ZMod k', j ≠ i → j ≠ i + 1 → 0 < det3 (quad b c' b' c (σ (i + 1)) - quad b c' b' c (σ i))
      (quad b c' b' c (σ j) - quad b c' b' c (σ i)) u)
    (hleft : ∀ (i : ZMod k') (a_ : ZMod 4), 0 ≤ det3 (quad b c' b' c (σ (i + 1)) - quad b c' b' c (σ i))
      (quad b c' b' c a_ - quad b c' b' c (σ i)) u)
    (hz : IsRobustUnimodal (fun i => ⟪quad b c' b' c (σ i), u⟫))
    (hbad : NoPersistHDN (fun i => quad b c' b' c (σ i)) u e) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) :=
  W5.np_Kb N.toW hreg hF hκ hκv hxe hf2 hL hr hk3 σ u e hu he hcyc hleft hz hbad

theorem np_K2 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hreg : RegT4 N.F)
    (hF : Fr e1 e2 e3) {κ κv : ℝ} (hκ : κ ≠ 0) (hκv : κv = κ ∨ κv = -κ) (hxe : d - b = κ • e3)
    (hf2 : ⟪c' - b, e2⟫ = 0) (hL : 0 < ⟪c' - b, e1⟫) (hr : 0 < ⟪b' - b, e2⟫)
    {k' : ℕ} [NeZero k'] (hk3 : 3 ≤ k') (σ : ZMod k' → ZMod 4) (u e : ℝ³)
    (hu : u = κv • e3) (he : e = ⟪c' - b, e1⟫ • e1)
    (hcyc : ∀ i j : ZMod k', j ≠ i → j ≠ i + 1 → 0 < det3 (quad d c' b' c (σ (i + 1)) - quad d c' b' c (σ i))
      (quad d c' b' c (σ j) - quad d c' b' c (σ i)) u)
    (hleft : ∀ (i : ZMod k') (a_ : ZMod 4), 0 ≤ det3 (quad d c' b' c (σ (i + 1)) - quad d c' b' c (σ i))
      (quad d c' b' c a_ - quad d c' b' c (σ i)) u)
    (hz : IsRobustUnimodal (fun i => ⟪quad d c' b' c (σ i), u⟫))
    (hbad : NoPersistHDN (fun i => quad d c' b' c (σ i)) u e) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) :=
  W5.np_K2 N.toW hreg hF hκ hκv hxe hf2 hL hr hk3 σ u e hu he hcyc hleft hz hbad

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.np_Kb
#print axioms Minimality.Type08Sp.np_K2
