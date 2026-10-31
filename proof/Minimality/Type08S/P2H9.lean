module

public import Minimality.Type08S.P2H8
public import Minimality.Type08S.P2QWP2H9

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# pkH H9: T4's `K_b` and `K_2` with a persistent HDN (frame form)
-/

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- **T4 `K_b` with a persistent HDN.** -/
theorem pers_Kb {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hreg : RegT4 N.F)
    (hF : Fr e1 e2 e3) {κ κv : ℝ} (hκ : κ ≠ 0) (hκv : κv = κ ∨ κv = -κ) (hxe : b - d = κ • e3)
    (hf2 : ⟪c - d, e2⟫ = 0) (hL : 0 < ⟪c - d, e1⟫) (hr : 0 < ⟪b' - d, e2⟫)
    {k' : ℕ} [NeZero k'] (hk3 : 3 ≤ k') (σ : ZMod k' → ZMod 4) (u e : ℝ³)
    (hu : u = κv • e3) (he : e = ⟪c - d, e1⟫ • e1)
    (hcyc : ∀ i j : ZMod k', j ≠ i → j ≠ i + 1 → 0 < det3 (quad b c' b' c (σ (i + 1)) - quad b c' b' c (σ i))
      (quad b c' b' c (σ j) - quad b c' b' c (σ i)) u)
    (hleft : ∀ (i : ZMod k') (a_ : ZMod 4), 0 ≤ det3 (quad b c' b' c (σ (i + 1)) - quad b c' b' c (σ i))
      (quad b c' b' c a_ - quad b c' b' c (σ i)) u)
    (hz : IsRobustUnimodal (fun i => ⟪quad b c' b' c (σ i), u⟫))
    (hp : ¬ NoPersistHDN (fun i => quad b c' b' c (σ i)) u e)
    (hLE : LemE3 d b c b' c') (hSC2 : SC2Kb a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) :=
  W5.pers_Kb N.toW hreg hF hκ hκv hxe hf2 hL hr hk3 σ u e hu he hcyc hleft hz hp hLE hSC2

/-- **T4 `K_2` with a persistent HDN.** -/
theorem pers_K2 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hreg : RegT4 N.F)
    (hF : Fr e1 e2 e3) {κ κv : ℝ} (hκ : κ ≠ 0) (hκv : κv = κ ∨ κv = -κ) (hxe : d - b = κ • e3)
    (hf2 : ⟪c' - b, e2⟫ = 0) (hL : 0 < ⟪c' - b, e1⟫) (hr : 0 < ⟪b' - b, e2⟫)
    {k' : ℕ} [NeZero k'] (hk3 : 3 ≤ k') (σ : ZMod k' → ZMod 4) (u e : ℝ³)
    (hu : u = κv • e3) (he : e = ⟪c' - b, e1⟫ • e1)
    (hcyc : ∀ i j : ZMod k', j ≠ i → j ≠ i + 1 → 0 < det3 (quad d c' b' c (σ (i + 1)) - quad d c' b' c (σ i))
      (quad d c' b' c (σ j) - quad d c' b' c (σ i)) u)
    (hleft : ∀ (i : ZMod k') (a_ : ZMod 4), 0 ≤ det3 (quad d c' b' c (σ (i + 1)) - quad d c' b' c (σ i))
      (quad d c' b' c a_ - quad d c' b' c (σ i)) u)
    (hz : IsRobustUnimodal (fun i => ⟪quad d c' b' c (σ i), u⟫))
    (hp : ¬ NoPersistHDN (fun i => quad d c' b' c (σ i)) u e)
    (hLE : LemE3 b d c' b' c) (hSC2 : SC2K2 a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) :=
  W5.pers_K2 N.toW hreg hF hκ hκv hxe hf2 hL hr hk3 σ u e hu he hcyc hleft hz hp hLE hSC2

end Type08Sp
end Minimality
