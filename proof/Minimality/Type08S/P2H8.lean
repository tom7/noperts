module

public import Minimality.Type08S.P2H7
public import Minimality.Type08S.P2FIN1
public import Minimality.Type08S.P2QWP2H8

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# pkH H8: the external hypotheses (Lemma E (iii) weak; the SC2 cases) and N2's `K_c`

* `LemE3 x' x f r g`: Lemma E (iii), weak: `x`, `x'` weakly on opposite sides of `Π' = aff(f, r, g)`
  (`det3 (r-f) (g-f) (x-f) · det3 (r-f) (g-f) (x'-f) ≤ 0`).  `lemEF_of_3`: its frame form `LemEF`.
* `SC2N2`, `SC2Kb`, `SC2K2`: what the SC2 package must prove (chord end at `f`, parallel set), in the canonical
  frame of each closing (as `frame_N2`, `frame_Kb`, `frame_K2` give it), with robustness.
* `pers_N2`: N2's `K_c` with a persistent HDN.
-/

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- **N2 `K_c` with a persistent HDN** (frame form of `close_hdn_pers`, N2 case). -/
theorem pers_N2 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hreg : RegN2 N.F)
    (hF : Fr e1 e2 e3) {κ κv : ℝ} (hκ : κ ≠ 0) (hκv : κv = κ ∨ κv = -κ) (hce : c - a' = κ • e3)
    (hb2 : ⟪b - a', e2⟫ = 0) (hL : 0 < ⟪b - a', e1⟫) (hr : 0 < ⟪c' - a', e2⟫)
    {k' : ℕ} [NeZero k'] (hk3 : 3 ≤ k') (σ : ZMod k' → ZMod 4) (u e : ℝ³)
    (hu : u = κv • e3) (he : e = ⟪b - a', e1⟫ • e1)
    (hcyc : ∀ i j : ZMod k', j ≠ i → j ≠ i + 1 → 0 < det3 (quad c b c' b' (σ (i + 1)) - quad c b c' b' (σ i))
      (quad c b c' b' (σ j) - quad c b c' b' (σ i)) u)
    (hleft : ∀ (i : ZMod k') (a_ : ZMod 4), 0 ≤ det3 (quad c b c' b' (σ (i + 1)) - quad c b c' b' (σ i))
      (quad c b c' b' a_ - quad c b c' b' (σ i)) u)
    (hz : IsRobustUnimodal (fun i => ⟪quad c b c' b' (σ i), u⟫))
    (hp : ¬ NoPersistHDN (fun i => quad c b c' b' (σ i)) u e)
    (hLE : LemE3 a' c b c' b') (hSC2 : SC2N2 a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) :=
  W5.pers_N2 N.toW hreg hF hκ hκv hce hb2 hL hr hk3 σ u e hu he hcyc hleft hz hp hLE hSC2

end Type08Sp
end Minimality
