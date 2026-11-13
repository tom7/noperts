module

public import Minimality.Type08S.P2I5b
public import Minimality.Type08S.P2I7b
public import Minimality.Type08S.P2TpX
public import Minimality.Type08S.P2J1
public import Minimality.Type08S.P2J2
public import Minimality.Type08S.P2J3
public import Minimality.Type08S.P2J4

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# I9: assembly of the case at `T'` (`close_T'_sig4E`) from the finished lemmas; the residual keeps the hypotheses of `Tp_poked`, `Tp_far`.

Finished (other files): `close_Tp_X` (¬QacTop, pkC), `close_T'2'` (tree; X_2a HDN-free, not level),
`close_Tp_R3_hdn` (I5b), `close_Tp_R4h_hdn` (I7b).
Also used: `Tp_other_noHDN`, `Tp_dichotomy`, `level_not_noHDN`, `Tp_level_hid` (J1-J4).
Unproved pieces `Tp_poked`, `Tp_far` appear only as their hypotheses (`TpPokedH`, `TpFarH`).
-/

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- `det3 (b' - a) (c - d) (b - d) = (α4 - 1) det3 (a - d) (c - d) (b - d)`. -/
theorem det_alpha {a b b' c d : ℝ³} {α4 γ4 : ℝ} (hb'rep : b' = d + α4 • (a - d) + γ4 • (c - d)) :
    det3 (b' - a) (c - d) (b - d) = (α4 - 1) * det3 (a - d) (c - d) (b - d) := by
  have : b' - a = (α4 - 1) • (a - d) + γ4 • (c - d) := by rw [hb'rep]; module
  rw [this]
  simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

end Type08Sp
end Minimality

