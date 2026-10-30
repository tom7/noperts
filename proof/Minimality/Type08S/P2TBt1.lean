module

public import Minimality.Type08S.P2TDefs
public import Minimality.Type08S.P2TB2d
public import Minimality.Type08S.P2TY4
public import Minimality.Type08S.P2TB0c

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkP / B / Bt1: transfer of `NoPersistHDN (quad d c' b' c)` to the rim cycle `σ` of `K_2` at `T`.
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

theorem noPersist_to_shift {k : ℕ} {x : ZMod k → ℝ³} {u e : ℝ³} (c : ZMod k)
    (h : NoPersistHDN x u e) : NoPersistHDN (fun i => x (c + i)) u e := by
  intro i j Y hY Y' hY' hne hu he hall
  refine h (c + i) (c + j) Y ?_ Y' ?_ hne hu he ?_
  · convert hY using 3; ring_nf
  · convert hY' using 3; ring_nf
  · intro m
    have := hall (m - c)
    simpa only [add_sub_cancel] using this

theorem noPersist_to_reflect {k : ℕ} {x : ZMod k → ℝ³} {u e : ℝ³} (c : ZMod k)
    (h : NoPersistHDN x u e) : NoPersistHDN (fun i => x (c - i)) u e := by
  intro i j Y hY Y' hY' hne hu he hall
  refine h (c - i - 1) (c - j - 1) Y ?_ Y' ?_ hne hu he ?_
  · rw [segment_symm]; convert hY using 3 <;> ring_nf
  · rw [segment_symm]; convert hY' using 3 <;> ring_nf
  · intro m
    have := hall (c - m)
    simpa only [sub_sub_cancel] using this

theorem noPersist_u_smul {k : ℕ} {x : ZMod k → ℝ³} {u e : ℝ³} (h : NoPersistHDN x u e) {lam : ℝ}
    (hlam : lam ≠ 0) : NoPersistHDN x (lam • u) e := by
  intro i j Y hY Y' hY' hne hu he
  rw [real_inner_smul_right] at hu
  exact h i j Y hY Y' hY' hne ((mul_eq_zero.mp hu).resolve_left hlam) he

end Type08Sp
end Minimality
