module

public import Minimality.Type08S.P2CR6

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# P3a core, part 7: transfer of robustness and `NoPersistHDN` along rotations/reflections of the rim.
-/

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

theorem robust_of_shift {k : ℕ} {z : ZMod k → ℝ} (c : ZMod k)
    (h : IsRobustUnimodal (fun i => z (c + i))) : IsRobustUnimodal z := by
  have := h.rot (-c)
  convert this using 2 with i
  congr 1; ring

theorem robust_of_reflect {k : ℕ} {z : ZMod k → ℝ} (c : ZMod k)
    (h : IsRobustUnimodal (fun i => z (c - i))) : IsRobustUnimodal z := by
  have h2 := h.reflect
  exact robust_of_shift c (by convert h2 using 2 with i; congr 1; ring)

theorem noPersist_of_shift {k : ℕ} {x : ZMod k → ℝ³} {u e : ℝ³} (c : ZMod k)
    (h : NoPersistHDN (fun i => x (c + i)) u e) : NoPersistHDN x u e := by
  intro i j Y hY Y' hY' hne hu he hall
  refine h (i - c) (j - c) Y ?_ Y' ?_ hne hu he ?_
  · convert hY using 3 <;> ring_nf
  · convert hY' using 3 <;> ring_nf
  · intro m
    exact hall (c + m)
  
theorem noPersist_of_reflect {k : ℕ} {x : ZMod k → ℝ³} {u e : ℝ³} (c : ZMod k)
    (h : NoPersistHDN (fun i => x (c - i)) u e) : NoPersistHDN x u e := by
  intro i j Y hY Y' hY' hne hu he hall
  refine h (c - i - 1) (c - j - 1) Y ?_ Y' ?_ hne hu he ?_
  · rw [segment_symm]
    convert hY using 3 <;> ring_nf
  · rw [segment_symm]
    convert hY' using 3 <;> ring_nf
  · intro m
    exact hall (c - m)

theorem noPersist_smul' {k : ℕ} {x : ZMod k → ℝ³} {u e : ℝ³} (h : NoPersistHDN x u e) {lam : ℝ}
    (hlam : lam ≠ 0) : NoPersistHDN x u (lam • e) := by
  intro i j Y hY Y' hY' hne hu he
  rw [real_inner_smul_right] at he
  exact h i j Y hY Y' hY' hne hu ((mul_eq_zero.mp he).resolve_left hlam)

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.noPersist_of_reflect
#print axioms Minimality.Type08Sp.robust_of_reflect
