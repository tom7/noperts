module

public import Minimality.Type08S.P2TpBase

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# T'X: two small eventual-in-the-tilt lemmas
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

theorem ev_lt_cont {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (h : f 0 < g 0) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), f s < g s :=
  (hf.continuousAt.eventually_lt hg.continuousAt h).filter_mono nhdsWithin_le_nhds

theorem ev_ne_affine {A B : ℝ} (h : A ≠ 0 ∨ B ≠ 0) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), A + s * B ≠ 0 := by
  by_cases hA : A = 0
  · have hB : B ≠ 0 := h.resolve_left (not_not.2 hA)
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [hA, zero_add]
    exact mul_ne_zero (ne_of_gt hs) hB
  · have hc : Continuous fun s : ℝ => A + s * B := by fun_prop
    exact (hc.continuousAt.eventually_ne (by simpa using hA)).filter_mono nhdsWithin_le_nhds

end Type08Sp
end Minimality
