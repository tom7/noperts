module

public import Minimality.Type08S.C2K22C1bB

@[expose] public section


/-!
# K22C1b / C: screen tests of the cycle `C⁺ = (b', a, c', b, a', c)` at the edge-on view `w = λ q + r`

Frame as in B.  Tilt `v = p + v2 q`.  Hidden: `d`.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- The ccw cycle `(b', a, c', b, a', c)`. -/
def k22c1bP (l β1 γ4 γ6 : ℝ) : ZMod 6 → ℝ × ℝ × ℝ :=
  ![(1, -(γ4 * l), γ4), (1, 0, 0), (1, β1, 0), (0, 1, 0), (0, 1 - γ6 * l, γ6), (0, -l, 1)]

theorem k22c1bP_0 : k22c1bP l β1 γ4 γ6 0 = (1, -(γ4 * l), γ4) := rfl
theorem k22c1bP_1 : k22c1bP l β1 γ4 γ6 1 = (1, 0, 0) := rfl
theorem k22c1bP_2 : k22c1bP l β1 γ4 γ6 2 = (1, β1, 0) := rfl
theorem k22c1bP_3 : k22c1bP l β1 γ4 γ6 3 = (0, 1, 0) := rfl
theorem k22c1bP_4 : k22c1bP l β1 γ4 γ6 4 = (0, 1 - γ6 * l, γ6) := rfl
theorem k22c1bP_5 : k22c1bP l β1 γ4 γ6 5 = (0, -l, 1) := rfl

set_option maxHeartbeats 6400000 in
theorem k22c1b_tscP {l β1 γ4 γ6 v2 : ℝ} (hl : 0 < l) (hβ1 : 0 < β1) (hγ4 : 0 < γ4) (hγ6 : 0 < γ6)
    (hγ61 : γ6 < 1) :
    (∀ i j : ZMod 6, j ≠ i → j ≠ i + 1 →
      TSc 1 (k22c1bP l β1 γ4 γ6 (i + 1) - k22c1bP l β1 γ4 γ6 i) (k22c1bP l β1 γ4 γ6 j - k22c1bP l β1 γ4 γ6 i)
        (1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ))], ∀ i : ZMod 6,
      TSc 1 (k22c1bP l β1 γ4 γ6 (i + 1) - k22c1bP l β1 γ4 γ6 i) (t - k22c1bP l β1 γ4 γ6 i) (1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3, f4, f5⟩ := z6_add_one
  have k1 := mul_pos hγ4 hl
  have k2 := mul_pos hβ1 hγ4
  have k3 := mul_pos hγ6 hl
  have k4 : 0 < 1 - γ6 := by linarith
  have k5 := mul_pos k4 hl
  have k6 := mul_pos hγ6 hγ4
  have k7 := mul_pos hγ6 hβ1
  constructor
  · intro i j h1 h2
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k22c1bP_0, k22c1bP_1, k22c1bP_2, k22c1bP_3, k22c1bP_4, k22c1bP_5,
          f0, f1, f2, f3, f4, f5, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    subst ht
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k22c1bP_0, k22c1bP_1, k22c1bP_2, k22c1bP_3, k22c1bP_4, k22c1bP_5,
          f0, f1, f2, f3, f4, f5, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
