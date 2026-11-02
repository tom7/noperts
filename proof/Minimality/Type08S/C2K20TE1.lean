module

public import Minimality.Type08S.C2K18A

@[expose] public section


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

/-- Cell E at `d - b`, frame `(P,Q,R) = (a-d, c-d, d-b)`: ccw cycle `(b, c', a, b', a')`. -/
def k20tE (A G b1 b6 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ := ![(0, 0, -1), (1, 0, -b1), (1, 0, 0), (A, G, 0), (0, 1, -b6)]
theorem k20tE_0 : k20tE A G b1 b6 0 = (0, 0, -1) := rfl
theorem k20tE_1 : k20tE A G b1 b6 1 = (1, 0, -b1) := rfl
theorem k20tE_2 : k20tE A G b1 b6 2 = (1, 0, 0) := rfl
theorem k20tE_3 : k20tE A G b1 b6 3 = (A, G, 0) := rfl
theorem k20tE_4 : k20tE A G b1 b6 4 = (0, 1, -b6) := rfl

set_option maxHeartbeats 6400000 in
theorem k20tE_tsc {A G b1 b6 v1 v2 : ℝ} (hA : 0 < A) (hG : 0 < G) (hs : 1 < A + G) (hb1 : 0 < b1) (hb6 : 0 < b6)
    (hv1 : v1 < 0) (hv2 : v2 < 0) (hc1 : 0 < -G * v1 + (A - 1) * v2) (hc2 : 0 < (1 - G) * v1 + A * v2) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k20tE A G b1 b6 (i + 1) - k20tE A G b1 b6 i) (k20tE A G b1 b6 j - k20tE A G b1 b6 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (0, 1, 0)], ∀ i : ZMod 5,
      TSc 1 (k20tE A G b1 b6 (i + 1) - k20tE A G b1 b6 i) (t - k20tE A G b1 b6 i) (v1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  have x1 : 0 < -v1 := by linarith
  have x2 : 0 < -v2 := by linarith
  have hs' : 0 < A + G - 1 := by linarith
  have k1 := mul_pos hb1 x1
  have k2 := mul_pos hb1 x2
  have k3 := mul_pos hb6 x1
  have k4 := mul_pos hb6 x2
  have k5 := mul_pos hA x1
  have k6 := mul_pos hA x2
  have k7 := mul_pos hG x1
  have k8 := mul_pos hG x2
  have k9 := mul_pos hs' x1
  have k10 := mul_pos hs' x2
  have k11 := mul_pos hb1 hc1
  have k12 := mul_pos hb1 hc2
  have k13 := mul_pos hb6 hc1
  have k14 := mul_pos hb6 hc2
  have k15 := mul_pos hA hc1
  have k16 := mul_pos hG hc2
  have k17 := mul_pos hA hc2
  have k18 := mul_pos hG hc1
  have k19 := mul_pos hb1 hb6
  have k20 := mul_pos (mul_pos hb1 hb6) x1
  have k21 := mul_pos (mul_pos hb1 hb6) x2
  have k22 := mul_pos hs' hc1
  have k23 := mul_pos hs' hc2
  constructor
  · intro i j h1 h2
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k20tE_0, k20tE_1, k20tE_2, k20tE_3, k20tE_4, f0, f1, f2, f3, f4, Prod.fst_sub,
          Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
    · rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k20tE_0, k20tE_1, k20tE_2, k20tE_3, k20tE_4, f0, f1, f2, f3, f4, Prod.fst_sub,
          Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
