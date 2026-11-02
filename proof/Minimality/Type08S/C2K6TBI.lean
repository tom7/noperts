module

public import Minimality.Type08S.C2K6TBH

@[expose] public section

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2

set_option maxHeartbeats 6400000 in
/-- Tilt test of the pentagon `(a,c',b',c,d) = k5dX4` for `γ4 > 1` (any `α4 > 0`, `γ6 ≤ 1`), cone
`0 < v2`, `α4 v2 < (γ4 - 1) v1`. -/
theorem k6t2_x4_tsc {α4 γ4 β1 β6 γ6 v1 v2 : ℝ}
    (hα4 : 0 < α4) (hγ4 : 1 < γ4) (hs : 1 < α4 + γ4) (hβ1 : 0 < β1)
    (hb6 : 0 < β6) (hγ6 : 0 < γ6) (hg61 : γ6 < 1 ∨ γ6 = 1)
    (hv2 : 0 < v2) (hc1 : α4 * v2 < (γ4 - 1) * v1) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k5dX4 α4 γ4 β1 β6 γ6 (i + 1) - k5dX4 α4 γ4 β1 β6 γ6 i) (k5dX4 α4 γ4 β1 β6 γ6 j - k5dX4 α4 γ4 β1 β6 γ6 i) (v1, v2, 0)) ∧
    (∀ t ∈ [(0, γ6, -β6), (0, 0, -1)], ∀ i : ZMod 5,
      TSc 1 (k5dX4 α4 γ4 β1 β6 γ6 (i + 1) - k5dX4 α4 γ4 β1 β6 γ6 i) (t - k5dX4 α4 γ4 β1 β6 γ6 i) (v1, v2, 0)) := by
  rcases hg61 with hg61 | rfl
  all_goals
    obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
    have hg : 0 < γ4 - 1 := by linarith
    have hv1 : 0 < v1 := by
      by_contra h; push Not at h
      nlinarith [mul_pos hα4 hv2, mul_nonneg hg.le (neg_nonneg.2 h)]
    have hc1' : 0 < (γ4 - 1) * v1 - α4 * v2 := by linarith
    have hc2' := mul_pos hv1 hv2
    have hs' : 0 < α4 + γ4 - 1 := by linarith
    have k1 := mul_pos hβ1 hv1
    have k2 := mul_pos hβ1 hv2
    have k3 := mul_pos hg hv1
    have k4 := mul_pos hα4 hv1
    have k5 := mul_pos hα4 hv2
    have k6 := mul_pos hb6 hv1
    have k7 := mul_pos hγ6 hv1
    have k8 := mul_pos hβ1 hc1'
    have k9 := mul_pos hs' hv1
    have k10 := mul_pos hα4 hb6
    have k11 := mul_pos hb6 hv2
    have k12 := mul_pos hβ1 hc2'
    have k13 := mul_pos hb6 hc2'
    have k17 := mul_pos hb6 hc1'
    have k18 := mul_pos hγ6 hv2
    have k19 := mul_pos hγ6 hb6
    constructor
    · intro i j h1 h2
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
        rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact absurd rfl h1
        | exact (h2 (by decide)).elim
        | (simp only [TSc, d3, k5dX4_0, k5dX4_1, k5dX4_2, k5dX4_3, k5dX4_4, f0, f1, f2, f3, f4, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
           first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
    · intro t ht i
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;>
        rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
        (simp only [TSc, d3, k5dX4_0, k5dX4_1, k5dX4_2, k5dX4_3, k5dX4_4, f0, f1, f2, f3, f4, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
