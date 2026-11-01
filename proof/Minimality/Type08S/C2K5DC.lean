module

public import Minimality.Type08S.C2K5DB

@[expose] public section


/-!
# K5d / C: cell 1, the pentagon `(c', b', c, d, b)` at `u0 = d - b` (TSc tables)

Frame `(P,Q,R) = (a - d, c - d, d - b)`; points over `d`: `d = 0, a = (1,0,0), c = (0,1,0), b' = (α4,γ4,0), b = (0,0,-1),
c' = (1,0,-β1), a' = (0,γ6,-β6)` (T': `α1 = 1`).  Cycle (ccw on screen) `(c', b', c, d, b)`, rest `a, a'`.
Cone: `v1 > 0, v2 < 0, γ4 v1 + (1-α4) v2 > 0`, and (needed at `γ6 = 1`) `(1-γ4) v1 + α4 v2 < 0`.
-/
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

def k5dX1 (α4 γ4 β1 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  ![(1, 0, -β1), (α4, γ4, 0), (0, 1, 0), (0, 0, 0), (0, 0, -1)]

theorem k5dX1_0 : k5dX1 α4 γ4 β1 0 = (1, 0, -β1) := rfl
theorem k5dX1_1 : k5dX1 α4 γ4 β1 1 = (α4, γ4, 0) := rfl
theorem k5dX1_2 : k5dX1 α4 γ4 β1 2 = (0, 1, 0) := rfl
theorem k5dX1_3 : k5dX1 α4 γ4 β1 3 = (0, 0, 0) := rfl
theorem k5dX1_4 : k5dX1 α4 γ4 β1 4 = (0, 0, -1) := rfl

set_option maxHeartbeats 3200000 in
theorem k5d_c1_tsc {α4 γ4 β1 β6 γ6 v1 v2 : ℝ} (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hs : 1 < α4 + γ4)
    (hβ1 : 0 < β1) (hb6 : 0 < β6) (hγ6 : 0 < γ6) (hg6 : γ6 < 1 ∨ γ6 = 1)
    (hv1 : 0 < v1) (hv2 : v2 < 0) (hc1 : 0 < γ4 * v1 + (1 - α4) * v2)
    (hc2 : (1 - γ4) * v1 + α4 * v2 < 0) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k5dX1 α4 γ4 β1 (i + 1) - k5dX1 α4 γ4 β1 i) (k5dX1 α4 γ4 β1 j - k5dX1 α4 γ4 β1 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0, γ6, -β6)], ∀ i : ZMod 5,
      TSc 1 (k5dX1 α4 γ4 β1 (i + 1) - k5dX1 α4 γ4 β1 i) (t - k5dX1 α4 γ4 β1 i) (v1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  have nv2 : 0 < -v2 := by linarith
  have hs' : 0 < α4 + γ4 - 1 := by linarith
  have k1 := mul_pos hβ1 hv1
  have k2 := mul_pos hβ1 nv2
  have k3 := mul_pos hγ4 hv1
  have k4 := mul_pos hα4 hv1
  have k5 := mul_pos hα4 nv2
  have k6 := mul_pos hb6 hv1
  have k7 := mul_pos hγ6 hv1
  have k8 := mul_pos hβ1 hc1
  have k9 := mul_pos hs' hv1
  have k10 := mul_pos hα4 hb6
  have k11 := mul_pos hb6 nv2
  have k12 := mul_pos hβ1 (neg_pos.2 hc2)
  have k13 := mul_pos hb6 (neg_pos.2 hc2)
  constructor
  · intro i j h1 h2
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k5dX1_0, k5dX1_1, k5dX1_2, k5dX1_3, k5dX1_4, f0, f1, f2, f3, f4, Prod.fst_sub,
          Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k5dX1_0, k5dX1_1, k5dX1_2, k5dX1_3, k5dX1_4, f0, f1, f2, f3, f4, Prod.fst_sub,
          Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
    · rcases hg6 with hg | rfl
      · have k14 := mul_pos (sub_pos.2 hg) hα4
        have k15 := mul_pos (sub_pos.2 hg) hv1
        have k16 := mul_pos (mul_pos (sub_pos.2 hg) hα4) hb6
        rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
        (simp only [TSc, d3, k5dX1_0, k5dX1_1, k5dX1_2, k5dX1_3, k5dX1_4, f0, f1, f2, f3, f4, Prod.fst_sub,
          Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
      · rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
        (simp only [TSc, d3, k5dX1_0, k5dX1_1, k5dX1_2, k5dX1_3, k5dX1_4, f0, f1, f2, f3, f4, Prod.fst_sub,
          Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
