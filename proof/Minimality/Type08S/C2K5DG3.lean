module

public import Minimality.Type08S.C2K5DB

@[expose] public section


/-!
# K5d / G3: cell 3, hexagon `(a, b', c, a', b, d)` (QPa, `α4 < 1`): TSc table
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

def k5dX3 (α4 γ4 β1 β6 γ6 : ℝ) : ZMod 6 → ℝ × ℝ × ℝ :=
  ![(1, 0, 0), (α4, γ4, 0), (0, 1, 0), (0, γ6, -β6), (0, 0, -1), (0, 0, 0)]

theorem k5dX3_0 : k5dX3 α4 γ4 β1 β6 γ6 0 = (1, 0, 0) := rfl
theorem k5dX3_1 : k5dX3 α4 γ4 β1 β6 γ6 1 = (α4, γ4, 0) := rfl
theorem k5dX3_2 : k5dX3 α4 γ4 β1 β6 γ6 2 = (0, 1, 0) := rfl
theorem k5dX3_3 : k5dX3 α4 γ4 β1 β6 γ6 3 = (0, γ6, -β6) := rfl
theorem k5dX3_4 : k5dX3 α4 γ4 β1 β6 γ6 4 = (0, 0, -1) := rfl
theorem k5dX3_5 : k5dX3 α4 γ4 β1 β6 γ6 5 = (0, 0, 0) := rfl

set_option maxHeartbeats 6400000 in
theorem k5dX3_tsc {α4 γ4 β1 β6 γ6 v1 v2 : ℝ}
    (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hs : 1 < α4 + γ4) (hβ1 : 0 < β1)
    (hb6 : 0 < β6) (hγ6 : 0 < γ6) (hg61 : γ6 < 1) (hbg : 1 < β6 + γ6)
    (hv1 : v1 < 0) (hv2 : 0 < v2) (hc1 : γ4 * v1 + (1 - α4) * v2 < 0) :
    (∀ i j : ZMod 6, j ≠ i → j ≠ i + 1 →
      TSc 1 (k5dX3 α4 γ4 β1 β6 γ6 (i + 1) - k5dX3 α4 γ4 β1 β6 γ6 i) (k5dX3 α4 γ4 β1 β6 γ6 j - k5dX3 α4 γ4 β1 β6 γ6 i) (v1, v2, 0)) ∧
    (∀ t ∈ [(1, 0, -β1)], ∀ i : ZMod 6,
      TSc 1 (k5dX3 α4 γ4 β1 β6 γ6 (i + 1) - k5dX3 α4 γ4 β1 β6 γ6 i) (t - k5dX3 α4 γ4 β1 β6 γ6 i) (v1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3, f4, f5⟩ := z6_add_one
  have hv1' : 0 < -v1 := by linarith
  have hv2' := hv2
  have hc1' : 0 < -(γ4 * v1 + (1 - α4) * v2) := by linarith
  have hc2' := mul_pos hv1' hv2
  have hs' : 0 < α4 + γ4 - 1 := by linarith
  have k1 := mul_pos hβ1 hv1'
  have k2 := mul_pos hβ1 hv2'
  have k3 := mul_pos hγ4 hv1'
  have k4 := mul_pos hα4 hv1'
  have k5 := mul_pos hα4 hv2'
  have k6 := mul_pos hb6 hv1'
  have k7 := mul_pos hγ6 hv1'
  have k8 := mul_pos hβ1 hc1'
  have k9 := mul_pos hs' hv1'
  have k10 := mul_pos hα4 hb6
  have k11 := mul_pos hb6 hv2'
  have k12 := mul_pos hβ1 hc2'
  have k13 := mul_pos hb6 hc2'
  have k14 := mul_pos (sub_pos.2 hg61) hα4
  have k15 := mul_pos (sub_pos.2 hg61) hv1'
  have k16 := mul_pos (mul_pos (sub_pos.2 hg61) hα4) hb6
  have k17 := mul_pos hb6 hc1'
  have k18 := mul_pos hγ6 hv2'
  have k19 := mul_pos hγ6 hb6
  have k20 := mul_pos (sub_pos.2 hbg) hv1'
  have k21 := mul_pos (sub_pos.2 hbg) hv2'
  have k22 := mul_pos (sub_pos.2 hbg) hα4
  constructor
  · intro i j h1 h2
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k5dX3_0, k5dX3_1, k5dX3_2, k5dX3_3, k5dX3_4, k5dX3_5, f0, f1, f2, f3, f4, f5, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl <;>
      rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k5dX3_0, k5dX3_1, k5dX3_2, k5dX3_3, k5dX3_4, k5dX3_5, f0, f1, f2, f3, f4, f5, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
