module

public import Minimality.Type08S.C2K5DB

@[expose] public section


/-!
# K5d / G6: cell 6, hexagon `(a, c', b', a', c, d)` (QTT, `γ6 = 1`): TSc table
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

def k5dX6 (α4 γ4 β1 β6 γ6 : ℝ) : ZMod 6 → ℝ × ℝ × ℝ :=
  ![(1, 0, 0), (1, 0, -β1), (α4, γ4, 0), (0, γ6, -β6), (0, 1, 0), (0, 0, 0)]

theorem k5dX6_0 : k5dX6 α4 γ4 β1 β6 γ6 0 = (1, 0, 0) := rfl
theorem k5dX6_1 : k5dX6 α4 γ4 β1 β6 γ6 1 = (1, 0, -β1) := rfl
theorem k5dX6_2 : k5dX6 α4 γ4 β1 β6 γ6 2 = (α4, γ4, 0) := rfl
theorem k5dX6_3 : k5dX6 α4 γ4 β1 β6 γ6 3 = (0, γ6, -β6) := rfl
theorem k5dX6_4 : k5dX6 α4 γ4 β1 β6 γ6 4 = (0, 1, 0) := rfl
theorem k5dX6_5 : k5dX6 α4 γ4 β1 β6 γ6 5 = (0, 0, 0) := rfl

set_option maxHeartbeats 6400000 in
theorem k5dX6_tsc {α4 γ4 β1 β6 γ6 v1 v2 : ℝ}
    (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hs : 1 < α4 + γ4) (hβ1 : 0 < β1)
    (hb6 : 0 < β6) (hg6 : γ6 = 1)
    (hv1 : 0 < v1) (hv2 : 0 < v2) (hc1 : 0 < γ4 * v1 + (1 - α4) * v2) (hc2 : 0 < α4 * v2 + (1 - γ4) * v1) :
    (∀ i j : ZMod 6, j ≠ i → j ≠ i + 1 →
      TSc 1 (k5dX6 α4 γ4 β1 β6 γ6 (i + 1) - k5dX6 α4 γ4 β1 β6 γ6 i) (k5dX6 α4 γ4 β1 β6 γ6 j - k5dX6 α4 γ4 β1 β6 γ6 i) (v1, v2, 0)) ∧
    (∀ t ∈ [(0, 0, -1)], ∀ i : ZMod 6,
      TSc 1 (k5dX6 α4 γ4 β1 β6 γ6 (i + 1) - k5dX6 α4 γ4 β1 β6 γ6 i) (t - k5dX6 α4 γ4 β1 β6 γ6 i) (v1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3, f4, f5⟩ := z6_add_one
  subst hg6
  have hg61 : (0:ℝ) < 1 := one_pos
  have hγ6 : (0:ℝ) < 1 := one_pos
  have hv1' := hv1
  have hv2' := hv2
  have hc1' := hc1
  have hc2' := hc2
  have hs' : 0 < α4 + γ4 - 1 := by linarith
  have k1 := mul_pos hβ1 hv1'
  have k2 := mul_pos hβ1 hv2'
  have k3 := mul_pos hγ4 hv1'
  have k4 := mul_pos hα4 hv1'
  have k5 := mul_pos hα4 hv2'
  have k6 := mul_pos hb6 hv1'
  have k8 := mul_pos hβ1 hc1'
  have k9 := mul_pos hs' hv1'
  have k10 := mul_pos hα4 hb6
  have k11 := mul_pos hb6 hv2'
  have k12 := mul_pos hβ1 hc2'
  have k13 := mul_pos hb6 hc2'
  have k17 := mul_pos hb6 hc1'
  constructor
  · intro i j h1 h2
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k5dX6_0, k5dX6_1, k5dX6_2, k5dX6_3, k5dX6_4, k5dX6_5, f0, f1, f2, f3, f4, f5, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl <;>
      rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k5dX6_0, k5dX6_1, k5dX6_2, k5dX6_3, k5dX6_4, k5dX6_5, f0, f1, f2, f3, f4, f5, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
