module

public import Minimality.Type08S.C2K6MF

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2

/-- The triangle `(a, c', b')` in the frame `(b-d, c-d, a-d)`. -/
def k6mTCyc (α1 β1 : ℝ) : ZMod 3 → ℝ × ℝ × ℝ := ![(0, 0, 1), (β1, 0, α1), (0, β1, α1)]

theorem k6mTCyc_0 : k6mTCyc α1 β1 0 = (0, 0, 1) := rfl
theorem k6mTCyc_1 : k6mTCyc α1 β1 1 = (β1, 0, α1) := rfl
theorem k6mTCyc_2 : k6mTCyc α1 β1 2 = (0, β1, α1) := rfl

theorem z3_cases (i : ZMod 3) : i = 0 ∨ i = 1 ∨ i = 2 := by revert i; decide
theorem z3_add : (0 : ZMod 3) + 1 = 1 ∧ (1 : ZMod 3) + 1 = 2 ∧ (2 : ZMod 3) + 1 = 0 := by decide

set_option maxHeartbeats 3200000 in
theorem k6m_T_tsc {α1 β1 β6 γ6 v1 v2 : ℝ} (hα1 : 0 < α1) (hβ1 : 1 < β1)
    (hb6 : 0 < β6) (hγ6 : 0 < γ6) (hσ : β6 + γ6 < β1) (hv1 : 0 < v1) (hv2 : 0 < v2) :
    (∀ i j : ZMod 3, j ≠ i → j ≠ i + 1 →
      TSc 1 (k6mTCyc α1 β1 (i + 1) - k6mTCyc α1 β1 i) (k6mTCyc α1 β1 j - k6mTCyc α1 β1 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (1, 0, 0), (0, 1, 0), (β6, γ6, 0)], ∀ i : ZMod 3,
      TSc 1 (k6mTCyc α1 β1 (i + 1) - k6mTCyc α1 β1 i) (t - k6mTCyc α1 β1 i) (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2⟩ := z3_add
  have a1 : 0 < β1 - 1 := by linarith
  have a2 : 0 < β1 - β6 - γ6 := by linarith
  have k2 := mul_pos (by linarith : (0:ℝ) < β1) hv1
  have k3 := mul_pos (by linarith : (0:ℝ) < β1) hv2
  have k4 := mul_pos a1 hv1
  have k5 := mul_pos a1 hv2
  have k6 := mul_pos (by linarith : (0:ℝ) < β1) hγ6
  have k7 := mul_pos (by linarith : (0:ℝ) < β1) hb6
  have k8 := mul_pos (by linarith : (0:ℝ) < β1) a2
  have k9 := mul_pos (by linarith : (0:ℝ) < β1) (by linarith : (0:ℝ) < β1)
  have k10 := mul_pos (by linarith : (0:ℝ) < β1) a1
  constructor
  · intro i j h1 h2
    rcases z3_cases i with rfl | rfl | rfl <;>
      rcases z3_cases j with rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k6mTCyc_0, k6mTCyc_1, k6mTCyc_2, s0, s1, s2, Prod.fst_sub, Prod.snd_sub,
          Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl <;>
      rcases z3_cases i with rfl | rfl | rfl <;>
      (simp only [TSc, d3, k6mTCyc_0, k6mTCyc_1, k6mTCyc_2, s0, s1, s2, Prod.fst_sub, Prod.snd_sub,
          Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
