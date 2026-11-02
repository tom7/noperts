module

public import Minimality.Type08S.C2K6MB

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2

set_option maxHeartbeats 3200000 in
theorem k6m_B_tsc {α1 β1 β6 γ6 v1 v2 : ℝ} (hα1 : 0 < α1) (hα11 : α1 < 1) (hβ1 : 0 < β1) (hs : 1 < α1 + β1)
    (hb6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hv1 : 0 < v1) (hv2 : 0 < v2) :
    (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      TSc 1 (kqCyc α1 β1 (i + 1) - kqCyc α1 β1 i) (kqCyc α1 β1 j - kqCyc α1 β1 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (0 : ℝ), (-1 : ℝ)), (α1, 0, -β1), (0, γ6, -β6)], ∀ i : ZMod 4,
      TSc 1 (kqCyc α1 β1 (i + 1) - kqCyc α1 β1 i) (t - kqCyc α1 β1 i) (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3⟩ := z4_add
  have a1 : 0 < 1 - α1 := by linarith
  have a2 : 0 < α1 + β1 - 1 := by linarith
  have a3 : 0 < 1 - γ6 := by linarith
  have k1 := mul_pos hβ1 hv2
  have k2 := mul_pos hb6 hv1
  have k3 := mul_pos hβ1 hv1
  have k4 := mul_pos hb6 hv2
  have k5 := mul_pos a1 hγ6
  have k6 := mul_pos hα1 hβ1
  have k7 := mul_pos hγ6 hb6
  have k8 := mul_pos a2 hγ6
  have k9 := mul_pos a3 hb6
  have k10 := mul_pos a2 hb6
  have k11 := mul_pos a1 hb6
  have k12 := mul_pos hα1 hb6
  have k13 := mul_pos a1 hβ1
  have k14 := mul_pos a2 hβ1
  have k15 := mul_pos hα1 hγ6
  have k16 := mul_pos a3 hα1
  have k17 := mul_pos a3 hβ1
  constructor
  · intro i j h1 h2
    rcases z4_cases i with rfl | rfl | rfl | rfl <;>
      rcases z4_cases j with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, kqCyc_0, kqCyc_1, kqCyc_2, kqCyc_3, s0, s1, s2, s3, Prod.fst_sub, Prod.snd_sub,
          Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;>
      rcases z4_cases i with rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, kqCyc_0, kqCyc_1, kqCyc_2, kqCyc_3, s0, s1, s2, s3, Prod.fst_sub, Prod.snd_sub,
          Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
