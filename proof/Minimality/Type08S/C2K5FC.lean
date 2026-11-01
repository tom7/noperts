module

public import Minimality.Type08S.C2K5FB

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- ccw cycle `(a, c', a', c, b')` of box C2 in the `c - d` frame. -/
def k5fC2Cyc (α1 β1 β6 α4 γ4 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  pc5 (1, 0, 0) (α1, β1, 0) (0, β6, 1) (0, 0, 1) (α4, 0, γ4)

set_option maxHeartbeats 1600000 in
theorem k5f_C2_cyc {α1 β1 β6 α4 γ4 v1 v2 v3 : ℝ} (hα1 : 1 ≤ α1) (hβ1 : 0 < β1) (hβ6 : 1 < β6)
    (hα4 : 0 < α4) (hα41 : α4 < 1) (hγ4 : 0 < γ4) (hs : 1 < α4 + γ4) (hv1 : 0 < v1) (hv2 : 0 < v2) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k5fC2Cyc α1 β1 β6 α4 γ4 (i + 1) - k5fC2Cyc α1 β1 β6 α4 γ4 i)
        (k5fC2Cyc α1 β1 β6 α4 γ4 j - k5fC2Cyc α1 β1 β6 α4 γ4 i) (v1, v2, v3) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have a1 : 0 < α1 := by linarith
  have a2 : 0 < α1 - 1 + β1 := by linarith
  have a3 : 0 < α1 * β6 - β6 + β1 := by nlinarith
  have a4 := sub_pos.2 hα41
  have a5 : 0 < α4 + γ4 - 1 := by linarith
  have a6 := mul_pos hβ1 a4
  have a7 := mul_pos hα4 (sub_pos.2 hβ6)
  have a8 := mul_pos hv2 a5
  have a9 := mul_pos hv1 hγ4
  intro i j h1 h2'
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2' (by decide)).elim
    | (simp only [TSc, d3, k5fC2Cyc, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 1600000 in
theorem k5f_C2_rest {α1 β1 β6 α4 γ4 v1 v2 v3 : ℝ} (hα1 : 1 ≤ α1) (hβ1 : 1 < β1) (hβ6 : 1 < β6)
    (hα4 : 0 < α4) (hα41 : α4 < 1) (hγ4 : 0 < γ4) (hs : 1 < α4 + γ4) (hv1 : 0 < v1) (hv2 : 0 < v2) :
    ∀ t ∈ [((0, 0, 0) : ℝ × ℝ × ℝ), (0, 1, 0)], ∀ i : ZMod 5,
      TSc 1 (k5fC2Cyc α1 β1 β6 α4 γ4 (i + 1) - k5fC2Cyc α1 β1 β6 α4 γ4 i)
        (t - k5fC2Cyc α1 β1 β6 α4 γ4 i) (v1, v2, v3) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have a1 : 0 < α1 := by linarith
  have a4 := sub_pos.2 hα41
  have a5 : 0 < α4 + γ4 - 1 := by linarith
  have a6 := mul_pos (sub_pos.2 hβ1) a4
  have a7 := mul_pos hα4 (sub_pos.2 hβ6)
  have a8 := mul_pos hv2 a5
  have a9 := mul_pos hv1 hγ4
  have a10 := mul_pos hv1 hv2
  intro t ht i
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl <;>
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, k5fC2Cyc, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
