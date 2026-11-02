module

public import Minimality.Type08S.C2K22ZA
public import Minimality.Type08S.C2K19G
public import Minimality.Type08S.C2K18A

@[expose] public section


set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- Pentagon `a (0,0,1), c' (β1,0,1), b (1,0,0), a' (1,γ6,0), b' (0,γ4,1)` in the frame `(b-d, c-d, a-d)`. -/
def k22t1Y (γ4 γ6 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  ![(0, 0, 1), (1, 0, 1), (1, 0, 0), (1, γ6, 0), (0, γ4, 1)]

theorem k22t1Y_0 : k22t1Y γ4 γ6 0 = (0, 0, 1) := rfl
theorem k22t1Y_1 : k22t1Y γ4 γ6 1 = (1, 0, 1) := rfl
theorem k22t1Y_2 : k22t1Y γ4 γ6 2 = (1, 0, 0) := rfl
theorem k22t1Y_3 : k22t1Y γ4 γ6 3 = (1, γ6, 0) := rfl
theorem k22t1Y_4 : k22t1Y γ4 γ6 4 = (0, γ4, 1) := rfl

theorem k22t1Y_inj {γ4 γ6 : ℝ} (hγ6 : 0 < γ6) (hγ4 : 1 < γ4) :
    ∀ i j, k22t1Y γ4 γ6 i = k22t1Y γ4 γ6 j → i = j := by
  intro i j h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [k22t1Y_0, k22t1Y_1, k22t1Y_2, k22t1Y_3, k22t1Y_4, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith) | (exfalso; linarith [h.1, h.2.1, h.2.2]) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; linarith)

set_option maxHeartbeats 12800000 in
theorem k22t1_tsc {D γ4 γ6 v1 v2 : ℝ} (hD : 0 < D) (hγ4 : 1 < γ4)
    (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hv1 : 0 < v1) (hv2 : 0 < v2) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc D (k22t1Y γ4 γ6 (i + 1) - k22t1Y γ4 γ6 i) (k22t1Y γ4 γ6 j - k22t1Y γ4 γ6 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (0, 1, 0)], ∀ i : ZMod 5,
      TSc D (k22t1Y γ4 γ6 (i + 1) - k22t1Y γ4 γ6 i) (t - k22t1Y γ4 γ6 i) (v1, v2, 0)) := by
  obtain ⟨e0, e1, e2, e3, e4, f0, f1, f2, f3, f4⟩ := k19_z5
  have k1 := hD
  have kg := mul_pos hD hγ6
  have kg1 := mul_pos hD (sub_pos.2 hγ61)
  have kg4 := mul_pos hD (sub_pos.2 hγ4)
  have kg4' := mul_pos hD (by linarith : (0:ℝ) < γ4)
  have kv1 := mul_pos hD hv1
  have kv2 := mul_pos hD hv2
  have kg4v1 := mul_pos (mul_pos hD (by linarith : (0:ℝ) < γ4)) hv1
  have kg4v1' := mul_pos (mul_pos hD (sub_pos.2 hγ4)) hv1
  have kgv1 := mul_pos (mul_pos hD hγ6) hv1
  have kgg := mul_pos (mul_pos hD (sub_pos.2 hγ61)) hγ6
  have kg4g := mul_pos (mul_pos hD (by linarith : (0:ℝ) < γ4)) (sub_pos.2 hγ61)
  have kg4g' := mul_pos (mul_pos hD (by linarith : (0:ℝ) < γ4)) hγ6
  refine ⟨?_, ?_⟩
  · intro i j h1 h2'
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, e0, e1, e2, e3, e4, f0, f1, f2, f3, f4, k22t1Y_0, k22t1Y_1, k22t1Y_2, k22t1Y_3,
          k22t1Y_4, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; nlinarith)
         | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, e0, e1, e2, e3, e4, f0, f1, f2, f3, f4, k22t1Y_0, k22t1Y_1, k22t1Y_2, k22t1Y_3,
          k22t1Y_4, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
