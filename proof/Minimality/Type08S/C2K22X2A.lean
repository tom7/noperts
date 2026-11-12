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

/-- Quadrilateral `a, c', a', b'` in the frame `(b-d, c-d, a-d)`. -/
def k22x2Y (β1 γ4 γ6 : ℝ) : ZMod 4 → ℝ × ℝ × ℝ :=
  ![(0, 0, 1), (β1, 0, 1), (1, γ6, 0), (0, γ4, 1)]

theorem k22x2Y_0 : k22x2Y β1 γ4 γ6 0 = (0, 0, 1) := rfl
theorem k22x2Y_1 : k22x2Y β1 γ4 γ6 1 = (β1, 0, 1) := rfl
theorem k22x2Y_2 : k22x2Y β1 γ4 γ6 2 = (1, γ6, 0) := rfl
theorem k22x2Y_3 : k22x2Y β1 γ4 γ6 3 = (0, γ4, 1) := rfl

theorem k22x2Y_inj {β1 γ4 γ6 : ℝ} (hβ1 : 0 < β1) (hβ11 : 1 < β1) (hγ6 : 0 < γ6) (hγ4 : 1 < γ4) :
    ∀ i j, k22x2Y β1 γ4 γ6 i = k22x2Y β1 γ4 γ6 j → i = j := by
  intro i j h
  rcases k19_z4_cases i with rfl | rfl | rfl | rfl <;>
    rcases k19_z4_cases j with rfl | rfl | rfl | rfl <;>
    simp only [k22x2Y_0, k22x2Y_1, k22x2Y_2, k22x2Y_3, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith)

set_option maxHeartbeats 12800000 in
theorem k22x2_tsc {D β1 γ4 γ6 v1 v2 : ℝ} (hD : 0 < D) (hβ1 : 0 < β1) (hβ11 : 1 < β1) (hγ4 : 1 < γ4)
    (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hout : β1 * γ4 < γ4 + β1 * γ6) (hv1 : 0 < v1) (hv2 : 0 < v2) :
    (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      TSc D (k22x2Y β1 γ4 γ6 (i + 1) - k22x2Y β1 γ4 γ6 i) (k22x2Y β1 γ4 γ6 j - k22x2Y β1 γ4 γ6 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (0, 1, 0), (1, 0, 0)], ∀ i : ZMod 4,
      TSc D (k22x2Y β1 γ4 γ6 (i + 1) - k22x2Y β1 γ4 γ6 i) (t - k22x2Y β1 γ4 γ6 i) (v1, v2, 0)) := by
  obtain ⟨e0, e1, e2, e3, f0, f1, f2, f3⟩ := k19_z4
  have k1 := hD
  have kb := mul_pos hD hβ1
  have kb1 := mul_pos hD (sub_pos.2 hβ11)
  have kg := mul_pos hD hγ6
  have kg1 := mul_pos hD (sub_pos.2 hγ61)
  have kg4 := mul_pos hD (sub_pos.2 hγ4)
  have kg4' := mul_pos hD (by linarith : (0:ℝ) < γ4)
  have kbb := mul_pos (mul_pos hD hβ1) (sub_pos.2 hβ11)
  have kbg4 := mul_pos (mul_pos hD hβ1) (sub_pos.2 hγ4)
  have kb1g4 := mul_pos (mul_pos hD (sub_pos.2 hβ11)) (sub_pos.2 hγ4)
  have kb1g6 := mul_pos (mul_pos hD (sub_pos.2 hβ11)) hγ6
  have kbg := mul_pos (mul_pos hD hβ1) hγ6
  have ko := mul_pos hD (sub_pos.2 hout)
  have kov1 := mul_pos (mul_pos hD (sub_pos.2 hout)) hv1
  have kov2 := mul_pos (mul_pos hD (sub_pos.2 hout)) hv2
  have kv1 := mul_pos hD hv1
  have kv2 := mul_pos hD hv2
  have kg4v1 := mul_pos (mul_pos hD (by linarith : (0:ℝ) < γ4)) hv1
  have kg4v1' := mul_pos (mul_pos hD (sub_pos.2 hγ4)) hv1
  have kbv2 := mul_pos (mul_pos hD hβ1) hv2
  have kgv1 := mul_pos (mul_pos hD hγ6) hv1
  have kgg := mul_pos (mul_pos hD (sub_pos.2 hγ61)) hγ6
  have kgg4 := mul_pos (mul_pos hD (sub_pos.2 hβ11)) (sub_pos.2 hγ61)
  have kg4g := mul_pos (mul_pos hD (by linarith : (0:ℝ) < γ4)) (sub_pos.2 hγ61)
  have kg4g' := mul_pos (mul_pos hD (by linarith : (0:ℝ) < γ4)) hγ6
  have kb1g6s := mul_pos (mul_pos hD (sub_pos.2 hβ11)) (sub_pos.2 hγ61)
  refine ⟨?_, ?_⟩
  · intro i j h1 h2'
    rcases k19_z4_cases i with rfl | rfl | rfl | rfl <;>
      rcases k19_z4_cases j with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, e0, e1, e2, e3, f0, f1, f2, f3, k22x2Y_0, k22x2Y_1, k22x2Y_2, k22x2Y_3,
            Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; nlinarith)
         | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;>
    rcases k19_z4_cases i with rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, e0, e1, e2, e3, f0, f1, f2, f3, k22x2Y_0, k22x2Y_1, k22x2Y_2, k22x2Y_3,
            Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
