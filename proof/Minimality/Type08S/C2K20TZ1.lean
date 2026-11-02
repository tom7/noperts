module

public import Minimality.Type08S.C2K20TG2

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

/-- Cell Z `(a, b', a', c')` at `c' - b`, frame `(c - d, b - d, c' - b)`: ccw cycle. -/
def k20tZ (A G b1 b6 : ℝ) : ZMod 4 → ℝ × ℝ × ℝ :=
  ![(0, 1 - b1, 1), (G, -A * (b1 - 1), A), (1, b6, 0), (0, 1, 1)]
theorem k20tZ_0 : k20tZ A G b1 b6 0 = (0, 1 - b1, 1) := rfl
theorem k20tZ_1 : k20tZ A G b1 b6 1 = (G, -A * (b1 - 1), A) := rfl
theorem k20tZ_2 : k20tZ A G b1 b6 2 = (1, b6, 0) := rfl
theorem k20tZ_3 : k20tZ A G b1 b6 3 = (0, 1, 1) := rfl

theorem z4_cases' (i : ZMod 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by revert i; decide
theorem z4_add' : (0 : ZMod 4) + 1 = 1 ∧ (1 : ZMod 4) + 1 = 2 ∧ (2 : ZMod 4) + 1 = 3 ∧ (3 : ZMod 4) + 1 = 0 := by decide

set_option maxHeartbeats 6400000 in
theorem k20tZ_tsc {A G b1 b6 v1 v2 : ℝ} (hA : 0 < A) (hG : 1 < G) (hs : 1 < A + G) (hb1 : 1 < b1) (hb6 : 0 < b6)
    (hF : A * (1 - b1) + G * (1 - b6) < 1) (hv1 : 0 < v1) (hc : 0 < (b6 - 1) * v1 - v2) :
    (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      TSc 1 (k20tZ A G b1 b6 (i + 1) - k20tZ A G b1 b6 i) (k20tZ A G b1 b6 j - k20tZ A G b1 b6 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (0, 1, 0), (1, 0, 0)], ∀ i : ZMod 4,
      TSc 1 (k20tZ A G b1 b6 (i + 1) - k20tZ A G b1 b6 i) (t - k20tZ A G b1 b6 i) (v1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3⟩ := z4_add'
  have u1 : 0 < b1 - 1 := by linarith
  have u2 : 0 < G - 1 := by linarith
  have hs' : 0 < A + G - 1 := by linarith
  have hF' : 0 < 1 - (A * (1 - b1) + G * (1 - b6)) := by linarith
  have p1 := mul_pos u1 hv1
  have p2 := mul_pos u2 hv1
  have p3 := mul_pos hA hv1
  have p4 := mul_pos hb6 hv1
  have p5 := mul_pos hs' hv1
  have p6 := mul_pos hF' hv1
  have q1 := mul_pos u1 hc
  have q2 := mul_pos u2 hc
  have q3 := mul_pos hA hc
  have q4 := mul_pos hb6 hc
  have q5 := mul_pos hs' hc
  have q6 := mul_pos hF' hc
  have r1 := mul_pos (mul_pos u1 hA) hv1
  have r2 := mul_pos (mul_pos u1 hA) hc
  have r3 := mul_pos (mul_pos u1 u2) hv1
  have r4 := mul_pos (mul_pos u1 u2) hc
  have r5 := mul_pos (mul_pos u1 hs') hv1
  have r6 := mul_pos (mul_pos u1 hs') hc
  have r7 := mul_pos (mul_pos u1 hb6) hv1
  have r8 := mul_pos (mul_pos u1 hb6) hc
  have r9 := mul_pos (mul_pos hA hb6) hv1
  have r10 := mul_pos (mul_pos hA hb6) hc
  have r11 := mul_pos hb6 hs'
  have r12 := mul_pos u2 hb6
  have r13 := mul_pos u1 hs'
  have r14 := mul_pos u1 u2
  have r15 := mul_pos hA u1
  have r16 := mul_pos hA u2
  have r17 := mul_pos hF' u1
  have r18 := mul_pos hF' u2
  constructor
  · intro i j h1 h2
    rcases z4_cases' i with rfl | rfl | rfl | rfl <;>
      rcases z4_cases' j with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k20tZ_0, k20tZ_1, k20tZ_2, k20tZ_3, f0, f1, f2, f3, Prod.fst_sub,
          Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;>
    · rcases z4_cases' i with rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k20tZ_0, k20tZ_1, k20tZ_2, k20tZ_3, f0, f1, f2, f3, Prod.fst_sub,
          Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
