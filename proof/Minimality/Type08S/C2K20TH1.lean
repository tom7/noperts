module

public import Minimality.Type08S.C2K20TZ2

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

/-- Facet cell `(d, b, a', c)` at `a - d`, frame `(b - d, c - d, a - d)`: ccw cycle. -/
def k20tH (b6 : ℝ) : ZMod 4 → ℝ × ℝ × ℝ := ![(0, 0, 0), (1, 0, 0), (b6, 1, 0), (0, 1, 0)]
theorem k20tH_0 : k20tH b6 0 = (0, 0, 0) := rfl
theorem k20tH_1 : k20tH b6 1 = (1, 0, 0) := rfl
theorem k20tH_2 : k20tH b6 2 = (b6, 1, 0) := rfl
theorem k20tH_3 : k20tH b6 3 = (0, 1, 0) := rfl

set_option maxHeartbeats 6400000 in
theorem k20tH_tsc {A G b1 b6 v1 v2 : ℝ} (hA : 0 < A) (hG0 : 0 < G) (hG : G < 1) (hb1 : 0 < b1) (hb11 : b1 < 1)
    (hb6 : 0 < b6) (hv1 : v1 < 0) (hv2 : v2 < 0) :
    (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      TSc 1 (k20tH b6 (i + 1) - k20tH b6 i) (k20tH b6 j - k20tH b6 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (0 : ℝ), (1 : ℝ)), (b1, 0, 1), (0, G, A)], ∀ i : ZMod 4,
      TSc 1 (k20tH b6 (i + 1) - k20tH b6 i) (t - k20tH b6 i) (v1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3⟩ := z4_add'
  have x1 : 0 < -v1 := by linarith
  have x2 : 0 < -v2 := by linarith
  have u1 : 0 < 1 - b1 := by linarith
  have u2 : 0 < 1 - G := by linarith
  have p1 := mul_pos hb1 x1
  have p2 := mul_pos hb1 x2
  have p3 := mul_pos u1 x1
  have p4 := mul_pos u1 x2
  have p5 := mul_pos hG0 x1
  have p6 := mul_pos hG0 x2
  have p7 := mul_pos u2 x1
  have p8 := mul_pos u2 x2
  have p9 := mul_pos hA x1
  have p10 := mul_pos hA x2
  have p11 := mul_pos hb6 x1
  have p12 := mul_pos hb6 x2
  have p13 := mul_pos hb6 hA
  have p14 := mul_pos hb6 u1
  have p15 := mul_pos hb6 u2
  have p16 := mul_pos hb6 hG0
  have p17 := mul_pos hb6 hb1
  have q1 := mul_pos (mul_pos hb6 hA) x1
  have q2 := mul_pos (mul_pos hb6 hA) x2
  have q3 := mul_pos (mul_pos hb6 hG0) x1
  have q4 := mul_pos (mul_pos hb6 hG0) x2
  have q5 := mul_pos (mul_pos hb6 u2) x1
  have q6 := mul_pos (mul_pos hb6 u2) x2
  have q7 := mul_pos (mul_pos u2 hb1) x1
  have q8 := mul_pos (mul_pos u2 hb1) x2
  have q9 := mul_pos (mul_pos u2 u1) x1
  have q10 := mul_pos (mul_pos u2 u1) x2
  have q11 := mul_pos (mul_pos hG0 u1) x1
  have q12 := mul_pos (mul_pos hG0 u1) x2
  have q13 := mul_pos (mul_pos hG0 hb1) x1
  have q14 := mul_pos (mul_pos hG0 hb1) x2
  constructor
  · intro i j h1 h2
    rcases z4_cases' i with rfl | rfl | rfl | rfl <;>
      rcases z4_cases' j with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k20tH_0, k20tH_1, k20tH_2, k20tH_3, f0, f1, f2, f3, Prod.fst_sub,
          Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;>
    · rcases z4_cases' i with rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k20tH_0, k20tH_1, k20tH_2, k20tH_3, f0, f1, f2, f3, Prod.fst_sub,
          Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
