module

public import Minimality.Type08S.C2K6TCK

@[expose] public section

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

/-- Pa cell `(a, c', a', b')` (counterclockwise) in the frame `(b - d, c - d, R)`, `R = (a - d) + s (c - d)`, `s = β1 - 1`
(`R ∥ b' - c` when `κ_a = 0`): `a = (0,-s,1)`, `c' = (1+s,-s,1)`, `a' = (β6,γ6,0)`, `b' = (0,1,α4)`;
`d = 0`, `b = (1,0,0)`, `c = (0,1,0)`. -/
def k6t3_paX (s b6 g6 a4 : ℝ) : ZMod 4 → ℝ × ℝ × ℝ :=
  ![(0, -s, 1), (1 + s, -s, 1), (b6, g6, 0), (0, 1, a4)]

theorem k6t3_paX_0 : k6t3_paX s b6 g6 a4 0 = (0, -s, 1) := rfl
theorem k6t3_paX_1 : k6t3_paX s b6 g6 a4 1 = (1 + s, -s, 1) := rfl
theorem k6t3_paX_2 : k6t3_paX s b6 g6 a4 2 = (b6, g6, 0) := rfl
theorem k6t3_paX_3 : k6t3_paX s b6 g6 a4 3 = (0, 1, a4) := rfl

set_option maxHeartbeats 6400000 in
/-- Tilt test of the Pa cell `(a,c',a',b')`, cone `0 < v1`, `β6 v2 + (1 - γ6) v1 < 0`. -/
theorem k6t3_pa_tsc {s b6 g6 a4 v1 v2 : ℝ} (hs : 0 < s) (hb6 : 0 < b6) (hg6 : 0 < g6) (hg61 : g6 < 1)
    (hcv : 1 < b6 + g6) (ha4 : 0 < a4) (hv1 : 0 < v1) (hv2 : b6 * v2 + (1 - g6) * v1 < 0) :
    (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      TSc 1 (k6t3_paX s b6 g6 a4 (i + 1) - k6t3_paX s b6 g6 a4 i) (k6t3_paX s b6 g6 a4 j - k6t3_paX s b6 g6 a4 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (1, 0, 0), (0, 1, 0)], ∀ i : ZMod 4,
      TSc 1 (k6t3_paX s b6 g6 a4 (i + 1) - k6t3_paX s b6 g6 a4 i) (t - k6t3_paX s b6 g6 a4 i) (v1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3⟩ := z4_add
  have nv := neg_pos.2 hv2
  have g1 : 0 < 1 - g6 := by linarith
  have cv : 0 < b6 + g6 - 1 := by linarith
  have k1 := mul_pos hs hb6
  have k2 := mul_pos hs hv1
  have k3 := mul_pos ha4 hv1
  have k4 := mul_pos hs ha4
  have k5 := mul_pos hb6 cv
  have k6 := mul_pos hs cv
  have k7 := mul_pos (mul_pos ha4 hs) hv1
  have k8 := mul_pos ha4 (neg_pos.2 hv2)
  have k9 := mul_pos hb6 hg6
  have k10 := mul_pos hb6 hv1
  have k11 := mul_pos g1 hv1
  have k12 := mul_pos ha4 (mul_pos hb6 (neg_pos.2 hv2))
  have k13 := mul_pos hs g1
  have k14 := mul_pos hs hg6
  have k15 := mul_pos ha4 hs
  have k16 := mul_pos (mul_pos ha4 hs) hb6
  constructor
  · intro i j h1 h2
    rcases z4_cases i with rfl | rfl | rfl | rfl <;>
      rcases z4_cases j with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k6t3_paX_0, k6t3_paX_1, k6t3_paX_2, k6t3_paX_3, f0, f1, f2, f3, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;>
      rcases z4_cases i with rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k6t3_paX_0, k6t3_paX_1, k6t3_paX_2, k6t3_paX_3, f0, f1, f2, f3, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
