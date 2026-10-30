module

public import Minimality.Type08S.P2RLexUni5
public import Minimality.Type08S.P2RKT1

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkR / R5a / Q1: tilt tests of the 5-cycle `R5 = (c', b', c, d, b)` with general `b' = (α,g,0)` (orientation `0 < Δ`), for `lexCell_P3Tp_n`.
Frame coordinates over `d`: `c' = (1,0,β)`, `b' = (1,g,0)`, `c = (0,1,0)`, `d = 0`, `b = (0,0,1)`; other points
`a = (1,0,0)`, `a' = (0,h,k)`.  Tilt `v = (v1, v2, v3)` with `v1 < 0 < v2` (`v3` free: it never enters a test).
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- The 5-cycle `R5` in frame coordinates. -/
def r5CycA (α β g : ℝ) : ZMod 5 → ℝ × ℝ × ℝ := pc5 (1, 0, β) (α, g, 0) (0, 1, 0) (0, 0, 0) (0, 0, 1)

set_option maxHeartbeats 1600000 in
theorem r5A_cyc {D α β g v1 v2 v3 : ℝ} (hD : 0 < D) (hα : 0 < α) (hαg : 1 < α + g) (hβ : 0 < β) (hg : 0 < g)
    (hv1 : v1 < 0) (hv2 : 0 < v2) (hq : 0 < (α - 1) * v2 - g * v1) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc D (r5CycA α β g (i + 1) - r5CycA α β g i) (r5CycA α β g j - r5CycA α β g i) (v1, v2, v3) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have k1 := hD
  have kq := mul_pos hD hq
  have kα := mul_pos hD hα
  have kαg := mul_pos hD (sub_pos.2 hαg)
  have kαv2 := mul_pos kα hv2
  have kg := mul_pos hD hg
  have kv1 := mul_pos hD (neg_pos.2 hv1)
  have kv2 := mul_pos hD hv2
  have kgv := mul_pos kg (neg_pos.2 hv1)
  have kgbv := mul_pos (mul_pos kg hβ) (neg_pos.2 hv1)
  intro i j h1 h2'
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2' (by decide)).elim
    | (simp only [TSc, d3, r5CycA, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 1600000 in
theorem r5A_rest {D α β g h k v1 v2 v3 : ℝ} (hD : 0 < D) (hα : 0 < α) (hαg : 1 < α + g) (hβ : 0 < β) (hg : 0 < g)
    (hh : 0 < h) (hh1 : h < 1) (hk : 0 < k) (hv1 : v1 < 0) (hv2 : 0 < v2) (hq : 0 < (α - 1) * v2 - g * v1) :
    (∀ i : ZMod 5, TSc D (r5CycA α β g (i + 1) - r5CycA α β g i) ((1, 0, 0) - r5CycA α β g i) (v1, v2, v3)) ∧
    (∀ i : ZMod 5, TSc D (r5CycA α β g (i + 1) - r5CycA α β g i) ((0, h, k) - r5CycA α β g i) (v1, v2, v3)) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have k1 := hD
  have kq := mul_pos hD hq
  have kα := mul_pos hD hα
  have kαg := mul_pos hD (sub_pos.2 hαg)
  have kαv2 := mul_pos kα hv2
  have kg := mul_pos hD hg
  have kh := mul_pos hD hh
  have kh1 := mul_pos hD (by linarith : (0 : ℝ) < 1 - h)
  have kv1 := mul_pos hD (neg_pos.2 hv1)
  have kv2 := mul_pos hD hv2
  have kgv := mul_pos kg (neg_pos.2 hv1)
  have kgbv := mul_pos (mul_pos kg hβ) (neg_pos.2 hv1)
  have kkv := mul_pos (mul_pos hD hk) (neg_pos.2 hv1)
  have khv := mul_pos kh (neg_pos.2 hv1)
  refine ⟨?_, ?_⟩ <;> intro i <;>
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, r5CycA, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

end Type08Sp
end Minimality
