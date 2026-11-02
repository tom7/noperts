module

public import Minimality.Type08S.C2K22ZA
public import Minimality.Type08S.C2K19G
public import Minimality.Type08S.C2K18A
public import Minimality.Type08S.C2K16E

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

/-- Pentagon `a, d, b, a', b'` in the frame `(b-d, c-d, a-c')`, `w = 1/(α1-1)`. -/
def k24h1dY (w b1 h6 g : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  ![(-(b1 * w), 0, -w), (0, 0, 0), (1, 0, 0), (h6, g, 0), (-(b1 * (w + 1)), b1, -(w + 1))]

theorem k24h1dY_0 : k24h1dY w b1 h6 g 0 = (-(b1 * w), 0, -w) := rfl
theorem k24h1dY_1 : k24h1dY w b1 h6 g 1 = (0, 0, 0) := rfl
theorem k24h1dY_2 : k24h1dY w b1 h6 g 2 = (1, 0, 0) := rfl
theorem k24h1dY_3 : k24h1dY w b1 h6 g 3 = (h6, g, 0) := rfl
theorem k24h1dY_4 : k24h1dY w b1 h6 g 4 = (-(b1 * (w + 1)), b1, -(w + 1)) := rfl

theorem k24h1dY_inj {w b1 h6 g : ℝ} (hw : 0 < w) (hb1 : 1 < b1) (hg : 0 < g) :
    ∀ i j, k24h1dY w b1 h6 g i = k24h1dY w b1 h6 g j → i = j := by
  intro i j h
  have hbw := mul_pos (by linarith : (0:ℝ) < b1) hw
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [k24h1dY_0, k24h1dY_1, k24h1dY_2, k24h1dY_3, k24h1dY_4, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith) | (exfalso; linarith [h.1, h.2.1, h.2.2]) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; nlinarith)

set_option maxHeartbeats 12800000 in
theorem k24h1d_tsc {D w b1 h6 g v1 v2 : ℝ} (hD : 0 < D) (hw : 0 < w) (hb1 : 1 < b1) (hg : 1 < g)
    (hh6 : 1 < h6) (he : b1 < h6 + g) (hv2 : 0 < v2) (hv : 0 < v1 + v2) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc D (k24h1dY w b1 h6 g (i + 1) - k24h1dY w b1 h6 g i) (k24h1dY w b1 h6 g j - k24h1dY w b1 h6 g i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (1 : ℝ), (0 : ℝ)), (-(b1 * w), 0, -(w + 1))], ∀ i : ZMod 5,
      TSc D (k24h1dY w b1 h6 g (i + 1) - k24h1dY w b1 h6 g i) (t - k24h1dY w b1 h6 g i) (v1, v2, 0)) := by
  obtain ⟨e0, e1, e2, e3, e4, f0, f1, f2, f3, f4⟩ := k19_z5
  have b0 : 0 < b1 := by linarith
  have hb1' : 0 < b1 - 1 := by linarith
  have hh' : 0 < h6 - 1 := by linarith
  have hg' : 0 < g - 1 := by linarith
  have he' : 0 < h6 + g - b1 := by linarith
  have g0 : 0 < g := by linarith
  have h0 : 0 < h6 := by linarith
  have w1 : 0 < w + 1 := by linarith
  refine ⟨?_, ?_⟩
  · intro i j h1 h2'
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, e0, e1, e2, e3, e4, f0, f1, f2, f3, f4, k24h1dY_0, k24h1dY_1, k24h1dY_2, k24h1dY_3,
          k24h1dY_4, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; nlinarith [mul_pos hD (mul_pos b0 hw), mul_pos hD (mul_pos b0 w1), mul_pos hD (mul_pos hw g0), mul_pos hD (mul_pos hb1' hw), mul_pos hD (mul_pos hb1' g0), mul_pos hD (mul_pos hh' b0), mul_pos hD (mul_pos hg' b0), mul_pos hD (mul_pos he' b0), mul_pos hD (mul_pos he' g0), mul_pos hD (mul_pos he' hw), mul_pos hD (mul_pos he' w1), mul_pos hD (mul_pos b0 g0), mul_pos hD (mul_pos hh' g0), mul_pos hD (mul_pos hb1' w1), mul_pos hD b0, mul_pos hD g0, mul_pos hD he', mul_pos hD hb1', mul_pos hD hh', mul_pos hD hg', mul_pos hD hw, mul_pos hD w1, mul_pos hD (mul_pos hh' w1), mul_pos hD (mul_pos hh' hw), mul_pos hD (mul_pos hg' w1), mul_pos hD (mul_pos hg' hw), mul_pos hD (mul_pos h0 hw), mul_pos hD (mul_pos h0 w1)])
         | (right; refine ⟨by ring, ?_⟩; nlinarith [mul_pos hD (mul_pos b0 hw), mul_pos hD (mul_pos b0 w1), mul_pos hD (mul_pos b0 hv2), mul_pos hD (mul_pos b0 hv), mul_pos hD (mul_pos hw hv2), mul_pos hD (mul_pos hw hv), mul_pos hD (mul_pos w1 hv2), mul_pos hD (mul_pos w1 hv), mul_pos hD (mul_pos (mul_pos b0 hw) hv2), mul_pos hD (mul_pos (mul_pos b0 hw) hv), mul_pos hD (mul_pos (mul_pos b0 w1) hv2), mul_pos hD (mul_pos (mul_pos b0 w1) hv), mul_pos hD hv2, mul_pos hD hv]))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, e0, e1, e2, e3, e4, f0, f1, f2, f3, f4, k24h1dY_0, k24h1dY_1, k24h1dY_2, k24h1dY_3,
          k24h1dY_4, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith [mul_pos hD (mul_pos b0 hw), mul_pos hD (mul_pos b0 w1), mul_pos hD (mul_pos hw g0), mul_pos hD (mul_pos hb1' hw), mul_pos hD (mul_pos hb1' g0), mul_pos hD (mul_pos hh' b0), mul_pos hD (mul_pos hg' b0), mul_pos hD (mul_pos he' b0), mul_pos hD (mul_pos he' g0), mul_pos hD (mul_pos he' hw), mul_pos hD (mul_pos he' w1), mul_pos hD (mul_pos b0 g0), mul_pos hD (mul_pos hh' g0), mul_pos hD (mul_pos hb1' w1), mul_pos hD b0, mul_pos hD g0, mul_pos hD he', mul_pos hD hb1', mul_pos hD hh', mul_pos hD hg', mul_pos hD hw, mul_pos hD w1, mul_pos hD (mul_pos hh' w1), mul_pos hD (mul_pos hh' hw), mul_pos hD (mul_pos hg' w1), mul_pos hD (mul_pos hg' hw), mul_pos hD (mul_pos h0 hw), mul_pos hD (mul_pos h0 w1)])
       | (right; refine ⟨by ring, ?_⟩; nlinarith [mul_pos hD (mul_pos b0 hw), mul_pos hD (mul_pos b0 w1), mul_pos hD (mul_pos b0 hv2), mul_pos hD (mul_pos b0 hv), mul_pos hD (mul_pos hw hv2), mul_pos hD (mul_pos hw hv), mul_pos hD (mul_pos w1 hv2), mul_pos hD (mul_pos w1 hv), mul_pos hD (mul_pos (mul_pos b0 hw) hv2), mul_pos hD (mul_pos (mul_pos b0 hw) hv), mul_pos hD (mul_pos (mul_pos b0 w1) hv2), mul_pos hD (mul_pos (mul_pos b0 w1) hv), mul_pos hD hv2, mul_pos hD hv]))

end C2
end Type08Sp
end Minimality
