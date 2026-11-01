module

public import Minimality.Type08S.C2K2E
public import Minimality.Type08S.C2FC1

@[expose] public section

/-!
# C2 / K1A: the 5-cycle `X1 = (d, b, a', b', c)` at the edge view `a - d` (frame form, `s > 0`)

Frame `p = b - d`, `q = c - d`, `r = a - d`, coordinates over `d`:
`b = (1,0,0), c = (0,1,0), a = (0,0,1), c' = (β1,0,α1), b' = (0,1,α4)` (`γ4 = 1`), `a' = (β6,1,0)` (`T`).
Screen: the trapezoid `d, b, a', {b', c}` with `a` over `d`, `c'` on `[d,b]` (`β1 < 1`).  Tilt `v = (λ - 1, -1)`.
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- The ccw cycle `(d, b, a', b', c)` in the `a - d` frame, `γ4 = 1`, `γ6 = 1`. -/
def k1Cyc (β6 α4 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ := pc5 (0, 0, 0) (1, 0, 0) (β6, 1, 0) (0, 1, α4) (0, 1, 0)

set_option maxHeartbeats 1600000 in
theorem k1_cyc {D β6 α4 v1 v2 v3 : ℝ} (hD : 0 < D) (hβ6 : 0 < β6) (hα4 : 0 < α4)
    (hv1 : v1 < 0) (hv2 : v2 < 0) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc D (k1Cyc β6 α4 (i + 1) - k1Cyc β6 α4 i) (k1Cyc β6 α4 j - k1Cyc β6 α4 i) (v1, v2, v3) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have k1 := hD
  have kb6 := mul_pos hD hβ6
  have kv1 := mul_pos (mul_pos hD hα4) (neg_pos.2 hv1)
  have kv2 := mul_pos (mul_pos hD hα4) (neg_pos.2 hv2)
  have kbv := mul_pos (mul_pos (mul_pos hD hα4) hβ6) (neg_pos.2 hv2)
  intro i j h1 h2'
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2' (by decide)).elim
    | (simp only [TSc, d3, k1Cyc, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 1600000 in
theorem k1_rest {D α1 β1 α4 β6 v1 v2 v3 : ℝ} (hD : 0 < D) (hα1 : 0 < α1) (hβ1 : 0 < β1) (hβ11 : β1 < 1)
    (hα4 : 0 < α4) (hβ6 : 0 < β6) (hv1 : v1 < 0) (hv2 : v2 < 0) :
    (∀ i : ZMod 5, TSc D (k1Cyc β6 α4 (i + 1) - k1Cyc β6 α4 i) ((0, 0, 1) - k1Cyc β6 α4 i) (v1, v2, v3)) ∧
    (∀ i : ZMod 5, TSc D (k1Cyc β6 α4 (i + 1) - k1Cyc β6 α4 i) ((β1, 0, α1) - k1Cyc β6 α4 i)
      (v1, v2, v3)) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have k1 := hD
  have kb6 := mul_pos hD hβ6
  have kb1 := mul_pos hD hβ1
  have kb11 := mul_pos hD (sub_pos.2 hβ11)
  have kv1 := mul_pos (mul_pos hD hα4) (neg_pos.2 hv1)
  have kv2 := mul_pos (mul_pos hD hα4) (neg_pos.2 hv2)
  have kbv := mul_pos (mul_pos (mul_pos hD hα4) hβ6) (neg_pos.2 hv2)
  have kb1v := mul_pos (mul_pos (mul_pos hD hα4) hβ1) (neg_pos.2 hv2)
  have kv1' := mul_pos hD (neg_pos.2 hv1)
  have kv2' := mul_pos hD (neg_pos.2 hv2)
  have ka1v := mul_pos (mul_pos hD hα1) (neg_pos.2 hv2)
  refine ⟨?_, ?_⟩ <;> intro i <;>
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, k1Cyc, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

theorem k1Cyc_inj {β6 α4 : ℝ} (hβ6 : 0 < β6) (hα4 : 0 < α4) :
    ∀ i j, k1Cyc β6 α4 i = k1Cyc β6 α4 j → i = j := by
  intro i j h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [k1Cyc, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; linarith [h]) | (exfalso; norm_num at h) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; linarith)

end C2
end Type08Sp
end Minimality
