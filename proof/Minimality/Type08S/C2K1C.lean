module

public import Minimality.Type08S.C2K1B

@[expose] public section

/-!
# C2 / K1C: the 6-cycle `X2 = (a, c', b, a', c, d)` at the edge view `a - d` as `HasLexCellAt` (`s < 0`)

Same frame as K1A.  Screen: `a, c', b, d` on the line `y = 0` (`a` over `d`), `a'` and `c` on `y = 1`; the tilt
`v = (-1, 1 + λ)` (cone `v1 < 0 < v2`) opens the hexagon `a, c', b, a', c, d`; `b'` hides behind `c`.
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- The ccw cycle `(a, c', b, a', c, d)` in the `a - d` frame, `γ4 = γ6 = 1`. -/
def k1Cyc6 (α1 β1 β6 : ℝ) : ZMod 6 → ℝ × ℝ × ℝ :=
  six (0, 0, 1) (β1, 0, α1) (1, 0, 0) (β6, 1, 0) (0, 1, 0) (0, 0, 0)

set_option maxHeartbeats 3200000 in
theorem k1_cyc6 {D α1 β1 β6 v1 v2 v3 : ℝ} (hD : 0 < D) (hα1 : 1 < α1) (hβ1 : 0 < β1) (hβ11 : β1 < 1)
    (hβ6 : 0 < β6) (hv1 : v1 < 0) (hv2 : 0 < v2) :
    ∀ i j : ZMod 6, j ≠ i → j ≠ i + 1 →
      TSc D (k1Cyc6 α1 β1 β6 (i + 1) - k1Cyc6 α1 β1 β6 i) (k1Cyc6 α1 β1 β6 j - k1Cyc6 α1 β1 β6 i)
        (v1, v2, v3) := by
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := z6_add_one
  have k1 := hD
  have kb6 := mul_pos hD hβ6
  have kb1 := mul_pos hD hβ1
  have kb11 := mul_pos hD (sub_pos.2 hβ11)
  have kv1 := mul_pos hD (neg_pos.2 hv1)
  have kv2 := mul_pos hD hv2
  have ka1 := mul_pos hD (sub_pos.2 hα1)
  have ka1v := mul_pos (mul_pos hD (sub_pos.2 hα1)) hv2
  have kb1v := mul_pos (mul_pos hD hβ1) hv2
  have kb6v := mul_pos (mul_pos hD hβ6) hv2
  have kab := mul_pos hD (by linarith : (0 : ℝ) < α1 + β1 - 1)
  have kabv := mul_pos (mul_pos hD (by linarith : (0 : ℝ) < α1 + β1 - 1)) hv2
  have ka1v' := mul_pos (mul_pos hD (by linarith : (0 : ℝ) < α1)) hv2
  intro i j h1 h2'
  rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2' (by decide)).elim
    | (simp only [TSc, d3, k1Cyc6, s0, s1, s2, s3, s4, s5, six_0, six_1, six_2, six_3, six_4, six_5,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 3200000 in
theorem k1_rest6 {D α1 β1 α4 β6 v1 v2 v3 : ℝ} (hD : 0 < D) (hα1 : 1 < α1) (hβ1 : 0 < β1) (hβ11 : β1 < 1)
    (hα4 : 0 < α4) (hβ6 : 0 < β6) (hv1 : v1 < 0) (hv2 : 0 < v2) :
    ∀ i : ZMod 6, TSc D (k1Cyc6 α1 β1 β6 (i + 1) - k1Cyc6 α1 β1 β6 i) ((0, 1, α4) - k1Cyc6 α1 β1 β6 i)
      (v1, v2, v3) := by
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := z6_add_one
  have k1 := hD
  have kb6 := mul_pos hD hβ6
  have kb1 := mul_pos hD hβ1
  have kb11 := mul_pos hD (sub_pos.2 hβ11)
  have kv1 := mul_pos hD (neg_pos.2 hv1)
  have kv2 := mul_pos hD hv2
  have kv1a := mul_pos (mul_pos hD hα4) (neg_pos.2 hv1)
  have kb6a := mul_pos (mul_pos (mul_pos hD hβ6) hα4) hv2
  have kb6v := mul_pos (mul_pos hD hβ6) hv2
  intro i
  rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, k1Cyc6, s0, s1, s2, s3, s4, s5, six_0, six_1, six_2, six_3, six_4, six_5,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

theorem k1Cyc6_inj {α1 β1 β6 : ℝ} (hα1 : 1 < α1) (hβ1 : 0 < β1) (hβ11 : β1 < 1) (hβ6 : 0 < β6) :
    ∀ i j, k1Cyc6 α1 β1 β6 i = k1Cyc6 α1 β1 β6 j → i = j := by
  intro i j h
  rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [k1Cyc6, six_0, six_1, six_2, six_3, six_4, six_5, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith [h])

end C2
end Type08Sp
end Minimality
