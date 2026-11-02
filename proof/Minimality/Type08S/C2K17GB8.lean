module

public import Minimality.Type08S.C2K17GB7

@[expose] public section


/-!
# K17GB / GB8: S1.9 (TaE double tie) real-coordinate lemmas.
Frame `(P,Q,R) = (b-d, c-d, b'-a')`, `κ = 1/α4`, `μ = (γ4-1) κ`, `lq = α1 κ`, `m = β1 - 1`, relation `μ lq = m κ`.
Points: `a = (β6κ,-μ,κ)`, `c' = (1+m+β6lq,-m,lq)`, `b' = (β6,1,1)`, `a' = (β6,1,0)`, `b = (1,0,0)`, `c = (0,1,0)`, `d = 0`.
Cycle ccw `(c', b', c, d, a)`.  Tilt cone: `v2 < 0 ∧ (1+m) v1 + (1+m+β6lq-β6) v2 < 0`.
-/
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

def k17gbY9 (m κ μ lq β6 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  pc5 (1 + m + β6 * lq, -m, lq) (β6, 1, 1) (0, 1, 0) (0, 0, 0) (β6 * κ, -μ, κ)

set_option maxHeartbeats 3200000 in
theorem k17gb_s19_tsc {D m κ μ lq β6 v1 v2 : ℝ} (hD : 0 < D) (hm : 0 < m) (hκ : 0 < κ) (hκ1 : κ < 1)
    (hμ : 0 < μ) (hlq : κ < lq) (hrel : μ * lq = m * κ) (hb6 : 0 < β6) (hb61 : β6 < 1)
    (hv2 : v2 < 0) (hc : (1 + m) * v1 + (1 + m + β6 * lq - β6) * v2 < 0) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc D (k17gbY9 m κ μ lq β6 (i + 1) - k17gbY9 m κ μ lq β6 i)
        (k17gbY9 m κ μ lq β6 j - k17gbY9 m κ μ lq β6 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((1 : ℝ), (0 : ℝ), (0 : ℝ)), (β6, 1, 0)], ∀ i : ZMod 5,
      TSc D (k17gbY9 m κ μ lq β6 (i + 1) - k17gbY9 m κ μ lq β6 i) (t - k17gbY9 m κ μ lq β6 i) (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add_one
  have k1 := hD
  have km := mul_pos hD hm
  have kk := mul_pos hD hκ
  have kk1 := mul_pos hD (sub_pos.2 hκ1)
  have kmu := mul_pos hD hμ
  have kl := mul_pos hD (by linarith : (0:ℝ) < lq)
  have kl2 := mul_pos hD (sub_pos.2 hlq)
  have kb := mul_pos hD hb6
  have kb1 := mul_pos hD (sub_pos.2 hb61)
  have knv2 := mul_pos hD (neg_pos.2 hv2)
  have kc := mul_pos hD (neg_pos.2 hc)
  have kbm := mul_pos (mul_pos hD hb6) hm
  have kbk := mul_pos (mul_pos hD hb6) hκ
  have kbl := mul_pos (mul_pos hD hb6) (by linarith : (0:ℝ) < lq)
  have kbmu := mul_pos (mul_pos hD hb6) hμ
  have kb1k := mul_pos (mul_pos hD (sub_pos.2 hb61)) hκ
  have kmmu := mul_pos (mul_pos hD hm) hμ
  have kb1m := mul_pos (mul_pos hD (sub_pos.2 hb61)) hm
  have kb1mu := mul_pos (mul_pos hD (sub_pos.2 hb61)) hμ
  have kk1b := mul_pos (mul_pos hD (sub_pos.2 hκ1)) hb6
  have kk1bm := mul_pos (mul_pos (mul_pos hD (sub_pos.2 hκ1)) hb6) hm
  have kk1bmu := mul_pos (mul_pos (mul_pos hD (sub_pos.2 hκ1)) hb6) hμ
  have hr1 : D * (μ * lq) = D * (m * κ) := by rw [hrel]
  constructor
  · intro i j h1 h2'
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, k17gbY9, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; nlinarith)
         | (right; refine ⟨by nlinarith, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k17gbY9, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by nlinarith, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
