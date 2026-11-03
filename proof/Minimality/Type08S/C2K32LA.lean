module

public import Minimality.Type08S.C2K20HI
public import Minimality.Type08S.C2K14O
public import Minimality.Type08S.C2K17BA
public import Minimality.Type08S.P2RR2a
public import Minimality.Type08S.P2RR2c

@[expose] public section

set_option maxHeartbeats 1000000

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

/-- K24B2L: cycle `(d, a, c', b', c)` in the frame `(q, r, p)`, `p = a-d`. -/
def k24b2Cyc (α1 β1 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  K.cyc5 (0, 0, 0) (0, 0, 1) (β1, 0, α1) (0, β1, α1) (0, 1, 0)

theorem k24b2_inj {α1 β1 : ℝ} (hα : 1 < α1) (hβ1 : 1 < β1) :
    ∀ i j : ZMod 5, k24b2Cyc α1 β1 i = k24b2Cyc α1 β1 j → i = j := by
  intro i j h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  have e3 := congrArg (fun t => t.2.2) h
  rcases K.z5c i with rfl | rfl | rfl | rfl | rfl <;> rcases K.z5c j with rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [k24b2Cyc, K.c5_0, K.c5_1, K.c5_2, K.c5_3, K.c5_4] at e1 e2 e3; linarith)

set_option maxHeartbeats 3200000 in
theorem k24b2_tsc {α1 β1 β6 γ6 v1 v2 : ℝ} (hα : 1 < α1) (hβ1 : 1 < β1) (hb6 : 0 < β6) (hg6 : 0 < γ6)
    (hs : β6 + γ6 = β1) (hv2 : 0 < v2) (hv12 : v1 + v2 < 0) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k24b2Cyc α1 β1 (i + 1) - k24b2Cyc α1 β1 i)
        (k24b2Cyc α1 β1 j - k24b2Cyc α1 β1 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((1 : ℝ), (0 : ℝ), (0 : ℝ)), (β6, γ6, 0)], ∀ i : ZMod 5,
      TSc 1 (k24b2Cyc α1 β1 (i + 1) - k24b2Cyc α1 β1 i)
        (t - k24b2Cyc α1 β1 i) (v1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := K.z5s
  have e1 : 0 < β1 - 1 := by linarith
  have b1 : 0 < β1 := by linarith
  have hv1 : v1 < 0 := by linarith
  have g6 : γ6 = β1 - β6 := by linarith
  have p1 := mul_pos b1 b1
  have p2 := mul_pos b1 hb6
  have p3 := mul_pos b1 hg6
  have p4 := mul_pos hb6 e1
  have p5 := mul_pos hg6 e1
  have p6 := mul_pos b1 hv2
  have p7 := mul_pos b1 e1
  have p8 := mul_pos hb6 hg6
  have p9 := mul_pos hb6 hv2
  have p10 := mul_pos hg6 hv2
  have p11 := mul_pos b1 (neg_pos.2 hv1)
  have p12 := mul_pos hg6 (neg_pos.2 hv1)
  have p13 := mul_pos hb6 (neg_pos.2 hv1)
  have p14 := mul_pos b1 (neg_pos.2 hv12)
  have p15 := mul_pos hg6 (neg_pos.2 hv12)
  have p16 := mul_pos hb6 (neg_pos.2 hv12)
  have p17 := mul_pos e1 (neg_pos.2 hv12)
  have p18 := mul_pos (sub_pos.2 hα) hv2
  constructor
  · intro i j h1 h2
    rcases K.z5c i with rfl | rfl | rfl | rfl | rfl <;>
      rcases K.z5c j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k24b2Cyc, K.c5_0, K.c5_1, K.c5_2, K.c5_3, K.c5_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by first | ring1 | (rw [← hs]; ring1), by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
      rcases K.z5c i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k24b2Cyc, K.c5_0, K.c5_1, K.c5_2, K.c5_3, K.c5_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by first | ring1 | (rw [← hs]; ring1), by nlinarith⟩))

end C2
end Type08Sp
end Minimality
