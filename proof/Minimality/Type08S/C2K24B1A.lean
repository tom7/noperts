module

public import Minimality.Type08S.C2K20HI
public import Minimality.Type08S.C2K14O
public import Minimality.Type08S.C2K17BA

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

/-- K24B1: quad `(a, c', a', b')` in the frame `(q, r, p)` (`p = a-d`, `q = b-d`, `r = c-d`), `α1 = 1`. -/
def k24b1Cyc (β1 β6 γ6 : ℝ) : ZMod 4 → ℝ × ℝ × ℝ :=
  ![(0, 0, 1), (β1, 0, 1), (β6, γ6, 0), (0, β1, 1)]

theorem k24b1Cyc_0 : k24b1Cyc β1 β6 γ6 0 = (0, 0, 1) := rfl
theorem k24b1Cyc_1 : k24b1Cyc β1 β6 γ6 1 = (β1, 0, 1) := rfl
theorem k24b1Cyc_2 : k24b1Cyc β1 β6 γ6 2 = (β6, γ6, 0) := rfl
theorem k24b1Cyc_3 : k24b1Cyc β1 β6 γ6 3 = (0, β1, 1) := rfl

theorem k24b1_inj {β1 β6 γ6 : ℝ} (hβ1 : 1 < β1) (hb6 : 0 < β6) (hg6 : 0 < γ6) :
    ∀ i j : ZMod 4, k24b1Cyc β1 β6 γ6 i = k24b1Cyc β1 β6 γ6 j → i = j := by
  intro i j h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  have e3 := congrArg (fun t => t.2.2) h
  rcases z4_cases i with rfl | rfl | rfl | rfl <;> rcases z4_cases j with rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [k24b1Cyc_0, k24b1Cyc_1, k24b1Cyc_2, k24b1Cyc_3] at e1 e2 e3; linarith)

set_option maxHeartbeats 3200000 in
theorem k24b1_tsc {β1 β6 γ6 v1 v2 : ℝ} (hβ1 : 1 < β1) (hb6 : 0 < β6) (hg6 : 0 < γ6)
    (hs : β1 < β6 + γ6) (hv1 : 0 < v1) (hv2 : 0 < v2) :
    (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      TSc 1 (k24b1Cyc β1 β6 γ6 (i + 1) - k24b1Cyc β1 β6 γ6 i)
        (k24b1Cyc β1 β6 γ6 j - k24b1Cyc β1 β6 γ6 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0, 1, 0), (0, 0, 0)], ∀ i : ZMod 4,
      TSc 1 (k24b1Cyc β1 β6 γ6 (i + 1) - k24b1Cyc β1 β6 γ6 i)
        (t - k24b1Cyc β1 β6 γ6 i) (v1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3⟩ := z4_add
  have e1 : 0 < β1 - 1 := by linarith
  have b1 : 0 < β1 := by linarith
  have s1 : 0 < β1 * β6 + γ6 - β1 := by nlinarith
  have s2 : 0 < β6 + β1 * γ6 - β1 := by nlinarith
  have p1 := mul_pos b1 b1
  have p2 := mul_pos b1 hb6
  have p3 := mul_pos b1 hg6
  have p4 := mul_pos hb6 e1
  have p5 := mul_pos hg6 e1
  have p6 := mul_pos b1 hv2
  have p7 := mul_pos b1 hv1
  have p8 := mul_pos b1 (sub_pos.2 hs)
  have p9 := mul_pos hb6 (sub_pos.2 hs)
  have p10 := mul_pos hg6 (sub_pos.2 hs)
  have p11 := mul_pos e1 (sub_pos.2 hs)
  have p12 := mul_pos hb6 hg6
  constructor
  · intro i j h1 h2
    rcases z4_cases i with rfl | rfl | rfl | rfl <;>
      rcases z4_cases j with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k24b1Cyc_0, k24b1Cyc_1, k24b1Cyc_2, k24b1Cyc_3, f0, f1, f2, f3,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;>
      rcases z4_cases i with rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k24b1Cyc_0, k24b1Cyc_1, k24b1Cyc_2, k24b1Cyc_3, f0, f1, f2, f3,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
