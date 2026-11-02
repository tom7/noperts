module

public import Minimality.Type08S.C2K14D

@[expose] public section


/-!
# K14 / E: the cell `(a, c', a', c, d)` at the view `c - d` (= `a - b'` at `α1 = 1`), frame `(P, Q, R) = (a - d, b - d, c - d)`
Screen tests in the cone `v1 > 0 > v2`.
-/
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

def k14A1Cyc (β1 β6 γ6 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  ![(1, 0, 0), (1, β1, 0), (0, β6, γ6), (0, 0, 1), (0, 0, 0)]

theorem k14A1Cyc_0 : k14A1Cyc β1 β6 γ6 0 = (1, 0, 0) := rfl
theorem k14A1Cyc_1 : k14A1Cyc β1 β6 γ6 1 = (1, β1, 0) := rfl
theorem k14A1Cyc_2 : k14A1Cyc β1 β6 γ6 2 = (0, β6, γ6) := rfl
theorem k14A1Cyc_3 : k14A1Cyc β1 β6 γ6 3 = (0, 0, 1) := rfl
theorem k14A1Cyc_4 : k14A1Cyc β1 β6 γ6 4 = (0, 0, 0) := rfl

theorem k14A1_inj {β1 β6 γ6 : ℝ} (hβ1 : 0 < β1) (hb6 : 0 < β6) (hγ6 : 0 < γ6) :
    ∀ i j : ZMod 5, k14A1Cyc β1 β6 γ6 i = k14A1Cyc β1 β6 γ6 j → i = j := by
  intro i j h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  have e3 := congrArg (fun t => t.2.2) h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [k14A1Cyc_0, k14A1Cyc_1, k14A1Cyc_2, k14A1Cyc_3, k14A1Cyc_4] at e1 e2 e3; linarith)

set_option maxHeartbeats 3200000 in
theorem k14A1_tsc {β1 β6 γ6 v1 v2 : ℝ} (hβ1 : 1 < β1) (hb6 : 1 < β6) (hγ6 : 0 < γ6)
    (hv1 : 0 < v1) (hv2 : v2 < 0) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k14A1Cyc β1 β6 γ6 (i + 1) - k14A1Cyc β1 β6 γ6 i)
        (k14A1Cyc β1 β6 γ6 j - k14A1Cyc β1 β6 γ6 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (1 : ℝ), (0 : ℝ)), (1, 0, β1)], ∀ i : ZMod 5,
      TSc 1 (k14A1Cyc β1 β6 γ6 (i + 1) - k14A1Cyc β1 β6 γ6 i)
        (t - k14A1Cyc β1 β6 γ6 i) (v1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  have nv : 0 < -v2 := by linarith
  have b1 : 0 < β1 - 1 := by linarith
  have b6 : 0 < β6 - 1 := by linarith
  have h1 := mul_pos hv1 hγ6
  have h2 := mul_pos nv hγ6
  have h3 := mul_pos hv1 b1
  have h4 := mul_pos nv b1
  have h5 := mul_pos hv1 b6
  have h6 := mul_pos nv b6
  have h7 := mul_pos hv1 (by linarith : (0:ℝ) < β1)
  have h8 := mul_pos nv (by linarith : (0:ℝ) < β1)
  have h9 := mul_pos hv1 (by linarith : (0:ℝ) < β6)
  have h10 := mul_pos nv (by linarith : (0:ℝ) < β6)
  have h11 := mul_pos hv1 nv
  have h12 := mul_pos b1 b6
  have h13 := mul_pos (mul_pos hv1 hγ6) b1
  have h14 := mul_pos (mul_pos nv hγ6) b1
  have h15 := mul_pos (mul_pos hv1 hγ6) b6
  have h16 := mul_pos (mul_pos nv hγ6) b6
  constructor
  · intro i j h1 h2
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k14A1Cyc_0, k14A1Cyc_1, k14A1Cyc_2, k14A1Cyc_3, k14A1Cyc_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k14A1Cyc_0, k14A1Cyc_1, k14A1Cyc_2, k14A1Cyc_3, k14A1Cyc_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
