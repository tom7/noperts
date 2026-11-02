module

public import Minimality.Type08S.C2K14H

@[expose] public section


/-!
# K14 / I: Ta box C, the tie `D_c < 0 ∧ ζ_C = ⟪c' - a, c - d⟫ = 0`: cell `(c', b', c, d, b)` at the view `d - b`
Frame `(P, Q, R) = (a - d, c - d, b - d)`, tilt cone `v1 < 0 < v2`.
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

def k14ZcCyc (α1 β1 α4 γ4 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  ![(α1, 0, β1), (α4, γ4, 0), (0, 1, 0), (0, 0, 0), (0, 0, 1)]

theorem k14ZcCyc_0 : k14ZcCyc α1 β1 α4 γ4 0 = (α1, 0, β1) := rfl
theorem k14ZcCyc_1 : k14ZcCyc α1 β1 α4 γ4 1 = (α4, γ4, 0) := rfl
theorem k14ZcCyc_2 : k14ZcCyc α1 β1 α4 γ4 2 = (0, 1, 0) := rfl
theorem k14ZcCyc_3 : k14ZcCyc α1 β1 α4 γ4 3 = (0, 0, 0) := rfl
theorem k14ZcCyc_4 : k14ZcCyc α1 β1 α4 γ4 4 = (0, 0, 1) := rfl

theorem k14Zc_inj {α1 β1 α4 γ4 : ℝ} (hα1 : 1 < α1) (hβ1 : 0 < β1) (hα4 : α4 < 1) (hγ4 : 1 < γ4) :
    ∀ i j : ZMod 5, k14ZcCyc α1 β1 α4 γ4 i = k14ZcCyc α1 β1 α4 γ4 j → i = j := by
  intro i j h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  have e3 := congrArg (fun t => t.2.2) h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [k14ZcCyc_0, k14ZcCyc_1, k14ZcCyc_2, k14ZcCyc_3, k14ZcCyc_4] at e1 e2 e3; linarith)

set_option maxHeartbeats 3200000 in
theorem k14Zc_tsc {α1 β1 α4 γ4 β6 v1 v2 : ℝ} (hα1 : 1 < α1) (hβ1 : 1 < β1) (hα4 : 0 < α4) (hα41 : α4 < 1)
    (hγ4 : 1 < γ4) (hb6 : 1 < β6) (hv1 : v1 < 0) (hv2 : 0 < v2) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k14ZcCyc α1 β1 α4 γ4 (i + 1) - k14ZcCyc α1 β1 α4 γ4 i)
        (k14ZcCyc α1 β1 α4 γ4 j - k14ZcCyc α1 β1 α4 γ4 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0, 1, β6)], ∀ i : ZMod 5,
      TSc 1 (k14ZcCyc α1 β1 α4 γ4 (i + 1) - k14ZcCyc α1 β1 α4 γ4 i)
        (t - k14ZcCyc α1 β1 α4 γ4 i) (v1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  have nv : 0 < -v1 := by linarith
  have a1 : 0 < α1 - 1 := by linarith
  have b1 : 0 < β1 - 1 := by linarith
  have g1 : 0 < γ4 - 1 := by linarith
  have a41 : 0 < 1 - α4 := by linarith
  have b6 : 0 < β6 - 1 := by linarith
  have h1 := mul_pos nv hv2
  have h2 := mul_pos nv a1
  have h3 := mul_pos hv2 a1
  have h4 := mul_pos nv hα4
  have h5 := mul_pos hv2 hα4
  have h6 := mul_pos nv g1
  have h7 := mul_pos hv2 g1
  have h8 := mul_pos nv (by linarith : (0:ℝ) < β1)
  have h9 := mul_pos hv2 (by linarith : (0:ℝ) < β1)
  have h10 := mul_pos nv (by linarith : (0:ℝ) < β6)
  have h11 := mul_pos hv2 (by linarith : (0:ℝ) < β6)
  have h12 := mul_pos nv a41
  have h13 := mul_pos hv2 a41
  have h14 := mul_pos (by linarith : (0:ℝ) < α1) hα4
  have h15 := mul_pos a1 g1
  have h16 := mul_pos hα4 g1
  have h17 := mul_pos (mul_pos nv hv2) (by linarith : (0:ℝ) < β1)
  have h18 := mul_pos (mul_pos nv hv2) (by linarith : (0:ℝ) < β6)
  constructor
  · intro i j h1 h2
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k14ZcCyc_0, k14ZcCyc_1, k14ZcCyc_2, k14ZcCyc_3, k14ZcCyc_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k14ZcCyc_0, k14ZcCyc_1, k14ZcCyc_2, k14ZcCyc_3, k14ZcCyc_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
