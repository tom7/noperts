module

public import Minimality.Type08S.C2K22C1bE

@[expose] public section


/-!
# K22C1b / G: screen tests of the face-on cells (view `p = a - d`), frame `(q, r, p)` over `d`

Points: `d = 0, b = (1,0,0), c = (0,1,0), a' = (1,γ6,0), a = (0,0,1), c' = (β1,0,1), b' = (0,γ4,1)`.
* `F1 = (a, c', a', c, d)` (`β1 = 1`, `γ4 < 1`), hidden `b, b'`, tilt `(-1, v2)`, `0 < v2 < 1`;
* `F2 = (d, b, a', b', a)` (`β1 ≤ 1 ≤ γ4`), hidden `c, c'`, tilt `(v1, -1)`, `0 < v1 < 1`.
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

def k22c1bF1 (γ6 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ := ![(0, 0, 1), (1, 0, 1), (1, γ6, 0), (0, 1, 0), (0, 0, 0)]
theorem k22c1bF1_0 : k22c1bF1 γ6 0 = (0, 0, 1) := rfl
theorem k22c1bF1_1 : k22c1bF1 γ6 1 = (1, 0, 1) := rfl
theorem k22c1bF1_2 : k22c1bF1 γ6 2 = (1, γ6, 0) := rfl
theorem k22c1bF1_3 : k22c1bF1 γ6 3 = (0, 1, 0) := rfl
theorem k22c1bF1_4 : k22c1bF1 γ6 4 = (0, 0, 0) := rfl

def k22c1bF2 (γ4 γ6 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ := ![(0, 0, 0), (1, 0, 0), (1, γ6, 0), (0, γ4, 1), (0, 0, 1)]
theorem k22c1bF2_0 : k22c1bF2 γ4 γ6 0 = (0, 0, 0) := rfl
theorem k22c1bF2_1 : k22c1bF2 γ4 γ6 1 = (1, 0, 0) := rfl
theorem k22c1bF2_2 : k22c1bF2 γ4 γ6 2 = (1, γ6, 0) := rfl
theorem k22c1bF2_3 : k22c1bF2 γ4 γ6 3 = (0, γ4, 1) := rfl
theorem k22c1bF2_4 : k22c1bF2 γ4 γ6 4 = (0, 0, 1) := rfl

set_option maxHeartbeats 3200000 in
theorem k22c1b_tscF1 {γ4 γ6 v2 : ℝ} (hγ4 : 0 < γ4) (hγ41 : γ4 < 1) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hv : 0 < v2) (hv1 : v2 < 1) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k22c1bF1 γ6 (i + 1) - k22c1bF1 γ6 i) (k22c1bF1 γ6 j - k22c1bF1 γ6 i) (-1, v2, 0)) ∧
    (∀ t ∈ [((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0, γ4, 1)], ∀ i : ZMod 5,
      TSc 1 (k22c1bF1 γ6 (i + 1) - k22c1bF1 γ6 i) (t - k22c1bF1 γ6 i) (-1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  have k1 := mul_pos hγ6 hv
  have k2 := mul_pos hγ4 hv
  constructor
  · intro i j h1 h2
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k22c1bF1_0, k22c1bF1_1, k22c1bF1_2, k22c1bF1_3, k22c1bF1_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k22c1bF1_0, k22c1bF1_1, k22c1bF1_2, k22c1bF1_3, k22c1bF1_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 6400000 in
theorem k22c1b_tscF2 {β1 γ4 γ6 v1 : ℝ} (hβ1 : 0 < β1) (hβ11 : β1 ≤ 1) (hγ41 : 1 ≤ γ4) (hγ6 : 0 < γ6)
    (hγ61 : γ6 < 1) (hv : 0 < v1) (hv1 : v1 < 1) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k22c1bF2 γ4 γ6 (i + 1) - k22c1bF2 γ4 γ6 i) (k22c1bF2 γ4 γ6 j - k22c1bF2 γ4 γ6 i) (v1, -1, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (1 : ℝ), (0 : ℝ)), (β1, 0, 1)], ∀ i : ZMod 5,
      TSc 1 (k22c1bF2 γ4 γ6 (i + 1) - k22c1bF2 γ4 γ6 i) (t - k22c1bF2 γ4 γ6 i) (v1, -1, 0)) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  have k1 := mul_pos hγ6 hv
  have k3 : 0 < 1 - γ6 := by linarith
  have k4 := mul_pos k3 hv
  have k5 : (1 - γ6) * v1 < 1 := by nlinarith
  have k2 := mul_pos (by linarith : (0:ℝ) < γ4) hv
  rcases lt_or_eq_of_le hβ11 with hb | rfl <;> rcases lt_or_eq_of_le hγ41 with hg | rfl <;>
  · constructor
    · intro i j h1 h2
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
        rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact absurd rfl h1
        | exact (h2 (by decide)).elim
        | (simp only [TSc, d3, k22c1bF2_0, k22c1bF2_1, k22c1bF2_2, k22c1bF2_3, k22c1bF2_4, f0, f1, f2, f3, f4,
            Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
           first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
    · intro t ht i
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;>
        rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
        (simp only [TSc, d3, k22c1bF2_0, k22c1bF2_1, k22c1bF2_2, k22c1bF2_3, k22c1bF2_4, f0, f1, f2, f3, f4,
            Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
