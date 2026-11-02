module

public import Minimality.Type08S.C2K22C1bA

@[expose] public section


/-!
# K22C1b / B: screen tests of the cycle `C⁻ = (b', c', b, d, c)` at the edge-on view `w = λ q + r`

Frame `(p, q, w)` over `d`, `w = λ q + r` (`λ > 0`), so `r = w - λ q`:
`d = 0, b = (0,1,0), c = (0,-λ,1), a' = (0,1-γ6 λ,γ6), a = (1,0,0), c' = (1,β1,0), b' = (1,-γ4 λ,γ4)`.
Screen at `w`: (p, q) coordinates.  The bottom points are collinear at `w`; the tilt `v = -p + v2 q` decides.
Hidden: `a`, `a'`.
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

/-- The ccw cycle `(b', c', b, d, c)`. -/
def k22c1bM (l β1 γ4 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  ![(1, -(γ4 * l), γ4), (1, β1, 0), (0, 1, 0), (0, 0, 0), (0, -l, 1)]

theorem k22c1bM_0 : k22c1bM l β1 γ4 0 = (1, -(γ4 * l), γ4) := rfl
theorem k22c1bM_1 : k22c1bM l β1 γ4 1 = (1, β1, 0) := rfl
theorem k22c1bM_2 : k22c1bM l β1 γ4 2 = (0, 1, 0) := rfl
theorem k22c1bM_3 : k22c1bM l β1 γ4 3 = (0, 0, 0) := rfl
theorem k22c1bM_4 : k22c1bM l β1 γ4 4 = (0, -l, 1) := rfl

set_option maxHeartbeats 3200000 in
theorem k22c1b_tscM {l β1 γ4 γ6 v2 : ℝ} (hl : 0 < l) (hβ1 : 0 < β1) (hγ4 : 0 < γ4) (hγ6 : 0 < γ6)
    (hγ61 : γ6 < 1) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k22c1bM l β1 γ4 (i + 1) - k22c1bM l β1 γ4 i) (k22c1bM l β1 γ4 j - k22c1bM l β1 γ4 i) (-1, v2, 0)) ∧
    (∀ t ∈ [((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0, 1 - γ6 * l, γ6)], ∀ i : ZMod 5,
      TSc 1 (k22c1bM l β1 γ4 (i + 1) - k22c1bM l β1 γ4 i) (t - k22c1bM l β1 γ4 i) (-1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  have k1 := mul_pos hγ4 hl
  have k2 := mul_pos hβ1 hγ4
  have k3 := mul_pos hγ6 hl
  have k4 : 0 < 1 - γ6 := by linarith
  have k5 := mul_pos k4 hl
  constructor
  · intro i j h1 h2
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k22c1bM_0, k22c1bM_1, k22c1bM_2, k22c1bM_3, k22c1bM_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k22c1bM_0, k22c1bM_1, k22c1bM_2, k22c1bM_3, k22c1bM_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
