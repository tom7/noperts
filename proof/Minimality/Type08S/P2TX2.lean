module

public import Minimality.Type08S.P2TX1

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkP / X2: orientation tests of the cell `(−,−,−)` at `T` in the frame of `h3_setup`.
Rim `X_ba' = (b, c', b', a')`; tilt `(t1, 1)` with `0 < u := σ (w1 - ha t1) < r (γ4 - 1) / α4`, `r = -(σ v1)`.
-/

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unreachableTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- The rim `(b, c', b', a')` in frame coordinates. -/
def cellRim (ν v1 ha w1 w3 C0 α1 α4 γ4 β1 β6 : ℝ) : ZMod 4 → ℝ × ℝ × ℝ :=
  quad (-v1, 0, ν) (-v1 + α1 * w1, α1 * ha, α1 * w3 + β1 * ν)
    (-v1 * (1 - γ4) + α4 * w1, α4 * ha, α4 * w3 + γ4 * C0) (0, 0, β6 * ν + C0)

theorem z4_add_one : (0 : ZMod 4) + 1 = 1 ∧ (1 : ZMod 4) + 1 = 2 ∧ (2 : ZMod 4) + 1 = 3 ∧
    (3 : ZMod 4) + 1 = 0 := by decide

set_option maxHeartbeats 1600000 in
theorem cell_cyc {σ t1 ν v1 ha w1 w3 C0 α1 α4 γ4 β1 β6 : ℝ}
    (hν : 0 < ν) (hha : 0 < ha) (hα : 1 < α1) (hα4 : 0 < α4) (hγ4 : 1 < γ4) (hβ1 : 0 < β1)
    (hE : 0 < α4 - α4 * β1 - α1 * (1 - γ4)) (hv : σ * v1 < 0) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      LT σ t1 1 (cellRim ν v1 ha w1 w3 C0 α1 α4 γ4 β1 β6 i)
        (cellRim ν v1 ha w1 w3 C0 α1 α4 γ4 β1 β6 (i + 1))
        (cellRim ν v1 ha w1 w3 C0 α1 α4 γ4 β1 β6 j) := by
  obtain ⟨s0, s1, s2, s3⟩ := z4_add_one
  have hr : 0 < -(σ * v1) := by linarith
  have kA := mul_pos (mul_pos (mul_pos hr hha) (by linarith : (0:ℝ) < γ4)) (by linarith : (0:ℝ) < α1)
  have kB := mul_pos (mul_pos hr hha) (by nlinarith [mul_pos hα4 hβ1] : 0 < α4 - α1 * (1 - γ4))
  have kC := mul_pos (mul_pos hr hha) hα4
  have kD := mul_pos (mul_pos hr hha) (by linarith : (0:ℝ) < α1)
  intro i j h1 h2'
  rcases z4_cases i with rfl | rfl | rfl | rfl <;>
    rcases z4_cases j with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2' (by decide)).elim
    | (simp only [LT, ori, fo, cellRim, s0, s1, s2, s3, quad4_0, quad4_1, quad4_2, quad4_3]
       left; linarith)

set_option maxHeartbeats 1600000 in
theorem cell_rest {σ t1 ν v1 ha w1 w3 C0 α1 α4 γ4 β1 β6 : ℝ}
    (hν : 0 < ν) (hha : 0 < ha) (hα : 1 < α1) (hα4 : 0 < α4) (hγ4 : 1 < γ4) (hβ1 : 0 < β1)
    (hβ6 : 0 < β6) (hv : σ * v1 < 0)
    (hu : 0 < σ * (w1 - ha * t1)) (hu2 : σ * (w1 - ha * t1) * α4 < -(σ * v1) * (γ4 - 1)) :
    (∀ i : ZMod 4, LT σ t1 1 (cellRim ν v1 ha w1 w3 C0 α1 α4 γ4 β1 β6 i)
        (cellRim ν v1 ha w1 w3 C0 α1 α4 γ4 β1 β6 (i + 1)) (-v1, 0, 0)) ∧
    (∀ i : ZMod 4, LT σ t1 1 (cellRim ν v1 ha w1 w3 C0 α1 α4 γ4 β1 β6 i)
        (cellRim ν v1 ha w1 w3 C0 α1 α4 γ4 β1 β6 (i + 1)) (0, 0, C0)) ∧
    (∀ i : ZMod 4, LT σ t1 1 (cellRim ν v1 ha w1 w3 C0 α1 α4 γ4 β1 β6 i)
        (cellRim ν v1 ha w1 w3 C0 α1 α4 γ4 β1 β6 (i + 1)) (-v1 + w1, ha, w3)) := by
  obtain ⟨s0, s1, s2, s3⟩ := z4_add_one
  have hr : 0 < -(σ * v1) := by linarith
  have kA := mul_pos (mul_pos (mul_pos hr hha) (by linarith : (0:ℝ) < γ4)) (by linarith : (0:ℝ) < α1)
  have kB := mul_pos (mul_pos hr hha) (by nlinarith [mul_pos hα4 hβ1] : 0 < α4 - α1 * (1 - γ4))
  have kC := mul_pos (mul_pos hr hha) hα4
  have kD := mul_pos (mul_pos hr hha) (by linarith : (0:ℝ) < α1)
  have kE := mul_pos (mul_pos (mul_pos hr hha) (by linarith : (0:ℝ) < γ4)) (by linarith : (0:ℝ) < α1 - 1)
  have kF := mul_pos (mul_pos hr hha) (by linarith : (0:ℝ) < α4 + γ4 - 1)
  have kG := mul_pos hr hha
  have fd0 := mul_pos (mul_pos hν (by linarith : (0:ℝ) < α1)) hu
  have fd3 := mul_pos hν hr
  have fc3 := mul_pos hβ6 (mul_pos hν hr)
  have fc2 := mul_pos (mul_pos hβ6 hν) (by linarith : 0 < -(σ * v1) * (γ4 - 1) - σ * (w1 - ha * t1) * α4)
  have fa0 := mul_pos (mul_pos hν (by linarith : (0:ℝ) < α1 + β1 - 1)) hu
  refine ⟨?_, ?_, ?_⟩ <;> intro i <;>
  rcases z4_cases i with rfl | rfl | rfl | rfl <;>
    (simp only [LT, ori, fo, cellRim, s0, s1, s2, s3, quad4_0, quad4_1, quad4_2, quad4_3]
     first
     | (left; linarith)
     | (right; refine ⟨by ring, by linarith⟩))

end Type08Sp
end Minimality
