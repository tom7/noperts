module

public import Minimality.Type08S.P2TX5

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkP / X2 / Y1: orientation tests of the cell `(+,−,−)` at `T` in the frame of `h3_setup`.
Rim `(a', b, d, a, c', b')` (six points); tilt `(t1, 1)` with `u := σ (ha t1 − w1) > 0` and
`α4 u > r (1 − γ4)`, `r = −(σ v1) > 0`.
-/

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unreachableTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- A 6-cycle as a function on `ZMod 6`. -/
def c2rim6 {α : Type*} (p₀ p₁ p₂ p₃ p₄ p₅ : α) : ZMod 6 → α := ![p₀, p₁, p₂, p₃, p₄, p₅]

theorem c2rim6_0 {α : Type*} {w0 w1 w2 w3 w4 w5 : α} : c2rim6 w0 w1 w2 w3 w4 w5 0 = w0 := rfl
theorem c2rim6_1 {α : Type*} {w0 w1 w2 w3 w4 w5 : α} : c2rim6 w0 w1 w2 w3 w4 w5 1 = w1 := rfl
theorem c2rim6_2 {α : Type*} {w0 w1 w2 w3 w4 w5 : α} : c2rim6 w0 w1 w2 w3 w4 w5 2 = w2 := rfl
theorem c2rim6_3 {α : Type*} {w0 w1 w2 w3 w4 w5 : α} : c2rim6 w0 w1 w2 w3 w4 w5 3 = w3 := rfl
theorem c2rim6_4 {α : Type*} {w0 w1 w2 w3 w4 w5 : α} : c2rim6 w0 w1 w2 w3 w4 w5 4 = w4 := rfl
theorem c2rim6_5 {α : Type*} {w0 w1 w2 w3 w4 w5 : α} : c2rim6 w0 w1 w2 w3 w4 w5 5 = w5 := rfl

theorem c2z6_cases (i : ZMod 6) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
  revert i; decide

theorem c2z6_add_one : (0 : ZMod 6) + 1 = 1 ∧ (1 : ZMod 6) + 1 = 2 ∧ (2 : ZMod 6) + 1 = 3 ∧
    (3 : ZMod 6) + 1 = 4 ∧ (4 : ZMod 6) + 1 = 5 ∧ (5 : ZMod 6) + 1 = 0 := by decide

theorem c2z6_sub_one : (0 : ZMod 6) - 1 = 5 ∧ (1 : ZMod 6) - 1 = 0 ∧ (2 : ZMod 6) - 1 = 1 ∧
    (3 : ZMod 6) - 1 = 2 ∧ (4 : ZMod 6) - 1 = 3 ∧ (5 : ZMod 6) - 1 = 4 := by decide

/-- The rim `(a', b, d, a, c', b')` in frame coordinates. -/
def cell2Rim (ν v1 ha w1 w3 C0 α1 α4 γ4 β1 β6 : ℝ) : ZMod 6 → ℝ × ℝ × ℝ :=
  c2rim6 (0, 0, β6 * ν + C0) (-v1, 0, ν) (-v1, 0, 0) (-v1 + w1, ha, w3)
    (-v1 + α1 * w1, α1 * ha, α1 * w3 + β1 * ν)
    (-v1 * (1 - γ4) + α4 * w1, α4 * ha, α4 * w3 + γ4 * C0)

set_option maxHeartbeats 3200000 in
theorem cell2_cyc {σ t1 ν v1 ha w1 w3 C0 α1 α4 γ4 β1 β6 : ℝ}
    (hν : 0 < ν) (hha : 0 < ha) (hα : 1 < α1) (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hβ1 : 0 < β1)
    (hβ6 : 0 < β6) (hE : 0 < α4 - α4 * β1 - α1 * (1 - γ4)) (hv : σ * v1 < 0)
    (hu : 0 < σ * (ha * t1 - w1)) (hu2 : -(σ * v1) * (1 - γ4) < α4 * (σ * (ha * t1 - w1))) :
    ∀ i j : ZMod 6, j ≠ i → j ≠ i + 1 →
      LT σ t1 1 (cell2Rim ν v1 ha w1 w3 C0 α1 α4 γ4 β1 β6 i)
        (cell2Rim ν v1 ha w1 w3 C0 α1 α4 γ4 β1 β6 (i + 1))
        (cell2Rim ν v1 ha w1 w3 C0 α1 α4 γ4 β1 β6 j) := by
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := c2z6_add_one
  have hr : 0 < -(σ * v1) := by linarith
  have hB : 0 < α4 - α1 * (1 - γ4) := by nlinarith [mul_pos hα4 hβ1]
  have hF : 0 < α4 + γ4 - 1 := by
    rcases le_or_gt γ4 1 with h | h
    · nlinarith
    · linarith
  have k1 := mul_pos hr hha
  have k2 := mul_pos (mul_pos hr hha) (by linarith : (0:ℝ) < α1)
  have k3 := mul_pos (mul_pos hr hha) hα4
  have k4 := mul_pos (mul_pos hr hha) hγ4
  have k5 := mul_pos (mul_pos (mul_pos hr hha) hγ4) (by linarith : (0:ℝ) < α1)
  have k6 := mul_pos (mul_pos hr hha) (by linarith : (0:ℝ) < α1 - 1)
  have k7 := mul_pos (mul_pos (mul_pos hr hha) hγ4) (by linarith : (0:ℝ) < α1 - 1)
  have k8 := mul_pos (mul_pos hr hha) hB
  have k9 := mul_pos (mul_pos hr hha) hF
  have k10 := mul_pos (mul_pos (mul_pos hr hha) hγ4) hα4
  have f1 := mul_pos hν hr
  have f2 := mul_pos hν hu
  have f3 := mul_pos (mul_pos hν hu) (by linarith : (0:ℝ) < α1)
  have f4 := mul_pos (mul_pos hν hu) hβ1
  have f5 := mul_pos (mul_pos hν hu) (by linarith : (0:ℝ) < α1 + β1 - 1)
  have f6 := mul_pos (mul_pos hν hu) hα4
  have f7 := mul_pos (mul_pos hν hr) hγ4
  have f8 := mul_pos (mul_pos hβ6 hν) hr
  have f9 := mul_pos (mul_pos hβ6 hν) (by linarith : 0 < α4 * (σ * (ha * t1 - w1)) - -(σ * v1) * (1 - γ4))
  intro i j h1 h2'
  rcases c2z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases c2z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2' (by decide)).elim
    | (simp only [LT, ori, fo, cell2Rim, s0, s1, s2, s3, s4, s5, c2rim6_0, c2rim6_1, c2rim6_2, c2rim6_3, c2rim6_4, c2rim6_5]
       first
       | (left; linarith)
       | (right; refine ⟨by ring, by linarith⟩))

end Type08Sp
end Minimality
