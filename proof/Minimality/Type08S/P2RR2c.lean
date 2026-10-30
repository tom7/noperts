module

public import Minimality.Type08S.P2RR2b
public import Minimality.Type08S.P2RKExport
public import Minimality.Type08S.P2RR0

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkR / R2c: `lexCell_N2WS` (cell `(+,+,+)`, cycle `(d, a, c', b', c)`).
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace R2

theorem pair_ne {z1 z2 w1 w2 : ℝ} (h : z1 = z2 → w1 ≠ w2) : (z1, w1) ≠ (z2, w2) :=
  fun e => h (congrArg Prod.fst e) (congrArg Prod.snd e)

theorem inner_pt_v {e1 e2 e3 : ℝ³} (hF : Fr e1 e2 e3) (o : ℝ³) (X Y z t1 t2 t3 : ℝ) :
    ⟪pt e1 e2 e3 o X Y z, pc e1 e2 e3 t1 t2 t3⟫ = ⟪o, pc e1 e2 e3 t1 t2 t3⟫ + X * t1 + Y * t2 + z * t3 := by
  simp only [pt, inner_add_left]
  rw [inner_pc hF]; ring

/-- Coordinates of the five depths and the arithmetic of N2's weak far triple. -/
theorem arith_N2 {ν w3 C0 α1 α4 β1 γ4 : ℝ} (hν : 0 < ν) (hα : 1 < α1) (hα4 : 0 < α4) (hγ4 : 0 < γ4)
    (hβ1 : 0 < β1) (hE : 0 < α4 - α4 * β1 - α1 * (1 - γ4)) (hz1 : ν = α1 * w3 + β1 * ν)
    (hz2 : ν = α4 * w3 + γ4 * C0) :
    w3 < ν ∧ C0 < ν ∧ (0 < w3 ∨ 0 < C0) := by
  have hw : α1 * w3 = ν * (1 - β1) := by linarith
  have h1 : w3 < ν := by nlinarith
  have h2 : C0 < ν := by
    have k : α1 * (α4 * w3 - ν * (1 - γ4)) = ν * (α4 * (1 - β1) - α1 * (1 - γ4)) := by
      linear_combination α4 * hw
    have k2 : 0 < α1 * (α4 * w3 - ν * (1 - γ4)) := by
      rw [k]; apply mul_pos hν; linarith
    have k3 : 0 < α4 * w3 - ν * (1 - γ4) := pos_of_mul_pos_right k2 (by linarith)
    by_contra hcon
    push_neg at hcon
    nlinarith
  refine ⟨h1, h2, ?_⟩
  by_cases hb : β1 < 1
  · left
    have : 0 < α1 * w3 := by rw [hw]; apply mul_pos hν; linarith
    exact pos_of_mul_pos_right this (by linarith)
  · right
    push_neg at hb
    have : α1 * w3 ≤ 0 := by rw [hw]; nlinarith
    have hw0 : w3 ≤ 0 := by nlinarith
    have : 0 < γ4 * C0 := by nlinarith
    exact pos_of_mul_pos_right this hγ4.le

end R2
end Type08Sp
end Minimality
