module

public import Minimality.Type08S.C2K21ZA
public import Minimality.Type08S.C2K20E
public import Minimality.Type08S.C2K19G
public import Minimality.Type08S.C2K18A

@[expose] public section


open scoped RealInnerProductSpace Topology
open Finset Filter
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

namespace Minimality
namespace Type08Sp
namespace C2

/-- Leftover of C1: right prismatoid (`pq = pr = 0`) with `¬(β1 = 1 ∧ γ4 = 1)`. -/
def K22C1Left (a a' b b' c c' d : ℝ³) : Prop :=
  ⟪a - d, b - d⟫ = 0 ∧ ⟪a - d, c - d⟫ = 0 ∧
  ∃ β1 γ4 γ6 : ℝ, det3 (a - d) (b - d) (c - d) ≠ 0 ∧
    c' = d + (1 : ℝ) • (a - d) + β1 • (b - d) ∧ b' = d + (1 : ℝ) • (a - d) + γ4 • (c - d) ∧
    a' = d + (1 : ℝ) • (b - d) + γ6 • (c - d) ∧ 0 < β1 ∧ 0 < γ4 ∧ 0 < γ6 ∧ γ6 < 1 ∧ (β1 ≠ 1 ∨ γ4 ≠ 1)

theorem k22c1_close {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (h : K6t3LeftPc a a' b b' c c' d)
    (hC1 : ⟪a - d, a - c'⟫ = 0 ∧ (⟪b - d, c - d⟫ = 0 ∨ ⟪b' - c, d - b⟫ = 0 ∨ ⟪b' - c', d - b⟫ = 0)) :
    HasLexCell (V8 a a' b b' c c' d) ∨ IsRupert (V8 a a' b b' c c' d) ∨ K22C1Left a a' b b' c c' d := by
  obtain ⟨h5, hu, hw⟩ := h
  obtain ⟨β1, γ4, γ6, hdet, hc', hb', ha', hβ1, hγ4, hγ6, hγ61, -⟩ := k17gc_pc_frame W h5
  set P := a - d with hP
  set Q := b - d with hQ
  set R := c - d with hR
  have ea : a = d + P := by simp [P]
  have eb : b = d + Q := by simp [Q]
  have ec : c = d + R := by simp [R]
  have hpq : ⟪P, Q⟫ = 0 := by
    have h1 : a - c' = -(β1 • Q) := by rw [hc', ea]; module
    have h2 := hC1.1
    rw [show a - c' = -(β1 • Q) by rw [hc', ea]; module] at h2
    simp only [inner_neg_right, real_inner_smul_right] at h2
    rcases mul_eq_zero.1 (neg_eq_zero.1 h2) with h | h
    · linarith
    · exact h
  have hpr : ⟪P, R⟫ = 0 := by
    have e : c - a' = (1 - γ6) • R - Q := by rw [ha', ec]; module
    have hqp : ⟪Q, P⟫ = 0 := by rw [real_inner_comm]; exact hpq
    rw [e, inner_sub_left, real_inner_smul_left, hqp] at hu
    simp only [sub_zero] at hu
    rcases mul_eq_zero.1 hu with h | h
    · linarith
    · rw [real_inner_comm]; exact h
  by_cases hb : β1 = 1 ∧ γ4 = 1
  · obtain ⟨rfl, rfl⟩ := hb
    right; left
    have key := k20_prism3 d P Q R (β := 1) (γ := γ6) (z0 := 1) (z1 := 1) (z2 := 1) hpq hpr
      (by intro h0; apply hdet; rw [← h0]; simp only [det3_expand]; ring) one_pos one_pos one_pos
      (by linarith)
    have q3 : d + ((1 : ℝ) • Q + γ6 • R) = a' := by rw [ha', add_assoc]
    have q5 : d + Q + (1 : ℝ) • P = c' := by rw [hc']; module
    have q6 : d + R + (1 : ℝ) • P = b' := by rw [hb']; module
    have q4 : d + (1 : ℝ) • P = a := by simp [P]
    have q1 : d + Q = b := by simp [Q]
    have q2 : d + R = c := by simp [R]
    rw [q5, q6, q3, q4, q1, q2] at key
    convert key using 1
    ext x; simp only [V8, Finset.mem_insert, Finset.mem_singleton]; tauto
  · right; right
    refine ⟨hpq, hpr, β1, γ4, γ6, hdet, hc', hb', ha', hβ1, hγ4, hγ6, hγ61, ?_⟩
    by_contra hn; push Not at hn; exact hb hn

end C2
end Type08Sp
end Minimality
