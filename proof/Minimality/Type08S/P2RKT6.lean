module

public import Minimality.Type08S.P2RKT5

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkR / K2 / KT6: the face cell in frame coordinates (`HasLexCellAt`).
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- Tilt parameter and distinctness of the four lex values. -/
theorem face_tilt (p q r : ℝ³) (hΔ : det3 p q r ≠ 0) {α γ : ℝ} (hα : 1 < α) (hγ : 0 < γ) :
    ∃ lam : ℝ, 0 < lam ∧ lam * γ < α - 1 ∧
      ⟪p, fcomb p q r (-lam) (-1) 0⟫ ≠ 0 ∧ ⟪q, fcomb p q r (-lam) (-1) 0⟫ ≠ 0 ∧
      ⟪p, fcomb p q r (-lam) (-1) 0⟫ ≠ ⟪q, fcomb p q r (-lam) (-1) 0⟫ ∧
      α * ⟪p, fcomb p q r (-lam) (-1) 0⟫ + γ * ⟪q, fcomb p q r (-lam) (-1) 0⟫ ≠ 0 ∧
      α * ⟪p, fcomb p q r (-lam) (-1) 0⟫ + γ * ⟪q, fcomb p q r (-lam) (-1) 0⟫ ≠
        ⟪p, fcomb p q r (-lam) (-1) 0⟫ ∧
      α * ⟪p, fcomb p q r (-lam) (-1) 0⟫ + γ * ⟪q, fcomb p q r (-lam) (-1) 0⟫ ≠
        ⟪q, fcomb p q r (-lam) (-1) 0⟫ := by
  have hlh : (0 : ℝ) < (α - 1) / γ := div_pos (by linarith) hγ
  obtain ⟨lam, h0, h1, hav⟩ := exists_tilt_avoid p q r hΔ hlh
    [(1, 0), (0, 1), (1, -1), (α, γ), (α - 1, γ), (α, γ - 1)]
    (by
      intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [Prod.ext_iff] <;> intro h <;> linarith)
  refine ⟨lam, h0, ?_, ?_⟩
  · rw [lt_div_iff₀ hγ] at h1; linarith
  have e : ∀ x y : ℝ, ⟪fcomb p q r x y 0, fcomb p q r (-lam) (-1) 0⟫ =
      x * ⟪p, fcomb p q r (-lam) (-1) 0⟫ + y * ⟪q, fcomb p q r (-lam) (-1) 0⟫ := by
    intro x y; rw [inner_fcomb_left]; ring
  have n1 := hav (1, 0) (by simp)
  have n2 := hav (0, 1) (by simp)
  have n3 := hav (1, -1) (by simp)
  have n4 := hav (α, γ) (by simp)
  have n5 := hav (α - 1, γ) (by simp)
  have n6 := hav (α, γ - 1) (by simp)
  simp only [e] at n1 n2 n3 n4 n5 n6
  refine ⟨by intro h; apply n1; linarith, by intro h; apply n2; linarith,
    by intro h; apply n3; linarith, by intro h; apply n4; linarith,
    by intro h; apply n5; linarith, by intro h; apply n6; linarith⟩

end Type08Sp
end Minimality
