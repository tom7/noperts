module

public import Minimality.Type08S.P2QQ1a

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkQ / Q1b: `exists_seq_strict`, `exists_seq_strict_T4cl` (statements as in PQ0).
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- Strict generic approximants of a closure point (direction `e₃ - e₅`, then a generic box). -/
theorem exists_seq_strict (θ : Fin 6 → ℝ) (hθ : Ineq08w θ) :
    ∃ θs : ℕ → Fin 6 → ℝ, Tendsto θs atTop (𝓝 θ) ∧ (∀ᶠ n in atTop, ∀ k, 0 < ineq08 (θs n) k) ∧
      ∀ n, MvPolynomial.eval (θs n) genPoly08 ≠ 0 := by
  have h0 : 0 < θ 0 := by simpa [ineq08] using hθ.1 0 (by decide) (by decide) (by decide)
  have h1 : 0 < θ 1 := by simpa [ineq08] using hθ.1 1 (by decide) (by decide) (by decide)
  obtain ⟨θs, h, -, h2, h3⟩ := seq_core θ hθ ![0, 0, 0, 1, 0, -1] (θ 0) (θ 1) h0 h1
    (fun t ht _ => by
      have := hθ.2.1
      rw [gWa_eq] at this ⊢
      simp
      nlinarith)
    (fun t ht _ => by
      have := hθ.2.2
      rw [gWb_eq] at this ⊢
      simp
      nlinarith)
  exact ⟨θs, h, h2, h3⟩

/-- Strict generic approximants on the T4 side of a point of the T4 closure (direction `e₀ + e₃ - e₅`). -/
theorem exists_seq_strict_T4cl (θ : Fin 6 → ℝ) (hθ : Ineq08w θ) (h0 : 1 ≤ θ 0) (h5 : θ 5 ≤ 1) :
    ∃ θs : ℕ → Fin 6 → ℝ, Tendsto θs atTop (𝓝 θ) ∧ (∀ᶠ n in atTop, ∀ k, 0 < ineq08 (θs n) k) ∧
      (∀ n, MvPolynomial.eval (θs n) genPoly08 ≠ 0) ∧ ∀ n, θs n 5 < 1 ∧ 1 < θs n 0 := by
  have h1 : 0 < θ 1 := by simpa [ineq08] using hθ.1 1 (by decide) (by decide) (by decide)
  have h3 : 0 < θ 3 := by simpa [ineq08] using hθ.1 3 (by decide) (by decide) (by decide)
  have h4 : 0 < θ 4 := by simpa [ineq08] using hθ.1 4 (by decide) (by decide) (by decide)
  obtain ⟨θs, h, hb, h2, hg⟩ := seq_core θ hθ ![1, 0, 0, 1, 0, -1] (θ 3) (θ 1) h3 h1
    (fun t ht _ => by
      have := hθ.2.1
      rw [gWa_eq] at this ⊢
      simp
      nlinarith)
    (fun t ht _ => by
      have := hθ.2.2
      rw [gWb_eq] at this ⊢
      simp
      nlinarith)
  refine ⟨θs, h, h2, hg, fun n => ?_⟩
  have t0 : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have t1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have e5 := abs_lt.mp (hb n 5)
  have e0 := abs_lt.mp (hb n 0)
  simp at e5 e0
  have tt : ((((n : ℝ) + 1)) ^ 2)⁻¹ ≤ ((n : ℝ) + 1)⁻¹ := by
    have : ((n : ℝ) + 1)⁻¹ ^ 2 ≤ ((n : ℝ) + 1)⁻¹ := by
      have := t1; rw [one_div] at this t0; nlinarith
    simpa [inv_pow] using this
  constructor <;> linarith [e5.1, e5.2, e0.1, e0.2]

end Type08Sp
end Minimality
