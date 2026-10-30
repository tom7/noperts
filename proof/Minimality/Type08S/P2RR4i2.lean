module

public import Minimality.Type08S.P2RR4i1

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkR / R4a / R4i2: reversing a cycle (orientation `Δ < 0`) and choosing the tilt.
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

theorem tsc_rev (Δ : ℝ) (P Q F v : ℝ × ℝ × ℝ) (h : TSc (-Δ) (P - Q) (F - Q) v) :
    TSc Δ (Q - P) (F - P) v := by
  have e0 : Δ * d3 (Q - P).1 (Q - P).2.1 (Q - P).2.2 (F - P).1 (F - P).2.1 (F - P).2.2 0 0 1 =
      (-Δ) * d3 (P - Q).1 (P - Q).2.1 (P - Q).2.2 (F - Q).1 (F - Q).2.1 (F - Q).2.2 0 0 1 := by
    simp only [d3, Prod.fst_sub, Prod.snd_sub]; ring
  have e1 : Δ * d3 (Q - P).1 (Q - P).2.1 (Q - P).2.2 (F - P).1 (F - P).2.1 (F - P).2.2 v.1 v.2.1 v.2.2 =
      (-Δ) * d3 (P - Q).1 (P - Q).2.1 (P - Q).2.2 (F - Q).1 (F - Q).2.1 (F - Q).2.2 v.1 v.2.1 v.2.2 := by
    simp only [d3, Prod.fst_sub, Prod.snd_sub]; ring
  unfold TSc at h ⊢
  rw [e0, e1]; exact h

theorem hcyc_rev {k : ℕ} [NeZero k] {X : ZMod k → ℝ × ℝ × ℝ} {Δ : ℝ} {v : ℝ × ℝ × ℝ}
    (h : ∀ i j, j ≠ i → j ≠ i + 1 → TSc (-Δ) (X (i + 1) - X i) (X j - X i) v) :
    ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 →
      TSc Δ ((fun i => X (-i)) (i + 1) - (fun i => X (-i)) i) ((fun i => X (-i)) j - (fun i => X (-i)) i) v := by
  intro i j h1 h2
  apply tsc_rev
  have := h (-i - 1) (-j) (by intro e; apply h2; have := neg_injective (e.trans (by ring : -i - 1 = -(i + 1))); exact this)
    (by intro e; apply h1; have : -j = -i := by rw [e]; ring
        exact neg_injective this)
  rw [sub_add_cancel] at this
  beta_reduce
  rw [show -(i + 1) = -i - 1 by ring]
  exact this

theorem hrest_rev {k : ℕ} [NeZero k] {X : ZMod k → ℝ × ℝ × ℝ} {Δ : ℝ} {v t : ℝ × ℝ × ℝ}
    (h : ∀ i, TSc (-Δ) (X (i + 1) - X i) (t - X i) v) :
    ∀ i : ZMod k, TSc Δ ((fun i => X (-i)) (i + 1) - (fun i => X (-i)) i) (t - (fun i => X (-i)) i) v := by
  intro i
  apply tsc_rev
  have := h (-i - 1)
  rw [sub_add_cancel] at this
  beta_reduce
  rw [show -(i + 1) = -i - 1 by ring]
  exact this

/-- A tilt `(-1, μ, 0)` with `μ > 0` and `⟪p, v⟫ ≠ 0` (`p ⊥ r`, `Δ ≠ 0`). -/
theorem exists_mu (p q r : ℝ³) (hΔ : det3 p q r ≠ 0) (hpr : ⟪p, r⟫ = 0) :
    ∃ μ : ℝ, 0 < μ ∧ ⟪p, fcomb p q r (-1) μ 0⟫ ≠ 0 := by
  have hp : p ≠ 0 := by
    rintro rfl; apply hΔ; simp [det3_expand]
  have hpp : 0 < ⟪p, p⟫ := real_inner_self_pos.2 hp
  have key : ∀ μ, ⟪p, fcomb p q r (-1) μ 0⟫ = -⟪p, p⟫ + μ * ⟪p, q⟫ := by
    intro μ; simp only [fcomb, inner_add_right, real_inner_smul_right, hpr]; ring
  by_cases h1 : ⟪p, fcomb p q r (-1) 1 0⟫ = 0
  · refine ⟨2, by norm_num, ?_⟩
    rw [key] at h1 ⊢
    intro h2; linarith
  · exact ⟨1, one_pos, h1⟩

end Type08Sp
end Minimality
