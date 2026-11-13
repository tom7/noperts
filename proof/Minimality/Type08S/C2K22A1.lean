module

public import Minimality.Type08S.C2K21ZA

@[expose] public section

/-!
# K22A1 / A1: the whole `β1 = 1` piece of the M boundary (`K17cLeft`, all three disjuncts) is Rupert.

At `β1 = 1` the Gram relation gives `p = a - d ⟂ q = b - d, r = c - d` (`k17c_m_zero`, `k17c_gram`), so
`c' = d + q + α1 p`, `b' = d + r + α1 p`, `a = d + p`, and `a' = d + β6 q + γ6 r` lies in the base plane beyond `bc`
(`β6 + γ6 > 1`): a right prism over `(d,b,c)` along `p` (heights `1, α1, α1`) with `a'` beyond `bc`, i.e. `k20_prism3`.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- The `β1 = 1` frame with `pq = pr = 0` is Rupert (any `α1 > 0`, any `β6, γ6` with `β6 + γ6 > 1`). -/
theorem k22a1_core {a a' b b' c c' d : ℝ³} {α1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + (1 : ℝ) • (b - d)) (hb' : b' = d + α1 • (a - d) + (1 : ℝ) • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d)) (hα1 : 0 < α1) (h3 : 1 < β6 + γ6)
    (hpq : ⟪a - d, b - d⟫ = 0) (hpr : ⟪a - d, c - d⟫ = 0) :
    IsRupert (V8 a a' b b' c c' d) := by
  set P := a - d with hP
  set Q := b - d with hQ
  set R := c - d with hR
  have key := k20_prism3 d P Q R (β := β6) (γ := γ6) (z0 := 1) (z1 := α1) (z2 := α1) hpq hpr
    (by intro h0; apply hdet; rw [← h0]; simp only [det3_expand]; ring) one_pos hα1 hα1 h3
  have q1 : d + Q = b := by simp [Q]
  have q2 : d + R = c := by simp [R]
  have q3 : d + (β6 • Q + γ6 • R) = a' := by rw [ha', add_assoc]
  have q4 : d + (1 : ℝ) • P = a := by simp [P]
  have q5 : d + Q + α1 • P = c' := by rw [hc']; module
  have q6 : d + R + α1 • P = b' := by rw [hb']; module
  rw [q5, q6, q3, q4, q1, q2] at key
  convert key using 1
  ext x; simp only [V8, Finset.mem_insert, Finset.mem_singleton]; tauto

/-- **`β1 = 1` in `K6sMN2`**: Rupert. -/
theorem k22a1_n2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hs : K6sMN2 a a' b b' c c' d) {α1 β1 β6 γ6 : ℝ} (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6)
    (h : β1 = 1) : IsRupert (V8 a a' b b' c c' d) := by
  obtain ⟨hdet, hc', hb', ha', hα1', hβ1', h1, hβ6', hγ6', h3⟩ := hC
  subst h
  have hrel := k17c_n2_rel W hs.1 hs.2.1 hs.2.2.1 hdet hc' ha' hγ6' h3
  have hm0 := k17c_m_zero hα1' hrel
  have hpr := (k17c_gram hdet hc' hb' hs.2.2 hm0).1
  exact k22a1_core hdet hc' hb' ha' hα1' h3 hm0 hpr

/-- **`β1 = 1` in `K6sMKb`**: Rupert. -/
theorem k22a1_kb {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hs : K6sMKb a a' b b' c c' d) {α1 β1 β6 γ6 : ℝ} (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6)
    (h : β1 = 1) : IsRupert (V8 a a' b b' c c' d) := by
  obtain ⟨hdet, hc', hb', ha', hα1', hβ1', h1, hβ6', hγ6', h3⟩ := hC
  subst h
  have hrel := k17c_kb_rel W hs.1 hs.2.1 hs.2.2.1 hdet hb'
  have hm0 := k17c_m_zero hα1' hrel
  have hpr := (k17c_gram hdet hc' hb' hs.2.2 hm0).1
  exact k22a1_core hdet hc' hb' ha' hα1' h3 hm0 hpr

/-- `K17mBoundary` without its `β1 = 1` disjunct (all of `K17cLeft` is Rupert). -/
def K22mBoundary (reg : Prop) (a a' b c c' d : ℝ³) (α1 β1 β6 γ6 : ℝ) : Prop :=
  (1 < β1 ∧ β6 + γ6 = β1) ∨
    (1 < β1 ∧ β1 < β6 + γ6 ∧ α1 = 1 ∧ ¬ reg ∧ (0 ≤ ⟪a - d, b - d⟫ ∨ (β6 ≤ 1 ∧ γ6 ≤ 1))) ∨
    (1 < β1 ∧ β1 < β6 + γ6 ∧ 1 < α1 ∧ (β6 = 1 ∨ γ6 = 1))

/-- Cut `K17mBoundary` given that its `β1 = 1` disjunct is Rupert. -/
theorem k22a1_boundary_cut {reg : Prop} {a a' b c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ} {X : Prop}
    (hX : β1 = 1 → X) (h : K17mBoundary reg a a' b c c' d α1 β1 β6 γ6) :
    X ∨ K22mBoundary reg a a' b c c' d α1 β1 β6 γ6 := by
  rcases h with h | h | h | h
  · exact Or.inl (hX h.1)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

end C2
end Type08Sp
end Minimality
