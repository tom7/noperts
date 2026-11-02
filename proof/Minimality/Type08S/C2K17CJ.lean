module

public import Minimality.Type08S.C2K17CI

@[expose] public section


/-!
# K17C / P3J: the cell at `a - d` for `γ6 ≤ 1` with weights (S3.6a), and its feasibility predicate.
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- Values of `A = ⟪b-d, v⟫`, `B = ⟪c-d, v⟫` (with `qq = |b-d|²`, `qr = ⟪b-d,c-d⟫`, `rr = |c-d|²`) on the two generators
`r3 = (β6, γ6-1)`, `r4 = (max (1-β6) 0, -γ6)` of the tilt cone, and `G = (β6-1) A + γ6 B`. -/
def k17cA3 (β6 γ6 qq qr : ℝ) : ℝ := β6 * qq + (γ6 - 1) * qr
def k17cB3 (β6 γ6 qr rr : ℝ) : ℝ := β6 * qr + (γ6 - 1) * rr
def k17cG3 (β6 γ6 qq qr rr : ℝ) : ℝ := (β6 - 1) * k17cA3 β6 γ6 qq qr + γ6 * k17cB3 β6 γ6 qr rr
def k17cA4 (β6 γ6 qq qr : ℝ) : ℝ := max (1 - β6) 0 * qq - γ6 * qr
def k17cB4 (β6 γ6 qr rr : ℝ) : ℝ := max (1 - β6) 0 * qr - γ6 * rr
def k17cG4 (β6 γ6 qq qr rr : ℝ) : ℝ := (β6 - 1) * k17cA4 β6 γ6 qq qr + γ6 * k17cB4 β6 γ6 qr rr

/-- No tilt of the cone works: the S3.6a leftover. -/
def K17cBad (β6 γ6 qq qr rr : ℝ) : Prop :=
  k17cG3 β6 γ6 qq qr rr ≤ 0 ∧ k17cG4 β6 γ6 qq qr rr ≤ 0 ∧ 0 ≤ k17cA3 β6 γ6 qq qr ∧ 0 ≤ k17cA4 β6 γ6 qq qr

theorem k17c_c3 {β6 γ6 : ℝ} (hb6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 ≤ 1) (hs : 1 < β6 + γ6) :
    -β6 * γ6 + (1 - γ6) * max (1 - β6) 0 < 0 := by
  have h2 : max (1 - β6) 0 = 1 - β6 ∨ max (1 - β6) 0 = 0 := by
    rcases le_total (1 - β6) 0 with h | h
    · right; exact max_eq_right h
    · left; exact max_eq_left h
  rcases h2 with h | h
  · rw [h]; nlinarith
  · rw [h]; nlinarith [mul_pos hb6 hγ6]

set_option maxHeartbeats 1600000 in
theorem k17c_A_weights {a a' b b' c c' d : ℝ³} {α1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + (1 : ℝ) • (b - d)) (hb' : b' = d + α1 • (a - d) + (1 : ℝ) • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 ≤ α1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (h3 : 1 < β6 + γ6) (hγ61 : γ6 ≤ 1)
    (hM : K6sM a a' b b' c c' d) (hm0 : ⟪a - d, b - d⟫ = 0)
    {l1 m1 l2 m2 : ℝ} (hl1 : 0 ≤ l1) (hm1 : 0 ≤ m1) (hl2 : 0 ≤ l2) (hm2 : 0 ≤ m2)
    (hl : 0 < l1 + l2) (hm : 0 < m1 + m2) (hlm : l1 * m2 - m1 * l2 ≠ 0)
    (hmet : ∀ lam : ℝ, 0 < lam → lam < 1 →
      ((1 - lam) * l1 + lam * l2) * k17cA3 β6 γ6 ⟪b - d, b - d⟫ ⟪b - d, c - d⟫ +
        ((1 - lam) * m1 + lam * m2) * k17cA4 β6 γ6 ⟪b - d, b - d⟫ ⟪b - d, c - d⟫ ≤ 0 ∨
      0 ≤ ((1 - lam) * l1 + lam * l2) * k17cG3 β6 γ6 ⟪b - d, b - d⟫ ⟪b - d, c - d⟫ ⟪c - d, c - d⟫ +
        ((1 - lam) * m1 + lam * m2) * k17cG4 β6 γ6 ⟪b - d, b - d⟫ ⟪b - d, c - d⟫ ⟪c - d, c - d⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  have hc3 := k17c_c3 hβ6 hγ6 hγ61 h3
  set m4 := max (1 - β6) 0 with hm4
  refine k17c_A_cell hdet hc' hb' ha' hα1 hβ6 hγ6 h3 hM hm0
    (u1 := l1 * β6 + m1 * m4) (u2 := l1 * (γ6 - 1) - m1 * γ6)
    (t1 := (l2 - l1) * β6 + (m2 - m1) * m4) (t2 := (l2 - l1) * (γ6 - 1) - (m2 - m1) * γ6) ?_ ?_ ?_
  · intro h
    apply hlm
    have : (l1 * β6 + m1 * m4) * ((l2 - l1) * (γ6 - 1) - (m2 - m1) * γ6) -
        (l1 * (γ6 - 1) - m1 * γ6) * ((l2 - l1) * β6 + (m2 - m1) * m4) = (l1 * m2 - m1 * l2) * (-β6 * γ6 + (1 - γ6) * m4) := by ring
    rw [this] at h
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd h hc3.ne
  · intro lam h0 h1
    have hΛ : 0 < (1 - lam) * l1 + lam * l2 := by
      rcases hl1.eq_or_lt with e | e
      · have : 0 < l2 := by linarith
        nlinarith [mul_pos h0 this]
      · nlinarith [mul_pos (sub_pos.2 h1) e, mul_nonneg h0.le hl2]
    have hM' : 0 < (1 - lam) * m1 + lam * m2 := by
      rcases hm1.eq_or_lt with e | e
      · have : 0 < m2 := by linarith
        nlinarith [mul_pos h0 this]
      · nlinarith [mul_pos (sub_pos.2 h1) e, mul_nonneg h0.le hm2]
    have := k17c_cone_gen hβ6 hγ6 hγ61 h3 hΛ hM'
    have e1 : l1 * β6 + m1 * m4 + lam * ((l2 - l1) * β6 + (m2 - m1) * m4) =
        ((1 - lam) * l1 + lam * l2) * β6 + ((1 - lam) * m1 + lam * m2) * m4 := by ring
    have e2 : l1 * (γ6 - 1) - m1 * γ6 + lam * ((l2 - l1) * (γ6 - 1) - (m2 - m1) * γ6) =
        ((1 - lam) * l1 + lam * l2) * (γ6 - 1) - ((1 - lam) * m1 + lam * m2) * γ6 := by ring
    rw [e1, e2]
    exact this
  · intro lam h0 h1
    rcases hmet lam h0 h1 with h | h
    · left
      simp only [k17cA3, k17cA4] at h
      nlinarith [h]
    · right
      simp only [k17cG3, k17cG4, k17cA3, k17cA4, k17cB3, k17cB4] at h
      nlinarith [h]

end C2
end Type08Sp
end Minimality
