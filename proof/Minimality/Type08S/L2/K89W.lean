module

public import Minimality.Type08S.L2.K89A
public import Minimality.Type08S.L2.K89B
public import Minimality.Type08S.L2.K87LexwA
public import Minimality.Type08S.L2.K87LexwB
public import Minimality.Type08S.L2.K89C

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace
namespace Minimality.Type08Sp.C2

/-- **Type 08 wall combiner** (`α1 = β1`).  Hypotheses are the `k83_reduce` output plus `gWb`
and the wall `α1 = β1`.  Named numerics-only facts (not proved here, sympy/exact sampling only):
`hbg : β6 = γ6` (K67SYM: on the corner `gWb = zab = zba = 0`, `β6 = γ6 = β1/(β1+1-α1)`);
`fA, fB, fC`: the depth/Gram facts of the three branches of `Lam = ⟪c-d,b-a⟫`
(K87WSPEC sec. 2-4, charts F1 (m,k), F3 (u,t); `fC`: the curve `L = 0` has
`Gram = μ((1+u)I - uJ)`, `u = (t-1)/(2t)`, `1 < t ≤ 5/3`, `e = (t+1)/(3-t)`; K85CRV). -/
theorem k89_wall {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (h1 : 1 < α1) (hgWb : β6 * (α1 - 1) = β1 * (γ6 - 1)) (hwall : α1 = β1) (hbg : β6 = γ6)
    (fA : 0 < ⟪c - d, b - a⟫ → 0 < ⟪c - d, a' - d⟫ ∧ 0 < ⟪c - d, b' - d⟫ ∧
      ⟪a' - d, k89_RA a' b' c d⟫ < 0 ∧ 0 < ⟪b' - d, k89_RA a' b' c d⟫ ∧ ⟪c' - d, k89_RA a' b' c d⟫ < 0)
    (fB : ⟪c - d, b - a⟫ < 0 → 0 < ⟪b - d, b - a⟫ ∧ ⟪c - d, k89_RB a b c d⟫ < 0 ∧ 0 < ⟪b' - d, k89_RB a b c d⟫)
    (fC : ⟪c - d, b - a⟫ = 0 → ∃ t μ : ℝ, 1 < t ∧ t ≤ 5/3 ∧ 0 < μ ∧
      ⟪a - d, a - d⟫ = μ ∧ ⟪b - d, b - d⟫ = μ ∧ ⟪c - d, c - d⟫ = μ ∧
      ⟪a - d, b - d⟫ = -μ * ((t-1)/(2*t)) ∧ ⟪a - d, c - d⟫ = -μ * ((t-1)/(2*t)) ∧
      ⟪b - d, c - d⟫ = -μ * ((t-1)/(2*t)) ∧ α1 = (t+1)/(3-t)) :
    HasLexCell (V8 a a' b b' c c' d) ∨ IsRupert (V8 a a' b b' c c' d) := by
  have hs : β6 = α1 := by
    subst hwall; rw [← hbg] at hgWb; linear_combination (-1 : ℝ) * hgWb
  obtain rfl : β1 = α1 := hwall.symm
  obtain rfl : β6 = β1 := hs
  obtain rfl : γ6 = β6 := hbg.symm
  rcases lt_trichotomy (⟪c - d, b - a⟫) 0 with hl | hl | hl
  · obtain ⟨hq, hs1, hz1⟩ := fB hl
    exact Or.inl (k87_wB hC hM h1 hl hq hs1 hz1)
  · obtain ⟨t, μ, ht1, ht2, hμ, hpp, hqq, hrr, hpq, hpr, hqr, he⟩ := fC hl
    obtain ⟨hdet, hc', hb', ha', -⟩ := hC
    rw [he] at hc' hb' ha'
    exact Or.inr (k89_curve ht1 ht2 hμ hdet hpp hqq hrr hpq hpr hqr hc' hb' ha')
  · obtain ⟨hk, hla, d1, d2, d3⟩ := fA hl
    exact Or.inl (k87_wA hC hM h1 hl hk hla d1 d2 d3)
end Minimality.Type08Sp.C2
