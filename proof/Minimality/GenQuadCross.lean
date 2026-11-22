module

public import Minimality.GenQuad

@[expose] public section

/-!
# Coplanar crossing at the lex level (R6)

Two crossing segments `p q`, `r s` (`CrossOf`) never carry a weak lex double peak, whenever the depth
triples `(⟪y,b⟫, ⟪y,d1⟫, ⟪y,d2⟫)` separate `p` from `r` (true if `b, d1, d2` is a basis).
-/

set_option autoImplicit false

open scoped RealInnerProductSpace
open Minimality Minimality.LexCell Minimality.H21

namespace Minimality.GenQuad

/-- Open segments `p q` and `r s` cross. -/
def CrossOf (p q r s : ℝ³) : Prop :=
  ∃ lam mu : ℝ, 0 < lam ∧ lam < 1 ∧ 0 < mu ∧ mu < 1 ∧ lam • p + (1 - lam) • q = mu • r + (1 - mu) • s

theorem crossOf_symm {p q r s : ℝ³} (h : CrossOf p q r s) : CrossOf r s p q := by
  obtain ⟨l, m, a, b, c, d, e⟩ := h
  exact ⟨m, l, c, d, a, b, e.symm⟩

/-- A convex crossing with `p, q ≤ r, s` forces all four equal. -/
theorem eq_of_cross_le {lam mu p q r s : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) (hm0 : 0 < mu) (hm1 : mu < 1)
    (e : lam * p + (1 - lam) * q = mu * r + (1 - mu) * s)
    (h1 : p ≤ r) (h2 : p ≤ s) (h3 : q ≤ r) (h4 : q ≤ s) :
    p = r ∧ p = s ∧ q = r ∧ q = s := by
  have a1 : 0 ≤ lam * mu * (r - p) := by have := sub_nonneg.2 h1; positivity
  have a2 : 0 ≤ lam * (1 - mu) * (s - p) := by
    have := sub_nonneg.2 h2; have : 0 < 1 - mu := by linarith
    positivity
  have a3 : 0 ≤ (1 - lam) * mu * (r - q) := by
    have := sub_nonneg.2 h3; have : 0 < 1 - lam := by linarith
    positivity
  have a4 : 0 ≤ (1 - lam) * (1 - mu) * (s - q) := by
    have := sub_nonneg.2 h4; have : 0 < 1 - lam := by linarith
    have : 0 < 1 - mu := by linarith
    positivity
  have hs : lam * mu * (r - p) + lam * (1 - mu) * (s - p) + (1 - lam) * mu * (r - q) +
      (1 - lam) * (1 - mu) * (s - q) = 0 := by linear_combination -e
  have z1 : lam * mu * (r - p) = 0 := by linarith
  have z2 : lam * (1 - mu) * (s - p) = 0 := by linarith
  have z3 : (1 - lam) * mu * (r - q) = 0 := by linarith
  have z4 : (1 - lam) * (1 - mu) * (s - q) = 0 := by linarith
  have pos1 : lam * mu ≠ 0 := by positivity
  have pos2 : lam * (1 - mu) ≠ 0 := by
    have : 0 < 1 - mu := by linarith
    positivity
  have pos3 : (1 - lam) * mu ≠ 0 := by
    have : 0 < 1 - lam := by linarith
    positivity
  have pos4 : (1 - lam) * (1 - mu) ≠ 0 := by
    have : 0 < 1 - lam := by linarith
    have : 0 < 1 - mu := by linarith
    positivity
  have := (mul_eq_zero.1 z1).resolve_left pos1
  have := (mul_eq_zero.1 z2).resolve_left pos2
  have := (mul_eq_zero.1 z3).resolve_left pos3
  have := (mul_eq_zero.1 z4).resolve_left pos4
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem neg_lexPos3 {A B C : ℝ} (h : ¬ LexPos3 A B C) :
    A ≤ 0 ∧ (A = 0 → B ≤ 0) ∧ (A = 0 → B = 0 → C ≤ 0) := by
  unfold LexPos3 at h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun hA => (h2 hA).1, fun hA hB => (h2 hA).2 hB⟩

/-- Depth triples are injective when `b, d1, d2` are linearly independent. -/
theorem depth_injective {b d1 d2 y : ℝ³} (hdet : Split.det3 b d1 d2 ≠ 0)
    (h0 : ⟪y, b⟫ = 0) (h1 : ⟪y, d1⟫ = 0) (h2 : ⟪y, d2⟫ = 0) : y = 0 := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three] at h0 h1 h2
  simp only [star_trivial] at h0 h1 h2
  have key : ∀ i, Split.det3 b d1 d2 * y i = 0 := by
    intro i
    simp only [Split.det3]
    fin_cases i
    · simp only [Fin.zero_eta]
      linear_combination
        (d1 1 * d2 2 - d1 2 * d2 1) * h0 + (d2 1 * b 2 - d2 2 * b 1) * h1 + (b 1 * d1 2 - b 2 * d1 1) * h2
    · simp only [Fin.mk_one]
      linear_combination
        (d1 2 * d2 0 - d1 0 * d2 2) * h0 + (d2 2 * b 0 - d2 0 * b 2) * h1 + (b 2 * d1 0 - b 0 * d1 2) * h2
    · simp only [Fin.reduceFinMk]
      linear_combination
        (d1 0 * d2 1 - d1 1 * d2 0) * h0 + (d2 0 * b 1 - d2 1 * b 0) * h1 + (b 0 * d1 1 - b 1 * d1 0) * h2
  ext i
  exact (mul_eq_zero.1 (key i)).resolve_left hdet

/-- Core: a crossing cannot carry a weak lex double peak `p, q ≤ r, s` unless `p` and `r` have equal depth triples. -/
theorem crossOf_lexClause_aux {p q r s b d1 d2 : ℝ³} (h : CrossOf p q r s)
    (hdet : Split.det3 b d1 d2 ≠ 0) (hpr : p ≠ r) : LexClause p q r s b d1 d2 := by
  by_contra hn
  unfold LexClause LexLt3 at hn
  simp only [not_or] at hn
  obtain ⟨l, m, hl0, hl1, hm0, hm1, e⟩ := h
  obtain ⟨n1, n2, n3, n4⟩ := hn
  have comp : ∀ f : ℝ³ → ℝ, (∀ x y : ℝ³, f (x + y) = f x + f y) → (∀ (c : ℝ) (x : ℝ³), f (c • x) = c * f x) →
      l * f p + (1 - l) * f q = m * f r + (1 - m) * f s := by
    intro f ha hs
    have := congrArg f e
    simpa only [ha, hs] using this
  have cb := comp (fun y => ⟪y, b⟫) (fun x y => inner_add_left x y b) (fun c x => by simp [inner_smul_left])
  have c1 := comp (fun y => ⟪y, d1⟫) (fun x y => inner_add_left x y d1) (fun c x => by simp [inner_smul_left])
  have c2 := comp (fun y => ⟪y, d2⟫) (fun x y => inner_add_left x y d2) (fun c x => by simp [inner_smul_left])
  obtain ⟨a1, a2, a3⟩ := neg_lexPos3 n1
  obtain ⟨b1, b2, b3⟩ := neg_lexPos3 n2
  obtain ⟨c1', c2', c3'⟩ := neg_lexPos3 n3
  obtain ⟨d1', d2', d3'⟩ := neg_lexPos3 n4
  obtain ⟨E1, E2, E3, E4⟩ := eq_of_cross_le hl0 hl1 hm0 hm1 cb (by linarith) (by linarith) (by linarith) (by linarith)
  have z1 : ⟪p, b⟫ - ⟪r, b⟫ = 0 := by linarith
  have z2 : ⟪p, b⟫ - ⟪s, b⟫ = 0 := by linarith
  have z3 : ⟪q, b⟫ - ⟪r, b⟫ = 0 := by linarith
  have z4 : ⟪q, b⟫ - ⟪s, b⟫ = 0 := by linarith
  obtain ⟨F1, F2, F3, F4⟩ := eq_of_cross_le hl0 hl1 hm0 hm1 c1 (by linarith [a2 z1]) (by linarith [b2 z2])
    (by linarith [c2' z3]) (by linarith [d2' z4])
  obtain ⟨G1, G2, G3, G4⟩ := eq_of_cross_le hl0 hl1 hm0 hm1 c2
    (by linarith [a3 z1 (by linarith [a2 z1, F1])]) (by linarith [b3 z2 (by linarith [b2 z2, F2])])
    (by linarith [c3' z3 (by linarith [c2' z3, F3])]) (by linarith [d3' z4 (by linarith [d2' z4, F4])])
  apply hpr
  have : p - r = 0 := depth_injective (b := b) (d1 := d1) (d2 := d2) hdet
    (by rw [inner_sub_left]; linarith) (by rw [inner_sub_left]; linarith) (by rw [inner_sub_left]; linarith)
  exact sub_eq_zero.1 this

/-- **R6.** Crossing segments give both clauses of the quadruple, provided the depth map separates `p` from `r`
(`b, d1, d2` linearly independent). Only `p ≠ r` is needed (not pairwise distinctness). -/
theorem lexClause_of_crossOf {p q r s b d1 d2 : ℝ³} (h : CrossOf p q r s)
    (hdet : Split.det3 b d1 d2 ≠ 0) (hpr : p ≠ r) :
    LexClause p q r s b d1 d2 ∧ LexClause r s p q b d1 d2 :=
  ⟨crossOf_lexClause_aux h hdet hpr, crossOf_lexClause_aux (crossOf_symm h) hdet hpr.symm⟩

end Minimality.GenQuad
