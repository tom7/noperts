module

public import Minimality.CornerStar

/-!
# Lemma SO (same orthant)

A closed-cell test whose failure patterns are all refuted on an open orthant `O_ε` of covectors
`l = G d` certifies every solid of the shape whose covector at the closure view lies in `O_ε`.
No obtuseness, no positive definiteness beyond the frame itself.
-/

@[expose] public section

open Finset
open scoped RealInnerProductSpace

namespace Minimality
namespace CornerSnap

/-- Shape-only certificate for the orthant `ε`: `lam ≥ 0`, `mu ≥ 0`, `mu ≠ 0` and
`Σ lam_i W_i = − Σ_a mu_a ε_a e_a` (so `Σ lam_i ⟨W_i, l⟩ = − Σ mu_a ε_a l_a < 0` on `O_ε`). -/
def OrthantCert {κ : Type*} [Fintype κ] (W : κ → Fin 3 → ℝ) (ε : Fin 3 → ℝ) (lam : κ → ℝ)
    (mu : Fin 3 → ℝ) : Prop :=
  (∀ i, 0 ≤ lam i) ∧ (∀ a, 0 ≤ mu a) ∧ mu ≠ 0 ∧ ∀ j, ∑ i, lam i * W i j = -(mu j * ε j)

/-- If `ε_a l_a > 0` for all `a` and the rows have an `OrthantCert`, some row `⟨W_i, l⟩` is
negative.  The covector `l` is arbitrary here. -/
theorem exists_neg_of_orthantCert {κ : Type*} [Fintype κ] {W : κ → Fin 3 → ℝ} {ε : Fin 3 → ℝ}
    {lam : κ → ℝ} {mu : Fin 3 → ℝ} (h : OrthantCert W ε lam mu) {l : Fin 3 → ℝ}
    (hl : ∀ a, 0 < ε a * l a) : ∃ i, W i 0 * l 0 + W i 1 * l 1 + W i 2 * l 2 < 0 := by
  obtain ⟨hlam, hmu, hne, heq⟩ := h
  by_contra hcon
  push Not at hcon
  have hsum : 0 ≤ ∑ i, lam i * (W i 0 * l 0 + W i 1 * l 1 + W i 2 * l 2) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hlam i) (hcon i)
  have key : ∑ i, lam i * (W i 0 * l 0 + W i 1 * l 1 + W i 2 * l 2) =
      (∑ i, lam i * W i 0) * l 0 + (∑ i, lam i * W i 1) * l 1 + (∑ i, lam i * W i 2) * l 2 := by
    simp only [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [key, heq 0, heq 1, heq 2] at hsum
  obtain ⟨a, ha⟩ : ∃ a, mu a ≠ 0 := by
    by_contra hh; push Not at hh; exact hne (funext hh)
  have hpos : 0 < mu a := lt_of_le_of_ne (hmu a) (Ne.symm ha)
  have p0 := mul_nonneg (hmu 0) (hl 0).le
  have p1 := mul_nonneg (hmu 1) (hl 1).le
  have p2 := mul_nonneg (hmu 2) (hl 2).le
  have pa := mul_pos hpos (hl a)
  have : 0 < mu 0 * (ε 0 * l 0) + mu 1 * (ε 1 * l 1) + mu 2 * (ε 2 * l 2) := by
    fin_cases a <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] at pa <;>
      linarith
  nlinarith

section Leaves
open Minimality.H21

variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}

/-- **Lemma SO (same orthant).**  A closed-cell test (rim length `≥ 4`) at the frame-fixed view
`d₀` whose failure patterns all have an `OrthantCert` for `ε` certifies every solid of the shape
whose covector `G d₀ = (cov d₀ a)_a` has `ε_a (G d₀)_a > 0`.  Neither obtuseness nor linear
independence of the frame is used. -/
theorem isRupert_corner_orthant {k : ℕ} [NeZero k] (hk : 4 ≤ k) (F : S0xFac m S x)
    (hx : Function.Injective x) {c : ZMod k → Fin n} (hc : Function.Injective c)
    {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn) {a : ℝ³} (ha : CellAt F U Dn a)
    {C : Corner (Fin n)} (hC : C.Rep x) (d₀ : Fin 3 → ℝ) (hu : CellLe F U Dn (C.view d₀))
    (ε : Fin 3 → ℝ) (hε : ∀ a, 0 < ε a * C.cov d₀ a)
    (hcert : ∀ (B : ZMod k) (b₁ b₂ b₃ : ℕ), 0 < b₁ → b₁ < b₂ → b₂ < b₃ → b₃ < k →
      ∃ (lam : Fin 4 → ℝ) (mu : Fin 3 → ℝ),
        OrthantCert (fun j => C.xdiff (c (patternPairs B b₁ b₂ b₃ j).1)
          (c (patternPairs B b₁ b₂ b₃ j).2)) ε lam mu) :
    IsRupert (univ.image x) := by
  refine isRupert_of_closedCell hk F hx hc hcyc ha hu (robUni_of_rows hC c d₀ ?_)
  intro B b₁ b₂ b₃ h1 h2 h3 h4
  obtain ⟨lam, mu, h⟩ := hcert B b₁ b₂ b₃ h1 h2 h3 h4
  obtain ⟨i, hi⟩ := exists_neg_of_orthantCert h hε
  exact ⟨i, by rwa [C.formRow_eq_cov]⟩

end Leaves

end CornerSnap
end Minimality
