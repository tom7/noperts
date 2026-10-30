module

public import Minimality.Type08S.P2RKT1

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkR / K2 / KT2: choosing the tilt off finitely many bad values (frame `p, q, r`).
`exists_tilt_avoid`: for pairs `(x, y) ≠ 0`, the inner product `⟪x p + y q, -λ p - q⟫` vanishes for finitely
many `λ`; so some `λ` in any open interval avoids all of them.
-/
set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

theorem fcomb_ne_zero (p q r : ℝ³) (hΔ : det3 p q r ≠ 0) {x y : ℝ} (h : (x, y) ≠ ((0 : ℝ), (0 : ℝ))) :
    fcomb p q r x y 0 ≠ 0 := by
  intro h0
  have e1 : fcomb p q r 0 1 0 = q := by simp [fcomb]
  have e2 : fcomb p q r 0 0 1 = r := by simp [fcomb]
  have e3 : fcomb p q r 1 0 0 = p := by simp [fcomb]
  have h1 := det3_coord p q r x y 0 0 1 0 0 0 1
  have h3 := det3_coord p q r 1 0 0 x y 0 0 0 1
  rw [h0, e1, e2, det3_zero_left'] at h1
  rw [h0, e2, e3, det3_zero_mid] at h3
  simp only [d3] at h1 h3
  have hx : x = 0 := by
    have : det3 p q r * x = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hΔ
  have hy : y = 0 := by
    have : det3 p q r * y = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hΔ
  exact h (by rw [hx, hy])

/-- The bad tilts of one pair form a finite set. -/
theorem finite_bad_tilt (p q r : ℝ³) (hΔ : det3 p q r ≠ 0) {x y : ℝ} (h : (x, y) ≠ ((0 : ℝ), (0 : ℝ))) :
    {lam : ℝ | ⟪fcomb p q r x y 0, fcomb p q r (-lam) (-1) 0⟫ = 0}.Finite := by
  set X := fcomb p q r x y 0 with hX
  have hX0 := fcomb_ne_zero p q r hΔ h
  have hexp : ∀ lam, ⟪X, fcomb p q r (-lam) (-1) 0⟫ = -lam * ⟪X, p⟫ - ⟪X, q⟫ := by
    intro lam
    simp only [fcomb, inner_add_right, real_inner_smul_right]; ring
  by_cases ht : ⟪X, p⟫ = 0
  · by_cases hs : ⟪X, q⟫ = 0
    · exfalso
      apply hX0
      have : ⟪X, X⟫ = 0 := by
        have h2 := inner_fcomb_left p q r X x y 0
        rw [← hX] at h2
        rw [h2, real_inner_comm X p, real_inner_comm X q, ht, hs]; ring
      exact inner_self_eq_zero.mp this
    · convert Set.finite_empty
      ext lam
      simp [hexp, ht, hs]
  · refine (Set.finite_singleton (-⟪X, q⟫ / ⟪X, p⟫)).subset ?_
    intro lam hl
    simp only [Set.mem_ofPred_eq, hexp] at hl
    simp only [Set.mem_singleton_iff]
    field_simp
    linarith

/-- **Toolkit.**  Some tilt parameter `λ ∈ (lo, hi)` avoids the bad values of every pair in the list. -/
theorem exists_tilt_avoid (p q r : ℝ³) (hΔ : det3 p q r ≠ 0) {lo hi : ℝ} (hlh : lo < hi)
    (L : List (ℝ × ℝ)) (hL : ∀ t ∈ L, t ≠ ((0 : ℝ), (0 : ℝ))) :
    ∃ lam : ℝ, lo < lam ∧ lam < hi ∧
      ∀ t ∈ L, ⟪fcomb p q r t.1 t.2 0, fcomb p q r (-lam) (-1) 0⟫ ≠ 0 := by
  have hfin : (⋃ t ∈ L.toFinset, {lam : ℝ | ⟪fcomb p q r t.1 t.2 0, fcomb p q r (-lam) (-1) 0⟫ = 0}).Finite :=
    Set.Finite.biUnion L.toFinset.finite_toSet fun t ht =>
      finite_bad_tilt p q r hΔ (hL t (List.mem_toFinset.mp ht))
  obtain ⟨lam, hl, hn⟩ := ((Set.Ioo_infinite hlh).sdiff hfin).nonempty
  refine ⟨lam, hl.1, hl.2, fun t ht h0 => hn ?_⟩
  simp only [Set.mem_iUnion]
  exact ⟨t, List.mem_toFinset.mpr ht, h0⟩

end Type08Sp
end Minimality
