module

public import Minimality.Type08S.C2FA2

@[expose] public section

/-!
# C2 / FB1: a tilt on a segment of the screen separates every depth tie of a frame cycle

`exists_sep_tilt`: for a cycle `X` of distinct frame points and tilts `v_λ = fcomb (u1 + λ t1) (u2 + λ t2) 0`
(`u1 t2 - u2 t1 ≠ 0`), all but finitely many `λ` make the lex pairs `(⟪x, r⟫, ⟪x, v_λ⟫)` injective on the cycle:
two points with equal depth differ by `X ≠ 0` with `X ⊥ r`, so `(⟪X,p⟫, ⟪X,q⟫) ≠ 0` and `⟪X, v_λ⟫` is a nonzero
affine function of `λ`.
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem fcomb3_ne_zero (p q r : ℝ³) (hΔ : det3 p q r ≠ 0) {t : ℝ × ℝ × ℝ} (ht : t ≠ 0) :
    fcomb p q r t.1 t.2.1 t.2.2 ≠ 0 := by
  intro h0
  have e1 : fcomb p q r 0 1 0 = q := by simp [fcomb]
  have e2 : fcomb p q r 0 0 1 = r := by simp [fcomb]
  have e3 : fcomb p q r 1 0 0 = p := by simp [fcomb]
  have h1 := det3_coord p q r t.1 t.2.1 t.2.2 0 1 0 0 0 1
  have h2 := det3_coord p q r 1 0 0 t.1 t.2.1 t.2.2 0 0 1
  have h3 := det3_coord p q r 1 0 0 0 1 0 t.1 t.2.1 t.2.2
  rw [h0, e1, e2, det3_zero_left'] at h1
  rw [h0, e2, e3, det3_zero_mid] at h2
  rw [h0, e1, e3] at h3
  have h3' : det3 p q 0 = 0 := by simp [det3_expand]
  rw [h3'] at h3
  simp only [d3] at h1 h2 h3
  have hx : t.1 = 0 := (mul_eq_zero.mp (by linarith : det3 p q r * t.1 = 0)).resolve_left hΔ
  have hy : t.2.1 = 0 := (mul_eq_zero.mp (by linarith : det3 p q r * t.2.1 = 0)).resolve_left hΔ
  have hz : t.2.2 = 0 := (mul_eq_zero.mp (by linarith : det3 p q r * t.2.2 = 0)).resolve_left hΔ
  exact ht (Prod.ext hx (Prod.ext hy hz))

/-- One tie: the bad `λ` form a finite set. -/
theorem finite_bad_sep (p q r : ℝ³) (hΔ : det3 p q r ≠ 0) {u1 u2 t1 t2 : ℝ} (hut : u1 * t2 - u2 * t1 ≠ 0)
    {t : ℝ × ℝ × ℝ} (ht : t ≠ 0) :
    {lam : ℝ | ⟪fcomb p q r t.1 t.2.1 t.2.2, r⟫ = 0 ∧
      ⟪fcomb p q r t.1 t.2.1 t.2.2, fcomb p q r (u1 + lam * t1) (u2 + lam * t2) 0⟫ = 0}.Finite := by
  set X := fcomb p q r t.1 t.2.1 t.2.2 with hX
  have hX0 : X ≠ 0 := fcomb3_ne_zero p q r hΔ ht
  by_cases hr : ⟪X, r⟫ = 0
  · set P := ⟪X, p⟫
    set Qv := ⟪X, q⟫
    have hexp : ∀ lam, ⟪X, fcomb p q r (u1 + lam * t1) (u2 + lam * t2) 0⟫ =
        (u1 * P + u2 * Qv) + lam * (t1 * P + t2 * Qv) := by
      intro lam
      simp only [fcomb, inner_add_right, real_inner_smul_right, P, Qv]; ring
    have hPQ : ¬ (P = 0 ∧ Qv = 0) := by
      rintro ⟨h1, h2⟩
      apply hX0
      have : ⟪X, X⟫ = 0 := by
        have h := inner_fcomb_left p q r X t.1 t.2.1 t.2.2
        rw [← hX] at h
        rw [h, real_inner_comm X p, real_inner_comm X q, real_inner_comm X r]
        simp only [P, Qv] at h1 h2
        rw [h1, h2, hr]; ring
      exact inner_self_eq_zero.mp this
    by_cases hB : t1 * P + t2 * Qv = 0
    · -- then u1 P + u2 Q ≠ 0, the bad set is empty
      have hA : u1 * P + u2 * Qv ≠ 0 := by
        intro hA; apply hPQ
        constructor
        · have : (u1 * t2 - u2 * t1) * P = 0 := by linear_combination t2 * hA - u2 * hB
          exact (mul_eq_zero.mp this).resolve_left hut
        · have : (u1 * t2 - u2 * t1) * Qv = 0 := by linear_combination u1 * hB - t1 * hA
          exact (mul_eq_zero.mp this).resolve_left hut
      convert Set.finite_empty
      ext lam
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _ h; rw [hexp, hB, mul_zero, add_zero] at h; exact hA h
    · refine (Set.finite_singleton (-(u1 * P + u2 * Qv) / (t1 * P + t2 * Qv))).subset ?_
      intro lam hl
      simp only [Set.mem_ofPred_eq, hexp] at hl
      simp only [Set.mem_singleton_iff]
      rw [eq_div_iff hB]
      linarith [hl.2]
  · convert Set.finite_empty
    ext lam
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro h; exact absurd h hr

/-- **Toolkit.**  A tilt `v_λ`, `λ ∈ (lo, hi)`, that separates every depth tie of the cycle `X` (distinct frame
points) in lex order. -/
theorem exists_sep_tilt (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0) {k : ℕ} [NeZero k] (X : ZMod k → ℝ × ℝ × ℝ)
    (hX : ∀ i j, X i = X j → i = j) {u1 u2 t1 t2 : ℝ} (hut : u1 * t2 - u2 * t1 ≠ 0) {lo hi : ℝ} (hlh : lo < hi) :
    ∃ lam : ℝ, lo < lam ∧ lam < hi ∧ ∀ i j,
      ⟪fpoint p q r d (X i), r⟫ = ⟪fpoint p q r d (X j), r⟫ →
      ⟪fpoint p q r d (X i), fcomb p q r (u1 + lam * t1) (u2 + lam * t2) 0⟫ =
        ⟪fpoint p q r d (X j), fcomb p q r (u1 + lam * t1) (u2 + lam * t2) 0⟫ → i = j := by
  classical
  set S : Finset (ℝ × ℝ × ℝ) := ((Finset.univ : Finset (ZMod k × ZMod k)).image
    (fun ij => X ij.1 - X ij.2)).filter (· ≠ 0) with hS
  have hfin : (⋃ t ∈ S, {lam : ℝ | ⟪fcomb p q r t.1 t.2.1 t.2.2, r⟫ = 0 ∧
      ⟪fcomb p q r t.1 t.2.1 t.2.2, fcomb p q r (u1 + lam * t1) (u2 + lam * t2) 0⟫ = 0}).Finite :=
    Set.Finite.biUnion S.finite_toSet fun t ht =>
      finite_bad_sep p q r hΔ hut (Finset.mem_filter.mp ht).2
  obtain ⟨lam, hl, hn⟩ := ((Set.Ioo_infinite hlh).sdiff hfin).nonempty
  refine ⟨lam, hl.1, hl.2, fun i j hz hw => ?_⟩
  by_contra hij
  have hne : X i - X j ≠ 0 := fun h => hij (hX i j (sub_eq_zero.mp h))
  apply hn
  simp only [Set.mem_iUnion]
  refine ⟨X i - X j, ?_, ?_, ?_⟩
  · rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩, hne⟩
  · rw [← fpoint_sub, inner_sub_left, hz, sub_self]
  · rw [← fpoint_sub, inner_sub_left, hw, sub_self]

end C2
end Type08Sp
end Minimality
