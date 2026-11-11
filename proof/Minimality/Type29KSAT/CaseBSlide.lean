module

public import Minimality.RightSlide
public import Minimality.Type29NF

@[expose] public section

/-!
# Type 29, class K2a on `Z1`, case B: the Slide Lemma leaf

* `Minimality.NF29.caseB_data`: the coordinate tables of the rectangle `1456`.
* `Minimality.NF29.isRupert_Z1_caseB_slide`: on `Z1` with the edge `14` orthogonal to the facet
  `015` (case B), the slab hypothesis at one end of the edge `15` gives Rupert.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset

namespace Minimality.NF29

variable {x : Fin 7 → ℝ³}

/-- **Case-B coordinates.**  On `Z1` with `x1 - x4` orthogonal to `x0 - x1` and `x0 - x5`:
`E₁ ⟂ E₂`, `⟪E₁, E₃⟫ = -⟪E₁, E₁⟫`, and with `ℓ = ⟪E₂, E₂⟫`, `k = ⟪E₁, E₁⟫`, `m = ⟪E₃, E₂⟫`, the
normal `W = m E₂ - ℓ E₁ - ℓ E₃` of the rectangle `1456` (`ω = -⟪E₃, W⟫ > 0`), the tables of
`⟪x i - x 1, E₂⟫`, `⟪x i - x 1, E₁⟫`, `⟪x i - x 1, W⟫`. -/
theorem caseB_data (N : NF29 x) (hZ : N.s = 1 ∧ N.t = 1 ∧ N.a0 + N.h0 = 0)
    (hB : ⟪x 1 - x 4, x 0 - x 1⟫ = 0 ∧ ⟪x 1 - x 4, x 0 - x 5⟫ = 0) :
    ∃ (ℓ k m ω : ℝ) (W : ℝ³), 0 < ℓ ∧ 0 < k ∧ 0 < ω ∧ W ≠ 0 ∧ N.E₁ ≠ 0 ∧ N.E₂ ≠ 0 ∧
      ⟪N.E₁, N.E₂⟫ = 0 ∧ ⟪N.E₂, W⟫ = 0 ∧ ⟪N.E₁, W⟫ = 0 ∧ ⟪N.E₂, N.E₂⟫ = ℓ ∧ ⟪N.E₁, N.E₁⟫ = k ∧
      (∀ i, ⟪x i - x 1, N.E₂⟫ = ![N.b0 * ℓ - N.h0 * m, 0, N.b2 * ℓ - N.h2 * m, -m, 0, ℓ, ℓ] i) ∧
      (∀ i, ⟪x i - x 1, N.E₁⟫ = ![0, 0, (N.a2 + N.h2) * k, k, k, 0, k] i) ∧
      (∀ i, ⟪x i - x 1, W⟫ = ![N.h0 * ω, 0, N.h2 * ω, ω, 0, 0, 0] i) := by
  obtain ⟨hs, ht, hz⟩ := hZ
  have ha0 : N.a0 = -N.h0 := by linarith
  set E1 := N.E₁ with hE1
  set E2 := N.E₂ with hE2
  set E3 := N.E₃ with hE3
  have c21 : ⟪E2, E1⟫ = ⟪E1, E2⟫ := real_inner_comm _ _
  have c31 : ⟪E3, E1⟫ = ⟪E1, E3⟫ := real_inner_comm _ _
  have c32 : ⟪E2, E3⟫ = ⟪E3, E2⟫ := real_inner_comm _ _
  obtain ⟨hB1, hB2⟩ := hB
  have v14 : x 1 - x 4 = -E1 := by rw [N.x1, N.x4]; simp only [nfP]; module
  have v01 : x 0 - x 1 = N.a0 • E1 + N.b0 • E2 + (-N.h0) • E3 := by
    rw [N.x0, N.x1]; simp only [nfP]; module
  have v05 : x 0 - x 5 = N.a0 • E1 + (N.b0 - 1) • E2 + (-N.h0) • E3 := by
    rw [N.x0, N.x5]; simp only [nfP]; module
  rw [v14, v01] at hB1
  rw [v14, v05] at hB2
  simp only [inner_neg_left, inner_add_right, real_inner_smul_right] at hB1 hB2
  have e12 : ⟪E1, E2⟫ = 0 := by linear_combination hB2 - hB1
  have e13 : ⟪E1, E3⟫ = -⟪E1, E1⟫ := by
    rw [e12, ha0] at hB1
    have : N.h0 * (⟪E1, E1⟫ + ⟪E1, E3⟫) = 0 := by linear_combination hB1
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h N.hh0.ne'
    · linarith
  have hne : ∀ i j : Fin 7, i ≠ j → x i ≠ x j := fun i j h e => h (N.inj e)
  have v41 : x 4 - x 1 = E1 := by rw [N.x4, N.x1]; simp only [nfP]; module
  have v51 : x 5 - x 1 = E2 := by rw [N.x5, N.x1]; simp only [nfP]; module
  have hE10 : E1 ≠ 0 := by
    rw [← v41]; exact sub_ne_zero.2 (hne 4 1 (by decide))
  have hE20 : E2 ≠ 0 := by
    rw [← v51]; exact sub_ne_zero.2 (hne 5 1 (by decide))
  set ℓ := ⟪E2, E2⟫ with hℓ
  set k := ⟪E1, E1⟫ with hk
  set m := ⟪E3, E2⟫ with hm
  set W : ℝ³ := m • E2 - ℓ • E1 - ℓ • E3 with hW
  set ω := ℓ * ⟪E3, E3⟫ - ℓ * k - m ^ 2 with hω
  have hℓ0 : 0 < ℓ := by rw [hℓ, real_inner_self_eq_norm_sq]; exact pow_pos (norm_pos_iff.2 hE20) 2
  have hk0 : 0 < k := by rw [hk, real_inner_self_eq_norm_sq]; exact pow_pos (norm_pos_iff.2 hE10) 2
  have w1 : ⟪E1, W⟫ = 0 := by
    simp only [hW, inner_sub_right, real_inner_smul_right, e12, e13]; ring
  have w2 : ⟪E2, W⟫ = 0 := by
    simp only [hW, inner_sub_right, real_inner_smul_right, c21, e12, c32]; ring
  have w3 : ⟪E3, W⟫ = -ω := by
    simp only [hW, inner_sub_right, real_inner_smul_right, c31, e13, hω]; ring
  have hW0 : W ≠ 0 := by
    intro h0
    have hj : ∀ j, m * E2 j - ℓ * E1 j - ℓ * E3 j = 0 := by
      intro j
      have := congrArg (fun v : ℝ³ => v j) h0
      simpa [hW] using this
    have hdet : ℓ * det3 E1 E2 E3 = 0 := by
      rw [det3_expand]
      linear_combination (-(E1 1 * E2 2 - E1 2 * E2 1)) * hj 0 -
        (E1 2 * E2 0 - E1 0 * E2 2) * hj 1 - (E1 0 * E2 1 - E1 1 * E2 0) * hj 2
    rcases mul_eq_zero.1 hdet with h | h
    · exact hℓ0.ne' h
    · exact N.hD h
  have hω0 : 0 < ω := by
    have hWW : ⟪W, W⟫ = ℓ * ω := by
      have h := (show ⟪m • E2 - ℓ • E1 - ℓ • E3, W⟫ = ℓ * ω by
        simp only [inner_sub_left, real_inner_smul_left, w1, w2, w3]; ring)
      exact h
    have : 0 < ⟪W, W⟫ := by
      rw [real_inner_self_eq_norm_sq]; exact pow_pos (norm_pos_iff.2 hW0) 2
    rw [hWW] at this
    exact (mul_pos_iff_of_pos_left hℓ0).1 this
  refine ⟨ℓ, k, m, ω, W, hℓ0, hk0, hω0, hW0, hE10, hE20, e12, w2, w1, rfl, rfl, ?_, ?_, ?_⟩ <;>
  · intro i
    fin_cases i <;>
    · simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, N.x0, N.x1, N.x2, N.x3,
        N.x4, N.x5, N.x6, nfP_sub, inner_nfV, hs, ht, ha0, ← hE1, ← hE2, ← hE3]
      simp only [c21, c31, e12, e13, w1, w2, w3, ← hℓ, ← hk, ← hm, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val]
      ring

set_option hygiene false in
/-- Closer for the per-vertex obligations of the four walls (uses the local names `k2`, `h2`). -/
macro "cb_close" : tactic => `(tactic| first
  | linarith
  | exact ⟨by linarith, by linarith⟩
  | (have := k2 (by linarith); linarith)
  | (rcases h2 with h | h <;> linarith))

/-- **Type 29 on `Z1`, case B, by the Slide Lemma.**  A type 29 normal form on the stratum `Z1`
(`s = t = 1`, `a0 + h0 = 0`: the quad `1456` a parallelogram, the facets `015` and `346` parallel)
in which the edge `x1 - x4` is orthogonal to the facet `015` (both inner products zero: case B, so
`1456` is a rectangle orthogonal to both facets) is Rupert as soon as the deep vertices `0, 2, 3`
all lie strictly beyond the plane through `x1` orthogonal to the edge `15`, or all strictly before
the plane through `x5` orthogonal to it.  (K) holds at the wall `015` (edge `15`) or at the wall
`346` (edge `46`) by `kdich`; all of it is `Slide.slide_walls` with the walls `015` (deep vertex `0`)
and `346` (deep vertex `3`).  No class hypothesis (`a2`, `b0`, `V`) is used. -/
theorem isRupert_Z1_caseB_slide (N : NF29 x) (hZ : N.s = 1 ∧ N.t = 1 ∧ N.a0 + N.h0 = 0)
    (hB : ⟪x 1 - x 4, x 0 - x 1⟫ = 0 ∧ ⟪x 1 - x 4, x 0 - x 5⟫ = 0)
    (hSl : (∀ p ∈ ({0, 2, 3} : Finset (Fin 7)), 0 < ⟪x p - x 1, x 5 - x 1⟫) ∨
      (∀ q ∈ ({0, 2, 3} : Finset (Fin 7)), 0 < ⟪x q - x 5, x 1 - x 5⟫)) :
    IsRupert (univ.image x) := by
  obtain ⟨ℓ, k, m, ω, W, hℓ, hk, hω, hW0, hE10, hE20, e12, w2, w1, eℓ, ek, tX, tG, tY⟩ :=
    caseB_data N hZ hB
  obtain ⟨hs, ht, hz⟩ := hZ
  have hh0 := N.hh0
  have hh2 := N.hh2
  have h2a : 0 < N.a2 + N.h2 := by
    have hF5 := N.hF5
    have : 0 < N.h0 * (N.a2 + N.h2) := by
      have ha0 : N.a0 = -N.h0 := by linarith
      rw [ha0] at hF5; linarith
    exact (mul_pos_iff_of_pos_left hh0).1 this
  have h2b : N.a2 + N.h2 < 1 := by
    have d234 := N.d234
    rw [hs, ht] at d234; linarith
  have q0 : 0 < N.h0 * ω := mul_pos hh0 hω
  have q2 : 0 < N.h2 * ω := mul_pos hh2 hω
  have q3 : 0 < (N.a2 + N.h2) * k := mul_pos h2a hk
  have q4 : (N.a2 + N.h2) * k < k := by nlinarith
  have hsh : ∀ i a : Fin 7, ∀ v : ℝ³, ⟪x i - x a, v⟫ = ⟪x i - x 1, v⟫ - ⟪x a - x 1, v⟫ := by
    intro i a v; rw [← inner_sub_left]; congr 1; abel
  have v41 : x 4 - x 1 = N.E₁ := by rw [N.x4, N.x1]; simp only [nfP]; module
  have v51 : x 5 - x 1 = N.E₂ := by rw [N.x5, N.x1]; simp only [nfP]; module
  have v61 : x 6 - x 1 = N.E₂ + N.E₁ := by rw [N.x6, N.x1, hs, ht]; simp only [nfP]; module
  have v14 : x 1 - x 4 = -N.E₁ := by rw [N.x1, N.x4]; simp only [nfP]; module
  have v15 : x 1 - x 5 = -N.E₂ := by rw [N.x1, N.x5]; simp only [nfP]; module
  have e21 : ⟪N.E₂, N.E₁⟫ = 0 := by rw [real_inner_comm]; exact e12
  have nk : ‖N.E₁‖ ^ 2 = k := by rw [← real_inner_self_eq_norm_sq]; exact ek
  refine Minimality.Split.Slide.slide_walls x 1 5 4 6 0 3 N.E₂ N.E₁ W (fun i => ⟪x i - x 1, N.E₂⟫)
    (fun i => ⟪x i - x 1, W⟫) (fun i => ⟪x i - x 1, N.E₁⟫) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) v51 v41 v61 hE20 hE10 hW0 e21 w2 w1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i h1 h2 h3 h4; fin_cases i <;> simp [tY] at h1 h2 h3 h4 ⊢ <;> cb_close
  · intro i; fin_cases i <;> simp [tG, nk] <;> cb_close
  · simp [tY]; cb_close
  · simp [tG]
  · intro i h1 h2; fin_cases i <;> simp [tY, tG] at h1 h2 ⊢ <;> cb_close
  · simp [tY]; cb_close
  · simp [tG, nk]
  · intro i h1 h2; fin_cases i <;> simp [tY, tG, nk] at h1 h2 ⊢ <;> cb_close
  · rcases hSl with hP | hM
    · left
      have P0 := hP 0 (by simp)
      have P2 := hP 2 (by simp)
      have P3 := hP 3 (by simp)
      rw [v51, tX] at P0 P2 P3
      simp only [Matrix.cons_val] at P0 P2 P3
      intro i hi; fin_cases i <;> simp [tX, tY] at hi ⊢ <;> cb_close
    · right
      have M0 := hM 0 (by simp)
      have M2 := hM 2 (by simp)
      have M3 := hM 3 (by simp)
      rw [hsh _ 5, v15, v51, inner_neg_right, inner_neg_right, tX, eℓ] at M0 M2 M3
      simp only [Matrix.cons_val] at M0 M2 M3
      rw [eℓ]
      intro i hi; fin_cases i <;> simp [tX, tY] at hi ⊢ <;> cb_close

/-- **The `σ`-image** (`σ = (0 2)(4 5)`, class K2b on `σ(Z1)`): on `t = 1 ∧ s = 1 ∧ b2 + h2 = 0`
with `x1 - x5` orthogonal to `x2 - x1` and `x2 - x4` (the facet `124`), the slab at one end of the
edge `14` gives Rupert. -/
theorem isRupert_sZ1_caseB_slide (N : NF29 x) (hZ : N.t = 1 ∧ N.s = 1 ∧ N.b2 + N.h2 = 0)
    (hB : ⟪x 1 - x 5, x 2 - x 1⟫ = 0 ∧ ⟪x 1 - x 5, x 2 - x 4⟫ = 0)
    (hSl : (∀ p ∈ ({0, 2, 3} : Finset (Fin 7)), 0 < ⟪x p - x 1, x 4 - x 1⟫) ∨
      (∀ q ∈ ({0, 2, 3} : Finset (Fin 7)), 0 < ⟪x q - x 4, x 1 - x 4⟫)) :
    IsRupert (univ.image x) := by
  have key : ∀ (P : Fin 7 → Prop), (∀ p ∈ ({0, 2, 3} : Finset (Fin 7)), P p) →
      ∀ p ∈ ({0, 2, 3} : Finset (Fin 7)), P (sigma29 p) := by
    intro P h p hp
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact h 2 (by decide)
    · exact h 0 (by decide)
    · exact h 3 (by decide)
  have := N.sigma.isRupert_Z1_caseB_slide (by exact hZ) (by exact hB) (by
    rcases hSl with h | h
    · exact Or.inl (key (fun p => 0 < ⟪x p - x 1, x 4 - x 1⟫) h)
    · exact Or.inr (key (fun p => 0 < ⟪x p - x 4, x 1 - x 4⟫) h))
  rwa [image_sigma29] at this

end Minimality.NF29

#print axioms Minimality.NF29.isRupert_Z1_caseB_slide
#print axioms Minimality.NF29.isRupert_sZ1_caseB_slide
