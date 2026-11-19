module

public import Mathlib

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Matrix Finset

namespace Minimality.LemmaWT

lemma dotProduct_three (v w : Fin 3 → ℝ) :
    v ⬝ᵥ w = v 0 * w 0 + v 1 * w 1 + v 2 * w 2 := by
  simp [dotProduct, Fin.sum_univ_three]

lemma mulVec_three (M : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 3 → ℝ) (i : Fin 3) :
    (M *ᵥ v) i = M i 0 * v 0 + M i 1 * v 1 + M i 2 * v 2 := by
  change (fun j => M i j) ⬝ᵥ v = _
  rw [dotProduct_three]

lemma form1_eval (G : Matrix (Fin 3) (Fin 3) ℝ) (hG : G.IsSymm) (θ γ : ℝ) :
    ![1, -1, 0] ⬝ᵥ G *ᵥ ![θ, 1 - θ - γ, γ] =
      G 0 0 * θ + G 0 1 * (1 - θ - γ) + G 0 2 * γ -
      (G 0 1 * θ + G 1 1 * (1 - θ - γ) + G 1 2 * γ) := by
  rw [dotProduct_three]
  rw [mulVec_three G _ 0, mulVec_three G _ 1, mulVec_three G _ 2]
  have h10 : G 1 0 = G 0 1 := hG.apply 0 1
  rw [h10]
  simp; ring

lemma form2_eval (G : Matrix (Fin 3) (Fin 3) ℝ) (hG : G.IsSymm) (a3 b3 c3 p : ℝ) :
    ![a3, b3 - 1, c3] ⬝ᵥ G *ᵥ ![p, 1 - p, 0] =
      a3 * (G 0 0 * p + G 0 1 * (1 - p)) +
      (b3 - 1) * (G 0 1 * p + G 1 1 * (1 - p)) +
      c3 * (G 0 2 * p + G 1 2 * (1 - p)) := by
  rw [dotProduct_three]
  rw [mulVec_three G _ 0, mulVec_three G _ 1, mulVec_three G _ 2]
  have h10 : G 1 0 = G 0 1 := hG.apply 0 1
  have h20 : G 2 0 = G 0 2 := hG.apply 0 2
  have h21 : G 2 1 = G 1 2 := hG.apply 1 2
  rw [h10, h20, h21]
  simp

lemma identity_s1 (G00 G01 G02 G11 G12 t0 t1 t2 θ γ : ℝ) :
    t2 * (G00 * θ + G01 * (1 - θ - γ) + G02 * γ - (G01 * θ + G11 * (1 - θ - γ) + G12 * γ)) =
      (t2 - γ) * (G01 - G11) + (θ * t2 - γ * t0) * (G00 + G11 - 2 * G01) +
      γ * ((G00 * t0 + G01 * t1 + G02 * t2) - (G01 * t0 + G11 * t1 + G12 * t2)) +
      γ * (G11 - G01) * (t0 + t1 + t2 - 1) := by
  ring

lemma identity_s2 (G00 G01 G02 G11 G12 h2 t0 t1 t2 a3 b3 c3 θ γ p : ℝ)
    (heq0 : G00 * t0 + G01 * t1 + G02 * t2 = h2)
    (heq1 : G01 * t0 + G11 * t1 + G12 * t2 = h2)
    (heq_sum : t0 + t1 + t2 = 1)
    (heq_θ : θ * (a3 + b3 + c3 - 1) = a3) :
    θ * (t1 * ((c3 * t0 - a3 * t2) * p *
        (G00 * θ + G01 * (1 - θ - γ) + G02 * γ - (G01 * θ + G11 * (1 - θ - γ) + G12 * γ)) +
        (θ * t2 - γ * t0) * (a3 * (G00 * p + G01 * (1 - p)) + (b3 - 1) * (G01 * p + G11 * (1 - p)) + c3 * (G02 * p + G12 * (1 - p))))) =
      - h2 * (p * (c3 * θ - a3 * γ) * (t0 - θ) + θ * (1 - b3) * (θ * t2 - γ * t0)) +
      G01 * ((t0 + t1) * p * (t0 - θ) * (c3 * θ - a3 * γ) + θ * (θ * t2 - γ * t0) * (a3 * t1 + (1 - b3) * t0)) +
      G12 * θ * ((c3 * t0 - a3 * t2) * p * (t2 * (1 - θ - γ) - t1 * γ) + (θ * t2 - γ * t0) * (1 - p) * ((1 - b3) * t2 + c3 * t1)) := by
  let A : ℝ := -p * t1 * θ * (a3 * γ - c3 * θ)
  let B : ℝ := θ * (-a3 * γ * p * t2 - a3 * p * t2 * θ + a3 * p * t2 + b3 * γ * p * t0 - b3 * γ * t0 - b3 * p * t2 * θ + b3 * t2 * θ + c3 * γ * p * t0 + c3 * p * t0 * θ - c3 * p * t0 - γ * p * t0 + γ * t0 + p * t2 * θ - t2 * θ)
  let C : ℝ := p * θ * (a3 * γ - c3 * θ) * (G01 * t0 + G01 * t1 - h2)
  let D : ℝ := -p * (γ * t0 - t2 * θ) * (G01 * t0 + G01 * t1 - h2)
  linear_combination
    A * heq0 +
    B * heq1 +
    C * heq_sum +
    D * heq_θ

lemma t2_beta_sub_t1_gamma_pos (t0 t1 t2 θ γ : ℝ)
    (hts : t0 + t1 + t2 = 1) (hta : θ < t0) (htc : γ < t2) (hθγ : θ + γ < 1) (hγ : 0 < γ) :
    0 < t2 * (1 - θ - γ) - t1 * γ := by
  have h1 : t1 = 1 - t0 - t2 := by linarith
  have h_diff : t2 * (1 - θ - γ) - t1 * γ = (t2 - γ) * (1 - θ - γ) + γ * ((t0 - θ) + (t2 - γ)) := by
    rw [h1]; ring
  rw [h_diff]
  have p1 : 0 < (t2 - γ) * (1 - θ - γ) := mul_pos (by linarith) (by linarith)
  have p2 : 0 < γ * ((t0 - θ) + (t2 - γ)) := mul_pos hγ (by linarith)
  linarith

lemma rhs_theta_neg (G01 G12 h2 t0 t1 t2 a3 b3 c3 θ γ ω al_t al_T β p : ℝ)
    (hh2 : 0 < h2) (hab : G01 ≤ 0) (hbc : G12 ≤ 0)
    (hb3 : b3 < 1) (ha3 : 0 < a3) (hc3 : 0 < c3) (hθ0 : 0 < θ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hta : θ < t0)
    (htp0 : 0 < t0) (htp1 : 0 < t1) (htp2 : 0 < t2)
    (hal : 0 ≤ al_t) (halT : 0 ≤ al_T) (h_omega : 0 < ω)
    (h_pos_bracket : 0 < t2 * β - t1 * γ) :
    - h2 * (p * al_T * (t0 - θ) + θ * (1 - b3) * ω) +
    G01 * ((t0 + t1) * p * (t0 - θ) * al_T + θ * ω * (a3 * t1 + (1 - b3) * t0)) +
    G12 * θ * (al_t * p * (t2 * β - t1 * γ) + ω * (1 - p) * ((1 - b3) * t2 + c3 * t1)) < 0 := by
  have ht0_sub_θ : 0 ≤ t0 - θ := by linarith
  have h1_sub_b3 : 0 < 1 - b3 := by linarith
  have h1_sub_p : 0 ≤ 1 - p := by linarith
  have h_t01 : 0 ≤ t0 + t1 := by linarith

  have hK1_1 : 0 ≤ p * al_T * (t0 - θ) := by
    apply mul_nonneg (mul_nonneg hp0 halT) ht0_sub_θ
  have hK1_2 : 0 < θ * (1 - b3) * ω := by
    apply mul_pos (mul_pos hθ0 h1_sub_b3) h_omega
  have hK1 : 0 < p * al_T * (t0 - θ) + θ * (1 - b3) * ω := by linarith
  have hT1 : - h2 * (p * al_T * (t0 - θ) + θ * (1 - b3) * ω) < 0 := by
    have h_neg : -h2 < 0 := by linarith
    exact mul_neg_of_neg_of_pos h_neg hK1

  have hK2_1 : 0 ≤ (t0 + t1) * p * (t0 - θ) * al_T := by
    apply mul_nonneg (mul_nonneg (mul_nonneg h_t01 hp0) ht0_sub_θ) halT
  have hK2_2a : 0 ≤ a3 * t1 + (1 - b3) * t0 := by
    have p_a3 : 0 ≤ a3 * t1 := by positivity
    have p_b3 : 0 ≤ (1 - b3) * t0 := by positivity
    linarith
  have hK2_2 : 0 ≤ θ * ω * (a3 * t1 + (1 - b3) * t0) := by
    apply mul_nonneg (mul_nonneg (by linarith) (by linarith)) hK2_2a
  have hK2 : 0 ≤ (t0 + t1) * p * (t0 - θ) * al_T + θ * ω * (a3 * t1 + (1 - b3) * t0) := by linarith
  have hT2 : G01 * ((t0 + t1) * p * (t0 - θ) * al_T + θ * ω * (a3 * t1 + (1 - b3) * t0)) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hab hK2

  have hK3_1 : 0 ≤ al_t * p * (t2 * β - t1 * γ) := by
    apply mul_nonneg (mul_nonneg hal hp0) (by linarith)
  have hK3_2a : 0 ≤ (1 - b3) * t2 + c3 * t1 := by
    have p_b3 : 0 ≤ (1 - b3) * t2 := by positivity
    have p_c3 : 0 ≤ c3 * t1 := by positivity
    linarith
  have hK3_2 : 0 ≤ ω * (1 - p) * ((1 - b3) * t2 + c3 * t1) := by
    apply mul_nonneg (mul_nonneg (by linarith) h1_sub_p) hK3_2a
  have hK3 : 0 ≤ al_t * p * (t2 * β - t1 * γ) + ω * (1 - p) * ((1 - b3) * t2 + c3 * t1) := by linarith
  have hT3a : G12 * θ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hbc (by linarith)
  have hT3 : G12 * θ * (al_t * p * (t2 * β - t1 * γ) + ω * (1 - p) * ((1 - b3) * t2 + c3 * t1)) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hT3a hK3

  linarith

/-- Lemma WT (two-point certificate): under obtuse metric conditions with positive height `0 < h2`,
at least one of the two facing forms at `T` or `P` is strictly negative. -/
theorem wt_two_point (G : Matrix (Fin 3) (Fin 3) ℝ) (hG : G.IsSymm) (t : Fin 3 → ℝ) (h2 : ℝ)
    (hh2 : 0 < h2) (ht : ∀ i, ∑ j, G i j * t j = h2) (htp : ∀ i, 0 < t i) (hts : t 0 + t 1 + t 2 = 1)
    (hab : G 0 1 ≤ 0) (hbc : G 1 2 ≤ 0) (hd : 0 < G 0 0 + G 1 1 - 2 * G 0 1)
    (a3 b3 c3 θ γ p : ℝ) (hb3 : b3 < 1) (ha3 : 0 < a3) (hc3 : 0 < c3) (hθ : θ * (a3 + b3 + c3 - 1) = a3) (hθ0 : 0 < θ)
    (hγ : 0 < γ) (hθγ : θ + γ < 1) (hp : 0 ≤ p ∧ p ≤ 1) (hta : θ < t 0) (htc : γ < t 2)
    (hal : 0 ≤ c3 * t 0 - a3 * t 2) (halT : 0 ≤ c3 * θ - a3 * γ) :
    (![1, -1, 0] ⬝ᵥ G *ᵥ ![θ, 1 - θ - γ, γ] < 0) ∨ (![a3, b3 - 1, c3] ⬝ᵥ G *ᵥ ![p, 1 - p, 0] < 0) := by
  have h_ht0 : G 0 0 * t 0 + G 0 1 * t 1 + G 0 2 * t 2 = h2 := by
    have h := ht 0
    simp [Fin.sum_univ_three] at h
    exact h
  have h_ht1 : G 0 1 * t 0 + G 1 1 * t 1 + G 1 2 * t 2 = h2 := by
    have h := ht 1
    simp [Fin.sum_univ_three] at h
    rw [← hG.apply 0 1]
    exact h

  have hzT : ![1, -1, 0] ⬝ᵥ G *ᵥ ![θ, 1 - θ - γ, γ] =
      G 0 0 * θ + G 0 1 * (1 - θ - γ) + G 0 2 * γ - (G 0 1 * θ + G 1 1 * (1 - θ - γ) + G 1 2 * γ) :=
    form1_eval G hG θ γ
  have hzP : ![a3, b3 - 1, c3] ⬝ᵥ G *ᵥ ![p, 1 - p, 0] =
      a3 * (G 0 0 * p + G 0 1 * (1 - p)) + (b3 - 1) * (G 0 1 * p + G 1 1 * (1 - p)) + c3 * (G 0 2 * p + G 1 2 * (1 - p)) :=
    form2_eval G hG a3 b3 c3 p

  by_cases h_omega : θ * t 2 - γ * t 0 ≤ 0
  · left
    rw [hzT]
    have heq01 : (G 0 0 * t 0 + G 0 1 * t 1 + G 0 2 * t 2) - (G 0 1 * t 0 + G 1 1 * t 1 + G 1 2 * t 2) = 0 := by
      linarith [h_ht0, h_ht1]
    have heq_sum : t 0 + t 1 + t 2 - 1 = 0 := by linarith [hts]
    have h_t2_z : t 2 * (G 0 0 * θ + G 0 1 * (1 - θ - γ) + G 0 2 * γ - (G 0 1 * θ + G 1 1 * (1 - θ - γ) + G 1 2 * γ)) =
        (t 2 - γ) * (G 0 1 - G 1 1) + (θ * t 2 - γ * t 0) * (G 0 0 + G 1 1 - 2 * G 0 1) := by
      have h := identity_s1 (G 0 0) (G 0 1) (G 0 2) (G 1 1) (G 1 2) (t 0) (t 1) (t 2) θ γ
      rw [heq01, heq_sum] at h
      linarith [h]

    have h_G11_t1 : 0 < G 1 1 * t 1 := by
      have h_nonpos1 : G 0 1 * t 0 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hab (by linarith [htp 0])
      have h_nonpos2 : G 1 2 * t 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hbc (by linarith [htp 2])
      linarith [h_ht1, hh2, h_nonpos1, h_nonpos2]
    have h_G11_pos : 0 < G 1 1 := pos_of_mul_pos_left h_G11_t1 (by linarith [htp 1])
    have h_diff_G : G 0 1 - G 1 1 < 0 := by linarith [hab, h_G11_pos]
    have h_term1_neg : (t 2 - γ) * (G 0 1 - G 1 1) < 0 :=
      mul_neg_of_pos_of_neg (by linarith [htc]) h_diff_G
    have h_term2_nonpos : (θ * t 2 - γ * t 0) * (G 0 0 + G 1 1 - 2 * G 0 1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h_omega (by linarith [hd])
    have h_prod_neg : t 2 * (G 0 0 * θ + G 0 1 * (1 - θ - γ) + G 0 2 * γ - (G 0 1 * θ + G 1 1 * (1 - θ - γ) + G 1 2 * γ)) < 0 := by
      linarith [h_t2_z, h_term1_neg, h_term2_nonpos]
    exact neg_of_mul_neg_right h_prod_neg (by linarith [htp 2])

  · by_cases hzT_lt : ![1, -1, 0] ⬝ᵥ G *ᵥ ![θ, 1 - θ - γ, γ] < 0
    · exact Or.inl hzT_lt
    · right
      have hzT_ge : 0 ≤ G 0 0 * θ + G 0 1 * (1 - θ - γ) + G 0 2 * γ - (G 0 1 * θ + G 1 1 * (1 - θ - γ) + G 1 2 * γ) := by
        linarith [hzT, hzT_lt]
      by_contra hzP_ge'
      have hzP_ge : 0 ≤ a3 * (G 0 0 * p + G 0 1 * (1 - p)) + (b3 - 1) * (G 0 1 * p + G 1 1 * (1 - p)) + c3 * (G 0 2 * p + G 1 2 * (1 - p)) := by
        linarith [hzP, hzP_ge']

      have h_omega_pos : 0 < θ * t 2 - γ * t 0 := by linarith [h_omega]

      have h_lhs_eq_rhs := identity_s2 (G 0 0) (G 0 1) (G 0 2) (G 1 1) (G 1 2) h2 (t 0) (t 1) (t 2) a3 b3 c3 θ γ p
        h_ht0 h_ht1 hts hθ

      have h_t2_beta : 0 < t 2 * (1 - θ - γ) - t 1 * γ :=
        t2_beta_sub_t1_gamma_pos (t 0) (t 1) (t 2) θ γ hts hta htc hθγ hγ

      have h_rhs_neg :
        - h2 * (p * (c3 * θ - a3 * γ) * (t 0 - θ) + θ * (1 - b3) * (θ * t 2 - γ * t 0)) +
        G 0 1 * ((t 0 + t 1) * p * (t 0 - θ) * (c3 * θ - a3 * γ) + θ * (θ * t 2 - γ * t 0) * (a3 * t 1 + (1 - b3) * t 0)) +
        G 1 2 * θ * ((c3 * t 0 - a3 * t 2) * p * (t 2 * (1 - θ - γ) - t 1 * γ) + (θ * t 2 - γ * t 0) * (1 - p) * ((1 - b3) * t 2 + c3 * t 1)) < 0 :=
        rhs_theta_neg (G 0 1) (G 1 2) h2 (t 0) (t 1) (t 2) a3 b3 c3 θ γ (θ * t 2 - γ * t 0) (c3 * t 0 - a3 * t 2) (c3 * θ - a3 * γ) (1 - θ - γ) p
          hh2 hab hbc hb3 ha3 hc3 hθ0 hp.1 hp.2 hta (htp 0) (htp 1) (htp 2) hal halT h_omega_pos h_t2_beta

      have h_term_a : 0 ≤ (c3 * t 0 - a3 * t 2) * p * (G 0 0 * θ + G 0 1 * (1 - θ - γ) + G 0 2 * γ - (G 0 1 * θ + G 1 1 * (1 - θ - γ) + G 1 2 * γ)) := by
        have hp0 : 0 ≤ p := hp.1
        apply mul_nonneg (mul_nonneg hal hp0) hzT_ge
      have h_term_b : 0 ≤ (θ * t 2 - γ * t 0) * (a3 * (G 0 0 * p + G 0 1 * (1 - p)) + (b3 - 1) * (G 0 1 * p + G 1 1 * (1 - p)) + c3 * (G 0 2 * p + G 1 2 * (1 - p))) :=
        mul_nonneg (by linarith [h_omega_pos]) hzP_ge
      have h_inner : 0 ≤ (c3 * t 0 - a3 * t 2) * p * (G 0 0 * θ + G 0 1 * (1 - θ - γ) + G 0 2 * γ - (G 0 1 * θ + G 1 1 * (1 - θ - γ) + G 1 2 * γ)) +
          (θ * t 2 - γ * t 0) * (a3 * (G 0 0 * p + G 0 1 * (1 - p)) + (b3 - 1) * (G 0 1 * p + G 1 1 * (1 - p)) + c3 * (G 0 2 * p + G 1 2 * (1 - p))) := by linarith
      have h_mid : 0 ≤ t 1 * ((c3 * t 0 - a3 * t 2) * p * (G 0 0 * θ + G 0 1 * (1 - θ - γ) + G 0 2 * γ - (G 0 1 * θ + G 1 1 * (1 - θ - γ) + G 1 2 * γ)) +
          (θ * t 2 - γ * t 0) * (a3 * (G 0 0 * p + G 0 1 * (1 - p)) + (b3 - 1) * (G 0 1 * p + G 1 1 * (1 - p)) + c3 * (G 0 2 * p + G 1 2 * (1 - p)))) :=
        mul_nonneg (by linarith [htp 1]) h_inner
      have h_lhs_nonneg : 0 ≤ θ * (t 1 * ((c3 * t 0 - a3 * t 2) * p *
          (G 0 0 * θ + G 0 1 * (1 - θ - γ) + G 0 2 * γ - (G 0 1 * θ + G 1 1 * (1 - θ - γ) + G 1 2 * γ)) +
          (θ * t 2 - γ * t 0) * (a3 * (G 0 0 * p + G 0 1 * (1 - p)) + (b3 - 1) * (G 0 1 * p + G 1 1 * (1 - p)) + c3 * (G 0 2 * p + G 1 2 * (1 - p))))) :=
        mul_nonneg (by linarith [hθ0]) h_mid

      linarith [h_lhs_eq_rhs, h_rhs_neg, h_lhs_nonneg]

end Minimality.LemmaWT
