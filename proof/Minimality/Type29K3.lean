module

public import Minimality.Type29K4

@[expose] public section

/-!
# Type 29, class K3 (`FEWER-FACES-PROOFS.md` §21.2)

In the normal coordinates of `NF29` class K3a is `a2 < 0 < b0`, `V > 0` (K3b is its `σ`-image).
On `R_G` every shape has a metric-free certificate (Theorem 21.22).  With
`R = Π ∩ {θ > α, f ≥ F4}`:

* Lemma 21.12 (`NF29.k3_facts`): `h0 < 1`, `G4 > 0 > G5`, `F4 > F5`, `h2 > h0`.
* Theorem 21.13 (`6 ∉ R`, `NF29.isRupert_k3_notR`): Lemma E at the edges `56`, `14`, `46` of `K`
  (`NF29.isRupert_k3_C56`, `_C14`, `_C46`; Corollary 14.1, `isRupert_edgePairσ`).
* Theorem 21.15 (i) (`h2 < 1`, `NF29.isRupert_k3_i`): the pair `P14 = {T1, T2}`
  (`NF29.isRupert_k3_P14`, Corollary 13.3 in general form, `not_both_depthSep_gen`) or a
  triangular `T2` (`_T2b`, `_T2c`); (ii) `R = ∅` for `h2 ≥ 1 + A2` (`NF29.k3_R_empty`).
* `1 < h2 < 1 + A2` (`NF29.isRupert_k3_open`): (iii) `h0 > F5`; (iv) P11 (`_P11`); (v) the planar
  `T3` (`_T3p`, `NF29.planar_unimodal`); Lemma 21.16 (`_X`), Lemma 21.17 (the planar `Y1`,
  `_Y1p`), Proposition 21.19 (P13, `_P13`), Lemma 21.20 with Proposition 21.21 (Y′, `_Yp`, the
  pattern argument in reals `k3_Y2_core`).
* Theorem 21.22: `NF29.isRupert_K3a` (special positions and genericity in `K3Gen`) and
  `NF29.isRupert_K3b`.

The views are `NF29.vT1`, `vT2`, `vT3`, `vY1` (vertex crossings) and the edges `5 − 0`, `6 − 4`.
Derived facts of each region (21.14, 21.18) are proved inline by explicit products, with a
multiplier where the paper divides (`pos_of_mul_pos_r`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Minimality

open scoped RealInnerProductSpace
open Finset

/-- **Corollary 13.3, two tests** (general form): two 4-corner rims whose diagonals meet along
both views cannot both be depth-separated when the four determinants have a negative product. -/
theorem not_both_depthSep_gen {d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ u v : ℝ³}
    (h1 : DepthSep d₀ d₁ e₀ e₁ u) (h2 : DepthSep f₀ f₁ g₀ g₁ v)
    (m1u : SegMeet d₀ d₁ e₀ e₁ u) (m1v : SegMeet d₀ d₁ e₀ e₁ v)
    (m2v : SegMeet f₀ f₁ g₀ g₁ v) (m2u : SegMeet f₀ f₁ g₀ g₁ u)
    (hdet : det3 u (d₁ - d₀) (e₁ - e₀) * det3 v (d₁ - d₀) (e₁ - e₀) *
      (det3 u (f₁ - f₀) (g₁ - g₀) * det3 v (f₁ - f₀) (g₁ - g₀)) < 0) : False := by
  obtain ⟨A, hne⟩ := depthSep_det_sign (a' := d₀) (a := d₁) (b := e₀) (b' := e₁) h1 m1u m1v
  obtain ⟨B, -⟩ := depthSep_det_sign (a' := f₀) (a := f₁) (b := g₀) (b' := g₁) h2 m2v m2u
  rw [real_inner_comm u v] at B
  have hsq : 0 < ⟪u, v⟫ * ⟪u, v⟫ := mul_self_pos.mpr hne
  have := mul_nonneg A B
  have e : ⟪u, v⟫ * (det3 u (d₁ - d₀) (e₁ - e₀) * det3 v (d₁ - d₀) (e₁ - e₀)) *
      (⟪u, v⟫ * (det3 v (f₁ - f₀) (g₁ - g₀) * det3 u (f₁ - f₀) (g₁ - g₀))) =
      (⟪u, v⟫ * ⟪u, v⟫) * (det3 u (d₁ - d₀) (e₁ - e₀) * det3 v (d₁ - d₀) (e₁ - e₀) *
        (det3 u (f₁ - f₀) (g₁ - g₀) * det3 v (f₁ - f₀) (g₁ - g₀))) := by ring
  rw [e] at this
  linarith [mul_neg_of_pos_of_neg hsq hdet]

/-- `SegMeet` from a combination with a common positive denominator (endpoints allowed). -/
theorem segMeet_of_smul' {d₀ d₁ e₀ e₁ v : ℝ³} {K s t l : ℝ} (hK : 0 < K) (hs : 0 ≤ s)
    (hs' : 0 ≤ K - s) (ht : 0 ≤ t) (ht' : 0 ≤ K - t)
    (h : K • (e₀ - d₀) + t • (e₁ - e₀) - s • (d₁ - d₀) = l • v) : SegMeet d₀ d₁ e₀ e₁ v :=
  ⟨s / K, t / K, l / K, div_nonneg hs hK.le, (div_le_one hK).mpr (by linarith),
    div_nonneg ht hK.le, (div_le_one hK).mpr (by linarith), meet_of_smul hK.ne' h⟩

/-- A middle with a positive offset, from a combination with a common positive denominator. -/
theorem mid_comb' {m X Y U : ℝ³} {D₀ α β : ℝ} (hD : 0 < D₀) (hα : 0 < α) (hα' : 0 < D₀ - α)
    (hβ : 0 < β) (h : D₀ • (m - X) = α • (Y - X) + β • U) :
    ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ 0 < δ ∧ m = X + s • (Y - X) + δ • U :=
  ⟨α / D₀, β / D₀, div_pos hα hD, (div_lt_one hD).mpr (by linarith), div_pos hβ hD,
    eq_comb_div hD.ne' h⟩

variable {x : Fin 7 → ℝ³}

/-- The view of `T1 = 012/1456`: `u1 = (F5, −F4, 0)`, along `aff 012 ∩ H`. -/
noncomputable def NF29.vT1 (N : NF29 x) : ℝ³ :=
  nfV N.E₁ N.E₂ N.E₃ (N.h0 * N.a2 - N.h2 * N.a0) (-(N.h2 * N.b0 - N.h0 * N.b2)) 0

/-- The view of `T2 = 1456/234`: `u2 = (κ, B2, 0)`, `κ = 1 − h2 − a2`, along `aff 234 ∩ H`. -/
noncomputable def NF29.vT2 (N : NF29 x) : ℝ³ :=
  nfV N.E₁ N.E₂ N.E₃ (1 - N.h2 - N.a2) (-N.b2) 0

/-- The view of `T3 = 015/124`: `u3 = (A0 h2, B2 h0, h0 h2)`, along `aff 015 ∩ aff 124`. -/
noncomputable def NF29.vT3 (N : NF29 x) : ℝ³ :=
  nfV N.E₁ N.E₂ N.E₃ (-N.a0 * N.h2) (-N.b2 * N.h0) (N.h0 * N.h2)

/-- The view of `Y1 = 015/356`: `(A0 s, h0 s − A0 (1 − t), h0 s)`, along `aff 015 ∩ aff 356`. -/
noncomputable def NF29.vY1 (N : NF29 x) : ℝ³ :=
  nfV N.E₁ N.E₂ N.E₃ (-N.a0 * N.s) (N.h0 * N.s + N.a0 * (1 - N.t)) (N.h0 * N.s)

/-- Certificate form of `NF29.isRupert_k3_T1`
(`FEWER-FACES-PROOFS.md` §18.2, §21): the rim at its named view as `RimCertPts`
(or `RimCert`), without the `NoHDNAt` hypotheses, which only enter the corollary. -/
theorem NF29.rimThen_k3_T1 (N : NF29 x)
    (hb0 : 0 < N.b0)
    (hG5n : 0 < -N.a0 * N.h2 + N.a2 * N.h0 + N.a0 - N.a2)
    (hF45 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0)
    (hh20 : 0 < -N.h0 + N.h2)
    (hf : 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s - N.b0
          * N.h2 + N.b2 * N.h0)
    (hh21 : 0 < -N.h2 + 1)
    (hz : IsRobustUnimodal (quad ⟪x 1, N.vT1⟫ ⟪x 2, N.vT1⟫ ⟪x 3, N.vT1⟫ ⟪x 6, N.vT1⟫)) :
    RimThen (univ.image x) (N.vT1) (quad (x 1) (x 2) (x 3) (x 6))
      (NoHDNAt (univ.image x) (N.vT1)) := by
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine vquadσ_both (univ.image x) ({x 0, x 4, x 5} : Finset ℝ³) (u := N.vT1) ?_ hσ
    (img29 1) (img29 2) (img29 3) (img29 6)
    (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff])
        (by simp [N.inj.eq_iff]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hz ?_
  · exact nfV_ne_zero N.hD (Or.inl (ne_of_gt N.hF5))
  · simp only [NF29.vT1]; nf29_test N hσD
        (by show 0 < N.a0 * N.b2 * N.h2 - N.a2 * N.b0 * N.h2; linarith [mul_pos (N.hh2) N.hDD])
  · simp only [NF29.vT1]; nf29_test N hσD
        (by
          show 0 < -N.a0 * N.h2 ^ 2 * N.t + N.a2 * N.h0 * N.h2 * N.t + N.b0 * N.h2 ^ 2 * N.s - N.b2
            * N.h0 * N.h2 * N.s
          linarith [mul_pos (N.hh2) hf, mul_pos (N.hh2) N.hF4])
  · simp only [NF29.vT1]; nf29_test N hσD
        (by
          show 0 < N.a0 * N.h2 ^ 2 * N.t - N.a2 * N.h0 * N.h2 * N.t - N.b0 * N.h2 ^ 2 * N.s + N.b2 *
            N.h0 * N.h2 * N.s + N.a0 * N.b2 * N.h2 - N.a0 * N.h2 * N.t - N.a2 * N.b0 * N.h2 + N.a2 *
            N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s
          linarith [mul_pos (hf) hh21, mul_pos (N.hF4) hh21, mul_pos (N.hh0) N.hDD, mul_pos
              (mul_pos (hA0) hB2) hh20, mul_pos (mul_pos (N.hh2) hb0) hG5n, mul_pos
              (mul_pos (hA0) N.hF4) hh21, mul_pos (mul_pos (N.hDD) hh20) hh21, mul_pos
              (mul_pos (N.hh2) N.hh2) N.hDD])
  · simp only [NF29.vT1]; nf29_test N hσD
        (by show 0 < N.a0 * N.b2 * N.h2 - N.a2 * N.b0 * N.h2; linarith [mul_pos (N.hh2) N.hDD])
  · simp only [NF29.vT1]; nf29_test N hσD
        (by
          show 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s
          linarith [hf, N.hF4])
  · simp only [NF29.vT1]; nf29_test N hσD
        (by
          show 0 < N.a0 * N.h2 ^ 2 * N.t - N.a2 * N.h0 * N.h2 * N.t - N.b0 * N.h2 ^ 2 * N.s + N.b2 *
            N.h0 * N.h2 * N.s + N.a0 * N.b2 * N.h2 - N.a0 * N.h2 * N.t - N.a2 * N.b0 * N.h2 + N.a2 *
            N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s
          linarith [mul_pos (hf) hh21, mul_pos (N.hF4) hh21, mul_pos (N.hh0) N.hDD, mul_pos
              (mul_pos (hA0) hB2) hh20, mul_pos (mul_pos (N.hh2) hb0) hG5n, mul_pos
              (mul_pos (hA0) N.hF4) hh21, mul_pos (mul_pos (N.hDD) hh20) hh21, mul_pos
              (mul_pos (N.hh2) N.hh2) N.hDD])
  · simp only [NF29.vT1]; nf29_test N hσD
        (by
          show 0 < -N.a0 * N.h2 ^ 2 * N.t + N.a2 * N.h0 * N.h2 * N.t + N.b0 * N.h2 ^ 2 * N.s - N.b2
            * N.h0 * N.h2 * N.s
          linarith [mul_pos (N.hh2) hf, mul_pos (N.hh2) N.hF4])
  · simp only [NF29.vT1]; nf29_test N hσD
        (by
          show 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s
          linarith [hf, N.hF4])
  · intro z hz hzM hn0 hn1 hn2 hn3
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · exact absurd (by simp) hzM
    · exact absurd rfl hn0
    · exact absurd rfl hn1
    · exact absurd rfl hn2
    · exact absurd (by simp) hzM
    · exact absurd (by simp) hzM
    · exact absurd rfl hn3
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl
    · have hmid := mid_comb (m := x 0) (X := x 1) (Y := x 2) (U := N.vT1)
        (D₀ := N.a0 * N.b2 * N.h2 - N.a2 * N.b0 * N.h2)
            (α := N.a0 * N.b2 * N.h0 - N.a2 * N.b0 * N.h0) (β := -N.a0 * N.b2 + N.a2 * N.b0)
        (by linarith [mul_pos (N.hh2) N.hDD]) (by linarith [mul_pos (N.hh0) N.hDD])
        (by linarith [mul_pos (N.hDD) hh20])
        (ne_of_lt (by linarith [N.hDD]))
        (by simp only [NF29.vT1]; nf29_vec N)
      obtain ⟨s, δ, h1, h2, h3, h4⟩ := hmid
      exact ⟨s, δ, h1, h2, h3, Or.inl <| h4⟩
    · have hmid := mid_comb (m := x 4) (X := x 6) (Y := x 1) (U := N.vT1)
        (D₀ := -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s)
            (α := -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s -
              N.b0 * N.h2 + N.b2 * N.h0) (β := N.t)
        (by linarith [hf, N.hF4]) (by linarith [hf])
        (by linarith [N.hF4])
        (ne_of_gt (by linarith [N.ht]))
        (by simp only [NF29.vT1]; nf29_vec N)
      obtain ⟨s, δ, h1, h2, h3, h4⟩ := hmid
      exact ⟨s, δ, h1, h2, h3, Or.inr <| Or.inr <| Or.inr <| h4⟩
    · have hmid := mid_comb (m := x 5) (X := x 6) (Y := x 1) (U := N.vT1)
        (D₀ := -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s)
            (α := -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s +
              N.a0 * N.h2 - N.a2 * N.h0) (β := -N.s)
        (by linarith [hf, N.hF4]) (by linarith [hf, hF45])
        (by linarith [N.hF5])
        (ne_of_lt (by linarith [N.hs]))
        (by simp only [NF29.vT1]; nf29_vec N)
      obtain ⟨s, δ, h1, h2, h3, h4⟩ := hmid
      exact ⟨s, δ, h1, h2, h3, Or.inr <| Or.inr <| Or.inr <| h4⟩

/-- **Test `T1 = 012/1456`** (§21.15 (i)): the vertex crossing at `1`, view `u1 = (F5, −F4, 0)`, rim
`(1, 2, 3, 6)`; `0` a middle over `1–2`, `4`, `5` over `6–1`. -/
theorem NF29.isRupert_k3_T1 (N : NF29 x)
    (hb0 : 0 < N.b0)
    (hG5n : 0 < -N.a0 * N.h2 + N.a2 * N.h0 + N.a0 - N.a2)
    (hF45 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0)
    (hh20 : 0 < -N.h0 + N.h2)
    (hf : 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s - N.b0
          * N.h2 + N.b2 * N.h0)
    (hh21 : 0 < -N.h2 + 1)
    (hz : IsRobustUnimodal (quad ⟪x 1, N.vT1⟫ ⟪x 2, N.vT1⟫ ⟪x 3, N.vT1⟫ ⟪x 6, N.vT1⟫))
    (hnd : NoHDNAt (univ.image x) (N.vT1)) : IsRupert (univ.image x) := by
  obtain ⟨-, -, -, h⟩ := NF29.rimThen_k3_T1 N hb0 hG5n hF45 hh20 hf hh21 hz
  exact h hnd

/-- Certificate form of `NF29.isRupert_k3_T2a`
(`FEWER-FACES-PROOFS.md` §18.2, §21): the rim at its named view as `RimCertPts`
(or `RimCert`), without the `NoHDNAt` hypotheses, which only enter the corollary. -/
theorem NF29.rimThen_k3_T2a (N : NF29 x)
    (hA2 : 0 < -N.a2)
    (hh21 : 0 < -N.h2 + 1)
    (hsg : 0 < N.a2 * N.t - N.b2 * N.s + N.h2 * N.t - N.a2 - N.h2 - N.t + 1)
    (hc0 : 0 < N.a0 * N.b2 - N.a2 * N.b0 - N.a2 * N.h0 - N.b0 * N.h2 - N.h0 * N.h2 + N.a2 + N.b0 +
          N.h0 + N.h2 - 1)
    (hz : IsRobustUnimodal (quad ⟪x 4, N.vT2⟫ ⟪x 3, N.vT2⟫ ⟪x 0, N.vT2⟫ ⟪x 5, N.vT2⟫)) :
    RimThen (univ.image x) (N.vT2) (quad (x 4) (x 3) (x 0) (x 5))
      (NoHDNAt (univ.image x) (N.vT2)) := by
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  have h345_2 : 0 < 1 - N.a2 - N.b2 - N.h2 := by linarith [N.t345_2]
  have hst : 0 < N.s + N.t - 1 := by linarith [N.hst]
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine vquadσ_both (univ.image x) ({x 1, x 2, x 6} : Finset ℝ³) (u := N.vT2) ?_ hσ
    (img29 4) (img29 3) (img29 0) (img29 5)
    (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff])
        (by simp [N.inj.eq_iff]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hz ?_
  · exact nfV_ne_zero N.hD (Or.inr (Or.inl (ne_of_gt (by linarith [N.hb2]))))
  · simp only [NF29.vT2]; nf29_test N hσD N.hDG4
  · simp only [NF29.vT2]; nf29_test N hσD h345_2
  · simp only [NF29.vT2]; nf29_test N hσD hc0
  · simp only [NF29.vT2]; nf29_test N hσD N.hDG4
  · simp only [NF29.vT2]; nf29_test N hσD
        (by
          show 0 < -N.a2 * N.h0 - N.b2 * N.h0 - N.h0 * N.h2 + N.h0
          linarith [mul_pos (N.hh0) h345_2])
  · simp only [NF29.vT2]; nf29_test N hσD hc0
  · simp only [NF29.vT2]; nf29_test N hσD h345_2
  · simp only [NF29.vT2]; nf29_test N hσD
        (by
          show 0 < -N.a2 * N.h0 - N.b2 * N.h0 - N.h0 * N.h2 + N.h0
          linarith [mul_pos (N.hh0) h345_2])
  · intro z hz hzM hn0 hn1 hn2 hn3
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · exact absurd rfl hn2
    · exact absurd (by simp) hzM
    · exact absurd (by simp) hzM
    · exact absurd rfl hn1
    · exact absurd rfl hn0
    · exact absurd rfl hn3
    · exact absurd (by simp) hzM
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl
    · have hmid := mid_comb (m := x 1) (X := x 5) (Y := x 4) (U := N.vT2)
        (D₀ := -N.a2 - N.b2 - N.h2 + 1) (α := -N.a2 - N.h2 + 1) (β := -1)
        (by linarith [h345_2]) (by linarith [hA2, hh21])
        (by linarith [hB2])
        (ne_of_lt (by norm_num))
        (by simp only [NF29.vT2]; nf29_vec N)
      obtain ⟨s, δ, h1, h2, h3, h4⟩ := hmid
      exact ⟨s, δ, h1, h2, h3, Or.inr <| Or.inr <| Or.inr <| h4⟩
    · have hmid := mid_comb (m := x 2) (X := x 4) (Y := x 3) (U := N.vT2)
        (D₀ := -N.b2) (α := -N.b2 * N.h2) (β := N.b2)
        (by linarith [hB2]) (by linarith [mul_pos (N.hh2) hB2])
        (by linarith [mul_pos (hB2) hh21])
        (ne_of_lt (by linarith [hB2]))
        (by simp only [NF29.vT2]; nf29_vec N)
      obtain ⟨s, δ, h1, h2, h3, h4⟩ := hmid
      exact ⟨s, δ, h1, h2, h3, Or.inl <| h4⟩
    · have hmid := mid_comb (m := x 6) (X := x 5) (Y := x 4) (U := N.vT2)
        (D₀ := -N.a2 - N.b2 - N.h2 + 1)
            (α := N.a2 * N.t - N.b2 * N.s + N.h2 * N.t - N.a2 - N.h2 - N.t + 1) (β := N.s + N.t - 1)
        (by linarith [h345_2]) (by linarith [hsg])
        (by linarith [N.d234])
        (ne_of_gt (by linarith [hst]))
        (by simp only [NF29.vT2]; nf29_vec N)
      obtain ⟨s, δ, h1, h2, h3, h4⟩ := hmid
      exact ⟨s, δ, h1, h2, h3, Or.inr <| Or.inr <| Or.inr <| h4⟩

/-- **Test `T2 = 1456/234`** (§21.15 (i)), `0` a corner: the vertex crossing at `4`, view `u2 = (κ,
B2, 0)`, rim `(4, 3, 0, 5)`; `2` a middle over `4–3`, `1`, `6` over `5–4`. -/
theorem NF29.isRupert_k3_T2a (N : NF29 x)
    (hA2 : 0 < -N.a2)
    (hh21 : 0 < -N.h2 + 1)
    (hsg : 0 < N.a2 * N.t - N.b2 * N.s + N.h2 * N.t - N.a2 - N.h2 - N.t + 1)
    (hc0 : 0 < N.a0 * N.b2 - N.a2 * N.b0 - N.a2 * N.h0 - N.b0 * N.h2 - N.h0 * N.h2 + N.a2 + N.b0 +
          N.h0 + N.h2 - 1)
    (hz : IsRobustUnimodal (quad ⟪x 4, N.vT2⟫ ⟪x 3, N.vT2⟫ ⟪x 0, N.vT2⟫ ⟪x 5, N.vT2⟫))
    (hnd : NoHDNAt (univ.image x) (N.vT2)) : IsRupert (univ.image x) := by
  obtain ⟨-, -, -, h⟩ := NF29.rimThen_k3_T2a N hA2 hh21 hsg hc0 hz
  exact h hnd

/-- Certificate form of `NF29.isRupert_k3_T2b`
(`FEWER-FACES-PROOFS.md` §18.2, §21): the rim at its named view as `RimCertPts`
(or `RimCert`), without the `NoHDNAt` hypotheses, which only enter the corollary. -/
theorem NF29.rimThen_k3_T2b (N : NF29 x)
    (hA2 : 0 < -N.a2)
    (hh21 : 0 < -N.h2 + 1)
    (hsg : 0 < N.a2 * N.t - N.b2 * N.s + N.h2 * N.t - N.a2 - N.h2 - N.t + 1)
    (hc0 : 0 < -N.a0 * N.b2 + N.a2 * N.b0 + N.a2 * N.h0 + N.b0 * N.h2 + N.h0 * N.h2 - N.a2 - N.b0 -
          N.h0 - N.h2 + 1)
    (hz : [⟪x 4, N.vT2⟫, ⟪x 3, N.vT2⟫, ⟪x 5, N.vT2⟫].Nodup) :
    RimThen (univ.image x) (N.vT2) (tri (x 4) (x 3) (x 5))
      (NoHDNAt (univ.image x) (N.vT2)) := by
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  have h345_2 : 0 < 1 - N.a2 - N.b2 - N.h2 := by linarith [N.t345_2]
  have hst : 0 < N.s + N.t - 1 := by linarith [N.hst]
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine vtriσ_both (univ.image x) ({x 1, x 2, x 6} : Finset ℝ³) (u := N.vT2) ?_ hσ
    (img29 4) (img29 3) (img29 5)
    (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) ?_ ?_ ?_ ?_ hz ?_
  · exact nfV_ne_zero N.hD (Or.inr (Or.inl (ne_of_gt (by linarith [N.hb2]))))
  · simp only [NF29.vT2]; nf29_test N hσD h345_2
  · simp only [NF29.vT2]; nf29_test N hσD h345_2
  · simp only [NF29.vT2]; nf29_test N hσD h345_2
  · intro z hz hzM hn0 hn1 hn2
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · refine ⟨?_, ?_, ?_⟩
      · simp only [NF29.vT2]; nf29_test N hσD N.hDG4
      · simp only [NF29.vT2]; nf29_test N hσD hc0
      · simp only [NF29.vT2]; nf29_test N hσD
            (by
              show 0 < -N.a2 * N.h0 - N.b2 * N.h0 - N.h0 * N.h2 + N.h0
              linarith [mul_pos (N.hh0) h345_2])
    · exact absurd (by simp) hzM
    · exact absurd (by simp) hzM
    · exact absurd rfl hn1
    · exact absurd rfl hn0
    · exact absurd rfl hn2
    · exact absurd (by simp) hzM
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl
    · have hmid := mid_comb (m := x 1) (X := x 5) (Y := x 4) (U := N.vT2)
        (D₀ := -N.a2 - N.b2 - N.h2 + 1) (α := -N.a2 - N.h2 + 1) (β := -1)
        (by linarith [h345_2]) (by linarith [hA2, hh21])
        (by linarith [hB2])
        (ne_of_lt (by norm_num))
        (by simp only [NF29.vT2]; nf29_vec N)
      obtain ⟨s, δ, h1, h2, h3, h4⟩ := hmid
      exact ⟨s, δ, h1, h2, h3, Or.inr <| Or.inr <| h4⟩
    · have hmid := mid_comb (m := x 2) (X := x 4) (Y := x 3) (U := N.vT2)
        (D₀ := -N.b2) (α := -N.b2 * N.h2) (β := N.b2)
        (by linarith [hB2]) (by linarith [mul_pos (N.hh2) hB2])
        (by linarith [mul_pos (hB2) hh21])
        (ne_of_lt (by linarith [hB2]))
        (by simp only [NF29.vT2]; nf29_vec N)
      obtain ⟨s, δ, h1, h2, h3, h4⟩ := hmid
      exact ⟨s, δ, h1, h2, h3, Or.inl <| h4⟩
    · have hmid := mid_comb (m := x 6) (X := x 5) (Y := x 4) (U := N.vT2)
        (D₀ := -N.a2 - N.b2 - N.h2 + 1)
            (α := N.a2 * N.t - N.b2 * N.s + N.h2 * N.t - N.a2 - N.h2 - N.t + 1) (β := N.s + N.t - 1)
        (by linarith [h345_2]) (by linarith [hsg])
        (by linarith [N.d234])
        (ne_of_gt (by linarith [hst]))
        (by simp only [NF29.vT2]; nf29_vec N)
      obtain ⟨s, δ, h1, h2, h3, h4⟩ := hmid
      exact ⟨s, δ, h1, h2, h3, Or.inr <| Or.inr <| h4⟩

/-- **Test `T2`** with `0` hidden: rim `(4, 3, 5)` (a triangle: free). -/
theorem NF29.isRupert_k3_T2b (N : NF29 x)
    (hA2 : 0 < -N.a2)
    (hh21 : 0 < -N.h2 + 1)
    (hsg : 0 < N.a2 * N.t - N.b2 * N.s + N.h2 * N.t - N.a2 - N.h2 - N.t + 1)
    (hc0 : 0 < -N.a0 * N.b2 + N.a2 * N.b0 + N.a2 * N.h0 + N.b0 * N.h2 + N.h0 * N.h2 - N.a2 - N.b0 -
          N.h0 - N.h2 + 1)
    (hz : [⟪x 4, N.vT2⟫, ⟪x 3, N.vT2⟫, ⟪x 5, N.vT2⟫].Nodup)
    (hnd : NoHDNAt (univ.image x) (N.vT2)) : IsRupert (univ.image x) := by
  obtain ⟨-, -, -, h⟩ := NF29.rimThen_k3_T2b N hA2 hh21 hsg hc0 hz
  exact h hnd

/-- Certificate form of `NF29.isRupert_k3_T2c`
(`FEWER-FACES-PROOFS.md` §18.2, §21): the rim at its named view as `RimCertPts`
(or `RimCert`), without the `NoHDNAt` hypotheses, which only enter the corollary. -/
theorem NF29.rimThen_k3_T2c (N : NF29 x)
    (hA2 : 0 < -N.a2)
    (hh01 : 0 < -N.h0 + 1)
    (hh21 : 0 < -N.h2 + 1)
    (hsg : 0 < -N.a2 * N.t + N.b2 * N.s - N.h2 * N.t + N.a2 + N.h2 + N.t - 1)
    (hx0 : 0 < -N.a0 * N.b2 + N.a2 * N.b0 + N.a2 * N.h0 + N.b0 * N.h2 + N.h0 * N.h2 - N.a2 - N.b0 -
          N.h0 - N.h2 + 1)
    (hz : [⟪x 4, N.vT2⟫, ⟪x 3, N.vT2⟫, ⟪x 6, N.vT2⟫].Nodup) :
    RimThen (univ.image x) (N.vT2) (tri (x 4) (x 3) (x 6))
      (NoHDNAt (univ.image x) (N.vT2)) := by
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  have h345_2 : 0 < 1 - N.a2 - N.b2 - N.h2 := by linarith [N.t345_2]
  have hst : 0 < N.s + N.t - 1 := by linarith [N.hst]
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine vtriσ_both (univ.image x) ({x 1, x 2, x 5} : Finset ℝ³) (u := N.vT2) ?_ hσ
    (img29 4) (img29 3) (img29 6)
    (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) ?_ ?_ ?_ ?_ hz ?_
  · exact nfV_ne_zero N.hD (Or.inr (Or.inl (ne_of_gt (by linarith [N.hb2]))))
  · simp only [NF29.vT2]; nf29_test N hσD N.d234
  · simp only [NF29.vT2]; nf29_test N hσD N.d234
  · simp only [NF29.vT2]; nf29_test N hσD N.d234
  · intro z hz hzM hn0 hn1 hn2
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · refine ⟨?_, ?_, ?_⟩
      · simp only [NF29.vT2]; nf29_test N hσD N.hDG4
      · simp only [NF29.vT2]; nf29_test N hσD
            (by
              show 0 < N.a2 * N.h0 * N.t - N.b2 * N.h0 * N.s + N.h0 * N.h2 * N.t - N.a0 * N.b2 +
                N.a2 * N.b0 - N.a2 * N.t + N.b0 * N.h2 + N.b2 * N.s - N.h0 * N.t - N.h2 * N.t - N.b0
                + N.t
              linarith [hx0, mul_pos (hh01) hsg])
      · simp only [NF29.vT2]; nf29_test N hσD
            (by
              show 0 < -N.a2 * N.h0 * N.t + N.b2 * N.h0 * N.s - N.h0 * N.h2 * N.t - N.b2 * N.h0 +
                N.h0 * N.t
              linarith [mul_pos (N.hh0) N.d234])
    · exact absurd (by simp) hzM
    · exact absurd (by simp) hzM
    · exact absurd rfl hn1
    · exact absurd rfl hn0
    · exact absurd (by simp) hzM
    · exact absurd rfl hn2
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl
    · have hmid := mid_comb (m := x 1) (X := x 6) (Y := x 4) (U := N.vT2)
        (D₀ := -N.a2 * N.t + N.b2 * N.s - N.h2 * N.t - N.b2 + N.t)
            (α := -N.a2 * N.t + N.b2 * N.s - N.h2 * N.t + N.t) (β := -N.t)
        (by linarith [N.d234]) (by linarith [hsg, hA2, hh21])
        (by linarith [hB2])
        (ne_of_lt (by linarith [N.ht]))
        (by simp only [NF29.vT2]; nf29_vec N)
      obtain ⟨s, δ, h1, h2, h3, h4⟩ := hmid
      exact ⟨s, δ, h1, h2, h3, Or.inr <| Or.inr <| h4⟩
    · have hmid := mid_comb (m := x 2) (X := x 4) (Y := x 3) (U := N.vT2)
        (D₀ := -N.b2) (α := -N.b2 * N.h2) (β := N.b2)
        (by linarith [hB2]) (by linarith [mul_pos (N.hh2) hB2])
        (by linarith [mul_pos (hB2) hh21])
        (ne_of_lt (by linarith [hB2]))
        (by simp only [NF29.vT2]; nf29_vec N)
      obtain ⟨s, δ, h1, h2, h3, h4⟩ := hmid
      exact ⟨s, δ, h1, h2, h3, Or.inl <| h4⟩
    · have hmid := mid_comb (m := x 5) (X := x 6) (Y := x 4) (U := N.vT2)
        (D₀ := -N.a2 * N.t + N.b2 * N.s - N.h2 * N.t - N.b2 + N.t)
            (α := -N.a2 * N.t + N.b2 * N.s - N.h2 * N.t + N.a2 + N.h2 + N.t - 1)
            (β := -N.s - N.t + 1)
        (by linarith [N.d234]) (by linarith [hsg])
        (by linarith [h345_2])
        (ne_of_lt (by linarith [hst]))
        (by simp only [NF29.vT2]; nf29_vec N)
      obtain ⟨s, δ, h1, h2, h3, h4⟩ := hmid
      exact ⟨s, δ, h1, h2, h3, Or.inr <| Or.inr <| h4⟩

/-- **Test `T2`** with `6` the far end of the quadrilateral (`σ6 < −κ`): rim `(4, 3, 6)` (free). -/
theorem NF29.isRupert_k3_T2c (N : NF29 x)
    (hA2 : 0 < -N.a2)
    (hh01 : 0 < -N.h0 + 1)
    (hh21 : 0 < -N.h2 + 1)
    (hsg : 0 < -N.a2 * N.t + N.b2 * N.s - N.h2 * N.t + N.a2 + N.h2 + N.t - 1)
    (hx0 : 0 < -N.a0 * N.b2 + N.a2 * N.b0 + N.a2 * N.h0 + N.b0 * N.h2 + N.h0 * N.h2 - N.a2 - N.b0 -
          N.h0 - N.h2 + 1)
    (hz : [⟪x 4, N.vT2⟫, ⟪x 3, N.vT2⟫, ⟪x 6, N.vT2⟫].Nodup)
    (hnd : NoHDNAt (univ.image x) (N.vT2)) : IsRupert (univ.image x) := by
  obtain ⟨-, -, -, h⟩ := NF29.rimThen_k3_T2c N hA2 hh01 hh21 hsg hx0 hz
  exact h hnd

/-- **The pair `P14 = {T1, T2}`** (§21.15 (i)): Corollary 13.3. -/
theorem NF29.isRupert_k3_P14 (N : NF29 x)
    (hA2 : 0 < -N.a2)
    (hb0 : 0 < N.b0)
    (hh01 : 0 < -N.h0 + 1)
    (hG5n : 0 < -N.a0 * N.h2 + N.a2 * N.h0 + N.a0 - N.a2)
    (hF45 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0)
    (hh20 : 0 < -N.h0 + N.h2)
    (hth : 0 < -N.a2 * N.t + N.b2 * N.s)
    (hf : 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s - N.b0
          * N.h2 + N.b2 * N.h0)
    (hh21 : 0 < -N.h2 + 1)
    (hsg : 0 < N.a2 * N.t - N.b2 * N.s + N.h2 * N.t - N.a2 - N.h2 - N.t + 1)
    (hc0 : 0 < N.a0 * N.b2 - N.a2 * N.b0 - N.a2 * N.h0 - N.b0 * N.h2 - N.h0 * N.h2 + N.a2 + N.b0 +
          N.h0 + N.h2 - 1)
    (hz1 : [⟪x 1, N.vT1⟫, ⟪x 2, N.vT1⟫, ⟪x 3, N.vT1⟫, ⟪x 6, N.vT1⟫].Nodup)
    (hz2 : [⟪x 4, N.vT2⟫, ⟪x 3, N.vT2⟫, ⟪x 0, N.vT2⟫, ⟪x 5, N.vT2⟫].Nodup)
    (hnd1 : NoHDNAt (univ.image x) N.vT1)
    (hnd2 : NoHDNAt (univ.image x) N.vT2) : IsRupert (univ.image x) := by
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  have h345_0 : 0 < 1 - N.a0 - N.b0 - N.h0 := by linarith [N.t345_0]
  have h345_2 : 0 < 1 - N.a2 - N.b2 - N.h2 := by linarith [N.t345_2]
  have m11 : SegMeet (x 1) (x 3) (x 2) (x 6) (N.vT1) := segMeet_of_smul'
      (K := N.a0 * N.b2 * N.h2 - N.a0 * N.h2 * N.t - N.a2 * N.b0 * N.h2 + N.a2 * N.h0 * N.t + N.b0 *
        N.h2 * N.s - N.b2 * N.h0 * N.s)
    (s := -N.a0 * N.h2 ^ 2 * N.t + N.a2 * N.h0 * N.h2 * N.t + N.b0 * N.h2 ^ 2 * N.s - N.b2 * N.h0 *
          N.h2 * N.s)
    (t := N.a0 * N.b2 * N.h2 - N.a2 * N.b0 * N.h2)
    (l := N.a2 * N.t - N.b2 * N.s)
    (by linarith [hf, N.hF4, mul_pos (N.hh2) N.hDD])
    (by linarith [mul_pos (N.hh2) hf, mul_pos (N.hh2) N.hF4])
    (by
          linarith [mul_pos (hf) hh21, mul_pos (hF45) hh21, mul_pos (N.hDD) hh20, mul_pos (N.hF5)
              hh21, mul_pos (mul_pos (N.hh0) hA2) hb0, mul_pos (mul_pos (N.hh2) hA0) hB2, mul_pos
              (mul_pos (N.hh2) hb0) hG5n, mul_pos (mul_pos (hA0) N.hF4) hh21, mul_pos
              (mul_pos (N.hh0) N.hh2) N.hDD])
    (by linarith [mul_pos (N.hh2) N.hDD])
    (by linarith [hf, N.hF4])
    (by simp only [NF29.vT1]; nf29_vec N)
  have m12 : SegMeet (x 1) (x 3) (x 2) (x 6) (N.vT2) := segMeet_of_smul'
      (K := -N.a2 * N.t + N.b2 * N.h2 + N.b2 * N.s - N.h2 * N.t - N.b2 + N.t)
    (s := -N.a2 * N.h2 * N.t + N.b2 * N.h2 * N.s - N.h2 ^ 2 * N.t + N.h2 * N.t)
    (t := N.b2 * N.h2 - N.b2)
    (l := N.a2 * N.t - N.b2 * N.s)
    (by linarith [hth, mul_pos (hB2) hh21, mul_pos (N.ht) hh21])
    (by linarith [mul_pos (N.hh2) hth, mul_pos (mul_pos (N.hh2) N.ht) hh21])
    (by linarith [mul_pos (N.d234) hh21])
    (by linarith [mul_pos (hB2) hh21])
    (by linarith [hth, mul_pos (N.ht) hh21])
    (by simp only [NF29.vT2]; nf29_vec N)
  have m21 : SegMeet (x 4) (x 0) (x 3) (x 5) (N.vT1) := segMeet_of_smul'
      (K := N.a0 * N.b2 * N.h0 + N.a0 * N.h0 * N.h2 - N.a2 * N.b0 * N.h0 - N.a2 * N.h0 ^ 2 + N.b0 *
        N.h2 - N.b2 * N.h0)
    (s := N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0)
    (t := N.a0 * N.b2 * N.h0 - N.a2 * N.b0 * N.h0 - N.b0 * N.h0 * N.h2 + N.b2 * N.h0 ^ 2 + N.b0 *
          N.h2 - N.b2 * N.h0)
    (l := N.a0 + N.b0 + N.h0 - 1)
    (by linarith [mul_pos (hb0) hh20, mul_pos (N.hh0) hF45, mul_pos (N.hh0) N.hDG4])
    (by linarith [hF45])
    (by linarith [mul_pos (hA0) hh20, mul_pos (N.hh0) N.hDG5])
    (by
          linarith [mul_pos (hA0) hh20, mul_pos (N.hh0) hc0, mul_pos (hh01) hF45, mul_pos
              (mul_pos (N.hh0) h345_0) hh21])
    (by linarith [mul_pos (N.hh0) hF45])
    (by simp only [NF29.vT1]; nf29_vec N)
  have m22 : SegMeet (x 4) (x 0) (x 3) (x 5) (N.vT2) := segMeet_of_smul'
      (K := N.a0 * N.b2 - N.a2 * N.b0 - N.a2 * N.h0 - N.b0 * N.h2 - N.h0 * N.h2 + N.b0 - N.b2
          + N.h0)
    (s := -N.a2 - N.b2 - N.h2 + 1)
    (t := N.a0 * N.b2 - N.a2 * N.b0 - N.b0 * N.h2 + N.b2 * N.h0 + N.b0 - N.b2)
    (l := -N.a0 - N.b0 - N.h0 + 1)
    (by linarith [hc0, h345_2])
    (by linarith [h345_2])
    (by linarith [hc0])
    (by linarith [N.hDG4])
    (by linarith [mul_pos (N.hh0) h345_2])
    (by simp only [NF29.vT2]; nf29_vec N)
  have eq11 : det3 (N.vT1) (x 3 - x 1) (x 6 - x 2) =
      (N.a0 * N.b2 * N.h2 - N.a0 * N.h2 * N.t - N.a2 * N.b0 * N.h2 + N.a2 * N.h0 * N.t + N.b0 * N.h2
        * N.s - N.b2 * N.h0 * N.s) * det3 N.E₁ N.E₂ N.E₃ := by
    simp only [NF29.vT1]; nf29_simp N; simp only [det3c]; ring
  have pq11 : 0 < N.a0 * N.b2 * N.h2 - N.a0 * N.h2 * N.t - N.a2 * N.b0 * N.h2 + N.a2 * N.h0 * N.t +
      N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s := (by linarith [hf, N.hF4, mul_pos (N.hh2) N.hDD])
  have eq12 : det3 (N.vT2) (x 3 - x 1) (x 6 - x 2) =
      (-N.a2 * N.t + N.b2 * N.h2 + N.b2 * N.s - N.h2 * N.t - N.b2 + N.t) * det3 N.E₁ N.E₂ N.E₃ := by
    simp only [NF29.vT2]; nf29_simp N; simp only [det3c]; ring
  have pq12 : 0 < -N.a2 * N.t + N.b2 * N.h2 + N.b2 * N.s - N.h2 * N.t - N.b2 + N.t :=
      (by linarith [hth, mul_pos (hB2) hh21, mul_pos (N.ht) hh21])
  have eq21 : det3 (N.vT1) (x 0 - x 4) (x 5 - x 3) =
      (-N.a0 * N.b2 * N.h0 - N.a0 * N.h0 * N.h2 + N.a2 * N.b0 * N.h0 + N.a2 * N.h0 ^ 2 - N.b0 * N.h2
        + N.b2 * N.h0) * det3 N.E₁ N.E₂ N.E₃ := by
    simp only [NF29.vT1]; nf29_simp N; simp only [det3c]; ring
  have pq21 : -N.a0 * N.b2 * N.h0 - N.a0 * N.h0 * N.h2 + N.a2 * N.b0 * N.h0 + N.a2 * N.h0 ^ 2 - N.b0
      * N.h2 + N.b2 * N.h0 < 0 :=
      (by linarith [mul_pos (hb0) hh20, mul_pos (N.hh0) hF45, mul_pos (N.hh0) N.hDG4])
  have eq22 : det3 (N.vT2) (x 0 - x 4) (x 5 - x 3) =
      (N.a0 * N.b2 - N.a2 * N.b0 - N.a2 * N.h0 - N.b0 * N.h2 - N.h0 * N.h2 + N.b0 - N.b2 + N.h0) *
      det3 N.E₁ N.E₂ N.E₃ := by
    simp only [NF29.vT2]; nf29_simp N; simp only [det3c]; ring
  have pq22 : 0 < N.a0 * N.b2 - N.a2 * N.b0 - N.a2 * N.h0 - N.b0 * N.h2 - N.h0 * N.h2 + N.b0 - N.b2
      + N.h0 := (by linarith [hc0, h345_2])
  by_cases h1 : DepthSep (x 1) (x 3) (x 2) (x 6) (N.vT1)
  · by_cases h2 : DepthSep (x 4) (x 0) (x 3) (x 5) (N.vT2)
    · exfalso
      exact not_both_depthSep_gen h1 h2 m11 m12 m22 m21
        (det4_neg N.hD eq11 eq12 eq21 eq22
              (mul_neg_of_pos_of_neg (mul_pos pq11 pq12) (mul_neg_of_neg_of_pos pq21 pq22)))
    · exact NF29.isRupert_k3_T2a N hA2 hh21 hsg hc0 (quad_unimodal h2 hz2).isRobustUnimodal hnd2
  · exact NF29.isRupert_k3_T1 N hb0 hG5n hF45 hh20 hf hh21 (quad_unimodal h1 hz1).isRobustUnimodal
        hnd1
/-- Certificate form of `NF29.isRupert_k3_T1o`
(`FEWER-FACES-PROOFS.md` §18.2, §21): the rim at its named view as `RimCertPts`
(or `RimCert`), without the `NoHDNAt` hypotheses, which only enter the corollary. -/
theorem NF29.rimThen_k3_T1o (N : NF29 x)
    (hh01 : 0 < -N.h0 + 1)
    (hF45 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0)
    (hh20 : 0 < -N.h0 + N.h2)
    (hth : 0 < -N.a2 * N.t + N.b2 * N.s)
    (hf : 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s - N.b0
          * N.h2 + N.b2 * N.h0)
    (hh2g : 0 < N.h2 - 1)
    (hz : IsRobustUnimodal (quad ⟪x 1, N.vT1⟫ ⟪x 2, N.vT1⟫ ⟪x 3, N.vT1⟫ ⟪x 6, N.vT1⟫)) :
    RimThen (univ.image x) (N.vT1) (quad (x 1) (x 2) (x 3) (x 6))
      (NoHDNAt (univ.image x) (N.vT1)) := by
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine vquadσ_both (univ.image x) ({x 0, x 4, x 5} : Finset ℝ³) (u := N.vT1) ?_ hσ
    (img29 1) (img29 2) (img29 3) (img29 6)
    (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff])
        (by simp [N.inj.eq_iff]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hz ?_
  · exact nfV_ne_zero N.hD (Or.inl (ne_of_gt N.hF5))
  · simp only [NF29.vT1]; nf29_test N hσD
        (by show 0 < N.a0 * N.b2 * N.h2 - N.a2 * N.b0 * N.h2; linarith [mul_pos (N.hh2) N.hDD])
  · simp only [NF29.vT1]; nf29_test N hσD
        (by
          show 0 < -N.a0 * N.h2 ^ 2 * N.t + N.a2 * N.h0 * N.h2 * N.t + N.b0 * N.h2 ^ 2 * N.s - N.b2
            * N.h0 * N.h2 * N.s
          linarith [mul_pos (N.hh2) hf, mul_pos (N.hh2) N.hF4])
  · simp only [NF29.vT1]; nf29_test N hσD
        (by
          show 0 < N.a0 * N.h2 ^ 2 * N.t - N.a2 * N.h0 * N.h2 * N.t - N.b0 * N.h2 ^ 2 * N.s + N.b2 *
            N.h0 * N.h2 * N.s + N.a0 * N.b2 * N.h2 - N.a0 * N.h2 * N.t - N.a2 * N.b0 * N.h2 + N.a2 *
            N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s
          linarith [N.d023, mul_pos (hh20) hth, mul_pos (N.d023) hh2g])
  · simp only [NF29.vT1]; nf29_test N hσD
        (by show 0 < N.a0 * N.b2 * N.h2 - N.a2 * N.b0 * N.h2; linarith [mul_pos (N.hh2) N.hDD])
  · simp only [NF29.vT1]; nf29_test N hσD
        (by
          show 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s
          linarith [hf, N.hF4])
  · simp only [NF29.vT1]; nf29_test N hσD
        (by
          show 0 < N.a0 * N.h2 ^ 2 * N.t - N.a2 * N.h0 * N.h2 * N.t - N.b0 * N.h2 ^ 2 * N.s + N.b2 *
            N.h0 * N.h2 * N.s + N.a0 * N.b2 * N.h2 - N.a0 * N.h2 * N.t - N.a2 * N.b0 * N.h2 + N.a2 *
            N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s
          linarith [N.d023, mul_pos (hh20) hth, mul_pos (N.d023) hh2g])
  · simp only [NF29.vT1]; nf29_test N hσD
        (by
          show 0 < -N.a0 * N.h2 ^ 2 * N.t + N.a2 * N.h0 * N.h2 * N.t + N.b0 * N.h2 ^ 2 * N.s - N.b2
            * N.h0 * N.h2 * N.s
          linarith [mul_pos (N.hh2) hf, mul_pos (N.hh2) N.hF4])
  · simp only [NF29.vT1]; nf29_test N hσD
        (by
          show 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s
          linarith [hf, N.hF4])
  · intro z hz hzM hn0 hn1 hn2 hn3
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · exact absurd (by simp) hzM
    · exact absurd rfl hn0
    · exact absurd rfl hn1
    · exact absurd rfl hn2
    · exact absurd (by simp) hzM
    · exact absurd (by simp) hzM
    · exact absurd rfl hn3
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl
    · have hmid := mid_comb (m := x 0) (X := x 1) (Y := x 2) (U := N.vT1)
        (D₀ := N.a0 * N.b2 * N.h2 - N.a2 * N.b0 * N.h2)
            (α := N.a0 * N.b2 * N.h0 - N.a2 * N.b0 * N.h0) (β := -N.a0 * N.b2 + N.a2 * N.b0)
        (by linarith [mul_pos (N.hh2) N.hDD]) (by linarith [mul_pos (N.hh0) N.hDD])
        (by linarith [mul_pos (N.hDD) hh2g, mul_pos (N.hDD) hh01])
        (ne_of_lt (by linarith [N.hDD]))
        (by simp only [NF29.vT1]; nf29_vec N)
      obtain ⟨s, δ, h1, h2, h3, h4⟩ := hmid
      exact ⟨s, δ, h1, h2, h3, Or.inl <| h4⟩
    · have hmid := mid_comb (m := x 4) (X := x 6) (Y := x 1) (U := N.vT1)
        (D₀ := -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s)
            (α := -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s -
              N.b0 * N.h2 + N.b2 * N.h0) (β := N.t)
        (by linarith [hf, N.hF4]) (by linarith [hf])
        (by linarith [N.hF4])
        (ne_of_gt (by linarith [N.ht]))
        (by simp only [NF29.vT1]; nf29_vec N)
      obtain ⟨s, δ, h1, h2, h3, h4⟩ := hmid
      exact ⟨s, δ, h1, h2, h3, Or.inr <| Or.inr <| Or.inr <| h4⟩
    · have hmid := mid_comb (m := x 5) (X := x 6) (Y := x 1) (U := N.vT1)
        (D₀ := -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s)
            (α := -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s +
              N.a0 * N.h2 - N.a2 * N.h0) (β := -N.s)
        (by linarith [hf, N.hF4]) (by linarith [hf, hF45])
        (by linarith [N.hF5])
        (ne_of_lt (by linarith [N.hs]))
        (by simp only [NF29.vT1]; nf29_vec N)
      obtain ⟨s, δ, h1, h2, h3, h4⟩ := hmid
      exact ⟨s, δ, h1, h2, h3, Or.inr <| Or.inr <| Or.inr <| h4⟩

/-- **Test `T1`** in P11 (§21.15 (iv)): rim `(1, 2, 3, 6)`. -/
theorem NF29.isRupert_k3_T1o (N : NF29 x)
    (hh01 : 0 < -N.h0 + 1)
    (hF45 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0)
    (hh20 : 0 < -N.h0 + N.h2)
    (hth : 0 < -N.a2 * N.t + N.b2 * N.s)
    (hf : 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s - N.b0
          * N.h2 + N.b2 * N.h0)
    (hh2g : 0 < N.h2 - 1)
    (hz : IsRobustUnimodal (quad ⟪x 1, N.vT1⟫ ⟪x 2, N.vT1⟫ ⟪x 3, N.vT1⟫ ⟪x 6, N.vT1⟫))
    (hnd : NoHDNAt (univ.image x) (N.vT1)) : IsRupert (univ.image x) := by
  obtain ⟨-, -, -, h⟩ := NF29.rimThen_k3_T1o N hh01 hF45 hh20 hth hf hh2g hz
  exact h hnd

/-- Certificate form of `NF29.isRupert_k3_T3o`
(`FEWER-FACES-PROOFS.md` §18.2, §21): the rim at its named view as `RimCertPts`
(or `RimCert`), without the `NoHDNAt` hypotheses, which only enter the corollary. -/
theorem NF29.rimThen_k3_T3o (N : NF29 x)
    (hh01 : 0 < -N.h0 + 1)
    (hh20 : 0 < -N.h0 + N.h2)
    (hth : 0 < -N.a2 * N.t + N.b2 * N.s)
    (hh2g : 0 < N.h2 - 1)
    (hh0F5 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.h0)
    (hF4h2 : 0 < N.b0 * N.h2 - N.b2 * N.h0 - N.h2)
    (hN : 0 < N.a0 * N.b2 - N.a2 * N.b0 - N.a2 * N.h0 + N.a2)
    (hal : 0 < -N.a0 * N.b0 * N.h2 + N.a0 * N.b2 * N.h0 - N.a0 * N.h0 * N.h2 - N.b0 * N.h0 * N.h2 -
          N.h0 ^ 2 * N.h2 + N.a0 * N.h2 + N.h0 * N.h2)
    (hhF5 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.h0 * N.h2)
    (hz : IsRobustUnimodal (quad ⟪x 1, N.vT3⟫ ⟪x 4, N.vT3⟫ ⟪x 3, N.vT3⟫ ⟪x 0, N.vT3⟫)) :
    RimThen (univ.image x) (N.vT3) (quad (x 1) (x 4) (x 3) (x 0))
      (NoHDNAt (univ.image x) (N.vT3)) := by
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  have h345_0 : 0 < 1 - N.a0 - N.b0 - N.h0 := by linarith [N.t345_0]
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine vquadσ_both (univ.image x) ({x 2, x 5} : Finset ℝ³) (u := N.vT3) ?_ hσ
    (img29 1) (img29 4) (img29 3) (img29 0)
    (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff])
        (by simp [N.inj.eq_iff]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hz ?_
  · exact nfV_ne_zero N.hD (Or.inr (Or.inr (ne_of_gt (mul_pos N.hh0 N.hh2))))
  · simp only [NF29.vT3]; nf29_test N hσD (by show 0 < -N.b2 * N.h0; linarith [mul_pos (N.hh0) hB2])
  · simp only [NF29.vT3]; nf29_test N hσD
        (by show 0 < N.b0 * N.h0 * N.h2 - N.b2 * N.h0 ^ 2; linarith [mul_pos (N.hh0) N.hF4])
  · simp only [NF29.vT3]; nf29_test N hσD
        (by
          show 0 < -N.a0 * N.b0 * N.h2 + N.a0 * N.b2 * N.h0 - N.b0 * N.h0 * N.h2 + N.b2 * N.h0 ^ 2 -
            N.b2 * N.h0
          linarith [hal, h345_0, mul_pos (hA0) hF4h2, mul_pos (hh01) hF4h2, mul_pos (h345_0) hh20,
              mul_pos (mul_pos (h345_0) hh01) hh2g])
  · simp only [NF29.vT3]; nf29_test N hσD (by show 0 < -N.b2 * N.h0; linarith [mul_pos (N.hh0) hB2])
  · simp only [NF29.vT3]; nf29_test N hσD
        (by
          show 0 < -N.a0 * N.b0 * N.h2 + N.a0 * N.b2 * N.h0
          linarith [hA0, mul_pos (hA0) hh20, mul_pos (hA0) hF4h2, mul_pos (mul_pos (hA0) hh01) hh2g,
              mul_pos (mul_pos (N.hh0) N.hh2) hA0])
  · simp only [NF29.vT3]; nf29_test N hσD
        (by
          show 0 < -N.a0 * N.b0 * N.h2 + N.a0 * N.b2 * N.h0 - N.b0 * N.h0 * N.h2 + N.b2 * N.h0 ^ 2 -
            N.b2 * N.h0
          linarith [hal, h345_0, mul_pos (hA0) hF4h2, mul_pos (hh01) hF4h2, mul_pos (h345_0) hh20,
              mul_pos (mul_pos (h345_0) hh01) hh2g])
  · simp only [NF29.vT3]; nf29_test N hσD
        (by show 0 < N.b0 * N.h0 * N.h2 - N.b2 * N.h0 ^ 2; linarith [mul_pos (N.hh0) N.hF4])
  · simp only [NF29.vT3]; nf29_test N hσD
        (by
          show 0 < -N.a0 * N.b0 * N.h2 + N.a0 * N.b2 * N.h0
          linarith [hA0, mul_pos (hA0) hh20, mul_pos (hA0) hF4h2, mul_pos (mul_pos (hA0) hh01) hh2g,
              mul_pos (mul_pos (N.hh0) N.hh2) hA0])
  · intro z hz hzM hn0 hn1 hn2 hn3
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · exact absurd rfl hn3
    · exact absurd rfl hn0
    · exact absurd (by simp) hzM
    · exact absurd rfl hn2
    · exact absurd rfl hn1
    · exact absurd (by simp) hzM
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [NF29.vT3]; nf29_test N hσD
            (by show 0 < N.h0 * N.h2 * N.t; linarith [mul_pos (mul_pos (N.hh0) N.hh2) N.ht])
      · simp only [NF29.vT3]; nf29_test N hσD
            (pos_of_mul_pos_r hN (by
                show 0 < (-N.a0 * N.h2 * N.t + N.b2 * N.h0 * N.s - N.h0 * N.h2 * N.t - N.b2 * N.h0)
                  * (N.a0 * N.b2 - N.a2 * N.b0 - N.a2 * N.h0 + N.a2)
                linarith [mul_pos (hth) hal, mul_pos (mul_pos (hA0) hB2) hF4h2, mul_pos
                    (mul_pos (hB2) N.d035) hhF5, mul_pos (mul_pos (hB2) h345_0) N.hF5]))
      · simp only [NF29.vT3]; nf29_test N hσD
            (by
              show 0 < -N.b0 * N.h0 * N.h2 * N.s + N.b2 * N.h0 ^ 2 * N.s - N.a0 * N.b0 * N.h2 + N.a0
                * N.b2 * N.h0 + N.a0 * N.h2 * N.t - N.b2 * N.h0 * N.s
              linarith [N.d035, mul_pos (hA0) hF4h2, mul_pos (N.d035) hh20, mul_pos
                  (mul_pos (N.hs) hh01) hF4h2, mul_pos (mul_pos (N.d035) hh01) hh2g, mul_pos
                  (mul_pos (N.hh0) N.hh2) N.d035])
      · simp only [NF29.vT3]; nf29_test N hσD
            (by
              show 0 < N.b0 * N.h0 * N.h2 * N.s - N.b2 * N.h0 ^ 2 * N.s
              linarith [mul_pos (mul_pos (N.hh0) N.hF4) N.hs])
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · have hmid := mid_comb (m := x 2) (X := x 1) (Y := x 4) (U := N.vT3)
        (D₀ := -N.b2 * N.h0) (α := N.a0 * N.b2 * N.h2 - N.a2 * N.b2 * N.h0) (β := N.b2)
        (by linarith [mul_pos (N.hh0) hB2]) (by linarith [mul_pos (hB2) N.hF5])
        (by linarith [mul_pos (hB2) hh0F5])
        (ne_of_lt (by linarith [hB2]))
        (by simp only [NF29.vT3]; nf29_vec N)
      obtain ⟨s, δ, h1, h2, h3, h4⟩ := hmid
      exact ⟨s, δ, h1, h2, h3, Or.inl <| h4⟩
    · have hmid := mid_comb (m := x 5) (X := x 0) (Y := x 1) (U := N.vT3)
        (D₀ := -N.a0 * N.b0 * N.h2 + N.a0 * N.b2 * N.h0)
            (α := -N.a0 * N.b0 * N.h2 + N.a0 * N.b2 * N.h0 + N.a0 * N.h2) (β := -N.a0)
        (by
              linarith [hA0, mul_pos (hA0) hh20, mul_pos (hA0) hF4h2, mul_pos (mul_pos (hA0) hh01)
                  hh2g, mul_pos (mul_pos (N.hh0) N.hh2) hA0]) (by linarith [mul_pos (hA0) hF4h2])
        (by linarith [hA0, mul_pos (hA0) hh2g])
        (ne_of_gt (by linarith [hA0]))
        (by simp only [NF29.vT3]; nf29_vec N)
      obtain ⟨s, δ, h1, h2, h3, h4⟩ := hmid
      exact ⟨s, δ, h1, h2, h3, Or.inr <| Or.inr <| Or.inr <| h4⟩

/-- **Test `T3 = 015/124`** in P11 (§21.15 (iv)): the vertex crossing at `1`, view `u3 = (A0 h2, B2
h0, h0 h2)`, rim `(1, 4, 3, 0)`; `2` a middle over `1–4`, `5` over `0–1`, `6` hidden. -/
theorem NF29.isRupert_k3_T3o (N : NF29 x)
    (hh01 : 0 < -N.h0 + 1)
    (hh20 : 0 < -N.h0 + N.h2)
    (hth : 0 < -N.a2 * N.t + N.b2 * N.s)
    (hh2g : 0 < N.h2 - 1)
    (hh0F5 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.h0)
    (hF4h2 : 0 < N.b0 * N.h2 - N.b2 * N.h0 - N.h2)
    (hN : 0 < N.a0 * N.b2 - N.a2 * N.b0 - N.a2 * N.h0 + N.a2)
    (hal : 0 < -N.a0 * N.b0 * N.h2 + N.a0 * N.b2 * N.h0 - N.a0 * N.h0 * N.h2 - N.b0 * N.h0 * N.h2 -
          N.h0 ^ 2 * N.h2 + N.a0 * N.h2 + N.h0 * N.h2)
    (hhF5 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.h0 * N.h2)
    (hz : IsRobustUnimodal (quad ⟪x 1, N.vT3⟫ ⟪x 4, N.vT3⟫ ⟪x 3, N.vT3⟫ ⟪x 0, N.vT3⟫))
    (hnd : NoHDNAt (univ.image x) (N.vT3)) : IsRupert (univ.image x) := by
  obtain ⟨-, -, -, h⟩ := NF29.rimThen_k3_T3o N hh01 hh20 hth hh2g hh0F5 hF4h2 hN hal hhF5 hz
  exact h hnd

/-- Certificate form of `NF29.isRupert_k3_T3p`
(`FEWER-FACES-PROOFS.md` §18.2, §21): the rim at its named view as `RimCertPts`
(or `RimCert`), without the `NoHDNAt` hypotheses, which only enter the corollary. -/
theorem NF29.rimThen_k3_T3p (N : NF29 x)
    (hh2g : 0 < N.h2 - 1)
    (hh0F5 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.h0)
    (hh2F4 : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.h2)
    (hq46 : 0 < N.a0 * N.h2 * N.t - N.b2 * N.h0 * N.s + N.h0 * N.h2 * N.t + N.b2 * N.h0)
    (hq65 : 0 < -N.a0 * N.h2 * N.t + N.b2 * N.h0 * N.s + N.h0 * N.h2 * N.s + N.a0 * N.h2)
    (hz : IsRobustUnimodal (quad ⟪x 1, N.vT3⟫ ⟪x 4, N.vT3⟫ ⟪x 6, N.vT3⟫ ⟪x 5, N.vT3⟫)) :
    RimThen (univ.image x) (N.vT3) (quad (x 1) (x 4) (x 6) (x 5))
      (NoHDNAt (univ.image x) (N.vT3)) := by
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  have hst : 0 < N.s + N.t - 1 := by linarith [N.hst]
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine vquadσ_both (univ.image x) ({x 0, x 2} : Finset ℝ³) (u := N.vT3) ?_ hσ
    (img29 1) (img29 4) (img29 6) (img29 5)
    (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff])
        (by simp [N.inj.eq_iff]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hz ?_
  · exact nfV_ne_zero N.hD (Or.inr (Or.inr (ne_of_gt (mul_pos N.hh0 N.hh2))))
  · simp only [NF29.vT3]; nf29_test N hσD
        (by show 0 < N.h0 * N.h2 * N.t; linarith [mul_pos (mul_pos (N.hh0) N.hh2) N.ht])
  · simp only [NF29.vT3]; nf29_test N hσD
        (by show 0 < N.h0 * N.h2; linarith [mul_pos (N.hh0) N.hh2])
  · simp only [NF29.vT3]; nf29_test N hσD
        (by
          show 0 < N.h0 * N.h2 * N.s + N.h0 * N.h2 * N.t - N.h0 * N.h2
          linarith [mul_pos (mul_pos (N.hh0) N.hh2) hst])
  · simp only [NF29.vT3]; nf29_test N hσD
        (by show 0 < N.h0 * N.h2 * N.t; linarith [mul_pos (mul_pos (N.hh0) N.hh2) N.ht])
  · simp only [NF29.vT3]; nf29_test N hσD
        (by show 0 < N.h0 * N.h2 * N.s; linarith [mul_pos (mul_pos (N.hh0) N.hh2) N.hs])
  · simp only [NF29.vT3]; nf29_test N hσD
        (by
          show 0 < N.h0 * N.h2 * N.s + N.h0 * N.h2 * N.t - N.h0 * N.h2
          linarith [mul_pos (mul_pos (N.hh0) N.hh2) hst])
  · simp only [NF29.vT3]; nf29_test N hσD
        (by show 0 < N.h0 * N.h2; linarith [mul_pos (N.hh0) N.hh2])
  · simp only [NF29.vT3]; nf29_test N hσD
        (by show 0 < N.h0 * N.h2 * N.s; linarith [mul_pos (mul_pos (N.hh0) N.hh2) N.hs])
  · intro z hz hzM hn0 hn1 hn2 hn3
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · exact absurd (by simp) hzM
    · exact absurd rfl hn0
    · exact absurd (by simp) hzM
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [NF29.vT3]; nf29_test N hσD
            (by show 0 < -N.b2 * N.h0; linarith [mul_pos (N.hh0) hB2])
      · simp only [NF29.vT3]; nf29_test N hσD hq46
      · simp only [NF29.vT3]; nf29_test N hσD hq65
      · simp only [NF29.vT3]; nf29_test N hσD
            (by show 0 < -N.a0 * N.h2; linarith [hA0, mul_pos (hA0) hh2g])
    · exact absurd rfl hn1
    · exact absurd rfl hn3
    · exact absurd rfl hn2
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · have hmid := mid_comb (m := x 0) (X := x 5) (Y := x 1) (U := N.vT3)
        (D₀ := -N.a0 * N.h2) (α := N.a0 * N.b0 * N.h2 - N.a0 * N.b2 * N.h0 - N.a0 * N.h2)
            (β := N.a0)
        (by linarith [hA0, mul_pos (hA0) hh2g]) (by linarith [mul_pos (hA0) hh2F4])
        (by linarith [mul_pos (hA0) N.hF4])
        (ne_of_lt (by linarith [hA0]))
        (by simp only [NF29.vT3]; nf29_vec N)
      obtain ⟨s, δ, h1, h2, h3, h4⟩ := hmid
      exact ⟨s, δ, h1, h2, h3, Or.inr <| Or.inr <| Or.inr <| h4⟩
    · have hmid := mid_comb (m := x 2) (X := x 1) (Y := x 4) (U := N.vT3)
        (D₀ := -N.b2 * N.h0) (α := N.a0 * N.b2 * N.h2 - N.a2 * N.b2 * N.h0) (β := N.b2)
        (by linarith [mul_pos (N.hh0) hB2]) (by linarith [mul_pos (hB2) N.hF5])
        (by linarith [mul_pos (hB2) hh0F5])
        (ne_of_lt (by linarith [hB2]))
        (by simp only [NF29.vT3]; nf29_vec N)
      obtain ⟨s, δ, h1, h2, h3, h4⟩ := hmid
      exact ⟨s, δ, h1, h2, h3, Or.inl <| h4⟩

/-- **Test `T3`, planar** (§21.15 (v)): rim `(1, 4, 6, 5)` in `H`; `2` a middle over `1–4`, `0` over
`5–1`, `3` hidden (`Q3` inside `(1, 4, 6, 5)`). -/
theorem NF29.isRupert_k3_T3p (N : NF29 x)
    (hh2g : 0 < N.h2 - 1)
    (hh0F5 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.h0)
    (hh2F4 : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.h2)
    (hq46 : 0 < N.a0 * N.h2 * N.t - N.b2 * N.h0 * N.s + N.h0 * N.h2 * N.t + N.b2 * N.h0)
    (hq65 : 0 < -N.a0 * N.h2 * N.t + N.b2 * N.h0 * N.s + N.h0 * N.h2 * N.s + N.a0 * N.h2)
    (hz : IsRobustUnimodal (quad ⟪x 1, N.vT3⟫ ⟪x 4, N.vT3⟫ ⟪x 6, N.vT3⟫ ⟪x 5, N.vT3⟫))
    (hnd : NoHDNAt (univ.image x) (N.vT3)) : IsRupert (univ.image x) := by
  obtain ⟨-, -, -, h⟩ := NF29.rimThen_k3_T3p N hh2g hh0F5 hh2F4 hq46 hq65 hz
  exact h hnd

/-- Certificate form of `NF29.isRupert_k3_Xa`
(`FEWER-FACES-PROOFS.md` §18.2, §21): the rim at its named view as `RimCertPts`
(or `RimCert`), without the `NoHDNAt` hypotheses, which only enter the corollary. -/
theorem NF29.rimThen_k3_Xa (N : NF29 x)
    (hh2F4 : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.h2)
    (hXf : 0 < -N.a0 * N.t + N.b0 * N.s - N.h0 * N.t - N.b0 - N.s + 1)
    (hb01 : 0 < -N.b0 + 1)
    (hXa2 : 0 < -N.a0 * N.b2 + N.a2 * N.b0 + N.b0 * N.h2 - N.b2 * N.h0 - N.a2 - N.b0 - N.h2 + 1)
    (hz : IsRobustUnimodal
          (quad ⟪x 5, (x 5 - x 0)⟫ ⟪x 1, (x 5 - x 0)⟫ ⟪x 4, (x 5 - x 0)⟫ ⟪x 3, (x 5 - x 0)⟫)) :
    RimThen (univ.image x) (x 5 - x 0) (quad (x 5) (x 1) (x 4) (x 3))
      (NoHDNAt ((univ.image x).erase (x 0)) ((x 5 - x 0))) := by
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have h345_0 : 0 < 1 - N.a0 - N.b0 - N.h0 := by linarith [N.t345_0]
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine equadσ_both (univ.image x) (∅ : Finset ℝ³) (u := (x 5 - x 0)) ?_ hσ (h := 1)
      one_ne_zero
    (by module) (img29 0)
    (img29 5) (img29 1) (img29 4) (img29 3)
    (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff])
        (by simp [N.inj.eq_iff]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hz ?_
  · exact sub_ne_zero.mpr (N.inj.ne (by decide))
  · nf29_test N hσD N.hh0
  · nf29_test N hσD hA0
  · nf29_test N hσD hb01
  · nf29_test N hσD N.hh0
  · nf29_test N hσD h345_0
  · nf29_test N hσD hb01
  · nf29_test N hσD hA0
  · nf29_test N hσD h345_0
  · intro z hz hzM hzw hn0 hn1 hn2 hn3
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · exact absurd rfl hzw
    · exact absurd rfl hn1
    · refine ⟨?_, ?_, ?_, ?_⟩
      · nf29_test N hσD N.hF5
      · nf29_test N hσD hh2F4
      · nf29_test N hσD hXa2
      · nf29_test N hσD N.hDG5
    · exact absurd rfl hn3
    · exact absurd rfl hn2
    · exact absurd rfl hn0
    · refine ⟨?_, ?_, ?_, ?_⟩
      · nf29_test N hσD (by show 0 < N.h0 * N.s; linarith [mul_pos (N.hh0) N.hs])
      · nf29_test N hσD (by show 0 < N.h0 * N.t; linarith [mul_pos (N.hh0) N.ht])
      · nf29_test N hσD hXf
      · nf29_test N hσD N.d035
  · intro m hm
    simp at hm

/-- **Test `Xa = 015/035-0`** (§21.16): the edge crossing along `05` (apex `5`, view `5 − 0`), rim
`(5, 1, 4, 3)`; `2`, `6` hidden. -/
theorem NF29.isRupert_k3_Xa (N : NF29 x)
    (hh2F4 : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.h2)
    (hXf : 0 < -N.a0 * N.t + N.b0 * N.s - N.h0 * N.t - N.b0 - N.s + 1)
    (hb01 : 0 < -N.b0 + 1)
    (hXa2 : 0 < -N.a0 * N.b2 + N.a2 * N.b0 + N.b0 * N.h2 - N.b2 * N.h0 - N.a2 - N.b0 - N.h2 + 1)
    (hz : IsRobustUnimodal
          (quad ⟪x 5, (x 5 - x 0)⟫ ⟪x 1, (x 5 - x 0)⟫ ⟪x 4, (x 5 - x 0)⟫ ⟪x 3, (x 5 - x 0)⟫))
    (hnd : NoHDNAt ((univ.image x).erase (x 0)) ((x 5 - x 0))) : IsRupert (univ.image x) := by
  obtain ⟨-, -, -, h⟩ := NF29.rimThen_k3_Xa N hh2F4 hXf hb01 hXa2 hz
  exact h hnd

/-- Certificate form of `NF29.isRupert_k3_T2o`
(`FEWER-FACES-PROOFS.md` §18.2, §21): the rim at its named view as `RimCertPts`
(or `RimCert`), without the `NoHDNAt` hypotheses, which only enter the corollary. -/
theorem NF29.rimThen_k3_T2o (N : NF29 x)
    (hV3 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (hh2g : 0 < N.h2 - 1)
    (hkap : 0 < -N.a2 - N.h2 + 1)
    (hsg : 0 < N.a2 * N.t - N.b2 * N.s + N.h2 * N.t - N.a2 - N.h2 - N.t + 1)
    (hz : IsRobustUnimodal (quad ⟪x 4, N.vT2⟫ ⟪x 2, N.vT2⟫ ⟪x 0, N.vT2⟫ ⟪x 5, N.vT2⟫)) :
    RimThen (univ.image x) (N.vT2) (quad (x 4) (x 2) (x 0) (x 5))
      (NoHDNAt (univ.image x) (N.vT2)) := by
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  have h345_2 : 0 < 1 - N.a2 - N.b2 - N.h2 := by linarith [N.t345_2]
  have hst : 0 < N.s + N.t - 1 := by linarith [N.hst]
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine vquadσ_both (univ.image x) ({x 1, x 3, x 6} : Finset ℝ³) (u := N.vT2) ?_ hσ
    (img29 4) (img29 2) (img29 0) (img29 5)
    (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff])
        (by simp [N.inj.eq_iff]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hz ?_
  · exact nfV_ne_zero N.hD (Or.inr (Or.inl (ne_of_gt (by linarith [N.hb2]))))
  · simp only [NF29.vT2]; nf29_test N hσD
        (by
          show 0 < N.a0 * N.b2 * N.h2 - N.a2 * N.b0 * N.h2 - N.b0 * N.h2 ^ 2 + N.b2 * N.h0 * N.h2 +
            N.b0 * N.h2 - N.b2 * N.h2
          linarith [mul_pos (N.hh2) N.hDG4])
  · simp only [NF29.vT2]; nf29_test N hσD
        (by
          show 0 < -N.a2 * N.h2 - N.b2 * N.h2 - N.h2 ^ 2 + N.h2
          linarith [h345_2, mul_pos (h345_2) hh2g])
  · simp only [NF29.vT2]; nf29_test N hσD
        (by
          show 0 < N.a0 * N.b2 * N.h2 - N.a2 * N.b0 * N.h2 - N.b0 * N.h2 ^ 2 + N.b2 * N.h0 * N.h2 -
            N.a2 * N.h0 + N.a2 * N.h2 + N.b0 * N.h2 - N.b2 * N.h0 - N.h0 * N.h2 + N.h2 ^ 2 + N.h0 -
            N.h2
          linarith [mul_pos (hV3) hkap, mul_pos (h345_2) N.hF5])
  · simp only [NF29.vT2]; nf29_test N hσD
        (by
          show 0 < N.a0 * N.b2 * N.h2 - N.a2 * N.b0 * N.h2 - N.b0 * N.h2 ^ 2 + N.b2 * N.h0 * N.h2 +
            N.b0 * N.h2 - N.b2 * N.h2
          linarith [mul_pos (N.hh2) N.hDG4])
  · simp only [NF29.vT2]; nf29_test N hσD
        (by
          show 0 < -N.a2 * N.h0 - N.b2 * N.h0 - N.h0 * N.h2 + N.h0
          linarith [mul_pos (N.hh0) h345_2])
  · simp only [NF29.vT2]; nf29_test N hσD
        (by
          show 0 < N.a0 * N.b2 * N.h2 - N.a2 * N.b0 * N.h2 - N.b0 * N.h2 ^ 2 + N.b2 * N.h0 * N.h2 -
            N.a2 * N.h0 + N.a2 * N.h2 + N.b0 * N.h2 - N.b2 * N.h0 - N.h0 * N.h2 + N.h2 ^ 2 + N.h0 -
            N.h2
          linarith [mul_pos (hV3) hkap, mul_pos (h345_2) N.hF5])
  · simp only [NF29.vT2]; nf29_test N hσD
        (by
          show 0 < -N.a2 * N.h2 - N.b2 * N.h2 - N.h2 ^ 2 + N.h2
          linarith [h345_2, mul_pos (h345_2) hh2g])
  · simp only [NF29.vT2]; nf29_test N hσD
        (by
          show 0 < -N.a2 * N.h0 - N.b2 * N.h0 - N.h0 * N.h2 + N.h0
          linarith [mul_pos (N.hh0) h345_2])
  · intro z hz hzM hn0 hn1 hn2 hn3
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · exact absurd rfl hn2
    · exact absurd (by simp) hzM
    · exact absurd rfl hn1
    · exact absurd (by simp) hzM
    · exact absurd rfl hn0
    · exact absurd rfl hn3
    · exact absurd (by simp) hzM
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl
    · have hmid := mid_comb (m := x 1) (X := x 5) (Y := x 4) (U := N.vT2)
        (D₀ := -N.a2 - N.b2 - N.h2 + 1) (α := -N.a2 - N.h2 + 1) (β := -1)
        (by linarith [h345_2]) (by linarith [hkap])
        (by linarith [hB2])
        (ne_of_lt (by norm_num))
        (by simp only [NF29.vT2]; nf29_vec N)
      obtain ⟨s, δ, h1, h2, h3, h4⟩ := hmid
      exact ⟨s, δ, h1, h2, h3, Or.inr <| Or.inr <| Or.inr <| h4⟩
    · have hmid := mid_comb (m := x 3) (X := x 4) (Y := x 2) (U := N.vT2)
        (D₀ := -N.b2 * N.h2) (α := -N.b2) (β := -N.b2)
        (by linarith [hB2, mul_pos (hB2) hh2g]) (by linarith [hB2])
        (by linarith [mul_pos (hB2) hh2g])
        (ne_of_gt (by linarith [hB2]))
        (by simp only [NF29.vT2]; nf29_vec N)
      obtain ⟨s, δ, h1, h2, h3, h4⟩ := hmid
      exact ⟨s, δ, h1, h2, h3, Or.inl <| h4⟩
    · have hmid := mid_comb (m := x 6) (X := x 5) (Y := x 4) (U := N.vT2)
        (D₀ := -N.a2 - N.b2 - N.h2 + 1)
            (α := N.a2 * N.t - N.b2 * N.s + N.h2 * N.t - N.a2 - N.h2 - N.t + 1) (β := N.s + N.t - 1)
        (by linarith [h345_2]) (by linarith [hsg])
        (by linarith [N.d234])
        (ne_of_gt (by linarith [hst]))
        (by simp only [NF29.vT2]; nf29_vec N)
      obtain ⟨s, δ, h1, h2, h3, h4⟩ := hmid
      exact ⟨s, δ, h1, h2, h3, Or.inr <| Or.inr <| Or.inr <| h4⟩

/-- **Test `T2`** for `h2 > 1` (§21.16, §21.19): rim `(4, 2, 0, 5)`; `3` a middle over `4–2`, `1`,
`6` over `5–4`. -/
theorem NF29.isRupert_k3_T2o (N : NF29 x)
    (hV3 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (hh2g : 0 < N.h2 - 1)
    (hkap : 0 < -N.a2 - N.h2 + 1)
    (hsg : 0 < N.a2 * N.t - N.b2 * N.s + N.h2 * N.t - N.a2 - N.h2 - N.t + 1)
    (hz : IsRobustUnimodal (quad ⟪x 4, N.vT2⟫ ⟪x 2, N.vT2⟫ ⟪x 0, N.vT2⟫ ⟪x 5, N.vT2⟫))
    (hnd : NoHDNAt (univ.image x) (N.vT2)) : IsRupert (univ.image x) := by
  obtain ⟨-, -, -, h⟩ := NF29.rimThen_k3_T2o N hV3 hh2g hkap hsg hz
  exact h hnd

/-- Certificate form of `NF29.isRupert_k3_Y1p`
(`FEWER-FACES-PROOFS.md` §18.2, §21): the rim at its named view as `RimCertPts`
(or `RimCert`), without the `NoHDNAt` hypotheses, which only enter the corollary. -/
theorem NF29.rimThen_k3_Y1p (N : NF29 x)
    (hb0 : 0 < N.b0)
    (hYs : 0 < N.h0 * N.s + N.a0)
    (hp56 : 0 < N.a2 * N.t - N.b2 * N.s - N.h2 * N.s - N.a2 + N.s)
    (hL36 : 0 < -N.a0 * N.h2 * N.t + N.b2 * N.h0 * N.s + N.h0 * N.h2 * N.s + N.a0 * N.h2)
    (hz : IsRobustUnimodal (quad ⟪x 1, N.vY1⟫ ⟪x 4, N.vY1⟫ ⟪x 6, N.vY1⟫ ⟪x 5, N.vY1⟫)) :
    RimThen (univ.image x) (N.vY1) (quad (x 1) (x 4) (x 6) (x 5))
      (NoHDNAt (univ.image x) (N.vY1)) := by
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have hst : 0 < N.s + N.t - 1 := by linarith [N.hst]
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine vquadσ_both (univ.image x) ({x 0, x 3} : Finset ℝ³) (u := N.vY1) ?_ hσ
    (img29 1) (img29 4) (img29 6) (img29 5)
    (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff])
        (by simp [N.inj.eq_iff]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hz ?_
  · exact nfV_ne_zero N.hD (Or.inr (Or.inr (ne_of_gt (mul_pos N.hh0 N.hs))))
  · simp only [NF29.vY1]; nf29_test N hσD
        (by show 0 < N.h0 * N.s * N.t; linarith [mul_pos (mul_pos (N.hh0) N.hs) N.ht])
  · simp only [NF29.vY1]; nf29_test N hσD (by show 0 < N.h0 * N.s; linarith [mul_pos (N.hh0) N.hs])
  · simp only [NF29.vY1]; nf29_test N hσD
        (by
          show 0 < N.h0 * N.s * N.t + N.h0 * N.s ^ 2 - N.h0 * N.s
          linarith [mul_pos (mul_pos (N.hh0) N.hs) hst])
  · simp only [NF29.vY1]; nf29_test N hσD
        (by show 0 < N.h0 * N.s * N.t; linarith [mul_pos (mul_pos (N.hh0) N.hs) N.ht])
  · simp only [NF29.vY1]; nf29_test N hσD
        (by show 0 < N.h0 * N.s ^ 2; linarith [mul_pos (mul_pos (N.hh0) N.hs) N.hs])
  · simp only [NF29.vY1]; nf29_test N hσD
        (by
          show 0 < N.h0 * N.s * N.t + N.h0 * N.s ^ 2 - N.h0 * N.s
          linarith [mul_pos (mul_pos (N.hh0) N.hs) hst])
  · simp only [NF29.vY1]; nf29_test N hσD (by show 0 < N.h0 * N.s; linarith [mul_pos (N.hh0) N.hs])
  · simp only [NF29.vY1]; nf29_test N hσD
        (by show 0 < N.h0 * N.s ^ 2; linarith [mul_pos (mul_pos (N.hh0) N.hs) N.hs])
  · intro z hz hzM hn0 hn1 hn2 hn3
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · exact absurd (by simp) hzM
    · exact absurd rfl hn0
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [NF29.vY1]; nf29_test N hσD hL36
      · simp only [NF29.vY1]; nf29_test N hσD
            (by
              show 0 < -N.a2 * N.h0 * N.s * N.t + N.b2 * N.h0 * N.s ^ 2 + N.h0 * N.h2 * N.s ^ 2 +
                N.a0 * N.h2 * N.s + N.a0 * N.h2 * N.t - N.b2 * N.h0 * N.s - N.h0 * N.h2 * N.s + N.h0
                * N.s * N.t - N.a0 * N.h2
              linarith [mul_pos (mul_pos (N.hh2) hst) hYs, mul_pos (mul_pos (N.hh0) N.hs) N.d234])
      · simp only [NF29.vY1]; nf29_test N hσD
            (by
              show 0 < N.a2 * N.h0 * N.s * N.t - N.b2 * N.h0 * N.s ^ 2 - N.h0 * N.h2 * N.s ^ 2 -
                N.a2 * N.h0 * N.s + N.h0 * N.s ^ 2
              linarith [mul_pos (mul_pos (N.hh0) N.hs) hp56])
      · simp only [NF29.vY1]; nf29_test N hσD
            (by show 0 < -N.a0 * N.h2 * N.s + N.a2 * N.h0 * N.s; linarith [mul_pos (N.hF5) N.hs])
    · exact absurd (by simp) hzM
    · exact absurd rfl hn1
    · exact absurd rfl hn3
    · exact absurd rfl hn2
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · have hmid := mid_comb (m := x 0) (X := x 5) (Y := x 1) (U := N.vY1)
        (D₀ := -N.a0 * N.s)
            (α := N.a0 * N.b0 * N.s + N.a0 * N.h0 * N.s - N.a0 ^ 2 * N.t - N.a0 * N.s + N.a0 ^ 2)
            (β := N.a0)
        (by linarith [mul_pos (hA0) N.hs]) (by linarith [mul_pos (hA0) N.d035])
        (by
              linarith [mul_pos (hA0) hYs, mul_pos (mul_pos (hA0) N.hs) hb0, mul_pos
                  (mul_pos (hA0) hA0) N.ht])
        (ne_of_lt (by linarith [hA0]))
        (by simp only [NF29.vY1]; nf29_vec N)
      obtain ⟨s, δ, h1, h2, h3, h4⟩ := hmid
      exact ⟨s, δ, h1, h2, h3, Or.inr <| Or.inr <| Or.inr <| h4⟩
    · have hmid := mid_comb (m := x 3) (X := x 6) (Y := x 5) (U := N.vY1)
        (D₀ := N.h0 * N.s ^ 2) (α := N.h0 * N.s ^ 2 + N.a0 * N.s) (β := -N.s)
        (by linarith [mul_pos (mul_pos (N.hh0) N.hs) N.hs]) (by linarith [mul_pos (N.hs) hYs])
        (by linarith [mul_pos (hA0) N.hs])
        (ne_of_lt (by linarith [N.hs]))
        (by simp only [NF29.vY1]; nf29_vec N)
      obtain ⟨s, δ, h1, h2, h3, h4⟩ := hmid
      exact ⟨s, δ, h1, h2, h3, Or.inr <| Or.inr <| Or.inl <| h4⟩

/-- **Test `Y1 = 015/356`, planar** (§21.17): the vertex crossing at `5`, view `(A0 s, h0 s − A0 (1
− t), h0 s)`, rim `(1, 4, 6, 5)` in `H`; `0` a middle over `5–1`, `3` over `6–5`, `2` hidden. -/
theorem NF29.isRupert_k3_Y1p (N : NF29 x)
    (hb0 : 0 < N.b0)
    (hYs : 0 < N.h0 * N.s + N.a0)
    (hp56 : 0 < N.a2 * N.t - N.b2 * N.s - N.h2 * N.s - N.a2 + N.s)
    (hL36 : 0 < -N.a0 * N.h2 * N.t + N.b2 * N.h0 * N.s + N.h0 * N.h2 * N.s + N.a0 * N.h2)
    (hz : IsRobustUnimodal (quad ⟪x 1, N.vY1⟫ ⟪x 4, N.vY1⟫ ⟪x 6, N.vY1⟫ ⟪x 5, N.vY1⟫))
    (hnd : NoHDNAt (univ.image x) (N.vY1)) : IsRupert (univ.image x) := by
  obtain ⟨-, -, -, h⟩ := NF29.rimThen_k3_Y1p N hb0 hYs hp56 hL36 hz
  exact h hnd

/-- Certificate form of `NF29.isRupert_k3_T3s`
(`FEWER-FACES-PROOFS.md` §18.2, §21): the rim at its named view as `RimCertPts`
(or `RimCert`), without the `NoHDNAt` hypotheses, which only enter the corollary. -/
theorem NF29.rimThen_k3_T3s (N : NF29 x)
    (hh2g : 0 < N.h2 - 1)
    (hh0F5 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.h0)
    (hh2F4 : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.h2)
    (hL36n : 0 < N.a0 * N.h2 * N.t - N.b2 * N.h0 * N.s - N.h0 * N.h2 * N.s - N.a0 * N.h2)
    (hW43 : 0 < -N.a0 * N.h2 * N.t + N.b2 * N.h0 * N.s - N.h0 * N.h2 * N.t - N.b2 * N.h0)
    (hAh0 : 0 < -N.a0 - N.h0)
    (hs1g : 0 < N.s - 1)
    (hz : IsRobustUnimodal (quad ⟪x 1, N.vT3⟫ ⟪x 4, N.vT3⟫ ⟪x 3, N.vT3⟫ ⟪x 5, N.vT3⟫)) :
    RimThen (univ.image x) (N.vT3) (quad (x 1) (x 4) (x 3) (x 5))
      (NoHDNAt (univ.image x) (N.vT3)) := by
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine vquadσ_both (univ.image x) ({x 0, x 2} : Finset ℝ³) (u := N.vT3) ?_ hσ
    (img29 1) (img29 4) (img29 3) (img29 5)
    (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff])
        (by simp [N.inj.eq_iff]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hz ?_
  · exact nfV_ne_zero N.hD (Or.inr (Or.inr (ne_of_gt (mul_pos N.hh0 N.hh2))))
  · simp only [NF29.vT3]; nf29_test N hσD (by show 0 < -N.b2 * N.h0; linarith [mul_pos (N.hh0) hB2])
  · simp only [NF29.vT3]; nf29_test N hσD
        (by show 0 < N.h0 * N.h2; linarith [mul_pos (N.hh0) N.hh2])
  · simp only [NF29.vT3]; nf29_test N hσD
        (by
          show 0 < -N.a0 * N.h2 - N.b2 * N.h0 - N.h0 * N.h2
          linarith [hAh0, mul_pos (hh2g) hAh0, mul_pos (N.hh0) hB2])
  · simp only [NF29.vT3]; nf29_test N hσD (by show 0 < -N.b2 * N.h0; linarith [mul_pos (N.hh0) hB2])
  · simp only [NF29.vT3]; nf29_test N hσD
        (by show 0 < -N.a0 * N.h2; linarith [hA0, mul_pos (hA0) hh2g])
  · simp only [NF29.vT3]; nf29_test N hσD
        (by
          show 0 < -N.a0 * N.h2 - N.b2 * N.h0 - N.h0 * N.h2
          linarith [hAh0, mul_pos (hh2g) hAh0, mul_pos (N.hh0) hB2])
  · simp only [NF29.vT3]; nf29_test N hσD
        (by show 0 < N.h0 * N.h2; linarith [mul_pos (N.hh0) N.hh2])
  · simp only [NF29.vT3]; nf29_test N hσD
        (by show 0 < -N.a0 * N.h2; linarith [hA0, mul_pos (hA0) hh2g])
  · intro z hz hzM hn0 hn1 hn2 hn3
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · exact absurd (by simp) hzM
    · exact absurd rfl hn0
    · exact absurd (by simp) hzM
    · exact absurd rfl hn2
    · exact absurd rfl hn1
    · exact absurd rfl hn3
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [NF29.vT3]; nf29_test N hσD
            (by show 0 < N.h0 * N.h2 * N.t; linarith [mul_pos (mul_pos (N.hh0) N.hh2) N.ht])
      · simp only [NF29.vT3]; nf29_test N hσD hW43
      · simp only [NF29.vT3]; nf29_test N hσD hL36n
      · simp only [NF29.vT3]; nf29_test N hσD
            (by
              show 0 < N.h0 * N.h2 * N.s
              linarith [mul_pos (N.hh0) N.hh2, mul_pos (mul_pos (N.hh0) N.hh2) hs1g])
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · have hmid := mid_comb (m := x 0) (X := x 5) (Y := x 1) (U := N.vT3)
        (D₀ := -N.a0 * N.h2) (α := N.a0 * N.b0 * N.h2 - N.a0 * N.b2 * N.h0 - N.a0 * N.h2)
            (β := N.a0)
        (by linarith [hA0, mul_pos (hA0) hh2g]) (by linarith [mul_pos (hA0) hh2F4])
        (by linarith [mul_pos (hA0) N.hF4])
        (ne_of_lt (by linarith [hA0]))
        (by simp only [NF29.vT3]; nf29_vec N)
      obtain ⟨s, δ, h1, h2, h3, h4⟩ := hmid
      exact ⟨s, δ, h1, h2, h3, Or.inr <| Or.inr <| Or.inr <| h4⟩
    · have hmid := mid_comb (m := x 2) (X := x 1) (Y := x 4) (U := N.vT3)
        (D₀ := -N.b2 * N.h0) (α := N.a0 * N.b2 * N.h2 - N.a2 * N.b2 * N.h0) (β := N.b2)
        (by linarith [mul_pos (N.hh0) hB2]) (by linarith [mul_pos (hB2) N.hF5])
        (by linarith [mul_pos (hB2) hh0F5])
        (ne_of_lt (by linarith [hB2]))
        (by simp only [NF29.vT3]; nf29_vec N)
      obtain ⟨s, δ, h1, h2, h3, h4⟩ := hmid
      exact ⟨s, δ, h1, h2, h3, Or.inl <| h4⟩

/-- **Test `T3`** on `S` with `L36 < 0` (§21.19): rim `(1, 4, 3, 5)`; `2` a middle over `1–4`, `0`
over `5–1`, `6` hidden. -/
theorem NF29.isRupert_k3_T3s (N : NF29 x)
    (hh2g : 0 < N.h2 - 1)
    (hh0F5 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.h0)
    (hh2F4 : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.h2)
    (hL36n : 0 < N.a0 * N.h2 * N.t - N.b2 * N.h0 * N.s - N.h0 * N.h2 * N.s - N.a0 * N.h2)
    (hW43 : 0 < -N.a0 * N.h2 * N.t + N.b2 * N.h0 * N.s - N.h0 * N.h2 * N.t - N.b2 * N.h0)
    (hAh0 : 0 < -N.a0 - N.h0)
    (hs1g : 0 < N.s - 1)
    (hz : IsRobustUnimodal (quad ⟪x 1, N.vT3⟫ ⟪x 4, N.vT3⟫ ⟪x 3, N.vT3⟫ ⟪x 5, N.vT3⟫))
    (hnd : NoHDNAt (univ.image x) (N.vT3)) : IsRupert (univ.image x) := by
  obtain ⟨-, -, -, h⟩ := NF29.rimThen_k3_T3s N hh2g hh0F5 hh2F4 hL36n hW43 hAh0 hs1g hz
  exact h hnd

/-- **The pair `P11 = {T1, T3}`** (§21.15 (iv)): the shared diagonal `[1, 3]`; Corollary 13.3. -/
theorem NF29.isRupert_k3_P11 (N : NF29 x)
    (hA2 : 0 < -N.a2)
    (hb0 : 0 < N.b0)
    (hh01 : 0 < -N.h0 + 1)
    (hG5n : 0 < -N.a0 * N.h2 + N.a2 * N.h0 + N.a0 - N.a2)
    (hF45 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0)
    (hh20 : 0 < -N.h0 + N.h2)
    (hth : 0 < -N.a2 * N.t + N.b2 * N.s)
    (hf : 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s - N.b0
          * N.h2 + N.b2 * N.h0)
    (hh2g : 0 < N.h2 - 1)
    (hkap : 0 < -N.a2 - N.h2 + 1)
    (hh0F5 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.h0)
    (hF4h2 : 0 < N.b0 * N.h2 - N.b2 * N.h0 - N.h2)
    (hN : 0 < N.a0 * N.b2 - N.a2 * N.b0 - N.a2 * N.h0 + N.a2)
    (hal : 0 < -N.a0 * N.b0 * N.h2 + N.a0 * N.b2 * N.h0 - N.a0 * N.h0 * N.h2 - N.b0 * N.h0 * N.h2 -
          N.h0 ^ 2 * N.h2 + N.a0 * N.h2 + N.h0 * N.h2)
    (hhF5 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.h0 * N.h2)
    (hz1 : [⟪x 1, N.vT1⟫, ⟪x 2, N.vT1⟫, ⟪x 3, N.vT1⟫, ⟪x 6, N.vT1⟫].Nodup)
    (hz2 : [⟪x 1, N.vT3⟫, ⟪x 4, N.vT3⟫, ⟪x 3, N.vT3⟫, ⟪x 0, N.vT3⟫].Nodup)
    (hnd1 : NoHDNAt (univ.image x) N.vT1)
    (hnd2 : NoHDNAt (univ.image x) N.vT3) : IsRupert (univ.image x) := by
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  have h345_0 : 0 < 1 - N.a0 - N.b0 - N.h0 := by linarith [N.t345_0]
  have h345_2 : 0 < 1 - N.a2 - N.b2 - N.h2 := by linarith [N.t345_2]
  have m11 : SegMeet (x 1) (x 3) (x 2) (x 6) (N.vT1) := segMeet_of_smul'
      (K := N.a0 * N.b2 * N.h2 - N.a0 * N.h2 * N.t - N.a2 * N.b0 * N.h2 + N.a2 * N.h0 * N.t + N.b0 *
        N.h2 * N.s - N.b2 * N.h0 * N.s)
    (s := -N.a0 * N.h2 ^ 2 * N.t + N.a2 * N.h0 * N.h2 * N.t + N.b0 * N.h2 ^ 2 * N.s - N.b2 * N.h0 *
          N.h2 * N.s)
    (t := N.a0 * N.b2 * N.h2 - N.a2 * N.b0 * N.h2)
    (l := N.a2 * N.t - N.b2 * N.s)
    (by
          linarith [hf, hA0, hG5n, hhF5, hh20, hF4h2, N.hF4, mul_pos (hA2) hh20, mul_pos (N.hh2) hN,
              mul_pos (hA2) hF4h2, mul_pos (hB2) N.hF5, mul_pos (N.hh0) hkap, mul_pos
              (mul_pos (hA2) hh01) hh2g])
    (by linarith [mul_pos (N.hh2) hf, mul_pos (N.hh2) N.hF4])
    (by linarith [N.d023, mul_pos (hh20) hth, mul_pos (N.d023) hh2g])
    (by linarith [mul_pos (N.hh2) N.hDD])
    (by linarith [hf, N.hF4])
    (by simp only [NF29.vT1]; nf29_vec N)
  have m12 : SegMeet (x 1) (x 3) (x 2) (x 6) (N.vT3) := segMeet_of_smul'
      (K := N.a0 * N.b2 * N.h2 - N.a0 * N.h2 * N.t - N.a2 * N.b2 * N.h0 + N.b2 * N.h0 * N.s)
    (s := -N.a0 * N.h2 ^ 2 * N.t + N.a2 * N.h0 * N.h2 * N.t)
    (t := N.a0 * N.b2 * N.h2 - N.a2 * N.b2 * N.h0)
    (l := N.a2 * N.t - N.b2 * N.s)
    (by linarith [mul_pos (N.hh0) hth, mul_pos (hB2) N.hF5, mul_pos (N.hF5) N.ht])
    (by linarith [mul_pos (mul_pos (N.hh2) N.hF5) N.ht])
    (by linarith [mul_pos (hth) hh0F5, mul_pos (N.hF5) N.d234])
    (by linarith [mul_pos (hB2) N.hF5])
    (by linarith [mul_pos (N.hh0) hth, mul_pos (N.hF5) N.ht])
    (by simp only [NF29.vT3]; nf29_vec N)
  have m21 : SegMeet (x 1) (x 3) (x 4) (x 0) (N.vT1) := segMeet_of_smul'
      (K := N.a0 * N.b2 * N.h0 - N.a2 * N.b0 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0)
    (s := N.b0 * N.h0 * N.h2 - N.b2 * N.h0 ^ 2)
    (t := N.b0 * N.h2 - N.b2 * N.h0)
    (l := -N.b0)
    (by
          linarith [hhF5, hh20, hF4h2, N.hF5, mul_pos (hb0) hh20, mul_pos (hb0) hh0F5, mul_pos (hA0)
              hF4h2, mul_pos (N.hh0) N.hDD, mul_pos (N.hh0) h345_2])
    (by linarith [mul_pos (N.hh0) N.hF4])
    (by
          linarith [mul_pos (hb0) hh2g, mul_pos (N.hh0) N.hDG4, mul_pos (mul_pos (hb0) hh01) hh01,
              mul_pos (mul_pos (N.hh0) hb0) hh20, mul_pos (mul_pos (N.hh2) hb0) hh01])
    (by linarith [N.hF4])
    (by linarith [mul_pos (N.hh0) N.hDD])
    (by simp only [NF29.vT1]; nf29_vec N)
  have m22 : SegMeet (x 1) (x 3) (x 4) (x 0) (N.vT3) := segMeet_of_smul'
      (K := -N.a0 * N.b0 * N.h2 + N.a0 * N.b2 * N.h0 - N.b2 * N.h0)
    (s := N.b0 * N.h0 * N.h2 - N.b2 * N.h0 ^ 2)
    (t := -N.b2 * N.h0)
    (l := N.b0)
    (by linarith [hF4h2, h345_0, mul_pos (hA0) hF4h2, mul_pos (N.hh0) N.hh2, mul_pos (h345_0) hh2g])
    (by linarith [mul_pos (N.hh0) N.hF4])
    (by
          linarith [hal, h345_0, mul_pos (hA0) hF4h2, mul_pos (hh01) hF4h2, mul_pos (h345_0) hh20,
              mul_pos (mul_pos (h345_0) hh01) hh2g])
    (by linarith [mul_pos (N.hh0) hB2])
    (by
          linarith [hA0, mul_pos (hA0) hh20, mul_pos (hA0) hF4h2, mul_pos (mul_pos (hA0) hh01) hh2g,
              mul_pos (mul_pos (N.hh0) N.hh2) hA0])
    (by simp only [NF29.vT3]; nf29_vec N)
  have eq11 : det3 (N.vT1) (x 3 - x 1) (x 6 - x 2) =
      (N.a0 * N.b2 * N.h2 - N.a0 * N.h2 * N.t - N.a2 * N.b0 * N.h2 + N.a2 * N.h0 * N.t + N.b0 * N.h2
        * N.s - N.b2 * N.h0 * N.s) * det3 N.E₁ N.E₂ N.E₃ := by
    simp only [NF29.vT1]; nf29_simp N; simp only [det3c]; ring
  have pq11 : 0 < N.a0 * N.b2 * N.h2 - N.a0 * N.h2 * N.t - N.a2 * N.b0 * N.h2 + N.a2 * N.h0 * N.t +
      N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s :=
      (by
        linarith [hf, hA0, hG5n, hhF5, hh20, hF4h2, N.hF4, mul_pos (hA2) hh20, mul_pos (N.hh2) hN,
            mul_pos (hA2) hF4h2, mul_pos (hB2) N.hF5, mul_pos (N.hh0) hkap, mul_pos
            (mul_pos (hA2) hh01) hh2g])
  have eq12 : det3 (N.vT3) (x 3 - x 1) (x 6 - x 2) =
      (N.a0 * N.b2 * N.h2 - N.a0 * N.h2 * N.t - N.a2 * N.b2 * N.h0 + N.b2 * N.h0 * N.s) * det3 N.E₁
      N.E₂ N.E₃ := by
    simp only [NF29.vT3]; nf29_simp N; simp only [det3c]; ring
  have pq12 : 0 < N.a0 * N.b2 * N.h2 - N.a0 * N.h2 * N.t - N.a2 * N.b2 * N.h0 + N.b2 * N.h0 * N.s :=
      (by linarith [mul_pos (N.hh0) hth, mul_pos (hB2) N.hF5, mul_pos (N.hF5) N.ht])
  have eq21 : det3 (N.vT1) (x 3 - x 1) (x 0 - x 4) =
      (-N.a0 * N.b2 * N.h0 + N.a2 * N.b0 * N.h0 - N.b0 * N.h2 + N.b2 * N.h0) * det3 N.E₁ N.E₂ N.E₃
      := by
    simp only [NF29.vT1]; nf29_simp N; simp only [det3c]; ring
  have pq21 : -N.a0 * N.b2 * N.h0 + N.a2 * N.b0 * N.h0 - N.b0 * N.h2 + N.b2 * N.h0 < 0 :=
      (by
        linarith [hhF5, hh20, hF4h2, N.hF5, mul_pos (hb0) hh20, mul_pos (hb0) hh0F5, mul_pos (hA0)
            hF4h2, mul_pos (N.hh0) N.hDD, mul_pos (N.hh0) h345_2])
  have eq22 : det3 (N.vT3) (x 3 - x 1) (x 0 - x 4) =
      (-N.a0 * N.b0 * N.h2 + N.a0 * N.b2 * N.h0 - N.b2 * N.h0) * det3 N.E₁ N.E₂ N.E₃ := by
    simp only [NF29.vT3]; nf29_simp N; simp only [det3c]; ring
  have pq22 : 0 < -N.a0 * N.b0 * N.h2 + N.a0 * N.b2 * N.h0 - N.b2 * N.h0 :=
      (by
        linarith [hF4h2, h345_0, mul_pos (hA0) hF4h2, mul_pos (N.hh0) N.hh2, mul_pos (h345_0) hh2g])
  by_cases h1 : DepthSep (x 1) (x 3) (x 2) (x 6) (N.vT1)
  · by_cases h2 : DepthSep (x 1) (x 3) (x 4) (x 0) (N.vT3)
    · exfalso
      exact not_both_depthSep_gen h1 h2 m11 m12 m22 m21
        (det4_neg N.hD eq11 eq12 eq21 eq22
              (mul_neg_of_pos_of_neg (mul_pos pq11 pq12) (mul_neg_of_neg_of_pos pq21 pq22)))
    · exact NF29.isRupert_k3_T3o N hh01 hh20 hth hh2g hh0F5 hF4h2 hN hal hhF5
          (quad_unimodal h2 hz2).isRobustUnimodal hnd2
  · exact NF29.isRupert_k3_T1o N hh01 hF45 hh20 hth hf hh2g (quad_unimodal h1 hz1).isRobustUnimodal
        hnd1

/-- **Lemma 21.16 (Lemma X)**: the pair `{Xa, T2}`; Corollary 13.3. -/
theorem NF29.isRupert_k3_X (N : NF29 x)
    (hA2 : 0 < -N.a2)
    (hb0 : 0 < N.b0)
    (hV3 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (hh01 : 0 < -N.h0 + 1)
    (hG4 : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.b0 - N.b2)
    (hG5n : 0 < -N.a0 * N.h2 + N.a2 * N.h0 + N.a0 - N.a2)
    (hh20 : 0 < -N.h0 + N.h2)
    (hh2g : 0 < N.h2 - 1)
    (hkap : 0 < -N.a2 - N.h2 + 1)
    (hh2F4 : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.h2)
    (hXf : 0 < -N.a0 * N.t + N.b0 * N.s - N.h0 * N.t - N.b0 - N.s + 1)
    (hb01 : 0 < -N.b0 + 1)
    (hsg : 0 < N.a2 * N.t - N.b2 * N.s + N.h2 * N.t - N.a2 - N.h2 - N.t + 1)
    (hXa2 : 0 < -N.a0 * N.b2 + N.a2 * N.b0 + N.b0 * N.h2 - N.b2 * N.h0 - N.a2 - N.b0 - N.h2 + 1)
    (hz1 : [⟪x 5, x 5 - x 0⟫, ⟪x 1, x 5 - x 0⟫, ⟪x 4, x 5 - x 0⟫, ⟪x 3, x 5 - x 0⟫].Nodup)
    (hz2 : [⟪x 4, N.vT2⟫, ⟪x 2, N.vT2⟫, ⟪x 0, N.vT2⟫, ⟪x 5, N.vT2⟫].Nodup)
    (hnd1 : NoHDNAt ((univ.image x).erase (x 0)) (x 5 - x 0))
    (hnd2 : NoHDNAt (univ.image x) N.vT2) : IsRupert (univ.image x) := by
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  have h345_0 : 0 < 1 - N.a0 - N.b0 - N.h0 := by linarith [N.t345_0]
  have h345_2 : 0 < 1 - N.a2 - N.b2 - N.h2 := by linarith [N.t345_2]
  have m11 : SegMeet (x 5) (x 4) (x 1) (x 3) (x 5 - x 0) := segMeet_of_smul' (K := -N.a0 - N.b0 + 1)
    (s := -N.a0)
    (t := N.h0)
    (l := -1)
    (by linarith [hA0, hb01])
    (by linarith [hA0])
    (by linarith [hb01])
    (by linarith [N.hh0])
    (by linarith [h345_0])
    (by nf29_vec N)
  have m12 : SegMeet (x 5) (x 4) (x 1) (x 3) (N.vT2) := segMeet_of_smul'
      (K := -N.a2 - N.b2 - N.h2 + 1)
    (s := -N.a2 - N.h2 + 1)
    (t := 0)
    (l := -1)
    (by linarith [h345_2])
    (by linarith [hkap])
    (by linarith [hB2])
    (le_of_eq (by ring))
    (by linarith [h345_2])
    (by simp only [NF29.vT2]; nf29_vec N)
  have m21 : SegMeet (x 4) (x 0) (x 2) (x 5) (x 5 - x 0) := segMeet_of_smul'
      (K := N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (s := N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (t := N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (l := N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (by linarith [hV3])
    (by linarith [hV3])
    (le_of_eq (by ring))
    (by linarith [hV3])
    (le_of_eq (by ring))
    (by nf29_vec N)
  have m22 : SegMeet (x 4) (x 0) (x 2) (x 5) (N.vT2) := segMeet_of_smul'
      (K := N.a0 * N.b2 * N.h2 - N.a2 * N.b0 * N.h2 - N.b0 * N.h2 ^ 2 + N.b2 * N.h0 * N.h2 - N.a2 *
        N.h0 + N.b0 * N.h2 - N.b2 * N.h0 - N.b2 * N.h2 - N.h0 * N.h2 + N.h0)
    (s := -N.a2 * N.h2 - N.b2 * N.h2 - N.h2 ^ 2 + N.h2)
    (t := N.a0 * N.b2 * N.h2 - N.a2 * N.b0 * N.h2 - N.b0 * N.h2 ^ 2 + N.b2 * N.h0 * N.h2 + N.b0 *
          N.h2 - N.b2 * N.h2)
    (l := -N.a0 * N.h2 + N.a2 * N.h0 - N.b0 * N.h2 + N.b2 * N.h0 - N.h0 + N.h2)
    (by
          linarith [hB2, hV3, h345_2, N.hDG4, mul_pos (hA2) hh01, mul_pos (hb0) hG5n, mul_pos
              (N.hh2) hG4, mul_pos (N.hDD) hh2g, mul_pos (N.hF5) hh2g, mul_pos (N.hh2) N.hDG5,
              mul_pos (mul_pos (N.hh0) hA2) hb0, mul_pos (mul_pos (hb0) hh01) hkap, mul_pos
              (mul_pos (hb0) hh2g) hkap, mul_pos (mul_pos (hA0) hh2g) hb01, mul_pos
              (mul_pos (hh20) hkap) hb01, mul_pos (mul_pos (hh01) hh2g) hh2g, mul_pos
              (mul_pos (hh2g) hh2g) hb01, mul_pos (mul_pos (N.hh0) hA2) hh2g, mul_pos
              (mul_pos (N.hh0) hkap) hb01, mul_pos (mul_pos (h345_2) hh01) hh2g, mul_pos
              (mul_pos (h345_0) hh2g) hh2g, mul_pos (mul_pos (N.hh2) N.hh2) h345_0])
    (by linarith [h345_2, mul_pos (h345_2) hh2g])
    (by linarith [mul_pos (hV3) hkap, mul_pos (h345_2) N.hF5])
    (by linarith [mul_pos (N.hh2) N.hDG4])
    (by linarith [mul_pos (N.hh0) h345_2])
    (by simp only [NF29.vT2]; nf29_vec N)
  have eq11 : det3 (x 5 - x 0) (x 4 - x 5) (x 3 - x 1) = (-N.a0 - N.b0 + 1) * det3 N.E₁ N.E₂ N.E₃ :=
      by
    nf29_simp N; simp only [det3c]; ring
  have pq11 : 0 < -N.a0 - N.b0 + 1 := (by linarith [hA0, hb01])
  have eq12 : det3 (N.vT2) (x 4 - x 5) (x 3 - x 1) = (-N.a2 - N.b2 - N.h2 + 1) * det3 N.E₁ N.E₂ N.E₃
      := by
    simp only [NF29.vT2]; nf29_simp N; simp only [det3c]; ring
  have pq12 : 0 < -N.a2 - N.b2 - N.h2 + 1 := (by linarith [h345_2])
  have eq21 : det3 (x 5 - x 0) (x 0 - x 4) (x 5 - x 2) =
      (-N.a0 * N.h2 + N.a2 * N.h0 - N.b0 * N.h2 + N.b2 * N.h0 - N.h0 + N.h2) * det3 N.E₁ N.E₂ N.E₃
      := by
    nf29_simp N; simp only [det3c]; ring
  have pq21 : -N.a0 * N.h2 + N.a2 * N.h0 - N.b0 * N.h2 + N.b2 * N.h0 - N.h0 + N.h2 < 0 :=
      (by linarith [hV3])
  have eq22 : det3 (N.vT2) (x 0 - x 4) (x 5 - x 2) =
      (N.a0 * N.b2 * N.h2 - N.a2 * N.b0 * N.h2 - N.b0 * N.h2 ^ 2 + N.b2 * N.h0 * N.h2 - N.a2 * N.h0
        + N.b0 * N.h2 - N.b2 * N.h0 - N.b2 * N.h2 - N.h0 * N.h2 + N.h0) * det3 N.E₁ N.E₂ N.E₃ := by
    simp only [NF29.vT2]; nf29_simp N; simp only [det3c]; ring
  have pq22 : 0 < N.a0 * N.b2 * N.h2 - N.a2 * N.b0 * N.h2 - N.b0 * N.h2 ^ 2 + N.b2 * N.h0 * N.h2 -
      N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 - N.b2 * N.h2 - N.h0 * N.h2 + N.h0 :=
      (by
        linarith [hB2, hV3, h345_2, N.hDG4, mul_pos (hA2) hh01, mul_pos (hb0) hG5n, mul_pos (N.hh2)
            hG4, mul_pos (N.hDD) hh2g, mul_pos (N.hF5) hh2g, mul_pos (N.hh2) N.hDG5, mul_pos
            (mul_pos (N.hh0) hA2) hb0, mul_pos (mul_pos (hb0) hh01) hkap, mul_pos
            (mul_pos (hb0) hh2g) hkap, mul_pos (mul_pos (hA0) hh2g) hb01, mul_pos
            (mul_pos (hh20) hkap) hb01, mul_pos (mul_pos (hh01) hh2g) hh2g, mul_pos
            (mul_pos (hh2g) hh2g) hb01, mul_pos (mul_pos (N.hh0) hA2) hh2g, mul_pos
            (mul_pos (N.hh0) hkap) hb01, mul_pos (mul_pos (h345_2) hh01) hh2g, mul_pos
            (mul_pos (h345_0) hh2g) hh2g, mul_pos (mul_pos (N.hh2) N.hh2) h345_0])
  by_cases h1 : DepthSep (x 5) (x 4) (x 1) (x 3) (x 5 - x 0)
  · by_cases h2 : DepthSep (x 4) (x 0) (x 2) (x 5) (N.vT2)
    · exfalso
      exact not_both_depthSep_gen h1 h2 m11 m12 m22 m21
        (det4_neg N.hD eq11 eq12 eq21 eq22
              (mul_neg_of_pos_of_neg (mul_pos pq11 pq12) (mul_neg_of_neg_of_pos pq21 pq22)))
    · exact NF29.isRupert_k3_T2o N hV3 hh2g hkap hsg (quad_unimodal h2 hz2).isRobustUnimodal hnd2
  · exact NF29.isRupert_k3_Xa N hh2F4 hXf hb01 hXa2 (quad_unimodal h1 hz1).isRobustUnimodal hnd1

/-- **Proposition 21.19 (P13)**: the pair `{T3, T2}` on `S` with `L36 < 0`; Corollary 13.3. -/
theorem NF29.isRupert_k3_P13 (N : NF29 x)
    (hV3 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (hh01 : 0 < -N.h0 + 1)
    (hh2g : 0 < N.h2 - 1)
    (hkap : 0 < -N.a2 - N.h2 + 1)
    (hh0F5 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.h0)
    (hh2F4 : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.h2)
    (hsg : 0 < N.a2 * N.t - N.b2 * N.s + N.h2 * N.t - N.a2 - N.h2 - N.t + 1)
    (hL36n : 0 < N.a0 * N.h2 * N.t - N.b2 * N.h0 * N.s - N.h0 * N.h2 * N.s - N.a0 * N.h2)
    (hW43 : 0 < -N.a0 * N.h2 * N.t + N.b2 * N.h0 * N.s - N.h0 * N.h2 * N.t - N.b2 * N.h0)
    (hAh0 : 0 < -N.a0 - N.h0)
    (hs1g : 0 < N.s - 1)
    (hz1 : [⟪x 1, N.vT3⟫, ⟪x 4, N.vT3⟫, ⟪x 3, N.vT3⟫, ⟪x 5, N.vT3⟫].Nodup)
    (hz2 : [⟪x 4, N.vT2⟫, ⟪x 2, N.vT2⟫, ⟪x 0, N.vT2⟫, ⟪x 5, N.vT2⟫].Nodup)
    (hnd1 : NoHDNAt (univ.image x) N.vT3)
    (hnd2 : NoHDNAt (univ.image x) N.vT2) : IsRupert (univ.image x) := by
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  have h345_0 : 0 < 1 - N.a0 - N.b0 - N.h0 := by linarith [N.t345_0]
  have h345_2 : 0 < 1 - N.a2 - N.b2 - N.h2 := by linarith [N.t345_2]
  have m11 : SegMeet (x 1) (x 3) (x 4) (x 5) (N.vT3) := segMeet_of_smul'
      (K := -N.a0 * N.h2 - N.b2 * N.h0)
    (s := N.h0 * N.h2)
    (t := -N.b2 * N.h0)
    (l := 1)
    (by linarith [hA0, mul_pos (hA0) hh2g, mul_pos (N.hh0) hB2])
    (by linarith [mul_pos (N.hh0) N.hh2])
    (by linarith [hAh0, mul_pos (hh2g) hAh0, mul_pos (N.hh0) hB2])
    (by linarith [mul_pos (N.hh0) hB2])
    (by linarith [hA0, mul_pos (hA0) hh2g])
    (by simp only [NF29.vT3]; nf29_vec N)
  have m12 : SegMeet (x 1) (x 3) (x 4) (x 5) (N.vT2) := segMeet_of_smul'
      (K := -N.a2 - N.b2 - N.h2 + 1)
    (s := 0)
    (t := -N.b2)
    (l := 1)
    (by linarith [h345_2])
    (le_of_eq (by ring))
    (by linarith [h345_2])
    (by linarith [hB2])
    (by linarith [hkap])
    (by simp only [NF29.vT2]; nf29_vec N)
  have m21 : SegMeet (x 4) (x 0) (x 2) (x 5) (N.vT3) := segMeet_of_smul'
      (K := N.a0 * N.b0 * N.h2 ^ 2 - N.a0 * N.b2 * N.h0 * N.h2 - N.a2 * N.b0 * N.h0 * N.h2 + N.a2 *
        N.b2 * N.h0 ^ 2 + N.h0 * N.h2)
    (s := N.a0 * N.h2 ^ 2 - N.a2 * N.h0 * N.h2 + N.h0 * N.h2)
    (t := N.a0 * N.b0 * N.h2 ^ 2 - N.a0 * N.b2 * N.h0 * N.h2 - N.a2 * N.b0 * N.h0 * N.h2 + N.a2 *
          N.b2 * N.h0 ^ 2 + N.b0 * N.h0 * N.h2 - N.b2 * N.h0 ^ 2)
    (l := N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (by
          linarith [hh2F4, mul_pos (hV3) hh01, mul_pos (N.hF5) hh2F4, mul_pos (N.hF4) hh0F5, mul_pos
              (mul_pos (N.hh0) N.hh2) hV3, mul_pos (mul_pos (hh01) hh2g) hh0F5, mul_pos
              (mul_pos (N.hh0) N.hh2) hh2F4])
    (by linarith [mul_pos (N.hh2) hh0F5])
    (by linarith [mul_pos (N.hF5) hh2F4])
    (by linarith [mul_pos (N.hF4) hh0F5])
    (by linarith [mul_pos (N.hh0) hh2F4])
    (by simp only [NF29.vT3]; nf29_vec N)
  have m22 : SegMeet (x 4) (x 0) (x 2) (x 5) (N.vT2) := segMeet_of_smul'
      (K := N.a0 * N.b2 * N.h2 - N.a2 * N.b0 * N.h2 - N.b0 * N.h2 ^ 2 + N.b2 * N.h0 * N.h2 - N.a2 *
        N.h0 + N.b0 * N.h2 - N.b2 * N.h0 - N.b2 * N.h2 - N.h0 * N.h2 + N.h0)
    (s := -N.a2 * N.h2 - N.b2 * N.h2 - N.h2 ^ 2 + N.h2)
    (t := N.a0 * N.b2 * N.h2 - N.a2 * N.b0 * N.h2 - N.b0 * N.h2 ^ 2 + N.b2 * N.h0 * N.h2 + N.b0 *
          N.h2 - N.b2 * N.h2)
    (l := -N.a0 * N.h2 + N.a2 * N.h0 - N.b0 * N.h2 + N.b2 * N.h0 - N.h0 + N.h2)
    (by
          linarith [hV3, h345_2, mul_pos (N.hh2) N.hDG5, mul_pos (N.hh2) N.hDG4, mul_pos
              (mul_pos (h345_2) hh01) hh2g, mul_pos (mul_pos (N.hh2) N.hh2) h345_0])
    (by linarith [h345_2, mul_pos (h345_2) hh2g])
    (by linarith [mul_pos (hV3) hkap, mul_pos (hB2) N.hF5, mul_pos (N.hF5) hkap])
    (by linarith [mul_pos (N.hh2) N.hDG4])
    (by linarith [mul_pos (N.hh0) h345_2])
    (by simp only [NF29.vT2]; nf29_vec N)
  have eq11 : det3 (N.vT3) (x 3 - x 1) (x 5 - x 4) = (-N.a0 * N.h2 - N.b2 * N.h0) * det3 N.E₁ N.E₂
      N.E₃ := by
    simp only [NF29.vT3]; nf29_simp N; simp only [det3c]; ring
  have pq11 : 0 < -N.a0 * N.h2 - N.b2 * N.h0 :=
      (by linarith [hA0, mul_pos (hA0) hh2g, mul_pos (N.hh0) hB2])
  have eq12 : det3 (N.vT2) (x 3 - x 1) (x 5 - x 4) = (-N.a2 - N.b2 - N.h2 + 1) * det3 N.E₁ N.E₂ N.E₃
      := by
    simp only [NF29.vT2]; nf29_simp N; simp only [det3c]; ring
  have pq12 : 0 < -N.a2 - N.b2 - N.h2 + 1 := (by linarith [h345_2])
  have eq21 : det3 (N.vT3) (x 0 - x 4) (x 5 - x 2) =
      (-N.a0 * N.b0 * N.h2 ^ 2 + N.a0 * N.b2 * N.h0 * N.h2 + N.a2 * N.b0 * N.h0 * N.h2 - N.a2 * N.b2
        * N.h0 ^ 2 - N.h0 * N.h2) * det3 N.E₁ N.E₂ N.E₃ := by
    simp only [NF29.vT3]; nf29_simp N; simp only [det3c]; ring
  have pq21 : -N.a0 * N.b0 * N.h2 ^ 2 + N.a0 * N.b2 * N.h0 * N.h2 + N.a2 * N.b0 * N.h0 * N.h2 - N.a2
      * N.b2 * N.h0 ^ 2 - N.h0 * N.h2 < 0 :=
      (by
        linarith [hh2F4, mul_pos (hV3) hh01, mul_pos (N.hF5) hh2F4, mul_pos (N.hF4) hh0F5, mul_pos
            (mul_pos (N.hh0) N.hh2) hV3, mul_pos (mul_pos (hh01) hh2g) hh0F5, mul_pos
            (mul_pos (N.hh0) N.hh2) hh2F4])
  have eq22 : det3 (N.vT2) (x 0 - x 4) (x 5 - x 2) =
      (N.a0 * N.b2 * N.h2 - N.a2 * N.b0 * N.h2 - N.b0 * N.h2 ^ 2 + N.b2 * N.h0 * N.h2 - N.a2 * N.h0
        + N.b0 * N.h2 - N.b2 * N.h0 - N.b2 * N.h2 - N.h0 * N.h2 + N.h0) * det3 N.E₁ N.E₂ N.E₃ := by
    simp only [NF29.vT2]; nf29_simp N; simp only [det3c]; ring
  have pq22 : 0 < N.a0 * N.b2 * N.h2 - N.a2 * N.b0 * N.h2 - N.b0 * N.h2 ^ 2 + N.b2 * N.h0 * N.h2 -
      N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 - N.b2 * N.h2 - N.h0 * N.h2 + N.h0 :=
      (by
        linarith [hV3, h345_2, mul_pos (N.hh2) N.hDG5, mul_pos (N.hh2) N.hDG4, mul_pos
            (mul_pos (h345_2) hh01) hh2g, mul_pos (mul_pos (N.hh2) N.hh2) h345_0])
  by_cases h1 : DepthSep (x 1) (x 3) (x 4) (x 5) (N.vT3)
  · by_cases h2 : DepthSep (x 4) (x 0) (x 2) (x 5) (N.vT2)
    · exfalso
      exact not_both_depthSep_gen h1 h2 m11 m12 m22 m21
        (det4_neg N.hD eq11 eq12 eq21 eq22
              (mul_neg_of_pos_of_neg (mul_pos pq11 pq12) (mul_neg_of_neg_of_pos pq21 pq22)))
    · exact NF29.isRupert_k3_T2o N hV3 hh2g hkap hsg (quad_unimodal h2 hz2).isRobustUnimodal hnd2
  · exact NF29.isRupert_k3_T3s N hh2g hh0F5 hh2F4 hL36n hW43 hAh0 hs1g
        (quad_unimodal h1 hz1).isRobustUnimodal hnd1
/-- Certificate form of `NF29.isRupert_k3_Y1q`
(`FEWER-FACES-PROOFS.md` §18.2, §21): the rim at its named view as `RimCertPts`
(or `RimCert`), without the `NoHDNAt` hypotheses, which only enter the corollary. -/
theorem NF29.rimThen_k3_Y1q (N : NF29 x)
    (hb0 : 0 < N.b0)
    (hV3 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (hh01 : 0 < -N.h0 + 1)
    (hh2g : 0 < N.h2 - 1)
    (hkap : 0 < -N.a2 - N.h2 + 1)
    (hh0F5 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.h0)
    (hb01 : 0 < -N.b0 + 1)
    (hAs : 0 < -N.h0 * N.s - N.a0)
    (hL36 : 0 < -N.a0 * N.h2 * N.t + N.b2 * N.h0 * N.s + N.h0 * N.h2 * N.s + N.a0 * N.h2)
    (hAh0 : 0 < -N.a0 - N.h0)
    (hs1g : 0 < N.s - 1)
    (hz : IsRobustUnimodal (quad ⟪x 5, N.vY1⟫ ⟪x 1, N.vY1⟫ ⟪x 4, N.vY1⟫ ⟪x 3, N.vY1⟫)) :
    RimThen (univ.image x) (N.vY1) (quad (x 5) (x 1) (x 4) (x 3))
      (NoHDNAt (univ.image x) (N.vY1)) := by
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  have h345_0 : 0 < 1 - N.a0 - N.b0 - N.h0 := by linarith [N.t345_0]
  have hst : 0 < N.s + N.t - 1 := by linarith [N.hst]
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine vquadσ_both (univ.image x) ({x 0, x 6} : Finset ℝ³) (u := N.vY1) ?_ hσ
    (img29 5) (img29 1) (img29 4) (img29 3)
    (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff])
        (by simp [N.inj.eq_iff]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hz ?_
  · exact nfV_ne_zero N.hD (Or.inr (Or.inr (ne_of_gt (mul_pos N.hh0 N.hs))))
  · simp only [NF29.vY1]; nf29_test N hσD (by show 0 < N.h0 * N.s; linarith [mul_pos (N.hh0) N.hs])
  · simp only [NF29.vY1]; nf29_test N hσD
        (by show 0 < -N.a0 * N.s; linarith [hA0, mul_pos (hA0) hs1g])
  · simp only [NF29.vY1]; nf29_test N hσD
        (pos_of_mul_pos_r N.hh2 (by
            show 0 < (-N.a0 * N.t + N.h0 * N.s + N.a0) * (N.h2)
            linarith [hL36, mul_pos (mul_pos (N.hh0) hB2) N.hs]))
  · simp only [NF29.vY1]; nf29_test N hσD (by show 0 < N.h0 * N.s; linarith [mul_pos (N.hh0) N.hs])
  · simp only [NF29.vY1]; nf29_test N hσD
        (by show 0 < -N.a0 * N.s - N.a0 * N.t + N.a0; linarith [mul_pos (hA0) hst])
  · simp only [NF29.vY1]; nf29_test N hσD
        (pos_of_mul_pos_r N.hh2 (by
            show 0 < (-N.a0 * N.t + N.h0 * N.s + N.a0) * (N.h2)
            linarith [hL36, mul_pos (mul_pos (N.hh0) hB2) N.hs]))
  · simp only [NF29.vY1]; nf29_test N hσD
        (by show 0 < -N.a0 * N.s; linarith [hA0, mul_pos (hA0) hs1g])
  · simp only [NF29.vY1]; nf29_test N hσD
        (by show 0 < -N.a0 * N.s - N.a0 * N.t + N.a0; linarith [mul_pos (hA0) hst])
  · intro z hz hzM hn0 hn1 hn2 hn3
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · exact absurd (by simp) hzM
    · exact absurd rfl hn1
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [NF29.vY1]; nf29_test N hσD
            (by show 0 < -N.a0 * N.h2 * N.s + N.a2 * N.h0 * N.s; linarith [mul_pos (N.hF5) N.hs])
      · simp only [NF29.vY1]; nf29_test N hσD hL36
      · simp only [NF29.vY1]; nf29_test N hσD
            (pos_of_mul_pos_r N.hh2 (by
                show 0 < (N.a0 * N.a2 * N.t - N.a0 * N.b2 * N.s + N.a0 * N.h2 * N.t - N.a2 * N.h0 *
                    N.s - N.b2 * N.h0 * N.s - N.h0 * N.h2 * N.s - N.a0 * N.a2 - N.a0 * N.h2 - N.a0 *
                    N.t + N.h0 * N.s + N.a0) * (N.h2)
                linarith
                  [mul_pos (hB2) hh0F5, mul_pos (hkap) hL36, mul_pos (mul_pos (hB2) hh0F5) hs1g]))
      · simp only [NF29.vY1]; nf29_test N hσD
            (by
              show 0 < -N.a0 * N.a2 * N.t + N.a0 * N.b2 * N.s + N.a0 * N.h2 * N.s + N.a0 * N.a2 -
                N.a0 * N.s
              linarith [mul_pos (N.hDG5) N.hs, mul_pos (N.d035) hkap, mul_pos (N.d035) hh2g])
    · exact absurd rfl hn3
    · exact absurd rfl hn2
    · exact absurd rfl hn0
    · exact absurd (by simp) hzM
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · have hmid := mid_comb (m := x 0) (X := x 5) (Y := x 1) (U := N.vY1)
        (D₀ := -N.a0 * N.s)
            (α := N.a0 * N.b0 * N.s + N.a0 * N.h0 * N.s - N.a0 ^ 2 * N.t - N.a0 * N.s + N.a0 ^ 2)
            (β := N.a0)
        (by linarith [hA0, mul_pos (hA0) hs1g]) (by linarith [mul_pos (hA0) N.d035])
        (by
              linarith [(pos_of_mul_pos_r N.hh0 (by
                      show 0 < (-N.a0 * N.b0 * N.s - N.a0 * N.h0 * N.s + N.a0 ^ 2 * N.t - N.a0 ^ 2)
                        * (N.h0)
                      linarith [mul_pos (hL36) hAh0, mul_pos (N.hh0) hL36, mul_pos
                          (mul_pos (hA0) N.hs) hV3, mul_pos (mul_pos (hA0) N.hF5) hb0, mul_pos
                          (mul_pos (hA0) N.hF5) hh01, mul_pos (mul_pos (hA0) N.hF5) hs1g, mul_pos
                          (mul_pos (hA0) N.d035) hh01, mul_pos (mul_pos (N.hF5) hb01) hAh0, mul_pos
                          (mul_pos (hA0) N.d035) hh2g, mul_pos (mul_pos (N.hh0) N.hh0) N.hF5,
                          mul_pos (mul_pos (N.hh0) h345_0) N.hF5]))])
        (ne_of_lt (by linarith [hA0]))
        (by simp only [NF29.vY1]; nf29_vec N)
      obtain ⟨s, δ, h1, h2, h3, h4⟩ := hmid
      exact ⟨s, δ, h1, h2, h3, Or.inl <| h4⟩
    · have hmid := mid_comb (m := x 6) (X := x 3) (Y := x 5) (U := N.vY1)
        (D₀ := -N.a0 * N.s) (α := -N.h0 * N.s ^ 2 - N.a0 * N.s) (β := N.s)
        (by linarith [hA0, mul_pos (hA0) hs1g]) (by linarith [hAs, mul_pos (hAs) hs1g])
        (by linarith [mul_pos (mul_pos (N.hh0) N.hs) N.hs])
        (ne_of_gt (by linarith [N.hs]))
        (by simp only [NF29.vY1]; nf29_vec N)
      obtain ⟨s, δ, h1, h2, h3, h4⟩ := hmid
      exact ⟨s, δ, h1, h2, h3, Or.inr <| Or.inr <| Or.inr <| h4⟩

/-- **Test `Y1 = 015/356`** on `S` with `L36 > 0` (§21.21): rim `(5, 1, 4, 3)`; `0` a middle over
`5–1`, `6` over `3–5`, `2` hidden. -/
theorem NF29.isRupert_k3_Y1q (N : NF29 x)
    (hb0 : 0 < N.b0)
    (hV3 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (hh01 : 0 < -N.h0 + 1)
    (hh2g : 0 < N.h2 - 1)
    (hkap : 0 < -N.a2 - N.h2 + 1)
    (hh0F5 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.h0)
    (hb01 : 0 < -N.b0 + 1)
    (hAs : 0 < -N.h0 * N.s - N.a0)
    (hL36 : 0 < -N.a0 * N.h2 * N.t + N.b2 * N.h0 * N.s + N.h0 * N.h2 * N.s + N.a0 * N.h2)
    (hAh0 : 0 < -N.a0 - N.h0)
    (hs1g : 0 < N.s - 1)
    (hz : IsRobustUnimodal (quad ⟪x 5, N.vY1⟫ ⟪x 1, N.vY1⟫ ⟪x 4, N.vY1⟫ ⟪x 3, N.vY1⟫))
    (hnd : NoHDNAt (univ.image x) (N.vY1)) : IsRupert (univ.image x) := by
  obtain ⟨-, -, -, h⟩ := NF29.rimThen_k3_Y1q N hb0 hV3 hh01 hh2g hkap hh0F5 hb01 hAs hL36 hAh0 hs1g
      hz
  exact h hnd

/-- Certificate form of `NF29.isRupert_k3_Y2`
(`FEWER-FACES-PROOFS.md` §18.2, §21): the rim at its named view as `RimCertPts`
(or `RimCert`), without the `NoHDNAt` hypotheses, which only enter the corollary. -/
theorem NF29.rimThen_k3_Y2 (N : NF29 x)
    (hb0 : 0 < N.b0)
    (hV3 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (hh01 : 0 < -N.h0 + 1)
    (hh20 : 0 < -N.h0 + N.h2)
    (hh2g : 0 < N.h2 - 1)
    (hb01 : 0 < -N.b0 + 1)
    (hW43 : 0 < -N.a0 * N.h2 * N.t + N.b2 * N.h0 * N.s - N.h0 * N.h2 * N.t - N.b2 * N.h0)
    (hs1g : 0 < N.s - 1)
    (hz : IsRobustUnimodal (quint ⟪x 6, (x 6 - x 4)⟫ ⟪x 3, (x 6 - x 4)⟫ ⟪x 2, (x 6 - x 4)⟫ ⟪x 0,
            (x 6 - x 4)⟫ ⟪x 5, (x 6 - x 4)⟫)) :
    RimThen (univ.image x) (x 6 - x 4) (quint (x 6) (x 3) (x 2) (x 0) (x 5))
      (NoHDNAt ((univ.image x).erase (x 4)) ((x 6 - x 4))) := by
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  have h345_0 : 0 < 1 - N.a0 - N.b0 - N.h0 := by linarith [N.t345_0]
  have hst : 0 < N.s + N.t - 1 := by linarith [N.hst]
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine equintσ_both (univ.image x) ({x 1} : Finset ℝ³) (u := (x 6 - x 4)) ?_ hσ (h := 1)
      one_ne_zero
    (by module) (img29 4)
    (img29 6) (img29 3) (img29 2) (img29 0) (img29 5)
    (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff])
        (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) ?_ ?_ hz ?_
  · exact sub_ne_zero.mpr (N.inj.ne (by decide))
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · nf29_test N hσD N.d234
    · nf29_test N hσD (by
            show 0 < -N.a0 * N.t + N.b0 * N.s - N.h0 * N.t - N.b0 + N.t
            linarith [mul_pos (hst) hb0, mul_pos (h345_0) N.ht])
    · nf29_test N hσD hst
    · nf29_test N hσD (by
            show 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s
              + N.a0 * N.t - N.a2 * N.t - N.b0 * N.h2 - N.b0 * N.s + N.b2 * N.h0 + N.b2 * N.s + N.b0
              - N.b2
            linarith [mul_pos (N.d234) hh01, mul_pos (mul_pos (hst) hb0) hh2g, mul_pos
                (mul_pos (h345_0) N.ht) hh2g])
    · nf29_test N hσD (by
            show 0 < -N.a2 * N.t + N.b2 * N.s + N.h2 * N.s - N.b2 - N.h2 - N.s + 1
            linarith [N.d234, mul_pos (hst) hh2g])
    · nf29_test N hσD N.d234
    · nf29_test N hσD (by
            show 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s
              - N.b0 * N.h2 + N.b2 * N.h0 + N.h0 * N.s - N.h2 * N.s - N.h0 + N.h2
            linarith [mul_pos (hV3) hs1g, mul_pos (N.hF5) hst])
    · nf29_test N hσD (by
            show 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s
              - N.b0 * N.h2 + N.b2 * N.h0 - N.h0 * N.t + N.h2 * N.t
            linarith [mul_pos (hst) hh2g, mul_pos (hV3) hs1g, mul_pos (hb0) hs1g, mul_pos (N.hF5)
                hst, mul_pos (N.hF5) N.ht, mul_pos (mul_pos (hst) hb0) hh20, mul_pos
                (mul_pos (N.ht) hb0) hh01, mul_pos (mul_pos (hst) hh01) hb01, mul_pos
                (mul_pos (N.ht) hh20) hb01, mul_pos (mul_pos (N.hh0) hB2) hs1g])
    · nf29_test N hσD (by
            show 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s
              + N.a0 * N.t - N.a2 * N.t - N.b0 * N.h2 - N.b0 * N.s + N.b2 * N.h0 + N.b2 * N.s + N.b0
              - N.b2
            linarith [mul_pos (N.d234) hh01, mul_pos (mul_pos (hst) hb0) hh2g, mul_pos
                (mul_pos (h345_0) N.ht) hh2g])
    · nf29_test N hσD (by show 0 < N.h0 * N.s + N.h0 * N.t - N.h0; linarith [mul_pos (N.hh0) hst])
    · nf29_test N hσD (pos_of_mul_pos_r N.hh2
            (by
              show 0 < (-N.a0 * N.t + N.b0 * N.s + N.h0 * N.s - N.b0 - N.h0 - N.s + 1) * (N.h2)
              linarith [hW43, mul_pos (hV3) hs1g, mul_pos (N.hF5) hs1g, mul_pos
                  (mul_pos (N.hh0) hh2g) hs1g, mul_pos (mul_pos (N.hh0) N.hh2) N.ht]))
    · nf29_test N hσD (by
            show 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s
              - N.b0 * N.h2 + N.b2 * N.h0 + N.h0 * N.s - N.h2 * N.s - N.h0 + N.h2
            linarith [mul_pos (hV3) hs1g, mul_pos (N.hF5) hst])
    · nf29_test N hσD hst
    · nf29_test N hσD (by show 0 < N.h2 * N.s + N.h2 * N.t - N.h2; linarith [mul_pos (N.hh2) hst])
    · nf29_test N hσD (by show 0 < N.h0 * N.s + N.h0 * N.t - N.h0; linarith [mul_pos (N.hh0) hst])
  · intro z hz hzM hzw hn0 hn1 hn2 hn3 hn4
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · exact absurd rfl hn3
    · exact absurd (by simp) hzM
    · exact absurd rfl hn2
    · exact absurd rfl hn1
    · exact absurd rfl hzw
    · exact absurd rfl hn4
    · exact absurd rfl hn0
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    subst hm
    have hmid := mid_comb (m := x 1) (X := x 5) (Y := x 6) (U := (x 6 - x 4))
      (D₀ := N.s + N.t - 1) (α := N.s - 1) (β := -N.s)
      (by linarith [hst]) (by linarith [hs1g])
      (by linarith [N.ht])
      (ne_of_lt (by linarith [N.hs]))
      (by nf29_vec N)
    obtain ⟨s, δ, h1, h2, h3, h4⟩ := hmid
    exact ⟨x 6, s, δ, Or.inl rfl, h1, h2, h3, Or.inr h4⟩

/-- **Test `Y2 = 1456/346-4`** (§21.20): the edge crossing along `46` (apex `6`, view `6 − 4`), rim
`(6, 3, 2, 0, 5)`; `1` a middle over `5–6`. -/
theorem NF29.isRupert_k3_Y2 (N : NF29 x)
    (hb0 : 0 < N.b0)
    (hV3 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (hh01 : 0 < -N.h0 + 1)
    (hh20 : 0 < -N.h0 + N.h2)
    (hh2g : 0 < N.h2 - 1)
    (hb01 : 0 < -N.b0 + 1)
    (hW43 : 0 < -N.a0 * N.h2 * N.t + N.b2 * N.h0 * N.s - N.h0 * N.h2 * N.t - N.b2 * N.h0)
    (hs1g : 0 < N.s - 1)
    (hz : IsRobustUnimodal (quint ⟪x 6, (x 6 - x 4)⟫ ⟪x 3, (x 6 - x 4)⟫ ⟪x 2, (x 6 - x 4)⟫ ⟪x 0,
            (x 6 - x 4)⟫ ⟪x 5, (x 6 - x 4)⟫))
    (hnd : NoHDNAt ((univ.image x).erase (x 4)) ((x 6 - x 4))) : IsRupert (univ.image x) := by
  obtain ⟨-, -, -, h⟩ := NF29.rimThen_k3_Y2 N hb0 hV3 hh01 hh20 hh2g hb01 hW43 hs1g hz
  exact h hnd

/-- **The pattern argument of Lemma 21.20 for `Y2`** in reals: with `q = ⟪u, u⟫ > 0`,
`w = ⟪u, u1⟫ > 0`, the cone identities (Y2-1), (Y2-2), (Y5c) with positive coefficients and
`w = g1 (z6 − z3) + g2 (z6 − z5)` (`g1, g2 > 0`), no two-peaked pattern of `(6, 3, 2, 0, 5)`
survives. -/
theorem k3_Y2_core {z6 z3 z2 z0 z5 q w c10 c11 c12 c13 c20 c21 c22 c23 c50 c51 c52 c53 g1 g2 : ℝ}
    (hinj : Function.Injective (quint z6 z3 z2 z0 z5)) (hq : 0 < q) (hw : 0 < w)
    (p10 : 0 < c10) (p11 : 0 < c11) (p12 : 0 < c12) (p13 : 0 < c13)
    (p20 : 0 < c20) (p21 : 0 < c21) (p22 : 0 < c22) (p23 : 0 < c23)
    (p50 : 0 < c50) (p51 : 0 < c51) (p52 : 0 < c52) (p53 : 0 < c53) (hg1 : 0 < g1) (hg2 : 0 < g2)
    (i21 : c10 * q + c11 * (z6 - z3) + c12 * (z0 - z2) + c13 * (z0 - z5) = 0)
    (i22 : c20 * q + c21 * (z6 - z3) + c22 * (z2 - z3) + c23 * (z2 - z0) = 0)
    (i5c : c50 * (z3 - z2) + c51 * (z0 - z2) + c52 * (z0 - z5) + c53 * w = 0)
    (ic : w = g1 * (z6 - z3) + g2 * (z6 - z5)) :
    IsCyclicUnimodal (quint z6 z3 z2 z0 z5) := by
  refine quint_unimodal_of hinj ?_ ?_ ?_ ?_ ?_
  · intro k1 k2 k3 k4
    nlinarith [mul_pos p20 hq, mul_pos p21 (sub_pos.mpr k2), mul_pos p22 (sub_pos.mpr k3),
      mul_pos p23 (sub_pos.mpr k4)]
  · intro k1 k2 k3 k4
    nlinarith [mul_pos p10 hq, mul_pos p11 (sub_pos.mpr k2), mul_pos p12 (sub_pos.mpr k3),
      mul_pos p13 (sub_pos.mpr k4)]
  · intro k1 k2 k3 k4
    nlinarith [mul_pos p50 (sub_pos.mpr k2), mul_pos p51 (sub_pos.mpr k3),
      mul_pos p52 (sub_pos.mpr k4), mul_pos p53 hw]
  · intro k1 k2 k3 k4
    nlinarith [mul_pos hg1 (sub_pos.mpr k1), mul_pos hg2 (sub_pos.mpr k4)]
  · intro k1 k2 k3 k4
    rcases le_or_gt z6 z3 with k5 | k5
    · nlinarith [mul_nonneg hg1.le (sub_nonneg.mpr k5), mul_pos hg2 (sub_pos.mpr k4)]
    · nlinarith [mul_pos p20 hq, mul_pos p21 (sub_pos.mpr k5), mul_pos p22 (sub_pos.mpr k1),
        mul_pos p23 (sub_pos.mpr k2)]


set_option maxHeartbeats 2000000 in
/-- **Lemma 21.20 (Y′) with Proposition 21.21**: on `S` with `L36 > 0`, the vertex crossing
`Y1 = 015/356` (rim `(5, 1, 4, 3)`) or the edge crossing `Y2 = 1456/346-4` (rim
`(6, 3, 2, 0, 5)`) is unimodal.  `Y1`'s diagonals cross along its view with `d − e = λ u1`,
`λ > 0`, so `Y1` fails only with `{5, 4}` above `{1, 3}`, and then `⟪6 − 4, u1⟫ > 0`
(`6 − 4 = (s − 1)(4 − 1) + t (5 − 1)`).  Every two-peaked pattern of `Y2` contains one of
`{6 > 3, 0 > 2, 0 > 5}` (excluded by the cone fact (Y2-1)), `{6 > 3, 2 > 3, 2 > 0}` ((Y2-2)),
`{3 > 6, 5 > 6}` (`u1 = h0 s (6 − 3) + (A0 − h0 s)(6 − 5)` gives `⟪6 − 4, u1⟫ < 0`) or
`{3 > 2, 0 > 2, 0 > 5}` ((Y5c) gives `⟪6 − 4, u1⟫ < 0`). -/
theorem NF29.isRupert_k3_Yp (N : NF29 x)
    (hb0 : 0 < N.b0)
    (hV3 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (hh01 : 0 < -N.h0 + 1)
    (hG5n : 0 < -N.a0 * N.h2 + N.a2 * N.h0 + N.a0 - N.a2)
    (hh20 : 0 < -N.h0 + N.h2)
    (hh2g : 0 < N.h2 - 1)
    (hkap : 0 < -N.a2 - N.h2 + 1)
    (hh0F5 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.h0)
    (hXfn : 0 < N.a0 * N.t - N.b0 * N.s + N.h0 * N.t + N.b0 + N.s - 1)
    (hb01 : 0 < -N.b0 + 1)
    (hAs : 0 < -N.h0 * N.s - N.a0)
    (hL36 : 0 < -N.a0 * N.h2 * N.t + N.b2 * N.h0 * N.s + N.h0 * N.h2 * N.s + N.a0 * N.h2)
    (hW43 : 0 < -N.a0 * N.h2 * N.t + N.b2 * N.h0 * N.s - N.h0 * N.h2 * N.t - N.b2 * N.h0)
    (hAh0 : 0 < -N.a0 - N.h0)
    (hs1g : 0 < N.s - 1)
    (hc4 : 0 < N.a0 * N.b2 - N.a2 * N.b0 - N.b0 * N.h2 + N.b2 * N.h0 - N.a0 + N.a2 - N.h0 + N.h2)
    (hz1 : [⟪x 5, N.vY1⟫, ⟪x 1, N.vY1⟫, ⟪x 4, N.vY1⟫, ⟪x 3, N.vY1⟫].Nodup)
    (hz2 : [⟪x 6, x 6 - x 4⟫, ⟪x 3, x 6 - x 4⟫, ⟪x 2, x 6 - x 4⟫, ⟪x 0, x 6 - x 4⟫,
      ⟪x 5, x 6 - x 4⟫].Nodup)
    (hnd1 : NoHDNAt (univ.image x) N.vY1)
    (hnd2 : NoHDNAt ((univ.image x).erase (x 4)) (x 6 - x 4)) : IsRupert (univ.image x) := by
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  have h345_0 : 0 < 1 - N.a0 - N.b0 - N.h0 := by linarith [N.t345_0]
  have h345_2 : 0 < 1 - N.a2 - N.b2 - N.h2 := by linarith [N.t345_2]
  have hE35 : 0 < -((N.b0 - 1 + N.h0) * N.a2 - N.a0 * N.b2 + N.a0 * (1 - N.h2)) :=
      by linarith [N.hE35]
  have hst : 0 < N.s + N.t - 1 := by linarith [N.hst]
  have vY21 : (N.a0 * N.h2 * N.t - N.a2 * N.h0 * N.t - N.b0 * N.h2 * N.s + N.b2 * N.h0 * N.s + N.a0
        * N.b2 - N.a2 * N.b0 - N.h0 * N.s + N.h2 * N.s - N.a0 + N.a2) • (x 6 - x 4) +
      (-N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s - N.b0 * N.h2
        + N.b2 * N.h0 + N.h0 * N.s - N.h2 * N.s - N.h0 + N.h2) • (x 6 - x 3) +
      (N.a0 * N.t - N.b0 * N.s + N.h0 * N.t + N.b0 + N.s - 1) • (x 0 - x 2) +
      (-N.a0 * N.t + N.a2 * N.t + N.b0 * N.s - N.b2 * N.s - N.h0 * N.t + N.h2 * N.t - N.b0 + N.b2) •
      (x 0 - x 5) = 0 := by
    nf29_vec N
  have cY210 : 0 < N.a0 * N.h2 * N.t - N.a2 * N.h0 * N.t - N.b0 * N.h2 * N.s + N.b2 * N.h0 * N.s +
      N.a0 * N.b2 - N.a2 * N.b0 - N.h0 * N.s + N.h2 * N.s - N.a0 + N.a2 :=
      (by
        linarith [(pos_of_mul_pos_r hA0 (by
                show 0 < (N.a0 * N.h2 * N.t - N.a2 * N.h0 * N.t - N.b0 * N.h2 * N.s + N.b2 * N.h0 *
                    N.s + N.a0 * N.b2 - N.a2 * N.b0 - N.h0 * N.s + N.h2 * N.s - N.a0 + N.a2) *
                  (-N.a0)
                linarith [mul_pos (hAs) hc4, mul_pos (hV3) hAs, mul_pos (N.hF5) N.d035]))])
  have cY211 : 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s -
      N.b0 * N.h2 + N.b2 * N.h0 + N.h0 * N.s - N.h2 * N.s - N.h0 + N.h2 :=
      (by linarith [mul_pos (hV3) hs1g, mul_pos (N.hF5) hst])
  have cY212 : 0 < N.a0 * N.t - N.b0 * N.s + N.h0 * N.t + N.b0 + N.s - 1 := (by linarith [hXfn])
  have cY213 : 0 < -N.a0 * N.t + N.a2 * N.t + N.b0 * N.s - N.b2 * N.s - N.h0 * N.t + N.h2 * N.t -
      N.b0 + N.b2 := (by
        linarith [(pos_of_mul_pos_r hb01 (by
                show 0 < (-N.a0 * N.t + N.a2 * N.t + N.b0 * N.s - N.b2 * N.s - N.h0 * N.t + N.h2 *
                    N.t - N.b0 + N.b2) * (-N.b0 + 1)
                linarith [mul_pos (N.ht) hc4, mul_pos (hb0) hXfn, mul_pos (hB2) hXfn]))])
  have vY22 : (N.a0 * N.h2 * N.t - N.a2 * N.h0 * N.t - N.b0 * N.h2 * N.s + N.b2 * N.h0 * N.s + N.a0
        * N.b2 - N.a0 * N.t - N.a2 * N.b0 + N.a2 * N.t + N.b0 * N.s - N.b2 * N.s) • (x 6 - x 4) +
      (-N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s + N.a0 * N.t -
        N.a2 * N.t - N.b0 * N.h2 - N.b0 * N.s + N.b2 * N.h0 + N.b2 * N.s + N.b0 - N.b2) •
      (x 6 - x 3) +
      (-N.a0 * N.t + N.a2 * N.t + N.b0 * N.s - N.b2 * N.s - N.h0 * N.t + N.h2 * N.t - N.b0 + N.b2) •
      (x 2 - x 3) + (-N.a2 * N.t + N.b2 * N.s - N.h2 * N.t - N.b2 + N.t) • (x 2 - x 0) = 0 := by
    nf29_vec N
  have cY220 : 0 < N.a0 * N.h2 * N.t - N.a2 * N.h0 * N.t - N.b0 * N.h2 * N.s + N.b2 * N.h0 * N.s +
      N.a0 * N.b2 - N.a0 * N.t - N.a2 * N.b0 + N.a2 * N.t + N.b0 * N.s - N.b2 * N.s :=
      (by linarith [N.d023])
  have cY221 : 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s +
      N.a0 * N.t - N.a2 * N.t - N.b0 * N.h2 - N.b0 * N.s + N.b2 * N.h0 + N.b2 * N.s + N.b0 - N.b2 :=
      (by
        linarith [mul_pos (N.d234) hh01, mul_pos (mul_pos (hst) hb0) hh2g, mul_pos
            (mul_pos (h345_0) N.ht) hh2g])
  have cY222 : 0 < -N.a0 * N.t + N.a2 * N.t + N.b0 * N.s - N.b2 * N.s - N.h0 * N.t + N.h2 * N.t -
      N.b0 + N.b2 := (by
        linarith [(pos_of_mul_pos_r hb01 (by
                show 0 < (-N.a0 * N.t + N.a2 * N.t + N.b0 * N.s - N.b2 * N.s - N.h0 * N.t + N.h2 *
                    N.t - N.b0 + N.b2) * (-N.b0 + 1)
                linarith [mul_pos (N.ht) hc4, mul_pos (hb0) hXfn, mul_pos (hB2) hXfn]))])
  have cY223 : 0 < -N.a2 * N.t + N.b2 * N.s - N.h2 * N.t - N.b2 + N.t := (by linarith [N.d234])
  have vY5c : (N.a0 * N.a2 * N.h0 * N.t + N.a0 * N.b0 * N.h2 * N.s + N.a0 * N.h0 * N.h2 * N.s - N.a0
        ^ 2 * N.h2 * N.t - N.a2 * N.b0 * N.h0 * N.s - N.a2 * N.h0 ^ 2 * N.s - N.a0 * N.a2 * N.h0 -
        N.a0 * N.h2 * N.s + N.a0 ^ 2 * N.h2 + N.a2 * N.h0 * N.s) • (x 3 - x 2) +
      (-N.a0 * N.a2 * N.h0 * N.t - N.a0 * N.b0 * N.h2 * N.s - N.a0 * N.h0 * N.h2 * N.s + N.a0 ^ 2 *
        N.h2 * N.t + N.a2 * N.b0 * N.h0 * N.s + N.a2 * N.h0 ^ 2 * N.s + N.a0 * N.a2 * N.h0 + N.a0 *
        N.b0 * N.s + N.a0 * N.h0 * N.s + N.a0 * N.h2 * N.s - N.a0 ^ 2 * N.h2 - N.a0 ^ 2 * N.t - N.a2
        * N.h0 * N.s - N.a0 * N.s + N.a0 ^ 2) • (x 0 - x 2) +
      (N.a0 * N.a2 * N.h0 * N.t + N.a0 * N.b0 * N.h2 * N.s + N.a0 * N.h0 * N.h2 * N.s - N.a0 ^ 2 *
        N.h2 * N.t - N.a2 * N.b0 * N.h0 * N.s - N.a2 * N.h0 ^ 2 * N.s - N.a0 * N.a2 * N.h0 - N.a0 *
        N.a2 * N.t - N.a0 * N.b0 * N.s + N.a0 * N.b2 * N.s - N.a0 * N.h0 * N.s + N.a0 ^ 2 * N.h2 +
        N.a0 ^ 2 * N.t + N.a2 * N.h0 * N.s + N.a0 * N.a2 - N.a0 ^ 2) • (x 0 - x 5) +
      (N.a0 * N.b2 + N.a0 * N.h2 - N.a2 * N.b0 - N.a2 * N.h0 - N.a0 + N.a2) • N.vY1 = 0 := by
    simp only [NF29.vY1]; nf29_vec N
  have cY5c0 : 0 < N.a0 * N.a2 * N.h0 * N.t + N.a0 * N.b0 * N.h2 * N.s + N.a0 * N.h0 * N.h2 * N.s -
      N.a0 ^ 2 * N.h2 * N.t - N.a2 * N.b0 * N.h0 * N.s - N.a2 * N.h0 ^ 2 * N.s - N.a0 * N.a2 * N.h0
      - N.a0 * N.h2 * N.s + N.a0 ^ 2 * N.h2 + N.a2 * N.h0 * N.s :=
      (by linarith [mul_pos (N.hF5) N.d035])
  have cY5c1 : 0 < -N.a0 * N.a2 * N.h0 * N.t - N.a0 * N.b0 * N.h2 * N.s - N.a0 * N.h0 * N.h2 * N.s +
      N.a0 ^ 2 * N.h2 * N.t + N.a2 * N.b0 * N.h0 * N.s + N.a2 * N.h0 ^ 2 * N.s + N.a0 * N.a2 * N.h0
      + N.a0 * N.b0 * N.s + N.a0 * N.h0 * N.s + N.a0 * N.h2 * N.s - N.a0 ^ 2 * N.h2 - N.a0 ^ 2 * N.t
      - N.a2 * N.h0 * N.s - N.a0 * N.s + N.a0 ^ 2 :=
      (by
        linarith [mul_pos (hXfn) hAh0, mul_pos (N.hF5) hXfn, mul_pos (hh0F5) hXfn, mul_pos (h345_0)
            hAs, mul_pos (N.d035) hh0F5])
  have cY5c2 : 0 < N.a0 * N.a2 * N.h0 * N.t + N.a0 * N.b0 * N.h2 * N.s + N.a0 * N.h0 * N.h2 * N.s -
      N.a0 ^ 2 * N.h2 * N.t - N.a2 * N.b0 * N.h0 * N.s - N.a2 * N.h0 ^ 2 * N.s - N.a0 * N.a2 * N.h0
      - N.a0 * N.a2 * N.t - N.a0 * N.b0 * N.s + N.a0 * N.b2 * N.s - N.a0 * N.h0 * N.s + N.a0 ^ 2 *
      N.h2 + N.a0 ^ 2 * N.t + N.a2 * N.h0 * N.s + N.a0 * N.a2 - N.a0 ^ 2 :=
      (by
        linarith [hc4, mul_pos (N.hs) hV3, mul_pos (N.hh0) hV3, mul_pos (hG5n) hXfn, mul_pos
            (N.d035) hh20, mul_pos (N.hDG5) hs1g, mul_pos (N.d035) hG5n, mul_pos (N.hF5) N.d035,
            mul_pos (mul_pos (hA0) N.hs) hV3, mul_pos (mul_pos (hh01) hs1g) hc4, mul_pos
            (mul_pos (N.hF5) hst) hb0, mul_pos (mul_pos (N.hh0) N.hs) hc4, mul_pos
            (mul_pos (h345_2) hh01) hAs, mul_pos (mul_pos (h345_0) hh2g) hAs, mul_pos
            (mul_pos (h345_0) N.hF5) hst, mul_pos (mul_pos (N.hDG5) N.hs) hh01])
  have cY5c3 : 0 < N.a0 * N.b2 + N.a0 * N.h2 - N.a2 * N.b0 - N.a2 * N.h0 - N.a0 + N.a2 :=
      (by linarith [N.hDG5])
  by_cases h1 : DepthSep (x 5) (x 4) (x 1) (x 3) N.vY1
  · -- `Y1` fails: `{5, 4}` above `{1, 3}`, so `⟪6 − 4, u1⟫ > 0`
    have hK : 0 < -N.a0 * N.s - N.a0 * N.t + N.h0 * N.s + N.a0 := by
      linarith [mul_pos hA0 hst, mul_pos N.hh0 N.hs]
    have hm := meet_of_smul (d₀ := x 5) (d₁ := x 4) (e₀ := x 1) (e₁ := x 3) (v := N.vY1)
      (K := -N.a0 * N.s - N.a0 * N.t + N.h0 * N.s + N.a0) (s := -N.a0 * N.s) (t := N.h0 * N.s)
      (l := -1) hK.ne' (by simp only [NF29.vY1]; nf29_vec N)
    have hsep := depthSep_of_meet (div_pos (by linarith [hA0, mul_pos hA0 hs1g]) hK).le
      ((div_le_one hK).mpr (by
        have : 0 < (-N.a0 * N.t + N.h0 * N.s + N.a0) * N.h2 := by
          linarith [hL36, mul_pos (mul_pos N.hh0 hB2) N.hs]
        nlinarith [N.hh2]))
      (div_pos (mul_pos N.hh0 N.hs) hK).le ((div_le_one hK).mpr (by linarith [mul_pos hA0 hst]))
      hm (div_nonpos_of_nonpos_of_nonneg (by norm_num) hK.le) h1
    have h41 : ⟪x 1, N.vY1⟫ < ⟪x 4, N.vY1⟫ :=
      lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hsep (min_le_right _ _))
    have h51 : ⟪x 1, N.vY1⟫ < ⟪x 5, N.vY1⟫ :=
      lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hsep (min_le_left _ _))
    have v64 : x 6 - x 4 = (N.s - 1) • (x 4 - x 1) + N.t • (x 5 - x 1) := by nf29_vec N
    have hpos : 0 < ⟪N.vY1, x 6 - x 4⟫ := by
      rw [real_inner_comm, v64]
      simp only [inner_add_left, inner_sub_left, real_inner_smul_left]
      linarith only [mul_pos hs1g (sub_pos.mpr h41), mul_pos N.ht (sub_pos.mpr h51)]
    have vc : N.vY1 = (N.h0 * N.s) • (x 6 - x 3) + (-N.a0 - N.h0 * N.s) • (x 6 - x 5) := by
      simp only [NF29.vY1]; nf29_vec N
    have ic : ⟪N.vY1, x 6 - x 4⟫ = N.h0 * N.s * (⟪x 6, x 6 - x 4⟫ - ⟪x 3, x 6 - x 4⟫) +
        (-N.a0 - N.h0 * N.s) * (⟪x 6, x 6 - x 4⟫ - ⟪x 5, x 6 - x 4⟫) := by
      rw [vc]; simp only [inner_add_left, inner_sub_left, real_inner_smul_left]
    have hu : 0 < ⟪x 6, x 6 - x 4⟫ - ⟪x 4, x 6 - x 4⟫ := by
      rw [← inner_sub_left]; exact real_inner_self_pos.mpr (sub_ne_zero.mpr (N.inj.ne (by decide)))
    have i21 := congrArg (fun w => ⟪w, x 6 - x 4⟫) vY21
    have i22 := congrArg (fun w => ⟪w, x 6 - x 4⟫) vY22
    have i5c := congrArg (fun w => ⟪w, x 6 - x 4⟫) vY5c
    simp only [inner_add_left, real_inner_smul_left, inner_zero_left, inner_sub_left] at i21 i22 i5c
    have hY2 := k3_Y2_core (NF16.quint_inj_of_nodup hz2) hu hpos cY210 cY211 cY212 cY213
      cY220 cY221 cY222 cY223 cY5c0 cY5c1 cY5c2 cY5c3 (mul_pos N.hh0 N.hs) hAs
      (by linear_combination i21) (by linear_combination i22) (by linear_combination i5c)
      (by rw [ic]; ring)
    exact NF29.isRupert_k3_Y2 N hb0 hV3 hh01 hh20 hh2g hb01 hW43 hs1g hY2.isRobustUnimodal hnd2
  · exact NF29.isRupert_k3_Y1q N hb0 hV3 hh01 hh2g hkap hh0F5 hb01 hAs hL36 hAh0 hs1g
        (quad_unimodal h1 hz1).isRobustUnimodal hnd1
/-- Certificate form of `NF29.isRupert_k3_C56`
(`FEWER-FACES-PROOFS.md` §18.2, §21): the rim at its named view as `RimCertPts`
(or `RimCert`), without the `NoHDNAt` hypotheses, which only enter the corollary. -/
theorem NF29.rimThen_k3_C56 (N : NF29 x)
    (hA2 : 0 < -N.a2)
    (hV3 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (hthn : 0 < N.a2 * N.t - N.b2 * N.s)
    (ht1 : 0 < -N.t + 1)
    (hfF5 : 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s +
          N.a0 * N.h2 - N.a2 * N.h0)
    (hgG5 : 0 < N.a0 * N.h2 * N.t - N.a2 * N.h0 * N.t - N.b0 * N.h2 * N.s + N.b2 * N.h0 * N.s - N.a0
          * N.h2 - N.a0 * N.t + N.a2 * N.h0 + N.a2 * N.t + N.b0 * N.s - N.b2 * N.s + N.a0 - N.a2)
    (hz₁ : [⟪x 6, (x 5 - x 6)⟫, ⟪x 3, (x 5 - x 6)⟫, ⟪x 2, (x 5 - x 6)⟫, ⟪x 1, (x 5 - x 6)⟫].Nodup)
    (hz₂ : [⟪x 5, (x 5 - x 6)⟫, ⟪x 3, (x 5 - x 6)⟫, ⟪x 2, (x 5 - x 6)⟫, ⟪x 1, (x 5 - x 6)⟫].Nodup) :
    RimCertThen (univ.image x) (x 5 - x 6)
      (NoHDNAt ((univ.image x).erase (x 5)) (x 5 - x 6) ∧
        NoHDNAt ((univ.image x).erase (x 6)) (x 5 - x 6)) := by
  have hst : 0 < N.s + N.t - 1 := by linarith [N.hst]
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine edgePairσ_both (univ.image x) hσ (img29 6) (img29 5) (img29 3) (img29 1) (img29 2)
    ?_ ?_ ?_ ?_ ?_ hz₁ hz₂ ?_
  · nf29_test N hσD (pos_of_mul_pos_r N.hh0
          (by
            show 0 < (N.a2 * N.t - N.b2 * N.s - N.h2 * N.s - N.a2 + N.s) * (N.h0)
            linarith [mul_pos (N.hs) hV3, mul_pos (N.hF5) hst, mul_pos (N.hh2) N.d035]))
  · nf29_test N hσD (by show 0 < N.a2 * N.t - N.b2 * N.s - N.a2; linarith [hA2, hthn])
  · nf29_test N hσD (by show 0 < N.h2 * N.s; linarith [mul_pos (N.hh2) N.hs])
  · nf29_test N hσD N.hs
  · nf29_simp N
    refine nf_E_le rfl rfl ?_
    have hE1 : 0 ≤ N.a2 * N.t - N.b2 * N.s := by
      linarith [hthn]
    have hE2 : N.a2 ≤ 0 := by
      linarith [hA2]
    simp only [det3c]
    linarith [mul_nonpos_of_nonneg_of_nonpos hE1 hE2]
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨?_, ?_, ?_, ?_⟩
      · nf29_test N hσD N.d035
      · nf29_test N hσD hgG5
      · nf29_test N hσD hfF5
      · nf29_test N hσD (by show 0 < N.h0 * N.s; linarith [mul_pos (N.hh0) N.hs])
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
    · exact Or.inr <| Or.inr <| Or.inl rfl
    · obtain ⟨s, δ, h1, h2, h3, h4⟩ := mid_comb' (m := x 4) (X := x 1) (Y := x 6) (U := x 6 - x 5)
        (D₀ := N.s) (α := -N.t + 1) (β := N.t)
        (by linarith [N.hs]) (by linarith [ht1]) (by linarith [hst]) (by linarith [N.ht])
            (by nf29_vec N)
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
          ⟨s, δ, h1, h2, h3, Or.inr <| Or.inl (h4.trans (by module))⟩
    · exact Or.inr <| Or.inl rfl
    · exact Or.inl rfl

/-- **Theorem 21.13, C2 at `56`** (`6 → 5` in `K − 4`, `t < 1`, `θ < α`): Lemma E at the edge `56`
of `K`, far path `1, 2, 3`; `4` a middle, `0` hidden. -/
theorem NF29.isRupert_k3_C56 (N : NF29 x)
    (hA2 : 0 < -N.a2)
    (hV3 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (hthn : 0 < N.a2 * N.t - N.b2 * N.s)
    (ht1 : 0 < -N.t + 1)
    (hfF5 : 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s +
          N.a0 * N.h2 - N.a2 * N.h0)
    (hgG5 : 0 < N.a0 * N.h2 * N.t - N.a2 * N.h0 * N.t - N.b0 * N.h2 * N.s + N.b2 * N.h0 * N.s - N.a0
          * N.h2 - N.a0 * N.t + N.a2 * N.h0 + N.a2 * N.t + N.b0 * N.s - N.b2 * N.s + N.a0 - N.a2)
    (hz₁ : [⟪x 6, (x 5 - x 6)⟫, ⟪x 3, (x 5 - x 6)⟫, ⟪x 2, (x 5 - x 6)⟫, ⟪x 1, (x 5 - x 6)⟫].Nodup)
    (hz₂ : [⟪x 5, (x 5 - x 6)⟫, ⟪x 3, (x 5 - x 6)⟫, ⟪x 2, (x 5 - x 6)⟫, ⟪x 1, (x 5 - x 6)⟫].Nodup)
    (hnd₁ : NoHDNAt ((univ.image x).erase (x 5)) (x 5 - x 6))
    (hnd₂ : NoHDNAt ((univ.image x).erase (x 6)) (x 5 - x 6)) : IsRupert (univ.image x) := by
  exact (NF29.rimThen_k3_C56 N hA2 hV3 hthn ht1 hfF5 hgG5 hz₁ hz₂).2 ⟨hnd₁, hnd₂⟩

/-- Certificate form of `NF29.isRupert_k3_C14`
(`FEWER-FACES-PROOFS.md` §18.2, §21): the rim at its named view as `RimCertPts`
(or `RimCert`), without the `NoHDNAt` hypotheses, which only enter the corollary. -/
theorem NF29.rimThen_k3_C14 (N : NF29 x)
    (hb0 : 0 < N.b0)
    (hG4 : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.b0 - N.b2)
    (hthn : 0 < N.a2 * N.t - N.b2 * N.s)
    (ht1g : 0 < N.t - 1)
    (he0n : 0 < -N.b0 - N.h0 + 1)
    (hz₁ : [⟪x 4, (x 1 - x 4)⟫, ⟪x 6, (x 1 - x 4)⟫, ⟪x 3, (x 1 - x 4)⟫, ⟪x 2, (x 1 - x 4)⟫].Nodup)
    (hz₂ : [⟪x 1, (x 1 - x 4)⟫, ⟪x 6, (x 1 - x 4)⟫, ⟪x 3, (x 1 - x 4)⟫, ⟪x 2, (x 1 - x 4)⟫].Nodup) :
    RimCertThen (univ.image x) (x 1 - x 4)
      (NoHDNAt ((univ.image x).erase (x 1)) (x 1 - x 4) ∧
        NoHDNAt ((univ.image x).erase (x 4)) (x 1 - x 4)) := by
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine edgePairσ_both (univ.image x) hσ (img29 4) (img29 1) (img29 6) (img29 2) (img29 3)
    ?_ ?_ ?_ ?_ ?_ hz₁ hz₂ ?_
  · nf29_test N hσD N.ht
  · nf29_test N hσD (by show 0 < -N.h2 * N.t - N.b2 + N.t; linarith [hthn, N.d234])
  · nf29_test N hσD hB2
  · nf29_test N hσD (by show 0 < N.h2 * N.t; linarith [mul_pos (N.hh2) N.ht])
  · nf29_simp N
    refine nf_E_le rfl rfl ?_
    have hE1 : 0 ≤ -N.a2 * N.t + N.b2 * N.s - N.h2 * N.t - N.b2 + N.t := by
      linarith [N.d234]
    have hE2 : -N.a2 * N.t + N.b2 * N.s ≤ 0 := by
      linarith [hthn]
    simp only [det3c]
    linarith [mul_nonpos_of_nonneg_of_nonpos hE1 hE2]
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨?_, ?_, ?_, ?_⟩
      · nf29_test N hσD (by show 0 < N.h0 * N.t; linarith [mul_pos (N.hh0) N.ht])
      · nf29_test N hσD (by
              show 0 < -N.h0 * N.t - N.b0 + N.t
              linarith [mul_pos (hb0) ht1g, mul_pos (N.ht) he0n])
      · nf29_test N hσD hG4
      · nf29_test N hσD N.hF4
    · exact Or.inr <| Or.inl rfl
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
    · exact Or.inl rfl
    · obtain ⟨s, δ, h1, h2, h3, h4⟩ := mid_comb' (m := x 5) (X := x 1) (Y := x 6) (U := x 1 - x 4)
        (D₀ := N.t) (α := 1) (β := N.s)
        (by linarith [N.ht]) (by norm_num) (by linarith [ht1g]) (by linarith [N.hs]) (by nf29_vec N)
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
          ⟨s, δ, h1, h2, h3, Or.inr <| Or.inr <| Or.inl (h4.trans (by module))⟩
    · exact Or.inr <| Or.inr <| Or.inl rfl

/-- **Theorem 21.13, C2 at `14`** (`4 → 1` in `K − 5`, `t > 1`, `θ < α`): Lemma E at the edge `14`
of `K`, far path `2, 3, 6`; `5` a middle, `0` hidden. -/
theorem NF29.isRupert_k3_C14 (N : NF29 x)
    (hb0 : 0 < N.b0)
    (hG4 : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.b0 - N.b2)
    (hthn : 0 < N.a2 * N.t - N.b2 * N.s)
    (ht1g : 0 < N.t - 1)
    (he0n : 0 < -N.b0 - N.h0 + 1)
    (hz₁ : [⟪x 4, (x 1 - x 4)⟫, ⟪x 6, (x 1 - x 4)⟫, ⟪x 3, (x 1 - x 4)⟫, ⟪x 2, (x 1 - x 4)⟫].Nodup)
    (hz₂ : [⟪x 1, (x 1 - x 4)⟫, ⟪x 6, (x 1 - x 4)⟫, ⟪x 3, (x 1 - x 4)⟫, ⟪x 2, (x 1 - x 4)⟫].Nodup)
    (hnd₁ : NoHDNAt ((univ.image x).erase (x 1)) (x 1 - x 4))
    (hnd₂ : NoHDNAt ((univ.image x).erase (x 4)) (x 1 - x 4)) : IsRupert (univ.image x) := by
  exact (NF29.rimThen_k3_C14 N hb0 hG4 hthn ht1g he0n hz₁ hz₂).2 ⟨hnd₁, hnd₂⟩

/-- Certificate form of `NF29.isRupert_k3_C46`
(`FEWER-FACES-PROOFS.md` §18.2, §21): the rim at its named view as `RimCertPts`
(or `RimCert`), without the `NoHDNAt` hypotheses, which only enter the corollary. -/
theorem NF29.rimThen_k3_C46 (N : NF29 x)
    (hb0 : 0 < N.b0)
    (hG4 : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.b0 - N.b2)
    (hG5n : 0 < -N.a0 * N.h2 + N.a2 * N.h0 + N.a0 - N.a2)
    (hth : 0 < -N.a2 * N.t + N.b2 * N.s)
    (hfn : 0 < N.a0 * N.h2 * N.t - N.a2 * N.h0 * N.t - N.b0 * N.h2 * N.s + N.b2 * N.h0 * N.s + N.b0
          * N.h2 - N.b2 * N.h0)
    (hs1 : 0 < -N.s + 1)
    (hz₁ : [⟪x 4, (x 6 - x 4)⟫, ⟪x 3, (x 6 - x 4)⟫, ⟪x 2, (x 6 - x 4)⟫, ⟪x 1, (x 6 - x 4)⟫].Nodup)
    (hz₂ : [⟪x 6, (x 6 - x 4)⟫, ⟪x 3, (x 6 - x 4)⟫, ⟪x 2, (x 6 - x 4)⟫, ⟪x 1, (x 6 - x 4)⟫].Nodup) :
    RimCertThen (univ.image x) (x 6 - x 4)
      (NoHDNAt ((univ.image x).erase (x 6)) (x 6 - x 4) ∧
        NoHDNAt ((univ.image x).erase (x 4)) (x 6 - x 4)) := by
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  have h345_0 : 0 < 1 - N.a0 - N.b0 - N.h0 := by linarith [N.t345_0]
  have hst : 0 < N.s + N.t - 1 := by linarith [N.hst]
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine edgePairσ_both (univ.image x) hσ (img29 4) (img29 6) (img29 3) (img29 1) (img29 2)
    ?_ ?_ ?_ ?_ ?_ hz₁ hz₂ ?_
  · nf29_test N hσD N.d234
  · nf29_test N hσD (by show 0 < -N.a2 * N.t + N.b2 * N.s - N.b2; linarith [hB2, hth])
  · nf29_test N hσD (by show 0 < N.h2 * N.t; linarith [mul_pos (N.hh2) N.ht])
  · nf29_test N hσD N.ht
  · nf29_simp N
    refine nf_E_le rfl rfl ?_
    have hE1 : 0 ≤ -N.b2 := by
      linarith [hB2]
    have hE2 : N.a2 * N.t - N.b2 * N.s ≤ 0 := by
      linarith [hth]
    simp only [det3c]
    linarith [mul_nonpos_of_nonneg_of_nonpos hE1 hE2]
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨?_, ?_, ?_, ?_⟩
      · nf29_test N hσD (by
              show 0 < -N.a0 * N.t + N.b0 * N.s - N.h0 * N.t - N.b0 + N.t
              linarith [mul_pos (hst) hb0, mul_pos (h345_0) N.ht])
      · nf29_test N hσD (by
              show 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 *
                N.s + N.a0 * N.t - N.a2 * N.t - N.b0 * N.h2 - N.b0 * N.s + N.b2 * N.h0 + N.b2 * N.s
                + N.b0 - N.b2
              linarith [mul_pos (hG4) hs1, mul_pos (N.ht) hG5n])
      · nf29_test N hσD hfn
      · nf29_test N hσD (by show 0 < N.h0 * N.t; linarith [mul_pos (N.hh0) N.ht])
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
    · exact Or.inr <| Or.inr <| Or.inl rfl
    · exact Or.inl rfl
    · obtain ⟨s, δ, h1, h2, h3, h4⟩ := mid_comb' (m := x 5) (X := x 1) (Y := x 6) (U := x 6 - x 4)
        (D₀ := N.t) (α := -N.s + 1) (β := N.s)
        (by linarith [N.ht]) (by linarith [hs1]) (by linarith [hst]) (by linarith [N.hs])
            (by nf29_vec N)
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
          ⟨s, δ, h1, h2, h3, Or.inr <| Or.inr <| Or.inr (h4.trans (by module))⟩
    · exact Or.inr <| Or.inl rfl

/-- **Theorem 21.13, C2 at `46`** (`4 → 6` in `K − 5`, `θ > α`, `f < F4`): Lemma E at the edge `46`
of `K`, far path `1, 2, 3`; `5` a middle, `0` hidden. -/
theorem NF29.isRupert_k3_C46 (N : NF29 x)
    (hb0 : 0 < N.b0)
    (hG4 : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.b0 - N.b2)
    (hG5n : 0 < -N.a0 * N.h2 + N.a2 * N.h0 + N.a0 - N.a2)
    (hth : 0 < -N.a2 * N.t + N.b2 * N.s)
    (hfn : 0 < N.a0 * N.h2 * N.t - N.a2 * N.h0 * N.t - N.b0 * N.h2 * N.s + N.b2 * N.h0 * N.s + N.b0
          * N.h2 - N.b2 * N.h0)
    (hs1 : 0 < -N.s + 1)
    (hz₁ : [⟪x 4, (x 6 - x 4)⟫, ⟪x 3, (x 6 - x 4)⟫, ⟪x 2, (x 6 - x 4)⟫, ⟪x 1, (x 6 - x 4)⟫].Nodup)
    (hz₂ : [⟪x 6, (x 6 - x 4)⟫, ⟪x 3, (x 6 - x 4)⟫, ⟪x 2, (x 6 - x 4)⟫, ⟪x 1, (x 6 - x 4)⟫].Nodup)
    (hnd₁ : NoHDNAt ((univ.image x).erase (x 6)) (x 6 - x 4))
    (hnd₂ : NoHDNAt ((univ.image x).erase (x 4)) (x 6 - x 4)) : IsRupert (univ.image x) := by
  exact (NF29.rimThen_k3_C46 N hb0 hG4 hG5n hth hfn hs1 hz₁ hz₂).2 ⟨hnd₁, hnd₂⟩

/-- **Lemma 21.12 (K3.1, K3.6 (a))** on `K3a ∩ R_G`: if `O` is of class K3a (`a2 < 0 < b0`,
`V > 0`) and none of its E-good `G` edges `0 → 3`, `1 → 4`, `5 → 1` is a quad edge
(Lemma 21.3), then, off `h0 = 1`, `G4 = 0`, `G5 = 0`, `F4 = F5`: `h0 < 1`, `G4 > 0 > G5`,
`F4 > F5` and `h2 > h0`. -/
theorem NF29.k3_facts (N : NF29 x) (ha2 : N.a2 < 0) (hb0 : 0 < N.b0)
    (hV : 0 < N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0))
    (n03 : ¬ (-N.b2 < N.h2 * N.b0 - N.h0 * N.b2 ∧ 1 < N.h0))
    (n14 : ¬ (N.b0 * (1 - N.h2) - N.b2 * (1 - N.h0) < 0 ∧ 1 < N.b0 + N.h0))
    (n51 : ¬ (0 < N.a2 * (1 - N.h0) - N.a0 * (1 - N.h2) ∧ N.a2 + N.h2 < 1))
    (sh0 : N.h0 ≠ 1) (sG4 : N.b0 * (1 - N.h2) - N.b2 * (1 - N.h0) ≠ 0)
    (sG5 : N.a2 * (1 - N.h0) - N.a0 * (1 - N.h2) ≠ 0)
    (sF : N.h2 * N.b0 - N.h0 * N.b2 ≠ N.h0 * N.a2 - N.h2 * N.a0) :
    N.h0 < 1 ∧ 0 < N.b0 * (1 - N.h2) - N.b2 * (1 - N.h0) ∧
      N.a2 * (1 - N.h0) - N.a0 * (1 - N.h2) < 0 ∧
      N.h0 * N.a2 - N.h2 * N.a0 < N.h2 * N.b0 - N.h0 * N.b2 ∧ N.h0 < N.h2 := by
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  have hF5 := N.hF5
  have hA2 : 0 < -N.a2 := by linarith
  -- `h0 < 1`
  have h0 : N.h0 < 1 := by
    rcases lt_or_gt_of_ne sh0 with h | h
    · exact h
    · exfalso
      exact n03 ⟨by nlinarith [mul_pos N.hh2 hb0, mul_pos hB2 (show 0 < N.h0 - 1 by linarith)], h⟩
  -- `G4 > 0`
  have hG4 : 0 < N.b0 * (1 - N.h2) - N.b2 * (1 - N.h0) := by
    have h01 : 0 < 1 - N.h0 := by linarith
    rcases lt_or_gt_of_ne sG4 with h | h
    · exfalso
      have hb : N.b0 + N.h0 ≤ 1 := not_lt.mp fun h' => n14 ⟨h, h'⟩
      -- `G4 < 0` forces `h2 > 1 + B2`; `V > 0`, `F5 > 0` and `h0 ≤ 1 − b0` force `h2 < 1 + B2`
      have hG4n : 0 < -(N.b0 * (1 - N.h2) - N.b2 * (1 - N.h0)) := by linarith
      have hb' : 0 ≤ 1 - N.b0 - N.h0 := by linarith
      linarith [mul_pos (hb0) hF5, mul_pos (hV) hG4n, mul_pos (mul_pos (hb0) hV) h01, mul_pos
            (mul_pos (hB2) hV) h01, mul_pos (mul_pos (hb0) hV) hA2, mul_pos (mul_pos (hb0) hF5) hA2,
            mul_pos (mul_pos (hB2) hF5) h01, mul_pos (mul_pos (hb0) N.hh0) hV, mul_pos
            (mul_pos (N.hh2) hA0) hG4n, mul_nonneg (mul_pos (hB2) hA2).le hb', mul_nonneg
            (mul_pos (hb0) hA2).le hb', mul_pos (mul_pos (N.hh0) N.hh2) hG4n, mul_nonneg
            (mul_pos (hA2) hG4n).le hb', mul_nonneg (mul_pos (hB2) N.hh2).le hb', mul_nonneg
            (mul_pos (hb0) N.hh2).le hb', mul_nonneg (mul_pos (N.hh2) hG4n).le hb']
    · exact h
  -- `G5 < 0`
  have hG5 : N.a2 * (1 - N.h0) - N.a0 * (1 - N.h2) < 0 := by
    rcases lt_or_gt_of_ne sG5 with h | h
    · exact h
    · exfalso
      have ha : 1 ≤ N.a2 + N.h2 := not_lt.mp fun h' => n51 ⟨h, h'⟩
      nlinarith [mul_pos (show 0 < -N.a2 by linarith) (show 0 < 1 - N.h0 by linarith),
        mul_nonneg hA0.le (show (0 : ℝ) ≤ N.h2 - 1 by linarith)]
  have h01 : 0 < 1 - N.h0 := by linarith
  -- `F4 > F5` and `h2 > h0`
  have hF : N.h0 * N.a2 - N.h2 * N.a0 < N.h2 * N.b0 - N.h0 * N.b2 := by
    rcases lt_or_gt_of_ne sF with h | h
    · exfalso
      -- `V > 0` gives `h2 < h0`; then `G5 < 0` gives `A0 < A2`, `F5 > 0` gives `A2 < A0`
      have hFn : 0 < N.h0 * N.a2 - N.h2 * N.a0 - (N.h2 * N.b0 - N.h0 * N.b2) := by linarith
      have hG5n : 0 < -(N.a2 * (1 - N.h0) - N.a0 * (1 - N.h2)) := by linarith
      linarith [mul_pos (hFn) hFn, mul_pos (hB2) hFn, mul_pos (hV) hG5n, mul_pos (mul_pos (hA0) hV)
            h01, mul_pos (mul_pos (hA0) hV) hA2, mul_pos (mul_pos (hB2) hA0) hV, mul_pos
            (mul_pos (hA0) hA2) hFn, mul_pos (mul_pos (hF5) h01) h01, mul_pos (mul_pos (hb0) h01)
            hFn, mul_pos (mul_pos (h01) hA2) hFn, mul_pos (mul_pos (hB2) hA0) hFn, mul_pos
            (mul_pos (N.hh0) hA0) hV, mul_pos (mul_pos (hb0) N.hh2) hG4, mul_pos
            (mul_pos (hB2) N.hh0) hG4, mul_pos (mul_pos (N.hh0) hF5) h01, mul_pos
            (mul_pos (hb0) N.hh0) hFn, mul_pos (mul_pos (N.hh0) hA2) hFn, mul_pos
            (mul_pos (N.hh0) hA2) hG4, mul_pos (mul_pos (N.hh2) h01) hG5n, mul_pos
            (mul_pos (hb0) N.hh2) hG5n, mul_pos (mul_pos (hB2) N.hh0) hG5n, mul_pos
            (mul_pos (N.hh0) hA2) hG5n, mul_pos (mul_pos (N.hh0) N.hh2) hG5n]
    · exact h
  have h01 : 0 < 1 - N.h0 := by linarith
  refine ⟨h0, hG4, hG5, hF, ?_⟩
  by_contra hc; push Not at hc
  have h20 : 0 ≤ N.h0 - N.h2 := by linarith
  have hG5n : 0 < -(N.a2 * (1 - N.h0) - N.a0 * (1 - N.h2)) := by linarith
  have hF : 0 < N.h2 * N.b0 - N.h0 * N.b2 - (N.h0 * N.a2 - N.h2 * N.a0) := by linarith
  linarith [mul_pos (hG5n) hF, mul_pos (hF5) hG4, mul_pos (mul_pos (hF5) h01) hA2, mul_pos
        (mul_pos (N.hh2) hA0) hG5n, mul_nonneg (mul_pos (hb0) hA2).le h20, mul_nonneg
        (mul_pos (hA0) hA2).le h20, mul_nonneg (mul_pos (hB2) hA0).le h20]

/-- The special positions of class K3a used by Theorem 21.22 (§21.5) and the genericity of its
named tests: distinct depths on the rims and no horizontal double normal at the views. -/
structure K3Gen (N : NF29 x) : Prop where
  h0 : N.h0 ≠ 1
  G4 : N.b0 * (1 - N.h2) - N.b2 * (1 - N.h0) ≠ 0
  G5 : N.a2 * (1 - N.h0) - N.a0 * (1 - N.h2) ≠ 0
  F : N.h2 * N.b0 - N.h0 * N.b2 ≠ N.h0 * N.a2 - N.h2 * N.a0
  th : -N.a2 * N.t + N.b2 * N.s ≠ 0
  f : -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s - N.b0 * N.h2 +
      N.b2 * N.h0 ≠ 0
  t1 : N.t ≠ 1
  h21 : N.h2 ≠ 1
  kap : -N.a2 - N.h2 + 1 ≠ 0
  F5h0 : N.h0 * N.a2 - N.h2 * N.a0 ≠ N.h0
  F4h2 : N.h2 * N.b0 - N.h0 * N.b2 ≠ N.h2
  sg : N.a2 * N.t - N.b2 * N.s + N.h2 * N.t - N.a2 - N.h2 - N.t + 1 ≠ 0
  c0 : N.a0 * N.b2 - N.a2 * N.b0 - N.a2 * N.h0 - N.b0 * N.h2 - N.h0 * N.h2 + N.a2 + N.b0 + N.h0 +
      N.h2 - 1 ≠ 0
  Xf : -N.a0 * N.t + N.b0 * N.s - N.h0 * N.t - N.b0 - N.s + 1 ≠ 0
  hs : N.h0 * N.s + N.a0 ≠ 0
  L36 : -N.a0 * N.h2 * N.t + N.b2 * N.h0 * N.s + N.h0 * N.h2 * N.s + N.a0 * N.h2 ≠ 0
  zT1 : [⟪x 1, N.vT1⟫, ⟪x 2, N.vT1⟫, ⟪x 3, N.vT1⟫, ⟪x 6, N.vT1⟫].Nodup
  zT2a : [⟪x 4, N.vT2⟫, ⟪x 3, N.vT2⟫, ⟪x 0, N.vT2⟫, ⟪x 5, N.vT2⟫].Nodup
  zT2b : [⟪x 4, N.vT2⟫, ⟪x 3, N.vT2⟫, ⟪x 5, N.vT2⟫].Nodup
  zT2c : [⟪x 4, N.vT2⟫, ⟪x 3, N.vT2⟫, ⟪x 6, N.vT2⟫].Nodup
  zT2o : [⟪x 4, N.vT2⟫, ⟪x 2, N.vT2⟫, ⟪x 0, N.vT2⟫, ⟪x 5, N.vT2⟫].Nodup
  zT3o : [⟪x 1, N.vT3⟫, ⟪x 4, N.vT3⟫, ⟪x 3, N.vT3⟫, ⟪x 0, N.vT3⟫].Nodup
  zT3p : [⟪x 1, N.vT3⟫, ⟪x 4, N.vT3⟫, ⟪x 6, N.vT3⟫, ⟪x 5, N.vT3⟫].Nodup
  zT3s : [⟪x 1, N.vT3⟫, ⟪x 4, N.vT3⟫, ⟪x 3, N.vT3⟫, ⟪x 5, N.vT3⟫].Nodup
  zXa : [⟪x 5, x 5 - x 0⟫, ⟪x 1, x 5 - x 0⟫, ⟪x 4, x 5 - x 0⟫, ⟪x 3, x 5 - x 0⟫].Nodup
  zY1p : [⟪x 1, N.vY1⟫, ⟪x 4, N.vY1⟫, ⟪x 6, N.vY1⟫, ⟪x 5, N.vY1⟫].Nodup
  zY1q : [⟪x 5, N.vY1⟫, ⟪x 1, N.vY1⟫, ⟪x 4, N.vY1⟫, ⟪x 3, N.vY1⟫].Nodup
  zY2 : [⟪x 6, x 6 - x 4⟫, ⟪x 3, x 6 - x 4⟫, ⟪x 2, x 6 - x 4⟫, ⟪x 0, x 6 - x 4⟫,
    ⟪x 5, x 6 - x 4⟫].Nodup
  zC56a : [⟪x 6, x 5 - x 6⟫, ⟪x 3, x 5 - x 6⟫, ⟪x 2, x 5 - x 6⟫, ⟪x 1, x 5 - x 6⟫].Nodup
  zC56b : [⟪x 5, x 5 - x 6⟫, ⟪x 3, x 5 - x 6⟫, ⟪x 2, x 5 - x 6⟫, ⟪x 1, x 5 - x 6⟫].Nodup
  zC14a : [⟪x 4, x 1 - x 4⟫, ⟪x 6, x 1 - x 4⟫, ⟪x 3, x 1 - x 4⟫, ⟪x 2, x 1 - x 4⟫].Nodup
  zC14b : [⟪x 1, x 1 - x 4⟫, ⟪x 6, x 1 - x 4⟫, ⟪x 3, x 1 - x 4⟫, ⟪x 2, x 1 - x 4⟫].Nodup
  zC46a : [⟪x 4, x 6 - x 4⟫, ⟪x 3, x 6 - x 4⟫, ⟪x 2, x 6 - x 4⟫, ⟪x 1, x 6 - x 4⟫].Nodup
  zC46b : [⟪x 6, x 6 - x 4⟫, ⟪x 3, x 6 - x 4⟫, ⟪x 2, x 6 - x 4⟫, ⟪x 1, x 6 - x 4⟫].Nodup
  ndT1 : NoHDNAt (univ.image x) N.vT1
  ndT2 : NoHDNAt (univ.image x) N.vT2
  ndT3 : NoHDNAt (univ.image x) N.vT3
  ndY1 : NoHDNAt (univ.image x) N.vY1
  ndXa : NoHDNAt ((univ.image x).erase (x 0)) (x 5 - x 0)
  ndY2 : NoHDNAt ((univ.image x).erase (x 4)) (x 6 - x 4)
  ndC56a : NoHDNAt ((univ.image x).erase (x 5)) (x 5 - x 6)
  ndC56b : NoHDNAt ((univ.image x).erase (x 6)) (x 5 - x 6)
  ndC14a : NoHDNAt ((univ.image x).erase (x 1)) (x 1 - x 4)
  ndC14b : NoHDNAt ((univ.image x).erase (x 4)) (x 1 - x 4)
  ndC46a : NoHDNAt ((univ.image x).erase (x 6)) (x 6 - x 4)
  ndC46b : NoHDNAt ((univ.image x).erase (x 4)) (x 6 - x 4)


/-- A planar rim `(1, 4, 6, 5)` in `H` (`6 = 1 + s (4 − 1) + t (5 − 1)`) with distinct depths is
robustly unimodal (`nws4_of_planar_quad_tie`). -/
theorem NF29.planar_unimodal (N : NF29 x) (u : ℝ³)
    (hz : [⟪x 1, u⟫, ⟪x 4, u⟫, ⟪x 6, u⟫, ⟪x 5, u⟫].Nodup) :
    IsRobustUnimodal (quad ⟪x 1, u⟫ ⟪x 4, u⟫ ⟪x 6, u⟫ ⟪x 5, u⟫) := by
  have v6 : x 6 = x 1 + N.s • (x 4 - x 1) + N.t • (x 5 - x 1) := by nf29_vec N
  refine (nws4_of_planar_quad_tie N.hs N.ht N.hst v6 ?_).isRobustUnimodal
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hz
  exact fun h => hz.1.1 h.1


/-- **Theorem 21.13** (`6 ∉ R`): Lemma E at `56`, `14` or `46`. -/
theorem NF29.isRupert_k3_notR (N : NF29 x)
    (hA2 : 0 < -N.a2)
    (hb0 : 0 < N.b0)
    (hV3 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (hh01 : 0 < -N.h0 + 1)
    (hG4 : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.b0 - N.b2)
    (hG5n : 0 < -N.a0 * N.h2 + N.a2 * N.h0 + N.a0 - N.a2)
    (hF45 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0)
    (hh20 : 0 < -N.h0 + N.h2)
    (hnR : ¬ (0 < -N.a2 * N.t + N.b2 * N.s ∧ 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 *
            N.h2 * N.s - N.b2 * N.h0 * N.s - N.b0 * N.h2 + N.b2 * N.h0)) (G : K3Gen N) : IsRupert
        (univ.image x) := by
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  have h345_0 : 0 < 1 - N.a0 - N.b0 - N.h0 := by linarith [N.t345_0]
  have h345_2 : 0 < 1 - N.a2 - N.b2 - N.h2 := by linarith [N.t345_2]
  have hE35 : 0 < -((N.b0 - 1 + N.h0) * N.a2 - N.a0 * N.b2 + N.a0 * (1 - N.h2)) :=
      by linarith [N.hE35]
  have hst : 0 < N.s + N.t - 1 := by linarith [N.hst]
  rcases lt_or_gt_of_ne G.th with hth0 | hth0
  · have hthn : 0 < N.a2 * N.t - N.b2 * N.s := by linarith
    rcases lt_or_gt_of_ne G.t1 with ht0 | ht0
    · have ht1 : 0 < -N.t + 1 := by linarith
      have hfF5 : 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s
          + N.a0 * N.h2 - N.a2 * N.h0 := by
        linarith [mul_pos (N.hF5) hst, mul_pos (N.hs) hF45]
      have hgG5 : 0 < N.a0 * N.h2 * N.t - N.a2 * N.h0 * N.t - N.b0 * N.h2 * N.s + N.b2 * N.h0 * N.s
          - N.a0 * N.h2 - N.a0 * N.t + N.a2 * N.h0 + N.a2 * N.t + N.b0 * N.s - N.b2 * N.s + N.a0 -
          N.a2 := by
        linarith [mul_pos (hG5n) ht1, mul_pos (N.hs) hG4]
      exact N.isRupert_k3_C56 hA2 hV3 hthn ht1 hfF5 hgG5 G.zC56a G.zC56b G.ndC56a G.ndC56b
    · have ht1g : 0 < N.t - 1 := by linarith
      have he0n : 0 < -N.b0 - N.h0 + 1 := by
        by_contra hc; push Not at hc
        have hneg : 0 ≤ N.b0 + N.h0 - 1 := by linarith
        linarith [N.d035, mul_pos (hA0) ht1g, mul_nonneg (N.hs).le hneg]
      exact N.isRupert_k3_C14 hb0 hG4 hthn ht1g he0n G.zC14a G.zC14b G.ndC14a G.ndC14b
  · have hth : 0 < -N.a2 * N.t + N.b2 * N.s := by linarith
    have hfn : 0 < N.a0 * N.h2 * N.t - N.a2 * N.h0 * N.t - N.b0 * N.h2 * N.s + N.b2 * N.h0 * N.s +
        N.b0 * N.h2 - N.b2 * N.h0 := by
      rcases lt_or_gt_of_ne G.f with h | h
      · linarith
      · exact absurd ⟨hth, h⟩ hnR
    have hs1 : 0 < -N.s + 1 := by
      by_contra hc; push Not at hc
      have hneg : 0 ≤ N.s - 1 := by linarith
      linarith [hfn, mul_pos (N.hF5) hst, mul_nonneg (hV3).le hneg, mul_nonneg (hh20).le hneg]
    exact N.isRupert_k3_C46 hb0 hG4 hG5n hth hfn hs1 G.zC46a G.zC46b G.ndC46a G.ndC46b

/-- **Theorem 21.15 (i)** (`6 ∈ R`, `h2 < 1`): `P14 = {T1, T2}`, or `T2` is a triangle. -/
theorem NF29.isRupert_k3_i (N : NF29 x)
    (hA2 : 0 < -N.a2)
    (hb0 : 0 < N.b0)
    (hV3 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (hh01 : 0 < -N.h0 + 1)
    (hG4 : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.b0 - N.b2)
    (hG5n : 0 < -N.a0 * N.h2 + N.a2 * N.h0 + N.a0 - N.a2)
    (hF45 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0)
    (hh20 : 0 < -N.h0 + N.h2)
    (hth : 0 < -N.a2 * N.t + N.b2 * N.s)
        (hf : 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s -
          N.b0 * N.h2 + N.b2 * N.h0)
    (hh21 : 0 < -N.h2 + 1) (G : K3Gen N) : IsRupert (univ.image x) := by
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  have h345_0 : 0 < 1 - N.a0 - N.b0 - N.h0 := by linarith [N.t345_0]
  have h345_2 : 0 < 1 - N.a2 - N.b2 - N.h2 := by linarith [N.t345_2]
  have hE35 : 0 < -((N.b0 - 1 + N.h0) * N.a2 - N.a0 * N.b2 + N.a0 * (1 - N.h2)) :=
      by linarith [N.hE35]
  have hst : 0 < N.s + N.t - 1 := by linarith [N.hst]
  rcases lt_or_gt_of_ne G.sg with hs0 | hs0
  · have hsg : 0 < -N.a2 * N.t + N.b2 * N.s - N.h2 * N.t + N.a2 + N.h2 + N.t - 1 := by linarith
    have hx0 : 0 < -N.a0 * N.b2 + N.a2 * N.b0 + N.a2 * N.h0 + N.b0 * N.h2 + N.h0 * N.h2 - N.a2 -
        N.b0 - N.h0 - N.h2 + 1 := by
      by_contra hc; push Not at hc
      have hneg : 0 ≤ N.a0 * N.b2 - N.a2 * N.b0 - N.a2 * N.h0 - N.b0 * N.h2 - N.h0 * N.h2 + N.a2 +
          N.b0 + N.h0 + N.h2 - 1 := by linarith
      linarith [mul_pos (N.d035) hA2, mul_pos (hB2) N.d035, mul_pos (N.d035) hh21, mul_pos (h345_0)
            hsg, mul_nonneg (hst).le hneg]
    exact N.isRupert_k3_T2c hA2 hh01 hh21 hsg hx0 G.zT2c G.ndT2
  · have hsg : 0 < N.a2 * N.t - N.b2 * N.s + N.h2 * N.t - N.a2 - N.h2 - N.t + 1 := by linarith
    rcases lt_or_gt_of_ne G.c0 with hc | hc
    · have hc0 : 0 < -N.a0 * N.b2 + N.a2 * N.b0 + N.a2 * N.h0 + N.b0 * N.h2 + N.h0 * N.h2 - N.a2 -
          N.b0 - N.h0 - N.h2 + 1 := by linarith
      exact N.isRupert_k3_T2b hA2 hh21 hsg hc0 G.zT2b G.ndT2
    · have hc0 : 0 < N.a0 * N.b2 - N.a2 * N.b0 - N.a2 * N.h0 - N.b0 * N.h2 - N.h0 * N.h2 + N.a2 +
          N.b0 + N.h0 + N.h2 - 1 := by linarith
      exact N.isRupert_k3_P14 hA2 hb0 hh01 hG5n hF45 hh20 hth hf hh21 hsg hc0 G.zT1 G.zT2a G.ndT1
          G.ndT2

/-- **Theorem 21.15 (ii)**: for `h2 ≥ 1 + A2` the region `R` is empty. -/
theorem NF29.k3_R_empty (N : NF29 x)
    (hA2 : 0 < -N.a2)
    (hb0 : 0 < N.b0)
    (hV3 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (hh01 : 0 < -N.h0 + 1)
    (hG4 : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.b0 - N.b2)
    (hG5n : 0 < -N.a0 * N.h2 + N.a2 * N.h0 + N.a0 - N.a2)
    (hF45 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0)
    (hh20 : 0 < -N.h0 + N.h2)
    (hth : 0 < -N.a2 * N.t + N.b2 * N.s)
        (hf : 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s -
          N.b0 * N.h2 + N.b2 * N.h0)
    (hh2g : 0 < N.h2 - 1) (hkn : 0 ≤ N.a2 + N.h2 - 1) : False := by
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  have h345_0 : 0 < 1 - N.a0 - N.b0 - N.h0 := by linarith [N.t345_0]
  have h345_2 : 0 < 1 - N.a2 - N.b2 - N.h2 := by linarith [N.t345_2]
  have hE35 : 0 < -((N.b0 - 1 + N.h0) * N.a2 - N.a0 * N.b2 + N.a0 * (1 - N.h2)) :=
      by linarith [N.hE35]
  have hst : 0 < N.s + N.t - 1 := by linarith [N.hst]
  linarith [mul_pos (hB2) hf, mul_pos (hV3) hth, mul_pos (hV3) hG4, mul_pos (hV3) hV3, mul_pos
        (h345_2) hf, mul_pos (h345_0) hV3, mul_pos (N.d035) hG4, mul_pos (N.d035) hV3, mul_pos
        (mul_pos (hA0) hA2) hV3, mul_pos (mul_pos (N.hh0) hB2) hV3, mul_pos (mul_pos (hV3) hh01)
        hh2g, mul_pos (mul_pos (h345_0) hh20) hth, mul_pos (mul_pos (h345_2) hV3) hh01, mul_pos
        (mul_pos (N.d234) hA2) hh01, mul_pos (mul_pos (N.d035) hA2) hh01, mul_pos
        (mul_pos (hA0) N.d035) hh2g, mul_pos (mul_pos (N.hh0) h345_0) hth, mul_pos
        (mul_pos (N.d234) hh01) hh01, mul_pos (mul_pos (N.hh0) N.d234) hh01, mul_nonneg
        (mul_pos (hb0) hV3).le hkn, mul_nonneg (mul_pos (hst) hh20).le hkn, mul_nonneg
        (mul_pos (N.hs) hV3).le hkn, mul_pos (mul_pos (h345_2) N.d035) hh2g, mul_pos
        (mul_pos (h345_0) N.d035) hh01, mul_nonneg (mul_pos (N.ht) hh20).le hkn, mul_pos
        (mul_pos (N.hh0) h345_0) N.d035, mul_nonneg (mul_pos (N.hF5) hst).le hkn, mul_nonneg
        (mul_pos (h345_0) hV3).le hkn, mul_nonneg (mul_pos (N.d234) hh01).le hkn, mul_nonneg
        (mul_pos (N.hh2) N.d035).le hkn, mul_nonneg (mul_pos (N.hh0) N.d234).le hkn]

set_option maxHeartbeats 1000000 in
/-- **Theorem 21.15 (iii)–(v), Lemmas 21.16–21.21** (`6 ∈ R`, `1 < h2 < 1 + A2`): P11, the planar
`T3`, `{Xa, T2}`, the planar `Y1`, P13 or Y′. -/
theorem NF29.isRupert_k3_open (N : NF29 x)
    (hA2 : 0 < -N.a2)
    (hb0 : 0 < N.b0)
    (hV3 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (hh01 : 0 < -N.h0 + 1)
    (hG4 : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.b0 - N.b2)
    (hG5n : 0 < -N.a0 * N.h2 + N.a2 * N.h0 + N.a0 - N.a2)
    (hF45 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0)
    (hh20 : 0 < -N.h0 + N.h2)
    (hth : 0 < -N.a2 * N.t + N.b2 * N.s)
        (hf : 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s -
          N.b0 * N.h2 + N.b2 * N.h0)
    (hh2g : 0 < N.h2 - 1) (hkap : 0 < -N.a2 - N.h2 + 1)
    (n24 : ¬ (N.h0 < N.h0 * N.a2 - N.h2 * N.a0 ∧
      1 - N.a0 - N.b0 - N.h0 < -((N.b0 - 1 + N.h0) * N.a2 - N.a0 * N.b2 + N.a0 * (1 - N.h2))))
    (G : K3Gen N) : IsRupert (univ.image x) := by
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  have h345_0 : 0 < 1 - N.a0 - N.b0 - N.h0 := by linarith [N.t345_0]
  have h345_2 : 0 < 1 - N.a2 - N.b2 - N.h2 := by linarith [N.t345_2]
  have hE35 : 0 < -((N.b0 - 1 + N.h0) * N.a2 - N.a0 * N.b2 + N.a0 * (1 - N.h2)) :=
      by linarith [N.hE35]
  have hst : 0 < N.s + N.t - 1 := by linarith [N.hst]
  -- Theorem 21.15 (iii): `h0 > F5`
  have hh0F5 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.h0 := by
    by_contra hc; push Not at hc
    have hlt : N.h0 < N.h0 * N.a2 - N.h2 * N.a0 := lt_of_le_of_ne (by linarith) (Ne.symm G.F5h0)
    rcases le_or_gt (N.h2 * N.b0 - N.h0 * N.b2) N.h2 with hle | hgt
    · linarith
    · have h := not_lt.mp fun h' => n24 ⟨hlt, h'⟩
      have hneg : 0 < -N.a0 * N.h2 + N.a2 * N.h0 - N.h0 := by linarith
      have hF4h2 : 0 < N.b0 * N.h2 - N.b2 * N.h0 - N.h2 := by linarith
      have hc2n : 0 ≤ -N.a0 * N.b2 - N.a0 * N.h2 + N.a2 * N.b0 + N.a2 * N.h0 - N.a2 - N.b0 - N.h0 +
          1 := by linarith
      linarith [mul_pos (hA2) hV3, mul_pos (hb0) hV3, mul_pos (hB2) hneg, mul_pos (hkap) hneg,
            mul_pos (N.hh0) hV3, mul_pos (h345_0) hV3, mul_pos (h345_0) hneg, mul_nonneg (N.hh2).le
            hc2n, mul_nonneg (N.hh0).le hc2n]
  rcases lt_or_gt_of_ne G.F4h2 with hF | hF
  · have hh2F4 : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.h2 := by linarith
    have hb01 : 0 < -N.b0 + 1 := pos_of_mul_pos_r N.hh2 (by
      linarith [hh2F4, mul_pos (N.hh0) hB2])
    by_cases hQ : 0 < N.a0 * N.h2 * N.t - N.b2 * N.h0 * N.s + N.h0 * N.h2 * N.t + N.b2 * N.h0 ∧ 0 <
        -N.a0 * N.h2 * N.t + N.b2 * N.h0 * N.s + N.h0 * N.h2 * N.s + N.a0 * N.h2
    · obtain ⟨hq46, hq65⟩ := hQ
      exact N.isRupert_k3_T3p hh2g hh0F5 hh2F4 hq46 hq65 (N.planar_unimodal N.vT3 G.zT3p) G.ndT3
    rcases lt_or_gt_of_ne G.Xf with hX | hX
    · have hXfn : 0 < N.a0 * N.t - N.b0 * N.s + N.h0 * N.t + N.b0 + N.s - 1 := by linarith
      rcases lt_or_gt_of_ne G.hs with hY | hY
      · have hAs : 0 < -N.h0 * N.s - N.a0 := by linarith
        have hAh0 : 0 < -N.a0 - N.h0 := by
          by_contra hc; push Not at hc
          have hneg : 0 ≤ N.a0 + N.h0 := by linarith
          linarith [mul_pos (hA0) hXfn, mul_pos (h345_0) hAs, mul_nonneg (N.d035).le hneg]
        have hs1g : 0 < N.s - 1 := pos_of_mul_pos_r hb01 (by
          linarith [hXfn, mul_pos (N.ht) hAh0])
        have hW43 : 0 < -N.a0 * N.h2 * N.t + N.b2 * N.h0 * N.s - N.h0 * N.h2 * N.t - N.b2 * N.h0 :=
            pos_of_mul_pos_r hA0 (by
              linarith [mul_pos (mul_pos (N.hh0) hB2) hAs, mul_pos (mul_pos (N.hh0) hth) hAh0,
                  mul_pos (mul_pos (N.hF5) N.ht) hAh0])
        have hsg : 0 < N.a2 * N.t - N.b2 * N.s + N.h2 * N.t - N.a2 - N.h2 - N.t + 1 :=
            pos_of_mul_pos_r hA0 (by
              linarith
                [mul_pos (N.hDG5) N.hs, mul_pos (N.d035) hkap,
                    mul_pos (mul_pos (h345_0) N.hs) hh2g])
        rcases lt_or_gt_of_ne G.L36 with hL | hL
        · have hL36n : 0 < N.a0 * N.h2 * N.t - N.b2 * N.h0 * N.s - N.h0 * N.h2 * N.s - N.a0 * N.h2
              := by linarith
          exact N.isRupert_k3_P13 hV3 hh01 hh2g hkap hh0F5 hh2F4 hsg hL36n hW43 hAh0 hs1g G.zT3s
              G.zT2o G.ndT3 G.ndT2
        · have hL36 : 0 < -N.a0 * N.h2 * N.t + N.b2 * N.h0 * N.s + N.h0 * N.h2 * N.s + N.a0 * N.h2
              := by linarith
          have hc4 : 0 < N.a0 * N.b2 - N.a2 * N.b0 - N.b0 * N.h2 + N.b2 * N.h0 - N.a0 + N.a2 - N.h0
              + N.h2 := pos_of_mul_pos_r hA0
              (by linarith [mul_pos (N.hDG5) hAh0, mul_pos (h345_0) N.hF5])
          exact N.isRupert_k3_Yp hb0 hV3 hh01 hG5n hh20 hh2g hkap hh0F5 hXfn hb01 hAs hL36 hW43 hAh0
              hs1g hc4 G.zY1q G.zY2 G.ndY1 G.ndY2
      · have hYs : 0 < N.h0 * N.s + N.a0 := by linarith
        have hp56 : 0 < N.a2 * N.t - N.b2 * N.s - N.h2 * N.s - N.a2 + N.s := pos_of_mul_pos_r hA0
            (by linarith [mul_pos (N.d035) hA2, mul_pos (N.hDG5) N.hs])
        have hL36 : 0 < -N.a0 * N.h2 * N.t + N.b2 * N.h0 * N.s + N.h0 * N.h2 * N.s + N.a0 * N.h2 :=
            by
          linarith [mul_pos (hb0) hYs, mul_pos (hb01) hYs, mul_pos (hh2g) hYs, mul_pos (N.hh0) hth,
                mul_pos (N.hF5) N.ht]
        exact N.isRupert_k3_Y1p hb0 hYs hp56 hL36 (N.planar_unimodal N.vY1 G.zY1p) G.ndY1
    · have hXf : 0 < -N.a0 * N.t + N.b0 * N.s - N.h0 * N.t - N.b0 - N.s + 1 := by linarith
      have hsg : 0 < N.a2 * N.t - N.b2 * N.s + N.h2 * N.t - N.a2 - N.h2 - N.t + 1 :=
          pos_of_mul_pos_r hA0 (by
            linarith [mul_pos (N.d035) hA2, mul_pos (N.hDG5) N.hs,
                mul_pos (mul_pos (hA0) hst) hh2g])
      have hXa2 : 0 < -N.a0 * N.b2 + N.a2 * N.b0 + N.b0 * N.h2 - N.b2 * N.h0 - N.a2 - N.b0 - N.h2 +
          1 := pos_of_mul_pos_r N.hh0 (by linarith [mul_pos (hV3) hb01, mul_pos (h345_0) hh2F4])
      exact N.isRupert_k3_X hA2 hb0 hV3 hh01 hG4 hG5n hh20 hh2g hkap hh2F4 hXf hb01 hsg hXa2 G.zXa
          G.zT2o G.ndXa G.ndT2
  · have hF4h2 : 0 < N.b0 * N.h2 - N.b2 * N.h0 - N.h2 := by linarith
    have hN : 0 < N.a0 * N.b2 - N.a2 * N.b0 - N.a2 * N.h0 + N.a2 := by
      linarith [N.hDG5, mul_pos (hA0) hh2g]
    have hal : 0 < -N.a0 * N.b0 * N.h2 + N.a0 * N.b2 * N.h0 - N.a0 * N.h0 * N.h2 - N.b0 * N.h0 *
        N.h2 - N.h0 ^ 2 * N.h2 + N.a0 * N.h2 + N.h0 * N.h2 := by
      linarith [mul_pos (hA0) hF4h2, mul_pos (N.hh0) h345_0, mul_pos (mul_pos (N.hh0) h345_0) hh2g]
    have hhF5 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.h0 * N.h2 := by
      linarith [hh0F5, mul_pos (N.hh0) hh2g]
    exact N.isRupert_k3_P11 hA2 hb0 hh01 hG5n hF45 hh20 hth hf hh2g hkap hh0F5 hF4h2 hN hal hhF5
        G.zT1 G.zT3o G.ndT1 G.ndT3

/-- **Theorem 21.22 (K3 is covered), class K3a.**  Let `K` be of type 29 in normal coordinates
(`NF29`) with `O = K − 6` of class K3a (`a2 < 0 < b0`, `V > 0`) in `R_G`: none of the E-good `G`
edges `0 → 3`, `2 → 4`, `1 → 4`, `5 → 1` is a quad edge (Lemma 21.3).  Off the special positions
and with the genericity of the named tests (`K3Gen`), `K` is Rupert: Lemma E at `56`, `14` or `46`
when `6 ∉ R` (21.13); in `R`, P14 or a free `T2` (`h2 < 1`), and for `1 < h2 < 1 + A2` P11, the
planar `T3`, `{Xa, T2}`, the planar `Y1`, P13 or Y′ (21.15–21.21); `h2 > 1 + A2` leaves `R`
empty. -/
theorem NF29.isRupert_K3a (N : NF29 x) (ha2 : N.a2 < 0) (hb0 : 0 < N.b0)
    (hV : 0 < N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0))
    (n03 : ¬ (-N.b2 < N.h2 * N.b0 - N.h0 * N.b2 ∧ 1 < N.h0))
    (n24 : ¬ (N.h0 < N.h0 * N.a2 - N.h2 * N.a0 ∧
      1 - N.a0 - N.b0 - N.h0 < -((N.b0 - 1 + N.h0) * N.a2 - N.a0 * N.b2 + N.a0 * (1 - N.h2))))
    (n14 : ¬ (N.b0 * (1 - N.h2) - N.b2 * (1 - N.h0) < 0 ∧ 1 < N.b0 + N.h0))
    (n51 : ¬ (0 < N.a2 * (1 - N.h0) - N.a0 * (1 - N.h2) ∧ N.a2 + N.h2 < 1))
    (G : K3Gen N) : IsRupert (univ.image x) := by
  obtain ⟨h0, hG4', hG5', hF', h20'⟩ := N.k3_facts ha2 hb0 hV n03 n14 n51 G.h0 G.G4 G.G5 G.F
  have hA2 : 0 < -N.a2 := by linarith
  have hb0 : 0 < N.b0 := by linarith
  have hV3 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2 := by linarith
  have hh01 : 0 < -N.h0 + 1 := by linarith
  have hG4 : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.b0 - N.b2 := by linarith
  have hG5n : 0 < -N.a0 * N.h2 + N.a2 * N.h0 + N.a0 - N.a2 := by linarith
  have hF45 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 := by linarith
  have hh20 : 0 < -N.h0 + N.h2 := by linarith
  by_cases hR : 0 < -N.a2 * N.t + N.b2 * N.s ∧ 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 *
      N.h2 * N.s - N.b2 * N.h0 * N.s - N.b0 * N.h2 + N.b2 * N.h0
  · obtain ⟨hth, hf⟩ := hR
    rcases lt_or_gt_of_ne G.h21 with h2 | h2
    · exact N.isRupert_k3_i hA2 hb0 hV3 hh01 hG4 hG5n hF45 hh20 hth hf (by linarith) G
    · rcases lt_or_gt_of_ne G.kap with hk | hk
      · exact (N.k3_R_empty hA2 hb0 hV3 hh01 hG4 hG5n hF45 hh20 hth hf
          (by linarith) (by linarith)).elim
      · exact N.isRupert_k3_open hA2 hb0 hV3 hh01 hG4 hG5n hF45 hh20 hth hf (by linarith) hk n24 G
  · exact N.isRupert_k3_notR hA2 hb0 hV3 hh01 hG4 hG5n hF45 hh20 hR G

/-- **Theorem 21.22, class K3b** (`σ` of K3a): `a2 > 0 > b0`, `V < 0`, and none of the E-good `G`
edges `2 → 3`, `0 → 5`, `1 → 5`, `4 → 1` is a quad edge (Lemma 21.3).  With the special positions
and genericity of the `σ`-image (`K3Gen N.sigma`), `K` is Rupert. -/
theorem NF29.isRupert_K3b (N : NF29 x) (ha2 : 0 < N.a2) (hb0 : N.b0 < 0)
    (hV : N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0) < 0)
    (n23 : ¬ (-N.a0 < N.h0 * N.a2 - N.h2 * N.a0 ∧ 1 < N.h2))
    (n05 : ¬ (N.h2 < N.h2 * N.b0 - N.h0 * N.b2 ∧
      1 - N.h2 - N.a2 - N.b2 < N.a0 * N.b2 + (1 - N.h2 - N.a2) * N.b0 - N.b2 * (1 - N.h0)))
    (n15 : ¬ (N.a2 * (1 - N.h0) - N.a0 * (1 - N.h2) < 0 ∧ 1 < N.a2 + N.h2))
    (n41 : ¬ (0 < N.b0 * (1 - N.h2) - N.b2 * (1 - N.h0) ∧ N.b0 + N.h0 < 1))
    (G : K3Gen N.sigma) : IsRupert (univ.image x) := by
  have h := NF29.isRupert_K3a N.sigma hb0 ha2 (by simp only [NF29.sigma]; linarith)
    (by intro h; simp only [NF29.sigma] at h; exact n23 ⟨by linarith [h.1], by linarith [h.2]⟩)
    (by intro h; simp only [NF29.sigma] at h; exact n05 ⟨by linarith [h.1], by linarith [h.2]⟩)
    (by intro h; simp only [NF29.sigma] at h; exact n15 ⟨by linarith [h.1], by linarith [h.2]⟩)
    (by intro h; simp only [NF29.sigma] at h; exact n41 ⟨by linarith [h.1], by linarith [h.2]⟩) G
  rwa [image_sigma29] at h

end Minimality

end
