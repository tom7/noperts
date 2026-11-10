module

public import Minimality.RightSlide
public import Minimality.Type29NF

@[expose] public section

/-!
# Type 29, class K2a on `Z1`, case B: the Slide Lemma leaf

* `Minimality.Split.Slide.slide_tab` / `slide_euclid`: the Slide Lemma (σ = +1) in any Euclidean
  position.  `e = x b - x a`, `g = x a' - x a`, `x b' - x a = e + g`, `nQ` a normal of the rectangle
  `Q = a b b' a'`; the coordinates `X = ⟪· - x a, e⟫`, `Y = ⟪· - x a, nQ⟫`, `G = ⟪· - x a, g⟫`.
  Reduced to `slide_core_rupert` by the orthonormal frame `e/‖e‖, nQ/‖nQ‖, -g/‖g‖`.
* `Minimality.Split.Slide.kdich`: the (K) dichotomy between the two walls.
* `Minimality.NF29.isRupert_Z1_caseB_slide`: on `Z1` with the edge `14` orthogonal to the facet
  `015` (case B), the slab hypothesis at one end of the edge `15` gives Rupert.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset

namespace Minimality.Split.Slide
open Minimality (pt pt_zero pt_one pt_two IsFrame orthoFrameMat orthoFrameMat_apply
  isRupert_of_frame_image)

/-- **Slide Lemma (σ = +1), Euclidean form with coordinate tables.**  `a, b, a', b'` the corners
of the rectangle `Q` (`e = x b - x a ⟂ g = x a' - x a`, `x b' - x a = e + g`), `nQ ≠ 0` a normal
of `Q`.  With `X i = ⟪x i - x a, e⟫`, `Y i = ⟪x i - x a, nQ⟫`, `G i = ⟪x i - x a, g⟫`:
(hD) every point other than the corners is deep (`Y > 0`); (hZ) `0 ≤ G ≤ ⟪g, g⟫` (the planes of
`F ∋ a, b` and `H ∋ a', b'`, both orthogonal to `g`, support); (Sl₊) deep points have `X > 0`;
(R) a deep point lies on `H`; (K₊) some `κ` with `Y < κ X` on the deep points of `H` and
`κ (X - ⟪e, e⟫) < Y` on the deep points of `F` beyond `b`. -/
theorem slide_tab {n : ℕ} (x : Fin n → ℝ³) (a b a' b' : Fin n) (e g nQ : ℝ³)
    (X Y G : Fin n → ℝ)
    (hX : ∀ i, ⟪x i - x a, e⟫ = X i) (hY : ∀ i, ⟪x i - x a, nQ⟫ = Y i)
    (hG : ∀ i, ⟪x i - x a, g⟫ = G i)
    (he : x b - x a = e) (hg : x a' - x a = g) (hb' : x b' - x a = e + g)
    (he0 : e ≠ 0) (hg0 : g ≠ 0) (hn0 : nQ ≠ 0)
    (heg : ⟪e, g⟫ = 0) (hen : ⟪e, nQ⟫ = 0) (hgn : ⟪g, nQ⟫ = 0)
    (hD : ∀ i, i ≠ a → i ≠ b → i ≠ a' → i ≠ b' → 0 < Y i)
    (hZ : ∀ i, 0 ≤ G i ∧ G i ≤ ⟪g, g⟫)
    (hSl : ∀ i, 0 < Y i → 0 < X i)
    (hR : ∃ q, 0 < Y q ∧ G q = ⟪g, g⟫)
    (hK : ∃ κ : ℝ, (∀ i, 0 < Y i → G i = ⟪g, g⟫ → Y i < κ * X i) ∧
      (∀ i, 0 < Y i → G i = 0 → ⟪e, e⟫ < X i → κ * (X i - ⟪e, e⟫) < Y i)) :
    IsRupert (univ.image x) := by
  classical
  have hL : 0 < ‖e‖ := norm_pos_iff.2 he0
  have hh : 0 < ‖g‖ := norm_pos_iff.2 hg0
  have hn : 0 < ‖nQ‖ := norm_pos_iff.2 hn0
  have hee : ⟪e, e⟫ = ‖e‖ ^ 2 := real_inner_self_eq_norm_sq e
  have hgg : ⟪g, g⟫ = ‖g‖ ^ 2 := real_inner_self_eq_norm_sq g
  have hLn : ‖e‖ ≠ 0 := hL.ne'
  have hhn : ‖g‖ ≠ 0 := hh.ne'
  have hnn : ‖nQ‖ ≠ 0 := hn.ne'
  set S : ℝ³ := ‖e‖⁻¹ • e with hS
  set T : ℝ³ := ‖nQ‖⁻¹ • nQ with hT
  set Nn : ℝ³ := ‖-g‖⁻¹ • (-g) with hN
  have hFr : IsFrame S T Nn := by
    refine ⟨AcuteEdge.frame_unit he0, AcuteEdge.frame_unit hn0,
      AcuteEdge.frame_unit (neg_ne_zero.2 hg0), ?_, ?_, ?_⟩
    · rw [hS, hT, real_inner_smul_left, real_inner_smul_right, hen]; ring
    · rw [hS, hN, real_inner_smul_left, real_inner_smul_right, inner_neg_right, heg]; ring
    · rw [hT, hN, real_inner_smul_left, real_inner_smul_right, inner_neg_right,
        real_inner_comm, hgn]; ring
  set c : Fin n → ℝ³ := fun i => pt (‖e‖⁻¹ * X i) (‖nQ‖⁻¹ * Y i) (-(‖g‖⁻¹ * G i)) with hc
  have hXa : X a = 0 := by rw [← hX a, sub_self, inner_zero_left]
  have hYa : Y a = 0 := by rw [← hY a, sub_self, inner_zero_left]
  have hGa : G a = 0 := by rw [← hG a, sub_self, inner_zero_left]
  have hcR : IsRupert (univ.image c) := by
    obtain ⟨q, hqY, hqG⟩ := hR
    obtain ⟨κ, hKH, hKF⟩ := hK
    refine slide_core_rupert c a b a' b' ‖e‖ ‖g‖ hL hh ?_ ?_ ?_ ?_ ?_ ?_ ?_ ⟨q, ?_, ?_⟩
      ⟨κ * ‖e‖ / ‖nQ‖, ?_, ?_⟩
    · simp only [hc, hXa, hYa, hGa, mul_zero, neg_zero]
    · simp only [hc, ← hX, ← hY, ← hG, he, hen, heg, hee, mul_zero, neg_zero]
      congr 1; field_simp
    · simp only [hc, ← hX, ← hY, ← hG, hg, real_inner_comm e g, heg, hgn, hgg, mul_zero]
      congr 1; field_simp
    · simp only [hc, ← hX, ← hY, ← hG, hb', inner_add_left, hen, hgn, heg,
        real_inner_comm e g, hee, hgg, add_zero, zero_add, mul_zero]
      congr 1 <;> field_simp
    · intro i h1 h2 h3 h4
      simp only [hc, pt_one]
      exact mul_pos (inv_pos.2 hn) (hD i h1 h2 h3 h4)
    · intro i
      simp only [hc, pt_two]
      obtain ⟨h1, h2⟩ := hZ i
      rw [hgg] at h2
      constructor
      · have : ‖g‖⁻¹ * G i ≤ ‖g‖ := by
          rw [inv_mul_le_iff₀ hh]; nlinarith
        linarith
      · have : 0 ≤ ‖g‖⁻¹ * G i := mul_nonneg (inv_nonneg.2 hh.le) h1
        linarith
    · intro i hi
      simp only [hc, pt_zero, pt_one] at hi ⊢
      have hYi : 0 < Y i := (mul_pos_iff_of_pos_left (inv_pos.2 hn)).1 hi
      exact mul_pos (inv_pos.2 hL) (hSl i hYi)
    · simp only [hc, pt_one]; exact mul_pos (inv_pos.2 hn) hqY
    · simp only [hc, pt_two, hqG, hgg]; field_simp
    · intro i h1 h2
      simp only [hc, pt_zero, pt_one, pt_two] at h1 h2 ⊢
      have hYi : 0 < Y i := (mul_pos_iff_of_pos_left (inv_pos.2 hn)).1 h1
      have hGi : G i = ⟪g, g⟫ := by
        rw [hgg]; field_simp at h2; linarith
      have hk := hKH i hYi hGi
      have : κ * ‖e‖ / ‖nQ‖ * (‖e‖⁻¹ * X i) = ‖nQ‖⁻¹ * (κ * X i) := by field_simp
      rw [this]; exact mul_lt_mul_of_pos_left hk (inv_pos.2 hn)
    · intro i h1 h2 h3
      simp only [hc, pt_zero, pt_one, pt_two] at h1 h2 h3 ⊢
      have hYi : 0 < Y i := (mul_pos_iff_of_pos_left (inv_pos.2 hn)).1 h1
      have hGi : G i = 0 := by
        have : ‖g‖⁻¹ * G i = 0 := by linarith
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h (inv_ne_zero hhn)
        · exact h
      have hXi : ⟪e, e⟫ < X i := by
        rw [hee]; rw [lt_inv_mul_iff₀ hL] at h3; nlinarith
      have hk := hKF i hYi hGi hXi
      have : κ * ‖e‖ / ‖nQ‖ * (‖e‖⁻¹ * X i - ‖e‖) = ‖nQ‖⁻¹ * (κ * (X i - ⟪e, e⟫)) := by
        rw [hee]; field_simp
      rw [this]; exact mul_lt_mul_of_pos_left hk (inv_pos.2 hn)
  apply isRupert_of_frame_image (univ.image x) (v := x a) hFr
  rw [Finset.image_image]
  convert hcR using 2
  funext i
  simp only [Function.comp_apply, orthoFrameMat_apply, hc, hS, hT, hN, real_inner_smul_right,
    inner_neg_right, norm_neg, hX, hY, hG]
  congr 1; ring

/-- **Slide Lemma (σ = +1), Euclidean form.**  `slide_tab` with the coordinates spelled out. -/
theorem slide_euclid {n : ℕ} (x : Fin n → ℝ³) (a b a' b' : Fin n) (e g nQ : ℝ³)
    (he : x b - x a = e) (hg : x a' - x a = g) (hb' : x b' - x a = e + g)
    (he0 : e ≠ 0) (hg0 : g ≠ 0) (hn0 : nQ ≠ 0)
    (heg : ⟪e, g⟫ = 0) (hen : ⟪e, nQ⟫ = 0) (hgn : ⟪g, nQ⟫ = 0)
    (hD : ∀ i, i ≠ a → i ≠ b → i ≠ a' → i ≠ b' → 0 < ⟪x i - x a, nQ⟫)
    (hZ : ∀ i, 0 ≤ ⟪x i - x a, g⟫ ∧ ⟪x i - x a, g⟫ ≤ ⟪g, g⟫)
    (hSl : ∀ i, 0 < ⟪x i - x a, nQ⟫ → 0 < ⟪x i - x a, e⟫)
    (hR : ∃ q, 0 < ⟪x q - x a, nQ⟫ ∧ ⟪x q - x a, g⟫ = ⟪g, g⟫)
    (hK : ∃ κ : ℝ, (∀ i, 0 < ⟪x i - x a, nQ⟫ → ⟪x i - x a, g⟫ = ⟪g, g⟫ →
        ⟪x i - x a, nQ⟫ < κ * ⟪x i - x a, e⟫) ∧
      (∀ i, 0 < ⟪x i - x a, nQ⟫ → ⟪x i - x a, g⟫ = 0 → ⟪e, e⟫ < ⟪x i - x a, e⟫ →
        κ * (⟪x i - x a, e⟫ - ⟪e, e⟫) < ⟪x i - x a, nQ⟫)) :
    IsRupert (univ.image x) :=
  slide_tab x a b a' b' e g nQ _ _ _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) he hg hb' he0
    hg0 hn0 heg hen hgn hD hZ hSl hR hK

/-- **The (K) dichotomy**.  Two walls share the slab `X > 0` (lengths along the
edge, `ℓ` the edge length squared in the units of `X`) and the depth `Y > 0`; the deep point of `H`
is `3` at wall `B` and `0` at wall `H`, and conversely on `F`.  Then (K₊) holds at one of the two
walls.  If it failed at both, `Y₃ (X₀ - ℓ) ≥ Y₀ X₃ > Y₀ (X₃ - ℓ) ≥ Y₃ X₀ > Y₃ (X₀ - ℓ)`. -/
theorem kdich {ℓ X0 X3 Y0 Y3 : ℝ} (hℓ : 0 < ℓ) (hX0 : 0 < X0) (hX3 : 0 < X3) (hY0 : 0 < Y0)
    (hY3 : 0 < Y3) :
    (∃ κ : ℝ, Y3 < κ * X3 ∧ (ℓ < X0 → κ * (X0 - ℓ) < Y0)) ∨
      (∃ κ : ℝ, Y0 < κ * X0 ∧ (ℓ < X3 → κ * (X3 - ℓ) < Y3)) := by
  by_cases h0 : X0 ≤ ℓ
  · left
    refine ⟨(Y3 + 1) / X3, ?_, fun h => absurd h (not_lt.2 h0)⟩
    rw [div_mul_cancel₀ _ hX3.ne']; linarith
  by_cases h3 : X3 ≤ ℓ
  · right
    refine ⟨(Y0 + 1) / X0, ?_, fun h => absurd h (not_lt.2 h3)⟩
    rw [div_mul_cancel₀ _ hX0.ne']; linarith
  rw [not_le] at h0 h3
  have p0 : 0 < X0 - ℓ := sub_pos.2 h0
  have p3 : 0 < X3 - ℓ := sub_pos.2 h3
  by_cases hc : Y3 * (X0 - ℓ) < Y0 * X3
  · left
    obtain ⟨κ, h1, h2⟩ := exists_between
      (show Y3 / X3 < Y0 / (X0 - ℓ) by rw [div_lt_div_iff₀ hX3 p0]; linarith)
    exact ⟨κ, (div_lt_iff₀ hX3).1 h1, fun _ => (lt_div_iff₀ p0).1 h2⟩
  · right
    rw [not_lt] at hc
    have hc' : Y0 * (X3 - ℓ) < Y3 * X0 := by nlinarith [mul_pos hY0 hℓ, mul_pos hY3 hℓ]
    obtain ⟨κ, h1, h2⟩ := exists_between
      (show Y0 / X0 < Y3 / (X3 - ℓ) by rw [div_lt_div_iff₀ hX0 p3]; linarith)
    exact ⟨κ, (div_lt_iff₀ hX0).1 h1, fun _ => (lt_div_iff₀ p3).1 h2⟩

end Minimality.Split.Slide

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
`346` (edge `46`) by `kdich`; the four normal forms are `slide_tab` at `(1,5,4,6)`, `(4,6,1,5)`
(σ = +1) and `(5,1,6,4)`, `(6,4,5,1)` (σ = -1, as σ = +1 with the edge reversed).  No class
hypothesis (`a2`, `b0`, `V`) is used. -/
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
  have v64 : x 6 - x 4 = N.E₂ := by rw [N.x6, N.x4, hs, ht]; simp only [nfP]; module
  have v14 : x 1 - x 4 = -N.E₁ := by rw [N.x1, N.x4]; simp only [nfP]; module
  have v54 : x 5 - x 4 = N.E₂ + -N.E₁ := by rw [N.x5, N.x4]; simp only [nfP]; module
  have v15 : x 1 - x 5 = -N.E₂ := by rw [N.x1, N.x5]; simp only [nfP]; module
  have v65 : x 6 - x 5 = N.E₁ := by rw [N.x6, N.x5, hs, ht]; simp only [nfP]; module
  have v45 : x 4 - x 5 = -N.E₂ + N.E₁ := by rw [N.x4, N.x5]; simp only [nfP]; module
  have v46 : x 4 - x 6 = -N.E₂ := by rw [N.x4, N.x6, hs, ht]; simp only [nfP]; module
  have v56 : x 5 - x 6 = -N.E₁ := by rw [N.x5, N.x6, hs, ht]; simp only [nfP]; module
  have v16 : x 1 - x 6 = -N.E₂ + -N.E₁ := by rw [N.x1, N.x6, hs, ht]; simp only [nfP]; module
  have e21 : ⟪N.E₂, N.E₁⟫ = 0 := by rw [real_inner_comm]; exact e12
  have nk : ‖N.E₁‖ ^ 2 = k := by rw [← real_inner_self_eq_norm_sq]; exact ek
  have nℓ : ‖N.E₂‖ ^ 2 = ℓ := by rw [← real_inner_self_eq_norm_sq]; exact eℓ
  have nE1 : -N.E₁ ≠ 0 := neg_ne_zero.2 hE10
  have nE2 : -N.E₂ ≠ 0 := neg_ne_zero.2 hE20
  rcases hSl with hP | hM
  · -- σ = +1: the deep vertices beyond `x1`
    have P0 := hP 0 (by simp)
    have P2 := hP 2 (by simp)
    have P3 := hP 3 (by simp)
    rw [v51, tX] at P0 P2 P3
    simp only [Matrix.cons_val] at P0 P2 P3
    rcases Minimality.Split.Slide.kdich hℓ P0 P3 q0 hω with ⟨κ, k1, k2⟩ | ⟨κ, k1, k2⟩
    · -- wall `B = 015`, edge `15`: `(a, b, a', b') = (1, 5, 4, 6)`
      refine Minimality.Split.Slide.slide_tab
        x 1 5 4 6 N.E₂ N.E₁ W (fun i => ⟪x i - x 1, N.E₂⟫)
        (fun i => ⟪x i - x 1, W⟫) (fun i => ⟪x i - x 1, N.E₁⟫) (fun _ => rfl) (fun _ => rfl)
        (fun _ => rfl) v51 v41 v61 hE20 hE10 hW0 e21 w2 w1 ?_ ?_ ?_ ⟨3, ?_, ?_⟩ ⟨κ, ?_, ?_⟩
      · intro i h1 h2 h3 h4; fin_cases i <;> simp [tY] at h1 h2 h3 h4 ⊢ <;> cb_close
      · intro i; fin_cases i <;> simp [tG, nk] <;> cb_close
      · intro i h; fin_cases i <;> simp [tX, tY] at h ⊢ <;> cb_close
      · simp [tY]; cb_close
      · simp [tG, nk]
      · intro i h1 h2; fin_cases i <;> simp [tX, tY, tG, nk] at h1 h2 ⊢ <;> cb_close
      · intro i h1 h2 h3; fin_cases i <;> simp [tX, tY, tG, nℓ] at h1 h2 h3 ⊢ <;> cb_close
    · -- wall `H = 346`, edge `46`: `(a, b, a', b') = (4, 6, 1, 5)`
      refine Minimality.Split.Slide.slide_tab
        x 4 6 1 5 N.E₂ (-N.E₁) W (fun i => ⟪x i - x 1, N.E₂⟫)
        (fun i => ⟪x i - x 1, W⟫) (fun i => k - ⟪x i - x 1, N.E₁⟫) ?_ ?_ ?_ v64 v14 v54 hE20 nE1
        hW0 (by rw [inner_neg_right, e21, neg_zero]) w2 (by rw [inner_neg_left, w1, neg_zero])
        ?_ ?_ ?_ ⟨0, ?_, ?_⟩ ⟨κ, ?_, ?_⟩
      · intro i; rw [hsh i 4, tX 4]; simp only [Matrix.cons_val]; ring
      · intro i; rw [hsh i 4, tY 4]; simp only [Matrix.cons_val]; ring
      · intro i
        rw [hsh i 4, inner_neg_right, inner_neg_right, tG 4]; simp only [Matrix.cons_val]; ring
      · intro i h1 h2 h3 h4; fin_cases i <;> simp [tY] at h1 h2 h3 h4 ⊢ <;> cb_close
      · intro i; fin_cases i <;> simp [tG, nk] <;> cb_close
      · intro i h; fin_cases i <;> simp [tX, tY] at h ⊢ <;> cb_close
      · simp [tY]; cb_close
      · simp [tG, nk]
      · intro i h1 h2; fin_cases i <;> simp [tX, tY, tG, nk] at h1 h2 ⊢ <;> cb_close
      · intro i h1 h2 h3; fin_cases i <;> simp [tX, tY, tG, nℓ] at h1 h2 h3 ⊢ <;> cb_close
  · -- σ = -1: the deep vertices before `x5`
    have M0 := hM 0 (by simp)
    have M2 := hM 2 (by simp)
    have M3 := hM 3 (by simp)
    rw [hsh _ 5, v15, v51, inner_neg_right, inner_neg_right, tX, eℓ] at M0 M2 M3
    simp only [Matrix.cons_val] at M0 M2 M3
    have M0' : 0 < ℓ - (N.b0 * ℓ - N.h0 * m) := by linarith
    have M3' : 0 < ℓ - -m := by linarith
    rcases Minimality.Split.Slide.kdich hℓ M0' M3' q0 hω with ⟨κ, k1, k2⟩ | ⟨κ, k1, k2⟩
    · -- wall `B = 015`, edge `51`: `(a, b, a', b') = (5, 1, 6, 4)`
      refine Minimality.Split.Slide.slide_tab
        x 5 1 6 4 (-N.E₂) N.E₁ W (fun i => ℓ - ⟪x i - x 1, N.E₂⟫)
        (fun i => ⟪x i - x 1, W⟫) (fun i => ⟪x i - x 1, N.E₁⟫) ?_ ?_ ?_ v15 v65 v45 nE2 hE10
        hW0 (by rw [inner_neg_left, e21, neg_zero]) (by rw [inner_neg_left, w2, neg_zero]) w1
        ?_ ?_ ?_ ⟨3, ?_, ?_⟩ ⟨κ, ?_, ?_⟩
      · intro i
        rw [hsh i 5, inner_neg_right, inner_neg_right, tX 5]; simp only [Matrix.cons_val]; ring
      · intro i; rw [hsh i 5, tY 5]; simp only [Matrix.cons_val]; ring
      · intro i; rw [hsh i 5, tG 5]; simp only [Matrix.cons_val]; ring
      · intro i h1 h2 h3 h4; fin_cases i <;> simp [tY] at h1 h2 h3 h4 ⊢ <;> cb_close
      · intro i; fin_cases i <;> simp [tG, nk] <;> cb_close
      · intro i h; fin_cases i <;> simp [tX, tY] at h ⊢ <;> cb_close
      · simp [tY]; cb_close
      · simp [tG, nk]
      · intro i h1 h2; fin_cases i <;> simp [tX, tY, tG, nk] at h1 h2 ⊢ <;> cb_close
      · intro i h1 h2 h3; fin_cases i <;> simp [tX, tY, tG, nℓ] at h1 h2 h3 ⊢ <;> cb_close
    · -- wall `H = 346`, edge `64`: `(a, b, a', b') = (6, 4, 5, 1)`
      refine Minimality.Split.Slide.slide_tab
        x 6 4 5 1 (-N.E₂) (-N.E₁) W (fun i => ℓ - ⟪x i - x 1, N.E₂⟫)
        (fun i => ⟪x i - x 1, W⟫) (fun i => k - ⟪x i - x 1, N.E₁⟫) ?_ ?_ ?_ v46 v56 v16 nE2 nE1
        hW0 (by rw [inner_neg_left, inner_neg_right, e21, neg_zero, neg_zero])
        (by rw [inner_neg_left, w2, neg_zero]) (by rw [inner_neg_left, w1, neg_zero])
        ?_ ?_ ?_ ⟨0, ?_, ?_⟩ ⟨κ, ?_, ?_⟩
      · intro i
        rw [hsh i 6, inner_neg_right, inner_neg_right, tX 6]; simp only [Matrix.cons_val]; ring
      · intro i; rw [hsh i 6, tY 6]; simp only [Matrix.cons_val]; ring
      · intro i
        rw [hsh i 6, inner_neg_right, inner_neg_right, tG 6]; simp only [Matrix.cons_val]; ring
      · intro i h1 h2 h3 h4; fin_cases i <;> simp [tY] at h1 h2 h3 h4 ⊢ <;> cb_close
      · intro i; fin_cases i <;> simp [tG, nk] <;> cb_close
      · intro i h; fin_cases i <;> simp [tX, tY] at h ⊢ <;> cb_close
      · simp [tY]; cb_close
      · simp [tG, nk]
      · intro i h1 h2; fin_cases i <;> simp [tX, tY, tG, nk] at h1 h2 ⊢ <;> cb_close
      · intro i h1 h2 h3; fin_cases i <;> simp [tX, tY, tG, nℓ] at h1 h2 h3 ⊢ <;> cb_close

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

#print axioms Minimality.Split.Slide.slide_tab
#print axioms Minimality.Split.Slide.kdich
#print axioms Minimality.NF29.isRupert_Z1_caseB_slide
#print axioms Minimality.NF29.isRupert_sZ1_caseB_slide
