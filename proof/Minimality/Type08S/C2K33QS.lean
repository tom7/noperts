module

public import Minimality.Type08S.C2K33QR
public import Minimality.Type08S.C2K20HI
public import Minimality.Type08S.C2K14O
public import Minimality.Type08S.C2K17BA

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem k28bq_ip (p q r : ℝ³) (hpq : ⟪p, r⟫ = ⟪p, q⟫) (x y z x' y' z' : ℝ) :
    ⟪fcomb p q r x y z, fcomb p q r x' y' z'⟫ =
      x * x' * ⟪p, p⟫ + (x * y' + y * x' + x * z' + z * x') * ⟪p, q⟫ + y * y' * ⟪q, q⟫ +
        (y * z' + z * y') * ⟪q, r⟫ + z * z' * ⟪r, r⟫ := by
  have h1 : ⟪q, p⟫ = ⟪p, q⟫ := real_inner_comm _ _
  have h2 : ⟪r, p⟫ = ⟪p, r⟫ := real_inner_comm _ _
  have h3 : ⟪r, q⟫ = ⟪q, r⟫ := real_inner_comm _ _
  simp only [fcomb, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, h1, h2, h3, hpq]
  ring

theorem k28bq_setup {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6)
    (hM : K6sM a a' b b' c c' d) (hrel : K16Rel a b c d α1 β1)
    (hβ : 1 < β1) (hσ : β6 + γ6 = β1)
    (hL : ⟪a - c', a - d⟫ = 0)
    (hM0 : 0 ≤ ⟪a - d, a - d⟫ * ⟪b - d, c - d⟫ - ⟪a - d, b - d⟫ ^ 2)
    (hΛ : (β1 - 1) * (⟪a - d, a - d⟫ * ⟪b - d, c - d⟫ - ⟪a - d, b - d⟫ ^ 2) +
      (γ6 - 1) * (⟪c - d, c - d⟫ - ⟪b - d, c - d⟫) * ⟪a - d, a - d⟫ < 0) :
    ∃ (P Q R : ℝ³) (t κA : ℝ), det3 P Q R ≠ 0 ∧ 1 < α1 ∧ 0 < β6 ∧ 0 < γ6 ∧ γ6 < 1 ∧ t < 0 ∧
      0 < κA ∧ κA = ⟪b' - a, c - a'⟫ ∧ t * κA = ⟪c' - a, c - a'⟫ ∧
      fpoint P Q R a (0, 0, 0) = a ∧ fpoint P Q R a (0, -β1, 0) = d ∧
      fpoint P Q R a (t, -(α1 + β1 - 1), -1) = b ∧ fpoint P Q R a (1, -(α1 + β1 - 1), 0) = c ∧
      fpoint P Q R a (β6 * t + γ6, -(α1 * β1), -β6) = a' ∧ fpoint P Q R a (t * β1, 0, -β1) = c' ∧
      fpoint P Q R a (β1, 0, 0) = b' ∧
      ⟪Q, R⟫ = 0 ∧
      (∃ e1 e2 : ℝ, ⟪P, R⟫ = e1 ∧ ⟪R, R⟫ = e2 ∧ e1 < 0 ∧ t * e1 - e2 < 0 ∧ e1 < β1 * (t * e1 - e2) ∧
        (1 - γ6) * e1 = β6 * (t * e1 - e2)) ∧
      ⟪a' - c, P⟫ < 0 := by
  obtain ⟨hdet, hc', hb', ha', hα1', hβ1', h1, hβ6', hγ6', h3⟩ := hC
  obtain ⟨m1, m2, m3⟩ := hM
  obtain ⟨hr1, hr2⟩ := hrel
  obtain rfl : γ6 = β1 - β6 := by linarith
  set p := a - d with hp
  set q := b - d with hq
  set r := c - d with hr
  have hb1 : β1 ≠ 0 := by linarith
  have hp0 : p ≠ 0 := by intro h0; apply hdet; rw [h0]; simp [det3_expand]
  have hpp : 0 < ⟪p, p⟫ := real_inner_self_pos.2 hp0
  have hm1 : ⟪p, r⟫ = ⟪p, q⟫ := by
    have : ⟪p, b - c⟫ = ⟪p, q⟫ - ⟪p, r⟫ := by
      rw [← inner_sub_right]; congr 1; rw [hq, hr]; abel
    linarith
  have hqp : ⟪q, p⟫ = ⟪p, q⟫ := real_inner_comm _ _
  have hrp : ⟪r, p⟫ = ⟪p, r⟫ := real_inner_comm _ _
  have hQR : ⟪q, r⟫ < ⟪q, q⟫ := by
    have e : c' - d = α1 • (p) + β1 • (q) := by rw [hc', hp, hq]; module
    have e2 : b - c = q - r := by rw [hq, hr]; abel
    rw [e, e2] at m2
    simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real, inner_sub_right] at m2
    have h0 : α1 * (⟪p, q⟫ - ⟪p, r⟫) = 0 := by rw [hm1]; ring
    nlinarith [m2, h0, hqp, hrp]
  have hRT : ⟪q, r⟫ < ⟪r, r⟫ := by
    have e : b' - d = α1 • (p) + β1 • (r) := by rw [hb', hp, hr]; module
    have e2 : b - c = q - r := by rw [hq, hr]; abel
    rw [e, e2] at m3
    simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real, inner_sub_right] at m3
    have h0 : α1 * (⟪p, q⟫ - ⟪p, r⟫) = 0 := by rw [hm1]; ring
    have hrq : ⟪r, q⟫ = ⟪q, r⟫ := real_inner_comm _ _
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg hβ1'.le (sub_nonneg.2 hh), m3, h0, hrq]
  have hs : ⟪p, q⟫ < 0 := by
    have hW : 0 < ⟪q, q⟫ + ⟪r, r⟫ - 2 * ⟪q, r⟫ := by linarith
    have h1 : 0 < (β1 - 1) * (⟪q, q⟫ * ⟪r, r⟫ - ⟪q, r⟫ ^ 2) :=
      mul_pos (by linarith) hr2
    by_contra hh; push Not at hh
    have h2 : 0 ≤ α1 * ⟪p, q⟫ * (⟪q, q⟫ + ⟪r, r⟫ - 2 * ⟪q, r⟫) :=
      mul_nonneg (mul_nonneg hα1'.le hh) hW.le
    nlinarith [hr1]
  have hLe : (α1 - 1) * ⟪p, p⟫ + β1 * ⟪p, q⟫ = 0 := by
    have e : a - c' = (1 - α1) • (p) - β1 • (q) := by rw [hc', hp, hq]; module
    rw [e] at hL
    simp only [inner_sub_left, inner_smul_left, RCLike.conj_to_real, hqp] at hL
    linarith
  have hα : 1 < α1 := by nlinarith
  have hD := hr2
  have hg1 : β1 - β6 < 1 := by
    by_contra hh; push Not at hh
    have := mul_nonneg (sub_nonneg.2 hh) (sub_nonneg.2 hRT.le)
    have h4 : 0 ≤ (β1 - 1) * (⟪p, p⟫ * ⟪q, r⟫ - ⟪p, q⟫ ^ 2) := mul_nonneg (by linarith) hM0
    have h5 : 0 ≤ ((β1 - β6) - 1) * (⟪r, r⟫ - ⟪q, r⟫) * ⟪p, p⟫ :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) hpp.le
    linarith
  -- vectors
  have hA : c' - a = fcomb (p) (q) (r) (α1 - 1) β1 0 := by rw [hc', hp, hq]; simp only [fcomb]; module
  have hB : b' - a = fcomb (p) (q) (r) (α1 - 1) 0 β1 := by rw [hb', hp, hr]; simp only [fcomb]; module
  have hCv : c - a' = fcomb (p) (q) (r) 0 (-β6) (1 - (β1 - β6)) := by
    rw [ha', hq, hr]; simp only [fcomb]; module
  have hip := k28bq_ip p q r hm1
  -- κA, κB, t
  have hκA : ⟪b' - a, c - a'⟫ = k28bqBC α1 β1 β6 ⟪p, q⟫ ⟪q, r⟫ ⟪r, r⟫ := by
    rw [hB, hCv, hip]; unfold k28bqBC; ring
  have hκB : ⟪c' - a, c - a'⟫ = k28bqAC α1 β1 β6 ⟪p, q⟫ ⟪q, q⟫ ⟪q, r⟫ := by
    rw [hA, hCv, hip]; unfold k28bqAC; ring
  have hκpos := k28bq_kpos hpp hLe hβ1' hΛ
  set κA := k28bqBC α1 β1 β6 ⟪p, q⟫ ⟪q, r⟫ ⟪r, r⟫ with hκAdef
  set κB := k28bqAC α1 β1 β6 ⟪p, q⟫ ⟪q, q⟫ ⟪q, r⟫ with hκBdef
  have hκne : κA ≠ 0 := hκpos.ne'
  have ht : (κB / κA) * κA = κB := div_mul_cancel₀ _ hκne
  obtain ⟨_, htn, hf, htie, he1, he2⟩ := k28bq_real hα hβ hβ6' hγ6' hg1 hpp hs hLe hQR hRT hD hM0 hr1 hΛ ht
  generalize κB / κA = t at ht htn hf htie he1 he2
  -- frame
  have hip' := hip
  have hPR : ⟪fcomb p q r ((α1 - 1) / β1) 0 1, fcomb p q r ((t - 1) * (α1 - 1) / β1) (-1) t⟫ =
      (t * k28bqBB α1 β1 ⟪p, p⟫ ⟪p, q⟫ ⟪r, r⟫ - k28bqAB α1 β1 ⟪p, p⟫ ⟪p, q⟫ ⟪q, r⟫) / β1 ^ 2 := by
    rw [hip]; unfold k28bqBB k28bqAB; field_simp; ring
  have hRR : ⟪fcomb p q r ((t - 1) * (α1 - 1) / β1) (-1) t, fcomb p q r ((t - 1) * (α1 - 1) / β1) (-1) t⟫ =
      (t ^ 2 * k28bqBB α1 β1 ⟪p, p⟫ ⟪p, q⟫ ⟪r, r⟫ - 2 * t * k28bqAB α1 β1 ⟪p, p⟫ ⟪p, q⟫ ⟪q, r⟫ +
        k28bqAA α1 β1 ⟪p, p⟫ ⟪p, q⟫ ⟪q, q⟫) / β1 ^ 2 := by
    rw [hip]; unfold k28bqBB k28bqAB k28bqAA; field_simp; ring
  have hQRz : ⟪fcomb p q r (1 / β1) 0 0, fcomb p q r ((t - 1) * (α1 - 1) / β1) (-1) t⟫ = 0 := by
    have e : ⟪fcomb p q r (1 / β1) 0 0, fcomb p q r ((t - 1) * (α1 - 1) / β1) (-1) t⟫ =
        (t - 1) / β1 ^ 2 * ((α1 - 1) * ⟪p, p⟫ + β1 * ⟪p, q⟫) := by
      rw [hip]; field_simp; ring
    rw [e, hLe, mul_zero]
  have hPB : fcomb p q r ((α1 - 1) / β1) 0 1 = β1⁻¹ • (b' - a) := by
    rw [hB]; simp only [fcomb]; match_scalars <;> (field_simp; try ring)
  have hdetPQR : det3 (fcomb p q r ((α1 - 1) / β1) 0 1) (fcomb p q r (1 / β1) 0 0)
      (fcomb p q r ((t - 1) * (α1 - 1) / β1) (-1) t) ≠ 0 := by
    rw [det3_coord]
    have : d3 ((α1 - 1) / β1) 0 1 (1 / β1) 0 0 ((t - 1) * (α1 - 1) / β1) (-1) t = -(1 / β1) := by
      simp only [d3]; ring
    rw [this]
    exact mul_ne_zero hdet (by simp [hb1])
  refine ⟨fcomb p q r ((α1 - 1) / β1) 0 1, fcomb p q r (1 / β1) 0 0,
    fcomb p q r ((t - 1) * (α1 - 1) / β1) (-1) t, t, κA, hdetPQR, hα, hβ6', hγ6', hg1, htn, hκpos,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hQRz, ?_, ?_⟩
  · exact hκA.symm
  · rw [hκB]; exact ht
  · simp only [fpoint, fcomb]; match_scalars <;> field_simp <;> ring
  · simp only [fpoint, fcomb]; match_scalars <;> field_simp <;> ring
  · simp only [fpoint, fcomb]; match_scalars <;> field_simp <;> ring
  · simp only [fpoint, fcomb]; match_scalars <;> field_simp <;> ring
  · rw [ha']; simp only [fpoint, fcomb]; match_scalars <;> field_simp <;> ring
  · rw [hc']; simp only [fpoint, fcomb]; match_scalars <;> field_simp <;> ring
  · rw [hb']; simp only [fpoint, fcomb]; match_scalars <;> field_simp <;> ring
  · set BBv := k28bqBB α1 β1 ⟪p, p⟫ ⟪p, q⟫ ⟪r, r⟫ with hBBv
    set ABv := k28bqAB α1 β1 ⟪p, p⟫ ⟪p, q⟫ ⟪q, r⟫ with hABv
    set AAv := k28bqAA α1 β1 ⟪p, p⟫ ⟪p, q⟫ ⟪q, q⟫ with hAAv
    have hb2 : 0 < β1 ^ 2 := by positivity
    refine ⟨(t * BBv - ABv) / β1 ^ 2, (t ^ 2 * BBv - 2 * t * ABv + AAv) / β1 ^ 2, hPR, hRR,
      div_neg_of_neg_of_pos he1 hb2, ?_, ?_, ?_⟩
    · have : t * ((t * BBv - ABv) / β1 ^ 2) - (t ^ 2 * BBv - 2 * t * ABv + AAv) / β1 ^ 2 =
          (t * ABv - AAv) / β1 ^ 2 := by field_simp; ring
      rw [this]; exact div_neg_of_neg_of_pos hf hb2
    · have : t * ((t * BBv - ABv) / β1 ^ 2) - (t ^ 2 * BBv - 2 * t * ABv + AAv) / β1 ^ 2 =
          (t * ABv - AAv) / β1 ^ 2 := by field_simp; ring
      rw [this, mul_div_assoc', div_lt_div_iff_of_pos_right hb2]; exact he2
    · have : t * ((t * BBv - ABv) / β1 ^ 2) - (t ^ 2 * BBv - 2 * t * ABv + AAv) / β1 ^ 2 =
          (t * ABv - AAv) / β1 ^ 2 := by field_simp; ring
      rw [this]
      field_simp
      linarith [htie]
  · rw [hPB, inner_smul_right]
    have : ⟪a' - c, b' - a⟫ = -κA := by
      rw [← neg_sub c a', inner_neg_left, real_inner_comm, hκA]
    rw [this]
    exact mul_neg_of_pos_of_neg (inv_pos.2 hβ1') (neg_lt_zero.2 hκpos)

end C2
end Type08Sp
end Minimality
