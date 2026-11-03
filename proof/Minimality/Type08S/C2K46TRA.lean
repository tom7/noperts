module

public import Minimality.Type08S.C2K45ZA

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
open scoped RealInnerProductSpace
open Minimality Minimality.Type08Sp Minimality.Type08Sp.C2

namespace Minimality.Type08Sp.C2


set_option maxHeartbeats 4000000 in
theorem k55_chart {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hβ : 1 < β1) (hσ : β6 + γ6 = β1) (hL : ⟪a - c', a - d⟫ = 0)
    (h : K45SigRest a a' b b' c c' d α1 β1 β6 γ6) :
    ∃ ea w kap rho : ℝ, 0 < ea ∧ 0 < w ∧ 0 < kap ∧ 0 < rho ∧ α1 = 1 + ea ∧ β1 = 2 + ea ∧
      β6 = (2 + ea) / 2 ∧ γ6 = (2 + ea) / 2 ∧
      ⟪a - d, a - d⟫ = (2 + ea) ^ 2 * w ∧ ⟪a - d, b - d⟫ = -(ea * (2 + ea) * w) ∧
      ⟪a - d, c - d⟫ = -(ea * (2 + ea) * w) ∧ ⟪b - d, c - d⟫ = ea ^ 2 * w ∧
      ⟪b - d, b - d⟫ = kap + ea ^ 2 * w ∧ ⟪c - d, c - d⟫ = rho + ea ^ 2 * w ∧
      kap * rho = 2 * ea * w * (kap + rho) ∧ ea * kap ≤ (2 + ea) * rho ∧ ea * rho < (2 + ea) * kap := by
  obtain ⟨hΛ0, hM00, hori, hdep, hlit, hbe⟩ := h
  have hM0 : ⟪b - d, c - d⟫ * ⟪a - d, a - d⟫ - ⟪a - d, b - d⟫ ^ 2 = 0 := by
    unfold k33Mpp at hM00; linarith
  have hΛ : 0 ≤ (β1 - 1) * (⟪b - d, c - d⟫ * ⟪a - d, a - d⟫ - ⟪a - d, b - d⟫ ^ 2) +
      (γ6 - 1) * (⟪c - d, c - d⟫ - ⟪b - d, c - d⟫) * ⟪a - d, a - d⟫ := by
    unfold k33Lam k33Mpp at hΛ0; linarith
  have hori := hori.le
  obtain ⟨hdet, hc', hb', ha', hα1', hβ1', h1, hβ6', hγ6', h3⟩ := hC
  obtain ⟨m1, m2, m3⟩ := hM
  obtain ⟨hr1, hr2⟩ := hrel
  set p := a - d with hp
  set q := b - d with hq
  set r := c - d with hr
  have hp0 : p ≠ 0 := by intro h0; apply hdet; rw [h0]; simp [det3_expand]
  have hpp : 0 < ⟪p, p⟫ := real_inner_self_pos.2 hp0
  have hm1 : ⟪p, q⟫ = ⟪p, r⟫ := by
    have : ⟪p, b - c⟫ = ⟪p, q⟫ - ⟪p, r⟫ := by
      rw [← inner_sub_right]; congr 1; rw [hq, hr]; abel
    linarith
  have hqp : ⟪q, p⟫ = ⟪p, q⟫ := real_inner_comm _ _
  have hrp : ⟪r, p⟫ = ⟪p, r⟫ := real_inner_comm _ _
  have hrq : ⟪r, q⟫ = ⟪q, r⟫ := real_inner_comm _ _
  have hQR : ⟪q, r⟫ < ⟪q, q⟫ := by
    have e : c' - d = α1 • p + β1 • q := by rw [hc', hp, hq]; module
    have e2 : b - c = q - r := by rw [hq, hr]; abel
    rw [e, e2] at m2
    simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real, inner_sub_right] at m2
    have h0 : α1 * (⟪p, q⟫ - ⟪p, r⟫) = 0 := by rw [hm1]; ring
    nlinarith [m2, h0, hqp, hrp]
  have hRT : ⟪q, r⟫ < ⟪r, r⟫ := by
    have e : b' - d = α1 • p + β1 • r := by rw [hb', hp, hr]; module
    have e2 : b - c = q - r := by rw [hq, hr]; abel
    rw [e, e2] at m3
    simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real, inner_sub_right] at m3
    have h0 : α1 * (⟪p, q⟫ - ⟪p, r⟫) = 0 := by rw [hm1]; ring
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg hβ1'.le (sub_nonneg.2 hh), m3, h0, hrq]
  have hs : ⟪p, q⟫ < 0 := by
    have hW : 0 < ⟪q, q⟫ + ⟪r, r⟫ - 2 * ⟪q, r⟫ := by linarith
    have h1' : 0 < (β1 - 1) * (⟪q, q⟫ * ⟪r, r⟫ - ⟪q, r⟫ ^ 2) := mul_pos (by linarith) hr2
    by_contra hh; push Not at hh
    have h2 : 0 ≤ α1 * ⟪p, q⟫ * (⟪q, q⟫ + ⟪r, r⟫ - 2 * ⟪q, r⟫) :=
      mul_nonneg (mul_nonneg hα1'.le hh) hW.le
    nlinarith [hr1]
  have hLe : (1 - α1) * ⟪p, p⟫ - β1 * ⟪p, q⟫ = 0 := by
    have e : a - c' = (1 - α1) • p - β1 • q := by rw [hc', hp, hq]; module
    rw [e] at hL
    simp only [inner_sub_left, inner_smul_left, RCLike.conj_to_real, hqp] at hL
    linarith
  have hα1 : 1 < α1 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg (sub_nonneg.2 hh) hpp.le, mul_pos hβ1' (neg_pos.2 hs), hLe]
  have hspr : ⟪p, r⟫ = ⟪p, q⟫ := hm1.symm
  have e1 : a - b = p - q := by rw [hp, hq]; abel
  have eaa : a - a' = p - β6 • q - γ6 • r := by rw [ha', hp, hq, hr]; module
  rw [eaa] at hlit
  clear_value p q r
  have ha2 : a = d + p := by rw [hp]; abel
  have hb2 : b = d + q := by rw [hq]; abel
  have hc2 : c = d + r := by rw [hr]; abel
  have hc'2 := hc'
  have hb'2 := hb'
  have ha'2 := ha'
  obtain ⟨ea, rfl⟩ : ∃ ea, α1 = 1 + ea := ⟨α1 - 1, by ring⟩
  obtain ⟨ee, rfl⟩ : ∃ ee, β1 = 1 + ee := ⟨β1 - 1, by ring⟩
  obtain rfl : γ6 = 1 + ee - β6 := by linarith
  have hea : 0 < ea := by linarith
  have hee : 0 < ee := by linarith
  obtain ⟨w, hwd⟩ : ∃ w : ℝ, w = ⟪p, p⟫ / (1 + ee) ^ 2 := ⟨_, rfl⟩
  have hb1 : 0 < 1 + ee := by linarith
  have ha1 : 0 < 1 + ea := by linarith
  have hw : 0 < w := by rw [hwd]; positivity
  have Epp : ⟪p, p⟫ = (1 + ee) ^ 2 * w := by rw [hwd]; field_simp
  have Es : ⟪p, q⟫ = -(ea * (1 + ee) * w) := by
    have : (1 + ee) * ⟪p, q⟫ = (1 + ee) * (-(ea * (1 + ee) * w)) := by rw [Epp] at hLe; nlinarith [hLe]
    exact mul_left_cancel₀ hb1.ne' this
  have Es2 : ⟪p, r⟫ = -(ea * (1 + ee) * w) := by rw [hspr, Es]
  have Eqr : ⟪q, r⟫ = ea ^ 2 * w := by
    have : (⟪q, r⟫ - ea ^ 2 * w) * ⟪p, p⟫ = 0 := by
      rw [Es, Epp] at hM0; rw [Epp]; linear_combination hM0
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h hpp.ne'
  obtain ⟨kap, hkd⟩ : ∃ kap : ℝ, kap = ⟪q, q⟫ - ⟪q, r⟫ := ⟨_, rfl⟩
  obtain ⟨rho, hrd⟩ : ∃ rho : ℝ, rho = ⟪r, r⟫ - ⟪q, r⟫ := ⟨_, rfl⟩
  have hk : 0 < kap := by rw [hkd]; linarith
  have hrho : 0 < rho := by rw [hrd]; linarith
  have Eqq : ⟪q, q⟫ = kap + ea ^ 2 * w := by rw [Eqr] at hkd; linarith
  have Err : ⟪r, r⟫ = rho + ea ^ 2 * w := by rw [Eqr] at hrd; linarith
  have hrel' : ee * (kap * rho) = ea * (ea + 1 + ee) * w * (kap + rho) := by
    rw [Es, Eqq, Eqr, Err] at hr1
    linear_combination hr1
  have hL0 : β6 ≤ ee := by
    rw [hM0, mul_zero, zero_add] at hΛ
    have h5 : 0 ≤ (ee - β6) * (rho * ⟪p, p⟫) := by
      have : (1 + ee - β6 - 1) * (⟪r, r⟫ - ⟪q, r⟫) * ⟪p, p⟫ = (ee - β6) * (rho * ⟪p, p⟫) := by
        rw [hrd]; ring
      rw [← this]; exact hΛ
    by_contra hh; push Not at hh
    nlinarith [mul_pos (mul_pos hrho hpp) (sub_pos.2 hh)]
  have hg6 : 0 < 1 + ee - β6 := by linarith
  have hβ6 := hβ6'
  have hSpos : 0 < 1 + ea + ee := by linarith
  -- dep
  have hβ6e : β6 * (1 + ea + ee) = (1 + ea) * (1 + ee) := by
    have hdep0 := hdep
    unfold k41Dep at hdep0
    rw [e1, ← hp, ← hq, ← hr] at hdep0
    simp only [inner_neg_right, inner_add_right, inner_smul_right, inner_sub_left, hqp] at hdep0
    rw [Epp, Es, Eqq, Eqr] at hdep0
    field_simp at hdep0
    have key : kap * ((1 + ea) * (1 + ee) - β6 * (1 + ea + ee)) = 0 := by linear_combination hdep0
    rcases mul_eq_zero.1 key with h | h
    · exact absurd h hk.ne'
    · linarith
  have hb6 : β6 = (1 + ea) * (1 + ee) / (1 + ea + ee) := by
    field_simp; linarith
  have hwS : w = ee * kap * rho / (ea * (1 + ea + ee) * (kap + rho)) := by
    field_simp; linear_combination (-1 : ℝ) * hrel'
  have hee1 : ee = 1 + ea := by linarith
  subst hee1
  have hO : ea * kap ≤ (1 + (1 + ea)) * rho := by
    have h := hori
    unfold k28b2rOri at h
    rw [Epp, Es, Eqq, Eqr, Err] at h
    have h2 : ((1 + ea) * (1 + ea) ^ 2 * (1 + (1 + ea)) ^ 3 * kap * rho / (ea * (1 + ea + (1 + ea)) ^ 2 * (kap + rho))) *
        (ea * kap - (1 + (1 + ea)) * rho) ≤ 0 := by
      convert h using 1
      rw [hwS, hb6]
      field_simp
      ring
    have hFp : 0 < ((1 + ea) * (1 + ea) ^ 2 * (1 + (1 + ea)) ^ 3 * kap * rho / (ea * (1 + ea + (1 + ea)) ^ 2 * (kap + rho))) := by positivity
    by_contra hh; push Not at hh
    nlinarith [mul_pos hFp (sub_pos.2 hh)]
  have hb6' : β6 = (2 + ea) / 2 := by rw [hb6]; field_simp; ring
  have hg6' : 1 + (1 + ea) - β6 = (2 + ea) / 2 := by rw [hb6']; ring
  have hkr : kap * rho = 2 * ea * w * (kap + rho) := by
    have : (1 + ea) * (kap * rho - 2 * ea * w * (kap + rho)) = 0 := by linear_combination hrel'
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have hlit2 : 0 < (1 + ea) * (2 + ea) * (2 * w * (1 + ea) - rho / 2) := by
    simp only [inner_sub_left, inner_smul_left, RCLike.conj_to_real, hqp, hrp] at hlit
    rw [Epp, Es, Es2, Eqr, Err, hb6'] at hlit
    convert hlit using 1
    ring
  have hlit3 : rho < 4 * w * (1 + ea) := by
    have h1 : 0 < (1 + ea) * (2 + ea) := by positivity
    have := (pos_iff_pos_of_mul_pos hlit2).1 h1
    linarith
  refine ⟨ea, w, kap, rho, hea, hw, hk, hrho, rfl, by ring, by rw [hb6'], hg6', ?_, ?_, ?_, ?_, ?_, ?_, hkr, by linarith, ?_⟩
  · rw [Epp]; ring
  · rw [Es]; ring
  · rw [Es2]; ring
  · exact Eqr
  · exact Eqq
  · exact Err
  · nlinarith [mul_pos hrho (mul_pos hea (add_pos hk hrho)), hkr, mul_lt_mul_of_pos_left hlit3 (mul_pos hea (add_pos hk hrho))]

end Minimality.Type08Sp.C2
