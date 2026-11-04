module

public import Minimality.Type08S.C2K22Z1C1bA
public import Minimality.Type08S.C2K17HZ

@[expose] public section


set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

set_option maxHeartbeats 12800000 in
/-- Type 08, special-position corner `Tc Z1`, cell C1 (view `a - c'`, silhouette `a, d, b, a', b'`), for `S2 < 0`. -/
theorem k22z1_c1_le {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K17hTcZ1 a a' b b' c c' d)
    (hS : ⟪b - a, a - c'⟫ ≤ 0) : HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hZ, hz1, hd1, hpq⟩ := h
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα1, hα4, hβ1, hγ4, hb6, hαγ, hE⟩ := k17ga_tc_coords W hZ
  set p := a - d with hp
  set q := b - d with hq
  set r := c - d with hr
  have hpq' : ⟪p, q⟫ = 0 := hpq
  have hqp : ⟪q, p⟫ = 0 := by rw [real_inner_comm]; exact hpq'
  have hrp : ⟪r, p⟫ = ⟪p, r⟫ := real_inner_comm _ _
  have hrq : ⟪r, q⟫ = ⟪q, r⟫ := real_inner_comm _ _
  have hq0 : q ≠ 0 := by intro h0; apply hdet; rw [h0]; simp [det3_expand]
  have hp0 : p ≠ 0 := by intro h0; apply hdet; rw [h0]; simp [det3_expand]
  have hqq : 0 < ⟪q, q⟫ := real_inner_self_pos.2 hq0
  have hpp : 0 < ⟪p, p⟫ := real_inner_self_pos.2 hp0
  -- qr = 0 from ζ(d,b) = 0
  have hzdb : ⟪d - b, a - b'⟫ = 0 := hZ.2.2.1
  have hqr : ⟪q, r⟫ = 0 := by
    have e1 : d - b = -q := by rw [hq]; abel
    have e2 : a - b' = (1 - α4) • p - γ4 • r := by rw [hb', hp, hr]; module
    rw [e1, e2] at hzdb
    simp only [inner_neg_left, inner_sub_right, inner_smul_right, hpq', hqp] at hzdb
    have : γ4 * ⟪q, r⟫ = 0 := by linarith
    rcases mul_eq_zero.1 this with h0 | h0
    · linarith
    · exact h0
  -- β1 = 1
  have hβ1' : β1 = 1 := by
    have e1 : d - b = -q := by rw [hq]; abel
    have e2 : c' - b = α1 • p + (β1 - 1) • q := by rw [hc', hp, hq]; module
    rw [e1, e2] at hd1
    simp only [inner_neg_left, inner_add_right, inner_smul_right, hpq', hqp] at hd1
    have : (β1 - 1) * ⟪q, q⟫ = 0 := by linarith
    rcases mul_eq_zero.1 this with h0 | h0
    · linarith
    · linarith
  subst hβ1'
  -- reparametrize
  obtain ⟨k, hk⟩ : ∃ k, β6 = 1 + k := ⟨β6 - 1, by ring⟩
  obtain ⟨g, hg⟩ : ∃ g, γ4 = 1 + g := ⟨γ4 - 1, by ring⟩
  obtain ⟨u, hu⟩ : ∃ u, α1 = 1 + u := ⟨α1 - 1, by ring⟩
  have hg0 : 0 ≤ g := by nlinarith
  have hu0 : 0 < u := by linarith
  have hα4' : α4 = 1 + (1 + g) * k := by rw [hg, hk] at hαγ; linarith
  have hk0 : 0 < k := by
    by_contra hh; push Not at hh
    have : (1 + g) * k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hh
    linarith
  subst hk hg hu hα4'
  obtain ⟨w, hw0, hwu⟩ : ∃ w, 0 < w ∧ w * u = 1 := ⟨1 / u, by positivity, by field_simp⟩
  -- Gram facts
  have eR : a - c' = (-u) • p - q := by rw [hc', hp, hq]; module
  have eS : b - a = q - p := by rw [hp, hq]; abel
  rw [eR, eS] at hS
  simp only [inner_sub_left, inner_sub_right, inner_smul_right, inner_smul_left, conj_trivial, hpq', hqp, real_inner_comm p q] at hS
  have hS' : u * ⟪p, p⟫ ≤ ⟪q, q⟫ := by nlinarith
  have htie : ⟪c' - c, a - b'⟫ = 0 := hz1
  have e3 : c' - c = (1 + u) • p + q - r := by rw [hc', hp, hq, hr]; module
  have e4 : a - b' = (1 - (1 + (1 + g) * k)) • p - (1 + g) • r := by rw [hb', hp, hr]; module
  rw [e3, e4] at htie
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_smul_right, inner_smul_left, conj_trivial, hpq', hqp, hqr,
    hrq, hrp] at htie
  have hG : 0 < ⟪p, p⟫ * ⟪r, r⟫ - ⟪p, r⟫ ^ 2 := by
    have hv : (⟪p, p⟫ • r - ⟪p, r⟫ • p) ≠ 0 := by
      intro h0
      have : det3 p q (⟪p, p⟫ • r - ⟪p, r⟫ • p) = ⟪p, p⟫ * det3 p q r := by
        simp only [det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
      rw [h0] at this
      have h1 : ⟪p, p⟫ * det3 p q r = 0 := by rw [← this]; simp [det3_expand]
      rcases mul_eq_zero.1 h1 with h2 | h2
      · linarith
      · exact hdet h2
    have h2 := real_inner_self_pos.2 hv
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, conj_trivial, real_inner_comm p r] at h2
    have : 0 < ⟪p, p⟫ * (⟪p, p⟫ * ⟪r, r⟫ - ⟪p, r⟫ ^ 2) := by nlinarith
    exact pos_of_mul_pos_right this hpp.le |>.trans_le le_rfl
  have hprod : (⟪p, r⟫ - (1 + u) * ⟪p, p⟫) * (⟪p, r⟫ + k * ⟪p, p⟫) < 0 := by
    have hg1 : 0 < 1 + g := by linarith
    have : (1 + g) * (⟪p, p⟫ * ⟪r, r⟫ - ⟪p, r⟫ ^ 2) = -((1 + g) * ((⟪p, r⟫ - (1 + u) * ⟪p, p⟫) * (⟪p, r⟫ + k * ⟪p, p⟫))) := by
      linear_combination ⟪p, p⟫ * htie
    have h3 := mul_pos hg1 hG
    rw [this] at h3
    nlinarith
  have hgr : 0 < ⟪p, r⟫ + k * ⟪p, p⟫ := by
    by_contra hh; push Not at hh
    have f1 : ⟪p, r⟫ - (1 + u) * ⟪p, p⟫ ≤ 0 := by nlinarith [mul_pos hk0 hpp, mul_pos hu0 hpp]
    nlinarith [mul_nonneg_of_nonpos_of_nonpos f1 hh]
  -- frame
  obtain ⟨P, hPq⟩ : ∃ P : ℝ³, P = q := ⟨_, rfl⟩
  obtain ⟨Q, hQr⟩ : ∃ Q : ℝ³, Q = r := ⟨_, rfl⟩
  obtain ⟨R, hRe⟩ : ∃ R : ℝ³, R = (-u) • p - q := ⟨_, rfl⟩
  have hRac : R = a - c' := by rw [hRe, ← eR]
  have hΔ : det3 P Q R ≠ 0 := by
    have e : det3 P Q R = (-u) * det3 p q r := by
      rw [hPq, hQr, hRe]
      simp only [hp, hq, hr, det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e]; exact mul_ne_zero (by linarith) hdet
  have hpw : p = (-w) • P + (-w) • R := by
    rw [hRe, hPq]
    have : (-w) • q + (-w) • ((-u) • p - q) = (w * u) • p := by module
    rw [this, hwu, one_smul]
  have hpa : a = d + p := by rw [hp]; abel
  have Ed : fpoint P Q R d (0, 0, 0) = d := by rw [k17f_fp]; module
  have Ea : fpoint P Q R d (-w, 0, -w) = a := by
    rw [k17f_fp, hpa, hpw]; module
  have Eb : fpoint P Q R d (1, 0, 0) = b := by rw [k17f_fp, hPq, hq]; module
  have Ec : fpoint P Q R d (0, 1, 0) = c := by rw [k17f_fp, hQr, hr]; module
  have Ea' : fpoint P Q R d (1 + k, 1, 0) = a' := by rw [k17f_fp, ha', hPq, hQr]; module
  have Eb' : fpoint P Q R d (-(1 + (1 + g) * k) * w, 1 + g, -(1 + (1 + g) * k) * w) = b' := by
    rw [k17f_fp, hb', hQr, hpw]; module
  have Ec' : fpoint P Q R d (-w, 0, -w - 1) = c' := by
    have : c' = d + p - R := by rw [hc', hRe]; module
    rw [k17f_fp, this, hpw]; module
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hPR : ⟪P, R⟫ = -⟪q, q⟫ := by
    rw [hPq, hRe]; simp only [inner_sub_right, inner_smul_right, hqp]; ring
  have hQR : ⟪Q, R⟫ = -u * ⟪p, r⟫ := by
    rw [hQr, hRe]; simp only [inner_sub_right, inner_smul_right, hrq, hqr, hrp]; ring
  have hRR : ⟪R, R⟫ = u ^ 2 * ⟪p, p⟫ + ⟪q, q⟫ := by
    rw [hRe]; simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, conj_trivial, hpq', hqp]; ring
  have hg1 : 0 < 1 + g := by linarith
  have z0 : ⟪fpoint P Q R d (-w, 0, -w), R⟫ = ⟪d, R⟫ - u * ⟪p, p⟫ := by
    rw [hz]; simp only [hPR, hQR, hRR]; linear_combination (-(u * ⟪p, p⟫)) * hwu
  have z1 : ⟪fpoint P Q R d (0, 0, 0), R⟫ = ⟪d, R⟫ := by rw [hz]; simp
  have z2 : ⟪fpoint P Q R d (1, 0, 0), R⟫ = ⟪d, R⟫ - ⟪q, q⟫ := by rw [hz]; simp only [hPR]; ring
  have z3 : ⟪fpoint P Q R d (1 + k, 1, 0), R⟫ = ⟪d, R⟫ - (1 + k) * ⟪q, q⟫ - u * ⟪p, r⟫ := by
    rw [hz]; simp only [hPR, hQR]; ring
  have z4 : ⟪fpoint P Q R d (-(1 + (1 + g) * k) * w, 1 + g, -(1 + (1 + g) * k) * w), R⟫ =
      ⟪d, R⟫ - (1 + (1 + g) * k) * (u * ⟪p, p⟫) - (1 + g) * (u * ⟪p, r⟫) := by
    rw [hz]; simp only [hPR, hQR, hRR]
    linear_combination (-((1 + (1 + g) * k) * (u * ⟪p, p⟫))) * hwu
  have i01 : -(u * ⟪p, p⟫) < 0 := by nlinarith [mul_pos hu0 hpp]
  have i21 : -⟪q, q⟫ < 0 := by linarith
  have i32 : -(1 + k) * ⟪q, q⟫ - u * ⟪p, r⟫ < -⟪q, q⟫ := by
    nlinarith [mul_pos hu0 hgr, mul_nonneg hk0.le (sub_nonneg.2 hS')]
  have i40 : -(1 + (1 + g) * k) * (u * ⟪p, p⟫) - (1 + g) * (u * ⟪p, r⟫) < -(u * ⟪p, p⟫) := by
    nlinarith [mul_pos (mul_pos hg1 hu0) hgr]
  have hR0 : R ≠ 0 := k17f_r0 hΔ
  refine ⟨R, hR0, ?_⟩
  refine k18_cone_cell (V8 a a' b b' c c' d) P Q R d hΔ (k := 5) (by norm_num) (k22z1c1bY w k g)
    (k22z1c1bY_inj hw0 hk0 hg0) ?_ [(1, 0), (0, 1)] (by simp) ?_ ?_ ?_
    (ρ1 := 1) (ρ2 := 1) (δ1 := 0) (δ2 := 0) ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · rw [k22z1c1bY_0, Ea]; simp [V8]
    · rw [k22z1c1bY_1, Ed]; simp [V8]
    · rw [k22z1c1bY_2, Eb]; simp [V8]
    · rw [k22z1c1bY_3, Ea']; simp [V8]
    · rw [k22z1c1bY_4, Eb']; simp [V8]
  · intro v1 v2 hC D hD
    have h1 := hC (1, 0) (by simp)
    have h2 := hC (0, 1) (by simp)
    simp only at h1 h2
    exact (k22z1c1b_tsc hD hw0 hk0 hg0 (by linarith) (by linarith)).1
  · intro y hy hyx
    have hV : y = fpoint P Q R d (-w, 0, -w) ∨ y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨
        y = fpoint P Q R d (1 + k, 1, 0) ∨
        y = fpoint P Q R d (-(1 + (1 + g) * k) * w, 1 + g, -(1 + (1 + g) * k) * w) ∨
        y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (-w, 0, -w - 1) := by
      rw [Ea, Ed, Eb, Ea', Ec, Eb', Ec']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    have hT : ∀ v1 v2 : ℝ, k18Cone [(1, 0), (0, 1)] v1 v2 → ∀ D : ℝ, 0 < D →
        ∀ t ∈ [((0 : ℝ), (1 : ℝ), (0 : ℝ)), (-w, 0, -w - 1)], ∀ i : ZMod 5,
          TSc D (k22z1c1bY w k g (i + 1) - k22z1c1bY w k g i) (t - k22z1c1bY w k g i) (v1, v2, 0) := by
      intro v1 v2 hC D hD
      have h1 := hC (1, 0) (by simp)
      have h2 := hC (0, 1) (by simp)
      simp only at h1 h2
      exact (k22z1c1b_tsc hD hw0 hk0 hg0 (by linarith) (by linarith)).2
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by rw [k22z1c1bY_0])).elim
    · exact (hyx 1 (by rw [k22z1c1bY_1])).elim
    · exact (hyx 2 (by rw [k22z1c1bY_2])).elim
    · exact (hyx 3 (by rw [k22z1c1bY_3])).elim
    · exact (hyx 4 (by rw [k22z1c1bY_4])).elim
    · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT v1 v2 hC D hD _ (by simp) i⟩
    · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT v1 v2 hC D hD _ (by simp) i⟩
  · intro v1 v2 hC hw
    obtain ⟨e0, e1, e2, e3, e4, f0, f1, f2, f3, f4⟩ := k19_z5
    refine k19_lexUni_nb _ _ hw 1 ?_ ?_ ?_
    · rw [e1]; left; simp only [k22z1c1bY_0, k22z1c1bY_1, z0, z1]; linarith
    · rw [f1]; left; simp only [k22z1c1bY_1, k22z1c1bY_2, z1, z2]; linarith
    · intro i hi
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · right; rw [f0]; left; simp only [k22z1c1bY_0, k22z1c1bY_1, z0, z1]; linarith
      · exact absurd rfl hi
      · left; rw [e2]; left; simp only [k22z1c1bY_1, k22z1c1bY_2, z1, z2]; linarith
      · left; rw [e3]; left; simp only [k22z1c1bY_2, k22z1c1bY_3, z2, z3]; linarith
      · right; rw [f4]; left; simp only [k22z1c1bY_4, k22z1c1bY_0, z4, z0]; linarith
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> (left; norm_num)

end C2
end Type08Sp
end Minimality
