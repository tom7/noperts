module

public import Minimality.Type08S.C2K22Z1GC2A
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
/-- Type 08, special-position corner `Tc Z1`, `γ4 = 1`, `S2 > 0`, `S3 ≤ 0`: cell C2 (view `a - c'`, silhouette `a, d, b, a', b', c'`). -/
theorem k22z1g_c2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K17hTcZ1 a a' b b' c c' d)
    (hγ : ∀ α4 γ4 : ℝ, b' = d + α4 • (a - d) + γ4 • (c - d) → γ4 = 1)
    (hS2 : 0 < ⟪b - a, a - c'⟫) (hS3 : ⟪a' - b, a - c'⟫ ≤ 0) : HasLexCell (V8 a a' b b' c c' d) := by
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
  have hγ1 : γ4 = 1 := hγ α4 γ4 hb'
  subst hγ1
  obtain ⟨k, hk⟩ : ∃ k, β6 = 1 + k := ⟨β6 - 1, by ring⟩
  obtain ⟨u, hu⟩ : ∃ u, α1 = 1 + u := ⟨α1 - 1, by ring⟩
  have hu0 : 0 < u := by linarith
  have hα4' : α4 = 1 + k := by rw [hk] at hαγ; linarith
  have hk0 : 0 < k := by linarith
  subst hk hu hα4'
  obtain ⟨w, hw0, hwu⟩ : ∃ w, 0 < w ∧ w * u = 1 := ⟨1 / u, by positivity, by field_simp⟩
  have hr0 : r ≠ 0 := by intro h0; apply hdet; rw [h0]; simp [det3_expand]
  have hrr : 0 < ⟪r, r⟫ := real_inner_self_pos.2 hr0
  -- Gram facts
  have eR : a - c' = (-u) • p - q := by rw [hc', hp, hq]; module
  have eS : b - a = q - p := by rw [hp, hq]; abel
  have eT : a' - b = k • q + r := by rw [ha', hq, hr]; module
  rw [eR, eS] at hS2
  rw [eR, eT] at hS3
  simp only [inner_sub_left, inner_sub_right, inner_smul_right, inner_smul_left, inner_add_left, conj_trivial, hpq', hqp,
    real_inner_comm p q, hrp, hrq, hqr] at hS2 hS3
  have hS' : ⟪q, q⟫ < u * ⟪p, p⟫ := by nlinarith
  have hS3' : 0 ≤ k * ⟪q, q⟫ + u * ⟪p, r⟫ := by nlinarith
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
  have Eb' : fpoint P Q R d (-(1 + k) * w, 1, -(1 + k) * w) = b' := by
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
  have z0 : ⟪fpoint P Q R d (-w, 0, -w), R⟫ = ⟪d, R⟫ - u * ⟪p, p⟫ := by
    rw [hz]; simp only [hPR, hQR, hRR]; linear_combination (-(u * ⟪p, p⟫)) * hwu
  have z1 : ⟪fpoint P Q R d (0, 0, 0), R⟫ = ⟪d, R⟫ := by rw [hz]; simp
  have z2 : ⟪fpoint P Q R d (1, 0, 0), R⟫ = ⟪d, R⟫ - ⟪q, q⟫ := by rw [hz]; simp only [hPR]; ring
  have z3 : ⟪fpoint P Q R d (1 + k, 1, 0), R⟫ = ⟪d, R⟫ - (1 + k) * ⟪q, q⟫ - u * ⟪p, r⟫ := by
    rw [hz]; simp only [hPR, hQR]; ring
  have z4 : ⟪fpoint P Q R d (-(1 + k) * w, 1, -(1 + k) * w), R⟫ =
      ⟪d, R⟫ - (1 + k) * (u * ⟪p, p⟫) - u * ⟪p, r⟫ := by
    rw [hz]; simp only [hPR, hQR, hRR]
    linear_combination (-((1 + k) * (u * ⟪p, p⟫))) * hwu
  have z5 : ⟪fpoint P Q R d (-w, 0, -w - 1), R⟫ = ⟪d, R⟫ - u * ⟪p, p⟫ - (u ^ 2 * ⟪p, p⟫ + ⟪q, q⟫) := by
    rw [hz]; simp only [hPR, hQR, hRR]; linear_combination (-(u * ⟪p, p⟫)) * hwu
  have hpu : 0 < u * ⟪p, p⟫ := mul_pos hu0 hpp
  have hRRp : 0 < u ^ 2 * ⟪p, p⟫ + ⟪q, q⟫ := by positivity
  have hR0 : R ≠ 0 := k17f_r0 hΔ
  have hcone : ∀ v1 v2 : ℝ, k18Cone [(0, 1), (-u, -k), (-k * ⟪q, q⟫, -⟪r, r⟫)] v1 v2 →
      0 < v2 ∧ v1 + w * k * v2 < 0 ∧ 0 < -(k * ⟪q, q⟫) * v1 + -⟪r, r⟫ * v2 := by
    intro v1 v2 hC
    have h1 := hC (0, 1) (by simp)
    have h2 := hC (-u, -k) (by simp)
    have h3 := hC (-k * ⟪q, q⟫, -⟪r, r⟫) (by simp)
    simp only at h1 h2 h3
    refine ⟨by linarith, ?_, by linarith⟩
    have := mul_pos hw0 h2
    have e : w * (-u * v1 + -k * v2) = -v1 - w * k * v2 := by linear_combination (-v1) * hwu
    linarith
  refine ⟨R, hR0, ?_⟩
  refine k18_cone_cell (V8 a a' b b' c c' d) P Q R d hΔ (k := 6) (by norm_num) (k22z1gc2Y w k)
    (k22z1gc2Y_inj hw0 hk0) ?_ [(0, 1), (-u, -k), (-k * ⟪q, q⟫, -⟪r, r⟫)] (by simp) ?_ ?_ ?_
    (ρ1 := -(k * w + ⟪r, r⟫ / (k * ⟪q, q⟫) + 1)) (ρ2 := 1) (δ1 := 0) (δ2 := 0) ?_
  · intro i
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [k22z1gc2Y_0, Ea]; simp [V8]
    · rw [k22z1gc2Y_1, Ed]; simp [V8]
    · rw [k22z1gc2Y_2, Eb]; simp [V8]
    · rw [k22z1gc2Y_3, Ea']; simp [V8]
    · rw [k22z1gc2Y_4, Eb']; simp [V8]
    · rw [k22z1gc2Y_5, Ec']; simp [V8]
  · intro v1 v2 hC D hD
    obtain ⟨h1, h2, -⟩ := hcone v1 v2 hC
    exact (k22z1gc2_tsc hD hw0 hk0 h1 h2).1
  · intro y hy hyx
    have hV : y = fpoint P Q R d (-w, 0, -w) ∨ y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨
        y = fpoint P Q R d (1 + k, 1, 0) ∨
        y = fpoint P Q R d (-(1 + k) * w, 1, -(1 + k) * w) ∨
        y = fpoint P Q R d (-w, 0, -w - 1) ∨ y = fpoint P Q R d (0, 1, 0) := by
      rw [Ea, Ed, Eb, Ea', Ec, Eb', Ec']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by rw [k22z1gc2Y_0])).elim
    · exact (hyx 1 (by rw [k22z1gc2Y_1])).elim
    · exact (hyx 2 (by rw [k22z1gc2Y_2])).elim
    · exact (hyx 3 (by rw [k22z1gc2Y_3])).elim
    · exact (hyx 4 (by rw [k22z1gc2Y_4])).elim
    · exact (hyx 5 (by rw [k22z1gc2Y_5])).elim
    · refine ⟨_, rfl, fun v1 v2 hC D hD i => ?_⟩
      obtain ⟨h1, h2, -⟩ := hcone v1 v2 hC
      exact (k22z1gc2_tsc hD hw0 hk0 h1 h2).2 i
  · intro v1 v2 hC hw
    obtain ⟨hv2, -, h3⟩ := hcone v1 v2 hC
    obtain ⟨e0, e1, e2, e3, e4, e5, f0, f1, f2, f3, f4, f5⟩ := k19_z6
    have hPP : ⟪P, P⟫ = ⟪q, q⟫ := by rw [hPq]
    have hQQ : ⟪Q, Q⟫ = ⟪r, r⟫ := by rw [hQr]
    have hPQ : ⟪P, Q⟫ = 0 := by rw [hPq, hQr]; exact hqr
    have hQP : ⟪Q, P⟫ = 0 := by rw [real_inner_comm]; exact hPQ
    refine k19_lexUni_nb _ _ hw 1 ?_ ?_ ?_
    · rw [e1]; left; simp only [k22z1gc2Y_0, k22z1gc2Y_1, z0, z1]; linarith
    · rw [f1]; left; simp only [k22z1gc2Y_1, k22z1gc2Y_2, z1, z2]; linarith
    · intro i hi
      rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl
      · right; rw [f0]; left; simp only [k22z1gc2Y_0, k22z1gc2Y_1, z0, z1]; linarith
      · exact absurd rfl hi
      · left; rw [e2]; left; simp only [k22z1gc2Y_1, k22z1gc2Y_2, z1, z2]; linarith
      · left; rw [e3]
        rcases hS3'.eq_or_lt with h0 | h0
        · right
          refine ⟨?_, ?_⟩
          · simp only [k22z1gc2Y_2, k22z1gc2Y_3, z2, z3]; linarith
          · simp only [k22z1gc2Y_2, k22z1gc2Y_3, k17f_fp, fcomb, inner_add_left, inner_add_right, inner_smul_left,
              inner_smul_right, conj_trivial, hPP, hQQ, hPQ, hQP, zero_smul, inner_zero_right, inner_zero_left]
            nlinarith
        · left; simp only [k22z1gc2Y_2, k22z1gc2Y_3, z2, z3]; linarith
      · left; rw [e4]; left; simp only [k22z1gc2Y_3, k22z1gc2Y_4, z3, z4]
        nlinarith [mul_pos (show 0 < 1 + k by linarith) (sub_pos.2 hS')]
      · right; rw [f5]; left; simp only [k22z1gc2Y_5, k22z1gc2Y_0, z5, z0]; linarith
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    have hx : 0 < ⟪r, r⟫ / (k * ⟪q, q⟫) := by positivity
    have hx' : k * ⟪q, q⟫ * (⟪r, r⟫ / (k * ⟪q, q⟫)) = ⟪r, r⟫ := by field_simp
    have hukw : u * (k * w) = k := by linear_combination k * hwu
    rcases hl with rfl | rfl | rfl
    · left; norm_num
    · left; simp only; nlinarith [mul_pos hu0 hx]
    · left; simp only; nlinarith [mul_pos (mul_pos hk0 hqq) hw0, mul_pos hk0 hqq, mul_pos hk0 hk0]

end C2
end Type08Sp
end Minimality
