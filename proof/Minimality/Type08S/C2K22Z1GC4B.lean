module

public import Minimality.Type08S.C2K22Z1GC4A
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
/-- Type 08, special-position corner `Tc Z1`, `γ4 = 1`, `S2 > 0`, `S3 > 0`: cell C4 (view `a - c'`, cycle `c', b, a', c, b'`). -/
theorem k22z1g_c4 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K17hTcZ1 a a' b b' c c' d)
    (hγ : ∀ α4 γ4 : ℝ, b' = d + α4 • (a - d) + γ4 • (c - d) → γ4 = 1)
    (hS2 : 0 < ⟪b - a, a - c'⟫) (hS3 : 0 < ⟪a' - b, a - c'⟫) : HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hZ, hz1, hd1, hpq⟩ := h
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα1, hα4, hβ1, hγ4, hb6, hαγ, hE⟩ := k17ga_tc_coords W hZ
  have hγ1 : γ4 = 1 := hγ α4 γ4 hb'
  subst hγ1
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
  have hzdb : ⟪d - b, a - b'⟫ = 0 := hZ.2.2.1
  have hqr : ⟪q, r⟫ = 0 := by
    have e1 : d - b = -q := by rw [hq]; abel
    have e2 : a - b' = (1 - α4) • p - (1:ℝ) • r := by rw [hb', hp, hr]; module
    rw [e1, e2] at hzdb
    simp only [inner_neg_left, inner_sub_right, inner_smul_right, hpq', hqp] at hzdb
    linarith
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
  obtain ⟨k, hk⟩ : ∃ k, β6 = 1 + k := ⟨β6 - 1, by ring⟩
  obtain ⟨u, hu⟩ : ∃ u, α1 = 1 + u := ⟨α1 - 1, by ring⟩
  have hu0 : 0 < u := by linarith
  have hα4' : α4 = 1 + k := by rw [hk] at hαγ; linarith
  have hk0 : 0 < k := by
    by_contra hh; push_neg at hh
    have : 1 * k ≤ 0 := by linarith
    linarith
  subst hk hu hα4'
  obtain ⟨w, hw0, hwu⟩ : ∃ w, 0 < w ∧ w * u = 1 := ⟨1 / u, by positivity, by field_simp⟩
  have eR : a - c' = (-u) • p - q := by rw [hc', hp, hq]; module
  have eS : a' - b = k • q + r := by rw [ha', hq, hr]; module
  rw [eR, eS] at hS3
  simp only [inner_sub_right, inner_add_left, inner_smul_left, inner_smul_right, conj_trivial, hpq', hqp, hqr,
    hrq, hrp] at hS3
  have hS3' : 0 < -(k * ⟪q, q⟫) - u * ⟪p, r⟫ := by nlinarith
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
  have hRR0 : 0 < u ^ 2 * ⟪p, p⟫ + ⟪q, q⟫ := by positivity
  have z0 : ⟪fpoint P Q R d (-w, 0, -w - 1), R⟫ = ⟪d, R⟫ - u * ⟪p, p⟫ - (u ^ 2 * ⟪p, p⟫ + ⟪q, q⟫) := by
    rw [hz]; simp only [hPR, hQR, hRR]; linear_combination (-(u * ⟪p, p⟫)) * hwu
  have z1 : ⟪fpoint P Q R d (1, 0, 0), R⟫ = ⟪d, R⟫ - ⟪q, q⟫ := by rw [hz]; simp only [hPR]; ring
  have z2 : ⟪fpoint P Q R d (1 + k, 1, 0), R⟫ = ⟪d, R⟫ - (1 + k) * ⟪q, q⟫ - u * ⟪p, r⟫ := by
    rw [hz]; simp only [hPR, hQR]; ring
  have z3 : ⟪fpoint P Q R d (0, 1, 0), R⟫ = ⟪d, R⟫ - u * ⟪p, r⟫ := by
    rw [hz]; simp only [hQR]; ring
  have z4 : ⟪fpoint P Q R d (-(1 + k) * w, 1, -(1 + k) * w), R⟫ =
      ⟪d, R⟫ - (1 + k) * (u * ⟪p, p⟫) - u * ⟪p, r⟫ := by
    rw [hz]; simp only [hPR, hQR, hRR]
    linear_combination (-((1 + k) * (u * ⟪p, p⟫))) * hwu
  have hR0 : R ≠ 0 := k17f_r0 hΔ
  refine ⟨R, hR0, ?_⟩
  refine k18_cone_cell (V8 a a' b b' c c' d) P Q R d hΔ (k := 5) (by norm_num) (k22z1gc4Y w k)
    (k22z1gc4Y_inj hw0 hk0) ?_ [(-1, 0), (0, -1)] (by simp) ?_ ?_ ?_
    (ρ1 := -1) (ρ2 := -1) (δ1 := 0) (δ2 := 0) ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · rw [k22z1gc4Y_0, Ec']; simp [V8]
    · rw [k22z1gc4Y_1, Eb]; simp [V8]
    · rw [k22z1gc4Y_2, Ea']; simp [V8]
    · rw [k22z1gc4Y_3, Ec]; simp [V8]
    · rw [k22z1gc4Y_4, Eb']; simp [V8]
  · intro v1 v2 hC D hD
    have h1 := hC (-1, 0) (by simp)
    have h2 := hC (0, -1) (by simp)
    simp only at h1 h2
    have := (k22z1gc4_tsc (s1 := -v1) (s2 := -v2) hD hw0 hk0 (by linarith) (by linarith)).1
    simpa using this
  · intro y hy hyx
    have hV : y = fpoint P Q R d (-w, 0, -w - 1) ∨ y = fpoint P Q R d (1, 0, 0) ∨
        y = fpoint P Q R d (1 + k, 1, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨
        y = fpoint P Q R d (-(1 + k) * w, 1, -(1 + k) * w) ∨
        y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (-w, 0, -w) := by
      rw [Ec', Eb, Ea', Ec, Eb', Ed, Ea]
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    have hT : ∀ v1 v2 : ℝ, k18Cone [(-1, 0), (0, -1)] v1 v2 → ∀ D : ℝ, 0 < D →
        ∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (-w, 0, -w)], ∀ i : ZMod 5,
          TSc D (k22z1gc4Y w k (i + 1) - k22z1gc4Y w k i) (t - k22z1gc4Y w k i) (v1, v2, 0) := by
      intro v1 v2 hC D hD
      have h1 := hC (-1, 0) (by simp)
      have h2 := hC (0, -1) (by simp)
      simp only at h1 h2
      have := (k22z1gc4_tsc (s1 := -v1) (s2 := -v2) hD hw0 hk0 (by linarith) (by linarith)).2
      simpa using this
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by rw [k22z1gc4Y_0])).elim
    · exact (hyx 1 (by rw [k22z1gc4Y_1])).elim
    · exact (hyx 2 (by rw [k22z1gc4Y_2])).elim
    · exact (hyx 3 (by rw [k22z1gc4Y_3])).elim
    · exact (hyx 4 (by rw [k22z1gc4Y_4])).elim
    · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT v1 v2 hC D hD _ (by simp) i⟩
    · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT v1 v2 hC D hD _ (by simp) i⟩
  · intro v1 v2 hC hw
    obtain ⟨e0, e1, e2, e3, e4, f0, f1, f2, f3, f4⟩ := k19_z5
    refine k19_lexUni_nb _ _ hw 3 ?_ ?_ ?_
    · rw [e3]; left; simp only [k22z1gc4Y_2, k22z1gc4Y_3, z2, z3]; nlinarith
    · rw [f3]; left; simp only [k22z1gc4Y_4, k22z1gc4Y_3, z4, z3]; nlinarith [mul_pos hu0 hpp, mul_pos hk0 (mul_pos hu0 hpp)]
    · intro i hi
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · right; rw [f0]; left; simp only [k22z1gc4Y_0, k22z1gc4Y_1, z0, z1]; nlinarith [mul_pos hu0 hpp]
      · right; rw [f1]; left; simp only [k22z1gc4Y_1, k22z1gc4Y_2, z1, z2]; linarith
      · right; rw [f2]; left; simp only [k22z1gc4Y_2, k22z1gc4Y_3, z2, z3]; nlinarith
      · exact absurd rfl hi
      · left; rw [e4]; left; simp only [k22z1gc4Y_4, k22z1gc4Y_3, z4, z3]; nlinarith [mul_pos hu0 hpp, mul_pos hk0 (mul_pos hu0 hpp)]
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> (left; norm_num)

end C2
end Type08Sp
end Minimality
