module

public import Minimality.Type08S.C2K22C3A

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

/-- Strict Cauchy-Schwarz for `Q, R` from `det3 P Q R ≠ 0`. -/
theorem k22c3_cs {P Q R : ℝ³} (hΔ : det3 P Q R ≠ 0) : ⟪Q, R⟫ ^ 2 < ⟪Q, Q⟫ * ⟪R, R⟫ := by
  have hR0 : R ≠ 0 := k17f_r0 hΔ
  have hRR : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hR0
  set u : ℝ³ := ⟪R, R⟫ • Q - ⟪Q, R⟫ • R with hu
  have hu0 : u ≠ 0 := by
    intro h0
    apply hΔ
    have hQ : Q = (⟪Q, R⟫ / ⟪R, R⟫) • R := by
      have : ⟪R, R⟫ • Q = ⟪Q, R⟫ • R := sub_eq_zero.1 h0
      rw [div_eq_inv_mul, mul_smul, ← this, smul_smul, inv_mul_cancel₀ hRR.ne', one_smul]
    rw [hQ]; simp [det3_expand]; ring
  have huu : 0 < ⟪u, u⟫ := real_inner_self_pos.2 hu0
  have e : ⟪u, u⟫ = ⟪R, R⟫ * (⟪Q, Q⟫ * ⟪R, R⟫ - ⟪Q, R⟫ ^ 2) := by
    simp only [hu, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_comm R Q]; ring
  rw [e] at huu
  nlinarith [(mul_pos_iff_of_pos_left hRR).1 huu]

set_option maxHeartbeats 12800000 in
/-- Pc corner C3, one cell at `c - d` (pentagon `(a',c,d,a,c')`). -/
theorem k22c3_cell {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K6t3LeftPc a a' b b' c c' d)
    (hC3 : ⟪a - d, a - c'⟫ < 0 ∧ ⟪c - b', d - b⟫ = 0 ∧ ⟪c - b', c - d⟫ = 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hPc, hca, -⟩ := h
  obtain ⟨β1, γ4, γ6, hdet, hc', hb', ha', hβ1, hγ4p, hγ6, hγ61, hβγ⟩ := k17gc_pc_frame W hPc
  obtain ⟨hlit, hb2, hc2⟩ := hC3
  set P := a - d with hP
  set Q := b - d with hQ
  set R := c - d with hR
  have hΔ : det3 P Q R ≠ 0 := hdet
  have Ea : fpoint P Q R d (1, 0, 0) = a := by rw [k17f_fp, hP]; module
  have Ed : fpoint P Q R d (0, 0, 0) = d := by rw [k17f_fp]; module
  have Eb : fpoint P Q R d (0, 1, 0) = b := by rw [k17f_fp, hQ]; module
  have Ec : fpoint P Q R d (0, 0, 1) = c := by rw [k17f_fp, hR]; module
  have Ea' : fpoint P Q R d (0, 1, γ6) = a' := by rw [k17f_fp, ha']; module
  have Eb' : fpoint P Q R d (1, 0, γ4) = b' := by rw [k17f_fp, hb']; module
  have Ec' : fpoint P Q R d (1, β1, 0) = c' := by rw [k17f_fp, hc']; module
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hR0 : R ≠ 0 := k17f_r0 hΔ
  have hRR : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hR0
  have hcs := k22c3_cs hΔ
  -- Gram facts
  have eac : a - c' = (-β1) • Q := by rw [hc', hQ]; module
  have eca : c - a' = (1 - γ6) • R - Q := by rw [ha', hQ, hR]; module
  have ecb : c - b' = (1 - γ4) • R - P := by rw [hb', hP, hR]; module
  have edb : d - b = -Q := by rw [hQ]; module
  have ecd : c - d = R := hR.symm
  have ead : a - d = P := hP.symm
  rw [eac] at hlit
  rw [eca] at hca
  rw [ecb, edb] at hb2
  rw [ecb] at hc2
  have hRP : ⟪R, P⟫ = ⟪P, R⟫ := real_inner_comm _ _
  have hRQ : ⟪R, Q⟫ = ⟪Q, R⟫ := real_inner_comm _ _
  have hPQ : ⟪Q, P⟫ = ⟪P, Q⟫ := real_inner_comm _ _
  simp only [inner_smul_right, inner_sub_right, inner_add_right, inner_neg_right, inner_smul_left,
    inner_sub_left, inner_add_left, inner_neg_left, conj_trivial, hRP, hRQ, hPQ] at hlit hca hb2 hc2
  have hpq : 0 < ⟪P, Q⟫ := by nlinarith
  -- hca : (1-γ6) PR - PQ = 0 ; hb2: PQ = (1-γ4) QR ; hc2 : PR = (1-γ4) RR
  have hpq' : ⟪P, Q⟫ = (1 - γ6) * ((1 - γ4) * ⟪R, R⟫) := by
    have : ⟪P, R⟫ = (1 - γ4) * ⟪R, R⟫ := by linarith
    rw [← this]; linarith
  have hg6 : 0 < 1 - γ6 := by linarith
  have hg4 : γ4 < 1 := by
    by_contra hn; push_neg at hn
    have : (1 - γ4) * ⟪R, R⟫ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hRR.le
    nlinarith [mul_nonneg hg6.le (neg_nonneg.2 this)]
  have hg4p : 0 < 1 - γ4 := by linarith
  have hQR : ⟪Q, R⟫ = (1 - γ6) * ⟪R, R⟫ := by
    have h1 : (1 - γ4) * (⟪Q, R⟫ - (1 - γ6) * ⟪R, R⟫) = 0 := by nlinarith
    rcases mul_eq_zero.1 h1 with h | h
    · linarith
    · linarith
  have hPR : ⟪P, R⟫ = (1 - γ4) * ⟪R, R⟫ := by linarith
  have hQQ : (1 - γ6) ^ 2 * ⟪R, R⟫ < ⟪Q, Q⟫ := by
    rw [hQR] at hcs
    nlinarith
  refine ⟨R, hR0, ?_⟩
  refine k18_cone_cell (V8 a a' b b' c c' d) P Q R d hΔ (k := 5) (by norm_num) (k22c3Y β1 γ6)
    (k22c3Y_inj hβ1 hγ6 hγ61) ?_ [(1, 0), (-1, -1)] (by simp) ?_ ?_ ?_
    (ρ1 := 1) (ρ2 := -2) (δ1 := 0) (δ2 := 0) ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · rw [k22c3Y_0, Ea']; simp [V8]
    · rw [k22c3Y_1, Ec]; simp [V8]
    · rw [k22c3Y_2, Ed]; simp [V8]
    · rw [k22c3Y_3, Ea]; simp [V8]
    · rw [k22c3Y_4, Ec']; simp [V8]
  · intro v1 v2 hC D hD
    have h1 := hC (1, 0) (by simp)
    have h2 := hC (-1, -1) (by simp)
    simp only at h1 h2
    exact (k22c3_tsc hD hβ1 hγ4p hγ6 hγ61 (by linarith) (by linarith)).1
  · intro y hy hyx
    have hV : y = fpoint P Q R d (0, 1, γ6) ∨ y = fpoint P Q R d (0, 0, 1) ∨ y = fpoint P Q R d (0, 0, 0) ∨
        y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (1, β1, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨
        y = fpoint P Q R d (1, 0, γ4) := by
      rw [Ea', Ec, Ed, Ea, Ec', Eb, Eb']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    have hT : ∀ v1 v2 : ℝ, k18Cone [(1, 0), (-1, -1)] v1 v2 → ∀ D : ℝ, 0 < D →
        ∀ t ∈ [((0 : ℝ), (1 : ℝ), (0 : ℝ)), (1, 0, γ4)], ∀ i : ZMod 5,
          TSc D (k22c3Y β1 γ6 (i + 1) - k22c3Y β1 γ6 i) (t - k22c3Y β1 γ6 i) (v1, v2, 0) := by
      intro v1 v2 hC D hD
      have h1 := hC (1, 0) (by simp)
      have h2 := hC (-1, -1) (by simp)
      simp only at h1 h2
      exact (k22c3_tsc hD hβ1 hγ4p hγ6 hγ61 (by linarith) (by linarith)).2
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by rw [k22c3Y_0])).elim
    · exact (hyx 1 (by rw [k22c3Y_1])).elim
    · exact (hyx 2 (by rw [k22c3Y_2])).elim
    · exact (hyx 3 (by rw [k22c3Y_3])).elim
    · exact (hyx 4 (by rw [k22c3Y_4])).elim
    · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT v1 v2 hC D hD _ (by simp) i⟩
    · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT v1 v2 hC D hD _ (by simp) i⟩
  · intro v1 v2 hC hw
    obtain ⟨e0, e1, e2, e3, e4, f0, f1, f2, f3, f4⟩ := k19_z5
    have h1 := hC (1, 0) (by simp)
    have h2 := hC (-1, -1) (by simp)
    simp only at h1 h2
    have hv2 : v2 < 0 := by linarith
    -- tilt depth tie
    have htie : ⟪fpoint P Q R d (k22c3Y β1 γ6 0), fcomb P Q R v1 v2 0⟫ <
        ⟪fpoint P Q R d (k22c3Y β1 γ6 1), fcomb P Q R v1 v2 0⟫ := by
      rw [k22c3Y_0, k22c3Y_1, k17f_fp, k17f_fp]
      have : ⟪d + (0:ℝ) • P + (1:ℝ) • Q + γ6 • R, fcomb P Q R v1 v2 0⟫ -
          ⟪d + (0:ℝ) • P + (0:ℝ) • Q + (1:ℝ) • R, fcomb P Q R v1 v2 0⟫ =
          v1 * (⟪P, Q⟫ - (1 - γ6) * ⟪P, R⟫) + v2 * (⟪Q, Q⟫ - (1 - γ6) * ⟪Q, R⟫) := by
        simp only [fcomb, zero_smul, add_zero, zero_add, one_smul, inner_add_left, inner_add_right,
          real_inner_smul_left, real_inner_smul_right, real_inner_comm P Q, real_inner_comm R Q,
          real_inner_comm R P]
        ring
      have h3 : v1 * (⟪P, Q⟫ - (1 - γ6) * ⟪P, R⟫) + v2 * (⟪Q, Q⟫ - (1 - γ6) * ⟪Q, R⟫) < 0 := by
        have : ⟪P, Q⟫ - (1 - γ6) * ⟪P, R⟫ = 0 := by linarith
        rw [this, hQR]; nlinarith
      linarith
    have kk := mul_pos hβ1 hRR
    have kk2 := mul_pos hg6 hRR
    have kk3 := mul_pos hβ1 kk2
    refine k19_lexUni_nb _ _ hw 1 ?_ ?_ ?_
    · rw [e1]; right; refine ⟨?_, htie⟩; simp only [k22c3Y_0, k22c3Y_1, hz]; rw [hQR]; ring_nf
    · rw [f1]; left; simp only [k22c3Y_1, k22c3Y_2, hz]; nlinarith
    · intro i hi
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · right; rw [f0]; right; refine ⟨?_, htie⟩; simp only [k22c3Y_0, k22c3Y_1, hz]; rw [hQR]; ring_nf
      · exact absurd rfl hi
      · left; rw [e2]; left; simp only [k22c3Y_1, k22c3Y_2, hz]; nlinarith
      · right; rw [f3]; left; simp only [k22c3Y_3, k22c3Y_4, hz]; nlinarith
      · right; rw [f4]; left; simp only [k22c3Y_4, k22c3Y_0, hz]; nlinarith
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> (left; norm_num)

end C2
end Type08Sp
end Minimality
