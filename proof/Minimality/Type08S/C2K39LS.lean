module

public import Minimality.Type08S.LexCertA
public import Minimality.Type08S.C2K28B4t0
public import Minimality.Type08S.C2K28B4c3
public import Minimality.Type08S.P2RR1

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2

set_option maxHeartbeats 3200000 in
theorem k34lw_Sq {a a' b b' c c' d : ℝ³} {α1 β1 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 1 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hα : 1 < α1) (hβ : 1 < β1) (hσ : β1 < 1 + γ6)
    (hLz : ⟪c' - c, k28b4c_u0 a a' c c' d⟫ = 0) (hLw : ⟪a - c', k28b4c_u0 a a' c c' d⟫ = 0)
    (hLp : 0 < ⟪c' - a', b' - c⟫)
    (hS : 0 ≤ ⟪a - d, a - c'⟫) : ⟪c' - a', b' - a⟫ < 0 := by
  have hC0 := hC
  obtain ⟨hdet, hc', hb', ha', -, -, -, -, hγ6, -⟩ := hC
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = ⟪c' - a', a - d⟫ := ⟨_, rfl⟩
  obtain ⟨m3, hm3⟩ : ∃ m3, m3 = ⟪c' - a', c - d⟫ := ⟨_, rfl⟩
  have hu0 : k28b4c_u0 a a' c c' d = m3 • (a - d) - m1 • (c - d) := by
    unfold k28b4c_u0; rw [hm1, hm3]
  rw [hu0] at hLz hLw
  have hLp2 : 0 < α1 * m1 + (β1 - 1) * m3 := by
    have e : b' - c = α1 • (a - d) + (β1 - 1) • (c - d) := by rw [hb']; module
    rw [e, inner_add_right, inner_smul_right, inner_smul_right, ← hm1, ← hm3] at hLp
    exact hLp
  have hu : m3 • (a - d) - m1 • (c - d) ≠ 0 := by
    intro h
    have e1 : det3 (m3 • (a - d) - m1 • (c - d)) (b - d) (c - d) = m3 * det3 (a - d) (b - d) (c - d) := by
      simp only [det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    have e2 : det3 (m3 • (a - d) - m1 • (c - d)) (b - d) (a - d) = m1 * det3 (a - d) (b - d) (c - d) := by
      simp only [det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    have z : ∀ x y : ℝ³, det3 0 x y = 0 := fun x y => by simp [det3_expand]
    have h3 : m3 = 0 := by
      have : m3 * det3 (a - d) (b - d) (c - d) = 0 := by rw [← e1, h]; exact z _ _
      exact (mul_eq_zero.1 this).resolve_right hdet
    have h1 : m1 = 0 := by
      have : m1 * det3 (a - d) (b - d) (c - d) = 0 := by rw [← e2, h]; exact z _ _
      exact (mul_eq_zero.1 this).resolve_right hdet
    rw [h1, h3] at hLp2; simp at hLp2
  have hcop : det3 (a - c') (c' - c) (c' - a') = 0 := by
    refine det3_orth hLw hLz ?_ hu
    rw [inner_sub_right, inner_smul_right, inner_smul_right, ← hm1, ← hm3]; ring
  have hC5 : α1 - 1 + β1 - β1 * γ6 = 0 := by
    have e : det3 (a - c') (c' - c) (c' - a') = (α1 - 1 + β1 - β1 * γ6) * det3 (a - d) (b - d) (c - d) := by
      rw [hc', ha']
      simp only [det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e] at hcop
    exact (mul_eq_zero.1 hcop).resolve_right hdet
  obtain ⟨ν, hν⟩ : ∃ ν, ν = (α1 - 1) / β1 := ⟨_, rfl⟩
  have hβ0 : 0 < β1 := by linarith
  have hνβ : β1 * ν = α1 - 1 := by rw [hν]; field_simp
  obtain ⟨R, hR⟩ : ∃ R : ℝ³, R = -(ν • (a - d)) - (b - d) := ⟨_, rfl⟩
  have hac : a - c' = β1 • R := by
    rw [hc', hR]; ext i
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
    linear_combination (a i - d i) * hνβ
  have hΔ : det3 (c - d) (a - d) R ≠ 0 := by
    have e : det3 (c - d) (a - d) R = det3 (a - d) (b - d) (c - d) * (-1) := by
      rw [hR]; simp only [det3_expand, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]; ring
    rw [e]; exact mul_ne_zero hdet (by norm_num)
  have hR0 : R ≠ 0 := k17f_r0 hΔ
  have Ea : fpoint (c - d) (a - d) R d (0, 1, 0) = a := by rw [k17f_fp]; module
  have Eb : fpoint (c - d) (a - d) R d (0, -ν, -1) = b := by rw [k17f_fp, hR]; module
  have Ec : fpoint (c - d) (a - d) R d (1, 0, 0) = c := by rw [k17f_fp]; module
  have Ed : fpoint (c - d) (a - d) R d (0, 0, 0) = d := by rw [k17f_fp]; module
  have Ec' : fpoint (c - d) (a - d) R d (0, 1, -β1) = c' := by rw [k17f_fp, neg_smul, ← hac]; module
  have Eb' : fpoint (c - d) (a - d) R d (β1, α1, 0) = b' := by rw [k17f_fp, hb']; module
  have Ea' : fpoint (c - d) (a - d) R d (γ6, -ν, -1) = a' := by rw [k17f_fp, ha', hR]; module
  have hLz' : m3 * ⟪c' - c, a - d⟫ - m1 * ⟪c' - c, c - d⟫ = 0 := by
    rw [inner_sub_right, inner_smul_right, inner_smul_right] at hLz; exact hLz
  have hLw' : m3 * ⟪a - c', a - d⟫ - m1 * ⟪a - c', c - d⟫ = 0 := by
    rw [inner_sub_right, inner_smul_right, inner_smul_right] at hLw; exact hLw
  have hν2 : ν = γ6 - 1 := by
    have : β1 * (ν - (γ6 - 1)) = 0 := by linear_combination hνβ + hC5
    have := (mul_eq_zero.1 this).resolve_left hβ0.ne'
    linarith
  have hν0 : 0 < ν := by rw [hν]; exact div_pos (by linarith) hβ0
  have hE : m3 * ⟪a - d, R⟫ = m1 * ⟪c - d, R⟫ := by
    have h := hLw'
    rw [hac, inner_smul_left, inner_smul_left, real_inner_comm (a - d) R, real_inner_comm (c - d) R] at h
    simp only [conj_trivial] at h
    have : β1 * (m3 * ⟪a - d, R⟫ - m1 * ⟪c - d, R⟫) = 0 := by linear_combination h
    have := (mul_eq_zero.1 this).resolve_left hβ0.ne'
    linarith
  have hQRv : ⟪a - d, a - c'⟫ = β1 * ⟪a - d, R⟫ := by rw [hac, inner_smul_right]
  have h2 : ⟪a - d, b - d⟫ = ⟪a - d, c - d⟫ := by
    have := hM.1
    rw [show b - c = (b - d) - (c - d) by abel, inner_sub_right] at this; linarith
  have hPQ : ⟪a - d, c - d⟫ < 0 := by
    have h1 := hrel.1
    have hbc : 0 < ⟪b - c, b - c⟫ := real_inner_self_pos.2 (by
      intro h0
      have : b - d = c - d := by rw [sub_eq_zero.1 h0]
      have : det3 (a - d) (b - d) (c - d) = 0 := by rw [this]; simp [det3_expand]; ring
      exact hdet this)
    have h3 : ⟪b - c, b - c⟫ = ⟪b - d, b - d⟫ + ⟪c - d, c - d⟫ - 2 * ⟪b - d, c - d⟫ := by
      have hc := real_inner_comm (b - d) (c - d)
      rw [show b - c = (b - d) - (c - d) by abel]
      simp only [inner_sub_left, inner_sub_right] at hc ⊢; linarith
    by_contra hn; push_neg at hn
    rw [h2, ← h3] at h1
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ α1) hn) hbc.le, mul_pos (by linarith : (0:ℝ) < β1 - 1) hrel.2]
  have hX : 0 ≤ ⟪a - d, R⟫ := by
    have h : 0 ≤ β1 * ⟪a - d, R⟫ := by rw [← hQRv]; exact hS
    exact (mul_nonneg_iff_of_pos_left hβ0).1 h
  have hw : b - d = -(ν • (a - d)) - R := by rw [hR]; module
  have hpq : ⟪a - d, c - d⟫ = -ν * ⟪a - d, a - d⟫ - ⟪a - d, R⟫ := by
    rw [← h2, hw, inner_sub_right, inner_neg_right, inner_smul_right]; ring
  have hcm : c' - a' = γ6 • (a - d) - γ6 • (c - d) - (β1 - 1) • R := by
    rw [hc', ha', hR]; ext i
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
    linear_combination (a i - d i) * (hν2 - hνβ)
  have c1 := real_inner_comm (a - d) (c - d)
  have c2 := real_inner_comm (a - d) R
  have c3 := real_inner_comm (c - d) R
  have e1 : m1 = γ6 * (⟪a - d, a - d⟫ - ⟪a - d, c - d⟫) - (β1 - 1) * ⟪a - d, R⟫ := by
    rw [hm1, hcm, inner_sub_left, inner_sub_left, inner_smul_left, inner_smul_left, inner_smul_left]
    simp only [conj_trivial]; rw [c1, c2]; ring
  have e3 : m3 = γ6 * (⟪a - d, c - d⟫ - ⟪c - d, c - d⟫) - (β1 - 1) * ⟪c - d, R⟫ := by
    rw [hm3, hcm, inner_sub_left, inner_sub_left, inner_smul_left, inner_smul_left, inner_smul_left]
    simp only [conj_trivial]; rw [c3]; ring
  have hqq : 0 < ⟪a - d, a - d⟫ := (real_inner_self_pos (x := a - d)).2 (by
    intro h0; apply hdet; simp [det3_expand, h0])
  have hpp : 0 < ⟪c - d, c - d⟫ := (real_inner_self_pos (x := c - d)).2 (by
    intro h0; apply hdet; simp [det3_expand, h0])
  have hPD := (cert_gram_pd hΔ).2.2.2.1
  have hν0 : 0 < ν := by rw [hν]; exact div_pos (by linarith) hβ0
  have hν1 : ν = γ6 - 1 := hν2
  have hWd : 0 < ⟪a - d, a - d⟫ - ⟪a - d, c - d⟫ := by rw [hpq]; nlinarith
  have hN0 : 0 < ⟪c - d, c - d⟫ - ⟪a - d, c - d⟫ := by rw [hpq]; nlinarith
  have k1 : 0 < m1 := by
    rw [e1]; rw [hpq]
    nlinarith [mul_pos hγ6 hqq, mul_pos (mul_pos hγ6 hγ6) hqq, mul_nonneg (by linarith : (0:ℝ) ≤ γ6 - (β1 - 1)) hX, mul_pos hγ6 hν0]
  have key : γ6 * (⟪a - d, a - d⟫ - ⟪a - d, c - d⟫) * m3 = γ6 * m1 * (⟪a - d, c - d⟫ - ⟪c - d, c - d⟫) := by
    linear_combination (β1 - 1) * hE - m3 * e1 + m1 * e3
  have hlt : ν * (⟪a - d, a - d⟫ - ⟪a - d, c - d⟫) < ⟪c - d, c - d⟫ - ⟪a - d, c - d⟫ := by
    have h1 : 0 < ⟪a - d, a - d⟫ * (⟪c - d, c - d⟫ - (ν ^ 2 * ⟪a - d, a - d⟫ + (ν - 1) * ⟪a - d, R⟫)) := by
      rw [real_inner_comm (a - d) (c - d), hpq] at hPD
      nlinarith [mul_nonneg hX hX, mul_nonneg hX hqq.le, mul_nonneg hν0.le hX, mul_pos hν0 hqq]
    have h2' := (mul_pos_iff_of_pos_left hqq).1 h1
    rw [hpq]; nlinarith
  have hnum : ν * m1 + m3 < 0 := by
    have hg : 0 < γ6 * (⟪a - d, a - d⟫ - ⟪a - d, c - d⟫) := mul_pos hγ6 hWd
    have : γ6 * (⟪a - d, a - d⟫ - ⟪a - d, c - d⟫) * (ν * m1 + m3) < 0 := by
      have e : γ6 * (⟪a - d, a - d⟫ - ⟪a - d, c - d⟫) * (ν * m1 + m3) = γ6 * m1 * (ν * (⟪a - d, a - d⟫ - ⟪a - d, c - d⟫) - (⟪c - d, c - d⟫ - ⟪a - d, c - d⟫)) := by
        linear_combination ν * 0 + key
      rw [e]; exact mul_neg_of_pos_of_neg (mul_pos hγ6 k1) (by linarith)
    by_contra hn; push_neg at hn
    nlinarith [mul_nonneg hg.le hn]
  have e5 : b' - a = (α1 - 1) • (a - d) + β1 • (c - d) := by rw [hb']; module
  rw [e5, inner_add_right, inner_smul_right, inner_smul_right, ← hm1, ← hm3]
  have : α1 - 1 = β1 * ν := hνβ.symm
  rw [this]; nlinarith [mul_pos hβ0 hβ0]


end C2
end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.C2.k34lw_Sq
