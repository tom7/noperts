module

public import Minimality.Type08S.C2K34GC

@[expose] public section

set_option maxHeartbeats 1000000

set_option maxHeartbeats 1000000
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2


set_option maxHeartbeats 3200000 in
/-- Metric facts of leaf C. -/
theorem k32g_hE {a a' b b' c c' d : ℝ³} {α1 β1 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 1 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hα1 : 1 < α1) (hβ1 : 1 < β1) (hσ : β1 < 1 + γ6)
    (hLp : ⟪c' - a', b' - c⟫ = 0)
    (hLz : ⟪c' - c, k28b4c_u0 a a' c c' d⟫ = 0) : 0 < ⟪c' - a', c - a'⟫ := by
  obtain ⟨hdet, hc', hb', ha', -, -, -, -, hγ6, -⟩ := hC
  obtain ⟨hm0, hm1, hm2⟩ := hM
  obtain ⟨hr1, hr2⟩ := hrel
  set P := a - d with hP
  set Q := b - d with hQ
  set R := c - d with hR
  have e1 : c' - a' = α1 • P + (β1 - 1) • Q - γ6 • R := by rw [hc', ha']; module
  have hcR : c = d + R := by rw [hR]; abel
  have e2 : b' - c = α1 • P + (β1 - 1) • R := by rw [hb', hcR]; module
  have e3 : a' - b' = (-α1) • P + Q + (γ6 - β1) • R := by
    rw [ha', hb']; module
  have e4 : b - c = Q - R := by rw [hQ, hR]; module
  have e5 : c' - d = α1 • P + β1 • Q := by rw [hc']; module
  have e6 : b' - d = α1 • P + β1 • R := by rw [hb']; module
  have e7 : b' - a = (α1 - 1) • P + β1 • R := by rw [hb', hP]; module
  rw [e1, e2] at hLp
  rw [e4] at hm0
  rw [e4, e5] at hm1
  rw [e6, e4] at hm2
  have hRP : ⟪R, P⟫ = ⟪P, R⟫ := real_inner_comm _ _
  have hRQ : ⟪R, Q⟫ = ⟪Q, R⟫ := real_inner_comm _ _
  have hPQ : ⟪Q, P⟫ = ⟪P, Q⟫ := real_inner_comm _ _
  have hcs := k24mta_cs hdet
  have hr1' : α1 * ⟪P, Q⟫ * (⟪Q, Q⟫ + ⟪R, R⟫ - 2 * ⟪Q, R⟫) =
      -(β1 - 1) * (⟪Q, Q⟫ * ⟪R, R⟫ - ⟪Q, R⟫ ^ 2) := hr1
  have hPP : 0 < ⟪P, P⟫ := real_inner_self_pos.2 (by
    intro h0; apply hdet; rw [← hP] at *; rw [h0]; simp [det3_expand])
  simp only [inner_smul_right, inner_sub_right, inner_add_right, inner_smul_left,
    inner_sub_left, inner_add_left, conj_trivial, hRP, hRQ, hPQ] at hm0 hm1 hm2 hr1 hLp
  have hPR : ⟪P, R⟫ = ⟪P, Q⟫ := by linarith
  rw [hPR] at hm1 hm2 hLp
  have hqq : ⟪Q, R⟫ < ⟪Q, Q⟫ := by nlinarith
  have hrr : ⟪Q, R⟫ < ⟪R, R⟫ := by nlinarith
  have hD : 0 < ⟪Q, Q⟫ * ⟪R, R⟫ - ⟪Q, R⟫ ^ 2 := by linarith
  have hW : 0 < ⟪Q, Q⟫ + ⟪R, R⟫ - 2 * ⟪Q, R⟫ := by linarith
  have hs : ⟪P, Q⟫ < 0 := by
    by_contra hn; push Not at hn
    have := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ α1) hn) hW.le
    nlinarith [mul_pos (sub_pos.2 hβ1) hD]
  have em1 : ⟪c' - a', P⟫ = α1 * ⟪P, P⟫ + (β1 - 1 - γ6) * ⟪P, Q⟫ := by
    rw [e1]
    simp only [inner_smul_left, inner_sub_left, inner_add_left, conj_trivial, hPR, hRP, hPQ] <;> ring
  have em3 : ⟪c' - a', R⟫ = α1 * ⟪P, Q⟫ + (β1 - 1) * ⟪Q, R⟫ - γ6 * ⟪R, R⟫ := by
    rw [e1]
    simp only [inner_smul_left, inner_sub_left, inner_add_left, conj_trivial, hPR, hRP, hPQ, hRQ] 
  have hm1p : 0 < α1 * ⟪P, P⟫ + (β1 - 1 - γ6) * ⟪P, Q⟫ := by
    nlinarith [mul_pos (by linarith : (0:ℝ) < α1) hPP, mul_nonneg (by linarith : (0:ℝ) ≤ γ6 + 1 - β1) (by linarith : (0:ℝ) ≤ -⟪P, Q⟫)]
  have hm3n : α1 * ⟪P, Q⟫ + (β1 - 1) * ⟪Q, R⟫ - γ6 * ⟪R, R⟫ < 0 := by
    rcases le_or_gt 0 ⟪Q, R⟫ with h | h
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ γ6 - (β1 - 1)) h, mul_pos hγ6 (sub_pos.2 hrr),
        mul_pos (by linarith : (0:ℝ) < α1) (neg_pos.2 hs)]
    · nlinarith [mul_pos (sub_pos.2 hβ1) (neg_pos.2 h), mul_pos hγ6 (by nlinarith : 0 < ⟪R, R⟫),
        mul_pos (by linarith : (0:ℝ) < α1) (neg_pos.2 hs)]
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = α1 * ⟪P, P⟫ + (β1 - 1 - γ6) * ⟪P, Q⟫ := ⟨_, rfl⟩
  obtain ⟨m3, hm3⟩ : ∃ m3, m3 = α1 * ⟪P, Q⟫ + (β1 - 1) * ⟪Q, R⟫ - γ6 * ⟪R, R⟫ := ⟨_, rfl⟩
  rw [← hm1] at hm1p
  rw [← hm3] at hm3n
  have hs0 : ⟪P, Q⟫ < 0 := hs
  have hLp' : α1 * m1 + (β1 - 1) * m3 = 0 := by rw [hm1, hm3]; linarith
  have hsq : ⟪P, R⟫ ^ 2 < ⟪P, P⟫ * ⟪R, R⟫ := by
    have hd2 : det3 Q P R ≠ 0 := by
      intro h; apply hdet; rw [hP, hQ, hR] at *
      simp only [det3_expand, PiLp.sub_apply] at h ⊢; linarith
    have := k24mta_cs hd2
    exact this
  have hsa : ⟪P, Q⟫ ^ 2 < ⟪P, P⟫ * ⟪R, R⟫ := by rw [← hPR]; exact hsq
  have hW' : α1 * (-⟪P, Q⟫) < (β1 - 1) * ⟪R, R⟫ := by
    by_contra hn; push Not at hn
    have e : ⟪R, R⟫ * (⟪Q, Q⟫ + ⟪R, R⟫ - 2 * ⟪Q, R⟫) - (⟪Q, Q⟫ * ⟪R, R⟫ - ⟪Q, R⟫ ^ 2) = (⟪R, R⟫ - ⟪Q, R⟫) ^ 2 := by ring
    nlinarith [mul_nonneg (sub_nonneg.2 hn) hW.le, mul_pos (sub_pos.2 hβ1) (pow_pos (sub_pos.2 hrr) 2), mul_pos (sub_pos.2 hβ1) hW, sq_nonneg (⟪R, R⟫ - ⟪Q, R⟫), mul_nonneg (sub_pos.2 hβ1).le (sq_nonneg (⟪R, R⟫ - ⟪Q, R⟫))]
  have g1 : m3 * ⟪P, Q⟫ - m1 * ⟪R, R⟫ < 0 := by
    have h1 : (β1 - 1) * (m3 * ⟪P, Q⟫ - m1 * ⟪R, R⟫) < 0 := by
      nlinarith [mul_pos hm1p (sub_pos.2 hW'), hLp']
    by_contra h; push Not at h
    nlinarith [mul_nonneg (sub_pos.2 hβ1).le h]
  have g2 : m3 * ⟪P, P⟫ - m1 * ⟪P, Q⟫ < 0 := by
    rw [hm1, hm3]
    rcases le_or_gt 0 (⟪P, P⟫ * ⟪Q, R⟫ - ⟪P, Q⟫ ^ 2) with hX | hX
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ γ6 - (β1 - 1)) hX, mul_pos hγ6 (mul_pos hPP (sub_pos.2 hrr))]
    · nlinarith [mul_pos (sub_pos.2 hβ1) (neg_pos.2 hX), mul_pos hγ6 (sub_pos.2 hsa)]
  have hLq' : (α1 - 1) * m1 + β1 * m3 < 0 := by rw [hm1, hm3]; nlinarith
  have e8 : c' - c = α1 • P + β1 • Q - R := by rw [hc', hcR]; module
  have e9 : c - a' = (1 - γ6) • R - Q := by rw [ha', hcR]; module
  have hu0 : k28b4c_u0 a a' c c' d = m3 • P - m1 • R := by
    unfold k28b4c_u0; rw [← hP, ← hR, e1]
    simp only [inner_smul_left, inner_sub_left, inner_add_left, conj_trivial, hPR, hRP, hPQ, hRQ]
    rw [hm1, hm3]; module
  rw [hu0, e8] at hLz
  rw [e1, e9]
  simp only [inner_smul_right, inner_sub_right, inner_add_right, inner_smul_left, inner_sub_left, inner_add_left, conj_trivial, hRP, hRQ, hPQ, hPR] at hLz ⊢
  have h := k32g_hE_real hα1 hβ1 hγ6 hm1 hm3 hm3n hLp' (by linear_combination hLz) hr1' hqq hrr hD
  rw [hm3] at h
  linarith [h]

end C2
end Type08Sp
end Minimality
