module

public import Minimality.Type08S.L2.K61A

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace
namespace Minimality.Type08Sp.C2

set_option maxHeartbeats 12800000 in
/-- Side facts of the type 08 `U0 = 0` branch (`W = (b-d) + lam (a-d)`, `lam Av = -Bv`). -/
theorem k86_facts {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 lam : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hα : 1 < α1) (hβ : 1 < β1) (hb6 : 1 < β6) (hg6 : 1 < γ6)
    (hσ : β1 < β6 + γ6) (hU0 : k28l2aU0 a b c d α1 β1 = 0)
    (hlamdef : lam * ⟪a - d, a' - b'⟫ = -⟪b - d, a' - b'⟫) :
    ⟪a - d, a' - b'⟫ < 0 ∧ 0 < lam ∧ α1 < β1 * lam + 1 ∧ ⟪a - d, c - d⟫ < 0 ∧
    ⟪a - d, a - d⟫ * (α1 - 1) = β1 * (-⟪a - d, c - d⟫) ∧
    ⟪b - d, c - d⟫ * β1 = (α1 - 1) * (-⟪a - d, c - d⟫) ∧
    0 < ⟪a - d, (b - d) + lam • (a - d)⟫ ∧ 0 < ⟪b - d, (b - d) + lam • (a - d)⟫ ∧
    ⟪b' - a, (b - d) + lam • (a - d)⟫ = 0 ∧ 0 < ⟪c' - b', (b - d) + lam • (a - d)⟫ ∧
    0 < ⟪a - a', a - d⟫ ∧ ⟪c' - a, a - d⟫ = 0 := by
  obtain ⟨hPR, hpp, hqq, hrr⟩ := k32e_facts hC hM
  have hC2 := hC
  obtain ⟨hdet, hc', hb', ha', -⟩ := hC
  have ip := k32e_ip (a - d) (b - d) (c - d) hPR
  obtain ⟨hr1, hr2⟩ := hrel
  have hpqn : ⟪a - d, b - d⟫ < 0 := k61_pq_neg hβ hα hqq hrr hr1 hr2
  have z : ∀ y1 y2 y3 : ℝ, k32e_G ⟪a - d, a - d⟫ ⟪a - d, b - d⟫ ⟪b - d, b - d⟫ ⟪b - d, c - d⟫ ⟪c - d, c - d⟫
      ((1 - α1) * ⟪a - d, b - d⟫ - β1 * ⟪b - d, c - d⟫) 0
      (-((1 - α1) * ⟪a - d, a - d⟫ - β1 * ⟪a - d, b - d⟫)) y1 y2 y3 = 0 := by
    intro y1 y2 y3
    have h0 : ⟪k28l2aU0 a b c d α1 β1, y1 • (a - d) + y2 • (b - d) + y3 • (c - d)⟫ = 0 := by
      rw [hU0]; simp
    rw [k32e_U, ip] at h0; exact h0
  have z1 := z 1 0 0
  have z2 := z 0 1 0
  have z3 := z 0 0 1
  simp only [k32e_G] at z1 z2 z3
  have hAv0 : ⟪a - d, a' - b'⟫ = -α1 * ⟪a - d, a - d⟫ + (β6 + γ6 - β1) * ⟪a - d, b - d⟫ := by
    have e : a' - b' = (-α1) • (a - d) + β6 • (b - d) + (γ6 - β1) • (c - d) := by
      rw [ha', hb']; module
    have e1 : a - d = (1:ℝ) • (a - d) + (0:ℝ) • (b - d) + (0:ℝ) • (c - d) := by module
    rw [e]; nth_rewrite 1 [e1]; rw [ip]; simp only [k32e_G]; ring
  have hBv0 : ⟪b - d, a' - b'⟫ = -α1 * ⟪a - d, b - d⟫ + β6 * ⟪b - d, b - d⟫ + (γ6 - β1) * ⟪b - d, c - d⟫ := by
    have e : a' - b' = (-α1) • (a - d) + β6 • (b - d) + (γ6 - β1) • (c - d) := by
      rw [ha', hb']; module
    have e1 : b - d = (0:ℝ) • (a - d) + (1:ℝ) • (b - d) + (0:ℝ) • (c - d) := by module
    rw [e]; nth_rewrite 1 [e1]; rw [ip]; simp only [k32e_G]; ring
  have ipW : ∀ (x1 x2 x3 : ℝ), ⟪x1 • (a - d) + x2 • (b - d) + x3 • (c - d), (b - d) + lam • (a - d)⟫ =
      k32e_G ⟪a - d, a - d⟫ ⟪a - d, b - d⟫ ⟪b - d, b - d⟫ ⟪b - d, c - d⟫ ⟪c - d, c - d⟫ x1 x2 x3 lam 1 0 := by
    intro x1 x2 x3
    have e : (b - d) + lam • (a - d) = lam • (a - d) + (1:ℝ) • (b - d) + (0:ℝ) • (c - d) := by module
    rw [e, ip]
  have e1 : a - d = (1:ℝ) • (a - d) + (0:ℝ) • (b - d) + (0:ℝ) • (c - d) := by module
  have e2 : b - d = (0:ℝ) • (a - d) + (1:ℝ) • (b - d) + (0:ℝ) • (c - d) := by module
  have eA : ⟪a - d, (b - d) + lam • (a - d)⟫ = lam * ⟪a - d, a - d⟫ + ⟪a - d, b - d⟫ := by
    have := ipW 1 0 0; rw [← e1] at this; rw [this]; simp only [k32e_G]; ring
  have eB : ⟪b - d, (b - d) + lam • (a - d)⟫ = lam * ⟪a - d, b - d⟫ + ⟪b - d, b - d⟫ := by
    have := ipW 0 1 0; rw [← e2] at this; rw [this]; simp only [k32e_G]; ring
  have eAB : ⟪b' - a, (b - d) + lam • (a - d)⟫ = (α1 - 1) * (lam * ⟪a - d, a - d⟫ + ⟪a - d, b - d⟫) +
      β1 * (lam * ⟪a - d, b - d⟫ + ⟪b - d, c - d⟫) := by
    have e : b' - a = (α1 - 1) • (a - d) + (0:ℝ) • (b - d) + β1 • (c - d) := by rw [hb']; module
    rw [e, ipW]; simp only [k32e_G]; ring
  have eCb : ⟪c' - b', (b - d) + lam • (a - d)⟫ = β1 * (⟪b - d, b - d⟫ - ⟪b - d, c - d⟫) := by
    have e : c' - b' = (0:ℝ) • (a - d) + β1 • (b - d) + (-β1) • (c - d) := by rw [hc', hb']; module
    rw [e, ipW]; simp only [k32e_G]; ring
  have eB1 : ⟪a - a', a - d⟫ = ⟪a - d, a - d⟫ - (β6 + γ6) * ⟪a - d, b - d⟫ := by
    have e : a - a' = (1:ℝ) • (a - d) + (-β6) • (b - d) + (-γ6) • (c - d) := by rw [ha']; module
    rw [e]; nth_rewrite 2 [e1]; rw [ip]; simp only [k32e_G]; ring
  have eN : ⟪c' - a, a - d⟫ = (α1 - 1) * ⟪a - d, a - d⟫ + β1 * ⟪a - d, b - d⟫ := by
    have e : c' - a = (α1 - 1) • (a - d) + β1 • (b - d) + (0:ℝ) • (c - d) := by rw [hc']; module
    rw [e]; nth_rewrite 2 [e1]; rw [ip]; simp only [k32e_G]; ring
  simp only [hPR]
  rw [eA, eB, eAB, eCb, eB1, eN, hAv0]
  rw [hAv0, hBv0] at hlamdef
  generalize ⟪a - d, a - d⟫ = pp at *
  generalize ⟪a - d, b - d⟫ = pq at *
  generalize ⟪b - d, b - d⟫ = qq at *
  generalize ⟪b - d, c - d⟫ = qr at *
  generalize ⟪c - d, c - d⟫ = rr at *
  have hmpr : ((1 - α1) * pp - β1 * pq) * (rr - qr) = 0 := by linarith [z2, z3]
  have hmp : (1 - α1) * pp - β1 * pq = 0 := by
    rcases mul_eq_zero.1 hmpr with h | h
    · exact h
    · linarith
  have hmrp : ((1 - α1) * pq - β1 * qr) * pp = 0 := by linear_combination z1 + pq * hmp
  have hmr : (1 - α1) * pq - β1 * qr = 0 := by
    rcases mul_eq_zero.1 hmrp with h | h
    · exact h
    · linarith
  have hU1 : pp * (α1 - 1) = β1 * (-pq) := by linarith
  have hU2 : qr * β1 = (α1 - 1) * (-pq) := by linarith
  have hD : pp * qr = pq ^ 2 := by
    have hne : β1 * (α1 - 1) ≠ 0 := by positivity
    apply mul_left_cancel₀ hne
    linear_combination (qr * β1) * hU1 + (-β1 * pq) * hU2
  have hσ' : 0 < β6 + γ6 - β1 := by linarith
  have hqrp : 0 < qr := by
    have h0 : 0 < qr * β1 := by rw [hU2]; exact mul_pos (by linarith) (neg_pos.2 hpqn)
    exact (mul_pos_iff_of_pos_right (by linarith : (0:ℝ) < β1)).1 h0
  have hA : 0 < α1 * pp - (β6 + γ6 - β1) * pq := by nlinarith [mul_pos hσ' (neg_pos.2 hpqn)]
  have hBv : 0 < -α1 * pq + β6 * qq + (γ6 - β1) * qr := by
    nlinarith [mul_pos (by linarith : (0:ℝ) < α1) (neg_pos.2 hpqn), mul_pos (by linarith : (0:ℝ) < β6) (sub_pos.2 hqq), mul_pos hσ' hqrp]
  have hl : lam * (α1 * pp - (β6 + γ6 - β1) * pq) = -α1 * pq + β6 * qq + (γ6 - β1) * qr := by
    linear_combination (-1) * hlamdef
  have hlampos : 0 < lam := by
    by_contra h; push Not at h
    nlinarith [mul_nonneg (neg_nonneg.2 h) hA.le]
  have kzA : (α1 * pp - (β6 + γ6 - β1) * pq) * (lam * pp + pq) = pp * β6 * (qq - qr) := by
    linear_combination pp * hl + (β6 + γ6 - β1) * hD
  have kzB : (α1 * pp - (β6 + γ6 - β1) * pq) * (lam * pq + qq) = (qq - qr) * (pp - γ6 * pq) := by
    linear_combination pq * hl + α1 * hD + (qq - qr) * hU1
  have kac : (α1 * pp - (β6 + γ6 - β1) * pq) * (β1 * lam - α1 + 1) = β1 * β6 * (qq - qr) := by
    linear_combination β1 * hl - α1 * hU1 + (β6 + γ6 - β1) * hU2
  have pos_of : ∀ x y : ℝ, 0 < x → x * y = x * y → 0 < x * y → 0 < y := fun x y hx _ h => by
    by_contra h'; push Not at h'; nlinarith [mul_nonneg hx.le (neg_nonneg.2 h')]
  refine ⟨by linarith [hA], hlampos, ?_, hpqn, hU1, hU2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := pos_of _ _ hA rfl (by rw [kac]; exact mul_pos (mul_pos (by linarith) (by linarith)) (sub_pos.2 hqq))
    linarith
  · have := pos_of _ _ hA rfl (by rw [kzA]; exact mul_pos (mul_pos hpp (by linarith)) (sub_pos.2 hqq))
    linarith
  · have := pos_of _ _ hA rfl (by rw [kzB]; exact mul_pos (sub_pos.2 hqq) (by nlinarith [mul_pos (by linarith : (0:ℝ) < γ6) (neg_pos.2 hpqn)]))
    linarith
  · linear_combination lam * hU1 + hU2
  · nlinarith [sub_pos.2 hqq, mul_pos (by linarith : (0:ℝ) < β1) (sub_pos.2 hqq)]
  · nlinarith [mul_pos (by linarith : (0:ℝ) < β6 + γ6) (neg_pos.2 hpqn)]
  · linarith
end Minimality.Type08Sp.C2
