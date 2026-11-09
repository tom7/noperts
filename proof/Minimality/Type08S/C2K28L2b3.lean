module

public import Minimality.Type08S.C2K28L2b2

@[expose] public section

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

set_option maxHeartbeats 12800000 in
/-- Cell B′ of the type 08 M-stratum L2 tail: leaf B's view, cycle and cone, valid for any sign of
`L = ⟪a - a', u0⟫` once `z(c) < z(a')` (`hz`); the top pair (c', a') is free. Extras as in leaf B. -/
theorem k28l2_Bp {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hH1 : K6mH1Left a a' b b' c c' d α1 β1 β6 γ6)
    (hL2 : K17b2L2Left a a' b b' c c' d α1 β1 β6 γ6)
    (hD0 : ⟪c - a', a - b'⟫ = 0 → ⟪a - c', a - b'⟫ ≤ 0) (hB0 : ⟪c' - a, b' - c⟫ ≠ 0)
    (hz : ⟪c, k28l2bU0 a b c d α1 β1⟫ < ⟪a', k28l2bU0 a b c d α1 β1⟫) : HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hα1, hβ1, hσ, hβ6, hγ6⟩ := hH1.1
  have hD : ⟪a - c', a - b'⟫ ≤ 0 := by
    rcases hH1.2.2 with h | h
    · exact hD0 h
    · exact h.2
  have hB : 0 ≤ ⟪c' - a, b' - c⟫ := hL2.1.2.1
  obtain ⟨hdet, hc', hb', ha', -⟩ := hC
  obtain ⟨hm0, hm1, hm2⟩ := hM
  obtain ⟨hr1, hr2⟩ := hrel
  obtain ⟨P, hP⟩ : ∃ P : ℝ³, P = a - d := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ³, Q = b - d := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ³, R = c - d := ⟨_, rfl⟩
  have ha2 : a = d + P := by rw [hP]; abel
  have hb2 : b = d + Q := by rw [hQ]; abel
  have hc2 : c = d + R := by rw [hR]; abel
  have hc'2 : c' = d + α1 • P + β1 • Q := by rw [hc', hP, hQ]
  have hb'2 : b' = d + α1 • P + β1 • R := by rw [hb', hP, hR]
  have ha'2 : a' = d + β6 • Q + γ6 • R := by rw [ha', hQ, hR]
  rw [← hP, ← hQ, ← hR] at hdet
  rw [← hP, ← hQ, ← hR] at hr1
  rw [← hQ, ← hR] at hr2
  have w1 : a - c' = (1 - α1) • P - β1 • Q := by rw [ha2, hc'2]; module
  have w2 : a - b' = (1 - α1) • P - β1 • R := by rw [ha2, hb'2]; module
  have w3 : c' - a = (α1 - 1) • P + β1 • Q := by rw [ha2, hc'2]; module
  have w4 : b' - c = α1 • P + (β1 - 1) • R := by rw [hc2, hb'2]; module
  have w5 : a - a' = P - β6 • Q - γ6 • R := by rw [ha2, ha'2]; module
  have w6 : b - c = Q - R := by rw [hb2, hc2]; module
  have w7 : c' - d = α1 • P + β1 • Q := by rw [hc'2]; module
  have w8 : b' - d = α1 • P + β1 • R := by rw [hb'2]; module
  have hRP : ⟪R, P⟫ = ⟪P, R⟫ := real_inner_comm _ _
  have hRQ : ⟪R, Q⟫ = ⟪Q, R⟫ := real_inner_comm _ _
  have hQP : ⟪Q, P⟫ = ⟪P, Q⟫ := real_inner_comm _ _
  have hm0' : ⟪P, Q - R⟫ = 0 := by rw [← w6, hP]; exact hm0
  have hm1' : 0 < ⟪α1 • P + β1 • Q, Q - R⟫ := by rw [← w7, ← w6]; exact hm1
  have hm2' : ⟪α1 • P + β1 • R, Q - R⟫ < 0 := by rw [← w8, ← w6]; exact hm2
  have hD' : ⟪(1 - α1) • P - β1 • Q, (1 - α1) • P - β1 • R⟫ ≤ 0 := by rw [← w1, ← w2]; exact hD
  have hB' : 0 ≤ ⟪(α1 - 1) • P + β1 • Q, α1 • P + (β1 - 1) • R⟫ := by rw [← w3, ← w4]; exact hB
  have hB0' : ⟪(α1 - 1) • P + β1 • Q, α1 • P + (β1 - 1) • R⟫ ≠ 0 := by rw [← w3, ← w4]; exact hB0
  obtain ⟨mp, hmp⟩ : ∃ mp : ℝ, mp = (1 - α1) * ⟪P, P⟫ - β1 * ⟪P, Q⟫ := ⟨_, rfl⟩
  obtain ⟨mr, hmr⟩ : ∃ mr : ℝ, mr = (1 - α1) * ⟪P, Q⟫ - β1 * ⟪Q, R⟫ := ⟨_, rfl⟩
  have hu : k28l2bU0 a b c d α1 β1 = mr • P - mp • R := by
    unfold k28l2bU0; rw [← hP, ← hQ, ← hR, hmp, hmr]
  simp only [inner_smul_right, inner_sub_right, inner_add_right, inner_smul_left, inner_sub_left,
    inner_add_left, conj_trivial, hRP, hRQ, hQP] at hm0' hm1' hm2' hD' hB' hB0'
  have hPR : ⟪P, R⟫ = ⟪P, Q⟫ := by linarith
  simp only [hPR] at hD' hB' hB0'
  have hq : ⟪Q, R⟫ < ⟪Q, Q⟫ := by
    by_contra hn; push Not at hn
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ β1) (sub_nonneg.2 hn)]
  have hr : ⟪Q, R⟫ < ⟪R, R⟫ := by
    by_contra hn; push Not at hn
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ β1) (sub_nonneg.2 hn)]
  have hD'' : (1 - α1) * mp - β1 * mr ≤ 0 := by rw [hmp, hmr]; nlinarith [hD']
  have hB'' : α1 * mp + (β1 - 1) * mr ≤ 0 := by rw [hmp, hmr]; nlinarith [hB']
  have hBs : α1 * mp + (β1 - 1) * mr ≠ 0 := by
    intro h; apply hB0'; rw [hmp, hmr] at h; nlinarith [h]
  have hne : mp ≠ 0 ∨ mr ≠ 0 := by
    by_contra hn; push Not at hn
    apply hBs; rw [hn.1, hn.2]; ring
  obtain ⟨hs, hmp0, hmr0, hBlt, hzr⟩ := k28l2b_alg hα1 hβ1 hq hr hr2 hr1 hmp hmr hD'' hB'' hBs hne
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = mr / (-mp) := ⟨_, rfl⟩
  have ht : 0 < -mp := by linarith
  have hμ0 : 0 < μ := by rw [hμ]; exact div_pos hmr0 ht
  have hμt : μ * (-mp) = mr := by rw [hμ, div_mul_cancel₀ _ ht.ne']
  have hE5 : α1 ≤ β1 * μ + 1 := by
    by_contra hn; push Not at hn
    nlinarith [mul_pos (sub_pos.2 hn) ht]
  have hE6 : (β1 - 1) * μ < α1 := by
    by_contra hn; push Not at hn
    nlinarith [mul_le_mul_of_nonneg_right hn ht.le]
  obtain ⟨r, hr'⟩ : ∃ r : ℝ³, r = R + μ • P := ⟨_, rfl⟩
  have hΔ : det3 P Q r ≠ 0 := by
    have e : det3 P Q r = det3 P Q R := by
      rw [hr']
      simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e]; exact hdet
  have hr0 : r ≠ 0 := k17f_r0 hΔ
  have hu_r : mr • P - mp • R = (-mp) • r := by rw [hr', ← hμt]; module
  have hzr : ⟪c, r⟫ < ⟪a', r⟫ := by
    rw [hu, hu_r, inner_smul_right, inner_smul_right] at hz
    by_contra hn; push Not at hn
    nlinarith [mul_nonneg ht.le (sub_nonneg.2 hn)]
  have hdac : ⟪a - c', r⟫ = 0 := by
    rw [w1, hr']
    simp only [inner_smul_right, inner_sub_right, inner_add_right, inner_smul_left, inner_sub_left,
      inner_add_left, conj_trivial, hRP, hRQ, hQP]
    rw [hmp, hmr] at hμt
    linear_combination (-1) * hμt + (1 - α1) * hPR
  have hcd : 0 < ⟪c - d, r⟫ := by
    rw [← hR, hr']
    simp only [inner_add_right, inner_smul_right, hRP, hPR]
    by_contra hn; push Not at hn
    nlinarith [mul_nonneg ht.le (neg_nonneg.2 hn), hμt]
  obtain ⟨m1, hm1d⟩ : ∃ m1 : ℝ, m1 = ⟪c' - a, P⟫ := ⟨_, rfl⟩
  obtain ⟨m2, hm2d⟩ : ∃ m2 : ℝ, m2 = ⟪c' - a, Q⟫ := ⟨_, rfl⟩
  have hm1p : 0 < m1 := by
    rw [hm1d, w3]
    simp only [inner_smul_right, inner_sub_right, inner_add_right, inner_smul_left, inner_sub_left,
      inner_add_left, conj_trivial, hRP, hRQ, hQP]
    nlinarith [hmp, ht]
  have hww : 0 < (α1 - 1) * m1 + β1 * m2 := by
    have hx0 : (α1 - 1) • P + β1 • Q ≠ 0 := by
      intro h0
      have : det3 ((α1 - 1) • P + β1 • Q) Q R = (α1 - 1) * det3 P Q R := by
        simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
      rw [h0] at this
      have h0' : det3 (0 : ℝ³) Q R = 0 := by simp [det3_expand]
      have h1 : (α1 - 1) * det3 P Q R = 0 := by rw [← this]; exact h0'
      rcases mul_eq_zero.1 h1 with h | h
      · linarith
      · exact hdet h
    have hpos := real_inner_self_pos.2 hx0
    have e : ⟪(α1 - 1) • P + β1 • Q, (α1 - 1) • P + β1 • Q⟫ = (α1 - 1) * m1 + β1 * m2 := by
      rw [hm1d, hm2d, w3]
      simp only [inner_smul_right, inner_add_left, inner_add_right, inner_smul_left, conj_trivial]
    rw [e] at hpos; exact hpos
  have Ea : fpoint P Q r d (1, 0, 0) = a := by rw [k17f_fp, ha2]; module
  have Ed : fpoint P Q r d (0, 0, 0) = d := by rw [k17f_fp]; module
  have Eb : fpoint P Q r d (0, 1, 0) = b := by rw [k17f_fp, hb2]; module
  have Ec : fpoint P Q r d (-μ, 0, 1) = c := by rw [k17f_fp, hc2, hr']; module
  have Ea' : fpoint P Q r d (-(γ6 * μ), β6, γ6) = a' := by rw [k17f_fp, ha'2, hr']; module
  have Eb' : fpoint P Q r d (α1 - β1 * μ, 0, β1) = b' := by rw [k17f_fp, hb'2, hr']; module
  have Ec' : fpoint P Q r d (α1, β1, 0) = c' := by rw [k17f_fp, hc'2]; module
  have hYinj := k28l2bY_inj (α1 := α1) (by linarith : 0 < β1) (by linarith : 0 < β6) (by linarith : 0 < γ6) hμ0
  have cone : ∀ v1 v2 : ℝ, k18Cone [((0:ℝ), (-1:ℝ)), (m1, m2)] v1 v2 →
      v2 < 0 ∧ 0 < β1 * v1 - (α1 - 1) * v2 := by
    intro v1 v2 hv
    have h1 := hv (0, -1) (by simp)
    have h2 := hv (m1, m2) (by simp)
    simp only at h1 h2
    have hv2 : v2 < 0 := by linarith
    refine ⟨hv2, ?_⟩
    by_contra hn; push Not at hn
    nlinarith [mul_nonneg hm1p.le (neg_nonneg.2 hn), mul_pos hww (neg_pos.2 hv2), mul_pos (by linarith : (0:ℝ) < β1) h2]
  refine ⟨r, hr0, ?_⟩
  refine k25_tie_cell2 (V8 a a' b b' c c' d) P Q r d hΔ (k := 5) (by norm_num) (k28l2bY α1 β1 β6 γ6 μ)
    hYinj ?_ [((0:ℝ), (-1:ℝ)), (m1, m2)] (by simp) ?_ ?_ 1 (by decide) ?_ ?_ ?_
    (ρ1 := 1 + m2) (ρ2 := -m1) (δ1 := 0) (δ2 := 0) ?_
  · intro i
    rcases k28l2b_z5_cases i with rfl | rfl | rfl | rfl | rfl
    · rw [k28l2bY_0, Ea]; simp [V8]
    · rw [k28l2bY_1, Ec']; simp [V8]
    · rw [k28l2bY_2, Ea']; simp [V8]
    · rw [k28l2bY_3, Ec]; simp [V8]
    · rw [k28l2bY_4, Ed]; simp [V8]
  · intro v1 v2 hv D hD0' i j h1 h2
    obtain ⟨hv2, hv3⟩ := cone v1 v2 hv
    exact (k28l2b_tsc hD0' hα1 hβ1 hβ6 hγ6 hσ hμ0 hE5 hE6 hv2 hv3).1 i j h1 h2
  · intro y hy hyx
    have hV : y = fpoint P Q r d (1, 0, 0) ∨ y = fpoint P Q r d (α1, β1, 0) ∨
        y = fpoint P Q r d (-(γ6 * μ), β6, γ6) ∨ y = fpoint P Q r d (-μ, 0, 1) ∨
        y = fpoint P Q r d (0, 0, 0) ∨ y = fpoint P Q r d (0, 1, 0) ∨
        y = fpoint P Q r d (α1 - β1 * μ, 0, β1) := by
      rw [Ea, Ec', Ea', Ec, Ed, Eb, Eb']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    have hT : ∀ v1 v2 : ℝ, k18Cone [((0:ℝ), (-1:ℝ)), (m1, m2)] v1 v2 → ∀ D : ℝ, 0 < D →
        ∀ t ∈ [((0 : ℝ), (1 : ℝ), (0 : ℝ)), (α1 - β1 * μ, 0, β1)], ∀ i : ZMod 5,
          TSc D (k28l2bY α1 β1 β6 γ6 μ (i + 1) - k28l2bY α1 β1 β6 γ6 μ i)
            (t - k28l2bY α1 β1 β6 γ6 μ i) (v1, v2, 0) := by
      intro v1 v2 hv D hD0'
      obtain ⟨hv2, hv3⟩ := cone v1 v2 hv
      exact (k28l2b_tsc hD0' hα1 hβ1 hβ6 hγ6 hσ hμ0 hE5 hE6 hv2 hv3).2
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by rw [k28l2bY_0])).elim
    · exact (hyx 1 (by rw [k28l2bY_1])).elim
    · exact (hyx 2 (by rw [k28l2bY_2])).elim
    · exact (hyx 3 (by rw [k28l2bY_3])).elim
    · exact (hyx 4 (by rw [k28l2bY_4])).elim
    · exact ⟨_, rfl, fun v1 v2 hv D hD0' i => hT v1 v2 hv D hD0' _ (by simp) i⟩
    · exact ⟨_, rfl, fun v1 v2 hv D hD0' i => hT v1 v2 hv D hD0' _ (by simp) i⟩
  · -- hP1 : a -> c'
    have e : (1 : ZMod 5) - 1 = 0 := by decide
    rw [e]
    refine ⟨?_, fun _ v1 v2 hv => ?_⟩
    · rw [k28l2bY_0, k28l2bY_1, Ea, Ec']
      have e1 : ⟪c', r⟫ - ⟪a, r⟫ = -⟪a - c', r⟫ := by simp only [inner_sub_left]; ring
      linarith
    · rw [k28l2bY_0, k28l2bY_1, Ea, Ec']
      have h2 := hv (m1, m2) (by simp)
      simp only at h2
      rw [← hm1d, ← hm2d]
      simpa using h2
  · have e : (1 : ZMod 5) + 1 + 1 = 3 := by decide
    have e' : (1 : ZMod 5) + 1 = 2 := by decide
    rw [e, e']
    apply k28l2b_step_lt
    rw [k28l2bY_3, k28l2bY_2, Ec, Ea']
    exact hzr
  · intro i hi1 hi2
    rcases k28l2b_z5_cases i with rfl | rfl | rfl | rfl | rfl
    · right
      have e : (0 : ZMod 5) + 1 = 1 := by decide
      rw [e]
      refine ⟨?_, fun _ v1 v2 hv => ?_⟩
      · rw [k28l2bY_0, k28l2bY_1, Ea, Ec']
        have e1 : ⟪c', r⟫ - ⟪a, r⟫ = -⟪a - c', r⟫ := by simp only [inner_sub_left]; ring
        linarith
      · rw [k28l2bY_0, k28l2bY_1, Ea, Ec']
        have h2 := hv (m1, m2) (by simp)
        simp only at h2
        rw [← hm1d, ← hm2d]
        simpa using h2
    · exact absurd rfl hi1
    · exact absurd rfl hi2
    · left
      have e : (3 : ZMod 5) - 1 = 2 := by decide
      rw [e]
      apply k28l2b_step_lt
      rw [k28l2bY_3, k28l2bY_2, Ec, Ea']
      exact hzr
    · left
      have e : (4 : ZMod 5) - 1 = 3 := by decide
      rw [e]
      apply k28l2b_step_lt
      rw [k28l2bY_4, k28l2bY_3, Ed, Ec]
      have e1 : ⟪c, r⟫ - ⟪d, r⟫ = ⟪c - d, r⟫ := by simp only [inner_sub_left]
      linarith
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · left; simp only; linarith
    · left; simp only; nlinarith

end C2
end Type08Sp
end Minimality
