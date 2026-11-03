module

public import Minimality.Type08S.C2K28L2c3

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

set_option maxHeartbeats 3200000 in
/-- **Leaf A** of the type 08 M-stratum L2 tail.  Extras: strictness `hX3 : ⟪a-c', a-b'⟫ < 0`
(`K6mH1Left` gives `≤`), `hX4 : 0 < ⟪c'-a, b'-c⟫` (`K17bL2Left` gives `≤`), and `hex` (the one genuinely
non-derived extra: at `L = 0`, `z(a') < z(c)`).  `hL2` is not used. -/
theorem k28l2_A0 {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hH1 : K6mH1Left a a' b b' c c' d α1 β1 β6 γ6)
    (hL2 : K17b2L2Left a a' b b' c c' d α1 β1 β6 γ6)
    (hX3 : ⟪a - c', a - b'⟫ < 0) (hX4 : 0 ≤ ⟪c' - a, b' - c⟫)
    (hex : ⟪a - a', k28l2aU0 a b c d α1 β1⟫ = 0 →
      ⟪a', k28l2aU0 a b c d α1 β1⟫ < ⟪c, k28l2aU0 a b c d α1 β1⟫)
    (hL : 0 ≤ ⟪a - a', k28l2aU0 a b c d α1 β1⟫) : HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hdet, hc', hb', ha', -, -, -, -, -, -⟩ := hC
  obtain ⟨hα1, hβ1, hσ, hβ6, hγ6⟩ := hH1.1
  obtain ⟨hm0, hm1, hm2⟩ := hM
  obtain ⟨hr1, hr2⟩ := hrel
  obtain ⟨P, hP⟩ : ∃ P : ℝ³, P = a - d := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ³, Q = b - d := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℝ³, r = c - d := ⟨_, rfl⟩
  have eac : a - c' = (1 - α1) • P - β1 • Q := by rw [hc', hP, hQ]; module
  have eab : a - b' = (1 - α1) • P - β1 • r := by rw [hb', hP, hr]; module
  have ecpa : c' - a = (α1 - 1) • P + β1 • Q := by rw [hc', hP, hQ]; module
  have ebpc : b' - c = α1 • P + (β1 - 1) • r := by rw [hb', hP, hr]; module
  have ebpa : b' - a = (α1 - 1) • P + β1 • r := by rw [hb', hP, hr]; module
  have ecpd : c' - d = α1 • P + β1 • Q := by rw [hc', hP, hQ]; module
  have ebpd : b' - d = α1 • P + β1 • r := by rw [hb', hP, hr]; module
  have ebc : b - c = Q - r := by rw [hQ, hr]; module
  have hdetP : det3 P Q r ≠ 0 := by rw [hP, hQ, hr]; exact hdet
  have hP0 : P ≠ 0 := by intro h0; apply hdetP; rw [h0]; simp [det3_expand]
  have hpp : 0 < ⟪P, P⟫ := real_inner_self_pos.2 hP0
  have hr1' : α1 * ⟪P, Q⟫ * (⟪Q, Q⟫ + ⟪r, r⟫ - 2 * ⟪Q, r⟫) = -(β1 - 1) * (⟪Q, Q⟫ * ⟪r, r⟫ - ⟪Q, r⟫ ^ 2) := by
    rw [hP, hQ, hr]; exact hr1
  have hr2' : 0 < ⟪Q, Q⟫ * ⟪r, r⟫ - ⟪Q, r⟫ ^ 2 := by rw [hQ, hr]; exact hr2
  rw [← hP, ebc] at hm0
  rw [ecpd, ebc] at hm1
  rw [ebpd, ebc] at hm2
  rw [eac, eab] at hX3
  rw [ecpa, ebpc] at hX4
  have hRP : ⟪r, P⟫ = ⟪P, r⟫ := real_inner_comm _ _
  have hRQ : ⟪r, Q⟫ = ⟪Q, r⟫ := real_inner_comm _ _
  have hPQ : ⟪Q, P⟫ = ⟪P, Q⟫ := real_inner_comm _ _
  simp only [inner_smul_right, inner_sub_right, inner_add_right, inner_smul_left, inner_sub_left,
    inner_add_left, conj_trivial, hRP, hRQ, hPQ] at hm0 hm1 hm2 hX3 hX4
  have hPR : ⟪P, r⟫ = ⟪P, Q⟫ := by linarith
  rw [hPR] at hm1 hm2 hX3 hX4
  have hqq : ⟪Q, r⟫ < ⟪Q, Q⟫ := by nlinarith
  have hrr : ⟪Q, r⟫ < ⟪r, r⟫ := by nlinarith
  obtain ⟨hμ, hmr, hx1, hx2, hZp, hZr⟩ := k28l2a0_alg hα1 hβ1 hpp hqq hrr hr2' hr1' (by nlinarith) (by nlinarith)
  obtain ⟨μ, hμd⟩ : ∃ μ, μ = -((1 - α1) * ⟪P, P⟫ - β1 * ⟪P, Q⟫) := ⟨_, rfl⟩
  obtain ⟨mr, hmrd⟩ : ∃ mr, mr = (1 - α1) * ⟪P, Q⟫ - β1 * ⟪Q, r⟫ := ⟨_, rfl⟩
  rw [← hμd] at hμ hx1 hx2 hZp hZr
  rw [← hmrd] at hmr hx1 hx2 hZp hZr
  obtain ⟨ρ, hρd⟩ : ∃ ρ, ρ = mr / μ := ⟨_, rfl⟩
  rw [← hρd] at hx1 hx2
  have hρμ : ρ * μ = mr := by rw [hρd]; field_simp
  have hρ : 0 < ρ := by rw [hρd]; exact div_pos hmr hμ
  obtain ⟨R, hR⟩ : ∃ R : ℝ³, R = (c - d) + ρ • (a - d) := ⟨_, rfl⟩
  have hRr : R = r + ρ • P := by rw [hR, hr, hP]
  have hμρ : μ * ρ = (1 - α1) * ⟪P, Q⟫ - β1 * ⟪Q, r⟫ := by rw [mul_comm, hρμ, hmrd]
  have hu0 : k28l2aU0 a b c d α1 β1 = μ • R := by
    simp only [k28l2aU0]
    rw [← hP, ← hQ, ← hr, hRr, smul_add, smul_smul, hμρ, hμd]; module
  have hu : ∀ x : ℝ³, ⟪x, k28l2aU0 a b c d α1 β1⟫ = μ * ⟪x, R⟫ := by
    intro x; rw [hu0, inner_smul_right]
  have hRa : ⟪a - c', R⟫ = 0 := by
    rw [eac, hRr]
    simp only [inner_smul_right, inner_sub_right, inner_add_right, inner_smul_left, inner_sub_left,
      inner_add_left, conj_trivial, hRP, hRQ, hPQ, hPR]
    rw [hμd] at hρμ
    rw [hmrd] at hρμ
    linear_combination (-1 : ℝ) * hρμ
  have hle : ⟪c', R⟫ ≤ ⟪a, R⟫ := by rw [inner_sub_left] at hRa; linarith
  have hzP : 0 < ⟪P, R⟫ := by
    have e : μ * ⟪P, R⟫ = ⟪P, P⟫ * mr + μ * ⟪P, Q⟫ := by
      rw [hRr]; simp only [inner_add_right, inner_smul_right, hPR]
      linear_combination ⟪P, P⟫ * hρμ
    exact (mul_pos_iff_of_pos_left hμ).1 (by rw [e]; exact hZp)
  have hzR : 0 < ⟪r, R⟫ := by
    have e : μ * ⟪r, R⟫ = ⟪P, Q⟫ * mr + μ * ⟪r, r⟫ := by
      rw [hRr]; simp only [inner_add_right, inner_smul_right, hRP, hPR]
      linear_combination ⟪P, Q⟫ * hρμ
    exact (mul_pos_iff_of_pos_left hμ).1 (by rw [e]; exact hZr)
  have hz1 : ⟪a, R⟫ < ⟪b', R⟫ := by
    have : 0 < ⟪b' - a, R⟫ := by
      rw [ebpa]; simp only [inner_add_left, inner_smul_left, conj_trivial]
      nlinarith [mul_pos (sub_pos.2 hα1) hzP, mul_pos (by linarith : (0:ℝ) < β1) hzR]
    rw [inner_sub_left] at this; linarith
  have hz2 : ⟪c, R⟫ < ⟪b', R⟫ := by
    have : 0 < ⟪b' - c, R⟫ := by
      rw [ebpc]; simp only [inner_add_left, inner_smul_left, conj_trivial]
      nlinarith [mul_pos (by linarith : (0:ℝ) < α1) hzP, mul_pos (sub_pos.2 hβ1) hzR]
    rw [inner_sub_left] at this; linarith
  have hz3 : ⟪a', R⟫ < ⟪c', R⟫ ∨ ⟪a', R⟫ < ⟪c, R⟫ := by
    rcases hL.lt_or_eq with h | h
    · left
      rw [hu] at h
      have h' : 0 < ⟪a - a', R⟫ := (mul_pos_iff_of_pos_left hμ).1 h
      rw [inner_sub_left] at h' hRa; linarith
    · right
      have h2 := hex h.symm
      rw [hu, hu] at h2
      exact lt_of_mul_lt_mul_left h2 hμ.le
  have hmp : ⟪a - c', a - d⟫ < 0 := by
    rw [eac, ← hP]
    simp only [inner_smul_right, inner_sub_right, inner_add_right, inner_smul_left, inner_sub_left,
      inner_add_left, conj_trivial, hRP, hRQ, hPQ]
    rw [hμd] at hμ; linarith
  rcases hx2.lt_or_eq with hx2' | hx2'
  · exact k28l2a_core hdet hc' hb' ha' hα1 hβ1 hβ6 hγ6 hσ hρ hx1 hx2' hR hmp rfl rfl hle hz1 hz2 hz3
  · have hmp' : ⟪a - c', a - d⟫ = -μ := by
      rw [eac, ← hP]
      simp only [inner_smul_right, inner_sub_right, inner_add_right, inner_smul_left, inner_sub_left,
        inner_add_left, conj_trivial, hRP, hRQ, hPQ]
      rw [hμd]; ring
    have hmq' : ⟪a - c', b - d⟫ = (1 - α1) * ⟪P, Q⟫ - β1 * ⟪Q, Q⟫ := by
      rw [eac, ← hQ]
      simp only [inner_smul_right, inner_sub_right, inner_add_right, inner_smul_left, inner_sub_left,
        inner_add_left, conj_trivial, hRP, hRQ, hPQ]
    have hmr' : ⟪a - c', c - d⟫ = (1 - α1) * ⟪P, Q⟫ - β1 * ⟪Q, r⟫ := by
      rw [eac, ← hr]
      simp only [inner_smul_right, inner_sub_right, inner_add_right, inner_smul_left, inner_sub_left,
        inner_add_left, conj_trivial, hRP, hRQ, hPQ, hPR]
    have hdd : d - a' = (-β6) • (b - d) + (-γ6) • (c - d) := by rw [ha']; module
    have hH : 0 < -β6 * ⟪a - c', b - d⟫ - γ6 * ⟪a - c', c - d⟫ := by
      have := hH1.2.1
      rw [hdd, inner_add_right, inner_smul_right, inner_smul_right] at this
      linarith
    rw [hmr', ← hmrd] at hH
    rw [hmq'] at hH
    refine k28l2a0_core hdet hc' hb' ha' hα1 hβ1 hβ6 hγ6 hσ hρ hx1 hx2'.symm hR hmp ?_ ?_ rfl rfl hle hz1 hz2 hz3
    · rw [hmp', hmq']
      have e1 : ρ * -(-μ) = mr := by rw [neg_neg, hρμ]
      rw [e1, hmrd]; nlinarith
    · rw [hmp', hmq']
      have e2 : (γ6 - 1) * ρ * -μ = -((γ6 - 1) * mr) := by linear_combination (-(γ6 - 1)) * hρμ
      rw [e2]; nlinarith

end C2
end Type08Sp
end Minimality
