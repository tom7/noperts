module

public import Minimality.Type08S.C2K24H1C0T

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
/-- Type 08 M-stratum H1 tie, cell C at the tie `N2 = 0`, `L2 < 0`: view `a - b'`, cycle `(b', c, a', c', a)` (stored ccw). -/
theorem k24h1_C0 {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hH1 : K6mH1Left a a' b b' c c' d α1 β1 β6 γ6)
    (ht : ⟪c - a', a - b'⟫ = 0) (hN : ⟪a - b', a' - c'⟫ = 0) (hL2 : ⟪a - c', a - b'⟫ < 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  have hH := hH1.1
  have hH' := hH
  obtain ⟨hα1, hβ1, hσ, hβ6, hγ6⟩ := hH'
  have hne : α1 - 1 ≠ 0 := by linarith
  obtain ⟨K1, K2⟩ := k24h1c0_keys hC hM hrel hH ht
  have hC' := hC
  obtain ⟨hdet, hc', hb', ha', -⟩ := hC'
  obtain ⟨R, hR⟩ : ∃ R : ℝ³, R = a - b' := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℝ³, P = b - d := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ³, Q = c - d := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = (α1 - 1)⁻¹ := ⟨_, rfl⟩
  have hw0 : 0 < w := by rw [hw]; exact inv_pos.2 (by linarith)
  have hwi : w * (α1 - 1) = 1 := by rw [hw]; exact inv_mul_cancel₀ hne
  have hw1 : (-w) * (1 - α1) = 1 := by linarith
  have hαw : α1 * w = 1 + w := by linarith
  have hb2 : b = d + P := by rw [hP]; abel
  have hc2 : c = d + Q := by rw [hQ]; abel
  have hRd : R = (1 - α1) • (a - d) - β1 • Q := by rw [hR, hb', hQ]; module
  have key : a - d = (-w) • R + (-(w * β1)) • Q := by
    have h1 : R + β1 • Q = (1 - α1) • (a - d) := by rw [hRd]; module
    calc a - d = ((-w) * (1 - α1)) • (a - d) := by rw [hw1, one_smul]
      _ = (-w) • ((1 - α1) • (a - d)) := by rw [mul_smul]
      _ = _ := by rw [← h1]; module
  have ha2 : a = d + ((-w) • R + (-(w * β1)) • Q) := by rw [← key]; abel
  have hb'2 : b' = d + (-(w * β1)) • Q + (-w - 1) • R := by
    have : b' = a - R := by rw [hR]; abel
    rw [this, ha2]; module
  have ha'2 : a' = d + β6 • P + γ6 • Q := by rw [ha', hP, hQ]
  have hc'2 : c' = d + β1 • P + (-(1 + w) * β1) • Q + (-(1 + w)) • R := by
    rw [hc', key, ← hP]
    match_scalars <;> first | ring1 | linear_combination (-β1) * hαw | linear_combination (-1 : ℝ) * hαw
  have hΔ : det3 P Q R ≠ 0 := by
    have e : det3 P Q R = (1 - α1) * det3 (a - d) (b - d) (c - d) := by
      rw [hRd, hP, hQ]
      simp only [det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e]
    exact mul_ne_zero (by linarith) hdet
  have hR0 : R ≠ 0 := k17f_r0 hΔ
  have Eb' : fpoint P Q R d (0, -w * β1, -w - 1) = b' := by rw [k17f_fp, hb'2]; module
  have Ea : fpoint P Q R d (0, -w * β1, -w) = a := by rw [k17f_fp, ha2]; module
  have Ec' : fpoint P Q R d (β1, -(1 + w) * β1, -(1 + w)) = c' := by rw [k17f_fp, hc'2]
  have Ea' : fpoint P Q R d (β6, γ6, 0) = a' := by rw [k17f_fp, ha'2]; module
  have Ec : fpoint P Q R d (0, 1, 0) = c := by rw [k17f_fp, hc2]; module
  have Ed : fpoint P Q R d (0, 0, 0) = d := by rw [k17f_fp]; module
  have Eb : fpoint P Q R d (1, 0, 0) = b := by rw [k17f_fp, hb2]; module
  -- metric facts
  obtain ⟨T2, hT2⟩ : ∃ T2 : ℝ, T2 = ⟪c - a', P⟫ := ⟨_, rfl⟩
  obtain ⟨T3, hT3⟩ : ∃ T3 : ℝ, T3 = ⟪c - a', Q⟫ := ⟨_, rfl⟩
  have hT3neg : T3 < 0 := by rw [hT3, hQ]; exact K2
  have hF1 : ⟪b', R⟫ < ⟪c, R⟫ := by
    have : 0 < ⟪c - b', R⟫ := by rw [hR]; exact K1
    rw [inner_sub_left] at this; linarith
  have hF2 : ⟪a', R⟫ = ⟪c', R⟫ := by
    have : ⟪R, a'⟫ - ⟪R, c'⟫ = 0 := by rw [← inner_sub_right, hR]; exact hN
    rw [real_inner_comm a' R, real_inner_comm c' R] at this; linarith
  have hF5 : ⟪a, R⟫ < ⟪c', R⟫ := by
    have : ⟪a - c', R⟫ < 0 := by rw [hR]; exact hL2
    rw [inner_sub_left] at this; linarith
  have hF3 : ⟪b', R⟫ < ⟪a, R⟫ := by
    have : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hR0
    have e : ⟪a, R⟫ - ⟪b', R⟫ = ⟪R, R⟫ := by rw [← inner_sub_left, ← hR]
    linarith
  have hF4 : ⟪c, R⟫ = ⟪a', R⟫ := by
    have : ⟪c - a', R⟫ = 0 := by rw [hR]; exact ht
    rw [inner_sub_left] at this; linarith
  obtain ⟨R2, hR2⟩ : ∃ R2 : ℝ, R2 = ⟪a' - c', P⟫ := ⟨_, rfl⟩
  obtain ⟨R3, hR3⟩ : ∃ R3 : ℝ, R3 = ⟪a' - c', Q⟫ := ⟨_, rfl⟩
  have hR3pos : 0 < R3 := by
    have h1 := k24h1c0_cc hC hM hrel hH ht
    have e : ⟪a' - c', Q⟫ = -⟪c - a', Q⟫ + ⟪c - c', Q⟫ := by
      rw [← inner_neg_left, ← inner_add_left]; congr 1; abel
    rw [hR3, e, ← hT3, hQ]; linarith
  have hW2 : ∀ v1 v2 : ℝ, ⟪a', fcomb P Q R v1 v2 0⟫ - ⟪c', fcomb P Q R v1 v2 0⟫ = v1 * R2 + v2 * R3 := by
    intro v1 v2
    rw [← inner_sub_left, hR2, hR3]
    simp only [fcomb, zero_smul, add_zero, inner_add_right, inner_smul_right]
  have hW : ∀ v1 v2 : ℝ, ⟪c, fcomb P Q R v1 v2 0⟫ - ⟪a', fcomb P Q R v1 v2 0⟫ = v1 * T2 + v2 * T3 := by
    intro v1 v2
    rw [← inner_sub_left, hT2, hT3]
    simp only [fcomb, zero_smul, add_zero, inner_add_right, inner_smul_right]
  refine ⟨R, hR0, ?_⟩
  refine k18_cone_cell (V8 a a' b b' c c' d) P Q R d hΔ (k := 5) (by norm_num) (k24h1c0Y w β1 β6 γ6)
    (k24h1c0Y_inj hw0 hβ1 hβ6 hγ6) ?_ [(-1, 0), (1, 1), (-T2, -T3), (R2, R3)] (by simp) ?_ ?_ ?_
    (ρ1 := 0) (ρ2 := 1) (δ1 := -1) (δ2 := 0) ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · rw [k24h1c0Y_0, Eb']; simp [V8]
    · rw [k24h1c0Y_1, Ea]; simp [V8]
    · rw [k24h1c0Y_2, Ec']; simp [V8]
    · rw [k24h1c0Y_3, Ea']; simp [V8]
    · rw [k24h1c0Y_4, Ec]; simp [V8]
  · intro v1 v2 hC D hD
    have h1 := hC (-1, 0) (by simp)
    have h2 := hC (1, 1) (by simp)
    simp only at h1 h2
    exact (k24h1c0_tsc hD hw0 hβ1 hβ6 hγ6 hσ (by linarith) (by linarith)).1
  · intro y hy hyx
    have hV : y = fpoint P Q R d (0, -w * β1, -w - 1) ∨ y = fpoint P Q R d (0, -w * β1, -w) ∨
        y = fpoint P Q R d (β1, -(1 + w) * β1, -(1 + w)) ∨ y = fpoint P Q R d (β6, γ6, 0) ∨
        y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) := by
      rw [Eb', Ea, Ec', Ea', Ec, Ed, Eb]
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    have hT : ∀ v1 v2 : ℝ, k18Cone [(-1, 0), (1, 1), (-T2, -T3), (R2, R3)] v1 v2 → ∀ D : ℝ, 0 < D →
        ∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (1, 0, 0)], ∀ i : ZMod 5,
          TSc D (k24h1c0Y w β1 β6 γ6 (i + 1) - k24h1c0Y w β1 β6 γ6 i) (t - k24h1c0Y w β1 β6 γ6 i) (v1, v2, 0) := by
      intro v1 v2 hC D hD
      have h1 := hC (-1, 0) (by simp)
      have h2 := hC (1, 1) (by simp)
      simp only at h1 h2
      exact (k24h1c0_tsc hD hw0 hβ1 hβ6 hγ6 hσ (by linarith) (by linarith)).2
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by rw [k24h1c0Y_0])).elim
    · exact (hyx 1 (by rw [k24h1c0Y_1])).elim
    · exact (hyx 2 (by rw [k24h1c0Y_2])).elim
    · exact (hyx 3 (by rw [k24h1c0Y_3])).elim
    · exact (hyx 4 (by rw [k24h1c0Y_4])).elim
    · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT v1 v2 hC D hD _ (by simp) i⟩
    · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT v1 v2 hC D hD _ (by simp) i⟩
  · intro v1 v2 hC hwj
    obtain ⟨e0, e1, e2, e3, e4, f0, f1, f2, f3, f4⟩ := k19_z5
    have h3 := hC (-T2, -T3) (by simp)
    have h4 := hC (R2, R3) (by simp)
    simp only at h3 h4
    have hFw : ⟪c, fcomb P Q R v1 v2 0⟫ < ⟪a', fcomb P Q R v1 v2 0⟫ := by
      have := hW v1 v2; linarith
    have hFw2 : ⟪c', fcomb P Q R v1 v2 0⟫ < ⟪a', fcomb P Q R v1 v2 0⟫ := by
      have := hW2 v1 v2; linarith
    have hFc : LexLt (⟪c, R⟫, ⟪c, fcomb P Q R v1 v2 0⟫) (⟪a', R⟫, ⟪a', fcomb P Q R v1 v2 0⟫) :=
      Or.inr ⟨hF4, hFw⟩
    have hFc' : LexLt (⟪c', R⟫, ⟪c', fcomb P Q R v1 v2 0⟫) (⟪a', R⟫, ⟪a', fcomb P Q R v1 v2 0⟫) :=
      Or.inr ⟨hF2.symm, hFw2⟩
    -- peak a'
    refine k19_lexUni_nb _ _ hwj 3 ?_ ?_ ?_
    · rw [e3]; simp only [k24h1c0Y_2, k24h1c0Y_3, Ea', Ec']; exact hFc'
    · rw [f3]; simp only [k24h1c0Y_4, k24h1c0Y_3, Ea', Ec]; exact hFc
    · intro i hi
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · right; rw [f0]; left; simp only [k24h1c0Y_0, k24h1c0Y_1, Eb', Ea]; exact hF3
      · right; rw [f1]; left; simp only [k24h1c0Y_1, k24h1c0Y_2, Ea, Ec']; exact hF5
      · right; rw [f2]; simp only [k24h1c0Y_2, k24h1c0Y_3, Ec', Ea']; exact hFc'
      · exact absurd rfl hi
      · left; rw [e4]; simp only [k24h1c0Y_4, k24h1c0Y_3, Ec, Ea']; exact hFc
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · right; refine ⟨by norm_num, by norm_num⟩
    · left; norm_num
    · left; simp only; linarith
    · left; simp only; linarith

end C2
end Type08Sp
end Minimality
