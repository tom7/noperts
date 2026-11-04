module

public import Minimality.Type08S.C2K24H1DB

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

set_option maxHeartbeats 3200000 in
/-- Gram facts from `Rel` and `K6sM`. -/
theorem k24h1d_m {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hα1 : 1 < α1) (hβ1 : 1 < β1) :
    ⟪a - d, b - d⟫ < 0 ∧ ⟪a - d, c - d⟫ = ⟪a - d, b - d⟫ ∧ ⟪b - d, c - d⟫ < ⟪b - d, b - d⟫ ∧
    ⟪b - d, c - d⟫ < ⟪c - d, c - d⟫ ∧ 0 < ⟪b - d, b - d⟫ ∧
    α1 * ⟪a - d, b - d⟫ * (⟪b - d, b - d⟫ + ⟪c - d, c - d⟫ - 2 * ⟪b - d, c - d⟫) =
      -(β1 - 1) * (⟪b - d, b - d⟫ * ⟪c - d, c - d⟫ - ⟪b - d, c - d⟫ ^ 2) := by
  obtain ⟨hdet, hc', hb', ha', -, -, -, -, hγ6, -⟩ := hC
  obtain ⟨hm0, hm1, hm2⟩ := hM
  obtain ⟨hr1, hr2⟩ := hrel
  set P := a - d with hP
  set Q := b - d with hQ
  set R := c - d with hR
  have e4 : b - c = Q - R := by rw [hQ, hR]; module
  have e5 : c' - d = α1 • P + β1 • Q := by rw [hc']; module
  have e6 : b' - d = α1 • P + β1 • R := by rw [hb']; module
  rw [e4] at hm0
  rw [e4, e5] at hm1
  rw [e6, e4] at hm2
  have hRP : ⟪R, P⟫ = ⟪P, R⟫ := real_inner_comm _ _
  have hRQ : ⟪R, Q⟫ = ⟪Q, R⟫ := real_inner_comm _ _
  have hPQ : ⟪Q, P⟫ = ⟪P, Q⟫ := real_inner_comm _ _
  have hcs := k24h1d_cs hdet
  simp only [inner_smul_right, inner_sub_right, inner_add_right, inner_smul_left,
    inner_sub_left, inner_add_left, conj_trivial, hRP, hRQ, hPQ] at hm0 hm1 hm2
  have hr1' : α1 * ⟪P, Q⟫ * (⟪Q, Q⟫ + ⟪R, R⟫ - 2 * ⟪Q, R⟫) =
      -(β1 - 1) * (⟪Q, Q⟫ * ⟪R, R⟫ - ⟪Q, R⟫ ^ 2) := hr1
  have hPR : ⟪P, R⟫ = ⟪P, Q⟫ := by linarith
  rw [hPR] at hm1 hm2
  have hqq : ⟪Q, R⟫ < ⟪Q, Q⟫ := by nlinarith
  have hrr : ⟪Q, R⟫ < ⟪R, R⟫ := by nlinarith
  have hD : 0 < ⟪Q, Q⟫ * ⟪R, R⟫ - ⟪Q, R⟫ ^ 2 := by linarith
  have hW : 0 < ⟪Q, Q⟫ + ⟪R, R⟫ - 2 * ⟪Q, R⟫ := by linarith
  have hs : ⟪P, Q⟫ < 0 := by
    by_contra hn; push Not at hn
    have := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ α1) hn) hW.le
    nlinarith [mul_pos (sub_pos.2 hβ1) hD]
  have hQ0 : Q ≠ 0 := by intro h0; apply hdet; rw [h0]; simp [det3_expand]
  have hQQ : 0 < ⟪Q, Q⟫ := real_inner_self_pos.2 hQ0
  exact ⟨hs, hPR, hqq, hrr, hQQ, hr1'⟩

set_option maxHeartbeats 12800000 in
/-- Type 08 M-stratum H1 tie, cell D (`N2 = 0`, `L2 ≥ 0`, `W ≤ 0`): view `a - c'`, silhouette `(a, d, b, a', b')`. -/
theorem k24h1_D {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hH1 : K6mH1Left a a' b b' c c' d α1 β1 β6 γ6)
    (ht : ⟪c - a', a - b'⟫ = 0) (hN : ⟪a - b', a' - c'⟫ = 0) (hL2 : 0 ≤ ⟪a - c', a - b'⟫)
    (hW : ⟪a' - c', c - b⟫ ≤ 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨⟨hα1, hβ1, hbe, hβ6, hγ61⟩, -, -⟩ := hH1
  obtain ⟨hs, hPR, hqq, hrr, hQQ, hrel'⟩ := k24h1d_m hC hM hrel hα1 hβ1
  obtain ⟨hdet, hc', hb', ha', hα1p, hβ1p, h1, hβ6p, hγ6p, h3⟩ := hC
  have hα0 : α1 - 1 ≠ 0 := by linarith
  obtain ⟨w, hw, hwm⟩ : ∃ w : ℝ, 0 < w ∧ w * (α1 - 1) = 1 :=
    ⟨1 / (α1 - 1), by apply div_pos one_pos; linarith, by field_simp⟩
  obtain ⟨P, hP⟩ : ∃ P : ℝ³, P = a - d := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ³, Q = b - d := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ³, R = c - d := ⟨_, rfl⟩
  simp only [← hP, ← hQ, ← hR] at hs hPR hqq hrr hQQ hrel'
  have ha_eq : a = d + P := by rw [hP]; abel
  have hb_eq : b = d + Q := by rw [hQ]; abel
  have hc_eq : c = d + R := by rw [hR]; abel
  have hc'' : c' = d + α1 • P + β1 • Q := by rw [hP, hQ]; exact hc'
  have hb'' : b' = d + α1 • P + β1 • R := by rw [hP, hR]; exact hb'
  have ha'' : a' = d + β6 • Q + γ6 • R := by rw [hQ, hR]; exact ha'
  have hΔ : det3 Q R (a - c') ≠ 0 := by
    intro h0; apply hdet
    have e : det3 (b - d) (c - d) (a - c') = -(α1 - 1) * det3 (a - d) (b - d) (c - d) := by
      rw [hc']; simp only [det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [hQ, hR, e] at h0
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h (by intro h'; apply hα0; linarith)
    · exact h
  have hR0 : (a - c') ≠ 0 := k17f_r0 hΔ
  have eu : a - c' = (-(α1 - 1)) • P + (-β1) • Q := by rw [hc'', ha_eq]; module
  have e1 : (w * (α1 - 1)) • P = P := by rw [hwm, one_smul]
  have key : ∀ X Y : ℝ³, X - Y = (w * (α1 - 1)) • P - P → X = Y := by
    intro X Y h; rw [e1] at h; simpa [sub_eq_zero] using h
  have Ea : fpoint Q R (a - c') d (-(β1 * w), 0, -w) = a := by
    refine key _ _ ?_; rw [k17f_fp, eu, ha_eq]; module
  have Ed : fpoint Q R (a - c') d (0, 0, 0) = d := by rw [k17f_fp]; module
  have Eb : fpoint Q R (a - c') d (1, 0, 0) = b := by rw [k17f_fp, hb_eq]; module
  have Ea' : fpoint Q R (a - c') d (β6, γ6, 0) = a' := by rw [k17f_fp, ha'']; module
  have Eb' : fpoint Q R (a - c') d (-(β1 * (w + 1)), β1, -(w + 1)) = b' := by
    refine key _ _ ?_; rw [k17f_fp, eu, hb'']; module
  have Ec : fpoint Q R (a - c') d (0, 1, 0) = c := by rw [k17f_fp, hc_eq]; module
  have Ec' : fpoint Q R (a - c') d (-(β1 * w), 0, -(w + 1)) = c' := by
    refine key _ _ ?_; rw [k17f_fp, eu, hc'']; module
  -- Gram scalars
  have hRP : ⟪R, P⟫ = ⟪P, R⟫ := real_inner_comm _ _
  have hRQ : ⟪R, Q⟫ = ⟪Q, R⟫ := real_inner_comm _ _
  have hPQ : ⟪Q, P⟫ = ⟪P, Q⟫ := real_inner_comm _ _
  have ecb : c - b = R + (-1 : ℝ) • Q := by rw [hc_eq, hb_eq]; module
  have eca : c - a' = (1 - γ6) • R + (-β6) • Q := by rw [hc_eq, ha'']; module
  have eab : a - b' = (-(α1 - 1)) • P + (-β1) • R := by rw [ha_eq, hb'']; module
  have eac' : a' - c' = (β6 - β1) • Q + γ6 • R + (-α1) • P := by rw [ha'', hc'']; module
  have eab2 : a' - b' = β6 • Q + (γ6 - β1) • R + (-α1) • P := by rw [ha'', hb'']; module
  have eab3 : a' - b = (β6 - 1) • Q + γ6 • R := by rw [ha'', hb_eq]; module
  have ebd : b - d = Q := hQ.symm
  have ead : a - d = P := hP.symm
  have eda : d - a = -P := by rw [hP]; abel
  -- scalar hypotheses
  have hPR' : ⟪P, R⟫ = ⟪P, Q⟫ := hPR
  have hL2o := hL2
  rw [eca, eab] at ht
  rw [eab, eac'] at hN
  rw [eac' , ecb] at hW
  rw [eu, eab] at hL2
  simp only [inner_smul_right, inner_sub_right, inner_add_right, inner_neg_right, inner_smul_left,
    inner_sub_left, inner_add_left, inner_neg_left, conj_trivial, hRP, hRQ, hPQ, hPR'] at ht hN hW hL2
  obtain ⟨c1, c2, c3, c4, c5⟩ := k24h1d_core (pp := ⟪P, P⟫) (qq := ⟪Q, Q⟫) (rr := ⟪R, R⟫) (s := ⟪P, Q⟫)
    (t := ⟪Q, R⟫) hα1 hβ1 hβ6 hγ61 hs hqq hrr hQQ hrel' (by linarith) (by linarith) (by linarith)
  have F1 : ⟪a', a - c'⟫ < ⟪b', a - c'⟫ := by
    have : ⟪a' - b', a - c'⟫ < 0 := by
      rw [eab2, eu]
      simp only [inner_smul_right, inner_sub_right, inner_add_right, inner_neg_right, inner_smul_left,
        inner_sub_left, inner_add_left, inner_neg_left, conj_trivial, hRP, hRQ, hPQ, hPR']
      linarith
    rw [inner_sub_left] at this; linarith
  have F2 : ⟪a', a - c'⟫ < ⟪b, a - c'⟫ := by
    have : ⟪a' - b, a - c'⟫ < 0 := by
      rw [eab3, eu]
      simp only [inner_smul_right, inner_sub_right, inner_add_right, inner_neg_right, inner_smul_left,
        inner_sub_left, inner_add_left, inner_neg_left, conj_trivial, hRP, hRQ, hPQ, hPR']
      linarith
    rw [inner_sub_left] at this; linarith
  have F3 : ⟪b, a - c'⟫ < ⟪d, a - c'⟫ := by
    have : ⟪b - d, a - c'⟫ < 0 := by
      rw [ebd, eu]
      simp only [inner_smul_right, inner_sub_right, inner_add_right, inner_neg_right, inner_smul_left,
        inner_sub_left, inner_add_left, inner_neg_left, conj_trivial, hRP, hRQ, hPQ, hPR']
      linarith
    rw [inner_sub_left] at this; linarith
  have F4 : ⟪a, a - c'⟫ < ⟪d, a - c'⟫ := by
    have : ⟪a - d, a - c'⟫ < 0 := by
      rw [ead, eu]
      simp only [inner_smul_right, inner_sub_right, inner_add_right, inner_neg_right, inner_smul_left,
        inner_sub_left, inner_add_left, inner_neg_left, conj_trivial, hRP, hRQ, hPQ, hPR']
      linarith
    rw [inner_sub_left] at this; linarith
  have hU1 : 0 < ⟪a - b', Q⟫ := by
    rw [eab]
    simp only [inner_smul_right, inner_sub_right, inner_add_right, inner_neg_right, inner_smul_left,
        inner_sub_left, inner_add_left, inner_neg_left, conj_trivial, hRP, hRQ, hPQ, hPR']
    linarith
  have hU2 := hU1
  refine ⟨a - c', hR0, ?_⟩
  refine k18_cone_cell (V8 a a' b b' c c' d) Q R (a - c') d hΔ (k := 5) (by norm_num)
    (k24h1dY w β1 β6 γ6) (k24h1dY_inj hw hβ1 hγ6p) ?_
    [(0, 1), (1, 1), (⟪a - b', Q⟫, ⟪a - b', R⟫)] (by simp) ?_ ?_ ?_
    (ρ1 := 1) (ρ2 := 0) (δ1 := 0) (δ2 := 1) ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · rw [k24h1dY_0, Ea]; simp [V8]
    · rw [k24h1dY_1, Ed]; simp [V8]
    · rw [k24h1dY_2, Eb]; simp [V8]
    · rw [k24h1dY_3, Ea']; simp [V8]
    · rw [k24h1dY_4, Eb']; simp [V8]
  · intro v1 v2 hC D hD
    have h1 := hC (0, 1) (by simp)
    have h2 := hC (1, 1) (by simp)
    simp only at h1 h2
    exact (k24h1d_tsc hD hw hβ1 hγ61 hβ6 hbe (by linarith) (by linarith)).1
  · intro y hy hyx
    have hV : y = fpoint Q R (a - c') d (-(β1 * w), 0, -w) ∨ y = fpoint Q R (a - c') d (0, 0, 0) ∨
        y = fpoint Q R (a - c') d (1, 0, 0) ∨ y = fpoint Q R (a - c') d (β6, γ6, 0) ∨
        y = fpoint Q R (a - c') d (-(β1 * (w + 1)), β1, -(w + 1)) ∨
        y = fpoint Q R (a - c') d (0, 1, 0) ∨ y = fpoint Q R (a - c') d (-(β1 * w), 0, -(w + 1)) := by
      rw [Ea, Ed, Eb, Ea', Eb', Ec, Ec']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    have hT : ∀ v1 v2 : ℝ, k18Cone [(0, 1), (1, 1), (⟪a - b', Q⟫, ⟪a - b', R⟫)] v1 v2 →
        ∀ D : ℝ, 0 < D → ∀ t ∈ [((0 : ℝ), (1 : ℝ), (0 : ℝ)), (-(β1 * w), 0, -(w + 1))], ∀ i : ZMod 5,
          TSc D (k24h1dY w β1 β6 γ6 (i + 1) - k24h1dY w β1 β6 γ6 i) (t - k24h1dY w β1 β6 γ6 i) (v1, v2, 0) := by
      intro v1 v2 hC D hD
      have h1 := hC (0, 1) (by simp)
      have h2 := hC (1, 1) (by simp)
      simp only at h1 h2
      exact (k24h1d_tsc hD hw hβ1 hγ61 hβ6 hbe (by linarith) (by linarith)).2
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by rw [k24h1dY_0])).elim
    · exact (hyx 1 (by rw [k24h1dY_1])).elim
    · exact (hyx 2 (by rw [k24h1dY_2])).elim
    · exact (hyx 3 (by rw [k24h1dY_3])).elim
    · exact (hyx 4 (by rw [k24h1dY_4])).elim
    · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT v1 v2 hC D hD _ (by simp) i⟩
    · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT v1 v2 hC D hD _ (by simp) i⟩
  · intro v1 v2 hC hw'
    obtain ⟨e0, e1', e2, e3, e4, f0, f1, f2, f3, f4⟩ := k19_z5
    have hw3 := hC (⟪a - b', Q⟫, ⟪a - b', R⟫) (by simp)
    simp only at hw3
    have hzab : ⟪a, a - c'⟫ - ⟪b', a - c'⟫ = ⟪a - c', a - b'⟫ := by
      rw [← inner_sub_left, real_inner_comm]
    have hwab : ⟪a, fcomb Q R (a - c') v1 v2 0⟫ - ⟪b', fcomb Q R (a - c') v1 v2 0⟫ =
        ⟪a - b', Q⟫ * v1 + ⟪a - b', R⟫ * v2 := by
      rw [← inner_sub_left]; simp only [fcomb, inner_add_right, inner_smul_right, inner_zero_right]
      ring
    have hlexBA : LexLt (⟪b', a - c'⟫, ⟪b', fcomb Q R (a - c') v1 v2 0⟫)
        (⟪a, a - c'⟫, ⟪a, fcomb Q R (a - c') v1 v2 0⟫) := by
      rcases hL2o.lt_or_eq with h | h
      · left; linarith
      · right; refine ⟨by linarith, by linarith⟩
    refine k19_lexUni_nb _ _ hw' 1 ?_ ?_ ?_
    · rw [e1']; left; simp only [k24h1dY_0, k24h1dY_1, Ea, Ed]; exact F4
    · rw [f1]; left; simp only [k24h1dY_1, k24h1dY_2, Ed, Eb]; exact F3
    · intro i hi
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · right; rw [f0]; left; simp only [k24h1dY_0, k24h1dY_1, Ea, Ed]; exact F4
      · exact absurd rfl hi
      · left; rw [e2]; left; simp only [k24h1dY_1, k24h1dY_2, Ed, Eb]; exact F3
      · left; rw [e3]; left; simp only [k24h1dY_2, k24h1dY_3, Eb, Ea']; exact F2
      · right; rw [f4]; simp only [k24h1dY_4, k24h1dY_0, Eb', Ea]; exact hlexBA
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · right; exact ⟨by norm_num, by norm_num⟩
    · left; norm_num
    · left; simp only; linarith

end C2
end Type08Sp
end Minimality
