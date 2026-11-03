module

public import Minimality.Type08S.C2K33QD
public import Minimality.Type08S.C2K33QC

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

set_option maxHeartbeats 3200000 in
theorem k43r2_tsc4w {α1 β1 β6 t v1 v2 : ℝ} (hα : 1 < α1) (hβ1 : 1 < β1) (hb6 : 0 < β6)
    (hg6 : 0 < β1 - β6) (hg1 : β1 - β6 < 1) (ht : t < 0) (hv2 : 0 < v2) (hZ : 0 < -(α1 + β1 - 1) * v1 + (β1 - 1) * v2)
    (o1 : t * (α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * (β1 - β6)) + (α1 + β1 - 1) * (β1 - β6) < 0)
    (o2 : t * ((α1 + β1 - 1) * β6) + α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * β6 ≤ 0) :
    (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      TSc 1 (k28bqCyc4 α1 β1 β6 t (i + 1) - k28bqCyc4 α1 β1 β6 t i)
        (k28bqCyc4 α1 β1 β6 t j - k28bqCyc4 α1 β1 β6 t i) (v1, v2, 0)) ∧
    (∀ x ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (0, -β1, 0), (t, -(α1 + β1 - 1), -1)], ∀ i : ZMod 4,
      TSc 1 (k28bqCyc4 α1 β1 β6 t (i + 1) - k28bqCyc4 α1 β1 β6 t i)
        (x - k28bqCyc4 α1 β1 β6 t i) (v1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3⟩ := z4_add
  have e1 : 0 < β1 - 1 := by linarith
  have e2 : 0 < α1 - 1 := by linarith
  have a0 : 0 < α1 := by linarith
  have b0 : 0 < β1 := by linarith
  have nt : 0 < -t := by linarith
  have p1 := mul_pos e1 e2
  have p2 := mul_pos a0 b0
  have p3 := mul_pos nt b0
  have p4 := mul_pos nt hb6
  have p5 := mul_pos nt hg6
  have p6 := mul_pos nt e1
  have p7 := mul_pos nt e2
  have p8 := mul_pos hb6 hg6
  have p9 := mul_pos p2 e1
  have p10 := mul_pos p2 e2
  constructor
  · intro i j h1 h2
    rcases z4_cases i with rfl | rfl | rfl | rfl <;>
      rcases z4_cases j with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k28bqCyc4_0, k28bqCyc4_1, k28bqCyc4_2, k28bqCyc4_3, f0, f1, f2, f3,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring1, by nlinarith [mul_pos hb6 hZ]⟩) | (rcases o2.lt_or_eq with h | h; (left; nlinarith); (right; refine ⟨by linarith, by nlinarith [mul_pos hb6 hZ]⟩)))
  · intro x hx i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;>
      rcases z4_cases i with rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k28bqCyc4_0, k28bqCyc4_1, k28bqCyc4_2, k28bqCyc4_3, f0, f1, f2, f3,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring1, by nlinarith [mul_pos hb6 hZ]⟩) | (rcases o2.lt_or_eq with h | h; (left; nlinarith); (right; refine ⟨by linarith, by nlinarith [mul_pos hb6 hZ]⟩)))

set_option maxHeartbeats 25600000 in
theorem k43r2_A {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6)
    (hM : K6sM a a' b b' c c' d) (hrel : K16Rel a b c d α1 β1)
    (hβ : 1 < β1) (hσ : β6 + γ6 = β1)
    (hL : ⟪a - c', a - d⟫ = 0)
    (hM0 : 0 ≤ ⟪a - d, a - d⟫ * ⟪b - d, c - d⟫ - ⟪a - d, b - d⟫ ^ 2)
    (hΛ : (β1 - 1) * (⟪a - d, a - d⟫ * ⟪b - d, c - d⟫ - ⟪a - d, b - d⟫ ^ 2) +
      (γ6 - 1) * (⟪c - d, c - d⟫ - ⟪b - d, c - d⟫) * ⟪a - d, a - d⟫ < 0)
    (hori : 0 < k28bqOriCBA α1 β1 β6 γ6 ⟪b' - a, c - a'⟫ ⟪c' - a, c - a'⟫)
    (hori2 : 0 ≤ k28bqOriBCA α1 β1 β6 γ6 ⟪b' - a, c - a'⟫ ⟪c' - a, c - a'⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨P, Q, R, t, κA, hdet, hα, hb6, hg6, hg1, ht, hκ, hκA, hκB, eA, eD, eB, eC, eA', eC', eB', hQR,
    ⟨e1, e2, hPR, hRR, he1, hf, hE, htie⟩, hl1⟩ := k28bq_setup hC hM hrel hβ hσ hL hM0 hΛ
  obtain rfl : γ6 = β1 - β6 := by linarith
  rw [← hκA, ← hκB] at hori hori2
  rw [k28bq_ori1] at hori
  rw [k28bq_ori2] at hori2
  have o1 : t * (α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * (β1 - β6)) + (α1 + β1 - 1) * (β1 - β6) < 0 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg hκ.le hh]
  have o2 : t * ((α1 + β1 - 1) * β6) + α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * β6 ≤ 0 := by
    by_contra hh; push Not at hh
    nlinarith [mul_pos hκ hh]
  have hb1 : 0 < β1 := by linarith
  have hdep : ∀ x y z : ℝ, ⟪fpoint P Q R a (x, y, z), R⟫ = ⟪a, R⟫ + x * e1 + z * e2 := by
    intro x y z; rw [inner_fpoint, hQR, hPR, hRR]; ring
  have hR0 : R ≠ 0 := by
    intro h0; apply hdet; rw [h0]; simp [det3_expand]
  refine ⟨R, hR0, ?_⟩
  set L : List (ℝ × ℝ) := [(⟪a' - c, P⟫, ⟪a' - c, Q⟫), (0, 1), (-(α1 + β1 - 1), β1 - 1)] with hLdef
  have hT : ∀ v1 v2 : ℝ, k18Cone L v1 v2 → 0 < v2 := by
    intro v1 v2 hv
    have := hv (0, 1) (by simp [hLdef])
    simpa using this
  have hZ : ∀ v1 v2 : ℝ, k18Cone L v1 v2 → 0 < -(α1 + β1 - 1) * v1 + (β1 - 1) * v2 := by
    intro v1 v2 hv
    have := hv (-(α1 + β1 - 1), β1 - 1) (by simp [hLdef])
    simpa using this
  have hsub : ∀ s u : ℝ × ℝ × ℝ, ⟪fpoint P Q R a s, R⟫ < ⟪fpoint P Q R a u, R⟫ → K25Step P Q R a L s u :=
    fun s u h => ⟨h.le, fun h' => absurd h' h.ne⟩
  have hF := hf
  have hb1' : 0 < β1 - 1 := by linarith
  have hp1 := mul_neg_of_pos_of_neg hb1' hF
  have hp2 := mul_neg_of_pos_of_neg hb1' he1
  refine k25_tie_cell (V8 a a' b b' c c' d) P Q R a hdet (k := 4) (by norm_num) (k28bqCyc4 α1 β1 β6 t)
    (k28bq_inj4 hα hβ hb6 hg6 ht) ?_ L (by simp [hLdef]) ?_ ?_
    (3 : ZMod 4) ?_ ?_ ?_ (ρ1 := -1) (ρ2 := 0) (δ1 := 0) (δ2 := 1) ?_
  · intro i
    rcases z4_cases i with rfl | rfl | rfl | rfl
    · simp only [k28bqCyc4_0, eA']; simp [V8]
    · simp only [k28bqCyc4_1, eC]; simp [V8]
    · simp only [k28bqCyc4_2, eB']; simp [V8]
    · simp only [k28bqCyc4_3, eC']; simp [V8]
  · intro v1 v2 hv D hD i j h1 h2
    exact tsc_scale hD ((k43r2_tsc4w hα hβ hb6 hg6 hg1 ht (hT v1 v2 hv) (hZ v1 v2 hv) o1 o2).1 i j h1 h2)
  · intro y hy hyx
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    have hV : y = fpoint P Q R a (0, 0, 0) ∨ y = fpoint P Q R a (0, -β1, 0) ∨
        y = fpoint P Q R a (t, -(α1 + β1 - 1), -1) ∨ y = fpoint P Q R a (1, -(α1 + β1 - 1), 0) ∨
        y = fpoint P Q R a (β6 * t + (β1 - β6), -(α1 * β1), -β6) ∨ y = fpoint P Q R a (t * β1, 0, -β1) ∨
        y = fpoint P Q R a (β1, 0, 0) := by
      rw [eA, eD, eB, eC, eA', eC', eB']; tauto
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨_, rfl, fun v1 v2 hv D hD i => ?_⟩
      exact tsc_scale hD ((k43r2_tsc4w hα hβ hb6 hg6 hg1 ht (hT v1 v2 hv) (hZ v1 v2 hv) o1 o2).2 _ (by simp) i)
    · refine ⟨_, rfl, fun v1 v2 hv D hD i => ?_⟩
      exact tsc_scale hD ((k43r2_tsc4w hα hβ hb6 hg6 hg1 ht (hT v1 v2 hv) (hZ v1 v2 hv) o1 o2).2 _ (by simp) i)
    · refine ⟨_, rfl, fun v1 v2 hv D hD i => ?_⟩
      exact tsc_scale hD ((k43r2_tsc4w hα hβ hb6 hg6 hg1 ht (hT v1 v2 hv) (hZ v1 v2 hv) o1 o2).2 _ (by simp) i)
    · exact (hyx 1 (by rw [k28bqCyc4_1])).elim
    · exact (hyx 0 (by rw [k28bqCyc4_0])).elim
    · exact (hyx 3 (by rw [k28bqCyc4_3])).elim
    · exact (hyx 2 (by rw [k28bqCyc4_2])).elim
  · rw [show (3 : ZMod 4) - 1 = 2 by decide]
    refine hsub _ _ ?_
    simp only [k28bqCyc4_2, k28bqCyc4_3, hdep]
    nlinarith
  · rw [show (3 : ZMod 4) + 1 = 0 by decide]
    refine hsub _ _ ?_
    simp only [k28bqCyc4_0, k28bqCyc4_3, hdep]
    nlinarith
  · intro i hi
    rcases z4_cases i with rfl | rfl | rfl | rfl
    · left
      rw [show (0 : ZMod 4) - 1 = 3 by decide]
      refine hsub _ _ ?_
      simp only [k28bqCyc4_0, k28bqCyc4_3, hdep]
      nlinarith
    · left
      rw [show (1 : ZMod 4) - 1 = 0 by decide]
      refine ⟨?_, fun h => ?_⟩
      · simp only [k28bqCyc4_0, k28bqCyc4_1, hdep]
        nlinarith
      · intro v1 v2 hv
        have := hv (⟪a' - c, P⟫, ⟪a' - c, Q⟫) (by simp [hLdef])
        simp only [k28bqCyc4_0, k28bqCyc4_1, eA', eC]
        simpa using this
    · left
      rw [show (2 : ZMod 4) - 1 = 1 by decide]
      refine hsub _ _ ?_
      simp only [k28bqCyc4_1, k28bqCyc4_2, hdep]
      nlinarith
    · exact absurd rfl hi
  · intro l hl
    simp only [hLdef, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · left; simp; exact hl1
    · right; simp
    · left; simp; linarith



set_option maxHeartbeats 3200000 in
theorem k43r2_tsc5w {α1 β1 β6 t v1 v2 : ℝ} (hα : 1 < α1) (hβ1 : 1 < β1) (hb6 : 0 < β6)
    (hg6 : 0 < β1 - β6) (hg1 : β1 - β6 < 1) (ht : t < 0) (hv2 : 0 < v2) (hZ : 0 < -(α1 + β1 - 1) * v1 + (β1 - 1) * v2)
    (o1 : 0 < t * (α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * (β1 - β6)) + (α1 + β1 - 1) * (β1 - β6))
    (o2 : t * ((α1 + β1 - 1) * β6) + α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * β6 ≤ 0) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k28bqCyc5 α1 β1 β6 t (i + 1) - k28bqCyc5 α1 β1 β6 t i)
        (k28bqCyc5 α1 β1 β6 t j - k28bqCyc5 α1 β1 β6 t i) (v1, v2, 0)) ∧
    (∀ x ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (0, -β1, 0)], ∀ i : ZMod 5,
      TSc 1 (k28bqCyc5 α1 β1 β6 t (i + 1) - k28bqCyc5 α1 β1 β6 t i)
        (x - k28bqCyc5 α1 β1 β6 t i) (v1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := k28bq_z5_add
  have e1 : 0 < β1 - 1 := by linarith
  have e2 : 0 < α1 - 1 := by linarith
  have a0 : 0 < α1 := by linarith
  have b0 : 0 < β1 := by linarith
  have nt : 0 < -t := by linarith
  have p1 := mul_pos e1 e2
  have p2 := mul_pos a0 b0
  have p3 := mul_pos nt b0
  have p4 := mul_pos nt hb6
  have p5 := mul_pos nt hg6
  have p6 := mul_pos nt e1
  have p7 := mul_pos nt e2
  have p8 := mul_pos hb6 hg6
  have p9 := mul_pos p2 e1
  have p10 := mul_pos p2 e2
  constructor
  · intro i j h1 h2
    rcases k28bq_z5 i with rfl | rfl | rfl | rfl | rfl <;>
      rcases k28bq_z5 j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k28bqCyc5_0, k28bqCyc5_1, k28bqCyc5_2, k28bqCyc5_3, k28bqCyc5_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring1, by nlinarith [mul_pos hb6 hZ]⟩) | (rcases o2.lt_or_eq with h | h; (left; nlinarith); (right; refine ⟨by linarith, by nlinarith [mul_pos hb6 hZ]⟩)))
  · intro x hx i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;>
      rcases k28bq_z5 i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k28bqCyc5_0, k28bqCyc5_1, k28bqCyc5_2, k28bqCyc5_3, k28bqCyc5_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring1, by nlinarith [mul_pos hb6 hZ]⟩) | (rcases o2.lt_or_eq with h | h; (left; nlinarith); (right; refine ⟨by linarith, by nlinarith [mul_pos hb6 hZ]⟩)))

set_option maxHeartbeats 25600000 in
theorem k43r2_B {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6)
    (hM : K6sM a a' b b' c c' d) (hrel : K16Rel a b c d α1 β1)
    (hβ : 1 < β1) (hσ : β6 + γ6 = β1)
    (hL : ⟪a - c', a - d⟫ = 0)
    (hM0 : 0 ≤ ⟪a - d, a - d⟫ * ⟪b - d, c - d⟫ - ⟪a - d, b - d⟫ ^ 2)
    (hΛ : (β1 - 1) * (⟪a - d, a - d⟫ * ⟪b - d, c - d⟫ - ⟪a - d, b - d⟫ ^ 2) +
      (γ6 - 1) * (⟪c - d, c - d⟫ - ⟪b - d, c - d⟫) * ⟪a - d, a - d⟫ < 0)
    (hori : k28bqOriCBA α1 β1 β6 γ6 ⟪b' - a, c - a'⟫ ⟪c' - a, c - a'⟫ < 0)
    (hori2 : 0 ≤ k28bqOriBCA α1 β1 β6 γ6 ⟪b' - a, c - a'⟫ ⟪c' - a, c - a'⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨P, Q, R, t, κA, hdet, hα, hb6, hg6, hg1, ht, hκ, hκA, hκB, eA, eD, eB, eC, eA', eC', eB', hQR,
    ⟨e1, e2, hPR, hRR, he1, hf, hE, htie⟩, hl1⟩ := k28bq_setup hC hM hrel hβ hσ hL hM0 hΛ
  obtain rfl : γ6 = β1 - β6 := by linarith
  rw [← hκA, ← hκB] at hori hori2
  rw [k28bq_ori1] at hori
  rw [k28bq_ori2] at hori2
  have o1 : 0 < t * (α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * (β1 - β6)) + (α1 + β1 - 1) * (β1 - β6) := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg hκ.le (neg_nonneg.2 hh)]
  have o2 : t * ((α1 + β1 - 1) * β6) + α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * β6 ≤ 0 := by
    by_contra hh; push Not at hh
    nlinarith [mul_pos hκ hh]
  have hb1 : 0 < β1 := by linarith
  have hdep : ∀ x y z : ℝ, ⟪fpoint P Q R a (x, y, z), R⟫ = ⟪a, R⟫ + x * e1 + z * e2 := by
    intro x y z; rw [inner_fpoint, hQR, hPR, hRR]; ring
  have hR0 : R ≠ 0 := by
    intro h0; apply hdet; rw [h0]; simp [det3_expand]
  refine ⟨R, hR0, ?_⟩
  set L : List (ℝ × ℝ) := [(⟪a' - c, P⟫, ⟪a' - c, Q⟫), (0, 1), (-(α1 + β1 - 1), β1 - 1)] with hLdef
  have hT : ∀ v1 v2 : ℝ, k18Cone L v1 v2 → 0 < v2 := by
    intro v1 v2 hv
    have := hv (0, 1) (by simp [hLdef])
    simpa using this
  have hZ : ∀ v1 v2 : ℝ, k18Cone L v1 v2 → 0 < -(α1 + β1 - 1) * v1 + (β1 - 1) * v2 := by
    intro v1 v2 hv
    have := hv (-(α1 + β1 - 1), β1 - 1) (by simp [hLdef])
    simpa using this
  have hsub : ∀ s u : ℝ × ℝ × ℝ, ⟪fpoint P Q R a s, R⟫ < ⟪fpoint P Q R a u, R⟫ → K25Step P Q R a L s u :=
    fun s u h => ⟨h.le, fun h' => absurd h' h.ne⟩
  have hF := hf
  have hb1' : 0 < β1 - 1 := by linarith
  have hp1 := mul_neg_of_pos_of_neg hb1' hF
  have hp2 := mul_neg_of_pos_of_neg hb1' he1
  refine k25_tie_cell (V8 a a' b b' c c' d) P Q R a hdet (k := 5) (by norm_num) (k28bqCyc5 α1 β1 β6 t)
    (k28bq_inj5 hα hβ hb6 hg6 ht) ?_ L (by simp [hLdef]) ?_ ?_
    (3 : ZMod 5) ?_ ?_ ?_ (ρ1 := -1) (ρ2 := 0) (δ1 := 0) (δ2 := 1) ?_
  · intro i
    rcases k28bq_z5 i with rfl | rfl | rfl | rfl | rfl
    · simp only [k28bqCyc5_0, eC]; simp [V8]
    · simp only [k28bqCyc5_1, eB']; simp [V8]
    · simp only [k28bqCyc5_2, eC']; simp [V8]
    · simp only [k28bqCyc5_3, eB]; simp [V8]
    · simp only [k28bqCyc5_4, eA']; simp [V8]
  · intro v1 v2 hv D hD i j h1 h2
    exact tsc_scale hD ((k43r2_tsc5w hα hβ hb6 hg6 hg1 ht (hT v1 v2 hv) (hZ v1 v2 hv) o1 o2).1 i j h1 h2)
  · intro y hy hyx
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    have hV : y = fpoint P Q R a (0, 0, 0) ∨ y = fpoint P Q R a (0, -β1, 0) ∨
        y = fpoint P Q R a (t, -(α1 + β1 - 1), -1) ∨ y = fpoint P Q R a (1, -(α1 + β1 - 1), 0) ∨
        y = fpoint P Q R a (β6 * t + (β1 - β6), -(α1 * β1), -β6) ∨ y = fpoint P Q R a (t * β1, 0, -β1) ∨
        y = fpoint P Q R a (β1, 0, 0) := by
      rw [eA, eD, eB, eC, eA', eC', eB']; tauto
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨_, rfl, fun v1 v2 hv D hD i => ?_⟩
      exact tsc_scale hD ((k43r2_tsc5w hα hβ hb6 hg6 hg1 ht (hT v1 v2 hv) (hZ v1 v2 hv) o1 o2).2 _ (by simp) i)
    · refine ⟨_, rfl, fun v1 v2 hv D hD i => ?_⟩
      exact tsc_scale hD ((k43r2_tsc5w hα hβ hb6 hg6 hg1 ht (hT v1 v2 hv) (hZ v1 v2 hv) o1 o2).2 _ (by simp) i)
    · exact (hyx 3 (by rw [k28bqCyc5_3])).elim
    · exact (hyx 0 (by rw [k28bqCyc5_0])).elim
    · exact (hyx 4 (by rw [k28bqCyc5_4])).elim
    · exact (hyx 2 (by rw [k28bqCyc5_2])).elim
    · exact (hyx 1 (by rw [k28bqCyc5_1])).elim
  · -- hP1 : c' < b
    rw [show (3 : ZMod 5) - 1 = 2 by decide]
    refine hsub _ _ ?_
    simp only [k28bqCyc5_2, k28bqCyc5_3, hdep]
    nlinarith
  · rw [show (3 : ZMod 5) + 1 = 4 by decide]
    refine hsub _ _ ?_
    simp only [k28bqCyc5_4, k28bqCyc5_3, hdep]
    nlinarith
  · intro i hi
    rcases k28bq_z5 i with rfl | rfl | rfl | rfl | rfl
    · left
      rw [show (0 : ZMod 5) - 1 = 4 by decide]
      refine ⟨?_, fun h => ?_⟩
      · simp only [k28bqCyc5_4, k28bqCyc5_0, hdep]
        nlinarith
      · intro v1 v2 hv
        have := hv (⟪a' - c, P⟫, ⟪a' - c, Q⟫) (by simp [hLdef])
        simp only [k28bqCyc5_4, k28bqCyc5_0, eA', eC]
        simpa using this
    · left
      rw [show (1 : ZMod 5) - 1 = 0 by decide]
      refine hsub _ _ ?_
      simp only [k28bqCyc5_0, k28bqCyc5_1, hdep]
      nlinarith
    · right
      rw [show (2 : ZMod 5) + 1 = 3 by decide]
      refine hsub _ _ ?_
      simp only [k28bqCyc5_2, k28bqCyc5_3, hdep]
      nlinarith
    · exact absurd rfl hi
    · left
      rw [show (4 : ZMod 5) - 1 = 3 by decide]
      refine hsub _ _ ?_
      simp only [k28bqCyc5_4, k28bqCyc5_3, hdep]
      nlinarith
  · intro l hl
    simp only [hLdef, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · left; simp; exact hl1
    · right; simp
    · left; simp; linarith



theorem k43r2_z3 (i : ZMod 3) : i = 0 ∨ i = 1 ∨ i = 2 := by revert i; decide
theorem k43r2_z3_add : (0 : ZMod 3) + 1 = 1 ∧ (1 : ZMod 3) + 1 = 2 ∧ (2 : ZMod 3) + 1 = 0 := by decide

/-- X1 triangle `(a', b', c')` (ccw in frame coordinates). -/
def k43r2Cyc3 (α1 β1 β6 t : ℝ) : ZMod 3 → ℝ × ℝ × ℝ :=
  ![(β6 * t + (β1 - β6), -(α1 * β1), -β6), (β1, 0, 0), (t * β1, 0, -β1)]
theorem k43r2Cyc3_0 : k43r2Cyc3 α1 β1 β6 t 0 = (β6 * t + (β1 - β6), -(α1 * β1), -β6) := rfl
theorem k43r2Cyc3_1 : k43r2Cyc3 α1 β1 β6 t 1 = (β1, 0, 0) := rfl
theorem k43r2Cyc3_2 : k43r2Cyc3 α1 β1 β6 t 2 = (t * β1, 0, -β1) := rfl

theorem k43r2_inj3 {α1 β1 β6 t : ℝ} (hα : 1 < α1) (hβ1 : 1 < β1) (hb6 : 0 < β6) (hg6 : 0 < β1 - β6)
    (ht : t < 0) : ∀ i j : ZMod 3, k43r2Cyc3 α1 β1 β6 t i = k43r2Cyc3 α1 β1 β6 t j → i = j := by
  intro i j h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  have e3 := congrArg (fun t => t.2.2) h
  have p1 := mul_pos (sub_pos.2 hα) (sub_pos.2 hβ1)
  have p2 := mul_pos (by linarith : (0:ℝ) < α1) (by linarith : (0:ℝ) < β1)
  have p3 := mul_neg_of_neg_of_pos ht (by linarith : (0:ℝ) < β1)
  have p4 := mul_neg_of_pos_of_neg hb6 ht
  rcases k43r2_z3 i with rfl | rfl | rfl <;> rcases k43r2_z3 j with rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [k43r2Cyc3_0, k43r2Cyc3_1, k43r2Cyc3_2] at e1 e2 e3; nlinarith)

set_option maxHeartbeats 3200000 in
theorem k43r2_tsc3 {α1 β1 β6 t v1 v2 : ℝ} (hα : 1 < α1) (hβ1 : 1 < β1) (hb6 : 0 < β6)
    (hg6 : 0 < β1 - β6) (hg1 : β1 - β6 < 1) (ht : t < 0) (hv2 : 0 < v2)
    (o1 : t * (α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * (β1 - β6)) + (α1 + β1 - 1) * (β1 - β6) < 0)
    (o2 : 0 < t * ((α1 + β1 - 1) * β6) + α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * β6) :
    (∀ i j : ZMod 3, j ≠ i → j ≠ i + 1 →
      TSc 1 (k43r2Cyc3 α1 β1 β6 t (i + 1) - k43r2Cyc3 α1 β1 β6 t i)
        (k43r2Cyc3 α1 β1 β6 t j - k43r2Cyc3 α1 β1 β6 t i) (v1, v2, 0)) ∧
    (∀ x ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (0, -β1, 0), (t, -(α1 + β1 - 1), -1), (1, -(α1 + β1 - 1), 0)], ∀ i : ZMod 3,
      TSc 1 (k43r2Cyc3 α1 β1 β6 t (i + 1) - k43r2Cyc3 α1 β1 β6 t i)
        (x - k43r2Cyc3 α1 β1 β6 t i) (v1, v2, 0)) := by
  obtain ⟨f0, f1, f2⟩ := k43r2_z3_add
  have e1 : 0 < β1 - 1 := by linarith
  have e2 : 0 < α1 - 1 := by linarith
  have a0 : 0 < α1 := by linarith
  have b0 : 0 < β1 := by linarith
  have nt : 0 < -t := by linarith
  have p1 := mul_pos e1 e2
  have p2 := mul_pos a0 b0
  have p3 := mul_pos nt b0
  have p4 := mul_pos nt hb6
  have p5 := mul_pos nt hg6
  have p6 := mul_pos nt e1
  have p7 := mul_pos nt e2
  have p8 := mul_pos hb6 hg6
  have p9 := mul_pos p2 e1
  have p10 := mul_pos p2 e2
  constructor
  · intro i j h1 h2
    rcases k43r2_z3 i with rfl | rfl | rfl <;>
      rcases k43r2_z3 j with rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k43r2Cyc3_0, k43r2Cyc3_1, k43r2Cyc3_2, f0, f1, f2,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring1, by nlinarith⟩))
  · intro x hx i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;>
      rcases k43r2_z3 i with rfl | rfl | rfl <;>
      (simp only [TSc, d3, k43r2Cyc3_0, k43r2Cyc3_1, k43r2Cyc3_2, f0, f1, f2,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring1, by nlinarith⟩))

set_option maxHeartbeats 25600000 in
theorem k43r2_C {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6)
    (hM : K6sM a a' b b' c c' d) (hrel : K16Rel a b c d α1 β1)
    (hβ : 1 < β1) (hσ : β6 + γ6 = β1)
    (hL : ⟪a - c', a - d⟫ = 0)
    (hM0 : 0 ≤ ⟪a - d, a - d⟫ * ⟪b - d, c - d⟫ - ⟪a - d, b - d⟫ ^ 2)
    (hΛ : (β1 - 1) * (⟪a - d, a - d⟫ * ⟪b - d, c - d⟫ - ⟪a - d, b - d⟫ ^ 2) +
      (γ6 - 1) * (⟪c - d, c - d⟫ - ⟪b - d, c - d⟫) * ⟪a - d, a - d⟫ < 0)
    (hori : 0 < k28bqOriCBA α1 β1 β6 γ6 ⟪b' - a, c - a'⟫ ⟪c' - a, c - a'⟫)
    (hori2 : k28bqOriBCA α1 β1 β6 γ6 ⟪b' - a, c - a'⟫ ⟪c' - a, c - a'⟫ < 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨P, Q, R, t, κA, hdet, hα, hb6, hg6, hg1, ht, hκ, hκA, hκB, eA, eD, eB, eC, eA', eC', eB', hQR,
    ⟨e1, e2, hPR, hRR, he1, hf, hE, htie⟩, hl1⟩ := k28bq_setup hC hM hrel hβ hσ hL hM0 hΛ
  obtain rfl : γ6 = β1 - β6 := by linarith
  rw [← hκA, ← hκB] at hori hori2
  rw [k28bq_ori1] at hori
  rw [k28bq_ori2] at hori2
  have o1 : t * (α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * (β1 - β6)) + (α1 + β1 - 1) * (β1 - β6) < 0 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg hκ.le hh]
  have o2 : 0 < t * ((α1 + β1 - 1) * β6) + α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * β6 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg hκ.le (neg_nonneg.2 hh)]
  have hb1 : 0 < β1 := by linarith
  have hdep : ∀ x y z : ℝ, ⟪fpoint P Q R a (x, y, z), R⟫ = ⟪a, R⟫ + x * e1 + z * e2 := by
    intro x y z; rw [inner_fpoint, hQR, hPR, hRR]; ring
  have hR0 : R ≠ 0 := by
    intro h0; apply hdet; rw [h0]; simp [det3_expand]
  refine ⟨R, hR0, ?_⟩
  set L : List (ℝ × ℝ) := [(0, 1)] with hLdef
  have hT : ∀ v1 v2 : ℝ, k18Cone L v1 v2 → 0 < v2 := by
    intro v1 v2 hv
    have := hv (0, 1) (by simp [hLdef])
    simpa using this
  have hsub : ∀ s u : ℝ × ℝ × ℝ, ⟪fpoint P Q R a s, R⟫ < ⟪fpoint P Q R a u, R⟫ → K25Step P Q R a L s u :=
    fun s u h => ⟨h.le, fun h' => absurd h' h.ne⟩
  have hF := hf
  have hb1' : 0 < β1 - 1 := by linarith
  have hp1 := mul_neg_of_pos_of_neg hb1' hF
  have hp2 := mul_neg_of_pos_of_neg hb1' he1
  have hFe : e1 < t * e1 - e2 := by nlinarith
  have hFe' : 0 < (t * e1 - e2) - e1 := by linarith
  have hg6' := mul_pos hg6 hFe'
  refine k25_tie_cell (V8 a a' b b' c c' d) P Q R a hdet (k := 3) (by norm_num) (k43r2Cyc3 α1 β1 β6 t)
    (k43r2_inj3 hα hβ hb6 hg6 ht) ?_ L (by simp [hLdef]) ?_ ?_
    (2 : ZMod 3) ?_ ?_ ?_ (ρ1 := 0) (ρ2 := 1) (δ1 := 0) (δ2 := 0) ?_
  · intro i
    rcases k43r2_z3 i with rfl | rfl | rfl
    · simp only [k43r2Cyc3_0, eA']; simp [V8]
    · simp only [k43r2Cyc3_1, eB']; simp [V8]
    · simp only [k43r2Cyc3_2, eC']; simp [V8]
  · intro v1 v2 hv D hD i j h1 h2
    exact tsc_scale hD ((k43r2_tsc3 hα hβ hb6 hg6 hg1 ht (hT v1 v2 hv) o1 o2).1 i j h1 h2)
  · intro y hy hyx
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    have hV : y = fpoint P Q R a (0, 0, 0) ∨ y = fpoint P Q R a (0, -β1, 0) ∨
        y = fpoint P Q R a (t, -(α1 + β1 - 1), -1) ∨ y = fpoint P Q R a (1, -(α1 + β1 - 1), 0) ∨
        y = fpoint P Q R a (β6 * t + (β1 - β6), -(α1 * β1), -β6) ∨ y = fpoint P Q R a (t * β1, 0, -β1) ∨
        y = fpoint P Q R a (β1, 0, 0) := by
      rw [eA, eD, eB, eC, eA', eC', eB']; tauto
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨_, rfl, fun v1 v2 hv D hD i => ?_⟩
      exact tsc_scale hD ((k43r2_tsc3 hα hβ hb6 hg6 hg1 ht (hT v1 v2 hv) o1 o2).2 _ (by simp) i)
    · refine ⟨_, rfl, fun v1 v2 hv D hD i => ?_⟩
      exact tsc_scale hD ((k43r2_tsc3 hα hβ hb6 hg6 hg1 ht (hT v1 v2 hv) o1 o2).2 _ (by simp) i)
    · refine ⟨_, rfl, fun v1 v2 hv D hD i => ?_⟩
      exact tsc_scale hD ((k43r2_tsc3 hα hβ hb6 hg6 hg1 ht (hT v1 v2 hv) o1 o2).2 _ (by simp) i)
    · refine ⟨_, rfl, fun v1 v2 hv D hD i => ?_⟩
      exact tsc_scale hD ((k43r2_tsc3 hα hβ hb6 hg6 hg1 ht (hT v1 v2 hv) o1 o2).2 _ (by simp) i)
    · exact (hyx 0 (by rw [k43r2Cyc3_0])).elim
    · exact (hyx 2 (by rw [k43r2Cyc3_2])).elim
    · exact (hyx 1 (by rw [k43r2Cyc3_1])).elim
  · rw [show (2 : ZMod 3) - 1 = 1 by decide]
    refine hsub _ _ ?_
    simp only [k43r2Cyc3_1, k43r2Cyc3_2, hdep]
    nlinarith
  · rw [show (2 : ZMod 3) + 1 = 0 by decide]
    refine hsub _ _ ?_
    simp only [k43r2Cyc3_0, k43r2Cyc3_2, hdep]
    nlinarith
  · intro i hi
    rcases k43r2_z3 i with rfl | rfl | rfl
    · left
      rw [show (0 : ZMod 3) - 1 = 2 by decide]
      refine hsub _ _ ?_
      simp only [k43r2Cyc3_0, k43r2Cyc3_2, hdep]
      nlinarith
    · right
      rw [show (1 : ZMod 3) + 1 = 2 by decide]
      refine hsub _ _ ?_
      simp only [k43r2Cyc3_1, k43r2Cyc3_2, hdep]
      nlinarith
    · exact absurd rfl hi
  · intro l hl
    simp only [hLdef, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl
    left; simp


/-- X2 quad `(a', b', c', b)` (ccw in frame coordinates). -/
def k43r2Cyc4 (α1 β1 β6 t : ℝ) : ZMod 4 → ℝ × ℝ × ℝ :=
  ![(β6 * t + (β1 - β6), -(α1 * β1), -β6), (β1, 0, 0), (t * β1, 0, -β1), (t, -(α1 + β1 - 1), -1)]
theorem k43r2Cyc4_0 : k43r2Cyc4 α1 β1 β6 t 0 = (β6 * t + (β1 - β6), -(α1 * β1), -β6) := rfl
theorem k43r2Cyc4_1 : k43r2Cyc4 α1 β1 β6 t 1 = (β1, 0, 0) := rfl
theorem k43r2Cyc4_2 : k43r2Cyc4 α1 β1 β6 t 2 = (t * β1, 0, -β1) := rfl
theorem k43r2Cyc4_3 : k43r2Cyc4 α1 β1 β6 t 3 = (t, -(α1 + β1 - 1), -1) := rfl

theorem k43r2_inj4 {α1 β1 β6 t : ℝ} (hα : 1 < α1) (hβ1 : 1 < β1) (hb6 : 0 < β6) (hg6 : 0 < β1 - β6)
    (ht : t < 0) : ∀ i j : ZMod 4, k43r2Cyc4 α1 β1 β6 t i = k43r2Cyc4 α1 β1 β6 t j → i = j := by
  intro i j h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  have e3 := congrArg (fun t => t.2.2) h
  have p1 := mul_pos (sub_pos.2 hα) (sub_pos.2 hβ1)
  have p2 := mul_pos (by linarith : (0:ℝ) < α1) (by linarith : (0:ℝ) < β1)
  have p3 := mul_neg_of_neg_of_pos ht (by linarith : (0:ℝ) < β1)
  have p4 := mul_neg_of_pos_of_neg hb6 ht
  rcases z4_cases i with rfl | rfl | rfl | rfl <;> rcases z4_cases j with rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [k43r2Cyc4_0, k43r2Cyc4_1, k43r2Cyc4_2, k43r2Cyc4_3] at e1 e2 e3; nlinarith)

set_option maxHeartbeats 3200000 in
theorem k43r2_tsc4 {α1 β1 β6 t v1 v2 : ℝ} (hα : 1 < α1) (hβ1 : 1 < β1) (hb6 : 0 < β6)
    (hg6 : 0 < β1 - β6) (hg1 : β1 - β6 < 1) (ht : t < 0) (hv2 : 0 < v2)
    (hZ : 0 < (α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * (β1 - β6)) * v1 + (β1 - β6) * (β1 - 1) * v2)
    (o1 : 0 ≤ t * (α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * (β1 - β6)) + (α1 + β1 - 1) * (β1 - β6))
    (o2 : 0 < t * ((α1 + β1 - 1) * β6) + α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * β6) :
    (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      TSc 1 (k43r2Cyc4 α1 β1 β6 t (i + 1) - k43r2Cyc4 α1 β1 β6 t i)
        (k43r2Cyc4 α1 β1 β6 t j - k43r2Cyc4 α1 β1 β6 t i) (v1, v2, 0)) ∧
    (∀ x ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (0, -β1, 0), (1, -(α1 + β1 - 1), 0)], ∀ i : ZMod 4,
      TSc 1 (k43r2Cyc4 α1 β1 β6 t (i + 1) - k43r2Cyc4 α1 β1 β6 t i)
        (x - k43r2Cyc4 α1 β1 β6 t i) (v1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3⟩ := z4_add
  have e1 : 0 < β1 - 1 := by linarith
  have e2 : 0 < α1 - 1 := by linarith
  have a0 : 0 < α1 := by linarith
  have b0 : 0 < β1 := by linarith
  have nt : 0 < -t := by linarith
  have p1 := mul_pos e1 e2
  have p2 := mul_pos a0 b0
  have p3 := mul_pos nt b0
  have p4 := mul_pos nt hb6
  have p5 := mul_pos nt hg6
  have p6 := mul_pos nt e1
  have p7 := mul_pos nt e2
  have p8 := mul_pos hb6 hg6
  have p9 := mul_pos p2 e1
  have p10 := mul_pos p2 e2
  constructor
  · intro i j h1 h2
    rcases z4_cases i with rfl | rfl | rfl | rfl <;>
      rcases z4_cases j with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k43r2Cyc4_0, k43r2Cyc4_1, k43r2Cyc4_2, k43r2Cyc4_3, f0, f1, f2, f3,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring1, by nlinarith⟩) | (rcases o1.lt_or_eq with h | h; (left; nlinarith); (right; refine ⟨by linarith, by nlinarith⟩)))
  · intro x hx i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;>
      rcases z4_cases i with rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k43r2Cyc4_0, k43r2Cyc4_1, k43r2Cyc4_2, k43r2Cyc4_3, f0, f1, f2, f3,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring1, by nlinarith⟩) | (rcases o1.lt_or_eq with h | h; (left; nlinarith); (right; refine ⟨by linarith, by nlinarith⟩)))

set_option maxHeartbeats 25600000 in
theorem k43r2_D {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6)
    (hM : K6sM a a' b b' c c' d) (hrel : K16Rel a b c d α1 β1)
    (hβ : 1 < β1) (hσ : β6 + γ6 = β1)
    (hL : ⟪a - c', a - d⟫ = 0)
    (hM0 : 0 ≤ ⟪a - d, a - d⟫ * ⟪b - d, c - d⟫ - ⟪a - d, b - d⟫ ^ 2)
    (hΛ : (β1 - 1) * (⟪a - d, a - d⟫ * ⟪b - d, c - d⟫ - ⟪a - d, b - d⟫ ^ 2) +
      (γ6 - 1) * (⟪c - d, c - d⟫ - ⟪b - d, c - d⟫) * ⟪a - d, a - d⟫ < 0)
    (hori : k28bqOriCBA α1 β1 β6 γ6 ⟪b' - a, c - a'⟫ ⟪c' - a, c - a'⟫ ≤ 0)
    (hori2 : k28bqOriBCA α1 β1 β6 γ6 ⟪b' - a, c - a'⟫ ⟪c' - a, c - a'⟫ < 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨P, Q, R, t, κA, hdet, hα, hb6, hg6, hg1, ht, hκ, hκA, hκB, eA, eD, eB, eC, eA', eC', eB', hQR,
    ⟨e1, e2, hPR, hRR, he1, hf, hE, htie⟩, hl1⟩ := k28bq_setup hC hM hrel hβ hσ hL hM0 hΛ
  obtain rfl : γ6 = β1 - β6 := by linarith
  rw [← hκA, ← hκB] at hori hori2
  rw [k28bq_ori1] at hori
  rw [k28bq_ori2] at hori2
  have o1 : 0 ≤ t * (α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * (β1 - β6)) + (α1 + β1 - 1) * (β1 - β6) := by
    by_contra hh; push Not at hh
    nlinarith [mul_pos hκ (neg_pos.2 hh)]
  have o2 : 0 < t * ((α1 + β1 - 1) * β6) + α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * β6 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg hκ.le (neg_nonneg.2 hh)]
  have hb1 : 0 < β1 := by linarith
  have hdep : ∀ x y z : ℝ, ⟪fpoint P Q R a (x, y, z), R⟫ = ⟪a, R⟫ + x * e1 + z * e2 := by
    intro x y z; rw [inner_fpoint, hQR, hPR, hRR]; ring
  have hR0 : R ≠ 0 := by
    intro h0; apply hdet; rw [h0]; simp [det3_expand]
  refine ⟨R, hR0, ?_⟩
  set L : List (ℝ × ℝ) := [(0, 1), (α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * (β1 - β6), (β1 - β6) * (β1 - 1))] with hLdef
  have hT : ∀ v1 v2 : ℝ, k18Cone L v1 v2 → 0 < v2 := by
    intro v1 v2 hv
    have := hv (0, 1) (by simp [hLdef])
    simpa using this
  have hZ : ∀ v1 v2 : ℝ, k18Cone L v1 v2 → 0 < (α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * (β1 - β6)) * v1 + (β1 - β6) * (β1 - 1) * v2 := by
    intro v1 v2 hv
    have := hv (α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * (β1 - β6), (β1 - β6) * (β1 - 1)) (by simp [hLdef])
    simpa using this
  have hsub : ∀ s u : ℝ × ℝ × ℝ, ⟪fpoint P Q R a s, R⟫ < ⟪fpoint P Q R a u, R⟫ → K25Step P Q R a L s u :=
    fun s u h => ⟨h.le, fun h' => absurd h' h.ne⟩
  have hF := hf
  have hb1' : 0 < β1 - 1 := by linarith
  have hp1 := mul_neg_of_pos_of_neg hb1' hF
  have hp2 := mul_neg_of_pos_of_neg hb1' he1
  have hFe : e1 < t * e1 - e2 := by nlinarith
  have hFe' : 0 < (t * e1 - e2) - e1 := by linarith
  have hg6' := mul_pos hg6 hFe'
  have hb6' := mul_pos hb6 hFe'
  refine k25_tie_cell (V8 a a' b b' c c' d) P Q R a hdet (k := 4) (by norm_num) (k43r2Cyc4 α1 β1 β6 t)
    (k43r2_inj4 hα hβ hb6 hg6 ht) ?_ L (by simp [hLdef]) ?_ ?_
    (3 : ZMod 4) ?_ ?_ ?_ (ρ1 := 0) (ρ2 := 1) (δ1 := 0) (δ2 := 0) ?_
  · intro i
    rcases z4_cases i with rfl | rfl | rfl | rfl
    · simp only [k43r2Cyc4_0, eA']; simp [V8]
    · simp only [k43r2Cyc4_1, eB']; simp [V8]
    · simp only [k43r2Cyc4_2, eC']; simp [V8]
    · simp only [k43r2Cyc4_3, eB]; simp [V8]
  · intro v1 v2 hv D hD i j h1 h2
    exact tsc_scale hD ((k43r2_tsc4 hα hβ hb6 hg6 hg1 ht (hT v1 v2 hv) (hZ v1 v2 hv) o1 o2).1 i j h1 h2)
  · intro y hy hyx
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    have hV : y = fpoint P Q R a (0, 0, 0) ∨ y = fpoint P Q R a (0, -β1, 0) ∨
        y = fpoint P Q R a (t, -(α1 + β1 - 1), -1) ∨ y = fpoint P Q R a (1, -(α1 + β1 - 1), 0) ∨
        y = fpoint P Q R a (β6 * t + (β1 - β6), -(α1 * β1), -β6) ∨ y = fpoint P Q R a (t * β1, 0, -β1) ∨
        y = fpoint P Q R a (β1, 0, 0) := by
      rw [eA, eD, eB, eC, eA', eC', eB']; tauto
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨_, rfl, fun v1 v2 hv D hD i => ?_⟩
      exact tsc_scale hD ((k43r2_tsc4 hα hβ hb6 hg6 hg1 ht (hT v1 v2 hv) (hZ v1 v2 hv) o1 o2).2 _ (by simp) i)
    · refine ⟨_, rfl, fun v1 v2 hv D hD i => ?_⟩
      exact tsc_scale hD ((k43r2_tsc4 hα hβ hb6 hg6 hg1 ht (hT v1 v2 hv) (hZ v1 v2 hv) o1 o2).2 _ (by simp) i)
    · exact (hyx 3 (by rw [k43r2Cyc4_3])).elim
    · refine ⟨_, rfl, fun v1 v2 hv D hD i => ?_⟩
      exact tsc_scale hD ((k43r2_tsc4 hα hβ hb6 hg6 hg1 ht (hT v1 v2 hv) (hZ v1 v2 hv) o1 o2).2 _ (by simp) i)
    · exact (hyx 0 (by rw [k43r2Cyc4_0])).elim
    · exact (hyx 2 (by rw [k43r2Cyc4_2])).elim
    · exact (hyx 1 (by rw [k43r2Cyc4_1])).elim
  · rw [show (3 : ZMod 4) - 1 = 2 by decide]
    refine hsub _ _ ?_
    simp only [k43r2Cyc4_2, k43r2Cyc4_3, hdep]
    nlinarith
  · rw [show (3 : ZMod 4) + 1 = 0 by decide]
    refine hsub _ _ ?_
    simp only [k43r2Cyc4_0, k43r2Cyc4_3, hdep]
    nlinarith
  · intro i hi
    rcases z4_cases i with rfl | rfl | rfl | rfl
    · left
      rw [show (0 : ZMod 4) - 1 = 3 by decide]
      refine hsub _ _ ?_
      simp only [k43r2Cyc4_0, k43r2Cyc4_3, hdep]
      nlinarith
    · left
      rw [show (1 : ZMod 4) - 1 = 0 by decide]
      refine hsub _ _ ?_
      simp only [k43r2Cyc4_0, k43r2Cyc4_1, hdep]
      nlinarith
    · right
      rw [show (2 : ZMod 4) + 1 = 3 by decide]
      refine hsub _ _ ?_
      simp only [k43r2Cyc4_2, k43r2Cyc4_3, hdep]
      nlinarith
    · exact absurd rfl hi
  · intro l hl
    simp only [hLdef, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · left; simp
    · left; simp; nlinarith


end C2
end Type08Sp
end Minimality
