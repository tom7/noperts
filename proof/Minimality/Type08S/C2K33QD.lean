module

public import Minimality.Type08S.C2K33QB

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

set_option maxHeartbeats 12800000 in
theorem k28b2_R24 {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6)
    (hM : K6sM a a' b b' c c' d) (hrel : K16Rel a b c d α1 β1)
    (hβ : 1 < β1) (hσ : β6 + γ6 = β1)
    (hL : ⟪a - c', a - d⟫ = 0)
    (hM0 : 0 ≤ ⟪a - d, a - d⟫ * ⟪b - d, c - d⟫ - ⟪a - d, b - d⟫ ^ 2)
    (hΛ : (β1 - 1) * (⟪a - d, a - d⟫ * ⟪b - d, c - d⟫ - ⟪a - d, b - d⟫ ^ 2) +
      (γ6 - 1) * (⟪c - d, c - d⟫ - ⟪b - d, c - d⟫) * ⟪a - d, a - d⟫ < 0)
    (hori : 0 < k28bqOriCBA α1 β1 β6 γ6 ⟪b' - a, c - a'⟫ ⟪c' - a, c - a'⟫)
    (hori2 : 0 < k28bqOriBCA α1 β1 β6 γ6 ⟪b' - a, c - a'⟫ ⟪c' - a, c - a'⟫) :
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
  have o2 : t * ((α1 + β1 - 1) * β6) + α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * β6 < 0 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg hκ.le hh]
  have hb1 : 0 < β1 := by linarith
  have hdep : ∀ x y z : ℝ, ⟪fpoint P Q R a (x, y, z), R⟫ = ⟪a, R⟫ + x * e1 + z * e2 := by
    intro x y z; rw [inner_fpoint, hQR, hPR, hRR]; ring
  have hR0 : R ≠ 0 := by
    intro h0; apply hdet; rw [h0]; simp [det3_expand]
  refine ⟨R, hR0, ?_⟩
  set L : List (ℝ × ℝ) := [(⟪a' - c, P⟫, ⟪a' - c, Q⟫), (0, 1)] with hLdef
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
    exact tsc_scale hD ((k28bq_tsc4 hα hβ hb6 hg6 hg1 ht (hT v1 v2 hv) o1 o2).1 i j h1 h2)
  · intro y hy hyx
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    have hV : y = fpoint P Q R a (0, 0, 0) ∨ y = fpoint P Q R a (0, -β1, 0) ∨
        y = fpoint P Q R a (t, -(α1 + β1 - 1), -1) ∨ y = fpoint P Q R a (1, -(α1 + β1 - 1), 0) ∨
        y = fpoint P Q R a (β6 * t + (β1 - β6), -(α1 * β1), -β6) ∨ y = fpoint P Q R a (t * β1, 0, -β1) ∨
        y = fpoint P Q R a (β1, 0, 0) := by
      rw [eA, eD, eB, eC, eA', eC', eB']; tauto
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨_, rfl, fun v1 v2 hv D hD i => ?_⟩
      exact tsc_scale hD ((k28bq_tsc4 hα hβ hb6 hg6 hg1 ht (hT v1 v2 hv) o1 o2).2 _ (by simp) i)
    · refine ⟨_, rfl, fun v1 v2 hv D hD i => ?_⟩
      exact tsc_scale hD ((k28bq_tsc4 hα hβ hb6 hg6 hg1 ht (hT v1 v2 hv) o1 o2).2 _ (by simp) i)
    · refine ⟨_, rfl, fun v1 v2 hv D hD i => ?_⟩
      exact tsc_scale hD ((k28bq_tsc4 hα hβ hb6 hg6 hg1 ht (hT v1 v2 hv) o1 o2).2 _ (by simp) i)
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
    rcases hl with rfl | rfl
    · left; simp; exact hl1
    · right; simp

end C2
end Type08Sp
end Minimality
