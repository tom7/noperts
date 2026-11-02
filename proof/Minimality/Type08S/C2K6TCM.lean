module

public import Minimality.Type08S.C2K6TCL

@[expose] public section

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2

theorem k6t3_z4_sub1 : (0 : ZMod 4) - 1 = 3 ∧ (1 : ZMod 4) - 1 = 0 ∧ (2 : ZMod 4) - 1 = 1 ∧ (3 : ZMod 4) - 1 = 2 := by decide

set_option maxHeartbeats 6400000 in
/-- Lex part of the Pa cell `(a,c',a',b')` (depth only): `u = ⟪b - d, R⟫ ≤ 0`.  Depths: `a = A - s t`,
`c' = (1+s) u - s t + A`, `a' = β6 u + γ6 t`, `b' = t + α4 A`. -/
theorem k6t3_pa_real {s b6 g6 a4 k0 U T B u t A : ℝ} (hs : 0 < s) (hb6 : 0 < b6) (hg6 : 0 < g6) (hg61 : g6 < 1) (hcv : 1 < b6 + g6) (ha4 : 0 < a4)
    (hA : 0 < A) (hu : u ≤ 0) (htie : u = 0 → U < 0)
    (hdep : ∀ i j : ZMod 4,
      k0 + (k6t3_paX s b6 g6 a4 i).1 * U + (k6t3_paX s b6 g6 a4 i).2.1 * T + (k6t3_paX s b6 g6 a4 i).2.2 * B <
      k0 + (k6t3_paX s b6 g6 a4 j).1 * U + (k6t3_paX s b6 g6 a4 j).2.1 * T + (k6t3_paX s b6 g6 a4 j).2.2 * B →
      (k6t3_paX s b6 g6 a4 i).1 * u + (k6t3_paX s b6 g6 a4 i).2.1 * t + (k6t3_paX s b6 g6 a4 i).2.2 * A ≤
      (k6t3_paX s b6 g6 a4 j).1 * u + (k6t3_paX s b6 g6 a4 j).2.1 * t + (k6t3_paX s b6 g6 a4 j).2.2 * A)
    (hinj : ∀ i j, k0 + (k6t3_paX s b6 g6 a4 i).1 * U + (k6t3_paX s b6 g6 a4 i).2.1 * T + (k6t3_paX s b6 g6 a4 i).2.2 * B =
      k0 + (k6t3_paX s b6 g6 a4 j).1 * U + (k6t3_paX s b6 g6 a4 j).2.1 * T + (k6t3_paX s b6 g6 a4 j).2.2 * B → i = j) :
    LexUni (fun _ => (0 : ℝ))
      (fun i => k0 + (k6t3_paX s b6 g6 a4 i).1 * U + (k6t3_paX s b6 g6 a4 i).2.1 * T + (k6t3_paX s b6 g6 a4 i).2.2 * B) := by
  obtain ⟨f0, f1, f2, f3⟩ := z4_add
  obtain ⟨s0, s1, s2, s3⟩ := k6t3_z4_sub1
  refine k5d_uni_of_nopair (by decide) _ hinj ?_
  intro i j h1 h2 h3
  rintro ⟨⟨h5, h6⟩, h7, h8⟩
  have d5 := hdep _ _ h5
  have d6 := hdep _ _ h6
  have d7 := hdep _ _ h7
  have d8 := hdep _ _ h8
  rcases z4_cases i with rfl | rfl | rfl | rfl <;>
    rcases z4_cases j with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2 (by decide)).elim
    | exact (h3 (by decide)).elim
    | (simp only [k6t3_paX_0, k6t3_paX_1, k6t3_paX_2, k6t3_paX_3, f0, f1, f2, f3, s0, s1, s2, s3] at d5 d6 d7 d8 h5 h6 h7 h8
       have g1 : 0 < 1 - g6 := by linarith
       have cv : 0 < b6 + g6 - 1 := by linarith
       rcases hu.lt_or_eq with hu' | hu'
       · nlinarith [mul_pos g1 hA, mul_pos cv hA, mul_pos ha4 hA, mul_pos hs hA, mul_pos hs g1, mul_pos hs cv, mul_nonneg cv.le (neg_nonneg.2 hu), mul_nonneg g1.le (neg_nonneg.2 hu), mul_nonneg hs.le (neg_nonneg.2 hu), mul_nonneg hb6.le (neg_nonneg.2 hu), mul_pos hs (neg_pos.2 hu'), mul_pos hb6 (neg_pos.2 hu')]
       · have hU := htie hu'
         subst hu'
         first
         | nlinarith [mul_pos hs (neg_pos.2 hU)]
         | (have ht : t < 0 := by
              by_contra hh
              push Not at hh
              nlinarith [mul_nonneg g1.le hh, mul_pos ha4 hA]
            nlinarith [mul_pos (add_pos hg6 hs) (neg_pos.2 ht)]))

end C2
end Type08Sp
end Minimality
