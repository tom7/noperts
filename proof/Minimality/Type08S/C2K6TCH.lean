module

public import Minimality.Type08S.C2K6TCF

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

set_option maxHeartbeats 6400000 in
/-- Pc leaf-1 pentagon, depth part under the weaker hypothesis `u > 0 ∨ t + A < 0` (`t + A = ⟪c - d, R⟫`). -/
theorem k6t3_pc1_real' {m g k0 U T B u t A : ℝ} (hm : 0 < m) (hm1 : m < 1) (hg : 0 < g) (hA : 0 < A)
    (hu : 0 < u ∨ t + A < 0)
    (hdep : ∀ i j : ZMod 5,
      k0 + (k6t3_pcX m g i).1 * U + (k6t3_pcX m g i).2.1 * T + (k6t3_pcX m g i).2.2 * B <
      k0 + (k6t3_pcX m g j).1 * U + (k6t3_pcX m g j).2.1 * T + (k6t3_pcX m g j).2.2 * B →
      (k6t3_pcX m g i).1 * u + (k6t3_pcX m g i).2.1 * t + (k6t3_pcX m g i).2.2 * A ≤
      (k6t3_pcX m g j).1 * u + (k6t3_pcX m g j).2.1 * t + (k6t3_pcX m g j).2.2 * A)
    (hinj : ∀ i j, k0 + (k6t3_pcX m g i).1 * U + (k6t3_pcX m g i).2.1 * T + (k6t3_pcX m g i).2.2 * B =
      k0 + (k6t3_pcX m g j).1 * U + (k6t3_pcX m g j).2.1 * T + (k6t3_pcX m g j).2.2 * B → i = j) :
    LexUni (fun _ => (0 : ℝ))
      (fun i => k0 + (k6t3_pcX m g i).1 * U + (k6t3_pcX m g i).2.1 * T + (k6t3_pcX m g i).2.2 * B) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  obtain ⟨s0, s1, s2, s3, s4⟩ := k5d_z5_sub
  refine k5d_uni_of_nopair (by decide) _ hinj ?_
  intro i j h1 h2 h3
  have g1 : 0 < 1 - m := by linarith
  have p1 := mul_pos hg hA
  have p2 := mul_pos hm hA
  have p3 := mul_pos g1 hA
  rintro ⟨⟨h5, h6⟩, h7, h8⟩
  have d5 := hdep _ _ h5
  have d6 := hdep _ _ h6
  have d7 := hdep _ _ h7
  have d8 := hdep _ _ h8
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2 (by decide)).elim
    | exact (h3 (by decide)).elim
    | (simp only [k6t3_pcX_0, k6t3_pcX_1, k6t3_pcX_2, k6t3_pcX_3, k6t3_pcX_4, f0, f1, f2, f3, f4, s0, s1, s2, s3, s4] at d5 d6 d7 d8
       rcases hu with hu | hu <;>
       first
       | nlinarith
       | (have hta : t + A < 0 := by
            by_contra hh
            push Not at hh
            nlinarith [mul_nonneg hg.le hh]
          nlinarith [mul_pos g1 (neg_pos.2 hta)]))

end C2
end Type08Sp
end Minimality
