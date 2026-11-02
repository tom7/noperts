module

public import Minimality.Type08S.C2K17CH

@[expose] public section


/-!
# K17C / P3I: cell S3.6a (`γ6 ≤ 1`) at `a - d` via the generators `r3 = (β6, γ6 - 1)`, `r4 = (m4, -γ6)`, `m4 = max (1-β6) 0`
of the tilt cone: `v = Λ r3 + M r4`, `Λ, M > 0`.
-/
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

theorem k17c_cone_gen {β6 γ6 Λ M : ℝ} (hb6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 ≤ 1) (hs : 1 < β6 + γ6)
    (hΛ : 0 < Λ) (hM : 0 < M) :
    K17cCone β6 γ6 (Λ * β6 + M * max (1 - β6) 0) (Λ * (γ6 - 1) - M * γ6) := by
  have h0 : 0 ≤ max (1 - β6) 0 := le_max_right _ _
  have h1 : 1 - β6 ≤ max (1 - β6) 0 := le_max_left _ _
  have h2 : max (1 - β6) 0 = 1 - β6 ∨ max (1 - β6) 0 = 0 := by
    rcases le_total (1 - β6) 0 with h | h
    · right; exact max_eq_right h
    · left; exact max_eq_left h
  set m4 := max (1 - β6) 0
  have hc3 : -β6 * γ6 + (1 - γ6) * m4 < 0 := by
    rcases h2 with h | h
    · rw [h]; nlinarith
    · rw [h]; nlinarith [mul_pos hb6 hγ6]
  have hc4 : 0 ≤ γ6 * (m4 - (1 - β6)) := mul_nonneg hγ6.le (by linarith)
  refine ⟨by nlinarith [mul_pos hΛ hb6, mul_nonneg hM.le h0], by nlinarith [mul_nonneg hΛ.le (sub_nonneg.2 hγ61), mul_pos hM hγ6],
    ?_, ?_⟩
  · nlinarith [mul_neg_of_pos_of_neg hM hc3]
  · nlinarith [mul_pos hΛ (sub_pos.2 hs), mul_nonneg hM.le hc4]

end C2
end Type08Sp
end Minimality
