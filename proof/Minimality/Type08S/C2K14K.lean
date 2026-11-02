module

public import Minimality.Type08S.C2K14J

@[expose] public section


/-!
# K14 / K: Ta box C leftover cut to `D_c = 0`; `K14LeftTa'`; wrapper `k14_Ta'`
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

/-- Ta box C with `D_c = 0` only (the tie `D_c < 0 ∧ ζ_C = 0` is closed by `k14_TaC_hasLexCell`). -/
def K14TaC (a a' b b' c c' d : ℝ³) : Prop :=
  IsT a' b c d ∧ det3 (c - b) (b' - b) (c' - b) = 0 ∧
  0 < det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) ∧
  det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) < 0 ∧
  0 < det3 (a' - b) (c - d) (a - d) * det3 (a - d) (b - d) (c - d) ∧
  ⟪b - d, c - d⟫ = 0

def K14LeftTa' (a a' b b' c c' d : ℝ³) : Prop :=
  K6t4B11 a a' b b' c c' d ∨ K6t4Zdb0 a a' b b' c c' d ∨ K14TaC a a' b b' c c' d ∨
  K6tTaA41 a a' b b' c c' d ∨ K6tTaE a a' b b' c c' d

theorem k14_Ta' {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (h : K5ZsTouch a a' b b' c c' d ∨ K5ZsTa a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K14LeftTa' a a' b b' c c' d := by
  have hT : IsT a' b c d := h.elim (fun h => h.1) (fun h => h.1)
  have hT' : ¬ IsT' a b c' d := h.elim (fun h => h.2.1) (fun h => h.2.1)
  rcases k6tz_Ta' W h with c | l
  · exact Or.inl c
  · rcases l with l | l | l | l | l
    · exact Or.inr (Or.inl l)
    · exact Or.inr (Or.inr (Or.inl l))
    · obtain ⟨hT0, hκ, hP1, hP4, hP6, hD⟩ := l
      rcases hD with hD | ⟨hD, hz⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hT0, hκ, hP1, hP4, hP6, hD⟩)))
      · exact Or.inl (k14_TaC_hasLexCell W hT0 hκ (k5z_far2 W hT0 hT') hP1 hP4 hP6 hD)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr l))))

end C2
end Type08Sp
end Minimality
