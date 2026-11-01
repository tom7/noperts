module

public import Minimality.Type08S.C2K8J
public import Minimality.Type08S.C2K9J

@[expose] public section

/-!
# C2 / K9K: the residual `Resid08FinalK9` — only the planar part is left

`tpA1iiK8_hasLexCell` (K9) removes the last non-planar leftover `TpA1iiK8`, so every non-planar item of
`Resid08FinalJ` is closed and what remains is the planar `ResidP6`.
-/
set_option autoImplicit true

open scoped RealInnerProductSpace Topology

namespace Minimality
namespace Type08Sp

/-- **`Resid08FinalK9`**: the planar part of `Resid08FinalK8` (all non-planar items closed). -/
def Resid08FinalK9 (a a' b b' c c' d : ℝ³) : Prop :=
  (PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ ResidP6 a a' b b' c c' d ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

theorem residNK8_false {p p' q q' r r' d : ℝ³} (h : ResidNK8 p p' q q' r r' d) : False := by
  obtain ⟨N, _, h2, h3⟩ := h
  exact h3 (tpA1iiK8_hasLexCell N h2)

theorem resid08FinalK8_imp_K9 {a a' b b' c c' d : ℝ³} (h : Resid08FinalK8 a a' b b' c c' d) :
    Resid08FinalK9 a a' b b' c c' d := by
  rcases h with h | h | h | h | h | h | h
  · exact h
  all_goals exact (residNK8_false h).elim

end Type08Sp
end Minimality
