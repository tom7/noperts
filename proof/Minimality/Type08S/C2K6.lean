module

public import Minimality.Type08S.C2K3G
public import Minimality.Type08S.C2K5sI

@[expose] public section

/-!
# C2 / K6: the shrunk residual `Resid08FinalK6` (`S4TRK3` cut down by `s4TRK3_hasLexCell`)

`S4TRK4` is the codim-7 sub-slice where `a'` and `b` tie in depth at both `a - d` and `b - d`.
-/
set_option autoImplicit true

open scoped RealInnerProductSpace Topology

namespace Minimality
namespace Type08Sp

/-- `S4TRK3` on the sub-slice `0 < ⟪a - d, b - d⟫`, `⟪a' - b, b - d⟫ = 0`, `0 ≤ ⟪a' - b, c - d⟫` (codimension 7). -/
def S4TRK4 (a a' b b' c c' d : ℝ³) : Prop :=
  S4TRK3 a a' b b' c c' d ∧ (0 < ⟪a - d, b - d⟫ ∧ ⟪a' - b, b - d⟫ = 0 ∧ 0 ≤ ⟪a' - b, c - d⟫)

def ResNK6 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) : Prop :=
  ResNC' N ∧ (S4TRK4 a a' b b' c c' d ∨ TpA1iiK a a' b b' c c' d) ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

def ResidNK6 (a a' b b' c c' d : ℝ³) : Prop := ∃ N : Norm08 a a' b b' c c' d, ResNK6 N

/-- **`Resid08FinalK6`**: `Resid08FinalK5` with `S4TRK3` cut down to `S4TRK4`. -/
def Resid08FinalK6 (a a' b b' c c' d : ℝ³) : Prop :=
  ((PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ ResidP6 a a' b b' c c' d ∧
      ¬ HasLexCell (V8 a a' b b' c c' d)) ∨
  ResidNK6 a a' b b' c c' d ∨ ResidNK6 b b' a a' c c' d ∨ ResidNK6 a a' c c' b b' d ∨
  ResidNK6 c c' a a' b b' d ∨ ResidNK6 b b' c c' a a' d ∨ ResidNK6 c c' b b' a a' d

theorem resNK5_imp_K6 {a a' b b' c c' d : ℝ³} {N : Norm08 a a' b b' c c' d} (h : ResNK5 N) : ResNK6 N := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, h3⟩
  rcases h2 with h | h
  · refine Or.inl ⟨h, ?_⟩
    by_contra hne
    exact h3 (s4TRK3_hasLexCell N h hne)
  · exact Or.inr h

theorem resid08FinalK5_imp_K6 {a a' b b' c c' d : ℝ³} (h : Resid08FinalK5 a a' b b' c c' d) :
    Resid08FinalK6 a a' b b' c c' d := by
  have g : ∀ {p p' q q' r r' : ℝ³}, ResidNK5 p p' q q' r r' d → ResidNK6 p p' q q' r r' d :=
    fun ⟨N, hN⟩ => ⟨N, resNK5_imp_K6 hN⟩
  rcases h with h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (g h))
  · exact Or.inr (Or.inr (Or.inl (g h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (g h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (g h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (g h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (g h))))))

end Type08Sp
end Minimality
