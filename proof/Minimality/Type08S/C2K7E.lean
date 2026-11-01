module

public import Minimality.Type08S.C2K7D

@[expose] public section

/-!
# C2 / K7E: the shrunk residual `Resid08FinalK7` (`S4TRK4` removed by `s4TRK4_hasLexCell`)

All non-planar items of type 08 are gone except `TpA1iiK`.
-/
set_option autoImplicit true

open scoped RealInnerProductSpace Topology

namespace Minimality
namespace Type08Sp

def ResNK7 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) : Prop :=
  ResNC' N ∧ TpA1iiK a a' b b' c c' d ∧ ¬ HasLexCell (V8 a a' b b' c c' d)

def ResidNK7 (a a' b b' c c' d : ℝ³) : Prop := ∃ N : Norm08 a a' b b' c c' d, ResNK7 N

/-- **`Resid08FinalK7`**: `Resid08FinalK6` without `S4TRK4` (package K7). -/
def Resid08FinalK7 (a a' b b' c c' d : ℝ³) : Prop :=
  ((PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ ResidP6 a a' b b' c c' d ∧
      ¬ HasLexCell (V8 a a' b b' c c' d)) ∨
  ResidNK7 a a' b b' c c' d ∨ ResidNK7 b b' a a' c c' d ∨ ResidNK7 a a' c c' b b' d ∨
  ResidNK7 c c' a a' b b' d ∨ ResidNK7 b b' c c' a a' d ∨ ResidNK7 c c' b b' a a' d

theorem resNK6_imp_K7 {a a' b b' c c' d : ℝ³} {N : Norm08 a a' b b' c c' d} (h : ResNK6 N) : ResNK7 N := by
  obtain ⟨h1, h2, h3⟩ := h
  rcases h2 with h | h
  · exact (h3 (s4TRK4_hasLexCell N h)).elim
  · exact ⟨h1, h, h3⟩

theorem resid08FinalK6_imp_K7 {a a' b b' c c' d : ℝ³} (h : Resid08FinalK6 a a' b b' c c' d) :
    Resid08FinalK7 a a' b b' c c' d := by
  have g : ∀ {p p' q q' r r' : ℝ³}, ResidNK6 p p' q q' r r' d → ResidNK7 p p' q q' r r' d :=
    fun ⟨N, hN⟩ => ⟨N, resNK6_imp_K7 hN⟩
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
