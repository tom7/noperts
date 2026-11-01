module

public import Minimality.Type08S.C2K1F
public import Minimality.Type08S.C2K4D

@[expose] public section

/-!
# C2 / K4E: the shrunk residual `Resid08FinalK4` (`S4TpRK` removed by `C2.s4TpRK_hasLexCell`)
-/
set_option autoImplicit true

open scoped RealInnerProductSpace Topology

namespace Minimality
namespace Type08Sp

def ResNK4 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) : Prop :=
  ResNC' N ∧ (S4TRK3 a a' b b' c c' d ∨ TpA1ii a a' b b' c c' d) ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

def ResidNK4 (a a' b b' c c' d : ℝ³) : Prop := ∃ N : Norm08 a a' b b' c c' d, ResNK4 N

/-- **`Resid08FinalK4`**: `Resid08FinalK3` without the item `S4TpRK` (package K4). -/
def Resid08FinalK4 (a a' b b' c c' d : ℝ³) : Prop :=
  ((PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ ResidP6 a a' b b' c c' d ∧
      ¬ HasLexCell (V8 a a' b b' c c' d)) ∨
  ResidNK4 a a' b b' c c' d ∨ ResidNK4 b b' a a' c c' d ∨ ResidNK4 a a' c c' b b' d ∨
  ResidNK4 c c' a a' b b' d ∨ ResidNK4 b b' c c' a a' d ∨ ResidNK4 c c' b b' a a' d

theorem resNK3_imp_K4 {a a' b b' c c' d : ℝ³} {N : Norm08 a a' b b' c c' d} (h : ResNK3 N) : ResNK4 N := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, h3⟩
  rcases h2 with h | h | h
  · exact Or.inl h
  · exact (h3 (C2.s4TpRK_hasLexCell N h)).elim
  · exact Or.inr h

theorem resid08FinalK3_imp_K4 {a a' b b' c c' d : ℝ³} (h : Resid08FinalK3 a a' b b' c c' d) :
    Resid08FinalK4 a a' b b' c c' d := by
  have g : ∀ {p p' q q' r r' : ℝ³}, ResidNK3 p p' q q' r r' d → ResidNK4 p p' q q' r r' d :=
    fun ⟨N, hN⟩ => ⟨N, resNK3_imp_K4 hN⟩
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
