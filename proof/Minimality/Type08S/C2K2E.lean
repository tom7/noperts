module

public import Minimality.Type08S.C2K2D

@[expose] public section

/-!
# C2 / K2E: the shrunk residual `Resid08FinalK2` (integration statement)

`Resid08FinalK` without `P3Tpii` and without the `L2` disjunct of `S4TRK` (both now have a lex cell, K2D):
* `S4TRK2` = `IsT ∧ ((B2) ∨ (B3)) ∧ det3 (c - b') (a - d) (b - d) = 0` (`γ4 = 1`);
* the other items of `K` are unchanged: `S4TpRK`, `TpA1ii`, planar `ResidP6`.
-/
set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- `S4TRK` without its `L2` disjunct: `(B2)` or `(B3)` on `γ4 = 1`. -/
def S4TRK2 (a a' b b' c c' d : ℝ³) : Prop :=
  IsT a' b c d ∧
    ((¬ RobKb a a' b b' c c' d ∧ N2WST a' b b' c c' d ∧ ¬ AngBig a b b' c d ∧
        ¬ NoHDNAt ({d, c', b', c} : Finset ℝ³) (b - d)) ∨
     (¬ RobKb a a' b b' c c' d ∧ RobXba a' b b' c' d ∧ ¬ AngBig a b b' c d ∧ ⟪c', b - d⟫ = ⟪b', b - d⟫ ∧
        ¬ NoHDNAt ({b, c', b', a'} : Finset ℝ³) (b - d) ∧ ¬ NoHDNAt ({d, c', b', c} : Finset ℝ³) (b - d))) ∧
    det3 (c - b') (a - d) (b - d) = 0

def ResNK2 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) : Prop :=
  ResNC' N ∧ (S4TRK2 a a' b b' c c' d ∨ S4TpRK a a' b b' c c' d ∨ TpA1ii a a' b b' c c' d) ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

def ResidNK2 (a a' b b' c c' d : ℝ³) : Prop := ∃ N : Norm08 a a' b b' c c' d, ResNK2 N

/-- **`Resid08FinalK2`**: `Resid08FinalK` without `P3Tpii` and without `L2` in `S4TRK`. -/
def Resid08FinalK2 (a a' b b' c c' d : ℝ³) : Prop :=
  ((PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ ResidP6 a a' b b' c c' d ∧
      ¬ HasLexCell (V8 a a' b b' c c' d)) ∨
  ResidNK2 a a' b b' c c' d ∨ ResidNK2 b b' a a' c c' d ∨ ResidNK2 a a' c c' b b' d ∨
  ResidNK2 c c' a a' b b' d ∨ ResidNK2 b b' c c' a a' d ∨ ResidNK2 c c' b b' a a' d

theorem resNK_imp_K2 {a a' b b' c c' d : ℝ³} {N : Norm08 a a' b b' c c' d} (h : ResNK N) : ResNK2 N := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, h3⟩
  rcases h2 with ⟨⟨hT, hL⟩, hdet⟩ | h | h | h
  · rcases hL with ⟨hTouch, -, -, -⟩ | ⟨hB2⟩ | ⟨hB3⟩
    · exact (h3 (C2.l2K_hasLexCell N hT hTouch hdet)).elim
    · exact Or.inl ⟨hT, Or.inl hB2, hdet⟩
    · exact Or.inl ⟨hT, Or.inr hB3, hdet⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact (h3 (C2.p3Tpii_hasLexCell N h)).elim

theorem resid08FinalK_imp_K2 {a a' b b' c c' d : ℝ³} (h : Resid08FinalK a a' b b' c c' d) :
    Resid08FinalK2 a a' b b' c c' d := by
  have g : ∀ {p p' q q' r r' : ℝ³}, ResidNK p p' q q' r r' d → ResidNK2 p p' q q' r r' d :=
    fun ⟨N, hN⟩ => ⟨N, resNK_imp_K2 hN⟩
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

#print axioms Minimality.Type08Sp.resid08FinalK_imp_K2
