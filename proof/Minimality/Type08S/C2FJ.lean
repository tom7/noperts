module

public import Minimality.Type08S.C2FB3

@[expose] public section

/-!
# C2 / FJ: the shrunk residual `Resid08FinalK` (integration statement)

`Resid08FinalJ` with its two codim-4 non-planar items cut down by the face cells at the edge views of `Q_ac`:
* `S4TRK`  = `S4TR ∧ γ4 = 1` (`det3 (c - b') (a - d) (b - d) = 0`, i.e. `b'c ∥ Q_ab`): codim 5;
* `S4TpRK` = `S4TpR ∧ (β6 = 1 ∨ (D_c ≤ 0 ∧ β6 ≥ 1))` (`det3 (a' - b) (c - d) (a - d) = 0`, i.e. `a'b ∥ cd`; and
  `D_c = ⟪c - d, b - d⟫`): codim 5.
Since every item of `J` carries `¬ HasLexCell`, `J → K` needs no Rupert conclusion (`resid08FinalJ_imp_K`).
-/
set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- `S4TR` on `γ4 = 1` (H2 at `T`). -/
def S4TRK (a a' b b' c c' d : ℝ³) : Prop :=
  S4TR a a' b b' c c' d ∧ det3 (c - b') (a - d) (b - d) = 0

/-- `S4TpR` on `β6 = 1`, or with `β6 ≥ 1` and `D_c ≤ 0`. -/
def S4TpRK (a a' b b' c c' d : ℝ³) : Prop :=
  S4TpR a a' b b' c c' d ∧ (det3 (a' - b) (c - d) (a - d) = 0 ∨
    (⟪c - d, b - d⟫ ≤ 0 ∧ 0 ≤ det3 (a' - b) (c - d) (a - d) * det3 (b - d) (c - d) (a - d)))

def ResNK {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) : Prop :=
  ResNC' N ∧ (S4TRK a a' b b' c c' d ∨ S4TpRK a a' b b' c c' d ∨ TpA1ii a a' b b' c c' d ∨
    P3Tpii a a' b b' c c' d) ∧ ¬ HasLexCell (V8 a a' b b' c c' d)

def ResidNK (a a' b b' c c' d : ℝ³) : Prop := ∃ N : Norm08 a a' b b' c c' d, ResNK N

/-- **`Resid08FinalK`**: `Resid08FinalJ` with `S4TR`, `S4TpR` replaced by `S4TRK`, `S4TpRK`. -/
def Resid08FinalK (a a' b b' c c' d : ℝ³) : Prop :=
  ((PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ ResidP6 a a' b b' c c' d ∧
      ¬ HasLexCell (V8 a a' b b' c c' d)) ∨
  ResidNK a a' b b' c c' d ∨ ResidNK b b' a a' c c' d ∨ ResidNK a a' c c' b b' d ∨
  ResidNK c c' a a' b b' d ∨ ResidNK b b' c c' a a' d ∨ ResidNK c c' b b' a a' d

theorem resNJ_imp_K {a a' b b' c c' d : ℝ³} {N : Norm08 a a' b b' c c' d} (h : ResNJ N) : ResNK N := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, h3⟩
  rcases h2 with h | h | h | h
  · refine Or.inl ⟨h, ?_⟩
    by_contra hne
    exact h3 (C2.s4TR_hasLexCell N h hne)
  · refine Or.inr (Or.inl ⟨h, ?_⟩)
    by_contra hne
    push_neg at hne
    obtain ⟨hb6, hC⟩ := hne
    apply h3
    refine C2.s4TpR_hasLexCell N h hb6 ?_
    by_cases hc : 0 < ⟪c - d, b - d⟫
    · exact Or.inl hc
    · exact Or.inr (hC (not_lt.mp hc))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem resid08FinalJ_imp_K {a a' b b' c c' d : ℝ³} (h : Resid08FinalJ a a' b b' c c' d) :
    Resid08FinalK a a' b b' c c' d := by
  have g : ∀ {p p' q q' r r' : ℝ³}, ResidNJ p p' q q' r r' d → ResidNK p p' q q' r r' d :=
    fun ⟨N, hN⟩ => ⟨N, resNJ_imp_K hN⟩
  rcases h with h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (g h))
  · exact Or.inr (Or.inr (Or.inl (g h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (g h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (g h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (g h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (g h))))))

/-- `K ⊆ J` (for the record). -/
theorem resid08FinalK_imp_J {a a' b b' c c' d : ℝ³} (h : Resid08FinalK a a' b b' c c' d) :
    Resid08FinalJ a a' b b' c c' d := by
  have g : ∀ {p p' q q' r r' : ℝ³}, ResidNK p p' q q' r r' d → ResidNJ p p' q q' r r' d := by
    rintro p p' q q' r r' ⟨N, h1, h2, h3⟩
    refine ⟨N, h1, ?_, h3⟩
    rcases h2 with h | h | h | h
    · exact Or.inl h.1
    · exact Or.inr (Or.inl h.1)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
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

#print axioms Minimality.Type08Sp.resid08FinalJ_imp_K
