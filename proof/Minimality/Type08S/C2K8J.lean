module

public import Minimality.Type08S.C2K7E
public import Minimality.Type08S.C2K8I

@[expose] public section

/-!
# C2 / K8J: the shrunk residual `Resid08FinalK8` (`TpA1iiK` cut down by `tpA1iiK_hasLexCell`)

`TpA1iiK8` is `TpA1iiK` where one of the three codim-6 conditions L1–L2–L3 of K8 fails.
-/
set_option autoImplicit true

open scoped RealInnerProductSpace Topology

namespace Minimality
namespace Type08Sp

/-- The hypotheses of `tpA1iiK_hasLexCell` (their failure is codimension 6). -/
def K8Hyp (a a' b b' c c' d : ℝ³) : Prop :=
  (⟪c - d, b - d⟫ = 0 → det3 (a' - b) (c - d) (a - d) ≠ 0) ∧
  (⟪c - d, b - d⟫ = 0 →
      (0 < det3 (a' - b) (c - d) (a - d) * det3 (b - d) (c - d) (a - d) → ⟪a' - c', c - d⟫ = 0 →
        0 < ⟪a' - c', a - d⟫ ∨ 0 < ⟪a' - c', b - d⟫) ∧
      (det3 (a' - b) (c - d) (a - d) * det3 (b - d) (c - d) (a - d) < 0 → ⟪b - c', c - d⟫ = 0 →
        0 < ⟪b - c', a - d⟫ ∨ 0 < ⟪b - c', b - d⟫)) ∧
  (0 < ⟪c - d, b - d⟫ →
      (0 ≤ det3 (a' - b) (c - d) (a - d) * det3 (b - d) (c - d) (a - d) → ⟪a' - c', c - d⟫ = 0 →
        ⟪a' - c', b - d⟫ ≠ 0) ∧
      (det3 (a' - b) (c - d) (a - d) * det3 (b - d) (c - d) (a - d) < 0 → ⟪b - c', c - d⟫ = 0 →
        ⟪b - c', b - d⟫ ≠ 0))

/-- `TpA1iiK` off the K8 hypotheses (codimension 6). -/
def TpA1iiK8 (a a' b b' c c' d : ℝ³) : Prop :=
  TpA1iiK a a' b b' c c' d ∧ ¬ K8Hyp a a' b b' c c' d

def ResNK8 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) : Prop :=
  ResNC' N ∧ TpA1iiK8 a a' b b' c c' d ∧ ¬ HasLexCell (V8 a a' b b' c c' d)

def ResidNK8 (a a' b b' c c' d : ℝ³) : Prop := ∃ N : Norm08 a a' b b' c c' d, ResNK8 N

/-- **`Resid08FinalK8`**: `Resid08FinalK7` with `TpA1iiK` cut down to `TpA1iiK8` (package K8). -/
def Resid08FinalK8 (a a' b b' c c' d : ℝ³) : Prop :=
  ((PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ ResidP6 a a' b b' c c' d ∧
      ¬ HasLexCell (V8 a a' b b' c c' d)) ∨
  ResidNK8 a a' b b' c c' d ∨ ResidNK8 b b' a a' c c' d ∨ ResidNK8 a a' c c' b b' d ∨
  ResidNK8 c c' a a' b b' d ∨ ResidNK8 b b' c c' a a' d ∨ ResidNK8 c c' b b' a a' d

theorem resNK7_imp_K8 {a a' b b' c c' d : ℝ³} {N : Norm08 a a' b b' c c' d} (h : ResNK7 N) : ResNK8 N := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ⟨h2, ?_⟩, h3⟩
  rintro ⟨hL1, hL2, hL3⟩
  exact h3 (tpA1iiK_hasLexCell N h2 hL1 hL2 hL3)

theorem resid08FinalK7_imp_K8 {a a' b b' c c' d : ℝ³} (h : Resid08FinalK7 a a' b b' c c' d) :
    Resid08FinalK8 a a' b b' c c' d := by
  have g : ∀ {p p' q q' r r' : ℝ³}, ResidNK7 p p' q q' r r' d → ResidNK8 p p' q q' r r' d :=
    fun ⟨N, hN⟩ => ⟨N, resNK7_imp_K8 hN⟩
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
