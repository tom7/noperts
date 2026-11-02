module

public import Minimality.Type08S.C2K17AC
public import Minimality.Type08S.C2K17HZ

@[expose] public section


/-!
# K17A / Z: composition.  `K6sDN2one` closed by `k17a_dn2one`; `Resid08FinalK17I` drops that disjunct.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
open C2

def K17ISlice {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6t3LeftTT a a' b b' c c' d ∨ K17gcLeftPa a a' b b' c c' d ∨ K17gcLeftPc a a' b b' c c' d ∨
  K17hLeftTa a a' b b' c c' d ∨ K17hLeftTc a a' b b' c c' d ∨
  K17B2LeftMN2 W ∨ K17LeftMKb W

theorem k17i_slice_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K17HSlice W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K17ISlice W := by
  rcases h with h | h | h | h | h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inl (k17a_dn2one W h)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

def K17IResidP (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ W : Norm08w a a' b b' c c' d, ResP W.F d ∧ K17ISlice W

def K17IResidP6 (a a' b b' c c' d : ℝ³) : Prop :=
  K17IResidP a a' b b' c c' d ∨ K17IResidP b b' a a' c c' d ∨ K17IResidP a a' c c' b b' d ∨
  K17IResidP c c' a a' b b' d ∨ K17IResidP b b' c c' a a' d ∨ K17IResidP c c' b b' a a' d

/-- **`Resid08FinalK17I`**: `Resid08FinalK17H` without the DN2 `α1 = 1` slice (closed by `k17a_dn2one`). -/
def Resid08FinalK17I (a a' b b' c c' d : ℝ³) : Prop :=
  (PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ K17IResidP6 a a' b b' c c' d ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

theorem k17i_residP_step {p p' q q' r r' d : ℝ³} (h : K17HResidP p p' q q' r r' d) :
    HasLexCell (V8 p p' q q' r r' d) ∨ K17IResidP p p' q q' r r' d := by
  obtain ⟨W, hR, hs⟩ := h
  rcases k17i_slice_step W hs with h | h
  · exact Or.inl h
  · exact Or.inr ⟨W, hR, h⟩

theorem resid08FinalK17H_imp_K17I {a a' b b' c c' d : ℝ³}
    (h : Resid08FinalK17H a a' b b' c c' d) : Resid08FinalK17I a a' b b' c c' d := by
  obtain ⟨hpl, h6, hno⟩ := h
  have e := type08_set_perm a a' b b' c c' d
  refine ⟨hpl, ?_, hno⟩
  rcases h6 with h | h | h | h | h | h
  · rcases k17i_residP_step h with h | h
    · exact (hno h).elim
    · exact Or.inl h
  · rcases k17i_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.1]; exact h)).elim
    · exact Or.inr (Or.inl h)
  · rcases k17i_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k17i_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k17i_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k17i_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.2]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Type08Sp
end Minimality
