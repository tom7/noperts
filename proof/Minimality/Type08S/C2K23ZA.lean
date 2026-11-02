module

public import Minimality.Type08S.C2K22ZA
public import Minimality.Type08S.C2K20TTT

@[expose] public section


/-!
# K23 / Z: composition.  TT closed by five cells up to the ties `K20Left` (K20TT).
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
open C2

def K23LeftTT (a a' b b' c c' d : ℝ³) : Prop :=
  K6t3LeftTT a a' b b' c c' d ∧ K20Left a a' b b' c c' d

theorem k23z_TT {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K6t3LeftTT a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K23LeftTT a a' b b' c c' d := by
  obtain ⟨hctx, h0⟩ := id h
  rcases k20_TT W hctx.1 hctx.2.1 h0 with h1 | h1
  · exact Or.inl h1
  · exact Or.inr ⟨h, h1⟩

def K23Slice {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K23LeftTT a a' b b' c c' d ∨ K22LeftPc a a' b b' c c' d ∨ K17hTcZ1 a a' b b' c c' d ∨
  K22LeftMN2 W ∨ K22LeftMKb W

theorem k23_slice_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : K22Slice W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K23Slice W := by
  rcases h with h | h | h | h | h
  · rcases k23z_TT W h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

def K23ResidP (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ W : Norm08w a a' b b' c c' d, ResP W.F d ∧ K23Slice W

def K23ResidP6 (a a' b b' c c' d : ℝ³) : Prop :=
  K23ResidP a a' b b' c c' d ∨ K23ResidP b b' a a' c c' d ∨ K23ResidP a a' c c' b b' d ∨
  K23ResidP c c' a a' b b' d ∨ K23ResidP b b' c c' a a' d ∨ K23ResidP c c' b b' a a' d

/-- **`Resid08FinalK23`**: TT closed up to the ties `K20Left`. -/
def Resid08FinalK23 (a a' b b' c c' d : ℝ³) : Prop :=
  (PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ K23ResidP6 a a' b b' c c' d ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

theorem k23_residP_step {p p' q q' r r' d : ℝ³}
    (hNR : ¬ IsRupert (V8 p p' q q' r r' d)) (h : K22ResidP p p' q q' r r' d) :
    HasLexCell (V8 p p' q q' r r' d) ∨ K23ResidP p p' q q' r r' d := by
  obtain ⟨W, hR, hs⟩ := h
  rcases k23_slice_step W hNR hs with h | h
  · exact Or.inl h
  · exact Or.inr ⟨W, hR, h⟩

theorem resid08FinalK22_imp_K23 {a a' b b' c c' d : ℝ³}
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : Resid08FinalK22 a a' b b' c c' d) :
    Resid08FinalK23 a a' b b' c c' d := by
  obtain ⟨hpl, h6, hno⟩ := h
  have e := type08_set_perm a a' b b' c c' d
  refine ⟨hpl, ?_, hno⟩
  rcases h6 with h | h | h | h | h | h
  · rcases k23_residP_step hNR h with h | h
    · exact (hno h).elim
    · exact Or.inl h
  · rcases k23_residP_step (fun hR => hNR (by rw [V8, ← e.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.1]; exact h)).elim
    · exact Or.inr (Or.inl h)
  · rcases k23_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k23_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k23_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k23_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.2]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.2]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Type08Sp
end Minimality
