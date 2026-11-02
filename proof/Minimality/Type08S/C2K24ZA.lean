module

public import Minimality.Type08S.C2K23ZA
public import Minimality.Type08S.C2K22C1bJ
public import Minimality.Type08S.C2K22C2ZA
public import Minimality.Type08S.C2K22C3B

/-!
# K24 / Z: composition.  Pc closed: C1 (`k22c1b_close`, one corner Rupert), C2 (`k22c2_close`), C3 (`k22c3_cell`).
-/
@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
open C2

theorem k24_pc {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K22LeftPc a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ IsRupert (V8 a a' b b' c c' d) := by
  obtain ⟨h0, h1 | h1 | h1⟩ := h
  · exact k22c1b_close W h0 h1
  · exact Or.inl (k22c2_close W h0 h1)
  · exact Or.inl (k22c3_cell W h0 h1)

def K24Slice {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K23LeftTT a a' b b' c c' d ∨ K17hTcZ1 a a' b b' c c' d ∨ K22LeftMN2 W ∨ K22LeftMKb W

theorem k24_slice_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : K23Slice W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K24Slice W := by
  rcases h with h | h | h | h | h
  · exact Or.inr (Or.inl h)
  · rcases k24_pc W h with h1 | h1
    · exact Or.inl h1
    · exact (hNR h1).elim
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

def K24ResidP (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ W : Norm08w a a' b b' c c' d, ResP W.F d ∧ K24Slice W

def K24ResidP6 (a a' b b' c c' d : ℝ³) : Prop :=
  K24ResidP a a' b b' c c' d ∨ K24ResidP b b' a a' c c' d ∨ K24ResidP a a' c c' b b' d ∨
  K24ResidP c c' a a' b b' d ∨ K24ResidP b b' c c' a a' d ∨ K24ResidP c c' b b' a a' d

/-- **`Resid08FinalK24`**: as K23 with the Pc corners closed. -/
def Resid08FinalK24 (a a' b b' c c' d : ℝ³) : Prop :=
  (PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ K24ResidP6 a a' b b' c c' d ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

theorem k24_residP_step {p p' q q' r r' d : ℝ³}
    (hNR : ¬ IsRupert (V8 p p' q q' r r' d)) (h : K23ResidP p p' q q' r r' d) :
    HasLexCell (V8 p p' q q' r r' d) ∨ K24ResidP p p' q q' r r' d := by
  obtain ⟨W, hR, hs⟩ := h
  rcases k24_slice_step W hNR hs with h | h
  · exact Or.inl h
  · exact Or.inr ⟨W, hR, h⟩

theorem resid08FinalK23_imp_K24 {a a' b b' c c' d : ℝ³}
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : Resid08FinalK23 a a' b b' c c' d) :
    Resid08FinalK24 a a' b b' c c' d := by
  obtain ⟨hpl, h6, hno⟩ := h
  have e := type08_set_perm a a' b b' c c' d
  refine ⟨hpl, ?_, hno⟩
  rcases h6 with h | h | h | h | h | h
  · rcases k24_residP_step hNR h with h | h
    · exact (hno h).elim
    · exact Or.inl h
  · rcases k24_residP_step (fun hR => hNR (by rw [V8, ← e.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.1]; exact h)).elim
    · exact Or.inr (Or.inl h)
  · rcases k24_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k24_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k24_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k24_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.2]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.2]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Type08Sp
end Minimality
