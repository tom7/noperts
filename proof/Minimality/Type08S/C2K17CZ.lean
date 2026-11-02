module

public import Minimality.Type08S.C2K17CP

@[expose] public section


/-!
# K17C / Z: composition.  The `β1 = 1` piece of the M boundary cut to `K17cLeft`.
`K17mBoundary`, `K17LeftMN2`, `K17LeftMKb`, `K17CSlice`, `Resid08FinalK17C`, `resid08FinalK16_imp_K17C`.
-/
set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
open C2

/-- `K16mBoundary` with its `β1 = 1` disjunct cut to the K17C leftover. -/
def K17mBoundary (reg : Prop) (a a' b c c' d : ℝ³) (α1 β1 β6 γ6 : ℝ) : Prop :=
  (β1 = 1 ∧ K17cLeft a a' b c c' d α1 β6 γ6) ∨ (1 < β1 ∧ β6 + γ6 = β1) ∨
    (1 < β1 ∧ β1 < β6 + γ6 ∧ α1 = 1 ∧ ¬ reg ∧ (0 ≤ ⟪a - d, b - d⟫ ∨ (β6 ≤ 1 ∧ γ6 ≤ 1))) ∨
    (1 < β1 ∧ β1 < β6 + γ6 ∧ 1 < α1 ∧ (β6 = 1 ∨ γ6 = 1))

def K17LeftMN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6sMN2 a a' b b' c c' d ∧ ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧
    (RegN2 W.F → 1 < γ6) ∧
    (K17mBoundary (RegN2 W.F) a a' b c c' d α1 β1 β6 γ6 ∨ K14mTie a a' b b' c c' α1 β1 β6 γ6 ∨
      K6mH1Left a a' b b' c c' d α1 β1 β6 γ6 ∨ K16mH5b a a' b b' c c' d α1 β1 β6 γ6)

def K17LeftMKb {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6sMKb a a' b b' c c' d ∧ ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧
    (RegT4 W.F → 1 < α1 ∧ γ6 < 1) ∧
    (K17mBoundary (RegT4 W.F) a a' b c c' d α1 β1 β6 γ6 ∨ K14mTie a a' b b' c c' α1 β1 β6 γ6 ∨
      K16mH5b a a' b b' c c' d α1 β1 β6 γ6)

theorem k17_boundary_cut {reg : Prop} {a a' b c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ} {X : Prop}
    (hX : β1 = 1 → X ∨ K17cLeft a a' b c c' d α1 β6 γ6)
    (h : K16mBoundary reg a b d α1 β1 β6 γ6) : X ∨ K17mBoundary reg a a' b c c' d α1 β1 β6 γ6 := by
  rcases h with h | h | h
  · rcases hX h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl ⟨h, h1⟩)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem k17_MN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K16LeftMN2 W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K17LeftMN2 W := by
  obtain ⟨hs, α1, β1, β6, γ6, hC, hreg, h0 | h0 | h0 | h0⟩ := h
  · rcases k17_boundary_cut (fun hb => k17c_boundary_n2 W hs hC hb) h0 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inl h1⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inl h0)⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inr (Or.inl h0))⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inr (Or.inr h0))⟩

theorem k17_MKb {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K16LeftMKb W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K17LeftMKb W := by
  obtain ⟨hs, α1, β1, β6, γ6, hC, hreg, h0 | h0 | h0⟩ := h
  · rcases k17_boundary_cut (fun hb => k17c_boundary_kb W hs hC hb) h0 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inl h1⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inl h0)⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inr h0)⟩

def K17CSlice {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6t3LeftTT a a' b b' c c' d ∨ K14LeftPa a a' b b' c c' d ∨ K6t3LeftPc a a' b b' c c' d ∨
  K14LeftTa' a a' b b' c c' d ∨ K6tLeftTc' a a' b b' c c' d ∨
  K17LeftMN2 W ∨ K6sDN2one a a' b b' c c' d ∨ K17LeftMKb W

theorem k17c_slice_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K16Slice W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K17CSlice W := by
  rcases h with h | h | h | h | h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · rcases k17_MN2 W h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · rcases k17_MKb W h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))

def K17CResidP (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ W : Norm08w a a' b b' c c' d, ResP W.F d ∧ K17CSlice W

def K17CResidP6 (a a' b b' c c' d : ℝ³) : Prop :=
  K17CResidP a a' b b' c c' d ∨ K17CResidP b b' a a' c c' d ∨ K17CResidP a a' c c' b b' d ∨
  K17CResidP c c' a a' b b' d ∨ K17CResidP b b' c c' a a' d ∨ K17CResidP c c' b b' a a' d

/-- **`Resid08FinalK17C`**: `Resid08FinalK16` with the M boundary's `β1 = 1` piece cut to `K17cLeft`. -/
def Resid08FinalK17C (a a' b b' c c' d : ℝ³) : Prop :=
  (PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ K17CResidP6 a a' b b' c c' d ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

theorem k17c_residP_step {p p' q q' r r' d : ℝ³} (h : K16ResidP p p' q q' r r' d) :
    HasLexCell (V8 p p' q q' r r' d) ∨ K17CResidP p p' q q' r r' d := by
  obtain ⟨W, hR, hs⟩ := h
  rcases k17c_slice_step W hs with h | h
  · exact Or.inl h
  · exact Or.inr ⟨W, hR, h⟩

theorem resid08FinalK16_imp_K17C {a a' b b' c c' d : ℝ³}
    (h : Resid08FinalK16 a a' b b' c c' d) : Resid08FinalK17C a a' b b' c c' d := by
  obtain ⟨hpl, h6, hno⟩ := h
  have e := type08_set_perm a a' b b' c c' d
  refine ⟨hpl, ?_, hno⟩
  rcases h6 with h | h | h | h | h | h
  · rcases k17c_residP_step h with h | h
    · exact (hno h).elim
    · exact Or.inl h
  · rcases k17c_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.1]; exact h)).elim
    · exact Or.inr (Or.inl h)
  · rcases k17c_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k17c_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k17c_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k17c_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.2]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Type08Sp
end Minimality
