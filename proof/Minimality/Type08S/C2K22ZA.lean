module

public import Minimality.Type08S.C2K22A1
public import Minimality.Type08S.C2K22C1A

@[expose] public section


/-!
# K22 / Z: composition.  M boundary at β1 = 1 Rupert (`k22a1_*`); Pc C1 at β1 = γ4 = 1 Rupert (`k22c1_close`).
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
open C2

def K22LeftPc (a a' b b' c c' d : ℝ³) : Prop :=
  K6t3LeftPc a a' b b' c c' d ∧
    (K22C1Left a a' b b' c c' d ∨
     (0 < ⟪a - d, a - c'⟫ ∧ ⟪c - d, c - a'⟫ = 0 ∧ ⟪b' - c, d - b⟫ = 0) ∨
     (⟪a - d, a - c'⟫ < 0 ∧ ⟪c - b', d - b⟫ = 0 ∧ ⟪c - b', c - d⟫ = 0))

def K22LeftMN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6sMN2 a a' b b' c c' d ∧ ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧
    (RegN2 W.F → 1 < γ6) ∧
    (K22mBoundary (RegN2 W.F) a a' b c c' d α1 β1 β6 γ6 ∨ K14mTie a a' b b' c c' α1 β1 β6 γ6 ∨
      K17B2H1Left a a' b b' c c' d α1 β1 β6 γ6 ∨ K20mH5c a a' b b' c c' d α1 β1 β6 γ6)

def K22LeftMKb {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6sMKb a a' b b' c c' d ∧ ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧
    (RegT4 W.F → 1 < α1 ∧ γ6 < 1) ∧
    (K22mBoundary (RegT4 W.F) a a' b c c' d α1 β1 β6 γ6 ∨ K14mTie a a' b b' c c' α1 β1 β6 γ6 ∨
      K20mH5c a a' b b' c c' d α1 β1 β6 γ6)

theorem k22z_Pc {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : K19LeftPc a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K22LeftPc a a' b b' c c' d := by
  obtain ⟨hP, h1 | h1 | h1⟩ := h
  · rcases k22c1_close W hP h1 with h2 | h2 | h2
    · exact Or.inl h2
    · exact (hNR h2).elim
    · exact Or.inr ⟨hP, Or.inl h2⟩
  · exact Or.inr ⟨hP, Or.inr (Or.inl h1)⟩
  · exact Or.inr ⟨hP, Or.inr (Or.inr h1)⟩

theorem k22z_MN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : K21LeftMN2 W) : K22LeftMN2 W := by
  obtain ⟨hs, α1, β1, β6, γ6, hC, hreg, h0 | h0 | h0 | h0⟩ := h
  · rcases k22a1_boundary_cut (fun hb => hNR (k22a1_n2 W hs hC hb)) h0 with h1 | h1
    · exact h1.elim
    · exact ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inl h1⟩
  · exact ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inl h0)⟩
  · exact ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inr (Or.inl h0))⟩
  · exact ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inr (Or.inr h0))⟩

theorem k22z_MKb {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : K21LeftMKb W) : K22LeftMKb W := by
  obtain ⟨hs, α1, β1, β6, γ6, hC, hreg, h0 | h0 | h0⟩ := h
  · rcases k22a1_boundary_cut (fun hb => hNR (k22a1_kb W hs hC hb)) h0 with h1 | h1
    · exact h1.elim
    · exact ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inl h1⟩
  · exact ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inl h0)⟩
  · exact ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inr h0)⟩

def K22Slice {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6t3LeftTT a a' b b' c c' d ∨ K22LeftPc a a' b b' c c' d ∨ K17hTcZ1 a a' b b' c c' d ∨
  K22LeftMN2 W ∨ K22LeftMKb W

theorem k22_slice_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : K21Slice W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K22Slice W := by
  rcases h with h | h | h | h | h
  · exact Or.inr (Or.inl h)
  · rcases k22z_Pc W hNR h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (k22z_MN2 W hNR h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (k22z_MKb W hNR h)))))

def K22ResidP (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ W : Norm08w a a' b b' c c' d, ResP W.F d ∧ K22Slice W

def K22ResidP6 (a a' b b' c c' d : ℝ³) : Prop :=
  K22ResidP a a' b b' c c' d ∨ K22ResidP b b' a a' c c' d ∨ K22ResidP a a' c c' b b' d ∨
  K22ResidP c c' a a' b b' d ∨ K22ResidP b b' c c' a a' d ∨ K22ResidP c c' b b' a a' d

/-- **`Resid08FinalK22`**: the M boundary at β1 = 1 and Pc C1 at β1 = γ4 = 1 are Rupert. -/
def Resid08FinalK22 (a a' b b' c c' d : ℝ³) : Prop :=
  (PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ K22ResidP6 a a' b b' c c' d ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

theorem k22_residP_step {p p' q q' r r' d : ℝ³}
    (hNR : ¬ IsRupert (V8 p p' q q' r r' d)) (h : K21ResidP p p' q q' r r' d) :
    HasLexCell (V8 p p' q q' r r' d) ∨ K22ResidP p p' q q' r r' d := by
  obtain ⟨W, hR, hs⟩ := h
  rcases k22_slice_step W hNR hs with h | h
  · exact Or.inl h
  · exact Or.inr ⟨W, hR, h⟩

theorem resid08FinalK21_imp_K22 {a a' b b' c c' d : ℝ³}
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : Resid08FinalK21 a a' b b' c c' d) :
    Resid08FinalK22 a a' b b' c c' d := by
  obtain ⟨hpl, h6, hno⟩ := h
  have e := type08_set_perm a a' b b' c c' d
  refine ⟨hpl, ?_, hno⟩
  rcases h6 with h | h | h | h | h | h
  · rcases k22_residP_step hNR h with h | h
    · exact (hno h).elim
    · exact Or.inl h
  · rcases k22_residP_step (fun hR => hNR (by rw [V8, ← e.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.1]; exact h)).elim
    · exact Or.inr (Or.inl h)
  · rcases k22_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k22_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k22_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k22_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.2]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.2]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Type08Sp
end Minimality
