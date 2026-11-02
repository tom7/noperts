module

public import Minimality.Type08S.C2K20ZA
public import Minimality.Type08S.C2K20HI
public import Minimality.Type08S.C2K21C

@[expose] public section


/-!
# K21 / Z: composition.  Pa and Ta closed (K21), Tc's A41 corner Rupert (K21), H5 cut by rules 3, 6, 7, 8 (K20H5).
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
open C2

def K21LeftMN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6sMN2 a a' b b' c c' d ∧ ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧
    (RegN2 W.F → 1 < γ6) ∧
    (K17mBoundary (RegN2 W.F) a a' b c c' d α1 β1 β6 γ6 ∨ K14mTie a a' b b' c c' α1 β1 β6 γ6 ∨
      K17B2H1Left a a' b b' c c' d α1 β1 β6 γ6 ∨ K20mH5c a a' b b' c c' d α1 β1 β6 γ6)

def K21LeftMKb {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6sMKb a a' b b' c c' d ∧ ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧
    (RegT4 W.F → 1 < α1 ∧ γ6 < 1) ∧
    (K17mBoundary (RegT4 W.F) a a' b c c' d α1 β1 β6 γ6 ∨ K14mTie a a' b b' c c' α1 β1 β6 γ6 ∨
      K20mH5c a a' b b' c c' d α1 β1 β6 γ6)

theorem k21z_MN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K17B2LeftMN2 W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K21LeftMN2 W := by
  obtain ⟨hs, α1, β1, β6, γ6, hC, hreg, h0 | h0 | h0 | h0⟩ := h
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inl h0⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inl h0)⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inr (Or.inl h0))⟩
  · rcases k20h_h5 hC hs.2.2 h0 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inr (Or.inr h1))⟩

theorem k21z_MKb {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K17LeftMKb W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K21LeftMKb W := by
  obtain ⟨hs, α1, β1, β6, γ6, hC, hreg, h0 | h0 | h0⟩ := h
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inl h0⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inl h0)⟩
  · rcases k20h_h5 hC hs.2.2 h0 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inr h1)⟩

def K21Slice {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6t3LeftTT a a' b b' c c' d ∨ K19LeftPc a a' b b' c c' d ∨ K17hTcZ1 a a' b b' c c' d ∨
  K21LeftMN2 W ∨ K21LeftMKb W

theorem k21_slice_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : K20Slice W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K21Slice W := by
  rcases h with h | h | h | h | h | h | h
  · exact Or.inr (Or.inl h)
  · rcases k21_pa_close W h with h1 | h1
    · exact Or.inl h1
    · exact (hNR h1).elim
  · exact Or.inr (Or.inr (Or.inl h))
  · rcases k21_ta_close W h with h1 | h1
    · exact Or.inl h1
    · exact (hNR h1).elim
  · rcases h with h | h
    · exact (hNR (k21_tca41 W h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k21z_MN2 W h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
  · rcases k21z_MKb W h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h1))))

def K21ResidP (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ W : Norm08w a a' b b' c c' d, ResP W.F d ∧ K21Slice W

def K21ResidP6 (a a' b b' c c' d : ℝ³) : Prop :=
  K21ResidP a a' b b' c c' d ∨ K21ResidP b b' a a' c c' d ∨ K21ResidP a a' c c' b b' d ∨
  K21ResidP c c' a a' b b' d ∨ K21ResidP b b' c c' a a' d ∨ K21ResidP c c' b b' a a' d

/-- **`Resid08FinalK21`**: Pa, Ta and Tc's A41 corner closed; H5 cut to `K20mH5c`. -/
def Resid08FinalK21 (a a' b b' c c' d : ℝ³) : Prop :=
  (PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ K21ResidP6 a a' b b' c c' d ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

theorem k21_residP_step {p p' q q' r r' d : ℝ³}
    (hNR : ¬ IsRupert (V8 p p' q q' r r' d)) (h : K20ResidP p p' q q' r r' d) :
    HasLexCell (V8 p p' q q' r r' d) ∨ K21ResidP p p' q q' r r' d := by
  obtain ⟨W, hR, hs⟩ := h
  rcases k21_slice_step W hNR hs with h | h
  · exact Or.inl h
  · exact Or.inr ⟨W, hR, h⟩

theorem resid08FinalK20_imp_K21 {a a' b b' c c' d : ℝ³}
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : Resid08FinalK20 a a' b b' c c' d) :
    Resid08FinalK21 a a' b b' c c' d := by
  obtain ⟨hpl, h6, hno⟩ := h
  have e := type08_set_perm a a' b b' c c' d
  refine ⟨hpl, ?_, hno⟩
  rcases h6 with h | h | h | h | h | h
  · rcases k21_residP_step hNR h with h | h
    · exact (hno h).elim
    · exact Or.inl h
  · rcases k21_residP_step (fun hR => hNR (by rw [V8, ← e.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.1]; exact h)).elim
    · exact Or.inr (Or.inl h)
  · rcases k21_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k21_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k21_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k21_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.2]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.2]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Type08Sp
end Minimality
