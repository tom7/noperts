module

public import Minimality.Type08S.C2K27ZA
public import Minimality.Type08S.C2K24H1LB
public import Minimality.Type08S.C2K24H1BB
public import Minimality.Type08S.C2K24H1CB
public import Minimality.Type08S.C2K24H1C0B
public import Minimality.Type08S.C2K24H1B0B
public import Minimality.Type08S.C2K24H1DC

/-!
# K28 / Z: M stratum, the H1 tie ⟪c - a', a - b'⟫ = 0 closed (specpos/C2/K24H1*, specs K24H1c, K24H1d).
Case tree: L1 = ⟪a-c',b'-c⟫ ≥ 0 → `k24h1_ge`; else N2 = ⟪a-b',a'-c'⟫ > 0 → B, < 0 → C; N2 = 0: L2 = ⟪a-c',a-b'⟫ < 0 → C0,
else W = ⟪a'-c',c-b⟫ > 0 → B0, ≤ 0 → D.
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

theorem k28_h1tie {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ} (W : Norm08w a a' b b' c c' d)
    (hs : K6sMN2 a a' b b' c c' d) (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6)
    (hH1 : K6mH1Left a a' b b' c c' d α1 β1 β6 γ6) (ht : ⟪c - a', a - b'⟫ = 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  have hrel : K16Rel a b c d α1 β1 := by
    obtain ⟨hdet, hc', hb', ha', hα1', -, -, -, hγ6', h3⟩ := hC
    exact k16_n2_rel W hs.1 hs.2.1 hs.2.2.1 hdet hc' ha' hα1' hH1.1.2.1 hγ6' h3
  have hM := hs.2.2
  rcases le_or_gt 0 ⟪a - c', b' - c⟫ with hL1 | hL1
  · exact k24h1_ge W hC hM hrel hH1 ht hL1
  rcases lt_trichotomy 0 ⟪a - b', a' - c'⟫ with hN | hN | hN
  · exact k24h1_B hC hM hrel hH1 ht hN
  · rcases lt_or_ge ⟪a - c', a - b'⟫ 0 with hL2 | hL2
    · exact k24h1_C0 hC hM hrel hH1 ht hN.symm hL2
    · rcases lt_or_ge 0 ⟪a' - c', c - b⟫ with hW | hW
      · exact k24h1_B0 hC hM hrel hH1 ht hN.symm hW
      · exact k24h1_D hC hM hrel hH1 ht hN.symm hL2 hW
  · exact k24h1_C hC hM hrel hH1 ht hN

def K28LeftMN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6sMN2 a a' b b' c c' d ∧ ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧
    (RegN2 W.F → 1 < γ6) ∧
    (K27mBoundary a a' b c c' d α1 β1 β6 γ6 ∨
      (K6mH1Left a a' b b' c c' d α1 β1 β6 γ6 ∧ K17b2L2Left a a' b b' c c' d α1 β1 β6 γ6) ∨
      K20mH5c a a' b b' c c' d α1 β1 β6 γ6)

theorem k28z_MN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K27LeftMN2 W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K28LeftMN2 W := by
  obtain ⟨hs, α1, β1, β6, γ6, hC, hreg, h0 | ⟨hH1, ht | hL⟩ | h0⟩ := h
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inl h0⟩
  · exact Or.inl (k28_h1tie W hs hC hH1 ht)
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inl ⟨hH1, hL⟩)⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inr h0)⟩

def K28Slice {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K28LeftMN2 W ∨ K27LeftMKb W

theorem k28_slice_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : K27Slice W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K28Slice W := by
  rcases h with h | h
  · rcases k28z_MN2 W h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h)

def K28ResidP (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ W : Norm08w a a' b b' c c' d, ResP W.F d ∧ K28Slice W

def K28ResidP6 (a a' b b' c c' d : ℝ³) : Prop :=
  K28ResidP a a' b b' c c' d ∨ K28ResidP b b' a a' c c' d ∨ K28ResidP a a' c c' b b' d ∨
  K28ResidP c c' a a' b b' d ∨ K28ResidP b b' c c' a a' d ∨ K28ResidP c c' b b' a a' d

/-- **`Resid08FinalK28`**: as K27 with the H1 tie closed. -/
def Resid08FinalK28 (a a' b b' c c' d : ℝ³) : Prop :=
  (PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ K28ResidP6 a a' b b' c c' d ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

theorem k28_residP_step {p p' q q' r r' d : ℝ³}
    (hNR : ¬ IsRupert (V8 p p' q q' r r' d)) (h : K27ResidP p p' q q' r r' d) :
    HasLexCell (V8 p p' q q' r r' d) ∨ K28ResidP p p' q q' r r' d := by
  obtain ⟨W, hR, hs⟩ := h
  rcases k28_slice_step W hNR hs with h | h
  · exact Or.inl h
  · exact Or.inr ⟨W, hR, h⟩

theorem resid08FinalK27_imp_K28 {a a' b b' c c' d : ℝ³}
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : Resid08FinalK27 a a' b b' c c' d) :
    Resid08FinalK28 a a' b b' c c' d := by
  obtain ⟨hpl, h6, hno⟩ := h
  have e := type08_set_perm a a' b b' c c' d
  refine ⟨hpl, ?_, hno⟩
  rcases h6 with h | h | h | h | h | h
  · rcases k28_residP_step hNR h with h | h
    · exact (hno h).elim
    · exact Or.inl h
  · rcases k28_residP_step (fun hR => hNR (by rw [V8, ← e.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.1]; exact h)).elim
    · exact Or.inr (Or.inl h)
  · rcases k28_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k28_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k28_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k28_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.2]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.2]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Type08Sp
end Minimality
