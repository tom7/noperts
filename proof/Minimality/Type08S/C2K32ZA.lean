module

public import Minimality.Type08S.C2K31ZA
public import Minimality.Type08S.C2K32GB
public import Minimality.Type08S.C2K32LB

/-!
# K32 / Z: M stratum (N2 side), σ = β1 off the tie (specpos/C2/K24B2G, K24B2L).
`β6 + γ6 = β1 > 1` with `L = ⟪a-c', a-d⟫ > 0` → `k24b2_ge`, `L < 0` → `k24b2_lt`. Left: the tie `L = 0`.
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

/-- K31's boundary with σ = β1 closed off the tie `⟪a-c', a-d⟫ = 0`. -/
def K32mBoundary (a a' b b' c c' d : ℝ³) (α1 β1 β6 γ6 : ℝ) : Prop :=
  (1 < β1 ∧ β6 + γ6 = β1 ∧ ⟪a - c', a - d⟫ = 0) ∨
    (1 < β1 ∧ β1 < β6 + γ6 ∧ 1 < α1 ∧ ((β6 = 1 ∧ K31B4Rest a a' b b' c c' d γ6) ∨ γ6 = 1))

def K32LeftMN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6sMN2 a a' b b' c c' d ∧ ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧
    (RegN2 W.F → 1 < γ6) ∧
    (K32mBoundary a a' b b' c c' d α1 β1 β6 γ6 ∨
      (K6mH1Left a a' b b' c c' d α1 β1 β6 γ6 ∧ K17b2L2Left a a' b b' c c' d α1 β1 β6 γ6 ∧
        K29L2Corner a a' b b' c c' d α1 β1) ∨
      (K20mH5c a a' b b' c c' d α1 β1 β6 γ6 ∧ ⟪c' - a, b' - a⟫ ≤ 0))

theorem k32z_MN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K31LeftMN2 W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K32LeftMN2 W := by
  obtain ⟨hs, α1, β1, β6, γ6, hC, hreg, h0 | hL | h5⟩ := h
  · rcases h0 with ⟨hβ1, hσ⟩ | h0
    · have hrel : K16Rel a b c d α1 β1 := by
        obtain ⟨hdet, hc', hb', ha', hα1', -, -, -, hγ6', h3⟩ := hC
        exact k16_n2_rel W hs.1 hs.2.1 hs.2.2.1 hdet hc' ha' hα1' hβ1 hγ6' h3
      rcases lt_trichotomy ⟪a - c', a - d⟫ 0 with hl | hl | hl
      · exact Or.inl (k24b2_lt hC hs.2.2 hrel hβ1 hσ hl)
      · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inl (Or.inl ⟨hβ1, hσ, hl⟩)⟩
      · exact Or.inl (k24b2_ge W hC hs.2.2 hrel hβ1 hσ hl)
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inl (Or.inr h0)⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inl hL)⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inr h5)⟩

def K32Slice {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K32LeftMN2 W ∨ K27LeftMKb W

theorem k32_slice_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : K31Slice W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K32Slice W := by
  rcases h with h | h
  · rcases k32z_MN2 W h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h)

def K32ResidP (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ W : Norm08w a a' b b' c c' d, ResP W.F d ∧ K32Slice W

def K32ResidP6 (a a' b b' c c' d : ℝ³) : Prop :=
  K32ResidP a a' b b' c c' d ∨ K32ResidP b b' a a' c c' d ∨ K32ResidP a a' c c' b b' d ∨
  K32ResidP c c' a a' b b' d ∨ K32ResidP b b' c c' a a' d ∨ K32ResidP c c' b b' a a' d

/-- **`Resid08FinalK32`**: as K31 with σ = β1 closed off the tie L = ⟪a-c',a-d⟫ = 0. -/
def Resid08FinalK32 (a a' b b' c c' d : ℝ³) : Prop :=
  (PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ K32ResidP6 a a' b b' c c' d ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

theorem k32_residP_step {p p' q q' r r' d : ℝ³}
    (hNR : ¬ IsRupert (V8 p p' q q' r r' d)) (h : K31ResidP p p' q q' r r' d) :
    HasLexCell (V8 p p' q q' r r' d) ∨ K32ResidP p p' q q' r r' d := by
  obtain ⟨W, hR, hs⟩ := h
  rcases k32_slice_step W hNR hs with h | h
  · exact Or.inl h
  · exact Or.inr ⟨W, hR, h⟩

theorem resid08FinalK31_imp_K32 {a a' b b' c c' d : ℝ³}
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : Resid08FinalK31 a a' b b' c c' d) :
    Resid08FinalK32 a a' b b' c c' d := by
  obtain ⟨hpl, h6, hno⟩ := h
  have e := type08_set_perm a a' b b' c c' d
  refine ⟨hpl, ?_, hno⟩
  rcases h6 with h | h | h | h | h | h
  · rcases k32_residP_step hNR h with h | h
    · exact (hno h).elim
    · exact Or.inl h
  · rcases k32_residP_step (fun hR => hNR (by rw [V8, ← e.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.1]; exact h)).elim
    · exact Or.inr (Or.inl h)
  · rcases k32_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k32_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k32_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k32_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.2]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.2]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Type08Sp
end Minimality
