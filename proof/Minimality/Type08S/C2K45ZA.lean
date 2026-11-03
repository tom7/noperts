module

public import Minimality.Type08S.C2K44ZA
public import Minimality.Type08S.C2K45B0

/-!
# K45 / Z: M stratum, σ = β1 tie, R2 at oc = ori(c′,b,a′) = 0 ≤ ob: cell `k43r2_B0` (R2.5's 5-cycle, cone
{l1, v2, Z, Z′}; the extra Gram fact κB < (α1+β1−1)⟪a−d,b−d⟫ follows from Rel, K6sM, γ6 < 1). Closes R2.
Left of the σ = β1 tie: only the R1 tie lit1 > 0 ∧ β1 = α1 + 1 at M = 0 ∧ ori < 0 ∧ dep = 0.
-/
@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
open C2

/-- What is left of the σ = β1 tie: the R1 tie lit1 > 0 ∧ β1 = α1 + 1 at M = 0 ∧ ori < 0 ∧ dep = 0. -/
def K45SigRest (a a' b b' c c' d : ℝ³) (α1 β1 β6 γ6 : ℝ) : Prop :=
  0 ≤ k33Lam a b c d β1 γ6 ∧ k33Mpp a b c d = 0 ∧
    k28b2rOri α1 β1 β6 γ6 ⟪a - d, a - d⟫ ⟪a - d, b - d⟫ ⟪b - d, b - d⟫ ⟪b - d, c - d⟫ ⟪c - d, c - d⟫ < 0 ∧
    k41Dep a b c d α1 β1 β6 = 0 ∧
    0 < α1 * ⟪a - a', a - d⟫ + (β1 - 1) * ⟪a - a', c - d⟫ ∧ β1 = α1 + 1

theorem k45_sig {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hβ : 1 < β1) (hσ : β6 + γ6 = β1) (hL : ⟪a - c', a - d⟫ = 0)
    (h : K44SigRest a a' b b' c c' d α1 β1 β6 γ6) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K45SigRest a a' b b' c c' d α1 β1 β6 γ6 := by
  obtain ⟨hm, ⟨hl, hc, hb⟩ | hr⟩ := h
  · exact Or.inl (k43r2_B0 hC hM hrel hβ hσ hL hm hl hc hb)
  · exact Or.inr hr

def K45mBoundary (a a' b b' c c' d : ℝ³) (α1 β1 β6 γ6 : ℝ) : Prop :=
  1 < β1 ∧ β6 + γ6 = β1 ∧ ⟪a - c', a - d⟫ = 0 ∧ K45SigRest a a' b b' c c' d α1 β1 β6 γ6

theorem k45_boundary {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : 1 < β1 → K16Rel a b c d α1 β1) (h : K44mBoundary a a' b b' c c' d α1 β1 β6 γ6) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K45mBoundary a a' b b' c c' d α1 β1 β6 γ6 := by
  obtain ⟨hβ1, hσ, hL, h⟩ := h
  rcases k45_sig hC hM (hrel hβ1) hβ1 hσ hL h with h1 | h1
  · exact Or.inl h1
  · exact Or.inr ⟨hβ1, hσ, hL, h1⟩

def K45LeftMN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6sMN2 a a' b b' c c' d ∧ ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧
    (RegN2 W.F → 1 < γ6) ∧
    (K45mBoundary a a' b b' c c' d α1 β1 β6 γ6 ∨
      (K6mH1Left a a' b b' c c' d α1 β1 β6 γ6 ∧ K17b2L2Left a a' b b' c c' d α1 β1 β6 γ6 ∧
        K33L2Corner a a' b b' c c' d α1 β1))

/-- The Kb side: only the σ = β1 rest. -/
def K45LeftMKb {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6sMKb a a' b b' c c' d ∧ ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧
    (RegT4 W.F → 1 < α1 ∧ γ6 < 1) ∧ K45mBoundary a a' b b' c c' d α1 β1 β6 γ6

theorem k45z_MN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K44LeftMN2 W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K45LeftMN2 W := by
  obtain ⟨hs, α1, β1, β6, γ6, hC, hreg, h0 | hL⟩ := h
  · have hrel : 1 < β1 → K16Rel a b c d α1 β1 := fun hβ1 => by
      obtain ⟨hdet, hc', hb', ha', hα1', -, -, -, hγ6', h3⟩ := hC
      exact k16_n2_rel W hs.1 hs.2.1 hs.2.2.1 hdet hc' ha' hα1' hβ1 hγ6' h3
    rcases k45_boundary hC hs.2.2 hrel h0 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inl h1⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr hL⟩

theorem k45z_MKb {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K44LeftMKb W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K45LeftMKb W := by
  obtain ⟨hs, α1, β1, β6, γ6, hC, hreg, h0⟩ := h
  have hrel : 1 < β1 → K16Rel a b c d α1 β1 := fun hβ1 => by
    obtain ⟨hdet, hc', hb', ha', hα1', -⟩ := hC
    exact k16_kb_rel W hs.1 hs.2.1 hs.2.2.1 hdet hb' hα1' hβ1
  rcases k45_boundary hC hs.2.2 hrel h0 with h1 | h1
  · exact Or.inl h1
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, h1⟩

def K45Slice {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K45LeftMN2 W ∨ K45LeftMKb W

theorem k45_slice_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : K44Slice W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K45Slice W := by
  rcases h with h | h
  · rcases k45z_MN2 W h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · rcases k45z_MKb W h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inr h1)

def K45ResidP (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ W : Norm08w a a' b b' c c' d, ResP W.F d ∧ K45Slice W

def K45ResidP6 (a a' b b' c c' d : ℝ³) : Prop :=
  K45ResidP a a' b b' c c' d ∨ K45ResidP b b' a a' c c' d ∨ K45ResidP a a' c c' b b' d ∨
  K45ResidP c c' a a' b b' d ∨ K45ResidP b b' c c' a a' d ∨ K45ResidP c c' b b' a a' d

/-- **`Resid08FinalK45`**: as K44 with R2 closed (only the R1 tie lit1 > 0 ∧ β1 = α1 + 1 is left of σ = β1). -/
def Resid08FinalK45 (a a' b b' c c' d : ℝ³) : Prop :=
  (PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ K45ResidP6 a a' b b' c c' d ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

theorem k45_residP_step {p p' q q' r r' d : ℝ³}
    (hNR : ¬ IsRupert (V8 p p' q q' r r' d)) (h : K44ResidP p p' q q' r r' d) :
    HasLexCell (V8 p p' q q' r r' d) ∨ K45ResidP p p' q q' r r' d := by
  obtain ⟨W, hR, hs⟩ := h
  rcases k45_slice_step W hNR hs with h | h
  · exact Or.inl h
  · exact Or.inr ⟨W, hR, h⟩

theorem resid08FinalK44_imp_K45 {a a' b b' c c' d : ℝ³}
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : Resid08FinalK44 a a' b b' c c' d) :
    Resid08FinalK45 a a' b b' c c' d := by
  obtain ⟨hpl, h6, hno⟩ := h
  have e := type08_set_perm a a' b b' c c' d
  refine ⟨hpl, ?_, hno⟩
  rcases h6 with h | h | h | h | h | h
  · rcases k45_residP_step hNR h with h | h
    · exact (hno h).elim
    · exact Or.inl h
  · rcases k45_residP_step (fun hR => hNR (by rw [V8, ← e.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.1]; exact h)).elim
    · exact Or.inr (Or.inl h)
  · rcases k45_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k45_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k45_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k45_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.2]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.2]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Type08Sp
end Minimality
