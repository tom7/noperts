module

public import Minimality.Type08S.C2K41ZA
public import Minimality.Type08S.C2K42B0
public import Minimality.Type08S.C2K42C0
public import Minimality.Type08S.C2K42M0

/-!
# K42 / Z: M stratum, σ = β1 tie, R1 rule with ori = 0: cells `k28b2s_R1M0` (M > 0), `k28b2s_R1B0` (M = 0, dep > 0),
`k28b2s_R1C0` (M = 0, dep ≤ 0) (specpos/C2/K28B2S/lean). Left of R1: M = 0 ∧ ori < 0 ∧ dep = 0.
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

/-- What is left of the σ = β1 tie: R2 without a cell, or R1 at M = 0 ∧ ori < 0 ∧ dep = 0. -/
def K42SigRest (a a' b b' c c' d : ℝ³) (α1 β1 β6 γ6 : ℝ) : Prop :=
  0 ≤ k33Mpp a b c d ∧
  ((k33Lam a b c d β1 γ6 < 0 ∧
      ¬ (k28bqOriCBA α1 β1 β6 γ6 ⟪b' - a, c - a'⟫ ⟪c' - a, c - a'⟫ < 0 ∧
        0 < k28bqOriBCA α1 β1 β6 γ6 ⟪b' - a, c - a'⟫ ⟪c' - a, c - a'⟫) ∧
      ¬ (0 < k28bqOriCBA α1 β1 β6 γ6 ⟪b' - a, c - a'⟫ ⟪c' - a, c - a'⟫ ∧
        0 < k28bqOriBCA α1 β1 β6 γ6 ⟪b' - a, c - a'⟫ ⟪c' - a, c - a'⟫)) ∨
    (0 ≤ k33Lam a b c d β1 γ6 ∧ k33Mpp a b c d = 0 ∧
      k28b2rOri α1 β1 β6 γ6 ⟪a - d, a - d⟫ ⟪a - d, b - d⟫ ⟪b - d, b - d⟫ ⟪b - d, c - d⟫ ⟪c - d, c - d⟫ < 0 ∧
      k41Dep a b c d α1 β1 β6 = 0))

theorem k42_sig {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hβ : 1 < β1) (hσ : β6 + γ6 = β1) (hL : ⟪a - c', a - d⟫ = 0)
    (h : K41SigRest a a' b b' c c' d α1 β1 β6 γ6) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K42SigRest a a' b b' c c' d α1 β1 β6 γ6 := by
  obtain ⟨hm, hl | ⟨hl, ho | ⟨hm0, ho, hd⟩⟩⟩ := h
  · exact Or.inr ⟨hm, Or.inl hl⟩
  · have e : ⟪b - d, c - d⟫ * ⟪a - d, a - d⟫ = ⟪a - d, a - d⟫ * ⟪b - d, c - d⟫ := mul_comm _ _
    have hΛ : 0 ≤ (β1 - 1) * (⟪b - d, c - d⟫ * ⟪a - d, a - d⟫ - ⟪a - d, b - d⟫ ^ 2) +
        (γ6 - 1) * (⟪c - d, c - d⟫ - ⟪b - d, c - d⟫) * ⟪a - d, a - d⟫ := by
      have := hl; unfold k33Lam k33Mpp at this; rw [e]; linarith
    rcases lt_or_eq_of_le hm with hmp | hm0
    · have hMp : 0 < ⟪b - d, c - d⟫ * ⟪a - d, a - d⟫ - ⟪a - d, b - d⟫ ^ 2 := by
        have := hmp; unfold k33Mpp at this; rw [e]; linarith
      exact Or.inl (k28b2s_R1M0 hC hM hrel hβ hσ hL hMp hΛ ho)
    · have hM0 : ⟪b - d, c - d⟫ * ⟪a - d, a - d⟫ - ⟪a - d, b - d⟫ ^ 2 = 0 := by
        have := hm0; unfold k33Mpp at this; rw [e]; linarith
      rcases lt_or_ge 0 (k41Dep a b c d α1 β1 β6) with hd | hd
      · exact Or.inl (k28b2s_R1B0 hC hM hrel hβ hσ hL hM0 hΛ hd ho)
      · exact Or.inl (k28b2s_R1C0 hC hM hrel hβ hσ hL hM0 hΛ hd ho)
  · exact Or.inr ⟨hm, Or.inr ⟨hl, hm0, ho, hd⟩⟩

def K42mBoundary (a a' b b' c c' d : ℝ³) (α1 β1 β6 γ6 : ℝ) : Prop :=
  1 < β1 ∧ β6 + γ6 = β1 ∧ ⟪a - c', a - d⟫ = 0 ∧ K42SigRest a a' b b' c c' d α1 β1 β6 γ6

theorem k42_boundary {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : 1 < β1 → K16Rel a b c d α1 β1) (h : K41mBoundary a a' b b' c c' d α1 β1 β6 γ6) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K42mBoundary a a' b b' c c' d α1 β1 β6 γ6 := by
  obtain ⟨hβ1, hσ, hL, h⟩ := h
  rcases k42_sig hC hM (hrel hβ1) hβ1 hσ hL h with h1 | h1
  · exact Or.inl h1
  · exact Or.inr ⟨hβ1, hσ, hL, h1⟩

def K42LeftMN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6sMN2 a a' b b' c c' d ∧ ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧
    (RegN2 W.F → 1 < γ6) ∧
    (K42mBoundary a a' b b' c c' d α1 β1 β6 γ6 ∨
      (K6mH1Left a a' b b' c c' d α1 β1 β6 γ6 ∧ K17b2L2Left a a' b b' c c' d α1 β1 β6 γ6 ∧
        K33L2Corner a a' b b' c c' d α1 β1))

/-- The Kb side: only the σ = β1 rest. -/
def K42LeftMKb {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6sMKb a a' b b' c c' d ∧ ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧
    (RegT4 W.F → 1 < α1 ∧ γ6 < 1) ∧ K42mBoundary a a' b b' c c' d α1 β1 β6 γ6

theorem k42z_MN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K41LeftMN2 W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K42LeftMN2 W := by
  obtain ⟨hs, α1, β1, β6, γ6, hC, hreg, h0 | hL⟩ := h
  · have hrel : 1 < β1 → K16Rel a b c d α1 β1 := fun hβ1 => by
      obtain ⟨hdet, hc', hb', ha', hα1', -, -, -, hγ6', h3⟩ := hC
      exact k16_n2_rel W hs.1 hs.2.1 hs.2.2.1 hdet hc' ha' hα1' hβ1 hγ6' h3
    rcases k42_boundary hC hs.2.2 hrel h0 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inl h1⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr hL⟩

theorem k42z_MKb {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K41LeftMKb W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K42LeftMKb W := by
  obtain ⟨hs, α1, β1, β6, γ6, hC, hreg, h0⟩ := h
  have hrel : 1 < β1 → K16Rel a b c d α1 β1 := fun hβ1 => by
    obtain ⟨hdet, hc', hb', ha', hα1', -⟩ := hC
    exact k16_kb_rel W hs.1 hs.2.1 hs.2.2.1 hdet hb' hα1' hβ1
  rcases k42_boundary hC hs.2.2 hrel h0 with h1 | h1
  · exact Or.inl h1
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, h1⟩

def K42Slice {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K42LeftMN2 W ∨ K42LeftMKb W

theorem k42_slice_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : K41Slice W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K42Slice W := by
  rcases h with h | h
  · rcases k42z_MN2 W h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · rcases k42z_MKb W h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inr h1)

def K42ResidP (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ W : Norm08w a a' b b' c c' d, ResP W.F d ∧ K42Slice W

def K42ResidP6 (a a' b b' c c' d : ℝ³) : Prop :=
  K42ResidP a a' b b' c c' d ∨ K42ResidP b b' a a' c c' d ∨ K42ResidP a a' c c' b b' d ∨
  K42ResidP c c' a a' b b' d ∨ K42ResidP b b' c c' a a' d ∨ K42ResidP c c' b b' a a' d

/-- **`Resid08FinalK42`**: as K41 with the R1 ori = 0 tie closed. -/
def Resid08FinalK42 (a a' b b' c c' d : ℝ³) : Prop :=
  (PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ K42ResidP6 a a' b b' c c' d ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

theorem k42_residP_step {p p' q q' r r' d : ℝ³}
    (hNR : ¬ IsRupert (V8 p p' q q' r r' d)) (h : K41ResidP p p' q q' r r' d) :
    HasLexCell (V8 p p' q q' r r' d) ∨ K42ResidP p p' q q' r r' d := by
  obtain ⟨W, hR, hs⟩ := h
  rcases k42_slice_step W hNR hs with h | h
  · exact Or.inl h
  · exact Or.inr ⟨W, hR, h⟩

theorem resid08FinalK41_imp_K42 {a a' b b' c c' d : ℝ³}
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : Resid08FinalK41 a a' b b' c c' d) :
    Resid08FinalK42 a a' b b' c c' d := by
  obtain ⟨hpl, h6, hno⟩ := h
  have e := type08_set_perm a a' b b' c c' d
  refine ⟨hpl, ?_, hno⟩
  rcases h6 with h | h | h | h | h | h
  · rcases k42_residP_step hNR h with h | h
    · exact (hno h).elim
    · exact Or.inl h
  · rcases k42_residP_step (fun hR => hNR (by rw [V8, ← e.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.1]; exact h)).elim
    · exact Or.inr (Or.inl h)
  · rcases k42_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k42_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k42_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k42_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.2]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.2]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Type08Sp
end Minimality
