module

public import Minimality.Type08S.C2K40ZA
public import Minimality.Type08S.C2K41H5
public import Minimality.Type08S.C2K41RA
public import Minimality.Type08S.C2K41RB
public import Minimality.Type08S.C2K41RC

/-!
# K41 / Z: M stratum: the H5 residue at S = 0 (cell `k39h5_S0`, specpos/C2/K39H5; closes H5 on both sides) and
the σ = β1 tie at R1, M = 0: cells A (ori > 0), B (ori < 0, dep > 0), C (ori < 0, dep < 0) (`k28b2s_R1A/B/C`,
specpos/C2/K28B2S/lean). Left of the σ = β1 tie: R2 without a cell, R1 with ori = 0, and M = 0 ∧ ori < 0 ∧ dep = 0.
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

/-- `dep(a − b)` at the R1 view on M = 0 (the literal of cells B, C). -/
noncomputable def k41Dep (a b c d : ℝ³) (α1 β1 β6 : ℝ) : ℝ :=
  ⟪a - b, -(((β6 * (⟪b - d, b - d⟫ - ⟪b - d, c - d⟫) + (α1 - 1) * α1 * ⟪a - d, a - d⟫ / β1) /
    (α1 * ⟪a - d, a - d⟫)) • (a - d) + (b - d))⟫

/-- What is left of the σ = β1 tie. -/
def K41SigRest (a a' b b' c c' d : ℝ³) (α1 β1 β6 γ6 : ℝ) : Prop :=
  0 ≤ k33Mpp a b c d ∧
  ((k33Lam a b c d β1 γ6 < 0 ∧
      ¬ (k28bqOriCBA α1 β1 β6 γ6 ⟪b' - a, c - a'⟫ ⟪c' - a, c - a'⟫ < 0 ∧
        0 < k28bqOriBCA α1 β1 β6 γ6 ⟪b' - a, c - a'⟫ ⟪c' - a, c - a'⟫) ∧
      ¬ (0 < k28bqOriCBA α1 β1 β6 γ6 ⟪b' - a, c - a'⟫ ⟪c' - a, c - a'⟫ ∧
        0 < k28bqOriBCA α1 β1 β6 γ6 ⟪b' - a, c - a'⟫ ⟪c' - a, c - a'⟫)) ∨
    (0 ≤ k33Lam a b c d β1 γ6 ∧
      (k28b2rOri α1 β1 β6 γ6 ⟪a - d, a - d⟫ ⟪a - d, b - d⟫ ⟪b - d, b - d⟫ ⟪b - d, c - d⟫ ⟪c - d, c - d⟫ = 0 ∨
        (k33Mpp a b c d = 0 ∧
          k28b2rOri α1 β1 β6 γ6 ⟪a - d, a - d⟫ ⟪a - d, b - d⟫ ⟪b - d, b - d⟫ ⟪b - d, c - d⟫ ⟪c - d, c - d⟫ < 0 ∧
          k41Dep a b c d α1 β1 β6 = 0))))

theorem k41_sig {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hβ : 1 < β1) (hσ : β6 + γ6 = β1) (hL : ⟪a - c', a - d⟫ = 0)
    (h : K40SigRest a a' b b' c c' d α1 β1 β6 γ6) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K41SigRest a a' b b' c c' d α1 β1 β6 γ6 := by
  obtain ⟨hm, hl | ⟨hl, hm0 | ho⟩⟩ := h
  · exact Or.inr ⟨hm, Or.inl hl⟩
  · have e : ⟪b - d, c - d⟫ * ⟪a - d, a - d⟫ = ⟪a - d, a - d⟫ * ⟪b - d, c - d⟫ := mul_comm _ _
    have hM0 : ⟪b - d, c - d⟫ * ⟪a - d, a - d⟫ - ⟪a - d, b - d⟫ ^ 2 = 0 := by
      have := hm0; unfold k33Mpp at this; rw [e]; linarith
    have hΛ : 0 ≤ (β1 - 1) * (⟪b - d, c - d⟫ * ⟪a - d, a - d⟫ - ⟪a - d, b - d⟫ ^ 2) +
        (γ6 - 1) * (⟪c - d, c - d⟫ - ⟪b - d, c - d⟫) * ⟪a - d, a - d⟫ := by
      have := hl; unfold k33Lam k33Mpp at this; rw [e]; linarith
    rcases lt_trichotomy (k28b2rOri α1 β1 β6 γ6 ⟪a - d, a - d⟫ ⟪a - d, b - d⟫ ⟪b - d, b - d⟫
        ⟪b - d, c - d⟫ ⟪c - d, c - d⟫) 0 with ho | ho | ho
    · rcases lt_trichotomy (k41Dep a b c d α1 β1 β6) 0 with hd | hd | hd
      · exact Or.inl (k28b2s_R1C hC hM hrel hβ hσ hL hM0 hΛ hd ho)
      · exact Or.inr ⟨hm, Or.inr ⟨hl, Or.inr ⟨hm0, ho, hd⟩⟩⟩
      · exact Or.inl (k28b2s_R1B hC hM hrel hβ hσ hL hM0 hΛ hd ho)
    · exact Or.inr ⟨hm, Or.inr ⟨hl, Or.inl ho⟩⟩
    · exact Or.inl (k28b2s_R1A hC hM hrel hβ hσ hL hM0 hΛ ho)
  · exact Or.inr ⟨hm, Or.inr ⟨hl, Or.inl ho⟩⟩

def K41mBoundary (a a' b b' c c' d : ℝ³) (α1 β1 β6 γ6 : ℝ) : Prop :=
  1 < β1 ∧ β6 + γ6 = β1 ∧ ⟪a - c', a - d⟫ = 0 ∧ K41SigRest a a' b b' c c' d α1 β1 β6 γ6

theorem k41_boundary {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : 1 < β1 → K16Rel a b c d α1 β1) (h : K40mBoundary a a' b b' c c' d α1 β1 β6 γ6) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K41mBoundary a a' b b' c c' d α1 β1 β6 γ6 := by
  obtain ⟨hβ1, hσ, hL, h⟩ := h
  rcases k41_sig hC hM (hrel hβ1) hβ1 hσ hL h with h1 | h1
  · exact Or.inl h1
  · exact Or.inr ⟨hβ1, hσ, hL, h1⟩

/-- The N2 side: the σ = β1 rest and the L2 corners (H5 is closed). -/
def K41LeftMN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6sMN2 a a' b b' c c' d ∧ ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧
    (RegN2 W.F → 1 < γ6) ∧
    (K41mBoundary a a' b b' c c' d α1 β1 β6 γ6 ∨
      (K6mH1Left a a' b b' c c' d α1 β1 β6 γ6 ∧ K17b2L2Left a a' b b' c c' d α1 β1 β6 γ6 ∧
        K33L2Corner a a' b b' c c' d α1 β1))

/-- The Kb side: only the σ = β1 rest. -/
def K41LeftMKb {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6sMKb a a' b b' c c' d ∧ ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧
    (RegT4 W.F → 1 < α1 ∧ γ6 < 1) ∧ K41mBoundary a a' b b' c c' d α1 β1 β6 γ6

theorem k41z_MN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K40LeftMN2 W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K41LeftMN2 W := by
  obtain ⟨hs, α1, β1, β6, γ6, hC, hreg, h0 | hL | ⟨h5, hS⟩⟩ := h
  · have hrel : 1 < β1 → K16Rel a b c d α1 β1 := fun hβ1 => by
      obtain ⟨hdet, hc', hb', ha', hα1', -, -, -, hγ6', h3⟩ := hC
      exact k16_n2_rel W hs.1 hs.2.1 hs.2.2.1 hdet hc' ha' hα1' hβ1 hγ6' h3
    rcases k41_boundary hC hs.2.2 hrel h0 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inl h1⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr hL⟩
  · have hβ1 : 1 < β1 := by
      obtain ⟨⟨⟨⟨⟨-, hβ, -, -, -⟩, -⟩, -, -⟩, -, -⟩, -, -⟩ := h5
      exact hβ
    have hrel : K16Rel a b c d α1 β1 := by
      obtain ⟨hdet, hc', hb', ha', hα1', -, -, -, hγ6', h3⟩ := hC
      exact k16_n2_rel W hs.1 hs.2.1 hs.2.2.1 hdet hc' ha' hα1' hβ1 hγ6' h3
    exact Or.inl (k39h5_S0 hC hs.2.2 hrel h5 hS)

theorem k41z_MKb {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K40LeftMKb W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K41LeftMKb W := by
  obtain ⟨hs, α1, β1, β6, γ6, hC, hreg, h0 | ⟨h5, hS⟩⟩ := h
  · have hrel : 1 < β1 → K16Rel a b c d α1 β1 := fun hβ1 => by
      obtain ⟨hdet, hc', hb', ha', hα1', -⟩ := hC
      exact k16_kb_rel W hs.1 hs.2.1 hs.2.2.1 hdet hb' hα1' hβ1
    rcases k41_boundary hC hs.2.2 hrel h0 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, h1⟩
  · have hβ1 : 1 < β1 := by
      obtain ⟨⟨⟨⟨⟨-, hβ, -, -, -⟩, -⟩, -, -⟩, -, -⟩, -, -⟩ := h5
      exact hβ
    have hrel : K16Rel a b c d α1 β1 := by
      obtain ⟨hdet, hc', hb', ha', hα1', -⟩ := hC
      exact k16_kb_rel W hs.1 hs.2.1 hs.2.2.1 hdet hb' hα1' hβ1
    exact Or.inl (k39h5_S0 hC hs.2.2 hrel h5 hS)

def K41Slice {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K41LeftMN2 W ∨ K41LeftMKb W

theorem k41_slice_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : K40Slice W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K41Slice W := by
  rcases h with h | h
  · rcases k41z_MN2 W h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · rcases k41z_MKb W h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inr h1)

def K41ResidP (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ W : Norm08w a a' b b' c c' d, ResP W.F d ∧ K41Slice W

def K41ResidP6 (a a' b b' c c' d : ℝ³) : Prop :=
  K41ResidP a a' b b' c c' d ∨ K41ResidP b b' a a' c c' d ∨ K41ResidP a a' c c' b b' d ∨
  K41ResidP c c' a a' b b' d ∨ K41ResidP b b' c c' a a' d ∨ K41ResidP c c' b b' a a' d

/-- **`Resid08FinalK41`**: as K40 with H5 at S = 0 and R1 at M = 0 (cells A, B, C) closed. -/
def Resid08FinalK41 (a a' b b' c c' d : ℝ³) : Prop :=
  (PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ K41ResidP6 a a' b b' c c' d ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

theorem k41_residP_step {p p' q q' r r' d : ℝ³}
    (hNR : ¬ IsRupert (V8 p p' q q' r r' d)) (h : K40ResidP p p' q q' r r' d) :
    HasLexCell (V8 p p' q q' r r' d) ∨ K41ResidP p p' q q' r r' d := by
  obtain ⟨W, hR, hs⟩ := h
  rcases k41_slice_step W hNR hs with h | h
  · exact Or.inl h
  · exact Or.inr ⟨W, hR, h⟩

theorem resid08FinalK40_imp_K41 {a a' b b' c c' d : ℝ³}
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : Resid08FinalK40 a a' b b' c c' d) :
    Resid08FinalK41 a a' b b' c c' d := by
  obtain ⟨hpl, h6, hno⟩ := h
  have e := type08_set_perm a a' b b' c c' d
  refine ⟨hpl, ?_, hno⟩
  rcases h6 with h | h | h | h | h | h
  · rcases k41_residP_step hNR h with h | h
    · exact (hno h).elim
    · exact Or.inl h
  · rcases k41_residP_step (fun hR => hNR (by rw [V8, ← e.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.1]; exact h)).elim
    · exact Or.inr (Or.inl h)
  · rcases k41_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k41_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k41_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k41_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.2]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.2]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Type08Sp
end Minimality
