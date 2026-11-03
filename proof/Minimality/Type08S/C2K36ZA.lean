module

public import Minimality.Type08S.C2K35ZA

/-!
# K36 / Z: M stratum, the Kb side. Every N2-side reduction of the boundary and H5 pieces (K29–K35) uses only
`K6mCoords`, `K6sM` and `K16Rel`; on the Kb side `K16Rel` comes from `k16_kb_rel`. So `K27LeftMKb` reduces to the
same open pieces as the N2 side (σ = β1 rest, β6 = 1 Lz = Lw = 0, γ6 = 1, H5 at S = 0); the Kb side has no H1/L2 pieces.
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

/-- What is left of the Kb side: the same open boundary and H5 pieces as the N2 side. -/
def K36LeftMKb {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6sMKb a a' b b' c c' d ∧ ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧
    (RegT4 W.F → 1 < α1 ∧ γ6 < 1) ∧
    (K34mBoundary a a' b b' c c' d α1 β1 β6 γ6 ∨
      (K20mH5c a a' b b' c c' d α1 β1 β6 γ6 ∧ ⟪c' - a, b' - a⟫ = 0))

theorem k36_kb {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K27LeftMKb W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K36LeftMKb W := by
  obtain ⟨hs, α1, β1, β6, γ6, hC, hreg, hb | h5⟩ := h
  · have hrel : 1 < β1 → K16Rel a b c d α1 β1 := fun hβ1 => by
      obtain ⟨hdet, hc', hb', ha', hα1', -⟩ := hC
      exact k16_kb_rel W hs.1 hs.2.1 hs.2.2.1 hdet hb' hα1' hβ1
    rcases hb with ⟨hβ1, hσ⟩ | ⟨hβ1, hσ, hα1, hb6 | hg⟩
    · rcases lt_trichotomy ⟪a - c', a - d⟫ 0 with hl | hl | hl
      · exact Or.inl (k24b2_lt hC hs.2.2 (hrel hβ1) hβ1 hσ hl)
      · rcases k33_sig hC hs.2.2 (hrel hβ1) hβ1 hσ hl with h1 | h1
        · exact Or.inl h1
        · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inl (Or.inl ⟨hβ1, hσ, hl, h1⟩)⟩
      · exact Or.inl (k24b2_ge W hC hs.2.2 (hrel hβ1) hβ1 hσ hl)
    · subst hb6
      have hr := hrel hβ1
      rcases lt_or_ge ⟪c' - a', b' - c⟫ 0 with hLp | hLp
      · exact Or.inl (k28b4_A hC hs.2.2 hr hα1 hβ1 hσ hLp)
      rcases k30_b4 hC hs.2.2 hr hα1 hβ1 hσ hLp with h1 | h1
      · exact Or.inl h1
      rcases k31_b4 hC hs.2.2 hr hα1 hβ1 hσ h1 with h2 | h2
      · exact Or.inl h2
      rcases k34_b4 hC hs.2.2 hr hα1 hβ1 hσ (k33_b4 hC hs.2.2 hr hα1 hβ1 hσ h2) with h3 | h3
      · exact Or.inl h3
      · exact Or.inr ⟨hs, α1, β1, 1, γ6, hC, hreg, Or.inl (Or.inr ⟨hβ1, hσ, hα1, Or.inl ⟨rfl, h3⟩⟩)⟩
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inl (Or.inr ⟨hβ1, hσ, hα1, Or.inr hg⟩)⟩
  · have hβ1 : 1 < β1 := by
      obtain ⟨⟨⟨⟨⟨-, hβ, -, -, -⟩, -⟩, -, -⟩, -, -⟩, -, -⟩ := h5
      exact hβ
    have hr : K16Rel a b c d α1 β1 := by
      obtain ⟨hdet, hc', hb', ha', hα1', -⟩ := hC
      exact k16_kb_rel W hs.1 hs.2.1 hs.2.2.1 hdet hb' hα1' hβ1
    rcases k29_h5 hC hs.2.2 hr h5 with h1 | ⟨hS, hT⟩ | hS
    · exact Or.inl h1
    · exact Or.inl (k28h5a0_A' hC hs.2.2 hr h5 hS hT)
    · rcases lt_or_eq_of_le hS with hS | hS
      · exact Or.inl (k35_h5B hC hs.2.2 hr h5 hS)
      · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr ⟨h5, hS⟩⟩

def K36Slice {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K35LeftMN2 W ∨ K36LeftMKb W

theorem k36_slice_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : K35Slice W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K36Slice W := by
  rcases h with h | h
  · exact Or.inr (Or.inl h)
  · rcases k36_kb W h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inr h1)

def K36ResidP (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ W : Norm08w a a' b b' c c' d, ResP W.F d ∧ K36Slice W

def K36ResidP6 (a a' b b' c c' d : ℝ³) : Prop :=
  K36ResidP a a' b b' c c' d ∨ K36ResidP b b' a a' c c' d ∨ K36ResidP a a' c c' b b' d ∨
  K36ResidP c c' a a' b b' d ∨ K36ResidP b b' c c' a a' d ∨ K36ResidP c c' b b' a a' d

/-- **`Resid08FinalK36`**: as K35 with the Kb side reduced to the N2 side's open pieces. -/
def Resid08FinalK36 (a a' b b' c c' d : ℝ³) : Prop :=
  (PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ K36ResidP6 a a' b b' c c' d ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

theorem k36_residP_step {p p' q q' r r' d : ℝ³}
    (hNR : ¬ IsRupert (V8 p p' q q' r r' d)) (h : K35ResidP p p' q q' r r' d) :
    HasLexCell (V8 p p' q q' r r' d) ∨ K36ResidP p p' q q' r r' d := by
  obtain ⟨W, hR, hs⟩ := h
  rcases k36_slice_step W hNR hs with h | h
  · exact Or.inl h
  · exact Or.inr ⟨W, hR, h⟩

theorem resid08FinalK35_imp_K36 {a a' b b' c c' d : ℝ³}
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : Resid08FinalK35 a a' b b' c c' d) :
    Resid08FinalK36 a a' b b' c c' d := by
  obtain ⟨hpl, h6, hno⟩ := h
  have e := type08_set_perm a a' b b' c c' d
  refine ⟨hpl, ?_, hno⟩
  rcases h6 with h | h | h | h | h | h
  · rcases k36_residP_step hNR h with h | h
    · exact (hno h).elim
    · exact Or.inl h
  · rcases k36_residP_step (fun hR => hNR (by rw [V8, ← e.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.1]; exact h)).elim
    · exact Or.inr (Or.inl h)
  · rcases k36_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k36_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k36_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k36_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.2]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.2]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Type08Sp
end Minimality
