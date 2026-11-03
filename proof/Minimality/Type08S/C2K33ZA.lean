module

public import Minimality.Type08S.C2K32ZA
public import Minimality.Type08S.C2K33MB
public import Minimality.Type08S.C2K33QC
public import Minimality.Type08S.C2K33QD
public import Minimality.Type08S.C2K33RB
public import Minimality.Type08S.C2K33EE

/-!
# K33 / Z: M stratum (N2 side): σ = β1 on the tie L = 0 (cells M < 0, R2.5, R2.4, R1+.5; specpos/C2/K24B2M,
K28B2Q, K28B2R), and four corners shown empty (K32EMP: `k32e_b4q`, `k32e_b4E`, `k32e_l2x4`, `k32e_l2x3`).
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

/-- `M · pp` for the σ = β1 tie (frame p = a-d, q = b-d, r = c-d). -/
noncomputable def k33Mpp (a b c d : ℝ³) : ℝ := ⟪a - d, a - d⟫ * ⟪b - d, c - d⟫ - ⟪a - d, b - d⟫ ^ 2

/-- `Λ · pp`. -/
noncomputable def k33Lam (a b c d : ℝ³) (β1 γ6 : ℝ) : ℝ :=
  (β1 - 1) * k33Mpp a b c d + (γ6 - 1) * (⟪c - d, c - d⟫ - ⟪b - d, c - d⟫) * ⟪a - d, a - d⟫

/-- What K33 leaves of the σ = β1 tie (M ≥ 0): R2 without a cell (the exotic X1/X2 and ori ties), R1 at M = 0
(cells A, B, C) or at R1+.6 (`ori ≥ 0`). -/
def K33SigRest (a a' b b' c c' d : ℝ³) (α1 β1 β6 γ6 : ℝ) : Prop :=
  0 ≤ k33Mpp a b c d ∧
  ((k33Lam a b c d β1 γ6 < 0 ∧
      ¬ (k28bqOriCBA α1 β1 β6 γ6 ⟪b' - a, c - a'⟫ ⟪c' - a, c - a'⟫ < 0 ∧
        0 < k28bqOriBCA α1 β1 β6 γ6 ⟪b' - a, c - a'⟫ ⟪c' - a, c - a'⟫) ∧
      ¬ (0 < k28bqOriCBA α1 β1 β6 γ6 ⟪b' - a, c - a'⟫ ⟪c' - a, c - a'⟫ ∧
        0 < k28bqOriBCA α1 β1 β6 γ6 ⟪b' - a, c - a'⟫ ⟪c' - a, c - a'⟫)) ∨
    (0 ≤ k33Lam a b c d β1 γ6 ∧
      ¬ (0 < k33Mpp a b c d ∧ k28b2rOri α1 β1 β6 γ6 ⟪a - d, a - d⟫ ⟪a - d, b - d⟫ ⟪b - d, b - d⟫
        ⟪b - d, c - d⟫ ⟪c - d, c - d⟫ < 0)))

theorem k33_sig {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hβ : 1 < β1) (hσ : β6 + γ6 = β1) (hL : ⟪a - c', a - d⟫ = 0) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K33SigRest a a' b b' c c' d α1 β1 β6 γ6 := by
  rcases lt_or_ge (k33Mpp a b c d) 0 with hm | hm
  · left
    exact k24b2m_tieM hC hM hrel hβ hσ hL (by unfold k33Mpp at hm; linarith)
  rcases lt_or_ge (k33Lam a b c d β1 γ6) 0 with hl | hl
  · by_cases h1 : k28bqOriCBA α1 β1 β6 γ6 ⟪b' - a, c - a'⟫ ⟪c' - a, c - a'⟫ < 0 ∧
        0 < k28bqOriBCA α1 β1 β6 γ6 ⟪b' - a, c - a'⟫ ⟪c' - a, c - a'⟫
    · exact Or.inl (k28b2_R25 hC hM hrel hβ hσ hL hm hl h1.1 h1.2)
    by_cases h2 : 0 < k28bqOriCBA α1 β1 β6 γ6 ⟪b' - a, c - a'⟫ ⟪c' - a, c - a'⟫ ∧
        0 < k28bqOriBCA α1 β1 β6 γ6 ⟪b' - a, c - a'⟫ ⟪c' - a, c - a'⟫
    · exact Or.inl (k28b2_R24 hC hM hrel hβ hσ hL hm hl h2.1 h2.2)
    exact Or.inr ⟨hm, Or.inl ⟨hl, h1, h2⟩⟩
  · by_cases h3 : 0 < k33Mpp a b c d ∧ k28b2rOri α1 β1 β6 γ6 ⟪a - d, a - d⟫ ⟪a - d, b - d⟫ ⟪b - d, b - d⟫
        ⟪b - d, c - d⟫ ⟪c - d, c - d⟫ < 0
    · left
      have e : ⟪b - d, c - d⟫ * ⟪a - d, a - d⟫ = ⟪a - d, a - d⟫ * ⟪b - d, c - d⟫ := mul_comm _ _
      refine k28b2_R15 hC hM hrel hβ hσ hL ?_ ?_ h3.2
      · have := h3.1; unfold k33Mpp at this; linarith
      · have := hl; unfold k33Lam k33Mpp at this; rw [e]; linarith
    · exact Or.inr ⟨hm, Or.inr ⟨hl, h3⟩⟩

/-- What K33 leaves of the β6 = 1 ties (`K31B4Rest` minus the two empty corners). -/
def K33B4Rest (a a' b b' c c' d : ℝ³) : Prop :=
  0 ≤ ⟪c' - a', b' - c⟫ ∧
  ((⟪c' - a', b' - c⟫ = 0 ∧ ⟪c' - c, k28b4c_u0 a a' c c' d⟫ = 0) ∨
    (⟪c' - c, k28b4c_u0 a a' c c' d⟫ = 0 ∧
      (⟪c' - a', b' - a⟫ = 0 ∨ ⟪a - c', k28b4c_u0 a a' c c' d⟫ = 0)))

theorem k33_b4 {a a' b b' c c' d : ℝ³} {α1 β1 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 1 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hα : 1 < α1) (hβ : 1 < β1) (hσ : β1 < 1 + γ6)
    (h : K31B4Rest a a' b b' c c' d γ6) : K33B4Rest a a' b b' c c' d := by
  obtain ⟨hLp, ⟨hp, hq | hz | ⟨hz, hE⟩⟩ | h2⟩ := h
  · exact absurd hq (not_le.mpr (k32e_b4q hC hM hrel hα hβ hσ hp))
  · exact ⟨hLp, Or.inl ⟨hp, hz⟩⟩
  · exact absurd hE (not_le.mpr (k32e_b4E hC hM hrel hα hβ hσ hp hz))
  · exact ⟨hLp, Or.inr h2⟩

/-- What K33 leaves of the L2 corners (`K29L2Corner` minus the corners shown empty). -/
def K33L2Corner (a a' b b' c c' d : ℝ³) (α1 β1 : ℝ) : Prop :=
  (⟪a - c', a - b'⟫ = 0 ∧ ⟪c' - a, b' - c⟫ = 0) ∨
  (⟪c' - a, b' - c⟫ = 0 ∧ ⟪a - a', k28l2aU0 a b c d α1 β1⟫ = 0 ∧ ⟪c, k28l2aU0 a b c d α1 β1⟫ ≤ ⟪a', k28l2aU0 a b c d α1 β1⟫) ∨
  (⟪a - a', k28l2aU0 a b c d α1 β1⟫ = 0 ∧ ⟪a', k28l2aU0 a b c d α1 β1⟫ = ⟪c, k28l2aU0 a b c d α1 β1⟫)

theorem k33_l2 {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hH1 : K6mH1Left a a' b b' c c' d α1 β1 β6 γ6)
    (hL2 : K17b2L2Left a a' b b' c c' d α1 β1 β6 γ6) (hne : ⟪c - a', a - b'⟫ ≠ 0)
    (h : K29L2Corner a a' b b' c c' d α1 β1) : K33L2Corner a a' b b' c c' d α1 β1 := by
  have hpos : 0 < ⟪c - a', a - b'⟫ ∧ ⟪a - c', a - b'⟫ ≤ 0 := by
    rcases hH1.2.2 with h0 | h0
    · exact (hne h0).elim
    · exact h0
  have hX4 : 0 ≤ ⟪c' - a, b' - c⟫ := hL2.1.2.1
  rcases h with ⟨h4, hl | h3 | ⟨hl, hz⟩⟩ | ⟨h3, hl, hz⟩ | h5
  · exact absurd hl (not_lt.mpr (k32e_l2x4 hC hM hrel hH1 hL2 hpos.2 h4))
  · exact Or.inl ⟨h3, h4⟩
  · exact Or.inr (Or.inl ⟨h4, hl, hz⟩)
  · obtain ⟨-, hle, hlt⟩ := k32e_l2x3 hC hM hrel hH1 hL2 h3 hpos.1
    rcases lt_or_eq_of_le hX4 with h4 | h4
    · exact absurd (hlt h4) (not_lt.mpr hz)
    · exact Or.inl ⟨h3, h4.symm⟩
  · exact Or.inr (Or.inr h5)

/-- K32's boundary with the σ = β1 tie and β6 = 1 corners reduced. -/
def K33mBoundary (a a' b b' c c' d : ℝ³) (α1 β1 β6 γ6 : ℝ) : Prop :=
  (1 < β1 ∧ β6 + γ6 = β1 ∧ ⟪a - c', a - d⟫ = 0 ∧ K33SigRest a a' b b' c c' d α1 β1 β6 γ6) ∨
    (1 < β1 ∧ β1 < β6 + γ6 ∧ 1 < α1 ∧ ((β6 = 1 ∧ K33B4Rest a a' b b' c c' d) ∨ γ6 = 1))

def K33LeftMN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6sMN2 a a' b b' c c' d ∧ ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧
    (RegN2 W.F → 1 < γ6) ∧
    (K33mBoundary a a' b b' c c' d α1 β1 β6 γ6 ∨
      (K6mH1Left a a' b b' c c' d α1 β1 β6 γ6 ∧ K17b2L2Left a a' b b' c c' d α1 β1 β6 γ6 ∧
        K33L2Corner a a' b b' c c' d α1 β1) ∨
      (K20mH5c a a' b b' c c' d α1 β1 β6 γ6 ∧ ⟪c' - a, b' - a⟫ ≤ 0))

theorem k33z_MN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K32LeftMN2 W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K33LeftMN2 W := by
  obtain ⟨hs, α1, β1, β6, γ6, hC, hreg, h0 | ⟨hH1, hL, hc⟩ | h5⟩ := h
  · rcases h0 with ⟨hβ1, hσ, hl⟩ | ⟨hβ1, hσ, hα1, ⟨hb, ht⟩ | hg⟩
    · have hrel : K16Rel a b c d α1 β1 := by
        obtain ⟨hdet, hc', hb', ha', hα1', -, -, -, hγ6', h3⟩ := hC
        exact k16_n2_rel W hs.1 hs.2.1 hs.2.2.1 hdet hc' ha' hα1' hβ1 hγ6' h3
      rcases k33_sig hC hs.2.2 hrel hβ1 hσ hl with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inl (Or.inl ⟨hβ1, hσ, hl, h1⟩)⟩
    · have hrel : K16Rel a b c d α1 β1 := by
        obtain ⟨hdet, hc', hb', ha', hα1', -, -, -, hγ6', h3⟩ := hC
        exact k16_n2_rel W hs.1 hs.2.1 hs.2.2.1 hdet hc' ha' hα1' hβ1 hγ6' h3
      subst hb
      exact Or.inr ⟨hs, α1, β1, 1, γ6, hC, hreg,
        Or.inl (Or.inr ⟨hβ1, hσ, hα1, Or.inl ⟨rfl, k33_b4 hC hs.2.2 hrel hα1 hβ1 hσ ht⟩⟩)⟩
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inl (Or.inr ⟨hβ1, hσ, hα1, Or.inr hg⟩)⟩
  · have hrel : K16Rel a b c d α1 β1 := by
      obtain ⟨hdet, hc', hb', ha', hα1', -, -, -, hγ6', h3⟩ := hC
      exact k16_n2_rel W hs.1 hs.2.1 hs.2.2.1 hdet hc' ha' hα1' hH1.1.2.1 hγ6' h3
    by_cases ht : ⟪c - a', a - b'⟫ = 0
    · exact Or.inl (k28_h1tie W hs hC hH1 ht)
    exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg,
      Or.inr (Or.inl ⟨hH1, hL, k33_l2 hC hs.2.2 hrel hH1 hL ht hc⟩)⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inr h5)⟩

def K33Slice {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K33LeftMN2 W ∨ K27LeftMKb W

theorem k33_slice_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : K32Slice W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K33Slice W := by
  rcases h with h | h
  · rcases k33z_MN2 W h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h)

def K33ResidP (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ W : Norm08w a a' b b' c c' d, ResP W.F d ∧ K33Slice W

def K33ResidP6 (a a' b b' c c' d : ℝ³) : Prop :=
  K33ResidP a a' b b' c c' d ∨ K33ResidP b b' a a' c c' d ∨ K33ResidP a a' c c' b b' d ∨
  K33ResidP c c' a a' b b' d ∨ K33ResidP b b' c c' a a' d ∨ K33ResidP c c' b b' a a' d

/-- **`Resid08FinalK33`**: as K32 with σ = β1 tie cells, four empty corners and the R2/R1 cells. -/
def Resid08FinalK33 (a a' b b' c c' d : ℝ³) : Prop :=
  (PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ K33ResidP6 a a' b b' c c' d ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

theorem k33_residP_step {p p' q q' r r' d : ℝ³}
    (hNR : ¬ IsRupert (V8 p p' q q' r r' d)) (h : K32ResidP p p' q q' r r' d) :
    HasLexCell (V8 p p' q q' r r' d) ∨ K33ResidP p p' q q' r r' d := by
  obtain ⟨W, hR, hs⟩ := h
  rcases k33_slice_step W hNR hs with h | h
  · exact Or.inl h
  · exact Or.inr ⟨W, hR, h⟩

theorem resid08FinalK32_imp_K33 {a a' b b' c c' d : ℝ³}
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : Resid08FinalK32 a a' b b' c c' d) :
    Resid08FinalK33 a a' b b' c c' d := by
  obtain ⟨hpl, h6, hno⟩ := h
  have e := type08_set_perm a a' b b' c c' d
  refine ⟨hpl, ?_, hno⟩
  rcases h6 with h | h | h | h | h | h
  · rcases k33_residP_step hNR h with h | h
    · exact (hno h).elim
    · exact Or.inl h
  · rcases k33_residP_step (fun hR => hNR (by rw [V8, ← e.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.1]; exact h)).elim
    · exact Or.inr (Or.inl h)
  · rcases k33_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k33_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k33_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k33_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.2]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.2]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Type08Sp
end Minimality
