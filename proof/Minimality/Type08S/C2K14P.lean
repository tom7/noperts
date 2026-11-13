module

public import Minimality.Type08S.C2K17F0A

@[expose] public section

/-!
# K14 / P: composition.  `K14Slice`, `Resid08FinalK14`, `resid08FinalK12_imp_K14` (and the M-only `resid08FinalK13_imp_K14M`).
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
open C2

/-- H5 with the single-literal rule `⟪a - d, a - c'⟫ > 0` removed (`k14_H5_hasLexCell`). -/
def K14mH5 (a c' d : ℝ³) (α1 β1 β6 γ6 : ℝ) : Prop := K6mH5 α1 β1 β6 γ6 ∧ ⟪a - d, a - c'⟫ ≤ 0

theorem k14_h5_step {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (h : K6mH5 α1 β1 β6 γ6) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K14mH5 a c' d α1 β1 β6 γ6 := by
  obtain ⟨hdet, hc', hb', ha', hα1', hβ1', h1, hβ6', hγ6', h3⟩ := hC
  obtain ⟨hα1, hβ1, hσ, -, -⟩ := id h
  by_cases hl : 0 < ⟪a - d, a - c'⟫
  · exact Or.inl (k14_H5_hasLexCell hdet hc' hb' ha' hα1 hβ1 hβ6' hγ6' hσ hM hl)
  · exact Or.inr ⟨h, not_lt.1 hl⟩

/-- M (QN2) leftover with ties and `α1 = 1` boundary shrunk. -/
def K14LeftMN2 (a a' b b' c c' d : ℝ³) : Prop :=
  K6sMN2 a a' b b' c c' d ∧ ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧
    (K14mBoundary a b d α1 β1 β6 γ6 ∨ K14mTie a a' b b' c c' α1 β1 β6 γ6 ∨
      K6mH1Left a a' b b' c c' d α1 β1 β6 γ6 ∨ K14mH5 a c' d α1 β1 β6 γ6)

/-- M (QCEb) leftover with ties and `α1 = 1` boundary shrunk. -/
def K14LeftMKb (a a' b b' c c' d : ℝ³) : Prop :=
  K6sMKb a a' b b' c c' d ∧ ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧
    (K14mBoundary a b d α1 β1 β6 γ6 ∨ K14mTie a a' b b' c c' α1 β1 β6 γ6 ∨ K14mH5 a c' d α1 β1 β6 γ6)

theorem k14_MN2 {a a' b b' c c' d : ℝ³} (h : K6sMLeftN2' a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K14LeftMN2 a a' b b' c c' d := by
  obtain ⟨hs, α1, β1, β6, γ6, hC, h0 | h0 | h0 | h0⟩ := h
  · rcases k14_boundary_step hC hs.2.2 h0 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, Or.inl h1⟩
  · rcases k14_tie_step hC hs.2.2 h0 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, Or.inr (Or.inl h1)⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, Or.inr (Or.inr (Or.inl h0))⟩
  · rcases k14_h5_step hC hs.2.2 h0 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, Or.inr (Or.inr (Or.inr h1))⟩

theorem k14_MKb {a a' b b' c c' d : ℝ³} (h : K6sMLeftKb a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K14LeftMKb a a' b b' c c' d := by
  obtain ⟨hs, α1, β1, β6, γ6, hC, h0 | h0 | h0⟩ := h
  · rcases k14_boundary_step hC hs.2.2 h0 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, Or.inl h1⟩
  · rcases k14_tie_step hC hs.2.2 h0 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, Or.inr (Or.inl h1)⟩
  · rcases k14_h5_step hC hs.2.2 h0 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, Or.inr (Or.inr h1)⟩

/-- **The K14 leftover in one labelling.** -/
def K14Slice {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6t3LeftTT a a' b b' c c' d ∨ K17fLeftPa a a' b b' c c' d ∨ K6t3LeftPc a a' b b' c c' d ∨
  K17fLeftTa14 a a' b b' c c' d ∨ K17fLeftTc' a a' b b' c c' d ∨
  K14LeftMN2 a a' b b' c c' d ∨ K6sDN2one a a' b b' c c' d ∨ K14LeftMKb a a' b b' c c' d

theorem k14_slice_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K7Slice W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K14Slice W := by
  rcases h with h | h | h | h | h | h | h | h | h
  · rcases k6t3_TT W h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases k17f_Pa W h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k6t3_Pc W h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k17f_Ta14 W (Or.inl h) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k17f_Ta14 W (Or.inr h) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k17f_Tc' W h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · rcases k6mh1_left h with h | h
    · exact Or.inl h
    · rcases k14_MN2 h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · rcases k14_MKb h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))

def K14ResidP (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ W : Norm08w a a' b b' c c' d, ResP W.F d ∧ K14Slice W

def K14ResidP6 (a a' b b' c c' d : ℝ³) : Prop :=
  K14ResidP a a' b b' c c' d ∨ K14ResidP b b' a a' c c' d ∨ K14ResidP a a' c c' b b' d ∨
  K14ResidP c c' a a' b b' d ∨ K14ResidP b b' c c' a a' d ∨ K14ResidP c c' b b' a a' d

/-- **`Resid08FinalK14`**: `Resid08FinalK12` with the M ties (H2/H4 up to `ζ(c',a') = 0`), the M `α1 = 1` boundary
(up to `⟪a-d,b-d⟫ ≥ 0` or `β6, γ6 ≤ 1`), Ta box C's `D_c < 0 ∧ ζ_C = 0` and Pa(1)'s `α4 > 1` closed. -/
def Resid08FinalK14 (a a' b b' c c' d : ℝ³) : Prop :=
  (PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ K14ResidP6 a a' b b' c c' d ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

theorem k14_residP_step {p p' q q' r r' d : ℝ³} (h : K7ResidP p p' q q' r r' d) :
    HasLexCell (V8 p p' q q' r r' d) ∨ K14ResidP p p' q q' r r' d := by
  obtain ⟨W, hR, hs⟩ := h
  rcases k14_slice_step W hs with h | h
  · exact Or.inl h
  · exact Or.inr ⟨W, hR, h⟩

theorem resid08FinalK12_imp_K14 {a a' b b' c c' d : ℝ³}
    (h : Resid08FinalK12 a a' b b' c c' d) : Resid08FinalK14 a a' b b' c c' d := by
  obtain ⟨hpl, h6, hno⟩ := h
  have e := type08_set_perm a a' b b' c c' d
  refine ⟨hpl, ?_, hno⟩
  rcases h6 with h | h | h | h | h | h
  · rcases k14_residP_step h with h | h
    · exact (hno h).elim
    · exact Or.inl h
  · rcases k14_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.1]; exact h)).elim
    · exact Or.inr (Or.inl h)
  · rcases k14_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k14_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k14_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k14_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.2]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

/-! ### The M-only step from `Resid08FinalK13` (Pa and Ta pieces need `hT'`/`hfar`, dropped at K13) -/

end Type08Sp
end Minimality
