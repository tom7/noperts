module

public import Minimality.Type08S.C2K16N

@[expose] public section


/-!
# K16 / R: composition.  `K16Slice`, `Resid08FinalK16`, `resid08FinalK14_imp_K16`.
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

/-- M (QN2) leftover with the region data: `RegN2 ⟹ γ6 > 1`, and the `α1 = 1` piece only off `RegN2`. -/
def K16LeftMN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6sMN2 a a' b b' c c' d ∧ ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧
    (RegN2 W.F → 1 < γ6) ∧
    (K16mBoundary (RegN2 W.F) a b d α1 β1 β6 γ6 ∨ K14mTie a a' b b' c c' α1 β1 β6 γ6 ∨
      K6mH1Left a a' b b' c c' d α1 β1 β6 γ6 ∨ K16mH5b a a' b b' c c' d α1 β1 β6 γ6)

/-- M (QCEb) leftover with the region data: `RegT4 ⟹ α1 > 1 ∧ γ6 < 1`, and the `α1 = 1` piece only off `RegT4`. -/
def K16LeftMKb {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6sMKb a a' b b' c c' d ∧ ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧
    (RegT4 W.F → 1 < α1 ∧ γ6 < 1) ∧
    (K16mBoundary (RegT4 W.F) a b d α1 β1 β6 γ6 ∨ K14mTie a a' b b' c c' α1 β1 β6 γ6 ∨
      K16mH5b a a' b b' c c' d α1 β1 β6 γ6)

theorem k16_MN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K14LeftMN2 a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K16LeftMN2 W := by
  obtain ⟨hs, α1, β1, β6, γ6, hC, h0 | h0 | h0 | h0⟩ := h
  · rcases k16_n2_boundary W hs.1 hs.2.1 hC hs.2.2 h0 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, (k16_reg_coords W hC).1, Or.inl h1⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, (k16_reg_coords W hC).1, Or.inr (Or.inl h0)⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, (k16_reg_coords W hC).1, Or.inr (Or.inr (Or.inl h0))⟩
  · obtain ⟨hdet, hc', hb', ha', hα1', hβ1', h1, hβ6', hγ6', h3⟩ := hC
    have hC' : K6mCoords a a' b b' c c' d α1 β1 β6 γ6 := ⟨hdet, hc', hb', ha', hα1', hβ1', h1, hβ6', hγ6', h3⟩
    rcases k16_h5_step2 hC' hs.2.2
        (fun hβ1 => k16_n2_rel W hs.1 hs.2.1 hs.2.2.1 hdet hc' ha' hα1' hβ1 hγ6' h3) h0 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC', (k16_reg_coords W hC').1, Or.inr (Or.inr (Or.inr h1))⟩

theorem k16_MKb {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K14LeftMKb a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K16LeftMKb W := by
  obtain ⟨hs, α1, β1, β6, γ6, hC, h0 | h0 | h0⟩ := h
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, (k16_reg_coords W hC).2, Or.inl (k16_kb_boundary W hC h0)⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, (k16_reg_coords W hC).2, Or.inr (Or.inl h0)⟩
  · obtain ⟨hdet, hc', hb', ha', hα1', hβ1', h1, hβ6', hγ6', h3⟩ := hC
    have hC' : K6mCoords a a' b b' c c' d α1 β1 β6 γ6 := ⟨hdet, hc', hb', ha', hα1', hβ1', h1, hβ6', hγ6', h3⟩
    rcases k16_h5_step2 hC' hs.2.2
        (fun hβ1 => k16_kb_rel W hs.1 hs.2.1 hs.2.2.1 hdet hb' hα1' hβ1) h0 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC', (k16_reg_coords W hC').2, Or.inr (Or.inr h1)⟩

/-- **The K16 leftover in one labelling.** -/
def K16Slice {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6t3LeftTT a a' b b' c c' d ∨ K17fLeftPa a a' b b' c c' d ∨ K6t3LeftPc a a' b b' c c' d ∨
  K17fLeftTa14 a a' b b' c c' d ∨ K17fLeftTc' a a' b b' c c' d ∨
  K16LeftMN2 W ∨ K6sDN2one a a' b b' c c' d ∨ K16LeftMKb W

theorem k16_slice_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K14Slice W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K16Slice W := by
  rcases h with h | h | h | h | h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · rcases k16_MN2 W h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · rcases k16_MKb W h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))

def K16ResidP (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ W : Norm08w a a' b b' c c' d, ResP W.F d ∧ K16Slice W

def K16ResidP6 (a a' b b' c c' d : ℝ³) : Prop :=
  K16ResidP a a' b b' c c' d ∨ K16ResidP b b' a a' c c' d ∨ K16ResidP a a' c c' b b' d ∨
  K16ResidP c c' a a' b b' d ∨ K16ResidP b b' c c' a a' d ∨ K16ResidP c c' b b' a a' d

/-- **`Resid08FinalK16`**: `Resid08FinalK14` with the M `α1 = 1` boundary piece cut to `¬ reg`
(N2: closed under `RegN2`; Kb: empty under `RegT4`). -/
def Resid08FinalK16 (a a' b b' c c' d : ℝ³) : Prop :=
  (PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ K16ResidP6 a a' b b' c c' d ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

theorem k16_residP_step {p p' q q' r r' d : ℝ³} (h : K14ResidP p p' q q' r r' d) :
    HasLexCell (V8 p p' q q' r r' d) ∨ K16ResidP p p' q q' r r' d := by
  obtain ⟨W, hR, hs⟩ := h
  rcases k16_slice_step W hs with h | h
  · exact Or.inl h
  · exact Or.inr ⟨W, hR, h⟩

theorem resid08FinalK14_imp_K16 {a a' b b' c c' d : ℝ³}
    (h : Resid08FinalK14 a a' b b' c c' d) : Resid08FinalK16 a a' b b' c c' d := by
  obtain ⟨hpl, h6, hno⟩ := h
  have e := type08_set_perm a a' b b' c c' d
  refine ⟨hpl, ?_, hno⟩
  rcases h6 with h | h | h | h | h | h
  · rcases k16_residP_step h with h | h
    · exact (hno h).elim
    · exact Or.inl h
  · rcases k16_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.1]; exact h)).elim
    · exact Or.inr (Or.inl h)
  · rcases k16_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k16_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k16_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k16_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.2]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Type08Sp
end Minimality
