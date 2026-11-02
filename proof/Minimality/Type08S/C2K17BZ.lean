module

public import Minimality.Type08S.C2K17BA
public import Minimality.Type08S.C2K17CZ

@[expose] public section


/-!
# K17B / Z: composition.  H1-L2 of stratum M cut to `K17bL2Left`.
`K17BH1Left`, `K17BLeftMN2`, `K17BSlice`, `Resid08FinalK17B`, `resid08FinalK17C_imp_K17B`.
-/
set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
open C2

/-- `K6mH1Left` with its leaf-L2 branch cut to `K17bL2Left` (the tie branch stays). -/
def K17BH1Left (a a' b b' c c' d : ℝ³) (α1 β1 β6 γ6 : ℝ) : Prop :=
  K6mH1Left a a' b b' c c' d α1 β1 β6 γ6 ∧
    (⟪c - a', a - b'⟫ = 0 ∨ K17bL2Left a a' b b' c c' d α1 β1 β6 γ6)

theorem k17b_h1_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hs : K6sMN2 a a' b b' c c' d) {α1 β1 β6 γ6 : ℝ} (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6)
    (h : K6mH1Left a a' b b' c c' d α1 β1 β6 γ6) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K17BH1Left a a' b b' c c' d α1 β1 β6 γ6 := by
  obtain ⟨hdet, hc', hb', ha', hα1', hβ1', h1, hβ6', hγ6', h3⟩ := hC
  obtain ⟨hH, hpos, ht | hL2⟩ := id h
  · exact Or.inr ⟨h, Or.inl ht⟩
  · obtain ⟨hα1, hβ1, hσ, hβ6, hγ6⟩ := hH
    have hrel := k16_n2_rel W hs.1 hs.2.1 hs.2.2.1 hdet hc' ha' hα1' hβ1 hγ6' h3
    rcases k17b_l2 hdet hc' hb' ha' hα1 hβ1 hβ6 hγ6 hσ hs.2.2 hrel with h2 | h2
    · exact Or.inl h2
    · exact Or.inr ⟨h, Or.inr h2⟩

def K17BLeftMN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6sMN2 a a' b b' c c' d ∧ ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧
    (RegN2 W.F → 1 < γ6) ∧
    (K17mBoundary (RegN2 W.F) a a' b c c' d α1 β1 β6 γ6 ∨ K14mTie a a' b b' c c' α1 β1 β6 γ6 ∨
      K17BH1Left a a' b b' c c' d α1 β1 β6 γ6 ∨ K16mH5b a a' b b' c c' d α1 β1 β6 γ6)

theorem k17b_MN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K17LeftMN2 W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K17BLeftMN2 W := by
  obtain ⟨hs, α1, β1, β6, γ6, hC, hreg, h0 | h0 | h0 | h0⟩ := h
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inl h0⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inl h0)⟩
  · rcases k17b_h1_step W hs hC h0 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inr (Or.inl h1))⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inr (Or.inr h0))⟩

def K17BSlice {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6t3LeftTT a a' b b' c c' d ∨ K14LeftPa a a' b b' c c' d ∨ K6t3LeftPc a a' b b' c c' d ∨
  K14LeftTa' a a' b b' c c' d ∨ K6tLeftTc' a a' b b' c c' d ∨
  K17BLeftMN2 W ∨ K6sDN2one a a' b b' c c' d ∨ K17LeftMKb W

theorem k17b_slice_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K17CSlice W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K17BSlice W := by
  rcases h with h | h | h | h | h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · rcases k17b_MN2 W h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))

def K17BResidP (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ W : Norm08w a a' b b' c c' d, ResP W.F d ∧ K17BSlice W

def K17BResidP6 (a a' b b' c c' d : ℝ³) : Prop :=
  K17BResidP a a' b b' c c' d ∨ K17BResidP b b' a a' c c' d ∨ K17BResidP a a' c c' b b' d ∨
  K17BResidP c c' a a' b b' d ∨ K17BResidP b b' c c' a a' d ∨ K17BResidP c c' b b' a a' d

/-- **`Resid08FinalK17B`**: `Resid08FinalK17C` with H1-L2 cut to `K17bL2Left`. -/
def Resid08FinalK17B (a a' b b' c c' d : ℝ³) : Prop :=
  (PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ K17BResidP6 a a' b b' c c' d ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

theorem k17b_residP_step {p p' q q' r r' d : ℝ³} (h : K17CResidP p p' q q' r r' d) :
    HasLexCell (V8 p p' q q' r r' d) ∨ K17BResidP p p' q q' r r' d := by
  obtain ⟨W, hR, hs⟩ := h
  rcases k17b_slice_step W hs with h | h
  · exact Or.inl h
  · exact Or.inr ⟨W, hR, h⟩

theorem resid08FinalK17C_imp_K17B {a a' b b' c c' d : ℝ³}
    (h : Resid08FinalK17C a a' b b' c c' d) : Resid08FinalK17B a a' b b' c c' d := by
  obtain ⟨hpl, h6, hno⟩ := h
  have e := type08_set_perm a a' b b' c c' d
  refine ⟨hpl, ?_, hno⟩
  rcases h6 with h | h | h | h | h | h
  · rcases k17b_residP_step h with h | h
    · exact (hno h).elim
    · exact Or.inl h
  · rcases k17b_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.1]; exact h)).elim
    · exact Or.inr (Or.inl h)
  · rcases k17b_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k17b_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k17b_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k17b_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.2]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Type08Sp
end Minimality
