module

public import Minimality.Type08S.C2K17B2Z
public import Minimality.Type08S.C2K17BZ

@[expose] public section


/-!
# K17B2 / Y: composition.  `K17bL2Left` cut to `K17b2L2Left` (K6M2's L2 rules 1, 2, 3, 4, 5, 13).
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
open C2

def K17B2H1Left (a a' b b' c c' d : ℝ³) (α1 β1 β6 γ6 : ℝ) : Prop :=
  K6mH1Left a a' b b' c c' d α1 β1 β6 γ6 ∧
    (⟪c - a', a - b'⟫ = 0 ∨ K17b2L2Left a a' b b' c c' d α1 β1 β6 γ6)

theorem k17b2_h1_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hs : K6sMN2 a a' b b' c c' d) {α1 β1 β6 γ6 : ℝ} (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6)
    (h : K17BH1Left a a' b b' c c' d α1 β1 β6 γ6) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K17B2H1Left a a' b b' c c' d α1 β1 β6 γ6 := by
  obtain ⟨hH1, ht | hL⟩ := h
  · exact Or.inr ⟨hH1, Or.inl ht⟩
  · obtain ⟨hdet, hc', hb', ha', hα1', hβ1', h1, hβ6', hγ6', h3⟩ := hC
    obtain ⟨⟨hα1, hβ1, hσ, hβ6, hγ6⟩, -, -⟩ := id hH1
    have hrel := k16_n2_rel W hs.1 hs.2.1 hs.2.2.1 hdet hc' ha' hα1' hβ1 hγ6' h3
    rcases k17b2_l2 hdet hc' hb' ha' hα1 hβ1 hβ6 hγ6 hσ hs.2.2 hrel hL with h2 | h2
    · exact Or.inl h2
    · exact Or.inr ⟨hH1, Or.inr h2⟩

def K17B2LeftMN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6sMN2 a a' b b' c c' d ∧ ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧
    (RegN2 W.F → 1 < γ6) ∧
    (K17mBoundary (RegN2 W.F) a a' b c c' d α1 β1 β6 γ6 ∨ K14mTie a a' b b' c c' α1 β1 β6 γ6 ∨
      K17B2H1Left a a' b b' c c' d α1 β1 β6 γ6 ∨ K16mH5b a a' b b' c c' d α1 β1 β6 γ6)

theorem k17b2_MN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K17BLeftMN2 W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K17B2LeftMN2 W := by
  obtain ⟨hs, α1, β1, β6, γ6, hC, hreg, h0 | h0 | h0 | h0⟩ := h
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inl h0⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inl h0)⟩
  · rcases k17b2_h1_step W hs hC h0 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inr (Or.inl h1))⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inr (Or.inr h0))⟩

def K17B2Slice {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6t3LeftTT a a' b b' c c' d ∨ K17fLeftPa a a' b b' c c' d ∨ K6t3LeftPc a a' b b' c c' d ∨
  K17fLeftTa14 a a' b b' c c' d ∨ K17fLeftTc' a a' b b' c c' d ∨
  K17B2LeftMN2 W ∨ K6sDN2one a a' b b' c c' d ∨ K17LeftMKb W

theorem k17b2_slice_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K17BSlice W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K17B2Slice W := by
  rcases h with h | h | h | h | h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · rcases k17b2_MN2 W h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))

def K17B2ResidP (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ W : Norm08w a a' b b' c c' d, ResP W.F d ∧ K17B2Slice W

def K17B2ResidP6 (a a' b b' c c' d : ℝ³) : Prop :=
  K17B2ResidP a a' b b' c c' d ∨ K17B2ResidP b b' a a' c c' d ∨ K17B2ResidP a a' c c' b b' d ∨
  K17B2ResidP c c' a a' b b' d ∨ K17B2ResidP b b' c c' a a' d ∨ K17B2ResidP c c' b b' a a' d

/-- **`Resid08FinalK17B2`**: `Resid08FinalK17B` with H1-L2 cut to `K17b2L2Left`. -/
def Resid08FinalK17B2 (a a' b b' c c' d : ℝ³) : Prop :=
  (PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ K17B2ResidP6 a a' b b' c c' d ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

theorem k17b2_residP_step {p p' q q' r r' d : ℝ³} (h : K17BResidP p p' q q' r r' d) :
    HasLexCell (V8 p p' q q' r r' d) ∨ K17B2ResidP p p' q q' r r' d := by
  obtain ⟨W, hR, hs⟩ := h
  rcases k17b2_slice_step W hs with h | h
  · exact Or.inl h
  · exact Or.inr ⟨W, hR, h⟩

theorem resid08FinalK17B_imp_K17B2 {a a' b b' c c' d : ℝ³}
    (h : Resid08FinalK17B a a' b b' c c' d) : Resid08FinalK17B2 a a' b b' c c' d := by
  obtain ⟨hpl, h6, hno⟩ := h
  have e := type08_set_perm a a' b b' c c' d
  refine ⟨hpl, ?_, hno⟩
  rcases h6 with h | h | h | h | h | h
  · rcases k17b2_residP_step h with h | h
    · exact (hno h).elim
    · exact Or.inl h
  · rcases k17b2_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.1]; exact h)).elim
    · exact Or.inr (Or.inl h)
  · rcases k17b2_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k17b2_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k17b2_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k17b2_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.2]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Type08Sp
end Minimality
