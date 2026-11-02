module

public import Minimality.Type08S.C2K26ZA
public import Minimality.Type08S.C2K24B1B
public import Minimality.Type08S.C2K24MTaB
public import Minimality.Type08S.C2K24MTbB
public import Minimality.Type08S.C2K24MTcB
public import Minimality.Type08S.C2K24MTdB

/-!
# K27 / Z: M stratum, `K14mTie` closed (four cells, split by ⟪b-c,b-a'⟫ resp. ⟪c-b,c-a'⟫; specpos/C2/K24MT*) and the
α1 = 1 piece of the boundary closed (`k24b1_cell`, specpos/C2/K24B1*).
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

theorem k27_mtie {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ} (W : Norm08w a a' b b' c c' d)
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : 1 < β1 → K16Rel a b c d α1 β1) (h : K14mTie a a' b b' c c' α1 β1 β6 γ6) :
    HasLexCell (V8 a a' b b' c c' d) := by
  rcases h with h | h
  · rcases le_or_gt ⟪b - c, b - a'⟫ 0 with hL | hL
    · exact k24mt_le W hC hM (hrel h.2.1) h hL
    · exact k24mt_gt W hC hM h hL
  · rcases le_or_gt ⟪c - b, c - a'⟫ 0 with hL | hL
    · exact k24mt2_le W hC hM (hrel h.2.1) h hL
    · exact k24mt2_gt W hC hM h hL

/-- The boundary pieces left: σ = β1, and β6 = 1 or γ6 = 1 at α1 > 1. -/
def K27mBoundary (a a' b c c' d : ℝ³) (α1 β1 β6 γ6 : ℝ) : Prop :=
  (1 < β1 ∧ β6 + γ6 = β1) ∨ (1 < β1 ∧ β1 < β6 + γ6 ∧ 1 < α1 ∧ (β6 = 1 ∨ γ6 = 1))

theorem k27_boundary {reg : Prop} {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ} (W : Norm08w a a' b b' c c' d)
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : 1 < β1 → K16Rel a b c d α1 β1) (h : K22mBoundary reg a a' b c c' d α1 β1 β6 γ6) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K27mBoundary a a' b c c' d α1 β1 β6 γ6 := by
  rcases h with h | ⟨hβ, hβs, hα, -, -⟩ | h
  · exact Or.inr (Or.inl h)
  · subst hα
    exact Or.inl (k24b1_cell W hC hM (hrel hβ) hβ hβs)
  · exact Or.inr (Or.inr h)

def K27LeftMN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6sMN2 a a' b b' c c' d ∧ ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧
    (RegN2 W.F → 1 < γ6) ∧
    (K27mBoundary a a' b c c' d α1 β1 β6 γ6 ∨ K17B2H1Left a a' b b' c c' d α1 β1 β6 γ6 ∨
      K20mH5c a a' b b' c c' d α1 β1 β6 γ6)

def K27LeftMKb {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6sMKb a a' b b' c c' d ∧ ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧
    (RegT4 W.F → 1 < α1 ∧ γ6 < 1) ∧
    (K27mBoundary a a' b c c' d α1 β1 β6 γ6 ∨ K20mH5c a a' b b' c c' d α1 β1 β6 γ6)

theorem k27z_MN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K22LeftMN2 W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K27LeftMN2 W := by
  obtain ⟨hs, α1, β1, β6, γ6, hC, hreg, h0⟩ := h
  have hrel : 1 < β1 → K16Rel a b c d α1 β1 := fun hβ1 => by
    obtain ⟨hdet, hc', hb', ha', hα1', -, -, -, hγ6', h3⟩ := hC
    exact k16_n2_rel W hs.1 hs.2.1 hs.2.2.1 hdet hc' ha' hα1' hβ1 hγ6' h3
  rcases h0 with h0 | h0 | h0 | h0
  · rcases k27_boundary W hC hs.2.2 hrel h0 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inl h1⟩
  · exact Or.inl (k27_mtie W hC hs.2.2 hrel h0)
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inl h0)⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inr h0)⟩

theorem k27z_MKb {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K22LeftMKb W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K27LeftMKb W := by
  obtain ⟨hs, α1, β1, β6, γ6, hC, hreg, h0⟩ := h
  have hrel : 1 < β1 → K16Rel a b c d α1 β1 := fun hβ1 => by
    obtain ⟨hdet, hc', hb', ha', hα1', -, -, -, -, -⟩ := hC
    exact k16_kb_rel W hs.1 hs.2.1 hs.2.2.1 hdet hb' hα1' hβ1
  rcases h0 with h0 | h0 | h0
  · rcases k27_boundary W hC hs.2.2 hrel h0 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inl h1⟩
  · exact Or.inl (k27_mtie W hC hs.2.2 hrel h0)
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr h0⟩

def K27Slice {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K27LeftMN2 W ∨ K27LeftMKb W

theorem k27_slice_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : K26Slice W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K27Slice W := by
  rcases h with h | h
  · rcases k27z_MN2 W h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · rcases k27z_MKb W h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inr h1)

def K27ResidP (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ W : Norm08w a a' b b' c c' d, ResP W.F d ∧ K27Slice W

def K27ResidP6 (a a' b b' c c' d : ℝ³) : Prop :=
  K27ResidP a a' b b' c c' d ∨ K27ResidP b b' a a' c c' d ∨ K27ResidP a a' c c' b b' d ∨
  K27ResidP c c' a a' b b' d ∨ K27ResidP b b' c c' a a' d ∨ K27ResidP c c' b b' a a' d

/-- **`Resid08FinalK27`**: as K26 with `K14mTie` and the α1 = 1 boundary piece closed. -/
def Resid08FinalK27 (a a' b b' c c' d : ℝ³) : Prop :=
  (PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ K27ResidP6 a a' b b' c c' d ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

theorem k27_residP_step {p p' q q' r r' d : ℝ³}
    (hNR : ¬ IsRupert (V8 p p' q q' r r' d)) (h : K26ResidP p p' q q' r r' d) :
    HasLexCell (V8 p p' q q' r r' d) ∨ K27ResidP p p' q q' r r' d := by
  obtain ⟨W, hR, hs⟩ := h
  rcases k27_slice_step W hNR hs with h | h
  · exact Or.inl h
  · exact Or.inr ⟨W, hR, h⟩

theorem resid08FinalK26_imp_K27 {a a' b b' c c' d : ℝ³}
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : Resid08FinalK26 a a' b b' c c' d) :
    Resid08FinalK27 a a' b b' c c' d := by
  obtain ⟨hpl, h6, hno⟩ := h
  have e := type08_set_perm a a' b b' c c' d
  refine ⟨hpl, ?_, hno⟩
  rcases h6 with h | h | h | h | h | h
  · rcases k27_residP_step hNR h with h | h
    · exact (hno h).elim
    · exact Or.inl h
  · rcases k27_residP_step (fun hR => hNR (by rw [V8, ← e.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.1]; exact h)).elim
    · exact Or.inr (Or.inl h)
  · rcases k27_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k27_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k27_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k27_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.2]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.2]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Type08Sp
end Minimality
