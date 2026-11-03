module

public import Minimality.Type08S.C2K38ZA
public import Minimality.Type08S.C2K39LN
public import Minimality.Type08S.C2K39LS

/-!
# K39 / Z: M stratum, the rest of the Lz = Lw = 0 corner (Lq > 0): on S = ⟪a − d, a − c′⟫ < 0 the cell `k34lw_Nq`
(no Lq hypothesis); S ≥ 0 forces Lq < 0 (`k34lw_Sq`, Gram positive definiteness). With the γ6 = 1 mirror this closes
β6 = 1 and γ6 = 1 entirely; the boundary keeps only the σ = β1 tie rest `K33SigRest`.
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

theorem k39_b4 {a a' b b' c c' d : ℝ³} {α1 β1 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 1 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hα : 1 < α1) (hβ : 1 < β1) (hσ : β1 < 1 + γ6)
    (h : K38B4Rest a a' b' c c' d) : HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hp, hz, hw, hq⟩ := h
  rcases lt_or_ge ⟪a - d, a - c'⟫ 0 with hS | hS
  · exact k34lw_Nq hC hM hrel hα hβ hσ hz hw hp hS
  · exact absurd hq (not_lt.mpr (k34lw_Sq hC hM hrel hα hβ hσ hz hw hp hS).le)

/-- K38's boundary with β6 = 1 and γ6 = 1 closed: only the σ = β1 tie rest. -/
def K39mBoundary (a a' b b' c c' d : ℝ³) (α1 β1 β6 γ6 : ℝ) : Prop :=
  1 < β1 ∧ β6 + γ6 = β1 ∧ ⟪a - c', a - d⟫ = 0 ∧ K33SigRest a a' b b' c c' d α1 β1 β6 γ6

theorem k39_boundary {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : 1 < β1 → K16Rel a b c d α1 β1) (h : K38mBoundary a a' b b' c c' d α1 β1 β6 γ6) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K39mBoundary a a' b b' c c' d α1 β1 β6 γ6 := by
  rcases h with h0 | ⟨hβ1, hσ, hα1, ⟨hb, h⟩ | ⟨hg, h⟩⟩
  · exact Or.inr h0
  · subst hb
    exact Or.inl (k39_b4 hC hM (hrel hβ1) hα1 hβ1 hσ h)
  · subst hg
    have h1 := k39_b4 (k37_coords_swap hC) (k6m_M_swap hM) (k16_rel_swap hM.1 (hrel hβ1)) hα1 hβ1
      (by linarith) h
    left; rwa [k6m_V8_swap] at h1

def K39LeftMN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6sMN2 a a' b b' c c' d ∧ ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧
    (RegN2 W.F → 1 < γ6) ∧
    (K39mBoundary a a' b b' c c' d α1 β1 β6 γ6 ∨
      (K6mH1Left a a' b b' c c' d α1 β1 β6 γ6 ∧ K17b2L2Left a a' b b' c c' d α1 β1 β6 γ6 ∧
        K33L2Corner a a' b b' c c' d α1 β1) ∨
      (K20mH5c a a' b b' c c' d α1 β1 β6 γ6 ∧ ⟪c' - a, b' - a⟫ = 0))

def K39LeftMKb {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6sMKb a a' b b' c c' d ∧ ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧
    (RegT4 W.F → 1 < α1 ∧ γ6 < 1) ∧
    (K39mBoundary a a' b b' c c' d α1 β1 β6 γ6 ∨
      (K20mH5c a a' b b' c c' d α1 β1 β6 γ6 ∧ ⟪c' - a, b' - a⟫ = 0))

theorem k39z_MN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K38LeftMN2 W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K39LeftMN2 W := by
  obtain ⟨hs, α1, β1, β6, γ6, hC, hreg, h0 | hL | h5⟩ := h
  · have hrel : 1 < β1 → K16Rel a b c d α1 β1 := fun hβ1 => by
      obtain ⟨hdet, hc', hb', ha', hα1', -, -, -, hγ6', h3⟩ := hC
      exact k16_n2_rel W hs.1 hs.2.1 hs.2.2.1 hdet hc' ha' hα1' hβ1 hγ6' h3
    rcases k39_boundary hC hs.2.2 hrel h0 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inl h1⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inl hL)⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inr h5)⟩

theorem k39z_MKb {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K38LeftMKb W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K39LeftMKb W := by
  obtain ⟨hs, α1, β1, β6, γ6, hC, hreg, h0 | h5⟩ := h
  · have hrel : 1 < β1 → K16Rel a b c d α1 β1 := fun hβ1 => by
      obtain ⟨hdet, hc', hb', ha', hα1', -⟩ := hC
      exact k16_kb_rel W hs.1 hs.2.1 hs.2.2.1 hdet hb' hα1' hβ1
    rcases k39_boundary hC hs.2.2 hrel h0 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inl h1⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr h5⟩

def K39Slice {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K39LeftMN2 W ∨ K39LeftMKb W

theorem k39_slice_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : K38Slice W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K39Slice W := by
  rcases h with h | h
  · rcases k39z_MN2 W h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · rcases k39z_MKb W h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inr h1)

def K39ResidP (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ W : Norm08w a a' b b' c c' d, ResP W.F d ∧ K39Slice W

def K39ResidP6 (a a' b b' c c' d : ℝ³) : Prop :=
  K39ResidP a a' b b' c c' d ∨ K39ResidP b b' a a' c c' d ∨ K39ResidP a a' c c' b b' d ∨
  K39ResidP c c' a a' b b' d ∨ K39ResidP b b' c c' a a' d ∨ K39ResidP c c' b b' a a' d

/-- **`Resid08FinalK39`**: as K38 with β6 = 1 and γ6 = 1 closed. -/
def Resid08FinalK39 (a a' b b' c c' d : ℝ³) : Prop :=
  (PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ K39ResidP6 a a' b b' c c' d ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

theorem k39_residP_step {p p' q q' r r' d : ℝ³}
    (hNR : ¬ IsRupert (V8 p p' q q' r r' d)) (h : K38ResidP p p' q q' r r' d) :
    HasLexCell (V8 p p' q q' r r' d) ∨ K39ResidP p p' q q' r r' d := by
  obtain ⟨W, hR, hs⟩ := h
  rcases k39_slice_step W hNR hs with h | h
  · exact Or.inl h
  · exact Or.inr ⟨W, hR, h⟩

theorem resid08FinalK38_imp_K39 {a a' b b' c c' d : ℝ³}
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : Resid08FinalK38 a a' b b' c c' d) :
    Resid08FinalK39 a a' b b' c c' d := by
  obtain ⟨hpl, h6, hno⟩ := h
  have e := type08_set_perm a a' b b' c c' d
  refine ⟨hpl, ?_, hno⟩
  rcases h6 with h | h | h | h | h | h
  · rcases k39_residP_step hNR h with h | h
    · exact (hno h).elim
    · exact Or.inl h
  · rcases k39_residP_step (fun hR => hNR (by rw [V8, ← e.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.1]; exact h)).elim
    · exact Or.inr (Or.inl h)
  · rcases k39_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k39_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k39_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k39_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.2]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.2]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Type08Sp
end Minimality
