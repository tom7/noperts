module

public import Minimality.Type08S.C2K36ZA

/-!
# K37 / Z: M stratum, γ6 = 1 by the b ↔ c mirror (both sides). Swapping (b, b′) ↔ (c, c′) swaps β6 ↔ γ6 and keeps
`K6sM` (`k6m_M_swap`), `K16Rel` (`k16_rel_swap`) and the point set (`k6m_V8_swap`); so the β6 = 1 chain (leaves A–E,
ties, corners: K29–K34) closes γ6 = 1 up to the mirrored corner Lz = Lw = 0.
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

theorem k37_coords_swap {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (h : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) : K6mCoords a a' c c' b b' d α1 β1 γ6 β6 := by
  obtain ⟨hdet, hc', hb', ha', h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨?_, hb', hc', by rw [ha']; abel, h1, h2, h3, h5, h4, by linarith⟩
  intro h; apply hdet
  simp only [det3_expand] at h ⊢; linarith

/-- The β6 = 1 chain of K29–K34 in one lemma. -/
theorem k37_b4chain {a a' b b' c c' d : ℝ³} {α1 β1 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 1 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hα : 1 < α1) (hβ : 1 < β1) (hσ : β1 < 1 + γ6) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K34B4Rest a a' b' c c' d := by
  rcases lt_or_ge ⟪c' - a', b' - c⟫ 0 with hLp | hLp
  · exact Or.inl (k28b4_A hC hM hrel hα hβ hσ hLp)
  rcases k30_b4 hC hM hrel hα hβ hσ hLp with h1 | h1
  · exact Or.inl h1
  rcases k31_b4 hC hM hrel hα hβ hσ h1 with h2 | h2
  · exact Or.inl h2
  exact k34_b4 hC hM hrel hα hβ hσ (k33_b4 hC hM hrel hα hβ hσ h2)

/-- K34's boundary with γ6 = 1 reduced to the mirrored corner. -/
def K37mBoundary (a a' b b' c c' d : ℝ³) (α1 β1 β6 γ6 : ℝ) : Prop :=
  (1 < β1 ∧ β6 + γ6 = β1 ∧ ⟪a - c', a - d⟫ = 0 ∧ K33SigRest a a' b b' c c' d α1 β1 β6 γ6) ∨
    (1 < β1 ∧ β1 < β6 + γ6 ∧ 1 < α1 ∧
      ((β6 = 1 ∧ K34B4Rest a a' b' c c' d) ∨ (γ6 = 1 ∧ K34B4Rest a a' c' b b' d)))

theorem k37_boundary {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : 1 < β1 → K16Rel a b c d α1 β1) (h : K34mBoundary a a' b b' c c' d α1 β1 β6 γ6) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K37mBoundary a a' b b' c c' d α1 β1 β6 γ6 := by
  rcases h with h0 | ⟨hβ1, hσ, hα1, hb | hg⟩
  · exact Or.inr (Or.inl h0)
  · exact Or.inr (Or.inr ⟨hβ1, hσ, hα1, Or.inl hb⟩)
  · subst hg
    have hC' := k37_coords_swap hC
    have hrel' := k16_rel_swap hM.1 (hrel hβ1)
    rcases k37_b4chain hC' (k6m_M_swap hM) hrel' hα1 hβ1 (by linarith) with h1 | h1
    · left; rwa [k6m_V8_swap] at h1
    · exact Or.inr (Or.inr ⟨hβ1, hσ, hα1, Or.inr ⟨rfl, h1⟩⟩)

def K37LeftMN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6sMN2 a a' b b' c c' d ∧ ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧
    (RegN2 W.F → 1 < γ6) ∧
    (K37mBoundary a a' b b' c c' d α1 β1 β6 γ6 ∨
      (K6mH1Left a a' b b' c c' d α1 β1 β6 γ6 ∧ K17b2L2Left a a' b b' c c' d α1 β1 β6 γ6 ∧
        K33L2Corner a a' b b' c c' d α1 β1) ∨
      (K20mH5c a a' b b' c c' d α1 β1 β6 γ6 ∧ ⟪c' - a, b' - a⟫ = 0))

def K37LeftMKb {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6sMKb a a' b b' c c' d ∧ ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧
    (RegT4 W.F → 1 < α1 ∧ γ6 < 1) ∧
    (K37mBoundary a a' b b' c c' d α1 β1 β6 γ6 ∨
      (K20mH5c a a' b b' c c' d α1 β1 β6 γ6 ∧ ⟪c' - a, b' - a⟫ = 0))

theorem k37z_MN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K35LeftMN2 W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K37LeftMN2 W := by
  obtain ⟨hs, α1, β1, β6, γ6, hC, hreg, h0 | hL | h5⟩ := h
  · have hrel : 1 < β1 → K16Rel a b c d α1 β1 := fun hβ1 => by
      obtain ⟨hdet, hc', hb', ha', hα1', -, -, -, hγ6', h3⟩ := hC
      exact k16_n2_rel W hs.1 hs.2.1 hs.2.2.1 hdet hc' ha' hα1' hβ1 hγ6' h3
    rcases k37_boundary hC hs.2.2 hrel h0 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inl h1⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inl hL)⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inr h5)⟩

theorem k37z_MKb {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K36LeftMKb W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K37LeftMKb W := by
  obtain ⟨hs, α1, β1, β6, γ6, hC, hreg, h0 | h5⟩ := h
  · have hrel : 1 < β1 → K16Rel a b c d α1 β1 := fun hβ1 => by
      obtain ⟨hdet, hc', hb', ha', hα1', -⟩ := hC
      exact k16_kb_rel W hs.1 hs.2.1 hs.2.2.1 hdet hb' hα1' hβ1
    rcases k37_boundary hC hs.2.2 hrel h0 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inl h1⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr h5⟩

def K37Slice {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K37LeftMN2 W ∨ K37LeftMKb W

theorem k37_slice_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : K36Slice W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K37Slice W := by
  rcases h with h | h
  · rcases k37z_MN2 W h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · rcases k37z_MKb W h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inr h1)

def K37ResidP (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ W : Norm08w a a' b b' c c' d, ResP W.F d ∧ K37Slice W

def K37ResidP6 (a a' b b' c c' d : ℝ³) : Prop :=
  K37ResidP a a' b b' c c' d ∨ K37ResidP b b' a a' c c' d ∨ K37ResidP a a' c c' b b' d ∨
  K37ResidP c c' a a' b b' d ∨ K37ResidP b b' c c' a a' d ∨ K37ResidP c c' b b' a a' d

/-- **`Resid08FinalK37`**: as K36 with γ6 = 1 mirrored onto the β6 = 1 chain. -/
def Resid08FinalK37 (a a' b b' c c' d : ℝ³) : Prop :=
  (PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ K37ResidP6 a a' b b' c c' d ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

theorem k37_residP_step {p p' q q' r r' d : ℝ³}
    (hNR : ¬ IsRupert (V8 p p' q q' r r' d)) (h : K36ResidP p p' q q' r r' d) :
    HasLexCell (V8 p p' q q' r r' d) ∨ K37ResidP p p' q q' r r' d := by
  obtain ⟨W, hR, hs⟩ := h
  rcases k37_slice_step W hNR hs with h | h
  · exact Or.inl h
  · exact Or.inr ⟨W, hR, h⟩

theorem resid08FinalK36_imp_K37 {a a' b b' c c' d : ℝ³}
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : Resid08FinalK36 a a' b b' c c' d) :
    Resid08FinalK37 a a' b b' c c' d := by
  obtain ⟨hpl, h6, hno⟩ := h
  have e := type08_set_perm a a' b b' c c' d
  refine ⟨hpl, ?_, hno⟩
  rcases h6 with h | h | h | h | h | h
  · rcases k37_residP_step hNR h with h | h
    · exact (hno h).elim
    · exact Or.inl h
  · rcases k37_residP_step (fun hR => hNR (by rw [V8, ← e.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.1]; exact h)).elim
    · exact Or.inr (Or.inl h)
  · rcases k37_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k37_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k37_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k37_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.2]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.2]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Type08Sp
end Minimality
