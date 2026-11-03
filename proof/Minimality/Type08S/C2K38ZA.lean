module

public import Minimality.Type08S.C2K37ZA
public import Minimality.Type08S.C2K38LN
public import Minimality.Type08S.C2K38LP
public import Minimality.Type08S.C2K38LZ

/-!
# K38 / Z: M stratum, the β6 = 1 corner Lz = Lw = 0 on Lq < 0 (and its γ6 = 1 mirror), both sides: three generated
cells at the view a − c′ split by the sign of S = ⟪a − d, a − c′⟫ (`k34lw_N`, `k34lw_Z`, `k34lw_P`; specpos/C2/K34LW).
Left of the corner: Lq = ⟪c′ − a′, b′ − a⟫ > 0 (occurs, with S < 0 on all samples).
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

/-- What is left of the β6 = 1 corner Lz = Lw = 0: Lp > 0 and Lq > 0. -/
def K38B4Rest (a a' b' c c' d : ℝ³) : Prop :=
  0 < ⟪c' - a', b' - c⟫ ∧ ⟪c' - c, k28b4c_u0 a a' c c' d⟫ = 0 ∧ ⟪a - c', k28b4c_u0 a a' c c' d⟫ = 0 ∧
    0 < ⟪c' - a', b' - a⟫

theorem k38_b4 {a a' b b' c c' d : ℝ³} {α1 β1 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 1 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hα : 1 < α1) (hβ : 1 < β1) (hσ : β1 < 1 + γ6)
    (h : K34B4Rest a a' b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K38B4Rest a a' b' c c' d := by
  obtain ⟨hLp, hz, hw⟩ := h
  rcases lt_or_eq_of_le hLp with hp | hp
  swap
  · exact Or.inl (k32h_LpLz hC hM hrel hα hβ hσ hp.symm hz)
  rcases lt_trichotomy ⟪c' - a', b' - a⟫ 0 with hq | hq | hq
  · rcases lt_trichotomy ⟪a - d, a - c'⟫ 0 with hS | hS | hS
    · exact Or.inl (k34lw_N hC hM hrel hα hβ hσ hz hw hp hq hS)
    · exact Or.inl (k34lw_Z hC hM hrel hα hβ hσ hz hw hp hq hS)
    · exact Or.inl (k34lw_P hC hM hrel hα hβ hσ hz hw hp hq hS)
  · exact Or.inl (k32h_LzLq hC hM hrel hα hβ hσ hq hz)
  · exact Or.inr ⟨hp, hz, hw, hq⟩

def K38mBoundary (a a' b b' c c' d : ℝ³) (α1 β1 β6 γ6 : ℝ) : Prop :=
  (1 < β1 ∧ β6 + γ6 = β1 ∧ ⟪a - c', a - d⟫ = 0 ∧ K33SigRest a a' b b' c c' d α1 β1 β6 γ6) ∨
    (1 < β1 ∧ β1 < β6 + γ6 ∧ 1 < α1 ∧
      ((β6 = 1 ∧ K38B4Rest a a' b' c c' d) ∨ (γ6 = 1 ∧ K38B4Rest a a' c' b b' d)))

theorem k38_boundary {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : 1 < β1 → K16Rel a b c d α1 β1) (h : K37mBoundary a a' b b' c c' d α1 β1 β6 γ6) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K38mBoundary a a' b b' c c' d α1 β1 β6 γ6 := by
  rcases h with h0 | ⟨hβ1, hσ, hα1, ⟨hb, h⟩ | ⟨hg, h⟩⟩
  · exact Or.inr (Or.inl h0)
  · subst hb
    rcases k38_b4 hC hM (hrel hβ1) hα1 hβ1 hσ h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inr ⟨hβ1, hσ, hα1, Or.inl ⟨rfl, h1⟩⟩)
  · subst hg
    rcases k38_b4 (k37_coords_swap hC) (k6m_M_swap hM) (k16_rel_swap hM.1 (hrel hβ1)) hα1 hβ1
        (by linarith) h with h1 | h1
    · left; rwa [k6m_V8_swap] at h1
    · exact Or.inr (Or.inr ⟨hβ1, hσ, hα1, Or.inr ⟨rfl, h1⟩⟩)

def K38LeftMN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6sMN2 a a' b b' c c' d ∧ ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧
    (RegN2 W.F → 1 < γ6) ∧
    (K38mBoundary a a' b b' c c' d α1 β1 β6 γ6 ∨
      (K6mH1Left a a' b b' c c' d α1 β1 β6 γ6 ∧ K17b2L2Left a a' b b' c c' d α1 β1 β6 γ6 ∧
        K33L2Corner a a' b b' c c' d α1 β1) ∨
      (K20mH5c a a' b b' c c' d α1 β1 β6 γ6 ∧ ⟪c' - a, b' - a⟫ = 0))

def K38LeftMKb {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6sMKb a a' b b' c c' d ∧ ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧
    (RegT4 W.F → 1 < α1 ∧ γ6 < 1) ∧
    (K38mBoundary a a' b b' c c' d α1 β1 β6 γ6 ∨
      (K20mH5c a a' b b' c c' d α1 β1 β6 γ6 ∧ ⟪c' - a, b' - a⟫ = 0))

theorem k38z_MN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K37LeftMN2 W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K38LeftMN2 W := by
  obtain ⟨hs, α1, β1, β6, γ6, hC, hreg, h0 | hL | h5⟩ := h
  · have hrel : 1 < β1 → K16Rel a b c d α1 β1 := fun hβ1 => by
      obtain ⟨hdet, hc', hb', ha', hα1', -, -, -, hγ6', h3⟩ := hC
      exact k16_n2_rel W hs.1 hs.2.1 hs.2.2.1 hdet hc' ha' hα1' hβ1 hγ6' h3
    rcases k38_boundary hC hs.2.2 hrel h0 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inl h1⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inl hL)⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inr h5)⟩

theorem k38z_MKb {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K37LeftMKb W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K38LeftMKb W := by
  obtain ⟨hs, α1, β1, β6, γ6, hC, hreg, h0 | h5⟩ := h
  · have hrel : 1 < β1 → K16Rel a b c d α1 β1 := fun hβ1 => by
      obtain ⟨hdet, hc', hb', ha', hα1', -⟩ := hC
      exact k16_kb_rel W hs.1 hs.2.1 hs.2.2.1 hdet hb' hα1' hβ1
    rcases k38_boundary hC hs.2.2 hrel h0 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inl h1⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr h5⟩

def K38Slice {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K38LeftMN2 W ∨ K38LeftMKb W

theorem k38_slice_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : K37Slice W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K38Slice W := by
  rcases h with h | h
  · rcases k38z_MN2 W h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · rcases k38z_MKb W h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inr h1)

def K38ResidP (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ W : Norm08w a a' b b' c c' d, ResP W.F d ∧ K38Slice W

def K38ResidP6 (a a' b b' c c' d : ℝ³) : Prop :=
  K38ResidP a a' b b' c c' d ∨ K38ResidP b b' a a' c c' d ∨ K38ResidP a a' c c' b b' d ∨
  K38ResidP c c' a a' b b' d ∨ K38ResidP b b' c c' a a' d ∨ K38ResidP c c' b b' a a' d

/-- **`Resid08FinalK38`**: as K37 with the Lz = Lw = 0 corner closed on Lq < 0. -/
def Resid08FinalK38 (a a' b b' c c' d : ℝ³) : Prop :=
  (PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ K38ResidP6 a a' b b' c c' d ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

theorem k38_residP_step {p p' q q' r r' d : ℝ³}
    (hNR : ¬ IsRupert (V8 p p' q q' r r' d)) (h : K37ResidP p p' q q' r r' d) :
    HasLexCell (V8 p p' q q' r r' d) ∨ K38ResidP p p' q q' r r' d := by
  obtain ⟨W, hR, hs⟩ := h
  rcases k38_slice_step W hNR hs with h | h
  · exact Or.inl h
  · exact Or.inr ⟨W, hR, h⟩

theorem resid08FinalK37_imp_K38 {a a' b b' c c' d : ℝ³}
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : Resid08FinalK37 a a' b b' c c' d) :
    Resid08FinalK38 a a' b b' c c' d := by
  obtain ⟨hpl, h6, hno⟩ := h
  have e := type08_set_perm a a' b b' c c' d
  refine ⟨hpl, ?_, hno⟩
  rcases h6 with h | h | h | h | h | h
  · rcases k38_residP_step hNR h with h | h
    · exact (hno h).elim
    · exact Or.inl h
  · rcases k38_residP_step (fun hR => hNR (by rw [V8, ← e.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.1]; exact h)).elim
    · exact Or.inr (Or.inl h)
  · rcases k38_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k38_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k38_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k38_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.2]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.2]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Type08Sp
end Minimality
