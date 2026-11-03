module

public import Minimality.Type08S.C2K30ZA
public import Minimality.Type08S.C2K28B4t2
public import Minimality.Type08S.C2K28B4u2
public import Minimality.Type08S.C2K28B4p2
public import Minimality.Type08S.C2K28B4q2
public import Minimality.Type08S.C2K28B4z2
public import Minimality.Type08S.C2K28B4z3
public import Minimality.Type08S.C2K28B4z4

/-!
# K31 / Z: M stratum (N2 side), the β6 = 1 ties (specpos/C2/K28B4S §4, K28B4T, K28B4Z).
With `Lp = ⟪c'-a', b'-c⟫ ≥ 0`, `Lq = ⟪c'-a', b'-a⟫`, `Lz = ⟪c'-c, u0⟫`, `Lw = ⟪a-c', u0⟫` (`u0 = k28b4c_u0`):
Lz > 0: Lp = 0, Lq < 0 → Bp0; Lq = 0 → Dq0.  Lz < 0: Lp = 0, Lq < 0, hE → Cp0; Lq = 0 → Cq0.
Lz = 0, Lp > 0: Lq < 0: Lw < 0 → Bz0, Lw > 0 → Cz0; Lq > 0 → Dz0.  Left: `K31B4Rest`.
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

/-- The β6 = 1 tie corners left by K31 (`hE` of `k28b4_Cp0` failing, double ties, `Lw = 0`). -/
def K31B4Rest (a a' b b' c c' d : ℝ³) (γ6 : ℝ) : Prop :=
  0 ≤ ⟪c' - a', b' - c⟫ ∧
  ((⟪c' - a', b' - c⟫ = 0 ∧ (0 ≤ ⟪c' - a', b' - a⟫ ∨ ⟪c' - c, k28b4c_u0 a a' c c' d⟫ = 0 ∨
      (⟪c' - c, k28b4c_u0 a a' c c' d⟫ < 0 ∧
        -⟪c' - a', b - d⟫ + (1 - γ6) * ⟪c' - a', c - d⟫ ≤ 0))) ∨
    (⟪c' - c, k28b4c_u0 a a' c c' d⟫ = 0 ∧
      (⟪c' - a', b' - a⟫ = 0 ∨ ⟪a - c', k28b4c_u0 a a' c c' d⟫ = 0)))

theorem k31_b4 {a a' b b' c c' d : ℝ³} {α1 β1 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 1 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hα : 1 < α1) (hβ : 1 < β1) (hσ : β1 < 1 + γ6)
    (ht : K30B4Tie a a' b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K31B4Rest a a' b b' c c' d γ6 := by
  obtain ⟨hLp, hT⟩ := ht
  rcases lt_trichotomy ⟪c' - c, k28b4c_u0 a a' c c' d⟫ 0 with hz | hz | hz
  · -- Lz < 0
    rcases lt_or_eq_of_le hLp with hp | hp
    · rcases hT with h | h | h
      · exact absurd h (ne_of_gt hp)
      · exact Or.inl (k28b4_Cq0 hC hM hrel hα hβ hσ h hz)
      · exact absurd h (ne_of_lt hz)
    · rcases lt_or_ge ⟪c' - a', b' - a⟫ 0 with hq | hq
      · rcases lt_or_ge 0 (-⟪c' - a', b - d⟫ + (1 - γ6) * ⟪c' - a', c - d⟫) with hE | hE
        · exact Or.inl (k28b4_Cp0 hC hM hrel hα hβ hσ hp.symm hq hE hz)
        · exact Or.inr ⟨hLp, Or.inl ⟨hp.symm, Or.inr (Or.inr ⟨hz, hE⟩)⟩⟩
      · exact Or.inr ⟨hLp, Or.inl ⟨hp.symm, Or.inl hq⟩⟩
  · -- Lz = 0
    rcases lt_or_eq_of_le hLp with hp | hp
    · rcases lt_trichotomy ⟪c' - a', b' - a⟫ 0 with hq | hq | hq
      · rcases lt_trichotomy ⟪a - c', k28b4c_u0 a a' c c' d⟫ 0 with hw | hw | hw
        · exact Or.inl (k28b4_Bz0 hC hM hrel hα hβ hσ hp hq hz hw)
        · exact Or.inr ⟨hLp, Or.inr ⟨hz, Or.inr hw⟩⟩
        · exact Or.inl (k28b4_Cz0 hC hM hrel hα hβ hσ hp hq hz hw)
      · exact Or.inr ⟨hLp, Or.inr ⟨hz, Or.inl hq⟩⟩
      · exact Or.inl (k28b4_Dz0 hC hM hrel hα hβ hσ hq hz)
    · exact Or.inr ⟨hLp, Or.inl ⟨hp.symm, Or.inr (Or.inl hz)⟩⟩
  · -- Lz > 0
    rcases lt_or_eq_of_le hLp with hp | hp
    · rcases hT with h | h | h
      · exact absurd h (ne_of_gt hp)
      · exact Or.inl (k28b4_Dq0 hC hM hrel hα hβ hσ h hz)
      · exact absurd h (ne_of_gt hz)
    · rcases lt_or_ge ⟪c' - a', b' - a⟫ 0 with hq | hq
      · exact Or.inl (k28b4_Bp0 hC hM hrel hα hβ hσ hp.symm hq hz)
      · exact Or.inr ⟨hLp, Or.inl ⟨hp.symm, Or.inl hq⟩⟩

/-- K30's boundary with the β6 = 1 ties closed up to `K31B4Rest`. -/
def K31mBoundary (a a' b b' c c' d : ℝ³) (α1 β1 β6 γ6 : ℝ) : Prop :=
  (1 < β1 ∧ β6 + γ6 = β1) ∨
    (1 < β1 ∧ β1 < β6 + γ6 ∧ 1 < α1 ∧ ((β6 = 1 ∧ K31B4Rest a a' b b' c c' d γ6) ∨ γ6 = 1))

def K31LeftMN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6sMN2 a a' b b' c c' d ∧ ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧
    (RegN2 W.F → 1 < γ6) ∧
    (K31mBoundary a a' b b' c c' d α1 β1 β6 γ6 ∨
      (K6mH1Left a a' b b' c c' d α1 β1 β6 γ6 ∧ K17b2L2Left a a' b b' c c' d α1 β1 β6 γ6 ∧
        K29L2Corner a a' b b' c c' d α1 β1) ∨
      (K20mH5c a a' b b' c c' d α1 β1 β6 γ6 ∧ ⟪c' - a, b' - a⟫ ≤ 0))

theorem k31z_MN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K30LeftMN2 W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K31LeftMN2 W := by
  obtain ⟨hs, α1, β1, β6, γ6, hC, hreg, h0 | hL | h5⟩ := h
  · rcases h0 with h0 | ⟨hβ1, hσ, hα1, ⟨hb, ht⟩ | hg⟩
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inl (Or.inl h0)⟩
    · have hrel : K16Rel a b c d α1 β1 := by
        obtain ⟨hdet, hc', hb', ha', hα1', -, -, -, hγ6', h3⟩ := hC
        exact k16_n2_rel W hs.1 hs.2.1 hs.2.2.1 hdet hc' ha' hα1' hβ1 hγ6' h3
      subst hb
      rcases k31_b4 hC hs.2.2 hrel hα1 hβ1 hσ ht with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨hs, α1, β1, 1, γ6, hC, hreg, Or.inl (Or.inr ⟨hβ1, hσ, hα1, Or.inl ⟨rfl, h1⟩⟩)⟩
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inl (Or.inr ⟨hβ1, hσ, hα1, Or.inr hg⟩)⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inl hL)⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inr h5)⟩

def K31Slice {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K31LeftMN2 W ∨ K27LeftMKb W

theorem k31_slice_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : K30Slice W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K31Slice W := by
  rcases h with h | h
  · rcases k31z_MN2 W h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h)

def K31ResidP (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ W : Norm08w a a' b b' c c' d, ResP W.F d ∧ K31Slice W

def K31ResidP6 (a a' b b' c c' d : ℝ³) : Prop :=
  K31ResidP a a' b b' c c' d ∨ K31ResidP b b' a a' c c' d ∨ K31ResidP a a' c c' b b' d ∨
  K31ResidP c c' a a' b b' d ∨ K31ResidP b b' c c' a a' d ∨ K31ResidP c c' b b' a a' d

/-- **`Resid08FinalK31`**: as K30 with the β6 = 1 ties closed except corners. -/
def Resid08FinalK31 (a a' b b' c c' d : ℝ³) : Prop :=
  (PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ K31ResidP6 a a' b b' c c' d ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

theorem k31_residP_step {p p' q q' r r' d : ℝ³}
    (hNR : ¬ IsRupert (V8 p p' q q' r r' d)) (h : K30ResidP p p' q q' r r' d) :
    HasLexCell (V8 p p' q q' r r' d) ∨ K31ResidP p p' q q' r r' d := by
  obtain ⟨W, hR, hs⟩ := h
  rcases k31_slice_step W hNR hs with h | h
  · exact Or.inl h
  · exact Or.inr ⟨W, hR, h⟩

theorem resid08FinalK30_imp_K31 {a a' b b' c c' d : ℝ³}
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : Resid08FinalK30 a a' b b' c c' d) :
    Resid08FinalK31 a a' b b' c c' d := by
  obtain ⟨hpl, h6, hno⟩ := h
  have e := type08_set_perm a a' b b' c c' d
  refine ⟨hpl, ?_, hno⟩
  rcases h6 with h | h | h | h | h | h
  · rcases k31_residP_step hNR h with h | h
    · exact (hno h).elim
    · exact Or.inl h
  · rcases k31_residP_step (fun hR => hNR (by rw [V8, ← e.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.1]; exact h)).elim
    · exact Or.inr (Or.inl h)
  · rcases k31_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k31_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k31_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k31_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.2]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.2]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Type08Sp
end Minimality
