module

public import Minimality.Type08S.C2K29ZA
public import Minimality.Type08S.C2K28B4b2
public import Minimality.Type08S.C2K28B4c3
public import Minimality.Type08S.C2K28B4d2
public import Minimality.Type08S.C2K28B4e2
public import Minimality.Type08S.C2K28H5z1

/-!
# K30 / Z: M stratum (N2 side), the β6 = 1 leaves B–E and H5 cell A at T = 0 (specpos/C2/K28B4S, K28H5T).
- β6 = 1, `Lp = ⟪c'-a', b'-c⟫ > 0`: with `Lq = ⟪c'-a', b'-a⟫` and `Lz = ⟪c'-c, u0⟫` (`u0 = k28b4c_u0`),
  Lq < 0: Lz > 0 → B, Lz < 0 → C; Lq > 0: Lz > 0 → D, Lz < 0 → E. Left: the ties Lp = 0, Lq = 0, Lz = 0.
- H5, `S > 0`, `T = 0`: cell A with one more tilt functional (`k28h5a0_A'`). Left: `S ≤ 0`.
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

/-- The β6 = 1 ties left by the leaves A–E. -/
def K30B4Tie (a a' b' c c' d : ℝ³) : Prop :=
  0 ≤ ⟪c' - a', b' - c⟫ ∧
    (⟪c' - a', b' - c⟫ = 0 ∨ ⟪c' - a', b' - a⟫ = 0 ∨ ⟪c' - c, k28b4c_u0 a a' c c' d⟫ = 0)

/-- K29's boundary with the β6 = 1 leaves B–E removed. -/
def K30mBoundary (a a' b b' c c' d : ℝ³) (α1 β1 β6 γ6 : ℝ) : Prop :=
  (1 < β1 ∧ β6 + γ6 = β1) ∨
    (1 < β1 ∧ β1 < β6 + γ6 ∧ 1 < α1 ∧ ((β6 = 1 ∧ K30B4Tie a a' b' c c' d) ∨ γ6 = 1))

theorem k30_b4 {a a' b b' c c' d : ℝ³} {α1 β1 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 1 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hα : 1 < α1) (hβ : 1 < β1) (hσ : β1 < 1 + γ6)
    (hLp : 0 ≤ ⟪c' - a', b' - c⟫) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K30B4Tie a a' b' c c' d := by
  by_cases ht : ⟪c' - a', b' - c⟫ = 0 ∨ ⟪c' - a', b' - a⟫ = 0 ∨ ⟪c' - c, k28b4c_u0 a a' c c' d⟫ = 0
  · exact Or.inr ⟨hLp, ht⟩
  push_neg at ht
  obtain ⟨hp0, hq0, hz0⟩ := ht
  have hLp' : 0 < ⟪c' - a', b' - c⟫ := lt_of_le_of_ne hLp (Ne.symm hp0)
  left
  rcases lt_or_gt_of_ne hq0 with hq | hq
  · rcases lt_or_gt_of_ne hz0 with hz | hz
    · exact k28b4_C hC hM hrel hα hβ hσ hLp' hq hz
    · exact k28b4_B hC hM hrel hα hβ hσ hLp' hq hz
  · rcases lt_or_gt_of_ne hz0 with hz | hz
    · exact k28b4_E hC hM hrel hα hβ hσ hq hz
    · exact k28b4_D hC hM hrel hα hβ hσ hq hz

def K30LeftMN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6sMN2 a a' b b' c c' d ∧ ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧
    (RegN2 W.F → 1 < γ6) ∧
    (K30mBoundary a a' b b' c c' d α1 β1 β6 γ6 ∨
      (K6mH1Left a a' b b' c c' d α1 β1 β6 γ6 ∧ K17b2L2Left a a' b b' c c' d α1 β1 β6 γ6 ∧
        K29L2Corner a a' b b' c c' d α1 β1) ∨
      (K20mH5c a a' b b' c c' d α1 β1 β6 γ6 ∧ ⟪c' - a, b' - a⟫ ≤ 0))

theorem k30z_MN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K29LeftMN2 W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K30LeftMN2 W := by
  obtain ⟨hs, α1, β1, β6, γ6, hC, hreg, h0 | hL | ⟨h5, hT | hS⟩⟩ := h
  · rcases h0 with h0 | ⟨hβ1, hσ, hα1, ⟨hb, hLp⟩ | hg⟩
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inl (Or.inl h0)⟩
    · have hrel : K16Rel a b c d α1 β1 := by
        obtain ⟨hdet, hc', hb', ha', hα1', -, -, -, hγ6', h3⟩ := hC
        exact k16_n2_rel W hs.1 hs.2.1 hs.2.2.1 hdet hc' ha' hα1' hβ1 hγ6' h3
      subst hb
      rcases k30_b4 hC hs.2.2 hrel hα1 hβ1 hσ hLp with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨hs, α1, β1, 1, γ6, hC, hreg, Or.inl (Or.inr ⟨hβ1, hσ, hα1, Or.inl ⟨rfl, h1⟩⟩)⟩
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inl (Or.inr ⟨hβ1, hσ, hα1, Or.inr hg⟩)⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inl hL)⟩
  · have hrel : K16Rel a b c d α1 β1 := by
      obtain ⟨hdet, hc', hb', ha', hα1', -, -, -, hγ6', h3⟩ := hC
      have hβ1 : 1 < β1 := by
        obtain ⟨⟨⟨⟨⟨-, hβ, -, -, -⟩, -⟩, -, -⟩, -, -⟩, -, -⟩ := h5
        exact hβ
      exact k16_n2_rel W hs.1 hs.2.1 hs.2.2.1 hdet hc' ha' hα1' hβ1 hγ6' h3
    exact Or.inl (k28h5a0_A' hC hs.2.2 hrel h5 hT.1 hT.2)
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inr ⟨h5, hS⟩)⟩

def K30Slice {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K30LeftMN2 W ∨ K27LeftMKb W

theorem k30_slice_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : K29Slice W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K30Slice W := by
  rcases h with h | h
  · rcases k30z_MN2 W h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h)

def K30ResidP (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ W : Norm08w a a' b b' c c' d, ResP W.F d ∧ K30Slice W

def K30ResidP6 (a a' b b' c c' d : ℝ³) : Prop :=
  K30ResidP a a' b b' c c' d ∨ K30ResidP b b' a a' c c' d ∨ K30ResidP a a' c c' b b' d ∨
  K30ResidP c c' a a' b b' d ∨ K30ResidP b b' c c' a a' d ∨ K30ResidP c c' b b' a a' d

/-- **`Resid08FinalK30`**: as K29 with the β6 = 1 leaves B–E and H5 at T = 0 closed. -/
def Resid08FinalK30 (a a' b b' c c' d : ℝ³) : Prop :=
  (PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ K30ResidP6 a a' b b' c c' d ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

theorem k30_residP_step {p p' q q' r r' d : ℝ³}
    (hNR : ¬ IsRupert (V8 p p' q q' r r' d)) (h : K29ResidP p p' q q' r r' d) :
    HasLexCell (V8 p p' q q' r r' d) ∨ K30ResidP p p' q q' r r' d := by
  obtain ⟨W, hR, hs⟩ := h
  rcases k30_slice_step W hNR hs with h | h
  · exact Or.inl h
  · exact Or.inr ⟨W, hR, h⟩

theorem resid08FinalK29_imp_K30 {a a' b b' c c' d : ℝ³}
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : Resid08FinalK29 a a' b b' c c' d) :
    Resid08FinalK30 a a' b b' c c' d := by
  obtain ⟨hpl, h6, hno⟩ := h
  have e := type08_set_perm a a' b b' c c' d
  refine ⟨hpl, ?_, hno⟩
  rcases h6 with h | h | h | h | h | h
  · rcases k30_residP_step hNR h with h | h
    · exact (hno h).elim
    · exact Or.inl h
  · rcases k30_residP_step (fun hR => hNR (by rw [V8, ← e.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.1]; exact h)).elim
    · exact Or.inr (Or.inl h)
  · rcases k30_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k30_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k30_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k30_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.2]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.2]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Type08Sp
end Minimality
