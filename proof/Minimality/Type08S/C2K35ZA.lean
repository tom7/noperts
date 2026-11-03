module

public import Minimality.Type08S.C2K34ZA
public import Minimality.Type08S.C2K35BB
public import Minimality.Type08S.C2K35D1
public import Minimality.Type08S.C2K35D2
public import Minimality.Type08S.C2K35HB

/-!
# K35 / Z: M stratum (N2 side), H5 residue on S = ⟪c'-a, b'-a⟫ < 0: cell B (`k28h5_B`, specpos/C2/K28H5LB) with all
its side facts proved: hd1, hd2 (Handelman certificates, K28H5BD), H1 = `k28h5rb_hrb` rescaled, H2, H3 (LP
certificates after a hand step eliminating pp, pq; K28H5H23). Left of the H5 residue: S = 0.
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

theorem k35_h5B {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (h5 : K20mH5c a a' b b' c c' d α1 β1 β6 γ6)
    (hS : ⟪c' - a, b' - a⟫ < 0) : HasLexCell (V8 a a' b b' c c' d) := by
  have hd1 := k28h5b_hd1 hC hM hrel h5
  have hd2 := k28h5b_hd2 hC hM hrel h5
  have hβ1 : 1 < β1 := by
    obtain ⟨⟨⟨⟨⟨-, hβ, -, -, -⟩, -⟩, -, -⟩, -, -⟩, -, -⟩ := h5
    exact hβ
  have hE : 0 < ⟪c' - a, c' - a⟫ := by
    rcases (real_inner_self_nonneg (x := c' - a)).lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 : c' - a = 0 := inner_self_eq_zero.mp h.symm
      rw [h0] at hd1
      simp at hd1
  have hr := k28h5rb_hrb hC hM hrel h5 _ _ rfl rfl
  have H1 : 0 < γ6 * (α1 + β1 - 1) * ⟪c' - a, b' - a⟫ +
      (α1 * β1 * (γ6 + β6 - 1) - γ6 * (α1 + β1 - 1)) * ⟪c' - a, c' - a⟫ := by
    have hb0 : (0 : ℝ) < β1 := by linarith
    have key : γ6 * (α1 + β1 - 1) * ⟪c' - a, b' - a⟫ +
        (α1 * β1 * (γ6 + β6 - 1) - γ6 * (α1 + β1 - 1)) * ⟪c' - a, c' - a⟫ =
        (β1 * ⟪c' - a, c' - a⟫) * (γ6 * ((α1 - 1) * (1 - ⟪c' - a, b' - a⟫ / ⟪c' - a, c' - a⟫) / β1) *
          (β1 - 1) + α1 * (β6 + γ6 * (⟪c' - a, b' - a⟫ / ⟪c' - a, c' - a⟫) - 1)) := by
      field_simp
      ring
    rw [key]
    exact mul_pos (mul_pos hb0 hE) hr
  obtain ⟨H2, H3⟩ := k28h5b_H23 hC hM hrel h5
  exact k28h5_B hC hM hrel h5 hS hd1 hd2 H1 H2 H3

def K35LeftMN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6sMN2 a a' b b' c c' d ∧ ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧
    (RegN2 W.F → 1 < γ6) ∧
    (K34mBoundary a a' b b' c c' d α1 β1 β6 γ6 ∨
      (K6mH1Left a a' b b' c c' d α1 β1 β6 γ6 ∧ K17b2L2Left a a' b b' c c' d α1 β1 β6 γ6 ∧
        K33L2Corner a a' b b' c c' d α1 β1) ∨
      (K20mH5c a a' b b' c c' d α1 β1 β6 γ6 ∧ ⟪c' - a, b' - a⟫ = 0))

theorem k35z_MN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K34LeftMN2 W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K35LeftMN2 W := by
  obtain ⟨hs, α1, β1, β6, γ6, hC, hreg, h0 | hL | ⟨h5, hS⟩⟩ := h
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inl h0⟩
  · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inl hL)⟩
  · rcases lt_or_eq_of_le hS with hS | hS
    · have hrel : K16Rel a b c d α1 β1 := by
        obtain ⟨hdet, hc', hb', ha', hα1', -, -, -, hγ6', h3⟩ := hC
        have hβ1 : 1 < β1 := by
          obtain ⟨⟨⟨⟨⟨-, hβ, -, -, -⟩, -⟩, -, -⟩, -, -⟩, -, -⟩ := h5
          exact hβ
        exact k16_n2_rel W hs.1 hs.2.1 hs.2.2.1 hdet hc' ha' hα1' hβ1 hγ6' h3
      exact Or.inl (k35_h5B hC hs.2.2 hrel h5 hS)
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inr ⟨h5, hS⟩)⟩

def K35Slice {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K35LeftMN2 W ∨ K27LeftMKb W

theorem k35_slice_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : K34Slice W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K35Slice W := by
  rcases h with h | h
  · rcases k35z_MN2 W h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h)

def K35ResidP (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ W : Norm08w a a' b b' c c' d, ResP W.F d ∧ K35Slice W

def K35ResidP6 (a a' b b' c c' d : ℝ³) : Prop :=
  K35ResidP a a' b b' c c' d ∨ K35ResidP b b' a a' c c' d ∨ K35ResidP a a' c c' b b' d ∨
  K35ResidP c c' a a' b b' d ∨ K35ResidP b b' c c' a a' d ∨ K35ResidP c c' b b' a a' d

/-- **`Resid08FinalK35`**: as K34 with H5 cell B (S < 0) closed. -/
def Resid08FinalK35 (a a' b b' c c' d : ℝ³) : Prop :=
  (PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ K35ResidP6 a a' b b' c c' d ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

theorem k35_residP_step {p p' q q' r r' d : ℝ³}
    (hNR : ¬ IsRupert (V8 p p' q q' r r' d)) (h : K34ResidP p p' q q' r r' d) :
    HasLexCell (V8 p p' q q' r r' d) ∨ K35ResidP p p' q q' r r' d := by
  obtain ⟨W, hR, hs⟩ := h
  rcases k35_slice_step W hNR hs with h | h
  · exact Or.inl h
  · exact Or.inr ⟨W, hR, h⟩

theorem resid08FinalK34_imp_K35 {a a' b b' c c' d : ℝ³}
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : Resid08FinalK34 a a' b b' c c' d) :
    Resid08FinalK35 a a' b b' c c' d := by
  obtain ⟨hpl, h6, hno⟩ := h
  have e := type08_set_perm a a' b b' c c' d
  refine ⟨hpl, ?_, hno⟩
  rcases h6 with h | h | h | h | h | h
  · rcases k35_residP_step hNR h with h | h
    · exact (hno h).elim
    · exact Or.inl h
  · rcases k35_residP_step (fun hR => hNR (by rw [V8, ← e.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.1]; exact h)).elim
    · exact Or.inr (Or.inl h)
  · rcases k35_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k35_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k35_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k35_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.2]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.2]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Type08Sp
end Minimality
