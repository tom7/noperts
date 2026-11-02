module

public import Minimality.Type08S.C2K25ZA
public import Minimality.Type08S.C2K22Z1C1bB
public import Minimality.Type08S.C2K22Z1C3B
public import Minimality.Type08S.C2K22Z1GC2B
public import Minimality.Type08S.C2K22Z1GC4B

/-!
# K26 / Z: Tc Z1 closed (cells C1, C3, and C2/C4 at the corner γ4 = 1; specs specpos/C2/K22Z1, K22Z1G).
-/
@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- **Tc Z1 closed**: S2 ≤ 0 by C1; S2 > 0: γ4 > 1 by C3, γ4 = 1 by C2 (S3 ≤ 0) or C4 (S3 > 0). -/
theorem k22z1_close {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K17hTcZ1 a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) := by
  rcases le_or_gt ⟪b - a, a - c'⟫ 0 with hS | hS
  · exact k22z1_c1_le W h hS
  obtain ⟨hK, hOC, hOB, hOA⟩ := id h
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα11, hα41, hβ1, hγ4p, hb6, hrel, hE0⟩ :=
    k17ga_tc_coords W hK
  have hq0 : b - d ≠ 0 := by intro h0; apply hdet; rw [h0]; simp [det3_expand]
  have hqq : 0 < ⟪b - d, b - d⟫ := real_inner_self_pos.2 hq0
  have hqp : ⟪b - d, a - d⟫ = 0 := by rw [real_inner_comm]; exact hOA
  have hβ11 : β1 = 1 := by
    have e1 : d - b = -(b - d) := by module
    have e2 : c' - b = α1 • (a - d) + (β1 - 1) • (b - d) := by rw [hc']; module
    rw [e1, e2] at hOB
    simp only [inner_neg_left, inner_add_right, inner_smul_right, hqp] at hOB
    have : (β1 - 1) * ⟪b - d, b - d⟫ = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h hqq.ne'
  have hγge : 1 ≤ γ4 := by
    rw [hβ11] at hE0; nlinarith
  -- uniqueness of the c - d coordinate of b'
  have uγ : ∀ α γ : ℝ, b' = d + α • (a - d) + γ • (c - d) → γ = γ4 := by
    intro α γ e
    have hxy : (α - α4) • (a - d) + (γ - γ4) • (c - d) = 0 := by
      have := e.symm.trans hb'
      rw [sub_smul, sub_smul]
      have h2 : α • (a - d) + γ • (c - d) = α4 • (a - d) + γ4 • (c - d) := by
        have := congrArg (fun v => v - d) this; simp only [add_sub_cancel_left, add_assoc] at this; exact this
      rw [← sub_eq_zero] at h2; rw [← h2]; abel
    have hdx : det3 (a - d) (b - d) ((α - α4) • (a - d) + (γ - γ4) • (c - d)) =
        (γ - γ4) * det3 (a - d) (b - d) (c - d) := by
      simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [hxy] at hdx
    have h0 : det3 (a - d) (b - d) (0 : ℝ³) = 0 := by simp [det3_expand]
    rw [h0] at hdx
    rcases mul_eq_zero.1 hdx.symm with h | h
    · linarith
    · exact absurd h hdet
  rcases hγge.lt_or_eq with hg | hg
  · exact k22z1_c3_strict W h hS (fun α γ e => by rw [uγ α γ e]; exact hg)
  · have hγ1 : ∀ α γ : ℝ, b' = d + α • (a - d) + γ • (c - d) → γ = 1 := fun α γ e => by rw [uγ α γ e]; exact hg.symm
    rcases le_or_gt ⟪a' - b, a - c'⟫ 0 with h3 | h3
    · exact k22z1g_c2 W h hγ1 hS h3
    · exact k22z1g_c4 W h hγ1 hS h3

end C2

def K26Slice {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K22LeftMN2 W ∨ K22LeftMKb W

theorem k26_slice_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : K25Slice W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K26Slice W := by
  rcases h with h | h
  · exact Or.inl (C2.k22z1_close W h)
  · exact Or.inr h

def K26ResidP (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ W : Norm08w a a' b b' c c' d, ResP W.F d ∧ K26Slice W

def K26ResidP6 (a a' b b' c c' d : ℝ³) : Prop :=
  K26ResidP a a' b b' c c' d ∨ K26ResidP b b' a a' c c' d ∨ K26ResidP a a' c c' b b' d ∨
  K26ResidP c c' a a' b b' d ∨ K26ResidP b b' c c' a a' d ∨ K26ResidP c c' b b' a a' d

/-- **`Resid08FinalK26`**: as K25 with Tc Z1 closed (`k22z1_close`); only the M stratum is left. -/
def Resid08FinalK26 (a a' b b' c c' d : ℝ³) : Prop :=
  (PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ K26ResidP6 a a' b b' c c' d ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

theorem k26_residP_step {p p' q q' r r' d : ℝ³}
    (hNR : ¬ IsRupert (V8 p p' q q' r r' d)) (h : K25ResidP p p' q q' r r' d) :
    HasLexCell (V8 p p' q q' r r' d) ∨ K26ResidP p p' q q' r r' d := by
  obtain ⟨W, hR, hs⟩ := h
  rcases k26_slice_step W hNR hs with h | h
  · exact Or.inl h
  · exact Or.inr ⟨W, hR, h⟩

theorem resid08FinalK25_imp_K26 {a a' b b' c c' d : ℝ³}
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : Resid08FinalK25 a a' b b' c c' d) :
    Resid08FinalK26 a a' b b' c c' d := by
  obtain ⟨hpl, h6, hno⟩ := h
  have e := type08_set_perm a a' b b' c c' d
  refine ⟨hpl, ?_, hno⟩
  rcases h6 with h | h | h | h | h | h
  · rcases k26_residP_step hNR h with h | h
    · exact (hno h).elim
    · exact Or.inl h
  · rcases k26_residP_step (fun hR => hNR (by rw [V8, ← e.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.1]; exact h)).elim
    · exact Or.inr (Or.inl h)
  · rcases k26_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k26_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k26_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k26_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.2]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.2]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Type08Sp
end Minimality
