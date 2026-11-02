module

public import Minimality.Type16VD
public import Minimality.Type16UW

@[expose] public section


/-! # H16/V: the wrapper with the smaller residual `H16VResid` -/
set_option autoImplicit true
set_option linter.unusedVariables false
open scoped RealInnerProductSpace
open Finset Filter

namespace Minimality
namespace H16U
open V2

variable {x : Fin 7 → ℝ³}

/-- L1 region with the one unexcluded depth pattern (peaks at 3 and 4; forces `p + r ≤ 1`, i.e. `¬hG`). -/
def H16VL1Bad (T : Type16 x) : Prop :=
  h16wZeta x < 0 ∧ 0 < h16wPhiF T ∧ 0 < h16wPhiH T ∧ H16VPat1 x
def H16VL7Bad (T : Type16 x) : Prop :=
  0 < h16wZeta x ∧ h16wPhiF T < 0 ∧ h16wPhiH T < 0 ∧ H16VPat7 x

/-- The smaller leftover of `rule_U`: `L1Bad`/`L7Bad` replaced by the single depth pattern. -/
def H16VResid (T : Type16 x) : Prop :=
  H16UWeakR3 T ∨ H16UWeakR5 T ∨ H16UTie T ∨ H16VL1Bad T ∨ H16VL7Bad T ∨ H16UTTBad T ∨
  H16UDepthTie x (x 6 - x 0) {6, 3, 5, 2, 4} ∨ H16UDepthTie x (x 0 - x 6) {0, 3, 5, 1, 4}

theorem h16v_rule_isRupert (T : Type16 x) (h : ¬ H16VResid T) : IsRupert (univ.image x) := by
  have h1 : ¬ H16UWeakR3 T := fun e => h (Or.inl e)
  have h2 : ¬ H16UWeakR5 T := fun e => h (Or.inr (Or.inl e))
  have h3 : ¬ H16UTie T := fun e => h (Or.inr (Or.inr (Or.inl e)))
  have h4 : ¬ H16VL1Bad T := fun e => h (Or.inr (Or.inr (Or.inr (Or.inl e))))
  have h5 : ¬ H16VL7Bad T := fun e => h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e)))))
  have h6 : ¬ H16UTTBad T := fun e => h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e))))))
  have h7 : ¬ H16UDepthTie x (x 6 - x 0) {6, 3, 5, 2, 4} := fun e =>
    h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e)))))))
  have h8 : ¬ H16UDepthTie x (x 0 - x 6) {0, 3, 5, 1, 4} := fun e =>
    h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr e)))))))
  have hz : h16wZeta x ≠ 0 := fun e => h3 (Or.inl e)
  have hF0 : h16wPhiF T ≠ 0 := fun e => h3 (Or.inr (Or.inl e))
  have hH0 : h16wPhiH T ≠ 0 := fun e => h3 (Or.inr (Or.inr (Or.inl e)))
  have hE10 : h16wE1 T ≠ 0 := fun e => h3 (Or.inr (Or.inr (Or.inr (Or.inl e))))
  have hE20 : h16wE2 T ≠ 0 := fun e => h3 (Or.inr (Or.inr (Or.inr (Or.inr e))))
  unfold h16wZeta at hz
  unfold h16wPhiF at hF0
  unfold h16wPhiH at hH0
  unfold H16UWeakR3 h16wZeta h16wPhiF h16wE1 at h1
  unfold H16UWeakR5 h16wZeta h16wPhiH h16wE2 at h2
  unfold H16VL1Bad h16wZeta h16wPhiF h16wPhiH at h4
  unfold H16VL7Bad h16wZeta h16wPhiF h16wPhiH at h5
  unfold H16UTTBad h16wE1 h16wE2 at h6
  have hE1 : T.ff 4 (x 5) - T.ff 4 (x 1) ≠ 0 := hE10
  have hE2 : T.ff 4 (x 5) - T.ff 4 (x 2) ≠ 0 := hE20
  -- depth facts along u = x6 - x0 on {6,3,5,2,4}
  have dA : ∀ {i j}, i ∈ ({6, 3, 5, 2, 4} : Finset (Fin 7)) → j ∈ ({6, 3, 5, 2, 4} : Finset (Fin 7)) →
      i ≠ j → ⟪x i, x 6 - x 0⟫ ≠ ⟪x j, x 6 - x 0⟫ := fun hi hj hij => h16w_ne h7 hi hj hij
  have dB : ∀ {i j}, i ∈ ({0, 3, 5, 1, 4} : Finset (Fin 7)) → j ∈ ({0, 3, 5, 1, 4} : Finset (Fin 7)) →
      i ≠ j → ⟪x i, x 0 - x 6⟫ ≠ ⟪x j, x 0 - x 6⟫ := fun hi hj hij => h16w_ne h8 hi hj hij
  rcases lt_or_gt_of_ne hz with hzl | hzg
  · rcases lt_or_gt_of_ne hF0 with hFl | hFg
    · -- phiF < 0
      rcases lt_or_gt_of_ne hE1 with hel | heg
      · exact absurd ⟨hzl, by linarith, by linarith⟩ h1
      · have hdep : ∀ r : ℝ³, r ≠ 0 → ⟪T.fN 1, r⟫ = 0 → ⟪T.fN 4, r⟫ = 0 → DepthOK x r 6 1 4 := by
          intro r hr a b
          by_contra hc
          exact h6 (Or.inl ⟨by linarith, r, hr, a, b, hc⟩)
        exact h16u_tt_LBE_isRupert T (by linarith) hdep
    · rcases lt_or_gt_of_ne hH0 with hHl | hHg
      · exact h16u_ev1_L2_isRupert T hzl hFg hHl
          (dA (by simp) (by simp) (by decide)) (dA (by simp) (by simp) (by decide))
          (dA (by simp) (by simp) (by decide)) (dA (by simp) (by simp) (by decide))
          (dA (by simp) (by simp) (by decide))
      · have hGX : ¬ H16VPat1 x := fun hc => h4 ⟨hzl, hFg, hHg, hc⟩
        exact isRupert_of_hasLexCell _ <| h16v_ev1_L1' T hzl hFg hHg hGX
          (dA (by simp) (by simp) (by decide)) (dA (by simp) (by simp) (by decide))
          (dA (by simp) (by simp) (by decide)) (dA (by simp) (by simp) (by decide))
          (dA (by simp) (by simp) (by decide)) (dA (by simp) (by simp) (by decide))
          (dA (by simp) (by simp) (by decide)) (dA (by simp) (by simp) (by decide))
          (dA (by simp) (by simp) (by decide))
  · rcases lt_or_gt_of_ne hH0 with hHl | hHg
    · rcases lt_or_gt_of_ne hF0 with hFl | hFg
      · have hGX : ¬ H16VPat7 x := fun hc => h5 ⟨hzg, hFl, hHl, hc⟩
        exact isRupert_of_hasLexCell _ <| h16v_ev1_L7' T hzg hFl hHl hGX
          (dB (by simp) (by simp) (by decide)) (dB (by simp) (by simp) (by decide))
          (dB (by simp) (by simp) (by decide)) (dB (by simp) (by simp) (by decide))
          (dB (by simp) (by simp) (by decide)) (dB (by simp) (by simp) (by decide))
          (dB (by simp) (by simp) (by decide)) (dB (by simp) (by simp) (by decide))
          (dB (by simp) (by simp) (by decide))
      · exact h16u_ev1_L6_isRupert T hzg hFg hHl
          (dB (by simp) (by simp) (by decide)) (dB (by simp) (by simp) (by decide))
          (dB (by simp) (by simp) (by decide)) (dB (by simp) (by simp) (by decide))
          (dB (by simp) (by simp) (by decide))
    · rcases lt_or_gt_of_ne hE2 with hel | heg
      · exact absurd ⟨hzg.le, hHg, by linarith⟩ h2
      · have hdep : ∀ r : ℝ³, r ≠ 0 → ⟪T.fN 0, r⟫ = 0 → ⟪T.fN 4, r⟫ = 0 → DepthOK x r 0 2 4 := by
          intro r hr a b
          by_contra hc
          exact h6 (Or.inr ⟨by linarith, r, hr, a, b, hc⟩)
        exact h16u_tt_LAE_isRupert T (by linarith) hdep

/-- Contradiction form for the skeleton. -/
theorem h16v_rule_false (hN : IsNopert (Finset.univ.image x)) (T : Type16 x)
    (h : ¬ H16VResid T) : False :=
  hN.2 (h16v_rule_isRupert T h)

end H16U
end Minimality
