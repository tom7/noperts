module

public import Minimality.Type16UM
public import Minimality.Type16Ties

@[expose] public section


/-!
# H16W: the rule_U wrapper.  `H16UResid` = leftover of the sigma-symmetric lex-cell rule, `h16u_rule_isRupert`.
-/

set_option autoImplicit true
set_option linter.unusedVariables false
open scoped RealInnerProductSpace
open Finset Filter

namespace Minimality
namespace H16U
open V2

variable {x : Fin 7 → ℝ³}

/-- The literals of the rule (`T.ff 4/5/7` = facets E/F/H). -/
noncomputable def h16wZeta (x : Fin 7 → ℝ³) : ℝ := ⟪x 5 - x 3, x 6 - x 0⟫
noncomputable def h16wPhiF (T : Type16 x) : ℝ := T.ff 5 (x 6) - T.ff 5 (x 0)
noncomputable def h16wPhiH (T : Type16 x) : ℝ := T.ff 7 (x 6) - T.ff 7 (x 0)
noncomputable def h16wE1 (T : Type16 x) : ℝ := T.ff 4 (x 5) - T.ff 4 (x 1)
noncomputable def h16wE2 (T : Type16 x) : ℝ := T.ff 4 (x 5) - T.ff 4 (x 2)

/-- The weak box `R3` (leaf LEF). -/
def H16UWeakR3 (T : Type16 x) : Prop := h16wZeta x < 0 ∧ h16wPhiF T ≤ 0 ∧ h16wE1 T ≤ 0
/-- The weak box `R5 = sigma R3` (leaf LEH). -/
def H16UWeakR5 (T : Type16 x) : Prop := 0 ≤ h16wZeta x ∧ 0 < h16wPhiH T ∧ h16wE2 T ≤ 0
/-- Some literal of the rule vanishes (includes the `zeta = 0` tie). -/
def H16UTie (T : Type16 x) : Prop :=
  h16wZeta x = 0 ∨ h16wPhiF T = 0 ∨ h16wPhiH T = 0 ∨ h16wE1 T = 0 ∨ h16wE2 T = 0
/-- Leaf L1 region, but `hG` or `hX` fails. -/
def H16UL1Bad (T : Type16 x) : Prop :=
  h16wZeta x < 0 ∧ 0 < h16wPhiF T ∧ 0 < h16wPhiH T ∧
    ¬ (T.ff 4 (x 5) < T.ff 4 (x 3) ∧ ⟪x 0, x 6 - x 0⟫ ≤ ⟪x 3, x 6 - x 0⟫)
/-- Leaf L7 region, but `hG` or `hX` fails. -/
def H16UL7Bad (T : Type16 x) : Prop :=
  0 < h16wZeta x ∧ h16wPhiF T < 0 ∧ h16wPhiH T < 0 ∧
    ¬ (T.ff 4 (x 5) < T.ff 4 (x 3) ∧ ⟪x 6, x 0 - x 6⟫ ≤ ⟪x 3, x 0 - x 6⟫)
/-- Two depths tie along `u` among the points `S`. -/
def H16UDepthTie (x : Fin 7 → ℝ³) (u : ℝ³) (S : Finset (Fin 7)) : Prop :=
  ¬ Set.InjOn (fun i => ⟪x i, u⟫) (S : Set (Fin 7))
/-- A `DepthOK` failure of the TT leaves (`LBE`, `LAE`). -/
def H16UTTBad (T : Type16 x) : Prop :=
  (0 < h16wE1 T ∧ ∃ r : ℝ³, r ≠ 0 ∧ ⟪T.fN 1, r⟫ = 0 ∧ ⟪T.fN 4, r⟫ = 0 ∧ ¬ DepthOK x r 6 1 4) ∨
  (0 < h16wE2 T ∧ ∃ r : ℝ³, r ≠ 0 ∧ ⟪T.fN 0, r⟫ = 0 ∧ ⟪T.fN 4, r⟫ = 0 ∧ ¬ DepthOK x r 0 2 4)

/-- The leftover of the rule `rule_U`. -/
def H16UResid (T : Type16 x) : Prop :=
  H16UWeakR3 T ∨ H16UWeakR5 T ∨ H16UTie T ∨ H16UL1Bad T ∨ H16UL7Bad T ∨ H16UTTBad T ∨
  H16UDepthTie x (x 6 - x 0) {6, 3, 5, 2, 4} ∨ H16UDepthTie x (x 0 - x 6) {0, 3, 5, 1, 4}

theorem h16w_ne {u : ℝ³} {S : Finset (Fin 7)} (h : ¬ H16UDepthTie x u S) {i j : Fin 7}
    (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j) : ⟪x i, u⟫ ≠ ⟪x j, u⟫ :=
  fun e => hij ((not_not.mp h) hi hj e)

theorem h16u_rule_isRupert (T : Type16 x) (h : ¬ H16UResid T) : IsRupert (univ.image x) := by
  have h1 : ¬ H16UWeakR3 T := fun e => h (Or.inl e)
  have h2 : ¬ H16UWeakR5 T := fun e => h (Or.inr (Or.inl e))
  have h3 : ¬ H16UTie T := fun e => h (Or.inr (Or.inr (Or.inl e)))
  have h4 : ¬ H16UL1Bad T := fun e => h (Or.inr (Or.inr (Or.inr (Or.inl e))))
  have h5 : ¬ H16UL7Bad T := fun e => h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e)))))
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
  unfold H16UL1Bad h16wZeta h16wPhiF h16wPhiH at h4
  unfold H16UL7Bad h16wZeta h16wPhiF h16wPhiH at h5
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
      · have hGX : T.ff 4 (x 5) < T.ff 4 (x 3) ∧ ⟪x 0, x 6 - x 0⟫ ≤ ⟪x 3, x 6 - x 0⟫ := by
          by_contra hc; exact h4 ⟨hzl, hFg, hHg, hc⟩
        exact h16u_ev1_L1_isRupert T hzl hFg hHg hGX.1 hGX.2
          (dA (by simp) (by simp) (by decide)) (dA (by simp) (by simp) (by decide))
          (dA (by simp) (by simp) (by decide)) (dA (by simp) (by simp) (by decide))
          (dA (by simp) (by simp) (by decide)) (dA (by simp) (by simp) (by decide))
          (dA (by simp) (by simp) (by decide)) (dA (by simp) (by simp) (by decide))
          (dA (by simp) (by simp) (by decide))
  · rcases lt_or_gt_of_ne hH0 with hHl | hHg
    · rcases lt_or_gt_of_ne hF0 with hFl | hFg
      · have hGX : T.ff 4 (x 5) < T.ff 4 (x 3) ∧ ⟪x 6, x 0 - x 6⟫ ≤ ⟪x 3, x 0 - x 6⟫ := by
          by_contra hc; exact h5 ⟨hzg, hFl, hHl, hc⟩
        exact h16u_ev1_L7_isRupert T hzg hFl hHl hGX.1 hGX.2
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

/-- The skeleton's `Type16 x` from the eight facet functionals (as in `Type16Ties`). -/
noncomputable def h16w_mkType16 (hx : Function.Injective x)
    (fA fB fC fD fE fF fG fH : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 2, 3, 5} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 2, 3, 5} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({1, 3, 5, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({1, 3, 5, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hC : ∀ i, (i ∈ ({0, 2, 4} : Finset (Fin 7)) → fC (x i) = 0) ∧
      (i ∉ ({0, 2, 4} : Finset (Fin 7)) → fC (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 3, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 3, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({0, 4, 6} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({0, 4, 6} : Finset (Fin 7)) → fE (x i) < 0))
    (hF : ∀ i, (i ∈ ({1, 4, 5} : Finset (Fin 7)) → fF (x i) = 0) ∧
      (i ∉ ({1, 4, 5} : Finset (Fin 7)) → fF (x i) < 0))
    (hG : ∀ i, (i ∈ ({1, 4, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({1, 4, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hH : ∀ i, (i ∈ ({2, 4, 5} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({2, 4, 5} : Finset (Fin 7)) → fH (x i) < 0)) : Type16 x :=
  ⟨hx, Face16.ofAffine fA hA, Face16.ofAffine fB hB, Face16.ofAffine fC hC,
    Face16.ofAffine fD hD, Face16.ofAffine fE hE, Face16.ofAffine fF hF, Face16.ofAffine fG hG,
    Face16.ofAffine fH hH⟩

/-- Contradiction form for the skeleton. -/
theorem h16u_rule_false (hN : IsNopert (Finset.univ.image x)) (T : Type16 x)
    (h : ¬ H16UResid T) : False :=
  hN.2 (h16u_rule_isRupert T h)

end H16U
end Minimality
