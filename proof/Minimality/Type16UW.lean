module

public import Minimality.Type16UM
public import Minimality.Cases

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
/-- Two depths tie along `u` among the points `S`. -/
def H16UDepthTie (x : Fin 7 → ℝ³) (u : ℝ³) (S : Finset (Fin 7)) : Prop :=
  ¬ Set.InjOn (fun i => ⟪x i, u⟫) (S : Set (Fin 7))
/-- A `DepthOK` failure of the TT leaves (`LBE`, `LAE`). -/
def H16UTTBad (T : Type16 x) : Prop :=
  (0 < h16wE1 T ∧ ∃ r : ℝ³, r ≠ 0 ∧ ⟪T.fN 1, r⟫ = 0 ∧ ⟪T.fN 4, r⟫ = 0 ∧ ¬ DepthOK x r 6 1 4) ∨
  (0 < h16wE2 T ∧ ∃ r : ℝ³, r ≠ 0 ∧ ⟪T.fN 0, r⟫ = 0 ∧ ⟪T.fN 4, r⟫ = 0 ∧ ¬ DepthOK x r 0 2 4)

theorem h16w_ne {u : ℝ³} {S : Finset (Fin 7)} (h : ¬ H16UDepthTie x u S) {i j : Fin 7}
    (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j) : ⟪x i, u⟫ ≠ ⟪x j, u⟫ :=
  fun e => hij ((not_not.mp h) hi hj e)

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

end H16U
end Minimality
