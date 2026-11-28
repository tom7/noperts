module

public import Minimality.Type24T2Corner

/-!
# Lemma P0 for the type-24 cone `T_2` (`cA2`): vertex 0 the peak

`z_q = ⟪x q, ·⟫` on the rim `cA2 = ![0, 5, 3, 6, 1]`.  Lemma Z (`z₀ < z₁`) and rule
T2C all need vertex 0 NOT to be the peak.  With `z₀` the largest depth the rim is unimodal iff the arc
`5 → 3 → 6 → 1` has a single valley, i.e. (strictly) `z₆ < z₃ < z₅` (valley at 6 or 1) or `z₃ < z₆ < z₁`
(valley at 3 or 5).  Neither chain needs `z₀` to be the peak:

* `cA2_robUni_of_p0`: every view `uT2 x β γ` (`β, γ > 0`) with `P0Letter` (`z₆ < z₃ < z₅` or `z₃ < z₆ < z₁`) has
  `RobUni` depths on `cA2` under `OB1 x`.  Only Fact 1 (`uT2_depth_signs`) is used; the cell sign pattern and
  Fact 2 are not needed (the `LexAny` form `cA2_lexAny_of_p0` needs the open cell for the cell certificate).
* (The edge region `P0Edge025` and its hole facts were pruned 11-27, pass 3: see TOOLBOX-LEAN.)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Filter Topology
open Finset
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.M4
open Minimality.T24.HC Minimality.T24.SF Minimality.T24.DeepC

namespace Minimality.T24.TwoCone

/-- **P0 letters** on the depths: `z₆ < z₃ < z₅` or `z₃ < z₆ < z₁` (the vertex-0-peak branches of `cA2`). -/
def P0Letter (z1 z3 z5 z6 : ℝ) : Prop :=
  (z6 < z3 ∧ z3 < z5) ∨ (z3 < z6 ∧ z6 < z1)

/-- **Lemma P0:** under `OB1 x`, every view `uT2 x β γ` (`β, γ > 0`; the `cA2` cell is not needed) satisfying the
P0 letter has `RobUni` depths on `cA2 = ![0, 5, 3, 6, 1]`.  Only Fact 1 (`uT2_depth_signs`) is used: a crown would
need `z₀ ≤ z₁` together with `z₆ ≤ z₁`, and Fact 1 turns `z₀ ≤ z₁` into `z₁ < z₆`. -/
theorem cA2_robUni_of_p0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hO : H24K.SAT.OB1 x)
    {beta gamma : ℝ} (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hlet : P0Letter ⟪x 1, uT2 x beta gamma⟫ ⟪x 3, uT2 x beta gamma⟫ ⟪x 5, uT2 x beta gamma⟫
      ⟪x 6, uT2 x beta gamma⟫) :
    H21.RobUni (fun i => ⟪x (cA2 i), uT2 x beta gamma⟫) := by
  have hF1 : ⟪x 0, uT2 x beta gamma⟫ ≤ ⟪x 1, uT2 x beta gamma⟫ →
      ⟪x 1, uT2 x beta gamma⟫ < ⟪x 6, uT2 x beta gamma⟫ := by
    intro h
    have h0 : ⟪x 0 - x 1, uT2 x beta gamma⟫ ≤ 0 := by rw [inner_sub_left]; linarith
    have h6 := (uT2_depth_signs F hO hbeta hgamma).2 h0
    rw [inner_sub_left] at h6; linarith
  intro B b c d hb hbc hcd hdk
  have hb5 : b < 5 := by omega
  have hc5 : c < 5 := by omega
  have hd5 : d < 5 := by omega
  have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by revert B; decide
  have hZ5 :
      ((0 : ZMod 5) + 1 = 1 ∧ (0 : ZMod 5) + 2 = 2 ∧ (0 : ZMod 5) + 3 = 3 ∧ (0 : ZMod 5) + 4 = 4) ∧
      ((1 : ZMod 5) + 1 = 2 ∧ (1 : ZMod 5) + 2 = 3 ∧ (1 : ZMod 5) + 3 = 4 ∧ (1 : ZMod 5) + 4 = 0) ∧
      ((2 : ZMod 5) + 1 = 3 ∧ (2 : ZMod 5) + 2 = 4 ∧ (2 : ZMod 5) + 3 = 0 ∧ (2 : ZMod 5) + 4 = 1) ∧
      ((3 : ZMod 5) + 1 = 4 ∧ (3 : ZMod 5) + 2 = 0 ∧ (3 : ZMod 5) + 3 = 1 ∧ (3 : ZMod 5) + 4 = 2) ∧
      ((4 : ZMod 5) + 1 = 0 ∧ (4 : ZMod 5) + 2 = 1 ∧ (4 : ZMod 5) + 3 = 2 ∧ (4 : ZMod 5) + 4 = 3) := by
    decide
  have hev : cA2 0 = 0 ∧ cA2 1 = 5 ∧ cA2 2 = 3 ∧ cA2 3 = 6 ∧ cA2 4 = 1 := by decide
  rcases hB with rfl | rfl | rfl | rfl | rfl <;>
  · interval_cases b <;> interval_cases c <;> interval_cases d <;>
    · simp only [Nat.cast_one, Nat.cast_ofNat, hZ5, hev]
      rintro ⟨h1, h2, h3, h4⟩
      rcases le_or_gt ⟪x 0, uT2 x beta gamma⟫ ⟪x 1, uT2 x beta gamma⟫ with hc | hc
      · have h6' := hF1 hc
        rcases hlet with ⟨l1, l2⟩ | ⟨l1, l2⟩ <;> linarith
      · rcases hlet with ⟨l1, l2⟩ | ⟨l1, l2⟩ <;> linarith

/-- **Lemma P0 (`LexAny` form):** `cA2` open cell + `OB1` + the P0 letter gives `Gen.LexAny F`. -/
theorem cA2_lexAny_of_p0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hO : H24K.SAT.OB1 x)
    {beta gamma : ℝ} (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hcell : CellAt F U_A2 D_A2 (uT2 x beta gamma))
    (hlet : P0Letter ⟪x 1, uT2 x beta gamma⟫ ⟪x 3, uT2 x beta gamma⟫ ⟪x 5, uT2 x beta gamma⟫
      ⟪x 6, uT2 x beta gamma⟫) :
    Gen.LexAny F :=
  WC.lexAny_of_cellAt_robUni (by norm_num) F cA2_inj cA2_cyc hcell
    (cA2_robUni_of_p0 F hO hbeta hgamma hlet)

end Minimality.T24.TwoCone
