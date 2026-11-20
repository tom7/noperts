module

public import Minimality.Sym24
public import Minimality.RX16
public import Minimality.RF0345
public import Minimality.RF0345N
public import Minimality.Type24SAT.K24.Wire24Res
public import Minimality.Q45

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT
open Minimality.T24.Q45 Minimality.T24.R012 Minimality.T24.R046 Minimality.T24.RX16 Minimality.T24.Sym

namespace Minimality.T24

/-- Inside the closed `C̄` region: `ω3, ω4, ω5 > 0` and `Δ24 ≥ 0`
(complement of `not_type24_outside_Cbar_of_isNopert` / `isRupert_type24_outside_Cbar`, `Type24.lean`). -/
def CbarIn (x : Fin 7 → ℝ³) : Prop :=
  0 < Minimality.omega3 x ∧ 0 < Minimality.omega4 x ∧ 0 < Minimality.omega5 x ∧
    0 ≤ Minimality.Delta24 x

/-- Universal `Q45HalfHyp` over all positive Lemma-M decompositions `x 3 - x 0 = s (x 4 - x 0) + t (x 5 - x 0)`
with `1 < s + t`. -/
def Q45HalfPred {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∀ s t : ℝ, 0 < s → 0 < t → 1 < s + t →
    x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0) → Q45HalfHyp F s t

/-- Region `R`: `C̄ ∩ OB1` with `¬ Q45HalfPred F`. -/
def Hole24R (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  CbarIn x ∧ H24K.SAT.OB1 x ∧ ¬ Q45HalfPred F

/-- Closed `C̄` outside `Q45HalfPred` (with or without `OB1`). -/
def Hole24NoQ45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  CbarIn x ∧ ¬ Q45HalfPred F

namespace RDispatch

variable {x : Fin 7 → ℝ³}

/-- Strict OB1 condition (`G_ij < 0` for all three pairs). -/
def OB1strict (x : Fin 7 → ℝ³) : Prop :=
  ⟪x 0 - x 1, x 2 - x 1⟫ < 0 ∧ ⟪x 0 - x 1, x 6 - x 1⟫ < 0 ∧ ⟪x 2 - x 1, x 6 - x 1⟫ < 0

/-- Canonical `u45` coefficients making `⟪x 4, u_Pi x α β⟫ = ⟪x 5, u_Pi x α β⟫`. -/
noncomputable def tieAlpha (x : Fin 7 → ℝ³) : ℝ := ⟪x 4 - x 5, x 4 - x 0⟫
/-- Canonical `u45` coefficients making `⟪x 4, u_Pi x α β⟫ = ⟪x 5, u_Pi x α β⟫`. -/
noncomputable def tieBeta (x : Fin 7 → ℝ³) : ℝ := -⟪x 4 - x 5, x 5 - x 0⟫

/-! ### Per-leaf Case, Gen, and H bundles (20 base leaves + 20 `Sym24` mirrors) -/

-- 1. q012_w3_pos
def Case_w3p (F : S0xFac 9 s0x_S24 x) : Prop :=
  0 < omega3_012 F ∧ ⟪F.N 4, u0 x (omega3_012 F)⟫ < 0 ∧ 0 < ⟪F.N 3, u0 x (omega3_012 F)⟫ ∧
  0 < ⟪F.N 8, u0 x (omega3_012 F)⟫ ∧
  min ⟪x 4, u0 x (omega3_012 F)⟫ ⟪x 2, u0 x (omega3_012 F)⟫ <
    max ⟪x 0, u0 x (omega3_012 F)⟫ ⟪x 6, u0 x (omega3_012 F)⟫

def Gen_w3p (F : S0xFac 9 s0x_S24 x) : Prop :=
  F.f 0 (x 4) ≠ F.f 0 (x 6) ∧
  (F.f 0 (x 4) < F.f 0 (x 6) → Off012 F 4) ∧
  (F.f 0 (x 6) < F.f 0 (x 4) → Off012 F 6) ∧
  Gen4 (quad (x 0) (x 4) (x 6) (x 2)) (u0 x (omega3_012 F)) (x 2 - x 1)

/-- Hypothesis bundle for `Minimality.T24.R012.q012_w3_pos`. -/
def H_w3p (F : S0xFac 9 s0x_S24 x) : Prop := Case_w3p F ∧ Gen_w3p F

-- 2. q012_w3_neg_A
def Case_w3nA (F : S0xFac 9 s0x_S24 x) : Prop :=
  0 < omega3_012 F ∧ ⟪F.N 4, u0 x (omega3_012 F)⟫ < 0 ∧ 0 < ⟪F.N 3, u0 x (omega3_012 F)⟫ ∧
  0 < ⟪F.N 6, u0 x (omega3_012 F)⟫ ∧ ⟪F.N 8, u0 x (omega3_012 F)⟫ < 0 ∧
  min ⟪x 0, u0 x (omega3_012 F)⟫ ⟪x 3, u0 x (omega3_012 F)⟫ <
    max ⟪x 4, u0 x (omega3_012 F)⟫ ⟪x 2, u0 x (omega3_012 F)⟫

def Gen_w3nA (F : S0xFac 9 s0x_S24 x) : Prop :=
  F.f 0 (x 4) ≠ F.f 0 (x 3) ∧
  (F.f 0 (x 4) < F.f 0 (x 3) → Off012 F 4) ∧
  (F.f 0 (x 3) < F.f 0 (x 4) → Off012 F 3) ∧
  Gen4 (quad (x 0) (x 4) (x 3) (x 2)) (u0 x (omega3_012 F)) (x 2 - x 1)

/-- Hypothesis bundle for `Minimality.T24.R012.q012_w3_neg_A`. -/
def H_w3nA (F : S0xFac 9 s0x_S24 x) : Prop := Case_w3nA F ∧ Gen_w3nA F

-- 3. q012_w3_neg_B
def Case_w3nB (F : S0xFac 9 s0x_S24 x) : Prop :=
  0 < omega3_012 F ∧ ⟪F.N 3, u0 x (omega3_012 F)⟫ < 0 ∧ 0 < ⟪F.N 6, u0 x (omega3_012 F)⟫ ∧
  min ⟪x 5, u0 x (omega3_012 F)⟫ ⟪x 2, u0 x (omega3_012 F)⟫ <
    max ⟪x 0, u0 x (omega3_012 F)⟫ ⟪x 3, u0 x (omega3_012 F)⟫

def Gen_w3nB (F : S0xFac 9 s0x_S24 x) : Prop :=
  F.f 0 (x 5) ≠ F.f 0 (x 3) ∧
  (F.f 0 (x 5) < F.f 0 (x 3) → Off012 F 5) ∧
  (F.f 0 (x 3) < F.f 0 (x 5) → Off012 F 3) ∧
  Gen4 (quad (x 0) (x 5) (x 3) (x 2)) (u0 x (omega3_012 F)) (x 2 - x 1)

/-- Hypothesis bundle for `Minimality.T24.R012.q012_w3_neg_B`. -/
def H_w3nB (F : S0xFac 9 s0x_S24 x) : Prop := Case_w3nB F ∧ Gen_w3nB F

-- 4. q012_w4_neg
def Case_w4n (F : S0xFac 9 s0x_S24 x) : Prop :=
  0 < omega4_012 F ∧ ⟪F.N 7, u0 x (inv_omega4_012 F)⟫ < 0 ∧
  0 < ⟪F.N 6, u0 x (inv_omega4_012 F)⟫ ∧ 0 < ⟪F.N 8, u0 x (inv_omega4_012 F)⟫ ∧
  min ⟪x 0, u0 x (inv_omega4_012 F)⟫ ⟪x 3, u0 x (inv_omega4_012 F)⟫ <
    max ⟪x 6, u0 x (inv_omega4_012 F)⟫ ⟪x 2, u0 x (inv_omega4_012 F)⟫

def Gen_w4n (F : S0xFac 9 s0x_S24 x) : Prop :=
  F.f 0 (x 6) ≠ F.f 0 (x 3) ∧
  (F.f 0 (x 6) < F.f 0 (x 3) → Off012 F 6) ∧
  (F.f 0 (x 3) < F.f 0 (x 6) → Off012 F 3) ∧
  Gen4 (quad (x 0) (x 6) (x 3) (x 2)) (u0 x (inv_omega4_012 F)) (x 2 - x 1)

/-- Hypothesis bundle for `Minimality.T24.R012.q012_w4_neg`. -/
def H_w4n (F : S0xFac 9 s0x_S24 x) : Prop := Case_w4n F ∧ Gen_w4n F

-- 5. q012_f346_pos_A_4
def Case_f346A (F : S0xFac 9 s0x_S24 x) : Prop :=
  F.f 0 (x 3) < F.f 0 (x 6) ∧ F.f 0 (x 6) < F.f 0 (x 4) ∧
  0 < ⟪F.N 6, u08 F⟫ ∧ F.f 8 (x 2) < F.f 8 (x 1) ∧
  min ⟪x 0, u08 F⟫ ⟪x 3, u08 F⟫ < max ⟪x 4, u08 F⟫ ⟪x 2, u08 F⟫

def Gen_f346A (F : S0xFac 9 s0x_S24 x) : Prop :=
  (∀ i j : ZMod 4, i ≠ j →
    ⟪quad (x 0) (x 4) (x 3) (x 2) i - quad (x 0) (x 4) (x 3) (x 2) j, u08 F⟫ ≠ 0 ∨
    ⟪quad (x 0) (x 4) (x 3) (x 2) i - quad (x 0) (x 4) (x 3) (x 2) j, x 2 - x 1⟫ ≠ 0) ∧
  (⟪F.N 0, cross (x 0 - x 2) (x 3 - x 2)⟫ ≠ 0 ∨
    ⟪x 3 - x 2, x 0 - x 2⟫ < 0 ∨ ⟪x 3 - x 0, x 2 - x 0⟫ < 0)

/-- Hypothesis bundle for `Minimality.T24.R012.q012_f346_pos_A_4`. -/
def H_f346A (F : S0xFac 9 s0x_S24 x) : Prop := Case_f346A F ∧ Gen_f346A F

-- 6. q012_f346_B_4
def Case_f346B (F : S0xFac 9 s0x_S24 x) : Prop :=
  F.f 0 (x 4) < F.f 0 (x 6) ∧ F.f 0 (x 6) < F.f 0 (x 3) ∧
  0 < ⟪F.N 6, -u08 F⟫ ∧ F.f 8 (x 1) < F.f 8 (x 2) ∧
  min ⟪x 0, -u08 F⟫ ⟪x 3, -u08 F⟫ < max ⟪x 4, -u08 F⟫ ⟪x 2, -u08 F⟫

def Gen_f346B (F : S0xFac 9 s0x_S24 x) : Prop :=
  (∀ i j : ZMod 4, i ≠ j →
    ⟪quad (x 0) (x 4) (x 3) (x 2) i - quad (x 0) (x 4) (x 3) (x 2) j, -u08 F⟫ ≠ 0 ∨
    ⟪quad (x 0) (x 4) (x 3) (x 2) i - quad (x 0) (x 4) (x 3) (x 2) j, x 1 - x 2⟫ ≠ 0) ∧
  (⟪F.N 0, cross (x 0 - x 2) (x 4 - x 2)⟫ ≠ 0 ∨
    ⟪x 4 - x 2, x 0 - x 2⟫ < 0 ∨ ⟪x 4 - x 0, x 2 - x 0⟫ < 0)

/-- Hypothesis bundle for `Minimality.T24.R012.q012_f346_B_4`. -/
def H_f346B (F : S0xFac 9 s0x_S24 x) : Prop := Case_f346B F ∧ Gen_f346B F

-- 7. q012_LC_plus_gen
def Case_LCp (F : S0xFac 9 s0x_S24 x) : Prop :=
  0 < t_LC x ∧ ⟪F.N 4, u_LC x⟫ < 0 ∧ ⟪F.N 7, u_LC x⟫ < 0 ∧
  0 < ⟪F.N 6, u_LC x⟫ ∧ 0 < ⟪F.N 3, u_LC x⟫ ∧ 0 < ⟪F.N 8, u_LC x⟫ ∧
  ⟪x 4, u_LC x⟫ < ⟪x 0, u_LC x⟫ ∧ ⟪x 0 - x 2, x 2 - x 1⟫ < 0

def Gen_LCp (F : S0xFac 9 s0x_S24 x) : Prop :=
  FarOff012 F ∧ SingleAdjacentTie (fun i => x (rim012 i)) (u_LC x) 4

/-- Hypothesis bundle for `Minimality.T24.R012.q012_LC_plus_gen`. -/
def H_LCp (F : S0xFac 9 s0x_S24 x) : Prop := Case_LCp F ∧ Gen_LCp F

-- 8. q012_LC_minus_gen
def Case_LCm (F : S0xFac 9 s0x_S24 x) : Prop :=
  0 < t_LC x ∧ ⟪F.N 4, u_LC x⟫ < 0 ∧ ⟪F.N 7, u_LC x⟫ < 0 ∧
  0 < ⟪F.N 6, u_LC x⟫ ∧ 0 < ⟪F.N 3, u_LC x⟫ ∧ 0 < ⟪F.N 8, u_LC x⟫ ∧
  ⟪x 3, u_LC x⟫ < ⟪x 0, u_LC x⟫ ∧ ⟪x 0 - x 2, x 2 - x 1⟫ < 0

def Gen_LCm (F : S0xFac 9 s0x_S24 x) : Prop :=
  FarOff012 F ∧ SingleAdjacentTie (fun i => x (rim012 i)) (u_LC x) 4

/-- Hypothesis bundle for `Minimality.T24.R012.q012_LC_minus_gen`. -/
def H_LCm (F : S0xFac 9 s0x_S24 x) : Prop := Case_LCm F ∧ Gen_LCm F

-- 9. m1_core
def Case_m1 (F : S0xFac 9 s0x_S24 x) : Prop :=
  0 < ⟪F.N 8, x 0 - x 2⟫ ∧ (UniM1 x ∨ DSm1 x)

def Gen_m1 (F : S0xFac 9 s0x_S24 x) : Prop :=
  (∀ i j : ZMod 5, i ≠ j →
    ⟪x (rimM1 i) - x (rimM1 j), x 0 - x 2⟫ ≠ 0 ∨ ⟪x (rimM1 i) - x (rimM1 j), x 1 - x 2⟫ ≠ 0) ∧
  ∃ w : ZMod 5, (w = 1 ∨ w = 2 ∨ w = 3) ∧
    (∀ m : ZMod 5, m ≠ w → rimM1 m ∉ s0x_S24 0 → F.f 0 (x (rimM1 w)) < F.f 0 (x (rimM1 m))) ∧
    (⟪F.N 0, cross (x 1 - x 0) (x (rimM1 w) - x 0)⟫ ≠ 0 ∨
      ⟪x (rimM1 w) - x 0, x 1 - x 0⟫ < 0 ∨ ⟪x (rimM1 w) - x 1, x 0 - x 1⟫ < 0)

/-- Hypothesis bundle for `Minimality.T24.R012.m1_core`. -/
def H_m1 (F : S0xFac 9 s0x_S24 x) : Prop := Case_m1 F ∧ Gen_m1 F

-- 10. m6_core
def Case_m6 (F : S0xFac 9 s0x_S24 x) : Prop :=
  ⟪F.N 8, x 0 - x 2⟫ < 0 ∧
  ((∃ t : ZMod 6, LexTop (fun i => x (rimM6 i)) (x 0 - x 2) (x 1 - x 2) t) ∨
    ∃ a c : ZMod 6, c ≠ a ∧ c ≠ a + 1 ∧
      LexDS (fun i => x (rimM6 i)) (-det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)) (x 0 - x 2) (x 1 - x 2) a c)

def Gen_m6 (F : S0xFac 9 s0x_S24 x) : Prop :=
  (∀ i j : ZMod 6, i ≠ j →
    ⟪x (rimM6 i) - x (rimM6 j), x 0 - x 2⟫ ≠ 0 ∨ ⟪x (rimM6 i) - x (rimM6 j), x 1 - x 2⟫ ≠ 0) ∧
  ∃ w : ZMod 6, (w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 5) ∧
    (∀ m : ZMod 6, m ≠ w → rimM6 m ∉ s0x_S24 0 → F.f 0 (x (rimM6 w)) < F.f 0 (x (rimM6 m))) ∧
    (⟪F.N 0, cross (x 1 - x 0) (x (rimM6 w) - x 0)⟫ ≠ 0 ∨
      ⟪x (rimM6 w) - x 0, x 1 - x 0⟫ < 0 ∨ ⟪x (rimM6 w) - x 1, x 0 - x 1⟫ < 0)

/-- Hypothesis bundle for `Minimality.T24.R012.m6_core`. -/
def H_m6 (F : S0xFac 9 s0x_S24 x) : Prop := Case_m6 F ∧ Gen_m6 F

-- 11. m1p5_core
def Case_m1p5 (F : S0xFac 9 s0x_S24 x) : Prop :=
  0 < ⟪F.N 8, x 0 - x 2⟫ ∧
  ((∃ t : ZMod 5, LexTop (fun i => x (rimP5 i)) (x 0 - x 2) (x 2 - x 1) t) ∨
    ∃ a c : ZMod 5, c ≠ a ∧ c ≠ a + 1 ∧
      LexDS (fun i => x (rimP5 i)) (-det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)) (x 0 - x 2) (x 2 - x 1) a c)

def Gen_m1p5 (F : S0xFac 9 s0x_S24 x) : Prop :=
  (∀ i j : ZMod 5, i ≠ j →
    ⟪x (rimP5 i) - x (rimP5 j), x 0 - x 2⟫ ≠ 0 ∨ ⟪x (rimP5 i) - x (rimP5 j), x 2 - x 1⟫ ≠ 0) ∧
  ∃ w : ZMod 5, (w = 1 ∨ w = 2 ∨ w = 3) ∧
    (∀ m : ZMod 5, m ≠ w → rimP5 m ∉ s0x_S24 0 → F.f 0 (x (rimP5 w)) < F.f 0 (x (rimP5 m))) ∧
    (⟪F.N 0, cross (x 1 - x 2) (x (rimP5 w) - x 2)⟫ ≠ 0 ∨
      ⟪x (rimP5 w) - x 2, x 1 - x 2⟫ < 0 ∨ ⟪x (rimP5 w) - x 1, x 2 - x 1⟫ < 0)

/-- Hypothesis bundle for `Minimality.T24.R012.m1p5_core`. -/
def H_m1p5 (F : S0xFac 9 s0x_S24 x) : Prop := Case_m1p5 F ∧ Gen_m1p5 F

-- 12. m1p6_core
def Case_m1p6 (F : S0xFac 9 s0x_S24 x) : Prop :=
  ⟪F.N 8, x 0 - x 2⟫ < 0 ∧
  ((∃ t : ZMod 6, LexTop (fun i => x (rimP6 i)) (x 0 - x 2) (x 2 - x 1) t) ∨
    ∃ a c : ZMod 6, c ≠ a ∧ c ≠ a + 1 ∧
      LexDS (fun i => x (rimP6 i)) (-det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)) (x 0 - x 2) (x 2 - x 1) a c)

def Gen_m1p6 (F : S0xFac 9 s0x_S24 x) : Prop :=
  (∀ i j : ZMod 6, i ≠ j →
    ⟪x (rimP6 i) - x (rimP6 j), x 0 - x 2⟫ ≠ 0 ∨ ⟪x (rimP6 i) - x (rimP6 j), x 2 - x 1⟫ ≠ 0) ∧
  ∃ w : ZMod 6, (w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 5) ∧
    (∀ m : ZMod 6, m ≠ w → rimP6 m ∉ s0x_S24 0 → F.f 0 (x (rimP6 w)) < F.f 0 (x (rimP6 m))) ∧
    (⟪F.N 0, cross (x 1 - x 2) (x (rimP6 w) - x 2)⟫ ≠ 0 ∨
      ⟪x (rimP6 w) - x 2, x 1 - x 2⟫ < 0 ∨ ⟪x (rimP6 w) - x 1, x 2 - x 1⟫ < 0)

/-- Hypothesis bundle for `Minimality.T24.R012.m1p6_core`. -/
def H_m1p6 (F : S0xFac 9 s0x_S24 x) : Prop := Case_m1p6 F ∧ Gen_m1p6 F

-- 12b. q012_x16_lo
def Case_x16lo (F : S0xFac 9 s0x_S24 x) : Prop :=
  ⟪x 1 - x 6, x 2 - x 1⟫ ≠ 0 ∧ t16 x < -1 ∧
  ⟪F.N 3, u16 x⟫ < 0 ∧ 0 < ⟪F.N 4, u16 x⟫ ∧ ⟪F.N 8, u16 x⟫ < 0 ∧
  (0 < (⟪x 1, u16 x⟫ - ⟪x 0, u16 x⟫) * (⟪x 1, u16 x⟫ - ⟪x 4, u16 x⟫) ∨
    0 < ⟪x 1 - x 6, x 2 - x 1⟫ * (⟪x 0, u16 x⟫ - ⟪x 4, u16 x⟫))

def Gen_x16lo (F : S0xFac 9 s0x_S24 x) : Prop :=
  (∀ i j : ZMod 4, i ≠ j → (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨
    ⟪quad (x 4) (x 0) (x 1) (x 6) i - quad (x 4) (x 0) (x 1) (x 6) j, u16 x⟫ ≠ 0) ∧
  ((F.f 0 (x 6) < F.f 0 (x 4) ∧
      (⟪F.N 0, cross (x 1 - x 0) (x 6 - x 0)⟫ ≠ 0 ∨
        ⟪x 6 - x 0, x 1 - x 0⟫ < 0 ∨ ⟪x 6 - x 1, x 0 - x 1⟫ < 0)) ∨
    (F.f 0 (x 4) < F.f 0 (x 6) ∧
      (⟪F.N 0, cross (x 1 - x 0) (x 4 - x 0)⟫ ≠ 0 ∨
        ⟪x 4 - x 0, x 1 - x 0⟫ < 0 ∨ ⟪x 4 - x 1, x 0 - x 1⟫ < 0)))

/-- Hypothesis bundle for `Minimality.T24.RX16.q012_x16_lo`. -/
def H_x16lo (F : S0xFac 9 s0x_S24 x) : Prop := Case_x16lo F ∧ Gen_x16lo F

-- 12c. q012_x16_hi
def Case_x16hi (F : S0xFac 9 s0x_S24 x) : Prop :=
  ⟪x 1 - x 6, x 2 - x 1⟫ ≠ 0 ∧ -1 < t16 x ∧ t16 x < 0 ∧
  0 < ⟪F.N 6, u16 x⟫ ∧ ⟪F.N 7, u16 x⟫ < 0 ∧ 0 < ⟪F.N 8, u16 x⟫ ∧
  (0 < (⟪x 1, u16 x⟫ - ⟪x 2, u16 x⟫) * (⟪x 1, u16 x⟫ - ⟪x 3, u16 x⟫) ∨
    0 < -⟪x 1 - x 6, x 2 - x 1⟫ * (⟪x 2, u16 x⟫ - ⟪x 3, u16 x⟫))

def Gen_x16hi (F : S0xFac 9 s0x_S24 x) : Prop :=
  (∀ i j : ZMod 4, i ≠ j → (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨
    ⟪quad (x 3) (x 2) (x 1) (x 6) i - quad (x 3) (x 2) (x 1) (x 6) j, u16 x⟫ ≠ 0) ∧
  ((F.f 0 (x 6) < F.f 0 (x 3) ∧
      (⟪F.N 0, cross (x 1 - x 2) (x 6 - x 2)⟫ ≠ 0 ∨
        ⟪x 6 - x 2, x 1 - x 2⟫ < 0 ∨ ⟪x 6 - x 1, x 2 - x 1⟫ < 0)) ∨
    (F.f 0 (x 3) < F.f 0 (x 6) ∧
      (⟪F.N 0, cross (x 1 - x 2) (x 3 - x 2)⟫ ≠ 0 ∨
        ⟪x 3 - x 2, x 1 - x 2⟫ < 0 ∨ ⟪x 3 - x 1, x 2 - x 1⟫ < 0)))

/-- Hypothesis bundle for `Minimality.T24.RX16.q012_x16_hi`. -/
def H_x16hi (F : S0xFac 9 s0x_S24 x) : Prop := Case_x16hi F ∧ Gen_x16hi F

-- 12d. q012_f0345
def Case_f0345 (F : S0xFac 9 s0x_S24 x) : Prop :=
  0 < t3_f0345 F ∧ ⟪F.N 4, u0 x (t3_f0345 F)⟫ < 0 ∧ ⟪F.N 7, u0 x (t3_f0345 F)⟫ < 0 ∧
  0 < ⟪F.N 6, u0 x (t3_f0345 F)⟫ ∧ ⟪F.N 8, u0 x (t3_f0345 F)⟫ < 0

def Gen_f0345 (F : S0xFac 9 s0x_S24 x) : Prop :=
  ¬ (⟪x 0, u0 x (t3_f0345 F)⟫ = ⟪x 2, u0 x (t3_f0345 F)⟫ ∧
      ⟪x 2, u0 x (t3_f0345 F)⟫ = ⟪x 3, u0 x (t3_f0345 F)⟫) ∧
  F.f 0 (x 4) ≠ F.f 0 (x 3) ∧
  (F.f 0 (x 4) < F.f 0 (x 3) → Off012 F 4) ∧
  (F.f 0 (x 3) < F.f 0 (x 4) → Off012 F 3) ∧
  Gen4 (quad (x 0) (x 4) (x 3) (x 2)) (u0 x (t3_f0345 F)) (x 2 - x 1) ∧
  F.f 0 (x 5) ≠ F.f 0 (x 3) ∧
  (F.f 0 (x 5) < F.f 0 (x 3) → Off012 F 5) ∧
  (F.f 0 (x 3) < F.f 0 (x 5) → Off012 F 3) ∧
  Gen4 (quad (x 0) (x 5) (x 3) (x 2)) (u0 x (t3_f0345 F)) (x 2 - x 1)

/-- Hypothesis bundle for `Minimality.T24.R012.q012_f0345`. -/
def H_f0345 (F : S0xFac 9 s0x_S24 x) : Prop := Case_f0345 F ∧ Gen_f0345 F

-- 12e. q012_f0345_neg_lo
def Case_f0345n (F : S0xFac 9 s0x_S24 x) : Prop :=
  t3n F < -1 ∧ 0 < ⟪F.N 4, u0 x (t3n F)⟫ ∧ ⟪F.N 8, u0 x (t3n F)⟫ < 0 ∧
  min ⟪x 0, u0 x (t3n F)⟫ ⟪x 6, u0 x (t3n F)⟫ < max ⟪x 1, u0 x (t3n F)⟫ ⟪x 4, u0 x (t3n F)⟫

def Gen_f0345n (F : S0xFac 9 s0x_S24 x) : Prop :=
  F.f 0 (x 6) ≠ F.f 0 (x 4) ∧
  (F.f 0 (x 6) < F.f 0 (x 4) → Off01 F 6) ∧
  (F.f 0 (x 4) < F.f 0 (x 6) → Off01 F 4) ∧
  Gen4 (quad (x 0) (x 1) (x 6) (x 4)) (u0 x (t3n F)) (x 2 - x 1)

/-- Hypothesis bundle for `Minimality.T24.R012.q012_f0345_neg_lo`. -/
def H_f0345n (F : S0xFac 9 s0x_S24 x) : Prop := Case_f0345n F ∧ Gen_f0345n F

-- 13. q046_cross_core
def Case_crossCore (F : S0xFac 9 s0x_S24 x) : Prop :=
  0 < ⟪F.N 5, x 4 - x 0⟫ ∧ 0 < ⟪F.N 6, u47 F⟫ ∧ ⟪x 6, u47 F⟫ < ⟪x 0, u47 F⟫ ∧
  ⟪F.N 5, u47 F⟫ < 0 ∧ ⟪F.N 2, u47 F⟫ ≤ 0

def Gen_crossCore (F : S0xFac 9 s0x_S24 x) : Prop :=
  ((F.f 4 (x 2) < F.f 4 (x 5) ∧
    (⟪F.N 4, cross (x 0 - x 6) (x 2 - x 6)⟫ ≠ 0 ∨
      ⟪x 2 - x 6, x 0 - x 6⟫ < 0 ∨ ⟪x 2 - x 0, x 6 - x 0⟫ < 0)) ∨
    (F.f 4 (x 5) < F.f 4 (x 2) ∧
    (⟪F.N 4, cross (x 0 - x 6) (x 5 - x 6)⟫ ≠ 0 ∨
      ⟪x 5 - x 6, x 0 - x 6⟫ < 0 ∨ ⟪x 5 - x 0, x 6 - x 0⟫ < 0))) ∧
  ∀ i j : ZMod 4, i ≠ j →
    ⟪quad (x 2) (x 6) (x 0) (x 5) i - quad (x 2) (x 6) (x 0) (x 5) j, u47 F⟫ ≠ 0 ∨
    ⟪quad (x 2) (x 6) (x 0) (x 5) i - quad (x 2) (x 6) (x 0) (x 5) j, x 6 - x 0⟫ ≠ 0

/-- Hypothesis bundle for `Minimality.T24.R046.q046_cross_core`. -/
def H_crossCore (F : S0xFac 9 s0x_S24 x) : Prop := Case_crossCore F ∧ Gen_crossCore F

-- 14. q046_cross_cbar
def Case_crossCbar (F : S0xFac 9 s0x_S24 x) : Prop :=
  0 < ⟪F.N 5, x 4 - x 0⟫ ∧ 0 < ⟪F.N 6, u47 F⟫ ∧ ⟪x 6, u47 F⟫ < ⟪x 0, u47 F⟫ ∧ CbarIn x

def Gen_crossCbar (F : S0xFac 9 s0x_S24 x) : Prop := Gen_crossCore F

/-- Hypothesis bundle for `Minimality.T24.R046.q046_cross_cbar`. -/
def H_crossCbar (F : S0xFac 9 s0x_S24 x) : Prop := Case_crossCbar F ∧ Gen_crossCbar F

-- 14b. ropen_cross_core_beta
def Case_crossB (F : S0xFac 9 s0x_S24 x) : Prop :=
  0 < F.f 7 (x 4) - F.f 7 (x 0) ∧ 0 < ⟪F.N 6, u47 F⟫ ∧
  min ⟪x 6, u47 F⟫ ⟪x 5, u47 F⟫ < max ⟪x 2, u47 F⟫ ⟪x 0, u47 F⟫ ∧
  ⟪F.N 5, u47 F⟫ < 0 ∧ ⟪F.N 2, u47 F⟫ ≤ 0

def Gen_crossB (F : S0xFac 9 s0x_S24 x) : Prop := Gen_crossCore F

/-- Hypothesis bundle for `Minimality.T24.R046.ropen_cross_core_beta`. -/
def H_crossB (F : S0xFac 9 s0x_S24 x) : Prop := Case_crossB F ∧ Gen_crossB F

-- 15. q046_coplanar
def Case_cop (F : S0xFac 9 s0x_S24 x) : Prop :=
  ⟪F.N 2, x 4 - x 6⟫ < 0 ∧ ⟪F.N 6, x 4 - x 6⟫ < 0

def Gen_cop (F : S0xFac 9 s0x_S24 x) : Prop :=
  F.f 4 (x 3) ≠ F.f 4 (x 5) ∧
  (⟪F.N 4, cross (x 0 - x 4) (x (if F.f 4 (x 3) < F.f 4 (x 5) then 3 else 5) - x 4)⟫ ≠ 0 ∨
    ⟪x (if F.f 4 (x 3) < F.f 4 (x 5) then 3 else 5) - x 4, x 0 - x 4⟫ < 0 ∨
    ⟪x (if F.f 4 (x 3) < F.f 4 (x 5) then 3 else 5) - x 0, x 4 - x 0⟫ < 0) ∧
  ∀ i j : ZMod 4, i ≠ j →
    ⟪quad (x 4) (x 0) (x 5) (x 3) i - quad (x 4) (x 0) (x 5) (x 3) j, x 4 - x 6⟫ ≠ 0 ∨
    ⟪quad (x 4) (x 0) (x 5) (x 3) i - quad (x 4) (x 0) (x 5) (x 3) j, x 0 - x 6⟫ ≠ 0

/-- Hypothesis bundle for `Minimality.T24.R046.q046_coplanar`. -/
def H_cop (F : S0xFac 9 s0x_S24 x) : Prop := Case_cop F ∧ Gen_cop F

-- 16. q45_J0_exp_end_ds
def Case_J0exp (F : S0xFac 9 s0x_S24 x) : Prop :=
  (∃ s t : ℝ, 0 < s ∧ 0 < t ∧ 1 < s + t ∧
    x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0) ∧ s ≤ 1) ∧
  0 < ⟪F.N 5, x 5 - x 0⟫ ∧
  (UniLex x (x 5 - x 0) (x 4 - x 5) ∨ DSany x (x 5 - x 0) (x 4 - x 5))

def Gen_J0exp (F : S0xFac 9 s0x_S24 x) : Prop :=
  (∀ i j : ZMod 5, i ≠ j →
    ⟪rimJ0 x i - rimJ0 x j, x 5 - x 0⟫ ≠ 0 ∨ ⟪rimJ0 x i - rimJ0 x j, x 4 - x 5⟫ ≠ 0) ∧
  ∃ w : Fin 7, (w = 1 ∨ w = 2 ∨ w = 6) ∧
    (∀ m : Fin 7, m ≠ w → (m = 1 ∨ m = 2 ∨ m = 6) → F.f 3 (x w) < F.f 3 (x m)) ∧
    (⟪F.N 3, cross (x 5 - x 4) (x w - x 4)⟫ ≠ 0 ∨ ⟪x w - x 4, x 5 - x 4⟫ < 0 ∨
      ⟪x w - x 5, x 4 - x 5⟫ < 0)

/-- Hypothesis bundle for `Minimality.T24.Q45.q45_J0_exp_end_ds`. -/
def H_J0exp (F : S0xFac 9 s0x_S24 x) : Prop := Case_J0exp F ∧ Gen_J0exp F

-- 17. q45_J0_exp_end_ds_gt
def Case_J0expGt (F : S0xFac 9 s0x_S24 x) : Prop :=
  (∃ s t : ℝ, 0 < s ∧ 0 < t ∧ 1 < s + t ∧
    x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0) ∧ 1 < s) ∧
  0 < ⟪F.N 5, x 3 - x 4⟫ ∧
  (UniLex x (x 3 - x 4) (x 4 - x 0) ∨ DSany x (x 3 - x 4) (x 4 - x 0))

def Gen_J0expGt (F : S0xFac 9 s0x_S24 x) : Prop :=
  (∀ i j : ZMod 5, i ≠ j →
    ⟪rimJ0 x i - rimJ0 x j, x 3 - x 4⟫ ≠ 0 ∨ ⟪rimJ0 x i - rimJ0 x j, x 4 - x 0⟫ ≠ 0) ∧
  ∃ w : Fin 7, (w = 1 ∨ w = 2 ∨ w = 6) ∧
    (∀ m : Fin 7, m ≠ w → (m = 1 ∨ m = 2 ∨ m = 6) → F.f 3 (x w) < F.f 3 (x m)) ∧
    (⟪F.N 3, cross (x 5 - x 4) (x w - x 4)⟫ ≠ 0 ∨ ⟪x w - x 4, x 5 - x 4⟫ < 0 ∨
      ⟪x w - x 5, x 4 - x 5⟫ < 0)

/-- Hypothesis bundle for `Minimality.T24.Q45.q45_J0_exp_end_ds_gt`. -/
def H_J0expGt (F : S0xFac 9 s0x_S24 x) : Prop := Case_J0expGt F ∧ Gen_J0expGt F

-- 18. q45_J0_tie45
def Case_tie45 (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ 1 < s + t ∧
    x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0) ∧
    0 < tieAlpha x ∧ 0 < tieBeta x ∧
    0 < tieAlpha x * (1 - s) + tieBeta x * t ∧
    0 < tieAlpha x * s + tieBeta x * (1 - t) ∧
    0 < ⟪F.N 5, u_Pi x (tieAlpha x) (tieBeta x)⟫ ∧
    min ⟪x 6, u_Pi x (tieAlpha x) (tieBeta x)⟫ ⟪x 2, u_Pi x (tieAlpha x) (tieBeta x)⟫ <
      max ⟪x 4, u_Pi x (tieAlpha x) (tieBeta x)⟫ ⟪x 1, u_Pi x (tieAlpha x) (tieBeta x)⟫

def Gen_tie45 (F : S0xFac 9 s0x_S24 x) : Prop :=
  SingleAdjacentTie (quint (x 4) (x 5) (x 2) (x 1) (x 6)) (u_Pi x (tieAlpha x) (tieBeta x)) 0 ∧
  ∃ w : Fin 7, (w = 1 ∨ w = 2 ∨ w = 6) ∧
    (∀ m : Fin 7, m ≠ w → (m = 1 ∨ m = 2 ∨ m = 6) → F.f 3 (x w) < F.f 3 (x m)) ∧
    (⟪F.N 3, cross (x 5 - x 4) (x w - x 4)⟫ ≠ 0 ∨ ⟪x w - x 4, x 5 - x 4⟫ < 0 ∨
      ⟪x w - x 5, x 4 - x 5⟫ < 0)

/-- Hypothesis bundle for `Minimality.T24.Q45.q45_J0_tie45`. -/
def H_tie45 (F : S0xFac 9 s0x_S24 x) : Prop := Case_tie45 F ∧ Gen_tie45 F

-- 19. rj0h_Kminus_e5
def Case_KminusE5 (F : S0xFac 9 s0x_S24 x) : Prop :=
  ⟪F.N 5, x 5 - x 0⟫ < 0 ∧
  (∃ s t : ℝ, 0 < s ∧ 0 < t ∧ 1 < s + t ∧
    x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0) ∧ s ≤ 1) ∧
  0 < det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) ∧
  min ⟪x 4, x 5 - x 0⟫ ⟪x 2, x 5 - x 0⟫ < max ⟪x 6, x 5 - x 0⟫ ⟪x 5, x 5 - x 0⟫

def Gen_KminusE5 (F : S0xFac 9 s0x_S24 x) : Prop :=
  (∀ i j : ZMod 4, i ≠ j →
    ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0 ∨
    ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0) ∧
  F.f 3 (x 2) ≠ F.f 3 (x 6) ∧
  (⟪F.N 3, cross (x 5 - x 4) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4)⟫ ≠ 0 ∨
    ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 5 - x 4⟫ < 0 ∨
    ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 4 - x 5⟫ < 0)

/-- Hypothesis bundle for `Minimality.T24.Q45.rj0h_Kminus_e5`. -/
def H_KminusE5 (F : S0xFac 9 s0x_S24 x) : Prop := Case_KminusE5 F ∧ Gen_KminusE5 F

-- 20. rj0h_Kminus_e34
def Case_KminusE34 (F : S0xFac 9 s0x_S24 x) : Prop :=
  ⟪F.N 5, x 3 - x 4⟫ < 0 ∧
  (∃ s t : ℝ, 0 < s ∧ 0 < t ∧ 1 < s + t ∧
    x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0) ∧ 1 < s) ∧
  0 < det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) ∧
  min ⟪x 4, x 3 - x 4⟫ ⟪x 2, x 3 - x 4⟫ < max ⟪x 6, x 3 - x 4⟫ ⟪x 5, x 3 - x 4⟫

def Gen_KminusE34 (F : S0xFac 9 s0x_S24 x) : Prop :=
  (∀ i j : ZMod 4, i ≠ j →
    ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 3 - x 4⟫ ≠ 0 ∨
    ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0) ∧
  F.f 3 (x 2) ≠ F.f 3 (x 6) ∧
  (⟪F.N 3, cross (x 5 - x 4) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4)⟫ ≠ 0 ∨
    ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 5 - x 4⟫ < 0 ∨
    ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 4 - x 5⟫ < 0)

/-- Hypothesis bundle for `Minimality.T24.Q45.rj0h_Kminus_e34`. -/
def H_KminusE34 (F : S0xFac 9 s0x_S24 x) : Prop := Case_KminusE34 F ∧ Gen_KminusE34 F

-- Sym24 mirrors (21..40)
def Case_w3p_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_w3p (sym24 F)
def Gen_w3p_sym (F : S0xFac 9 s0x_S24 x) : Prop := Gen_w3p (sym24 F)
/-- Mirror hypothesis bundle for `Sym.q016_w3_pos` (`q012_w3_pos` via `Sym.faceChordView_sym`). -/
def H_w3p_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_w3p_sym F ∧ Gen_w3p_sym F

def Case_w3nA_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_w3nA (sym24 F)
def Gen_w3nA_sym (F : S0xFac 9 s0x_S24 x) : Prop := Gen_w3nA (sym24 F)
/-- Mirror hypothesis bundle for `Sym.q016_w3_neg_A` (`q012_w3_neg_A` via `Sym.faceChordView_sym`). -/
def H_w3nA_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_w3nA_sym F ∧ Gen_w3nA_sym F

def Case_w3nB_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_w3nB (sym24 F)
def Gen_w3nB_sym (F : S0xFac 9 s0x_S24 x) : Prop := Gen_w3nB (sym24 F)
/-- Mirror hypothesis bundle for `Sym.q016_w3_neg_B` (`q012_w3_neg_B` via `Sym.faceChordView_sym`). -/
def H_w3nB_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_w3nB_sym F ∧ Gen_w3nB_sym F

def Case_w4n_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_w4n (sym24 F)
def Gen_w4n_sym (F : S0xFac 9 s0x_S24 x) : Prop := Gen_w4n (sym24 F)
/-- Mirror hypothesis bundle for `Sym.q016_w4_neg` (`q012_w4_neg` via `Sym.faceChordView_sym`). -/
def H_w4n_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_w4n_sym F ∧ Gen_w4n_sym F

def Case_f346A_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_f346A (sym24 F)
def Gen_f346A_sym (F : S0xFac 9 s0x_S24 x) : Prop := Gen_f346A (sym24 F)
/-- Mirror hypothesis bundle for `Sym.q016_f346_pos_A_4` (`q012_f346_pos_A_4` via `Sym.faceChordView_sym`). -/
def H_f346A_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_f346A_sym F ∧ Gen_f346A_sym F

def Case_f346B_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_f346B (sym24 F)
def Gen_f346B_sym (F : S0xFac 9 s0x_S24 x) : Prop := Gen_f346B (sym24 F)
/-- Mirror hypothesis bundle for `Sym.q016_f346_B_4` (`q012_f346_B_4` via `Sym.faceChordView_sym`). -/
def H_f346B_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_f346B_sym F ∧ Gen_f346B_sym F

def Case_LCp_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_LCp (sym24 F)
def Gen_LCp_sym (F : S0xFac 9 s0x_S24 x) : Prop := Gen_LCp (sym24 F)
/-- Mirror hypothesis bundle for `Sym.q016_LC_plus_gen` (`q012_LC_plus_gen` via `Sym.faceChordView_sym`). -/
def H_LCp_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_LCp_sym F ∧ Gen_LCp_sym F

def Case_LCm_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_LCm (sym24 F)
def Gen_LCm_sym (F : S0xFac 9 s0x_S24 x) : Prop := Gen_LCm (sym24 F)
/-- Mirror hypothesis bundle for `Sym.q016_LC_minus_gen` (`q012_LC_minus_gen` via `Sym.faceChordView_sym`). -/
def H_LCm_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_LCm_sym F ∧ Gen_LCm_sym F

def Case_m1_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_m1 (sym24 F)
def Gen_m1_sym (F : S0xFac 9 s0x_S24 x) : Prop := Gen_m1 (sym24 F)
/-- Mirror hypothesis bundle for `Sym.q016_m1_core` (`m1_core` via `Sym.faceChordView_sym`). -/
def H_m1_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_m1_sym F ∧ Gen_m1_sym F

def Case_m6_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_m6 (sym24 F)
def Gen_m6_sym (F : S0xFac 9 s0x_S24 x) : Prop := Gen_m6 (sym24 F)
/-- Mirror hypothesis bundle for `Sym.q016_m6_core` (`m6_core` via `Sym.faceChordView_sym`). -/
def H_m6_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_m6_sym F ∧ Gen_m6_sym F

def Case_m1p5_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_m1p5 (sym24 F)
def Gen_m1p5_sym (F : S0xFac 9 s0x_S24 x) : Prop := Gen_m1p5 (sym24 F)
/-- Mirror hypothesis bundle for `Sym.q016_m1p5_core` (`m1p5_core` via `Sym.faceChordView_sym`). -/
def H_m1p5_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_m1p5_sym F ∧ Gen_m1p5_sym F

def Case_m1p6_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_m1p6 (sym24 F)
def Gen_m1p6_sym (F : S0xFac 9 s0x_S24 x) : Prop := Gen_m1p6 (sym24 F)
/-- Mirror hypothesis bundle for `Sym.q016_m1p6_core` (`m1p6_core` via `Sym.faceChordView_sym`). -/
def H_m1p6_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_m1p6_sym F ∧ Gen_m1p6_sym F

def Case_x16lo_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_x16lo (sym24 F)
def Gen_x16lo_sym (F : S0xFac 9 s0x_S24 x) : Prop := Gen_x16lo (sym24 F)
/-- Mirror hypothesis bundle for `Sym.q016_x16_lo` (`q012_x16_lo` via `Sym.faceChordView_sym`). -/
def H_x16lo_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_x16lo_sym F ∧ Gen_x16lo_sym F

def Case_x16hi_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_x16hi (sym24 F)
def Gen_x16hi_sym (F : S0xFac 9 s0x_S24 x) : Prop := Gen_x16hi (sym24 F)
/-- Mirror hypothesis bundle for `Sym.q016_x16_hi` (`q012_x16_hi` via `Sym.faceChordView_sym`). -/
def H_x16hi_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_x16hi_sym F ∧ Gen_x16hi_sym F

def Case_f0345_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_f0345 (sym24 F)
def Gen_f0345_sym (F : S0xFac 9 s0x_S24 x) : Prop := Gen_f0345 (sym24 F)
/-- Mirror hypothesis bundle for `Sym.q016_f0345` (`q012_f0345` via `Sym.faceChordView_sym`). -/
def H_f0345_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_f0345_sym F ∧ Gen_f0345_sym F

def Case_f0345n_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_f0345n (sym24 F)
def Gen_f0345n_sym (F : S0xFac 9 s0x_S24 x) : Prop := Gen_f0345n (sym24 F)
/-- Mirror hypothesis bundle for `Sym.q016_f0345_neg_lo` (`q012_f0345_neg_lo` via `Sym.faceChordView_sym`). -/
def H_f0345n_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_f0345n_sym F ∧ Gen_f0345n_sym F

def Case_crossCore_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_crossCore (sym24 F)
def Gen_crossCore_sym (F : S0xFac 9 s0x_S24 x) : Prop := Gen_crossCore (sym24 F)
/-- Mirror hypothesis bundle for `Sym.q025_cross_core` (`q046_cross_core` via `Sym.faceChordView_sym`). -/
def H_crossCore_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_crossCore_sym F ∧ Gen_crossCore_sym F

def Case_crossCbar_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_crossCbar (sym24 F)
def Gen_crossCbar_sym (F : S0xFac 9 s0x_S24 x) : Prop := Gen_crossCbar (sym24 F)
/-- Mirror hypothesis bundle for `Sym.q025_cross_cbar` (`q046_cross_cbar` via `Sym.faceChordView_sym`). -/
def H_crossCbar_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_crossCbar_sym F ∧ Gen_crossCbar_sym F

def Case_crossB_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_crossB (sym24 F)
def Gen_crossB_sym (F : S0xFac 9 s0x_S24 x) : Prop := Gen_crossB (sym24 F)
/-- Mirror hypothesis bundle for `Sym.q025_cross_core_beta` (`ropen_cross_core_beta` via `Sym.faceChordView_sym`). -/
def H_crossB_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_crossB_sym F ∧ Gen_crossB_sym F

def Case_cop_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_cop (sym24 F)
def Gen_cop_sym (F : S0xFac 9 s0x_S24 x) : Prop := Gen_cop (sym24 F)
/-- Mirror hypothesis bundle for `Sym.q025_coplanar` (`q046_coplanar` via `Sym.faceChordView_sym`). -/
def H_cop_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_cop_sym F ∧ Gen_cop_sym F

def Case_J0exp_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_J0exp (sym24 F)
def Gen_J0exp_sym (F : S0xFac 9 s0x_S24 x) : Prop := Gen_J0exp (sym24 F)
/-- Mirror hypothesis bundle for `Sym.q45_J0_exp_end_ds_sym` (`q45_J0_exp_end_ds` via `Sym.faceChordView_sym`). -/
def H_J0exp_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_J0exp_sym F ∧ Gen_J0exp_sym F

def Case_J0expGt_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_J0expGt (sym24 F)
def Gen_J0expGt_sym (F : S0xFac 9 s0x_S24 x) : Prop := Gen_J0expGt (sym24 F)
/-- Mirror hypothesis bundle for `Sym.q45_J0_exp_end_ds_gt_sym` (`q45_J0_exp_end_ds_gt` via `Sym.faceChordView_sym`). -/
def H_J0expGt_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_J0expGt_sym F ∧ Gen_J0expGt_sym F

def Case_tie45_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_tie45 (sym24 F)
def Gen_tie45_sym (F : S0xFac 9 s0x_S24 x) : Prop := Gen_tie45 (sym24 F)
/-- Mirror hypothesis bundle for `Sym.q45_J0_tie45_sym` (`q45_J0_tie45` via `Sym.faceChordView_sym`). -/
def H_tie45_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_tie45_sym F ∧ Gen_tie45_sym F

def Case_KminusE5_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_KminusE5 (sym24 F)
def Gen_KminusE5_sym (F : S0xFac 9 s0x_S24 x) : Prop := Gen_KminusE5 (sym24 F)
/-- Mirror hypothesis bundle for `Sym.rj0h_Kminus_e5_sym` (`rj0h_Kminus_e5` via `Sym.faceChordView_sym`). -/
def H_KminusE5_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_KminusE5_sym F ∧ Gen_KminusE5_sym F

def Case_KminusE34_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_KminusE34 (sym24 F)
def Gen_KminusE34_sym (F : S0xFac 9 s0x_S24 x) : Prop := Gen_KminusE34 (sym24 F)
/-- Mirror hypothesis bundle for `Sym.rj0h_Kminus_e34_sym` (`rj0h_Kminus_e34` via `Sym.faceChordView_sym`). -/
def H_KminusE34_sym (F : S0xFac 9 s0x_S24 x) : Prop := Case_KminusE34_sym F ∧ Gen_KminusE34_sym F

/-! ### Disjunctions `HAvail`, `CaseAny`, `Wall24` and `RResidual` -/

/-- Disjunction of all 50 proved R-region leaf hypothesis bundles (25 base + 25 `Sym24` mirrors). -/
def HAvail (F : S0xFac 9 s0x_S24 x) : Prop :=
  H_w3p F ∨ H_w3nA F ∨ H_w3nB F ∨ H_w4n F ∨ H_f346A F ∨ H_f346B F ∨
  H_LCp F ∨ H_LCm F ∨ H_m1 F ∨ H_m6 F ∨ H_m1p5 F ∨ H_m1p6 F ∨
  H_x16lo F ∨ H_x16hi F ∨ H_f0345 F ∨ H_f0345n F ∨
  H_crossCore F ∨ H_crossCbar F ∨ H_crossB F ∨ H_cop F ∨
  H_J0exp F ∨ H_J0expGt F ∨ H_tie45 F ∨ H_KminusE5 F ∨ H_KminusE34 F ∨
  H_w3p_sym F ∨ H_w3nA_sym F ∨ H_w3nB_sym F ∨ H_w4n_sym F ∨ H_f346A_sym F ∨ H_f346B_sym F ∨
  H_LCp_sym F ∨ H_LCm_sym F ∨ H_m1_sym F ∨ H_m6_sym F ∨ H_m1p5_sym F ∨ H_m1p6_sym F ∨
  H_x16lo_sym F ∨ H_x16hi_sym F ∨ H_f0345_sym F ∨ H_f0345n_sym F ∨
  H_crossCore_sym F ∨ H_crossCbar_sym F ∨ H_crossB_sym F ∨ H_cop_sym F ∨
  H_J0exp_sym F ∨ H_J0expGt_sym F ∨ H_tie45_sym F ∨ H_KminusE5_sym F ∨ H_KminusE34_sym F

/-- Disjunction of all 50 strict case conditions (without genericity `Gen_*`). -/
def CaseAny (F : S0xFac 9 s0x_S24 x) : Prop :=
  Case_w3p F ∨ Case_w3nA F ∨ Case_w3nB F ∨ Case_w4n F ∨ Case_f346A F ∨ Case_f346B F ∨
  Case_LCp F ∨ Case_LCm F ∨ Case_m1 F ∨ Case_m6 F ∨ Case_m1p5 F ∨ Case_m1p6 F ∨
  Case_x16lo F ∨ Case_x16hi F ∨ Case_f0345 F ∨ Case_f0345n F ∨
  Case_crossCore F ∨ Case_crossCbar F ∨ Case_crossB F ∨ Case_cop F ∨
  Case_J0exp F ∨ Case_J0expGt F ∨ Case_tie45 F ∨ Case_KminusE5 F ∨ Case_KminusE34 F ∨
  Case_w3p_sym F ∨ Case_w3nA_sym F ∨ Case_w3nB_sym F ∨ Case_w4n_sym F ∨ Case_f346A_sym F ∨ Case_f346B_sym F ∨
  Case_LCp_sym F ∨ Case_LCm_sym F ∨ Case_m1_sym F ∨ Case_m6_sym F ∨ Case_m1p5_sym F ∨ Case_m1p6_sym F ∨
  Case_x16lo_sym F ∨ Case_x16hi_sym F ∨ Case_f0345_sym F ∨ Case_f0345n_sym F ∨
  Case_crossCore_sym F ∨ Case_crossCbar_sym F ∨ Case_crossB_sym F ∨ Case_cop_sym F ∨
  Case_J0exp_sym F ∨ Case_J0expGt_sym F ∨ Case_tie45_sym F ∨ Case_KminusE5_sym F ∨ Case_KminusE34_sym F

/-- One-sided codimension-1 walls in facet-sign form (`c3=1`, `c4=1`, `a4=1`, `a5=1`, `s=1`, `P=0`,
Lemma D1/D2/M1/LC/J0 walls). -/
def Wall24_0 (F : S0xFac 9 s0x_S24 x) : Prop :=
  ⟪F.N 8, u0 x (omega3_012 F)⟫ = 0 ∨
  ⟪F.N 8, u0 x (inv_omega4_012 F)⟫ = 0 ∨
  ⟪F.N 3, u0 x (omega3_012 F)⟫ = 0 ∨
  ⟪F.N 6, u0 x (inv_omega4_012 F)⟫ = 0 ∨
  ⟪F.N 6, u08 F⟫ = 0 ∨
  F.f 8 (x 1) = F.f 8 (x 2) ∨
  ⟪F.N 4, u_LC x⟫ = 0 ∨ ⟪F.N 7, u_LC x⟫ = 0 ∨ ⟪F.N 6, u_LC x⟫ = 0 ∨
  ⟪F.N 3, u_LC x⟫ = 0 ∨ ⟪F.N 8, u_LC x⟫ = 0 ∨
  ⟪x 4, u_LC x⟫ = ⟪x 0, u_LC x⟫ ∨ ⟪x 3, u_LC x⟫ = ⟪x 0, u_LC x⟫ ∨
  ⟪x 0 - x 2, x 2 - x 1⟫ = 0 ∨ t_LC x = 0 ∨
  omega3_012 F = 0 ∨ omega4_012 F = 0 ∨
  ⟪F.N 8, x 0 - x 2⟫ = 0 ∨
  ⟪F.N 6, u47 F⟫ = 0 ∨
  ⟪F.N 5, x 4 - x 0⟫ = 0 ∨
  F.f 7 (x 4) = F.f 7 (x 0) ∨
  F.f 4 (x 2) = F.f 4 (x 5) ∨
  ⟪x 6, u47 F⟫ = ⟪x 0, u47 F⟫ ∨
  min ⟪x 6, u47 F⟫ ⟪x 5, u47 F⟫ = max ⟪x 2, u47 F⟫ ⟪x 0, u47 F⟫ ∨
  ⟪F.N 2, x 4 - x 6⟫ = 0 ∨ ⟪F.N 6, x 4 - x 6⟫ = 0 ∨
  ⟪F.N 5, x 5 - x 0⟫ = 0 ∨ ⟪F.N 5, x 3 - x 4⟫ = 0 ∨
  ⟪F.N 5, u_Pi x (tieAlpha x) (tieBeta x)⟫ = 0 ∨
  ⟪x 1 - x 6, x 2 - x 1⟫ = 0 ∨ t16 x = -1 ∨ t16 x = 0 ∨
  ⟪F.N 3, u16 x⟫ = 0 ∨ ⟪F.N 4, u16 x⟫ = 0 ∨ ⟪F.N 8, u16 x⟫ = 0 ∨
  ⟪F.N 6, u16 x⟫ = 0 ∨ ⟪F.N 7, u16 x⟫ = 0 ∨
  ((⟪x 1, u16 x⟫ - ⟪x 0, u16 x⟫) * (⟪x 1, u16 x⟫ - ⟪x 4, u16 x⟫) = 0 ∧
    ⟪x 1 - x 6, x 2 - x 1⟫ * (⟪x 0, u16 x⟫ - ⟪x 4, u16 x⟫) = 0) ∨
  ((⟪x 1, u16 x⟫ - ⟪x 2, u16 x⟫) * (⟪x 1, u16 x⟫ - ⟪x 3, u16 x⟫) = 0 ∧
    -⟪x 1 - x 6, x 2 - x 1⟫ * (⟪x 2, u16 x⟫ - ⟪x 3, u16 x⟫) = 0) ∨
  t3_f0345 F = 0 ∨
  ⟪F.N 4, u0 x (t3_f0345 F)⟫ = 0 ∨ ⟪F.N 7, u0 x (t3_f0345 F)⟫ = 0 ∨
  ⟪F.N 6, u0 x (t3_f0345 F)⟫ = 0 ∨ ⟪F.N 8, u0 x (t3_f0345 F)⟫ = 0 ∨
  (⟪x 0, u0 x (t3_f0345 F)⟫ = ⟪x 2, u0 x (t3_f0345 F)⟫ ∧
    ⟪x 2, u0 x (t3_f0345 F)⟫ = ⟪x 3, u0 x (t3_f0345 F)⟫) ∨
  t3n F = -1 ∨
  min ⟪x 0, u0 x (t3n F)⟫ ⟪x 6, u0 x (t3n F)⟫ = max ⟪x 1, u0 x (t3n F)⟫ ⟪x 4, u0 x (t3n F)⟫ ∨
  det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) = 0 ∨
  (∃ s t : ℝ, 0 < s ∧ 0 < t ∧ 1 < s + t ∧
    x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0) ∧ s = 1)

/-- Codimension-1 walls across both orientations (`F` and `sym24 F`). -/
def Wall24 (F : S0xFac 9 s0x_S24 x) : Prop := Wall24_0 F ∨ Wall24_0 (sym24 F)

/-- Special-position residual (codim ≥ 1): a strict leaf case condition holds, but its genericity
condition fails (`¬ HAvail F`). -/
def R24Spec (F : S0xFac 9 s0x_S24 x) : Prop :=
  Hole24NoQ45 x F ∧ ¬ HAvail F ∧ CaseAny F

/-- Codimension-1 wall residual: inside `Wall24 F`, off `CaseAny`. -/
def R24Wall (F : S0xFac 9 s0x_S24 x) : Prop :=
  Hole24NoQ45 x F ∧ ¬ HAvail F ∧ ¬ CaseAny F ∧ Wall24 F

/-- Full-dimensional open residual in `C̄ \ Q45HalfPred`: all leaf case conditions fail off walls. -/
def R24Open (F : S0xFac 9 s0x_S24 x) : Prop :=
  Hole24NoQ45 x F ∧ ¬ HAvail F ∧ ¬ CaseAny F ∧ ¬ Wall24 F

/-- Residual of the OB1-free dispatcher `r_dispatch`. -/
def RResidual' (F : S0xFac 9 s0x_S24 x) : Prop :=
  R24Spec F ∨ R24Wall F ∨ R24Open F

/-! ### Wrappers for the 20 base leaves -/

private theorem leaf_w3p {F : S0xFac 9 s0x_S24 x} (h : H_w3p F) : FaceChordView F 0 :=
  q012_w3_pos F h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2
    h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

private theorem leaf_w3nA {F : S0xFac 9 s0x_S24 x} (h : H_w3nA F) : FaceChordView F 0 :=
  q012_w3_neg_A F h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2.1 h.1.2.2.2.2.2
    h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

private theorem leaf_w3nB {F : S0xFac 9 s0x_S24 x} (h : H_w3nB F) : FaceChordView F 0 :=
  q012_w3_neg_B F h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2
    h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

private theorem leaf_w4n {F : S0xFac 9 s0x_S24 x} (h : H_w4n F) : FaceChordView F 0 :=
  q012_w4_neg F h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2
    h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

private theorem leaf_f346A {F : S0xFac 9 s0x_S24 x} (h : H_f346A F) : FaceChordView F 0 :=
  q012_f346_pos_A_4 F h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2 h.2.1 h.2.2

private theorem leaf_f346B {F : S0xFac 9 s0x_S24 x} (h : H_f346B F) : FaceChordView F 0 :=
  q012_f346_B_4 F h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2 h.2.1 h.2.2

private theorem leaf_LCp {F : S0xFac 9 s0x_S24 x} (h : H_LCp F) : FaceChordView F 0 :=
  q012_LC_plus_gen x F h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2.1 h.1.2.2.2.2.2.1
    h.2.1 h.1.2.2.2.2.2.2.1 h.2.2 h.1.2.2.2.2.2.2.2

private theorem leaf_LCm {F : S0xFac 9 s0x_S24 x} (h : H_LCm F) : FaceChordView F 0 :=
  q012_LC_minus_gen x F h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2.1 h.1.2.2.2.2.2.1
    h.2.1 h.1.2.2.2.2.2.2.1 h.2.2 h.1.2.2.2.2.2.2.2

private theorem leaf_m1 {F : S0xFac 9 s0x_S24 x} (h : H_m1 F) : FaceChordView F 0 := by
  obtain ⟨⟨hN8, hU⟩, hgen, w, hw, hfar, hoff⟩ := h
  exact m1_core F hN8 hU hgen w hw hfar hoff

private theorem leaf_m6 {F : S0xFac 9 s0x_S24 x} (h : H_m6 F) : FaceChordView F 0 := by
  obtain ⟨⟨hN8, hU⟩, hgen, w, hw, hfar, hoff⟩ := h
  exact m6_core F hN8 hU hgen w hw hfar hoff

private theorem leaf_m1p5 {F : S0xFac 9 s0x_S24 x} (h : H_m1p5 F) : FaceChordView F 0 := by
  obtain ⟨⟨hN8, hU⟩, hgen, w, hw, hfar, hoff⟩ := h
  exact m1p5_core F hN8 hU hgen w hw hfar hoff

private theorem leaf_m1p6 {F : S0xFac 9 s0x_S24 x} (h : H_m1p6 F) : FaceChordView F 0 := by
  obtain ⟨⟨hN8, hU⟩, hgen, w, hw, hfar, hoff⟩ := h
  exact m1p6_core F hN8 hU hgen w hw hfar hoff

private theorem leaf_x16lo {F : S0xFac 9 s0x_S24 x} (h : H_x16lo F) : FaceChordView F 0 :=
  q012_x16_lo F h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2.1 h.1.2.2.2.2.2 h.2.1 h.2.2

private theorem leaf_x16hi {F : S0xFac 9 s0x_S24 x} (h : H_x16hi F) : FaceChordView F 0 :=
  q012_x16_hi F h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2.1 h.1.2.2.2.2.2.1
    h.1.2.2.2.2.2.2 h.2.1 h.2.2

private theorem leaf_f0345 {F : S0xFac 9 s0x_S24 x} (h : H_f0345 F) : FaceChordView F 0 :=
  q012_f0345 F h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2
    h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1
    h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2

private theorem leaf_f0345n {F : S0xFac 9 s0x_S24 x} (h : H_f0345n F) : FaceChordView F 0 :=
  q012_f0345_neg_lo F h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2
    h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

private theorem leaf_crossCore {F : S0xFac 9 s0x_S24 x} (h : H_crossCore F) : FaceChordView F 4 :=
  q046_cross_core F h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2 h.2.1 h.2.2

private theorem leaf_crossCbar {F : S0xFac 9 s0x_S24 x} (h : H_crossCbar F) : FaceChordView F 4 :=
  q046_cross_cbar F h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2 h.2.1 h.2.2

private theorem leaf_crossB {F : S0xFac 9 s0x_S24 x} (h : H_crossB F) : FaceChordView F 4 :=
  ropen_cross_core_beta F h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2 h.2.1 h.2.2

private theorem leaf_cop {F : S0xFac 9 s0x_S24 x} (h : H_cop F) : FaceChordView F 4 :=
  q046_coplanar F h.1.1 h.1.2 h.2.1 h.2.2.1 h.2.2.2

private theorem leaf_J0exp {F : S0xFac 9 s0x_S24 x} (h : H_J0exp F) : FaceChordView F 3 := by
  obtain ⟨⟨⟨s, t, hs0, ht, hst, hdec, hs⟩, hN5, hU⟩, hgen, w, hw, hmin, hoff⟩ := h
  exact q45_J0_exp_end_ds F s t hs0 ht hst hdec hs hN5 hU hgen w hw hmin hoff

private theorem leaf_J0expGt {F : S0xFac 9 s0x_S24 x} (h : H_J0expGt F) : FaceChordView F 3 := by
  obtain ⟨⟨⟨s, t, hs0, ht, hst, hdec, hs⟩, hN5, hU⟩, hgen, w, hw, hmin, hoff⟩ := h
  exact q45_J0_exp_end_ds_gt F s t hs0 ht hst hdec hs hN5 hU hgen w hw hmin hoff

private theorem leaf_tie45 {F : S0xFac 9 s0x_S24 x} (h : H_tie45 F) : FaceChordView F 3 := by
  obtain ⟨⟨s, t, hs0, ht, hst, hdec, hα, hβ, h8, h6, hN5, hnot⟩, htie, w, hw, hmin, hoff⟩ := h
  exact q45_J0_tie45 F s t hs0 ht hst hdec (tieAlpha x) (tieBeta x) hα hβ h8 h6 hN5 htie hnot
    w hw hmin hoff

private theorem leaf_KminusE5 {F : S0xFac 9 s0x_S24 x} (h : H_KminusE5 F) : FaceChordView F 3 := by
  obtain ⟨⟨ha5, ⟨s, t, hs0, ht, hst, hdec, hs⟩, hk, h2lo⟩, hS2, hS3, hS4⟩ := h
  exact rj0h_Kminus_e5 F ha5 s t hs0 ht hst hdec hk hs h2lo hS2 hS3 hS4

private theorem leaf_KminusE34 {F : S0xFac 9 s0x_S24 x} (h : H_KminusE34 F) : FaceChordView F 3 := by
  obtain ⟨⟨ha34, ⟨s, t, hs0, ht, hst, hdec, hs⟩, hk, h2lo⟩, hS2, hS3, hS4⟩ := h
  exact rj0h_Kminus_e34 F ha34 s t hs0 ht hst hdec hk hs h2lo hS2 hS3 hS4

/-- Every disjunct of `HAvail F` yields one of the five `FaceChordView` circles `{0, 1, 2, 3, 4}`. -/
theorem avail_closes {F : S0xFac 9 s0x_S24 x} (h : HAvail F) :
    FaceChordView F 0 ∨ FaceChordView F 1 ∨ FaceChordView F 2 ∨
      FaceChordView F 3 ∨ FaceChordView F 4 := by
  rcases h with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl (leaf_w3p h)
  · exact Or.inl (leaf_w3nA h)
  · exact Or.inl (leaf_w3nB h)
  · exact Or.inl (leaf_w4n h)
  · exact Or.inl (leaf_f346A h)
  · exact Or.inl (leaf_f346B h)
  · exact Or.inl (leaf_LCp h)
  · exact Or.inl (leaf_LCm h)
  · exact Or.inl (leaf_m1 h)
  · exact Or.inl (leaf_m6 h)
  · exact Or.inl (leaf_m1p5 h)
  · exact Or.inl (leaf_m1p6 h)
  · exact Or.inl (leaf_x16lo h)
  · exact Or.inl (leaf_x16hi h)
  · exact Or.inl (leaf_f0345 h)
  · exact Or.inl (leaf_f0345n h)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (leaf_crossCore h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (leaf_crossCbar h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (leaf_crossB h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (leaf_cop h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (leaf_J0exp h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (leaf_J0expGt h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (leaf_tie45 h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (leaf_KminusE5 h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (leaf_KminusE34 h))))
  · exact Or.inr (Or.inl (faceChordView_sym F (t := 0) (leaf_w3p h)))
  · exact Or.inr (Or.inl (faceChordView_sym F (t := 0) (leaf_w3nA h)))
  · exact Or.inr (Or.inl (faceChordView_sym F (t := 0) (leaf_w3nB h)))
  · exact Or.inr (Or.inl (faceChordView_sym F (t := 0) (leaf_w4n h)))
  · exact Or.inr (Or.inl (faceChordView_sym F (t := 0) (leaf_f346A h)))
  · exact Or.inr (Or.inl (faceChordView_sym F (t := 0) (leaf_f346B h)))
  · exact Or.inr (Or.inl (faceChordView_sym F (t := 0) (leaf_LCp h)))
  · exact Or.inr (Or.inl (faceChordView_sym F (t := 0) (leaf_LCm h)))
  · exact Or.inr (Or.inl (faceChordView_sym F (t := 0) (leaf_m1 h)))
  · exact Or.inr (Or.inl (faceChordView_sym F (t := 0) (leaf_m6 h)))
  · exact Or.inr (Or.inl (faceChordView_sym F (t := 0) (leaf_m1p5 h)))
  · exact Or.inr (Or.inl (faceChordView_sym F (t := 0) (leaf_m1p6 h)))
  · exact Or.inr (Or.inl (faceChordView_sym F (t := 0) (leaf_x16lo h)))
  · exact Or.inr (Or.inl (faceChordView_sym F (t := 0) (leaf_x16hi h)))
  · exact Or.inr (Or.inl (faceChordView_sym F (t := 0) (leaf_f0345 h)))
  · exact Or.inr (Or.inl (faceChordView_sym F (t := 0) (leaf_f0345n h)))
  · exact Or.inr (Or.inr (Or.inl (faceChordView_sym F (t := 4) (leaf_crossCore h))))
  · exact Or.inr (Or.inr (Or.inl (faceChordView_sym F (t := 4) (leaf_crossCbar h))))
  · exact Or.inr (Or.inr (Or.inl (faceChordView_sym F (t := 4) (leaf_crossB h))))
  · exact Or.inr (Or.inr (Or.inl (faceChordView_sym F (t := 4) (leaf_cop h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (faceChordView_sym F (t := 3) (leaf_J0exp h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (faceChordView_sym F (t := 3) (leaf_J0expGt h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (faceChordView_sym F (t := 3) (leaf_tie45 h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (faceChordView_sym F (t := 3) (leaf_KminusE5 h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (faceChordView_sym F (t := 3) (leaf_KminusE34 h)))))

/-- **Region-R Dispatcher (`r_dispatch`)**: inside `Hole24NoQ45 x F` (`CbarIn x ∧ ¬ Q45HalfPred F`,
without `OB1`), either one of the 40 proved face-chord leaves closes `F`, or `F` falls into
`RResidual' F` (`R24Spec ∨ R24Wall ∨ R24Open`). -/
theorem r_dispatch (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (hQ : ¬ Q45HalfPred F) :
    FaceChordView F 0 ∨ FaceChordView F 1 ∨ FaceChordView F 2 ∨ FaceChordView F 3 ∨
      FaceChordView F 4 ∨ RResidual' F := by
  have hR : Hole24NoQ45 x F := ⟨hC, hQ⟩
  by_cases hA : HAvail F
  · rcases avail_closes hA with h0 | h1 | h2 | h3 | h4
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h2))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h4))))
  · by_cases hCase : CaseAny F
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hR, hA, hCase⟩)))))
    · by_cases hW : Wall24 F
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hR, hA, hCase, hW⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hR, hA, hCase, hW⟩))))))

end RDispatch

end Minimality.T24
