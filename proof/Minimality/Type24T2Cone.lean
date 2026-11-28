module

public import Minimality.Type24WDCell
public import Minimality.Type24WCOrder
public import Minimality.SameView

/-!
# Hidden-`2` cone `T_2` (`cA2 = ![0, 5, 3, 6, 1]`, `cB2 = ![0, 5, 3, 4, 6, 1]`, Carbon A85)

* `FS2` (`uT2_four_facets`, `cA2_cellAt_iff`, `cB2_cellAt_iff`, `CA2CertAt`, `CB2CertAt`, the
  `cA2_lexAny_of_z0_lt` (Lemma Z) / `uT2_depth_signs` results): the `T_2 = {0, 2, 5, 6, 7}` cone around vertex `2`.
  The per-certificate Edge-Plane arrows and the `TwoConeResidue_FS2` chain were deleted
  (11-27 pass 2); the named residue now goes through the cells (`Type24CellWall`).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.M4
open Minimality.T24.HC Minimality.T24.SF Minimality.T24.DeepC

namespace Minimality.T24.TwoCone

/-! ## `T_2` cone cells `cA2 = ![0, 5, 3, 6, 1]` and `cB2 = ![0, 5, 3, 4, 6, 1]` -/

/-- Rim `cA2 = ![0, 5, 3, 6, 1]` (`3.5.0.1.6` reversed, hiding `2` and `4`). -/
def cA2 : ZMod 5 → Fin 7 := ![0, 5, 3, 6, 1]

/-- Rim `cB2 = ![0, 5, 3, 4, 6, 1]` (`3.5.0.1.6.4` reversed, hiding `2`). -/
def cB2 : ZMod 6 → Fin 7 := ![0, 5, 3, 4, 6, 1]

theorem cA2_inj : Function.Injective cA2 := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)

theorem cB2_inj : Function.Injective cB2 := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)

/-- Up facets `{1, 3, 4, 8}` of `cA2`. -/
def U_A2 : Finset (Fin 9) := {1, 3, 4, 8}

/-- Down facets `{0, 2, 5, 6, 7}` (`T_2`) of `cA2`. -/
def D_A2 : Finset (Fin 9) := {0, 2, 5, 6, 7}

/-- Up facets `{1, 3, 4}` of `cB2`. -/
def U_B2 : Finset (Fin 9) := {1, 3, 4}

theorem cA2_cyc : S0xCycUD s0x_S24 cA2 U_A2 D_A2 := by
  decide

/-- View `u_{T_2}(x, β, γ) := capView x 1 (-β) γ`. -/
noncomputable def uT2 (x : Fin 7 → ℝ³) (beta gamma : ℝ) : ℝ³ :=
  capView x 1 (-beta) gamma

/-- On `uT2 x β γ` with `CbarIn x`, `β > 0`, `γ > 0`, four facets `{1, 4}` (`> 0`) and
`{0, 5}` (`< 0`) hold automatically. -/
theorem uT2_four_facets {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    {beta gamma : ℝ} (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    0 < ⟪F.N 1, uT2 x beta gamma⟫ ∧ 0 < ⟪F.N 4, uT2 x beta gamma⟫ ∧
    ⟪F.N 0, uT2 x beta gamma⟫ < 0 ∧ ⟪F.N 5, uT2 x beta gamma⟫ < 0 := by
  have T := type24OfFac F
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [uT2, inner_cap, F.zero 1 1 (by decide), F.zero 1 0 (by decide), F.zero 1 6 (by decide)]
    have hf := F.neg 1 2 (by decide)
    nlinarith
  · rw [uT2, inner_cap, F.zero 4 0 (by decide), F.zero 4 6 (by decide)]
    have e4 := fac_eval F 4 4
    rw [F.zero 4 4 (by decide), F.zero 4 0 (by decide), F.zero 4 6 (by decide)] at e4
    have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
    have h4eq := eq4 F
    have hf21 : F.f 4 (x 2) - F.f 4 (x 1) = omega4 x * F.f 4 (x 1) := by
      have hmul : oblX2 x 4 * (F.f 4 (x 2) - F.f 4 (x 1)) =
          oblX2 x 4 * (omega4 x * F.f 4 (x 1)) := by
        linear_combination -e4 + F.f 4 (x 1) * h4eq
      exact mul_left_cancel₀ hb4.ne' hmul
    have hf1 : F.f 4 (x 1) < 0 := F.neg 4 1 (by decide)
    have hw4 : 0 < omega4 x := hC.2.1
    rw [hf21]
    have heval : 1 * (0 - F.f 4 (x 1)) + -beta * (omega4 x * F.f 4 (x 1)) +
        gamma * (0 - F.f 4 (x 1)) = -(1 + omega4 x * beta + gamma) * F.f 4 (x 1) := by ring
    rw [heval]
    have hpos : 0 < 1 + omega4 x * beta + gamma := by nlinarith
    exact mul_pos_of_neg_of_neg (by linarith) hf1
  · rw [uT2, inner_cap, F.zero 0 1 (by decide), F.zero 0 0 (by decide), F.zero 0 2 (by decide)]
    have hf := F.neg 0 6 (by decide)
    nlinarith
  · rw [uT2, inner_cap, F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)]
    have hf := F.neg 5 0 (by decide)
    nlinarith

/-- `CA2CertAt x F β γ`: interior `(U_A2, D_A2)` cell conditions and strict line separation at
`uT2 x β γ` on some edge `a : ZMod 5` of `cA2 = ![0, 5, 3, 6, 1]`. -/
def CA2CertAt (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) (beta gamma : ℝ) : Prop :=
  0 < beta ∧ 0 < gamma ∧
  ⟪F.N 2, uT2 x beta gamma⟫ < 0 ∧ 0 < ⟪F.N 3, uT2 x beta gamma⟫ ∧
  ⟪F.N 6, uT2 x beta gamma⟫ < 0 ∧ ⟪F.N 7, uT2 x beta gamma⟫ < 0 ∧
  0 < ⟪F.N 8, uT2 x beta gamma⟫ ∧
  ∃ a : ZMod 5,
    ⟪x (cA2 (a + 1)) - x (cA2 a), uT2 x beta gamma⟫ ≠ 0 ∧
    (∀ i : ZMod 5, i ≠ a →
      Split.det3 (x (cA2 (i + 1)) - x (cA2 i)) (x (cA2 (a + 1)) - x (cA2 a)) (uT2 x beta gamma) ≠ 0) ∧
    ∃ sh α' μ' : ℝ, (sh = 1 ∨ sh = -1) ∧
      (∀ i j : ZMod 5, i ≠ a → (j = i ∨ j = i + 1) →
        0 < Split.det3 (x (cA2 (i + 1)) - x (cA2 i)) (x (cA2 (a + 1)) - x (cA2 a)) (uT2 x beta gamma) →
        (-sh * ⟪Split.Slope.linSpinVec (fun t => x (cA2 t)) a i j, uT2 x beta gamma⟫ /
            Split.det3 (x (cA2 (i + 1)) - x (cA2 i)) (x (cA2 (a + 1)) - x (cA2 a)) (uT2 x beta gamma)) -
          μ' * ⟪x (cA2 j) - x (cA2 a), uT2 x beta gamma⟫ < α') ∧
      (∀ p q : ZMod 5, p ≠ a → (q = p ∨ q = p + 1) →
        Split.det3 (x (cA2 (p + 1)) - x (cA2 p)) (x (cA2 (a + 1)) - x (cA2 a)) (uT2 x beta gamma) < 0 →
        α' < (-sh * ⟪Split.Slope.linSpinVec (fun t => x (cA2 t)) a p q, uT2 x beta gamma⟫ /
            Split.det3 (x (cA2 (p + 1)) - x (cA2 p)) (x (cA2 (a + 1)) - x (cA2 a)) (uT2 x beta gamma)) -
          μ' * ⟪x (cA2 q) - x (cA2 a), uT2 x beta gamma⟫)

/-- `CB2CertAt x F β γ`: interior `(U_B2, D_B2)` cell conditions and strict line separation at
`uT2 x β γ` on some edge `a : ZMod 6` of `cB2 = ![0, 5, 3, 4, 6, 1]`. -/
def CB2CertAt (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) (beta gamma : ℝ) : Prop :=
  0 < beta ∧ 0 < gamma ∧
  ⟪F.N 2, uT2 x beta gamma⟫ < 0 ∧ 0 < ⟪F.N 3, uT2 x beta gamma⟫ ∧
  ⟪F.N 6, uT2 x beta gamma⟫ < 0 ∧ ⟪F.N 7, uT2 x beta gamma⟫ < 0 ∧
  ⟪F.N 8, uT2 x beta gamma⟫ < 0 ∧
  ∃ a : ZMod 6,
    ⟪x (cB2 (a + 1)) - x (cB2 a), uT2 x beta gamma⟫ ≠ 0 ∧
    (∀ i : ZMod 6, i ≠ a →
      Split.det3 (x (cB2 (i + 1)) - x (cB2 i)) (x (cB2 (a + 1)) - x (cB2 a)) (uT2 x beta gamma) ≠ 0) ∧
    ∃ sh α' μ' : ℝ, (sh = 1 ∨ sh = -1) ∧
      (∀ i j : ZMod 6, i ≠ a → (j = i ∨ j = i + 1) →
        0 < Split.det3 (x (cB2 (i + 1)) - x (cB2 i)) (x (cB2 (a + 1)) - x (cB2 a)) (uT2 x beta gamma) →
        (-sh * ⟪Split.Slope.linSpinVec (fun t => x (cB2 t)) a i j, uT2 x beta gamma⟫ /
            Split.det3 (x (cB2 (i + 1)) - x (cB2 i)) (x (cB2 (a + 1)) - x (cB2 a)) (uT2 x beta gamma)) -
          μ' * ⟪x (cB2 j) - x (cB2 a), uT2 x beta gamma⟫ < α') ∧
      (∀ p q : ZMod 6, p ≠ a → (q = p ∨ q = p + 1) →
        Split.det3 (x (cB2 (p + 1)) - x (cB2 p)) (x (cB2 (a + 1)) - x (cB2 a)) (uT2 x beta gamma) < 0 →
        α' < (-sh * ⟪Split.Slope.linSpinVec (fun t => x (cB2 t)) a p q, uT2 x beta gamma⟫ /
            Split.det3 (x (cB2 (p + 1)) - x (cB2 p)) (x (cB2 (a + 1)) - x (cB2 a)) (uT2 x beta gamma)) -
          μ' * ⟪x (cB2 q) - x (cB2 a), uT2 x beta gamma⟫)

/-- **FV2 (`CA2OCCertAt`):** `CA2` cell conditions plus `OrderCertAt` at `uT2 x β γ`. -/
def CA2OCCertAt (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) (beta gamma : ℝ) : Prop :=
  0 < beta ∧ 0 < gamma ∧
  ⟪F.N 2, uT2 x beta gamma⟫ < 0 ∧ 0 < ⟪F.N 3, uT2 x beta gamma⟫ ∧
  ⟪F.N 6, uT2 x beta gamma⟫ < 0 ∧ ⟪F.N 7, uT2 x beta gamma⟫ < 0 ∧
  0 < ⟪F.N 8, uT2 x beta gamma⟫ ∧
  Split.Slope.OrderCertAt (fun t => x (cA2 t)) (uT2 x beta gamma)

/-- **FV2 (`CB2OCCertAt`):** `CB2` cell conditions plus `OrderCertAt` at `uT2 x β γ`. -/
def CB2OCCertAt (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) (beta gamma : ℝ) : Prop :=
  0 < beta ∧ 0 < gamma ∧
  ⟪F.N 2, uT2 x beta gamma⟫ < 0 ∧ 0 < ⟪F.N 3, uT2 x beta gamma⟫ ∧
  ⟪F.N 6, uT2 x beta gamma⟫ < 0 ∧ ⟪F.N 7, uT2 x beta gamma⟫ < 0 ∧
  ⟪F.N 8, uT2 x beta gamma⟫ < 0 ∧
  Split.Slope.OrderCertAt (fun t => x (cB2 t)) (uT2 x beta gamma)

theorem cA2CertAt_of_oc {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} {beta gamma : ℝ}
    (hoc : CA2OCCertAt x F beta gamma) : CA2CertAt x F beta gamma := by
  rcases hoc with ⟨hb, hg, h2, h3, h6, h7, h8, a, hD0, hc_ne0, sh, hsh, hOrd, hEq⟩
  obtain ⟨α', μ', hB, hO⟩ := Split.Slope.lineSep_of_depthOrder_ties
    (fun t => x (cA2 t)) (uT2 x beta gamma) a sh hOrd hEq
  exact ⟨hb, hg, h2, h3, h6, h7, h8, a, hD0, hc_ne0, sh, α', μ', hsh, hB, hO⟩

theorem cB2CertAt_of_oc {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} {beta gamma : ℝ}
    (hoc : CB2OCCertAt x F beta gamma) : CB2CertAt x F beta gamma := by
  rcases hoc with ⟨hb, hg, h2, h3, h6, h7, h8, a, hD0, hc_ne0, sh, hsh, hOrd, hEq⟩
  obtain ⟨α', μ', hB, hO⟩ := Split.Slope.lineSep_of_depthOrder_ties
    (fun t => x (cB2 t)) (uT2 x beta gamma) a sh hOrd hEq
  exact ⟨hb, hg, h2, h3, h6, h7, h8, a, hD0, hc_ne0, sh, α', μ', hsh, hB, hO⟩

/-! ## Task FX: Lemma Z (`cA2` unimodal when `z₀ < z₁`) and Corollary Z1 -/

/-- **FX1 (Fact 1):** under `OB1 x` and `0 < β, γ`, at `uT2 x β γ` we have `z₂ < 0 (= z₁)`,
and `z₀ ≤ 0 → 0 < z₆` (by strict Cauchy-Schwarz on non-collinear `x₀ - x₁, x₆ - x₁`). -/
theorem uT2_depth_signs {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hO : H24K.SAT.OB1 x)
    {beta gamma : ℝ} (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    ⟪x 2 - x 1, uT2 x beta gamma⟫ < 0 ∧
      (⟪x 0 - x 1, uT2 x beta gamma⟫ ≤ 0 → 0 < ⟪x 6 - x 1, uT2 x beta gamma⟫) := by
  obtain ⟨hab, hac, hbc⟩ := hO
  have hx21 : x 2 - x 1 ≠ 0 := by
    intro h
    have hf := F.hN 2 (x 2) (x 1)
    rw [h, inner_zero_right, F.zero 2 2 (by decide)] at hf
    linarith [F.neg 2 1 (by decide)]
  have hx01 : x 0 - x 1 ≠ 0 := by
    intro h
    have hf := F.hN 5 (x 0) (x 1)
    rw [h, inner_zero_right, F.zero 5 1 (by decide)] at hf
    linarith [F.neg 5 0 (by decide)]
  have hbb : 0 < ⟪x 2 - x 1, x 2 - x 1⟫ := real_inner_self_pos.mpr hx21
  have haa : 0 < ⟪x 0 - x 1, x 0 - x 1⟫ := real_inner_self_pos.mpr hx01
  refine ⟨?_, fun hz0 => ?_⟩
  · dsimp only [uT2, capView]
    rw [inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right]
    have hcomm20 : ⟪x 2 - x 1, x 0 - x 1⟫ = ⟪x 0 - x 1, x 2 - x 1⟫ := real_inner_comm _ _
    rw [hcomm20]
    nlinarith [mul_pos hbeta hbb, mul_nonpos_of_nonneg_of_nonpos hgamma.le hbc]
  · have hcs : ⟪x 0 - x 1, x 6 - x 1⟫ ^ 2 <
        ⟪x 0 - x 1, x 0 - x 1⟫ * ⟪x 6 - x 1, x 6 - x 1⟫ := by
      have hle : ⟪x 0 - x 1, x 6 - x 1⟫ ^ 2 ≤
          ⟪x 0 - x 1, x 0 - x 1⟫ * ⟪x 6 - x 1, x 6 - x 1⟫ := by
        have h := abs_real_inner_le_norm (x 0 - x 1) (x 6 - x 1)
        have hsq : |⟪x 0 - x 1, x 6 - x 1⟫| ^ 2 ≤ (‖x 0 - x 1‖ * ‖x 6 - x 1‖) ^ 2 :=
          sq_le_sq' (by linarith [abs_nonneg ⟪x 0 - x 1, x 6 - x 1⟫]) h
        rw [sq_abs, mul_pow, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq] at hsq
        exact hsq
      refine lt_of_le_of_ne hle (fun heq => ?_)
      have key_orth : ∀ (a b : ℝ³), ⟪a, b⟫ ^ 2 = ⟪a, a⟫ * ⟪b, b⟫ →
          ⟪⟪a, a⟫ • b - ⟪a, b⟫ • a, ⟪a, a⟫ • b - ⟪a, b⟫ • a⟫ = 0 := by
        intro a b hab_eq
        simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
        have hcomm : ⟪b, a⟫ = ⟪a, b⟫ := real_inner_comm a b
        rw [hcomm]
        linear_combination -⟪a, a⟫ * hab_eq
      let w0 : ℝ³ := ⟪x 0 - x 1, x 0 - x 1⟫ • (x 6 - x 1) -
        ⟪x 0 - x 1, x 6 - x 1⟫ • (x 0 - x 1)
      have hw0' : w0 = 0 := inner_self_eq_zero.mp (key_orth _ _ heq)
      have hfn := congrArg (fun v => ⟪F.N 0, v⟫) hw0'
      rw [inner_zero_right] at hfn
      dsimp only [w0] at hfn
      rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right,
        ← F.hN 0 (x 6) (x 1), ← F.hN 0 (x 0) (x 1),
        F.zero 0 0 (by decide), F.zero 0 1 (by decide)] at hfn
      simp only [sub_zero, mul_zero] at hfn
      have hf06 : F.f 0 (x 6) < 0 := F.neg 0 6 (by decide)
      exact absurd hfn (ne_of_lt (mul_neg_of_pos_of_neg haa hf06))
    dsimp only [uT2, capView] at hz0 ⊢
    rw [inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right] at hz0 ⊢
    have hcomm60 : ⟪x 6 - x 1, x 0 - x 1⟫ = ⟪x 0 - x 1, x 6 - x 1⟫ := real_inner_comm _ _
    have hcomm62 : ⟪x 6 - x 1, x 2 - x 1⟫ = ⟪x 2 - x 1, x 6 - x 1⟫ := real_inner_comm _ _
    have h1 : ⟪x 0 - x 1, x 0 - x 1⟫ + gamma * ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0 := by
      nlinarith [mul_nonneg hbeta.le (neg_nonneg.mpr hab)]
    have h2 : 0 < gamma * (⟪x 0 - x 1, x 6 - x 1⟫ + gamma * ⟪x 6 - x 1, x 6 - x 1⟫) := by
      have hmul : ⟪x 0 - x 1, x 0 - x 1⟫ * (gamma * ⟪x 0 - x 1, x 6 - x 1⟫ +
          gamma ^ 2 * ⟪x 6 - x 1, x 6 - x 1⟫) > 0 := by
        nlinarith [mul_nonneg (show 0 ≤ -(gamma * ⟪x 0 - x 1, x 6 - x 1⟫) by linarith)
          (show 0 ≤ -(⟪x 0 - x 1, x 0 - x 1⟫ + gamma * ⟪x 0 - x 1, x 6 - x 1⟫) by linarith),
          mul_pos (sq_pos_of_pos hgamma) (sub_pos.mpr hcs)]
      have hpos : 0 < gamma * ⟪x 0 - x 1, x 6 - x 1⟫ + gamma ^ 2 * ⟪x 6 - x 1, x 6 - x 1⟫ :=
        pos_of_mul_pos_right hmul haa.le
      linarith
    have hmul_pos : 0 < gamma * (1 * ⟪x 6 - x 1, x 0 - x 1⟫ + -beta * ⟪x 6 - x 1, x 2 - x 1⟫ +
        gamma * ⟪x 6 - x 1, x 6 - x 1⟫) := by
      rw [hcomm60, hcomm62]
      nlinarith [mul_nonneg hgamma.le (mul_nonneg hbeta.le (neg_nonneg.mpr hbc))]
    exact pos_of_mul_pos_right hmul_pos hgamma.le

private theorem cA2_frontDiag_aux {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {w : ℝ³}
    (hcell : CellAt F U_A2 D_A2 w) {v : Fin 7} (hv : v = 6 ∨ v = 1) :
    ¬ (max ⟪x 0, w⟫ ⟪x 3, w⟫ ≤ min ⟪x 5, w⟫ ⟪x v, w⟫) := by
  have hw3 : 0 < ⟪F.N 3, w⟫ := hcell.1 3 (by decide)
  have hw0 : w ≠ 0 := by
    intro h; rw [h, inner_zero_right] at hw3; exact lt_irrefl 0 hw3
  have hfv : F.f 3 (x v) < 0 := by
    rcases hv with rfl | rfl <;> exact F.neg 3 _ (by decide)
  have hfront : FrontDiag (x 0) (x 3) (x 5) (x v) w := by
    have hrim_cases := LexEP.strictRimN_of_openCell (by norm_num) F cA2_inj cA2_cyc hcell
    have get_det : (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
        0 < det3 (x (cA2 (i + 1)) - x (cA2 i)) (x (cA2 j) - x (cA2 i)) w) ∨
        (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
        0 < det3 (x (cA2 i) - x (cA2 (i + 1))) (x (cA2 j) - x (cA2 (i + 1))) w) := by
      rcases hrim_cases with hccw | hcw
      · left; intro i j h1 h2
        rw [← Split.det3_eq_minimality]
        exact hccw (cA2 j) i (fun e => h1 (cA2_inj e)) (fun e => h2 (cA2_inj e))
      · right; intro i j h1 h2
        have h := hcw (cA2 j) (-i - 1)
          (fun e => by have hj := cA2_inj e; apply h2; linear_combination hj)
          (fun e => by have hj := cA2_inj e; apply h1; linear_combination hj)
        have hc1 : cA2 (-(-i - 1 + 1)) = cA2 i := by congr 1; ring
        have hc0 : cA2 (-(-i - 1)) = cA2 (i + 1) := by congr 1; ring
        change 0 < Split.det3 (x (cA2 (-(-i - 1 + 1))) - x (cA2 (-(-i - 1))))
          (x (cA2 j) - x (cA2 (-(-i - 1)))) w at h
        rw [hc1, hc0, Split.det3_eq_minimality] at h
        exact h
    have build_fd : ∀ (v1 v2 : Fin 7) (hv12 : (v1 = 5 ∧ v2 = v) ∨ (v1 = v ∧ v2 = 5))
        (q1 : 0 < det3 (x v1 - x 0) (x 3 - x 0) w)
        (q2 : 0 < det3 (x 3 - x v1) (x v2 - x v1) w)
        (q3 : 0 < det3 (x v2 - x 3) (x 0 - x 3) w)
        (q4 : 0 < det3 (x 0 - x v2) (x v1 - x v2) w), FrontDiag (x 0) (x 3) (x 5) (x v) w := by
      intro v1 v2 hv12 q1 q2 q3 q4
      have hsm : SegMeet (x 0) (x 3) (x v1) (x v2) w := by
        refine segMeet_of_sides ?_ ?_
        · have i1 : det3 (x 3 - x 0) (x v1 - x 0) w = -det3 (x v1 - x 0) (x 3 - x 0) w := by
            simp only [det3_expand, PiLp.sub_apply]; ring
          have i2 : det3 (x 3 - x 0) (x v2 - x 0) w = det3 (x v2 - x 3) (x 0 - x 3) w := by
            simp only [det3_expand, PiLp.sub_apply]; ring
          rw [i1, i2]; nlinarith
        · have i3 : det3 (x v2 - x v1) (x 0 - x v1) w = det3 (x 0 - x v2) (x v1 - x v2) w := by
            simp only [det3_expand, PiLp.sub_apply]; ring
          have i4 : det3 (x v2 - x v1) (x 3 - x v1) w = -det3 (x 3 - x v1) (x v2 - x v1) w := by
            simp only [det3_expand, PiLp.sub_apply]; ring
          rw [i3, i4]; nlinarith
      obtain ⟨s, t, μ, hs0, hs1, ht0, ht1, he⟩ := hsm
      have ht_pos : 0 < t := by
        refine lt_of_le_of_ne ht0 (fun ht => ?_)
        rw [← ht, zero_smul, add_zero] at he
        have hdet0 : det3 (x 3 - x 0) (x v1 - x 0) w = 0 := by
          have : x v1 - x 0 = s • (x 3 - x 0) + μ • w := by rw [← he]; abel
          rw [this]
          simp only [det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
          ring
        have : det3 (x v1 - x 0) (x 3 - x 0) w = 0 := by
          have : det3 (x v1 - x 0) (x 3 - x 0) w = -det3 (x 3 - x 0) (x v1 - x 0) w := by
            simp only [det3_expand, PiLp.sub_apply]; ring
          linarith
        linarith
      have hhe : (x v1 - x 0) + t • (x v2 - x v1) - s • (x 3 - x 0) = μ • w := by
        rw [← he]; abel
      have hfn := congrArg (fun z => ⟪F.N 3, z⟫) hhe
      rw [inner_sub_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
        real_inner_smul_right, ← F.hN 3 (x v1) (x 0), ← F.hN 3 (x v2) (x v1),
        ← F.hN 3 (x 3) (x 0), F.zero 3 0 (by decide), F.zero 3 3 (by decide)] at hfn
      simp only [sub_zero, mul_zero] at hfn
      have hμ : μ < 0 := by
        rcases hv12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [F.zero 3 5 (by decide), sub_zero, zero_add] at hfn
          have hprod : μ * ⟪F.N 3, w⟫ < 0 := by nlinarith [mul_pos ht_pos (neg_pos.mpr hfv)]
          by_contra hge; push Not at hge
          exact absurd hprod (not_lt.mpr (mul_nonneg hge hw3.le))
        · have ht_lt : t < 1 := by
            refine lt_of_le_of_ne ht1 (fun ht => ?_)
            rw [ht, one_smul] at he
            have h53 : x 5 - x 3 = (s - 1) • (x 3 - x 0) + μ • w := by
              calc x 5 - x 3 = (x v1 + (x 5 - x v1) - (x 0 + s • (x 3 - x 0))) +
                  (x 0 + s • (x 3 - x 0) - x 3) := by abel
                _ = μ • w + (s - 1) • (x 3 - x 0) := by rw [he]; module
                _ = (s - 1) • (x 3 - x 0) + μ • w := by abel
            have hdet53 : det3 (x 5 - x 3) (x 0 - x 3) w = 0 := by
              rw [h53]
              simp only [det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
              ring
            linarith
          rw [F.zero 3 5 (by decide), zero_sub] at hfn
          have hprod : μ * ⟪F.N 3, w⟫ < 0 := by
            nlinarith [mul_pos (sub_pos.mpr ht_lt) (neg_pos.mpr hfv)]
          by_contra hge; push Not at hge
          exact absurd hprod (not_lt.mpr (mul_nonneg hge hw3.le))
      have hfd : FrontDiag (x 0) (x 3) (x v1) (x v2) w :=
        ⟨s, t, -μ, hs0, hs1, ht0, ht1, by linarith, by rw [neg_smul, ← he]; abel⟩
      rcases hv12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hfd
      · exact hfd.swap_e
    have cyc_det : ∀ a b c : ℝ³, det3 (b - a) (c - a) w = det3 (c - b) (a - b) w := fun a b c => by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rcases get_det with hccw | hcw
    · rcases hv with rfl | rfl
      · refine build_fd 5 6 (Or.inl ⟨rfl, rfl⟩)
          (hccw 0 2 (by decide) (by decide)) (hccw 1 3 (by decide) (by decide))
          (hccw 2 0 (by decide) (by decide)) ?_
        rw [cyc_det]; exact hccw 0 3 (by decide) (by decide)
      · refine build_fd 5 1 (Or.inl ⟨rfl, rfl⟩)
          (hccw 0 2 (by decide) (by decide)) (hccw 1 4 (by decide) (by decide))
          ?_ (hccw 4 1 (by decide) (by decide))
        rw [cyc_det]; exact hccw 4 2 (by decide) (by decide)
    · rcases hv with rfl | rfl
      · refine build_fd 6 5 (Or.inr ⟨rfl, rfl⟩) ?_ (hcw 2 1 (by decide) (by decide))
          (hcw 1 0 (by decide) (by decide)) (hcw 0 3 (by decide) (by decide))
        rw [cyc_det]; exact hcw 2 0 (by decide) (by decide)
      · refine build_fd 1 5 (Or.inr ⟨rfl, rfl⟩) (hcw 4 2 (by decide) (by decide))
          ?_ (hcw 1 0 (by decide) (by decide)) (hcw 0 4 (by decide) (by decide))
        rw [cyc_det]; exact hcw 1 4 (by decide) (by decide)
  exact hfront.not_back hw0

/-- **FX2 (Fact 2):** in `cA2` (`0345` front, rim order `0, 5, 3, 6`), `z₅, z₆ ≥ z₀, z₃`
is impossible (since `[0, 3]` is a front diagonal of facet `3` = `0345`). -/
theorem cA2_not_back_03_56 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {w : ℝ³}
    (hcell : CellAt F U_A2 D_A2 w) :
    ¬ (max ⟪x 0, w⟫ ⟪x 3, w⟫ ≤ min ⟪x 5, w⟫ ⟪x 6, w⟫) :=
  cA2_frontDiag_aux F hcell (Or.inl rfl)

/-- **FX3 (Lemma Z):** every `cA2` open-cell view `uT2 x β γ` with `z₀ < z₁ (= 0)` under `OB1 x`
has `RobUni` depths on `cA2 = ![0, 5, 3, 6, 1]`. -/
theorem cA2_robUni_of_z0_lt {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hO : H24K.SAT.OB1 x)
    {beta gamma : ℝ} (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hcell : CellAt F U_A2 D_A2 (uT2 x beta gamma))
    (hz0 : ⟪x 0 - x 1, uT2 x beta gamma⟫ < 0) :
    H21.RobUni (fun i => ⟪x (cA2 i), uT2 x beta gamma⟫) := by
  have hz6 : 0 < ⟪x 6 - x 1, uT2 x beta gamma⟫ :=
    (uT2_depth_signs F hO hbeta hgamma).2 hz0.le
  have hz0' : ⟪x 0, uT2 x beta gamma⟫ < ⟪x 1, uT2 x beta gamma⟫ := by
    rw [inner_sub_left] at hz0; linarith
  have hz6' : ⟪x 1, uT2 x beta gamma⟫ < ⟪x 6, uT2 x beta gamma⟫ := by
    rw [inner_sub_left] at hz6; linarith
  have hnb6 := cA2_frontDiag_aux F hcell (Or.inl rfl)
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
      exact hnb6 (max_le (le_min (by linarith) (by linarith)) (le_min (by linarith) (by linarith)))

/-- **FX3 (`cA2_lexAny_of_z0_lt`):** `cA2` open cell + `OB1` + `z₀ < z₁` yields `Gen.LexAny F`. -/
theorem cA2_lexAny_of_z0_lt {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hO : H24K.SAT.OB1 x)
    {beta gamma : ℝ} (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hcell : CellAt F U_A2 D_A2 (uT2 x beta gamma))
    (hz0 : ⟪x 0 - x 1, uT2 x beta gamma⟫ < 0) :
    Gen.LexAny F :=
  WC.lexAny_of_cellAt_robUni (by norm_num) F cA2_inj cA2_cyc hcell
    (cA2_robUni_of_z0_lt F hO hbeta hgamma hcell hz0)

end Minimality.T24.TwoCone
