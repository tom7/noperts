module

public import Minimality.Type24T2Cone

/-!
# Interior `T_0` cone leaves (`CA0CertAt`, `CB0CertAt`, Carbon A86 Section 0)

* `FT1`: interior views `uT0 x b gamma := capView x (-1) b gamma` (`b > 0, gamma > 0`) in
  `T_0 = {0, 1, 2, 3, 4 < 0}`, exact 5-active-facet `gamma` windows `(gamma_A0_lo, gamma_A0_hi)`
  and `(gamma_B0_lo, gamma_B0_hi)` (`iff CellAt`), automatic `HiddenInTriangles` for vertices
  `0` and `4` on `cA`, interior leaves `cA0_edgePlaneAny` / `cB0_edgePlaneAny`, `CA0CertAt`,
  `CB0CertAt`, hole facts, and `π_24` twins.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.M4
open Minimality.T24.HC Minimality.T24.SF Minimality.T24.DeepC

namespace Minimality.T24.TwoCone

/-! ## Interior `T_0` cells `(U_A0, D_A0)` and `(U_B0, D_B0)` -/

/-- Up facets `{5, 6, 7}` of `cA = ![1, 2, 5, 3, 6]`. -/
def U_A0 : Finset (Fin 9) := {5, 6, 7}

/-- Down facets `{0, 1, 2, 3, 4, 8}` of `cA = ![1, 2, 5, 3, 6]`. -/
def D_A0 : Finset (Fin 9) := {0, 1, 2, 3, 4, 8}

/-- Up facets `{5, 6, 7, 8}` of `cB = ![1, 2, 5, 3, 4, 6]`. -/
def U_B0 : Finset (Fin 9) := {5, 6, 7, 8}

/-- Down facets `{0, 1, 2, 3, 4}` of `cB = ![1, 2, 5, 3, 4, 6]`. -/
def D_B0 : Finset (Fin 9) := {0, 1, 2, 3, 4}

theorem cA_cycUD : S0xCycUD s0x_S24 cA U_A0 D_A0 := by
  decide

theorem cB_cycUD : S0xCycUD s0x_S24 cB U_B0 D_B0 := by
  decide

/-- Interior `T_0` view `u_{T_0}(x, b, γ) := capView x (-1) b γ`. -/
noncomputable def uT0 (x : Fin 7 → ℝ³) (b gamma : ℝ) : ℝ³ :=
  capView x (-1) b gamma

/-- On `uT0 x b γ` with `CbarIn x`, `b > 0`, `γ > 0`, four facets `{5, 7}` (`> 0`) and
`{0, 1}` (`< 0`) hold automatically. -/
theorem uT0_four_facets {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    {b gamma : ℝ} (hb : 0 < b) (hgamma : 0 < gamma) :
    0 < ⟪F.N 5, uT0 x b gamma⟫ ∧ 0 < ⟪F.N 7, uT0 x b gamma⟫ ∧
    ⟪F.N 0, uT0 x b gamma⟫ < 0 ∧ ⟪F.N 1, uT0 x b gamma⟫ < 0 := by
  have T := type24OfFac F
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [uT0, inner_cap, F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)]
    have hf := F.neg 5 0 (by decide)
    nlinarith
  · rw [uT0, inner_cap, F.zero 7 2 (by decide), F.zero 7 6 (by decide)]
    have e3 := fac_eval F 7 3
    rw [F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at e3
    have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
    have h3eq := eq3 F
    have hf01 : F.f 7 (x 0) - F.f 7 (x 1) = omega3 x * F.f 7 (x 1) := by
      have hmul : oblX0 x 3 * (F.f 7 (x 0) - F.f 7 (x 1)) =
          oblX0 x 3 * (omega3 x * F.f 7 (x 1)) := by
        linear_combination -e3 + F.f 7 (x 1) * h3eq
      exact mul_left_cancel₀ ha3.ne' hmul
    have hf1 : F.f 7 (x 1) < 0 := F.neg 7 1 (by decide)
    have hw3 : 0 < omega3 x := hC.1
    rw [hf01]
    have heval : -1 * (omega3 x * F.f 7 (x 1)) + b * (0 - F.f 7 (x 1)) +
        gamma * (0 - F.f 7 (x 1)) = -(omega3 x + b + gamma) * F.f 7 (x 1) := by ring
    rw [heval]
    exact mul_pos_of_neg_of_neg (by linarith) hf1
  · rw [uT0, inner_cap, F.zero 0 1 (by decide), F.zero 0 0 (by decide), F.zero 0 2 (by decide)]
    have hf := F.neg 0 6 (by decide)
    nlinarith
  · rw [uT0, inner_cap, F.zero 1 1 (by decide), F.zero 1 0 (by decide), F.zero 1 6 (by decide)]
    have hf := F.neg 1 2 (by decide)
    nlinarith

/-! ## Pure-shape `γ` window `(gamma_A0_lo, gamma_A0_hi)` and `(gamma_B0_lo, gamma_B0_hi)` -/

noncomputable def t0_Delta_bc (x : Fin 7 → ℝ³) : ℝ :=
  oblX2 x 5 * oblX6 x 4 - oblX2 x 4 * oblX6 x 5

noncomputable def t0_nB (x : Fin 7 → ℝ³) : ℝ :=
  (1 - oblX0 x 5) * oblX6 x 4 - (1 - oblX0 x 4) * oblX6 x 5

noncomputable def t0_nC (x : Fin 7 → ℝ³) : ℝ :=
  -(1 - oblX0 x 5) * oblX2 x 4 + (1 - oblX0 x 4) * oblX2 x 5

noncomputable def t0_d6 (x : Fin 7 → ℝ³) : ℝ :=
  oblX0 x 5 * oblX6 x 3 - oblX0 x 3 * oblX6 x 5

noncomputable def t0_d8 (x : Fin 7 → ℝ³) : ℝ :=
  oblX0 x 4 * oblX2 x 3 - oblX0 x 3 * oblX2 x 4

noncomputable def t0_s6 (x : Fin 7 → ℝ³) : ℝ :=
  oblX0 x 5 * (oblX2 x 3 - 1) - oblX0 x 3 * (oblX2 x 5 - 1)

noncomputable def t0_r6 (x : Fin 7 → ℝ³) (b : ℝ) : ℝ :=
  (oblX6 x 3 * (oblX2 x 5 - 1) - oblX6 x 5 * (oblX2 x 3 - 1)) + t0_d6 x * b

noncomputable def t0_gamma8 (x : Fin 7 → ℝ³) (b : ℝ) : ℝ :=
  ((oblX2 x 4 * (oblX6 x 3 - 1) - oblX2 x 3 * (oblX6 x 4 - 1)) +
    (oblX0 x 4 * (oblX6 x 3 - 1) - oblX0 x 3 * (oblX6 x 4 - 1)) * b) / t0_d8 x

noncomputable def gamma_T0_lo (x : Fin 7 → ℝ³) (b : ℝ) : ℝ :=
  max (max 0 ((b - 1) / omega5 x))
    (max (if t0_nC x < 0 then (t0_Delta_bc x - t0_nB x * b) / t0_nC x else 0)
      (if t0_s6 x < 0 then t0_r6 x b / t0_s6 x else 0))

noncomputable def gamma_T0_hi (x : Fin 7 → ℝ³) (b : ℝ) : ℝ :=
  min (1 + omega4 x * b)
    (min (if 0 < t0_nC x then (t0_Delta_bc x - t0_nB x * b) / t0_nC x else 1 + omega4 x * b)
      (if 0 < t0_s6 x then t0_r6 x b / t0_s6 x else 1 + omega4 x * b))

noncomputable def gamma_A0_lo (x : Fin 7 → ℝ³) (b : ℝ) : ℝ := gamma_T0_lo x b
noncomputable def gamma_A0_hi (x : Fin 7 → ℝ³) (b : ℝ) : ℝ := min (gamma_T0_hi x b) (t0_gamma8 x b)
noncomputable def gamma_B0_lo (x : Fin 7 → ℝ³) (b : ℝ) : ℝ := max (gamma_T0_lo x b) (t0_gamma8 x b)
noncomputable def gamma_B0_hi (x : Fin 7 → ℝ³) (b : ℝ) : ℝ := gamma_T0_hi x b

theorem t0_d6_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : 0 < t0_d6 x := by
  have T := type24OfFac F
  have e3 := fac_eval F 6 3
  have e5 := fac_eval F 6 5
  rw [F.zero 6 3 (by decide), F.zero 6 2 (by decide)] at e3
  rw [F.zero 6 5 (by decide), F.zero 6 2 (by decide)] at e5
  have hf1 : F.f 6 (x 1) < 0 := F.neg 6 1 (by decide)
  have hf6 : F.f 6 (x 6) < 0 := F.neg 6 6 (by decide)
  have hlt5 : F.f 7 (x 5) < 0 := F.neg 7 5 (by decide)
  have e75 := fac_eval F 7 5
  rw [F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at e75
  have e73 := fac_eval F 7 3
  rw [F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at e73
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have h7f1 : F.f 7 (x 1) < 0 := F.neg 7 1 (by decide)
  have hcomb : oblX0 x 3 * F.f 7 (x 5) =
      -(oblX0 x 5 * (oblX2 x 3 + oblX6 x 3 - 1) - oblX0 x 3 * (oblX2 x 5 + oblX6 x 5 - 1)) *
        (-F.f 7 (x 1)) := by
    linear_combination oblX0 x 3 * e75 - oblX0 x 5 * e73
  have hpos_num : 0 < oblX0 x 5 * (oblX2 x 3 + oblX6 x 3 - 1) -
      oblX0 x 3 * (oblX2 x 5 + oblX6 x 5 - 1) := by
    have hmul : oblX0 x 3 * F.f 7 (x 5) < 0 := mul_neg_of_pos_of_neg ha3 hlt5
    have hneg : 0 < -F.f 7 (x 1) := neg_pos.mpr h7f1
    nlinarith [hcomb]
  have hid6 : t0_d6 x * (-F.f 6 (x 6)) =
      (oblX0 x 5 * (oblX2 x 3 + oblX6 x 3 - 1) - oblX0 x 3 * (oblX2 x 5 + oblX6 x 5 - 1)) *
        (-F.f 6 (x 1)) := by
    unfold t0_d6
    linear_combination oblX0 x 5 * e3 - oblX0 x 3 * e5
  nlinarith [mul_pos hpos_num (neg_pos.mpr hf1)]

theorem t0_d8_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : 0 < t0_d8 x := by
  have T := type24OfFac F
  have e3 := fac_eval F 8 3
  have e4 := fac_eval F 8 4
  rw [F.zero 8 3 (by decide), F.zero 8 6 (by decide)] at e3
  rw [F.zero 8 4 (by decide), F.zero 8 6 (by decide)] at e4
  have hf1 : F.f 8 (x 1) < 0 := F.neg 8 1 (by decide)
  have hf0 : F.f 8 (x 0) < 0 := F.neg 8 0 (by decide)
  have hlt3 : F.f 4 (x 3) < 0 := F.neg 4 3 (by decide)
  have e43 := fac_eval F 4 3
  rw [F.zero 4 0 (by decide), F.zero 4 6 (by decide)] at e43
  have e44 := fac_eval F 4 4
  rw [F.zero 4 4 (by decide), F.zero 4 0 (by decide), F.zero 4 6 (by decide)] at e44
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have h4f1 : F.f 4 (x 1) < 0 := F.neg 4 1 (by decide)
  have hcomb : oblX2 x 4 * F.f 4 (x 3) =
      -(oblX2 x 3 * (oblX0 x 4 + oblX6 x 4 - 1) - oblX2 x 4 * (oblX0 x 3 + oblX6 x 3 - 1)) *
        (-F.f 4 (x 1)) := by
    linear_combination oblX2 x 4 * e43 - oblX2 x 3 * e44
  have hpos_num : 0 < oblX2 x 3 * (oblX0 x 4 + oblX6 x 4 - 1) -
      oblX2 x 4 * (oblX0 x 3 + oblX6 x 3 - 1) := by
    have hmul : oblX2 x 4 * F.f 4 (x 3) < 0 := mul_neg_of_pos_of_neg hb4 hlt3
    have hneg : 0 < -F.f 4 (x 1) := neg_pos.mpr h4f1
    nlinarith [hcomb]
  have hid8 : t0_d8 x * (-F.f 8 (x 0)) =
      (oblX2 x 3 * (oblX0 x 4 + oblX6 x 4 - 1) - oblX2 x 4 * (oblX0 x 3 + oblX6 x 3 - 1)) *
        (-F.f 8 (x 1)) := by
    unfold t0_d8
    linear_combination -oblX2 x 4 * e3 + oblX2 x 3 * e4
  nlinarith [mul_pos hpos_num (neg_pos.mpr hf1)]

theorem t0_Delta_bc_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : 0 < t0_Delta_bc x := by
  have T := type24OfFac F
  have e4 := fac_eval F 3 4
  have e5 := fac_eval F 3 5
  rw [F.zero 3 4 (by decide), F.zero 3 0 (by decide)] at e4
  rw [F.zero 3 5 (by decide), F.zero 3 0 (by decide)] at e5
  have hf1 : F.f 3 (x 1) < 0 := F.neg 3 1 (by decide)
  have hf2 : F.f 3 (x 2) < 0 := F.neg 3 2 (by decide)
  have hlt4 : F.f 2 (x 4) < 0 := F.neg 2 4 (by decide)
  have e24 := fac_eval F 2 4
  rw [F.zero 2 0 (by decide), F.zero 2 2 (by decide)] at e24
  have e25 := fac_eval F 2 5
  rw [F.zero 2 5 (by decide), F.zero 2 0 (by decide), F.zero 2 2 (by decide)] at e25
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have h2f1 : F.f 2 (x 1) < 0 := F.neg 2 1 (by decide)
  have hcomb : oblX6 x 5 * F.f 2 (x 4) =
      -(oblX6 x 4 * (oblX0 x 5 + oblX2 x 5 - 1) - oblX6 x 5 * (oblX0 x 4 + oblX2 x 4 - 1)) *
        (-F.f 2 (x 1)) := by
    linear_combination oblX6 x 5 * e24 - oblX6 x 4 * e25
  have hpos_num : 0 < oblX6 x 4 * (oblX0 x 5 + oblX2 x 5 - 1) -
      oblX6 x 5 * (oblX0 x 4 + oblX2 x 4 - 1) := by
    have hmul : oblX6 x 5 * F.f 2 (x 4) < 0 := mul_neg_of_pos_of_neg hc5 hlt4
    have hneg : 0 < -F.f 2 (x 1) := neg_pos.mpr h2f1
    nlinarith [hcomb]
  have hidbc : t0_Delta_bc x * (-F.f 3 (x 2)) =
      (oblX6 x 4 * (oblX0 x 5 + oblX2 x 5 - 1) - oblX6 x 5 * (oblX0 x 4 + oblX2 x 4 - 1)) *
        (-F.f 3 (x 1)) := by
    unfold t0_Delta_bc
    linear_combination oblX6 x 4 * e5 - oblX6 x 5 * e4
  nlinarith [mul_pos hpos_num (neg_pos.mpr hf1), neg_pos.mpr hf2]

private theorem uT0_active_facets_iff {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    {b gamma : ℝ} (_hb : 0 < b) (hgamma : 0 < gamma) :
    (⟪F.N 2, uT0 x b gamma⟫ < 0 ∧ ⟪F.N 3, uT0 x b gamma⟫ < 0 ∧
      ⟪F.N 4, uT0 x b gamma⟫ < 0 ∧ 0 < ⟪F.N 6, uT0 x b gamma⟫) ↔
    (gamma_T0_lo x b < gamma ∧ gamma < gamma_T0_hi x b ∧
      (t0_nC x = 0 → 0 < t0_Delta_bc x - t0_nB x * b) ∧
      (t0_s6 x = 0 → 0 < t0_r6 x b)) := by
  have T := type24OfFac F
  have h2_iff : ⟪F.N 2, uT0 x b gamma⟫ < 0 ↔ (b - 1) / omega5 x < gamma := by
    have e5 := fac_eval F 2 5
    rw [F.zero 2 5 (by decide), F.zero 2 0 (by decide), F.zero 2 2 (by decide)] at e5
    have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
    have h5eq := eq5 F
    have hf61 : F.f 2 (x 6) - F.f 2 (x 1) = omega5 x * F.f 2 (x 1) := by
      have hmul : oblX6 x 5 * (F.f 2 (x 6) - F.f 2 (x 1)) =
          oblX6 x 5 * (omega5 x * F.f 2 (x 1)) := by
        linear_combination -e5 + F.f 2 (x 1) * h5eq
      exact mul_left_cancel₀ hc5.ne' hmul
    have hf1 : F.f 2 (x 1) < 0 := F.neg 2 1 (by decide)
    have hw5 : 0 < omega5 x := hC.2.2.1
    rw [uT0, inner_cap, F.zero 2 0 (by decide), F.zero 2 2 (by decide), hf61]
    have heval : -1 * (0 - F.f 2 (x 1)) + b * (0 - F.f 2 (x 1)) +
        gamma * (omega5 x * F.f 2 (x 1)) = (1 - b + omega5 x * gamma) * F.f 2 (x 1) := by ring
    rw [heval, mul_neg_iff]
    constructor
    · intro h
      rcases h with ⟨hpos, _⟩ | ⟨hneg, hf1p⟩
      · exact (div_lt_iff₀ hw5).mpr (by linarith)
      · exact absurd hf1 (not_lt.mpr hf1p.le)
    · intro hg
      left
      have := (div_lt_iff₀ hw5).mp hg
      exact ⟨by linarith, hf1⟩
  have h4_iff : ⟪F.N 4, uT0 x b gamma⟫ < 0 ↔ gamma < 1 + omega4 x * b := by
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
    rw [uT0, inner_cap, F.zero 4 0 (by decide), F.zero 4 6 (by decide), hf21]
    have heval : -1 * (0 - F.f 4 (x 1)) + b * (omega4 x * F.f 4 (x 1)) +
        gamma * (0 - F.f 4 (x 1)) = (1 + omega4 x * b - gamma) * F.f 4 (x 1) := by ring
    rw [heval, mul_neg_iff]
    constructor
    · intro h
      rcases h with ⟨hpos, _⟩ | ⟨_, hf1p⟩
      · linarith
      · exact absurd hf1 (not_lt.mpr hf1p.le)
    · intro hg
      exact Or.inl ⟨by linarith, hf1⟩
  have h3_iff : ⟪F.N 3, uT0 x b gamma⟫ < 0 ↔ 0 < t0_Delta_bc x - t0_nB x * b - t0_nC x * gamma := by
    have e4 := fac_eval F 3 4
    have e5 := fac_eval F 3 5
    rw [F.zero 3 4 (by decide), F.zero 3 0 (by decide)] at e4
    rw [F.zero 3 5 (by decide), F.zero 3 0 (by decide)] at e5
    have hf1 : F.f 3 (x 1) < 0 := F.neg 3 1 (by decide)
    have hDbc : 0 < t0_Delta_bc x := t0_Delta_bc_pos F
    have hmul : t0_Delta_bc x * ⟪F.N 3, uT0 x b gamma⟫ =
        (t0_Delta_bc x - t0_nB x * b - t0_nC x * gamma) * F.f 3 (x 1) := by
      rw [uT0, inner_cap, F.zero 3 0 (by decide)]
      unfold t0_Delta_bc t0_nB t0_nC
      linear_combination (b * oblX6 x 5 - gamma * oblX2 x 5) * e4 +
        (-b * oblX6 x 4 + gamma * oblX2 x 4) * e5
    constructor
    · intro h3n
      have hneg : (t0_Delta_bc x - t0_nB x * b - t0_nC x * gamma) * F.f 3 (x 1) < 0 := by
        rw [← hmul]; exact mul_neg_of_pos_of_neg hDbc h3n
      nlinarith
    · intro hpos
      have hneg : t0_Delta_bc x * ⟪F.N 3, uT0 x b gamma⟫ < 0 := by
        rw [hmul]; exact mul_neg_of_pos_of_neg hpos hf1
      nlinarith
  have h6_iff : 0 < ⟪F.N 6, uT0 x b gamma⟫ ↔ 0 < t0_r6 x b - t0_s6 x * gamma := by
    have e3 := fac_eval F 6 3
    have e5 := fac_eval F 6 5
    rw [F.zero 6 3 (by decide), F.zero 6 2 (by decide)] at e3
    rw [F.zero 6 5 (by decide), F.zero 6 2 (by decide)] at e5
    have hf1 : F.f 6 (x 1) < 0 := F.neg 6 1 (by decide)
    have hd6 : 0 < t0_d6 x := t0_d6_pos F
    have hmul : t0_d6 x * ⟪F.N 6, uT0 x b gamma⟫ =
        (t0_r6 x b - t0_s6 x * gamma) * (-F.f 6 (x 1)) := by
      rw [uT0, inner_cap, F.zero 6 2 (by decide)]
      unfold t0_r6 t0_s6 t0_d6
      linear_combination -(oblX6 x 5 + gamma * oblX0 x 5) * e3 -
        (-oblX6 x 3 - gamma * oblX0 x 3) * e5
    constructor
    · intro h6p
      have hpos : 0 < (t0_r6 x b - t0_s6 x * gamma) * (-F.f 6 (x 1)) := by
        rw [← hmul]; exact mul_pos hd6 h6p
      nlinarith
    · intro hpos
      have hpos' : 0 < t0_d6 x * ⟪F.N 6, uT0 x b gamma⟫ := by
        rw [hmul]; exact mul_pos hpos (neg_pos.mpr hf1)
      nlinarith
  rw [h2_iff, h3_iff, h4_iff, h6_iff]
  unfold gamma_T0_lo gamma_T0_hi
  simp only [lt_min_iff, max_lt_iff]
  constructor
  · rintro ⟨hg5, h3p, hg4, h6p⟩
    refine ⟨⟨⟨hgamma, hg5⟩, ?_, ?_⟩, ⟨hg4, ?_, ?_⟩, ?_, ?_⟩
    · split_ifs with hnC
      · exact (div_lt_iff_of_neg hnC).mpr (by linarith)
      · exact hgamma
    · split_ifs with hs6
      · exact (div_lt_iff_of_neg hs6).mpr (by linarith)
      · exact hgamma
    · split_ifs with hnC
      · exact (lt_div_iff₀ hnC).mpr (by linarith)
      · exact hg4
    · split_ifs with hs6
      · exact (lt_div_iff₀ hs6).mpr (by linarith)
      · exact hg4
    · intro hnC0; rw [hnC0, zero_mul, sub_zero] at h3p; exact h3p
    · intro hs60; rw [hs60, zero_mul, sub_zero] at h6p; exact h6p
  · rintro ⟨⟨⟨_, hg5⟩, h3lo, h6lo⟩, ⟨hg4, h3hi, h6hi⟩, hnC0, hs60⟩
    refine ⟨hg5, ?_, hg4, ?_⟩
    · rcases lt_trichotomy (t0_nC x) 0 with hn | hz | hp
      · simp only [hn, ↓reduceIte] at h3lo
        have := (div_lt_iff_of_neg hn).mp h3lo; linarith
      · have hpos := hnC0 hz; rw [hz, zero_mul, sub_zero]; exact hpos
      · simp only [hp, ↓reduceIte] at h3hi
        have := (lt_div_iff₀ hp).mp h3hi; linarith
    · rcases lt_trichotomy (t0_s6 x) 0 with hn | hz | hp
      · simp only [hn, ↓reduceIte] at h6lo
        have := (div_lt_iff_of_neg hn).mp h6lo; linarith
      · have hpos := hs60 hz; rw [hz, zero_mul, sub_zero]; exact hpos
      · simp only [hp, ↓reduceIte] at h6hi
        have := (lt_div_iff₀ hp).mp h6hi; linarith

private theorem uT0_facet8_lt_iff {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (b gamma : ℝ) :
    ⟪F.N 8, uT0 x b gamma⟫ < 0 ↔ gamma < t0_gamma8 x b := by
  have e3 := fac_eval F 8 3
  have e4 := fac_eval F 8 4
  rw [F.zero 8 3 (by decide), F.zero 8 6 (by decide)] at e3
  rw [F.zero 8 4 (by decide), F.zero 8 6 (by decide)] at e4
  have hf1 : F.f 8 (x 1) < 0 := F.neg 8 1 (by decide)
  have hd8 : 0 < t0_d8 x := t0_d8_pos F
  have hmul : t0_d8 x * ⟪F.N 8, uT0 x b gamma⟫ =
      (t0_d8 x * gamma - ((oblX2 x 4 * (oblX6 x 3 - 1) - oblX2 x 3 * (oblX6 x 4 - 1)) +
        (oblX0 x 4 * (oblX6 x 3 - 1) - oblX0 x 3 * (oblX6 x 4 - 1)) * b)) * (-F.f 8 (x 1)) := by
    rw [uT0, inner_cap, F.zero 8 6 (by decide)]
    unfold t0_d8
    linear_combination -(oblX2 x 4 + b * oblX0 x 4) * e3 -
      (-oblX2 x 3 - b * oblX0 x 3) * e4
  unfold t0_gamma8
  rw [lt_div_iff₀ hd8]
  constructor
  · intro h8n
    have hneg : t0_d8 x * ⟪F.N 8, uT0 x b gamma⟫ < 0 := mul_neg_of_pos_of_neg hd8 h8n
    rw [hmul] at hneg
    nlinarith
  · intro hlt
    have hneg : t0_d8 x * ⟪F.N 8, uT0 x b gamma⟫ < 0 := by
      rw [hmul]; exact mul_neg_of_neg_of_pos (by linarith) (neg_pos.mpr hf1)
    nlinarith

private theorem uT0_facet8_pos_iff {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (b gamma : ℝ) :
    0 < ⟪F.N 8, uT0 x b gamma⟫ ↔ t0_gamma8 x b < gamma := by
  have e3 := fac_eval F 8 3
  have e4 := fac_eval F 8 4
  rw [F.zero 8 3 (by decide), F.zero 8 6 (by decide)] at e3
  rw [F.zero 8 4 (by decide), F.zero 8 6 (by decide)] at e4
  have hf1 : F.f 8 (x 1) < 0 := F.neg 8 1 (by decide)
  have hd8 : 0 < t0_d8 x := t0_d8_pos F
  have hmul : t0_d8 x * ⟪F.N 8, uT0 x b gamma⟫ =
      (t0_d8 x * gamma - ((oblX2 x 4 * (oblX6 x 3 - 1) - oblX2 x 3 * (oblX6 x 4 - 1)) +
        (oblX0 x 4 * (oblX6 x 3 - 1) - oblX0 x 3 * (oblX6 x 4 - 1)) * b)) * (-F.f 8 (x 1)) := by
    rw [uT0, inner_cap, F.zero 8 6 (by decide)]
    unfold t0_d8
    linear_combination -(oblX2 x 4 + b * oblX0 x 4) * e3 -
      (-oblX2 x 3 - b * oblX0 x 3) * e4
  unfold t0_gamma8
  rw [div_lt_iff₀ hd8]
  constructor
  · intro h8p
    have hpos : 0 < t0_d8 x * ⟪F.N 8, uT0 x b gamma⟫ := mul_pos hd8 h8p
    rw [hmul] at hpos
    nlinarith
  · intro hgt
    have hpos : 0 < t0_d8 x * ⟪F.N 8, uT0 x b gamma⟫ := by
      rw [hmul]; exact mul_pos (by linarith) (neg_pos.mpr hf1)
    nlinarith

/-- **FT1 (`iff CellAt` for `U_A0, D_A0`):** under `CbarIn x`, `b > 0`, `γ > 0`,
`CellAt F U_A0 D_A0 (uT0 x b γ)` holds iff `γ ∈ (gamma_A0_lo x b, gamma_A0_hi x b)`
and the `= 0` side guards hold. -/
theorem cA0_cellAt_iff {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    {b gamma : ℝ} (hb : 0 < b) (hgamma : 0 < gamma) :
    CellAt F U_A0 D_A0 (uT0 x b gamma) ↔
      gamma_A0_lo x b < gamma ∧ gamma < gamma_A0_hi x b ∧
      (t0_nC x = 0 → 0 < t0_Delta_bc x - t0_nB x * b) ∧
      (t0_s6 x = 0 → 0 < t0_r6 x b) := by
  have ⟨h5, h7, h0, h1⟩ := uT0_four_facets F hC hb hgamma
  have hact := uT0_active_facets_iff F hC hb hgamma
  have h8 := uT0_facet8_lt_iff F b gamma
  unfold gamma_A0_lo gamma_A0_hi
  rw [lt_min_iff]
  constructor
  · intro ⟨hup, hdn⟩
    have h2346 : ⟪F.N 2, uT0 x b gamma⟫ < 0 ∧ ⟪F.N 3, uT0 x b gamma⟫ < 0 ∧
        ⟪F.N 4, uT0 x b gamma⟫ < 0 ∧ 0 < ⟪F.N 6, uT0 x b gamma⟫ :=
      ⟨hdn 2 (by decide), hdn 3 (by decide), hdn 4 (by decide), hup 6 (by decide)⟩
    obtain ⟨hlo, hhi, hnC, hs6⟩ := hact.mp h2346
    exact ⟨hlo, ⟨hhi, h8.mp (hdn 8 (by decide))⟩, hnC, hs6⟩
  · rintro ⟨hlo, ⟨hhi, hg8⟩, hnC, hs6⟩
    obtain ⟨h2, h3, h4, h6⟩ := hact.mpr ⟨hlo, hhi, hnC, hs6⟩
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · fin_cases t <;> simp [U_A0] at ht
      · exact h5
      · exact h6
      · exact h7
    · fin_cases t <;> simp [D_A0] at ht
      · exact h0
      · exact h1
      · exact h2
      · exact h3
      · exact h4
      · exact h8.mpr hg8

/-- **FT1 (`iff CellAt` for `U_B0, D_B0`):** under `CbarIn x`, `b > 0`, `γ > 0`,
`CellAt F U_B0 D_B0 (uT0 x b γ)` holds iff `γ ∈ (gamma_B0_lo x b, gamma_B0_hi x b)`
and the `= 0` side guards hold. -/
theorem cB0_cellAt_iff {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    {b gamma : ℝ} (hb : 0 < b) (hgamma : 0 < gamma) :
    CellAt F U_B0 D_B0 (uT0 x b gamma) ↔
      gamma_B0_lo x b < gamma ∧ gamma < gamma_B0_hi x b ∧
      (t0_nC x = 0 → 0 < t0_Delta_bc x - t0_nB x * b) ∧
      (t0_s6 x = 0 → 0 < t0_r6 x b) := by
  have ⟨h5, h7, h0, h1⟩ := uT0_four_facets F hC hb hgamma
  have hact := uT0_active_facets_iff F hC hb hgamma
  have h8 := uT0_facet8_pos_iff F b gamma
  unfold gamma_B0_lo gamma_B0_hi
  rw [max_lt_iff]
  constructor
  · intro ⟨hup, hdn⟩
    have h2346 : ⟪F.N 2, uT0 x b gamma⟫ < 0 ∧ ⟪F.N 3, uT0 x b gamma⟫ < 0 ∧
        ⟪F.N 4, uT0 x b gamma⟫ < 0 ∧ 0 < ⟪F.N 6, uT0 x b gamma⟫ :=
      ⟨hdn 2 (by decide), hdn 3 (by decide), hdn 4 (by decide), hup 6 (by decide)⟩
    obtain ⟨hlo, hhi, hnC, hs6⟩ := hact.mp h2346
    exact ⟨⟨hlo, h8.mp (hup 8 (by decide))⟩, hhi, hnC, hs6⟩
  · rintro ⟨⟨hlo, hg8⟩, hhi, hnC, hs6⟩
    obtain ⟨h2, h3, h4, h6⟩ := hact.mpr ⟨hlo, hhi, hnC, hs6⟩
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · fin_cases t <;> simp [U_B0] at ht
      · exact h5
      · exact h6
      · exact h7
      · exact h8.mpr hg8
    · fin_cases t <;> simp [D_B0] at ht
      · exact h0
      · exact h1
      · exact h2
      · exact h3
      · exact h4

/-! ## Automatic `HiddenInTriangles` and interior `cA0 / cB0` leaves -/

/-- **FT1 (`cA` automatic hiding):** on any `CellAt F U_A0 D_A0 w`, both `0` (via
`hidden_zero_of_T0`) and `4` (via `hidden_of_three_facets` on `{3, 8, 4}`) satisfy
`Split.HiddenInTriangles x w cA`. -/
theorem hidden_in_cA_of_cell {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {w : ℝ³}
    (hcell : CellAt F U_A0 D_A0 w) :
    Split.HiddenInTriangles x w cA := by
  intro m hm
  have hm04 : m = 0 ∨ m = 4 := by
    fin_cases m
    · exact Or.inl rfl
    · exact absurd rfl (hm 0)
    · exact absurd rfl (hm 1)
    · exact absurd rfl (hm 3)
    · exact Or.inr rfl
    · exact absurd rfl (hm 2)
    · exact absurd rfl (hm 4)
  rcases hm04 with rfl | rfl
  · obtain ⟨p, q, r, hp, hq, hr, d1, d2, d3, d4⟩ :=
      hidden_zero_of_T0 F (fun t ht => hcell.2 t (by fin_cases t <;> simp [D_A0] at ht ⊢))
    have hsub : ∀ y ∈ univ.image (x ∘ (0 : Fin 7).succAbove), y ∈ univ.image x := by
      intro y hy
      rcases mem_image.mp hy with ⟨i, _, rfl⟩
      exact mem_image_of_mem x (mem_univ _)
    exact ⟨p, hsub p hp, q, hsub q hq, r, hsub r hr, d1, d2, d3, d4⟩
  · obtain ⟨p, hp, q, hq, r, hr, d1, d2, d3, d4⟩ :=
      hidden_of_three_facets F 4 0 3 6 3 8 4
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (hcell.2 3 (by decide)) (hcell.2 8 (by decide)) (hcell.2 4 (by decide))
    have hsub : ∀ y ∈ ({x 0, x 3, x 6} : Finset ℝ³), y ∈ univ.image x := fun y hy => by
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl | rfl <;> exact mem_image_of_mem x (mem_univ _)
    exact ⟨p, hsub p hp, q, hsub q hq, r, hsub r hr, d1, d2, d3, d4⟩

/-- **FT1 (`cB` automatic hiding):** on any `CellAt F U_B0 D_B0 w`, vertex `0` (via
`hidden_zero_of_T0`) satisfies `Split.HiddenInTriangles x w cB`. -/
theorem hidden_in_cB_of_cell {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {w : ℝ³}
    (hcell : CellAt F U_B0 D_B0 w) :
    Split.HiddenInTriangles x w cB := by
  intro m hm
  have hm0 : m = 0 := by
    fin_cases m
    · rfl
    · exact absurd rfl (hm 0)
    · exact absurd rfl (hm 1)
    · exact absurd rfl (hm 3)
    · exact absurd rfl (hm 4)
    · exact absurd rfl (hm 2)
    · exact absurd rfl (hm 5)
  subst hm0
  obtain ⟨p, q, r, hp, hq, hr, d1, d2, d3, d4⟩ :=
    hidden_zero_of_T0 F (fun t ht => hcell.2 t (by fin_cases t <;> simp [D_B0] at ht ⊢))
  have hsub : ∀ y ∈ univ.image (x ∘ (0 : Fin 7).succAbove), y ∈ univ.image x := by
    intro y hy
    rcases mem_image.mp hy with ⟨i, _, rfl⟩
    exact mem_image_of_mem x (mem_univ _)
  exact ⟨p, hsub p hp, q, hsub q hq, r, hsub r hr, d1, d2, d3, d4⟩

/-- **FT1 (`cA0` interior leaf):** strict line separation at an interior view `uT0 x b γ` of
`(U_A0, D_A0)` on any edge `a : ZMod 5` yields `Gen.EdgePlaneAny x` (zero `hhid4` needed). -/
theorem cA0_edgePlaneAny {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    {b gamma : ℝ} (hb : 0 < b) (hgamma : 0 < gamma)
    (hcell_win : gamma_A0_lo x b < gamma ∧ gamma < gamma_A0_hi x b ∧
      (t0_nC x = 0 → 0 < t0_Delta_bc x - t0_nB x * b) ∧ (t0_s6 x = 0 → 0 < t0_r6 x b))
    (a : ZMod 5)
    (hD0 : ⟪x (cA (a + 1)) - x (cA a), uT0 x b gamma⟫ ≠ 0)
    (hc_ne0 : ∀ i : ZMod 5, i ≠ a →
      Split.det3 (x (cA (i + 1)) - x (cA i)) (x (cA (a + 1)) - x (cA a)) (uT0 x b gamma) ≠ 0)
    (sh : ℝ) (hsh : sh = 1 ∨ sh = -1) (α' μ' : ℝ)
    (hBlue0 : ∀ i j : ZMod 5, i ≠ a → (j = i ∨ j = i + 1) →
      0 < Split.det3 (x (cA (i + 1)) - x (cA i)) (x (cA (a + 1)) - x (cA a)) (uT0 x b gamma) →
      (-sh * ⟪Split.Slope.linSpinVec (fun t => x (cA t)) a i j, uT0 x b gamma⟫ /
          Split.det3 (x (cA (i + 1)) - x (cA i)) (x (cA (a + 1)) - x (cA a)) (uT0 x b gamma)) -
        μ' * ⟪x (cA j) - x (cA a), uT0 x b gamma⟫ < α')
    (hOrange0 : ∀ p q : ZMod 5, p ≠ a → (q = p ∨ q = p + 1) →
      Split.det3 (x (cA (p + 1)) - x (cA p)) (x (cA (a + 1)) - x (cA a)) (uT0 x b gamma) < 0 →
      α' < (-sh * ⟪Split.Slope.linSpinVec (fun t => x (cA t)) a p q, uT0 x b gamma⟫ /
          Split.det3 (x (cA (p + 1)) - x (cA p)) (x (cA (a + 1)) - x (cA a)) (uT0 x b gamma)) -
        μ' * ⟪x (cA q) - x (cA a), uT0 x b gamma⟫) :
    Gen.EdgePlaneAny x := by
  have hcell : CellAt F U_A0 D_A0 (uT0 x b gamma) :=
    (cA0_cellAt_iff F hC hb hgamma).mpr hcell_win
  exact cell_lineSep_edgePlaneAny F (by norm_num) cA cA_inj cA_cycUD hcell
    (hidden_in_cA_of_cell F hcell) a hD0 hc_ne0 sh hsh α' μ' hBlue0 hOrange0

/-- **FT1 (`cB0` interior leaf):** strict line separation at an interior view `uT0 x b γ` of
`(U_B0, D_B0)` on any edge `a : ZMod 6` yields `Gen.EdgePlaneAny x`. -/
theorem cB0_edgePlaneAny {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    {b gamma : ℝ} (hb : 0 < b) (hgamma : 0 < gamma)
    (hcell_win : gamma_B0_lo x b < gamma ∧ gamma < gamma_B0_hi x b ∧
      (t0_nC x = 0 → 0 < t0_Delta_bc x - t0_nB x * b) ∧ (t0_s6 x = 0 → 0 < t0_r6 x b))
    (a : ZMod 6)
    (hD0 : ⟪x (cB (a + 1)) - x (cB a), uT0 x b gamma⟫ ≠ 0)
    (hc_ne0 : ∀ i : ZMod 6, i ≠ a →
      Split.det3 (x (cB (i + 1)) - x (cB i)) (x (cB (a + 1)) - x (cB a)) (uT0 x b gamma) ≠ 0)
    (sh : ℝ) (hsh : sh = 1 ∨ sh = -1) (α' μ' : ℝ)
    (hBlue0 : ∀ i j : ZMod 6, i ≠ a → (j = i ∨ j = i + 1) →
      0 < Split.det3 (x (cB (i + 1)) - x (cB i)) (x (cB (a + 1)) - x (cB a)) (uT0 x b gamma) →
      (-sh * ⟪Split.Slope.linSpinVec (fun t => x (cB t)) a i j, uT0 x b gamma⟫ /
          Split.det3 (x (cB (i + 1)) - x (cB i)) (x (cB (a + 1)) - x (cB a)) (uT0 x b gamma)) -
        μ' * ⟪x (cB j) - x (cB a), uT0 x b gamma⟫ < α')
    (hOrange0 : ∀ p q : ZMod 6, p ≠ a → (q = p ∨ q = p + 1) →
      Split.det3 (x (cB (p + 1)) - x (cB p)) (x (cB (a + 1)) - x (cB a)) (uT0 x b gamma) < 0 →
      α' < (-sh * ⟪Split.Slope.linSpinVec (fun t => x (cB t)) a p q, uT0 x b gamma⟫ /
          Split.det3 (x (cB (p + 1)) - x (cB p)) (x (cB (a + 1)) - x (cB a)) (uT0 x b gamma)) -
        μ' * ⟪x (cB q) - x (cB a), uT0 x b gamma⟫) :
    Gen.EdgePlaneAny x := by
  have hcell : CellAt F U_B0 D_B0 (uT0 x b gamma) :=
    (cB0_cellAt_iff F hC hb hgamma).mpr hcell_win
  exact cell_lineSep_edgePlaneAny F (by norm_num) cB cB_inj cB_cycUD hcell
    (hidden_in_cB_of_cell F hcell) a hD0 hc_ne0 sh hsh α' μ' hBlue0 hOrange0

/-- `CA0CertAt x F b γ`: interior `(U_A0, D_A0)` cell conditions and strict line separation at
`uT0 x b γ` on some edge `a : ZMod 5` of `cA = ![1, 2, 5, 3, 6]`. -/
def CA0CertAt (x : Fin 7 → ℝ³) (_F : S0xFac 9 s0x_S24 x) (b gamma : ℝ) : Prop :=
  0 < b ∧ 0 < gamma ∧
  gamma_A0_lo x b < gamma ∧ gamma < gamma_A0_hi x b ∧
  (t0_nC x = 0 → 0 < t0_Delta_bc x - t0_nB x * b) ∧ (t0_s6 x = 0 → 0 < t0_r6 x b) ∧
  ∃ a : ZMod 5,
    ⟪x (cA (a + 1)) - x (cA a), uT0 x b gamma⟫ ≠ 0 ∧
    (∀ i : ZMod 5, i ≠ a →
      Split.det3 (x (cA (i + 1)) - x (cA i)) (x (cA (a + 1)) - x (cA a)) (uT0 x b gamma) ≠ 0) ∧
    ∃ sh α' μ' : ℝ, (sh = 1 ∨ sh = -1) ∧
      (∀ i j : ZMod 5, i ≠ a → (j = i ∨ j = i + 1) →
        0 < Split.det3 (x (cA (i + 1)) - x (cA i)) (x (cA (a + 1)) - x (cA a)) (uT0 x b gamma) →
        (-sh * ⟪Split.Slope.linSpinVec (fun t => x (cA t)) a i j, uT0 x b gamma⟫ /
            Split.det3 (x (cA (i + 1)) - x (cA i)) (x (cA (a + 1)) - x (cA a)) (uT0 x b gamma)) -
          μ' * ⟪x (cA j) - x (cA a), uT0 x b gamma⟫ < α') ∧
      (∀ p q : ZMod 5, p ≠ a → (q = p ∨ q = p + 1) →
        Split.det3 (x (cA (p + 1)) - x (cA p)) (x (cA (a + 1)) - x (cA a)) (uT0 x b gamma) < 0 →
        α' < (-sh * ⟪Split.Slope.linSpinVec (fun t => x (cA t)) a p q, uT0 x b gamma⟫ /
            Split.det3 (x (cA (p + 1)) - x (cA p)) (x (cA (a + 1)) - x (cA a)) (uT0 x b gamma)) -
          μ' * ⟪x (cA q) - x (cA a), uT0 x b gamma⟫)

/-- `CB0CertAt x F b γ`: interior `(U_B0, D_B0)` cell conditions and strict line separation at
`uT0 x b γ` on some edge `a : ZMod 6` of `cB = ![1, 2, 5, 3, 4, 6]`. -/
def CB0CertAt (x : Fin 7 → ℝ³) (_F : S0xFac 9 s0x_S24 x) (b gamma : ℝ) : Prop :=
  0 < b ∧ 0 < gamma ∧
  gamma_B0_lo x b < gamma ∧ gamma < gamma_B0_hi x b ∧
  (t0_nC x = 0 → 0 < t0_Delta_bc x - t0_nB x * b) ∧ (t0_s6 x = 0 → 0 < t0_r6 x b) ∧
  ∃ a : ZMod 6,
    ⟪x (cB (a + 1)) - x (cB a), uT0 x b gamma⟫ ≠ 0 ∧
    (∀ i : ZMod 6, i ≠ a →
      Split.det3 (x (cB (i + 1)) - x (cB i)) (x (cB (a + 1)) - x (cB a)) (uT0 x b gamma) ≠ 0) ∧
    ∃ sh α' μ' : ℝ, (sh = 1 ∨ sh = -1) ∧
      (∀ i j : ZMod 6, i ≠ a → (j = i ∨ j = i + 1) →
        0 < Split.det3 (x (cB (i + 1)) - x (cB i)) (x (cB (a + 1)) - x (cB a)) (uT0 x b gamma) →
        (-sh * ⟪Split.Slope.linSpinVec (fun t => x (cB t)) a i j, uT0 x b gamma⟫ /
            Split.det3 (x (cB (i + 1)) - x (cB i)) (x (cB (a + 1)) - x (cB a)) (uT0 x b gamma)) -
          μ' * ⟪x (cB j) - x (cB a), uT0 x b gamma⟫ < α') ∧
      (∀ p q : ZMod 6, p ≠ a → (q = p ∨ q = p + 1) →
        Split.det3 (x (cB (p + 1)) - x (cB p)) (x (cB (a + 1)) - x (cB a)) (uT0 x b gamma) < 0 →
        α' < (-sh * ⟪Split.Slope.linSpinVec (fun t => x (cB t)) a p q, uT0 x b gamma⟫ /
            Split.det3 (x (cB (p + 1)) - x (cB p)) (x (cB (a + 1)) - x (cB a)) (uT0 x b gamma)) -
          μ' * ⟪x (cB q) - x (cB a), uT0 x b gamma⟫)

theorem holeLeaf_not_cA0 {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F)
    {b gamma : ℝ} (hc : CA0CertAt x F b gamma) : False := by
  rcases hc with ⟨hb, hg, hlo, hhi, hnC, hs6, a, hD0, hc_ne0, sh, α', μ', hsh, hB, hO⟩
  exact Atlas.holeLeaf_not_edgePlaneAny hF
    (cA0_edgePlaneAny F hF.1 hb hg ⟨hlo, hhi, hnC, hs6⟩ a hD0 hc_ne0 sh hsh α' μ' hB hO)

theorem hole24_not_cA0 {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : Hole24 x F)
    {b gamma : ℝ} (hc : CA0CertAt x F b gamma) : False :=
  holeLeaf_not_cA0 hF.1 hc

theorem holeLeaf_not_cB0 {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F)
    {b gamma : ℝ} (hc : CB0CertAt x F b gamma) : False := by
  rcases hc with ⟨hb, hg, hlo, hhi, hnC, hs6, a, hD0, hc_ne0, sh, α', μ', hsh, hB, hO⟩
  exact Atlas.holeLeaf_not_edgePlaneAny hF
    (cB0_edgePlaneAny F hF.1 hb hg ⟨hlo, hhi, hnC, hs6⟩ a hD0 hc_ne0 sh hsh α' μ' hB hO)

theorem hole24_not_cB0 {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : Hole24 x F)
    {b gamma : ℝ} (hc : CB0CertAt x F b gamma) : False :=
  holeLeaf_not_cB0 hF.1 hc

/-- **FV2 (`CA0OCCertAt`):** `CA0` cell conditions plus `OrderCertAt` at `uT0 x b γ`. -/
def CA0OCCertAt (x : Fin 7 → ℝ³) (_F : S0xFac 9 s0x_S24 x) (b gamma : ℝ) : Prop :=
  0 < b ∧ 0 < gamma ∧
  gamma_A0_lo x b < gamma ∧ gamma < gamma_A0_hi x b ∧
  (t0_nC x = 0 → 0 < t0_Delta_bc x - t0_nB x * b) ∧ (t0_s6 x = 0 → 0 < t0_r6 x b) ∧
  Split.Slope.OrderCertAt (fun t => x (cA t)) (uT0 x b gamma)

/-- **FV2 (`CB0OCCertAt`):** `CB0` cell conditions plus `OrderCertAt` at `uT0 x b γ`. -/
def CB0OCCertAt (x : Fin 7 → ℝ³) (_F : S0xFac 9 s0x_S24 x) (b gamma : ℝ) : Prop :=
  0 < b ∧ 0 < gamma ∧
  gamma_B0_lo x b < gamma ∧ gamma < gamma_B0_hi x b ∧
  (t0_nC x = 0 → 0 < t0_Delta_bc x - t0_nB x * b) ∧ (t0_s6 x = 0 → 0 < t0_r6 x b) ∧
  Split.Slope.OrderCertAt (fun t => x (cB t)) (uT0 x b gamma)

theorem cA0CertAt_of_oc {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} {b gamma : ℝ}
    (hoc : CA0OCCertAt x F b gamma) : CA0CertAt x F b gamma := by
  rcases hoc with ⟨hb, hg, hlo, hhi, hnC, hs6, a, hD0, hc_ne0, sh, hsh, hOrd, hEq⟩
  obtain ⟨α', μ', hB, hO⟩ := Split.Slope.lineSep_of_depthOrder_ties
    (fun t => x (cA t)) (uT0 x b gamma) a sh hOrd hEq
  exact ⟨hb, hg, hlo, hhi, hnC, hs6, a, hD0, hc_ne0, sh, α', μ', hsh, hB, hO⟩

theorem cB0CertAt_of_oc {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} {b gamma : ℝ}
    (hoc : CB0OCCertAt x F b gamma) : CB0CertAt x F b gamma := by
  rcases hoc with ⟨hb, hg, hlo, hhi, hnC, hs6, a, hD0, hc_ne0, sh, hsh, hOrd, hEq⟩
  obtain ⟨α', μ', hB, hO⟩ := Split.Slope.lineSep_of_depthOrder_ties
    (fun t => x (cB t)) (uT0 x b gamma) a sh hOrd hEq
  exact ⟨hb, hg, hlo, hhi, hnC, hs6, a, hD0, hc_ne0, sh, α', μ', hsh, hB, hO⟩

theorem holeLeaf_not_cA0_oc {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F)
    {b gamma : ℝ} (hc : CA0OCCertAt x F b gamma) : False :=
  holeLeaf_not_cA0 hF (cA0CertAt_of_oc hc)

theorem holeLeaf_not_cB0_oc {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F)
    {b gamma : ℝ} (hc : CB0OCCertAt x F b gamma) : False :=
  holeLeaf_not_cB0 hF (cB0CertAt_of_oc hc)

theorem cA0_edgePlaneAny_twin {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    {b gamma : ℝ} (hc : CA0CertAt (x ∘ Sym.pi24) (Sym.sym24 F) b gamma) :
    Gen.EdgePlaneAny x := by
  rcases hc with ⟨hb, hg, hlo, hhi, hnC, hs6, a, hD0, hc_ne0, sh, α', μ', hsh, hB, hO⟩
  exact edgePlaneAny_of_comp_pi24 x
    (cA0_edgePlaneAny (Sym.sym24 F) ((Sym.cbarIn_comp_pi24 x).2 hC) hb hg ⟨hlo, hhi, hnC, hs6⟩
      a hD0 hc_ne0 sh hsh α' μ' hB hO)

theorem cB0_edgePlaneAny_twin {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    {b gamma : ℝ} (hc : CB0CertAt (x ∘ Sym.pi24) (Sym.sym24 F) b gamma) :
    Gen.EdgePlaneAny x := by
  rcases hc with ⟨hb, hg, hlo, hhi, hnC, hs6, a, hD0, hc_ne0, sh, α', μ', hsh, hB, hO⟩
  exact edgePlaneAny_of_comp_pi24 x
    (cB0_edgePlaneAny (Sym.sym24 F) ((Sym.cbarIn_comp_pi24 x).2 hC) hb hg ⟨hlo, hhi, hnC, hs6⟩
      a hD0 hc_ne0 sh hsh α' μ' hB hO)

theorem holeLeaf_not_cA0_twin {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F)
    {b gamma : ℝ} (hc : CA0CertAt (x ∘ Sym.pi24) (Sym.sym24 F) b gamma) : False :=
  Atlas.holeLeaf_not_edgePlaneAny hF (cA0_edgePlaneAny_twin F hF.1 hc)

theorem hole24_not_cA0_twin {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : Hole24 x F)
    {b gamma : ℝ} (hc : CA0CertAt (x ∘ Sym.pi24) (Sym.sym24 F) b gamma) : False :=
  holeLeaf_not_cA0_twin hF.1 hc

theorem holeLeaf_not_cB0_twin {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F)
    {b gamma : ℝ} (hc : CB0CertAt (x ∘ Sym.pi24) (Sym.sym24 F) b gamma) : False :=
  Atlas.holeLeaf_not_edgePlaneAny hF (cB0_edgePlaneAny_twin F hF.1 hc)

theorem hole24_not_cB0_twin {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : Hole24 x F)
    {b gamma : ℝ} (hc : CB0CertAt (x ∘ Sym.pi24) (Sym.sym24 F) b gamma) : False :=
  holeLeaf_not_cB0_twin hF.1 hc

end Minimality.T24.TwoCone
