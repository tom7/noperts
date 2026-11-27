module

public import Minimality.Type24T2Cone

/-!
# Lemma AH and the corner region `AH3Region` for the type-24 cone `T_2` (`cA2`)

Same skeleton as Lemma Z / `Z1Region` (`Type24T2Cone.lean`), one more input letter:

* `cA2_robUni_of_ah`: every open `cA2` view `uT2 x β γ` with `z₀ < z₅` and `z₀ < z₃`
  (`z_v = ⟪x v, ·⟫`) has `RobUni` depths on `cA2 = ![0, 5, 3, 6, 1]` under `OB1 x`
  (the ten crowns are excluded by the two comparisons, `uT2_depth_signs` and `cA2_not_back_03_56`).
* `AH3Region`: at the edge view `x₃ - x₂` (a vertex of the closed `cA2` cell iff `b₃ < 1`, i.e.
  `F.f 1 (x 2) < F.f 1 (x 3)`), the two letters are strict; a view just inside the cell exists
  (`cA2_exists_of_ah3Region`), hence `Gen.LexAny F` (`lexAny_of_ah3Region`, `π_24` twin, hole facts).
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

/-- **Lemma AH:** under `OB1 x`, every open-cell view `uT2 x β γ` of `cA2` with `z₀ < z₅` and
`z₀ < z₃` has `RobUni` depths on `cA2 = ![0, 5, 3, 6, 1]`. -/
theorem cA2_robUni_of_ah {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hO : H24K.SAT.OB1 x)
    {beta gamma : ℝ} (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hcell : CellAt F U_A2 D_A2 (uT2 x beta gamma))
    (h05 : ⟪x 0, uT2 x beta gamma⟫ < ⟪x 5, uT2 x beta gamma⟫)
    (h03 : ⟪x 0, uT2 x beta gamma⟫ < ⟪x 3, uT2 x beta gamma⟫) :
    H21.RobUni (fun i => ⟪x (cA2 i), uT2 x beta gamma⟫) := by
  have hF1 : ⟪x 0, uT2 x beta gamma⟫ ≤ ⟪x 1, uT2 x beta gamma⟫ →
      ⟪x 1, uT2 x beta gamma⟫ < ⟪x 6, uT2 x beta gamma⟫ := by
    intro h
    have h0 : ⟪x 0 - x 1, uT2 x beta gamma⟫ ≤ 0 := by rw [inner_sub_left]; linarith
    have h6 := (uT2_depth_signs F hO hbeta hgamma).2 h0
    rw [inner_sub_left] at h6; linarith
  have hnb6 := cA2_not_back_03_56 F hcell
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
      · have h6 := hF1 hc
        first
          | linarith
          | exact hnb6 (max_le (le_min (by linarith) (by linarith)) (le_min (by linarith) (by linarith)))
      · first
          | linarith
          | exact hnb6 (max_le (le_min (by linarith) (by linarith)) (le_min (by linarith) (by linarith)))

/-- **Lemma AH (`LexAny` form):** `cA2` open cell + `OB1` + `z₀ < z₅` + `z₀ < z₃` gives
`Gen.LexAny F`. -/
theorem cA2_lexAny_of_ah {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hO : H24K.SAT.OB1 x)
    {beta gamma : ℝ} (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hcell : CellAt F U_A2 D_A2 (uT2 x beta gamma))
    (h05 : ⟪x 0, uT2 x beta gamma⟫ < ⟪x 5, uT2 x beta gamma⟫)
    (h03 : ⟪x 0, uT2 x beta gamma⟫ < ⟪x 3, uT2 x beta gamma⟫) :
    Gen.LexAny F :=
  WC.lexAny_of_cellAt_robUni (by norm_num) F cA2_inj cA2_cyc hcell
    (cA2_robUni_of_ah F hO hbeta hgamma hcell h05 h03)

/-- **AH3Region:** `OB1 x`, `ω₄ > 0`, `b₃ < 1` (`F.f 1 (x 2) < F.f 1 (x 3)`: `x₃ - x₂` is a vertex
of the closed `cA2` cell) and the two Gram inequalities `⟪x₅ - x₀, x₃ - x₂⟫ > 0`,
`⟪x₃ - x₀, x₃ - x₂⟫ > 0` at that edge view.  (`CbarIn x` gives `ω₄ > 0`; nothing else of it is
used.) -/
def AH3Region (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  0 < omega4 x ∧ H24K.SAT.OB1 x ∧ F.f 1 (x 2) < F.f 1 (x 3) ∧
  0 < ⟪x 5 - x 0, x 3 - x 2⟫ ∧ 0 < ⟪x 3 - x 0, x 3 - x 2⟫

/-- **AH3 corner:** on `AH3Region x F` there are `β, γ > 0` with `uT2 x β γ` an open `cA2` view
(`β = (1 + t - b₃) / a₃`, `γ = c₃ / a₃`, i.e. the view `x₃ - x₂ + t (x₁ - x₂)`, `t > 0` small)
satisfying `z₀ < z₅` and `z₀ < z₃`. -/
theorem cA2_exists_of_ah3Region {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x}
    (hZ : AH3Region x F) :
    ∃ beta gamma : ℝ, 0 < beta ∧ 0 < gamma ∧ CellAt F U_A2 D_A2 (uT2 x beta gamma) ∧
      ⟪x 0, uT2 x beta gamma⟫ < ⟪x 5, uT2 x beta gamma⟫ ∧
      ⟪x 0, uT2 x beta gamma⟫ < ⟪x 3, uT2 x beta gamma⟫ := by
  rcases hZ with ⟨hw4, -, hf, hA5x, hA3x⟩
  have T := type24OfFac F
  have ha : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hc : 0 < oblX6 x 3 := T.X6_pos (v := 3) (by decide)
  -- `b₃ < 1`
  have hb1 : oblX2 x 3 < 1 := by
    have e := fac_eval F 1 3
    rw [F.zero 1 0 (by decide), F.zero 1 1 (by decide), F.zero 1 6 (by decide)] at e
    have h12 := F.neg 1 2 (by decide)
    nlinarith
  -- facet 4 at the corner
  have hf4 : 0 < F.f 4 (x 3) - F.f 4 (x 2) := by
    have e3 := fac_eval F 4 3
    have e4 := fac_eval F 4 4
    rw [F.zero 4 0 (by decide), F.zero 4 6 (by decide)] at e3 e4
    rw [F.zero 4 4 (by decide)] at e4
    have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
    have h4eq := eq4 F
    have hf21 : F.f 4 (x 2) - F.f 4 (x 1) = omega4 x * F.f 4 (x 1) := by
      have hmul : oblX2 x 4 * (F.f 4 (x 2) - F.f 4 (x 1)) =
          oblX2 x 4 * (omega4 x * F.f 4 (x 1)) := by
        linear_combination -e4 + F.f 4 (x 1) * h4eq
      exact mul_left_cancel₀ hb4.ne' hmul
    have hf1 : F.f 4 (x 1) < 0 := F.neg 4 1 (by decide)
    have hid : F.f 4 (x 3) - F.f 4 (x 2) = (-F.f 4 (x 1)) *
        (oblX0 x 3 + oblX6 x 3 + omega4 x * (1 - oblX2 x 3)) := by
      linear_combination e3 - hf21 * (1 - oblX2 x 3) + 0 * hf21
    rw [hid]
    exact mul_pos (neg_pos.mpr hf1) (by nlinarith)
  have hane : oblX0 x 3 ≠ 0 := ha.ne'
  have hrep : x 3 - x 1 = oblX0 x 3 • (x 0 - x 1) + oblX2 x 3 • (x 2 - x 1) +
      oblX6 x 3 • (x 6 - x 1) := by
    rw [T.rep 3]; abel
  -- the view `uT2 x β γ` is a positive multiple of `x₃ - x₂ + t (x₁ - x₂)`
  have hview : ∀ t : ℝ, uT2 x ((1 + t - oblX2 x 3) / oblX0 x 3) (oblX6 x 3 / oblX0 x 3) =
      (oblX0 x 3)⁻¹ • ((x 3 - x 2) + t • (x 1 - x 2)) := by
    intro t
    have e : (x 3 - x 2) + t • (x 1 - x 2) = oblX0 x 3 • (x 0 - x 1) +
        (oblX2 x 3 - 1 - t) • (x 2 - x 1) + oblX6 x 3 • (x 6 - x 1) := by
      rw [T.rep 3]; module
    have e1 : -((1 + t - oblX2 x 3) / oblX0 x 3) = (oblX0 x 3)⁻¹ * (oblX2 x 3 - 1 - t) := by
      field_simp; ring
    have e2 : oblX6 x 3 / oblX0 x 3 = (oblX0 x 3)⁻¹ * oblX6 x 3 := by rw [div_eq_inv_mul]
    rw [uT2, capView, e, smul_add, smul_add, smul_smul, smul_smul, smul_smul,
      inv_mul_cancel₀ hane, one_smul, e1, e2]
  have hN : ∀ (s : Fin 9) (t : ℝ), ⟪F.N s, (x 3 - x 2) + t • (x 1 - x 2)⟫ =
      (F.f s (x 3) - F.f s (x 2)) + (F.f s (x 1) - F.f s (x 2)) * t := by
    intro s t
    rw [inner_add_right, real_inner_smul_right, F.inner_sub, F.inner_sub, mul_comm]
  have hz : ∀ (u : Fin 7) (t : ℝ), ⟪x u - x 0, (x 3 - x 2) + t • (x 1 - x 2)⟫ =
      ⟪x u - x 0, x 3 - x 2⟫ + ⟪x u - x 0, x 1 - x 2⟫ * t := by
    intro u t
    rw [inner_add_right, real_inner_smul_right, mul_comm]
  have hA1 : 0 < F.f 1 (x 3) - F.f 1 (x 2) := sub_pos.mpr hf
  have hA3 : 0 < F.f 3 (x 3) - F.f 3 (x 2) := by
    rw [F.zero 3 3 (by decide)]; linarith [F.neg 3 2 (by decide)]
  have hA8 : 0 < F.f 8 (x 3) - F.f 8 (x 2) := by
    rw [F.zero 8 3 (by decide)]; linarith [F.neg 8 2 (by decide)]
  have hA0 : F.f 0 (x 3) - F.f 0 (x 2) < 0 := by
    rw [F.zero 0 2 (by decide)]; linarith [F.neg 0 3 (by decide)]
  have hA2 : F.f 2 (x 3) - F.f 2 (x 2) < 0 := by
    rw [F.zero 2 2 (by decide)]; linarith [F.neg 2 3 (by decide)]
  have hA5 : F.f 5 (x 3) - F.f 5 (x 2) < 0 := by
    rw [F.zero 5 2 (by decide)]; linarith [F.neg 5 3 (by decide)]
  have hf6 := F.neg 6 1 (by decide)
  have hf7 := F.neg 7 1 (by decide)
  have key : ∀ᶠ t : ℝ in 𝓝[>] 0, ∃ beta gamma : ℝ, 0 < beta ∧ 0 < gamma ∧
      CellAt F U_A2 D_A2 (uT2 x beta gamma) ∧
      ⟪x 0, uT2 x beta gamma⟫ < ⟪x 5, uT2 x beta gamma⟫ ∧
      ⟪x 0, uT2 x beta gamma⟫ < ⟪x 3, uT2 x beta gamma⟫ := by
    filter_upwards [Minimality.T24.Belt.ev_gt0,
      Minimality.T24.Belt.ev_pos _ (F.f 1 (x 1) - F.f 1 (x 2)) hA1,
      Minimality.T24.Belt.ev_pos _ (F.f 3 (x 1) - F.f 3 (x 2)) hA3,
      Minimality.T24.Belt.ev_pos _ (F.f 4 (x 1) - F.f 4 (x 2)) hf4,
      Minimality.T24.Belt.ev_pos _ (F.f 8 (x 1) - F.f 8 (x 2)) hA8,
      Minimality.T24.Belt.ev_neg _ (F.f 0 (x 1) - F.f 0 (x 2)) hA0,
      Minimality.T24.Belt.ev_neg _ (F.f 2 (x 1) - F.f 2 (x 2)) hA2,
      Minimality.T24.Belt.ev_neg _ (F.f 5 (x 1) - F.f 5 (x 2)) hA5,
      Minimality.T24.Belt.ev_pos _ ⟪x 5 - x 0, x 1 - x 2⟫ hA5x,
      Minimality.T24.Belt.ev_pos _ ⟪x 3 - x 0, x 1 - x 2⟫ hA3x] with t ht p1 p3 p4 p8 q0 q2 q5 r5 r3
    have hpos : 0 < (1 + t - oblX2 x 3) / oblX0 x 3 := div_pos (by linarith) ha
    have hpos' : 0 < oblX6 x 3 / oblX0 x 3 := div_pos hc ha
    have hia : 0 < (oblX0 x 3)⁻¹ := inv_pos.mpr ha
    have hk : ∀ s : Fin 9, ⟪F.N s, uT2 x ((1 + t - oblX2 x 3) / oblX0 x 3)
        (oblX6 x 3 / oblX0 x 3)⟫ = (oblX0 x 3)⁻¹ *
        ((F.f s (x 3) - F.f s (x 2)) + (F.f s (x 1) - F.f s (x 2)) * t) := by
      intro s; rw [hview, real_inner_smul_right, hN]
    refine ⟨_, _, hpos, hpos', ?_, ?_, ?_⟩
    · have c1 : 0 < ⟪F.N 1, uT2 x ((1 + t - oblX2 x 3) / oblX0 x 3) (oblX6 x 3 / oblX0 x 3)⟫ := by
        rw [hk]; exact mul_pos hia p1
      have c3 : 0 < ⟪F.N 3, uT2 x ((1 + t - oblX2 x 3) / oblX0 x 3) (oblX6 x 3 / oblX0 x 3)⟫ := by
        rw [hk]; exact mul_pos hia p3
      have c4 : 0 < ⟪F.N 4, uT2 x ((1 + t - oblX2 x 3) / oblX0 x 3) (oblX6 x 3 / oblX0 x 3)⟫ := by
        rw [hk]; exact mul_pos hia p4
      have c8 : 0 < ⟪F.N 8, uT2 x ((1 + t - oblX2 x 3) / oblX0 x 3) (oblX6 x 3 / oblX0 x 3)⟫ := by
        rw [hk]; exact mul_pos hia p8
      have c0 : ⟪F.N 0, uT2 x ((1 + t - oblX2 x 3) / oblX0 x 3) (oblX6 x 3 / oblX0 x 3)⟫ < 0 := by
        rw [hk]; exact mul_neg_of_pos_of_neg hia q0
      have c2 : ⟪F.N 2, uT2 x ((1 + t - oblX2 x 3) / oblX0 x 3) (oblX6 x 3 / oblX0 x 3)⟫ < 0 := by
        rw [hk]; exact mul_neg_of_pos_of_neg hia q2
      have c5 : ⟪F.N 5, uT2 x ((1 + t - oblX2 x 3) / oblX0 x 3) (oblX6 x 3 / oblX0 x 3)⟫ < 0 := by
        rw [hk]; exact mul_neg_of_pos_of_neg hia q5
      have c6 : ⟪F.N 6, uT2 x ((1 + t - oblX2 x 3) / oblX0 x 3) (oblX6 x 3 / oblX0 x 3)⟫ < 0 := by
        rw [hk, F.zero 6 3 (by decide), F.zero 6 2 (by decide)]
        exact mul_neg_of_pos_of_neg hia (by nlinarith)
      have c7 : ⟪F.N 7, uT2 x ((1 + t - oblX2 x 3) / oblX0 x 3) (oblX6 x 3 / oblX0 x 3)⟫ < 0 := by
        rw [hk, F.zero 7 3 (by decide), F.zero 7 2 (by decide)]
        exact mul_neg_of_pos_of_neg hia (by nlinarith)
      refine ⟨fun s hs => ?_, fun s hs => ?_⟩
      · fin_cases s <;> simp [U_A2] at hs
        · exact c1
        · exact c3
        · exact c4
        · exact c8
      · fin_cases s <;> simp [D_A2] at hs
        · exact c0
        · exact c2
        · exact c5
        · exact c6
        · exact c7
    · have e : ⟪x 5, uT2 x ((1 + t - oblX2 x 3) / oblX0 x 3) (oblX6 x 3 / oblX0 x 3)⟫ -
          ⟪x 0, uT2 x ((1 + t - oblX2 x 3) / oblX0 x 3) (oblX6 x 3 / oblX0 x 3)⟫ =
          (oblX0 x 3)⁻¹ * (⟪x 5 - x 0, x 3 - x 2⟫ + ⟪x 5 - x 0, x 1 - x 2⟫ * t) := by
        rw [← inner_sub_left, hview, real_inner_smul_right, hz]
      have := mul_pos hia r5
      linarith
    · have e : ⟪x 3, uT2 x ((1 + t - oblX2 x 3) / oblX0 x 3) (oblX6 x 3 / oblX0 x 3)⟫ -
          ⟪x 0, uT2 x ((1 + t - oblX2 x 3) / oblX0 x 3) (oblX6 x 3 / oblX0 x 3)⟫ =
          (oblX0 x 3)⁻¹ * (⟪x 3 - x 0, x 3 - x 2⟫ + ⟪x 3 - x 0, x 1 - x 2⟫ * t) := by
        rw [← inner_sub_left, hview, real_inner_smul_right, hz]
      have := mul_pos hia r3
      linarith
  obtain ⟨t, beta, gamma, h⟩ := key.exists
  exact ⟨beta, gamma, h⟩

/-- **Lemma AH + AH3:** `AH3Region x F` implies `Gen.LexAny F`. -/
theorem lexAny_of_ah3Region {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x}
    (hZ : AH3Region x F) : Gen.LexAny F := by
  obtain ⟨beta, gamma, hb, hg, hcell, h05, h03⟩ := cA2_exists_of_ah3Region hZ
  exact cA2_lexAny_of_ah F hZ.2.1 hb hg hcell h05 h03

/-- **AH3 (`π_24` mirror):** `AH3Region (x ∘ Sym.pi24) (Sym.sym24 F)` implies `Gen.LexAny F`. -/
theorem lexAny_of_ah3Region_twin {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x}
    (hZ : AH3Region (x ∘ Sym.pi24) (Sym.sym24 F)) : Gen.LexAny F :=
  Sym.lexAny_sym F (lexAny_of_ah3Region hZ)

/-- **AH3 hole fact:** `HoleLeaf x F` excludes `AH3Region x F`. -/
theorem holeLeaf_not_ah3Region {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F)
    (hZ : AH3Region x F) : False :=
  hF.2.2.2.1 (lexAny_of_ah3Region hZ)

/-- **AH3 twin hole fact:** `HoleLeaf x F` excludes `AH3Region (x ∘ Sym.pi24) (Sym.sym24 F)`. -/
theorem holeLeaf_not_ah3Region_twin {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F)
    (hZ : AH3Region (x ∘ Sym.pi24) (Sym.sym24 F)) : False :=
  hF.2.2.2.1 (lexAny_of_ah3Region_twin hZ)

end Minimality.T24.TwoCone
