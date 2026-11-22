import Minimality.M4cType24
import Minimality.Type24Quad

/-!
# Type 24, region A1: bridges and easy region facts (group F1)

`sigma_le_one_iff`, `a5_gt_one_iff_N5`, `lam5_nonneg_A1`, `E05P5U_le`, `t25_facets`, `t25_016`,
`t26_facets`, `t25_tilt_frame`.  Facet indices are those of `s0x_S24`:
`0 = 012, 1 = 016, 2 = 025, 3 = 0345, 4 = 046, 5 = 126, 6 = 235, 7 = 236, 8 = 346`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.A1

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell
  Minimality.LexCell Minimality.Split Minimality.T24.M4 Minimality.T24.A7 Minimality.T24.A8
  Minimality.T24.Q24 Minimality.T24

/-- Lemma M with the `f8` relation: `x3 - x0 = s (x4 - x0) + t (x5 - x0)` forces
`t f8(x5) = (s + t - 1) f8(x0)` (facet `346`, index 8). -/
theorem f8_relation {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {s t : ℝ}
    (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) :
    t * F.f 8 (x 5) = (s + t - 1) * F.f 8 (x 0) := by
  have h3 : F.f 8 (x 3) = 0 := F.zero 8 3 (by decide)
  have h4 : F.f 8 (x 4) = 0 := F.zero 8 4 (by decide)
  have e : F.f 8 (x 3) - F.f 8 (x 0) =
      s * (F.f 8 (x 4) - F.f 8 (x 0)) + t * (F.f 8 (x 5) - F.f 8 (x 0)) := by
    rw [F.hN 8 (x 3) (x 0), hdec, inner_add_right, inner_smul_right, inner_smul_right,
      ← F.hN 8 (x 4) (x 0), ← F.hN 8 (x 5) (x 0)]
  rw [h3, h4] at e
  linarith

theorem sigma_le_one_iff {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    F.f 8 (x 0) ≤ F.f 8 (x 5) ↔
      ∀ s t : ℝ, 0 < s → 0 < t → 1 < s + t →
        x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0) → s ≤ 1 := by
  have f0 : F.f 8 (x 0) < 0 := F.neg 8 0 (by decide)
  have f5 : F.f 8 (x 5) < 0 := F.neg 8 5 (by decide)
  constructor
  · intro h s t hs ht _ hdec
    have e := f8_relation F hdec
    by_contra hlt
    push Not at hlt
    nlinarith
  · intro h
    obtain ⟨s, t, hs, ht, hdec, -⟩ := lemmaM_coords F
    have e := f8_relation F hdec
    have hst : 1 < s + t := by nlinarith
    have hs1 := h s t hs ht hst hdec
    nlinarith

theorem a5_gt_one_iff_N5 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    ⟪F.N 5, x 5 - x 0⟫ < 0 ↔ 1 < oblX0 x 5 := by
  have ev := fac_eval F 5 5
  rw [F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)] at ev
  have f0 : F.f 5 (x 0) < 0 := F.neg 5 0 (by decide)
  rw [← F.hN 5 (x 5) (x 0), ev]
  constructor
  · intro h; by_contra hle; push Not at hle; nlinarith
  · intro h; nlinarith

/-- `Lam5 > 0` already from `sigma ≤ 1` (the `a5 > 1` hypothesis of A1PLAN is not needed, nor `C̄`):
`t (f7(x5) - f7(x0)) = (s - 1) f7(x0) - s f7(x4)` and `⟪N7, x5 - x0⟫ = -f7(x1) Lam5`. -/
theorem lam5_pos_of_sigma {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hsig : F.f 8 (x 0) ≤ F.f 8 (x 5)) : 0 < Lam5 x := by
  have T := type24OfFac F
  obtain ⟨s, t, hs, ht, hdec, -⟩ := lemmaM_coords F
  have e8 := f8_relation F hdec
  have f0 : F.f 8 (x 0) < 0 := F.neg 8 0 (by decide)
  have f5 : F.f 8 (x 5) < 0 := F.neg 8 5 (by decide)
  have hs1 : s ≤ 1 := by nlinarith
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hf7_0 : F.f 7 (x 0) = (1 + omega3 x) * F.f 7 (x 1) := by
    have ev7 := fac_eval F 7 3
    rw [F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at ev7
    have e3 := eq3 F
    have hprod : oblX0 x 3 * (F.f 7 (x 0) - (1 + omega3 x) * F.f 7 (x 1)) = 0 := by
      linear_combination -ev7 + F.f 7 (x 1) * e3
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left ha3.ne')
  have hw7 : F.f 7 (x 5) - F.f 7 (x 0) = (-F.f 7 (x 1)) * Lam5 x := by
    dsimp [Lam5]
    have ev7_5 := fac_eval F 7 5
    rw [F.zero 7 2 (by decide), F.zero 7 6 (by decide), hf7_0] at ev7_5
    rw [ev7_5, hf7_0]; ring
  have h7_0 : F.f 7 (x 0) < 0 := F.neg 7 0 (by decide)
  have h7_4 : F.f 7 (x 4) < 0 := F.neg 7 4 (by decide)
  have h7_1 : F.f 7 (x 1) < 0 := F.neg 7 1 (by decide)
  have e7 : F.f 7 (x 3) - F.f 7 (x 0) =
      s * (F.f 7 (x 4) - F.f 7 (x 0)) + t * (F.f 7 (x 5) - F.f 7 (x 0)) := by
    rw [F.hN 7 (x 3) (x 0), hdec, inner_add_right, inner_smul_right, inner_smul_right,
      ← F.hN 7 (x 4) (x 0), ← F.hN 7 (x 5) (x 0)]
  rw [F.zero 7 3 (by decide)] at e7
  have hpos : 0 < t * (F.f 7 (x 5) - F.f 7 (x 0)) := by nlinarith
  have hpos' : 0 < F.f 7 (x 5) - F.f 7 (x 0) := (mul_pos_iff_of_pos_left ht).mp hpos
  rw [hw7] at hpos'
  by_contra hc
  push Not at hc
  nlinarith

theorem lam5_nonneg_A1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hsig : F.f 8 (x 0) ≤ F.f 8 (x 5)) : 0 ≤ Lam5 x :=
  (lam5_pos_of_sigma F hsig).le

theorem nC_pos_of_le {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha4 : oblX0 x 4 ≤ 1) (ha5 : 1 < oblX0 x 5) : 0 < nC x := by
  have T := type24OfFac F
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  dsimp [nC]
  nlinarith

theorem R04_neg_le {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha4 : oblX0 x 4 ≤ 1) (ha5 : 1 < oblX0 x 5) : R04 x < 0 := by
  have T := type24OfFac F
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hc4 : 0 < oblX6 x 4 := T.X6_pos (v := 4) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  dsimp [R04]
  nlinarith

theorem e05p5u_split_le {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha5 : 1 < oblX0 x 5) (hR46 : R46 x < 0) (hR04 : R04 x < 0)
    (hfac_lex : ∀ t : Fin 9,
      LexPos3 (if decide (t = 3 ∨ t = 6 ∨ t = 7 ∨ t = 8) then ⟪F.N t, x 5 - x 0⟫ else -⟪F.N t, x 5 - x 0⟫)
              (if decide (t = 3 ∨ t = 6 ∨ t = 7 ∨ t = 8) then ⟪F.N t, x 6 - x 1⟫ else -⟪F.N t, x 6 - x 1⟫)
              (if decide (t = 3 ∨ t = 6 ∨ t = 7 ∨ t = 8) then ⟪F.N t, x 6 - x 5⟫ else -⟪F.N t, x 6 - x 5⟫))
    (hz : ⟪x 4, x 5 - x 0⟫ < ⟪x 5, x 5 - x 0⟫ ∧ ⟪x 5, x 5 - x 0⟫ < ⟪x 2, x 5 - x 0⟫)
    (h65 : LexPos3 (-⟪x 6 - x 5, x 5 - x 0⟫) (-⟪x 6 - x 5, x 6 - x 1⟫) (-⟪x 6 - x 5, x 6 - x 5⟫)) :
    SplitAny24 F := by
  have T := type24OfFac F
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hrows := rows_P5 F
  have hd2 : 0 < det24 x * det24 x := mul_self_pos.mpr T.det_ne
  let w05 : ℝ³ := x 5 - x 0
  let d1 : ℝ³ := x 6 - x 1
  let d2 : ℝ³ := x 6 - x 5
  let c : ZMod 5 → Fin 7 := ![0, 4, 6, 2, 5]
  let pat : Fin 9 → Bool := fun t => decide (t = 3 ∨ t = 6 ∨ t = 7 ∨ t = 8)
  have hz05 : ⟪x 0 - x 5, w05⟫ < 0 := by
    dsimp [w05]; rw [← neg_sub, inner_neg_left]
    have hw_ne : w05 ≠ 0 := sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide)
    exact neg_neg_of_pos (real_inner_self_pos.mpr hw_ne)
  have hz45 : ⟪x 4 - x 5, w05⟫ < 0 := by rw [inner_sub_left]; exact sub_lt_zero.mpr hz.1
  have hz25 : 0 < ⟪x 2 - x 5, w05⟫ := by rw [inner_sub_left]; exact sub_pos.mpr hz.2
  refine splitAny24_of_lex3' F (by decide) c
    (by intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide))
    pat (by unfold S0xCycOK; decide) w05 d1 d2 hfac_lex 2 4 (by decide) (by decide) (det24 x) ?_
  intro i hia j hj hjc
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by decide +revert
  have hc0 : c 0 = 0 := rfl
  have hc1 : c 1 = 4 := rfl
  have hc2 : c 2 = 6 := rfl
  have hc3 : c 3 = 2 := rfl
  have hc4 : c 4 = 5 := rfl
  have he0 : (0 : ZMod 5) + 1 = 1 := rfl
  have he1 : (1 : ZMod 5) + 1 = 2 := rfl
  have he2 : (2 : ZMod 5) + 1 = 3 := rfl
  have he3 : (3 : ZMod 5) + 1 = 4 := rfl
  have he4 : (4 : ZMod 5) + 1 = 0 := rfl
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · rcases hj with rfl | rfl
    · refine ⟨-1, Or.inl (by rw [hc0, hc4]; linarith [hz05]), Or.inl ?_⟩
      rw [he0, he2, hc0, hc1, hc2, hc3]; dsimp [w05]; rw [hrows.1]
      have h1 : det24 x * -1 * (det24 x * R04 x) = (det24 x * det24 x) * (-R04 x) := by ring
      rw [h1]; exact mul_pos hd2 (neg_pos.mpr hR04)
    · refine ⟨-1, Or.inl (by rw [he0, hc1, hc4]; linarith [hz45]), Or.inl ?_⟩
      rw [he0, he2, hc0, hc1, hc2, hc3]; dsimp [w05]; rw [hrows.1]
      have h1 : det24 x * -1 * (det24 x * R04 x) = (det24 x * det24 x) * (-R04 x) := by ring
      rw [h1]; exact mul_pos hd2 (neg_pos.mpr hR04)
  · rcases hj with rfl | rfl
    · refine ⟨-1, Or.inl (by rw [hc1, hc4]; linarith [hz45]), Or.inl ?_⟩
      rw [he1, he2, hc1, hc2, hc3]; dsimp [w05]; rw [hrows.2.1]
      have h1 : det24 x * -1 * (det24 x * R46 x) = (det24 x * det24 x) * (-R46 x) := by ring
      rw [h1]; exact mul_pos hd2 (neg_pos.mpr hR46)
    · refine ⟨-1, ?_, Or.inl ?_⟩
      · rw [he1, hc2, hc4]
        simpa only [neg_one_mul] using h65
      · rw [he1, he2, hc1, hc2, hc3]; dsimp [w05]; rw [hrows.2.1]
        have h1 : det24 x * -1 * (det24 x * R46 x) = (det24 x * det24 x) * (-R46 x) := by ring
        rw [h1]; exact mul_pos hd2 (neg_pos.mpr hR46)
  · exact absurd rfl hia
  · rcases hj with rfl | rfl
    · refine ⟨1, Or.inl (by rw [hc3, hc4]; linarith [hz25]), Or.inl ?_⟩
      rw [he3, he2, hc2, hc3, hc4]; dsimp [w05]; rw [hrows.2.2.1]
      have h5_pos : 0 < oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1 := by linarith
      have h1 : det24 x * 1 * (det24 x * (oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1)) =
          (det24 x * det24 x) * (oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1) := by ring
      rw [h1]; exact mul_pos hd2 h5_pos
    · exact absurd rfl hjc
  · rcases hj with rfl | rfl
    · exact absurd rfl hjc
    · refine ⟨-1, Or.inl (by rw [he4, hc0, hc4]; linarith [hz05]), Or.inr ⟨?_, Or.inl ?_⟩⟩
      · rw [he4, he2, hc0, hc2, hc3, hc4]; dsimp [w05]
        have : det3 (x 0 - x 5) (x 2 - x 6) (x 5 - x 0) = 0 := by
          simp only [det3_expand, PiLp.sub_apply]; ring
        rw [this, mul_zero]
      · rw [he4, he2, hc0, hc2, hc3, hc4]; dsimp [d1]; rw [hrows.2.2.2]
        have h1 : det24 x * -1 * (det24 x * (1 - oblX0 x 5)) =
            (det24 x * det24 x) * (oblX0 x 5 - 1) := by ring
        rw [h1]; exact mul_pos hd2 (sub_pos.mpr ha5)

theorem E05P5U_le {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (ha5 : 1 < oblX0 x 5) (ha4 : oblX0 x 4 ≤ 1)
    (hL : 0 ≤ Lam5 x) (h346 : F.f 8 (x 0) ≤ F.f 8 (x 5))
    (hz : ⟪x 4, x 5 - x 0⟫ < ⟪x 5, x 5 - x 0⟫ ∧
          ⟪x 5, x 5 - x 0⟫ < ⟪x 2, x 5 - x 0⟫) :
    LexAny F ∨ SplitAny24 F := by
  have T := type24OfFac F
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hnc : F.f 3 (x 1) < F.f 3 (x 6) :=
    (nC_pos_iff F).mp (nC_pos_of_le F ha4 ha5)
  have hR46 : R46 x < 0 := R46_neg F ha5 hL
  have hR04 : R04 x < 0 := R04_neg_le F ha4 ha5
  let w05 : ℝ³ := x 5 - x 0
  let d1 : ℝ³ := x 6 - x 1
  let d2 : ℝ³ := x 6 - x 5
  let c : ZMod 5 → Fin 7 := ![0, 4, 6, 2, 5]
  let pat : Fin 9 → Bool := fun t => decide (t = 3 ∨ t = 6 ∨ t = 7 ∨ t = 8)
  have hc_inj : Function.Injective c := by
    intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)
  have hcyc_ok : S0xCycOK s0x_S24 c pat := by unfold S0xCycOK; decide
  -- Facings at `(w05, d1, d2)`:
  have hf0 : ⟪F.N 0, w05⟫ < 0 := by
    dsimp [w05]; rw [← F.hN 0 (x 5) (x 0), F.zero 0 0 (by decide), sub_zero]
    exact F.neg 0 5 (by decide)
  have hf1 : ⟪F.N 1, w05⟫ < 0 := by
    dsimp [w05]; rw [← F.hN 1 (x 5) (x 0), F.zero 1 0 (by decide), sub_zero]
    exact F.neg 1 5 (by decide)
  have hf2_0 : ⟪F.N 2, w05⟫ = 0 := by
    dsimp [w05]; rw [← F.hN 2 (x 5) (x 0), F.zero 2 5 (by decide), F.zero 2 0 (by decide), sub_self]
  have hd2_1 : 0 < -⟪F.N 2, d1⟫ := by
    dsimp [d1]; rw [← F.hN 2 (x 6) (x 1)]
    have ev25 := fac_eval F 2 5
    rw [F.zero 2 5 (by decide), F.zero 2 0 (by decide), F.zero 2 2 (by decide)] at ev25
    have e5 := eq5 F
    have h1' : F.f 2 (x 1) * (1 - oblX0 x 5 - oblX2 x 5) +
        oblX6 x 5 * (F.f 2 (x 6) - F.f 2 (x 1)) = 0 := by linear_combination -ev25
    have h2' : oblX6 x 5 * ((F.f 2 (x 6) - F.f 2 (x 1)) - F.f 2 (x 1) * omega5 x) = 0 := by
      linear_combination h1' + F.f 2 (x 1) * e5
    have h6_eq : F.f 2 (x 6) - F.f 2 (x 1) = F.f 2 (x 1) * omega5 x :=
      sub_eq_zero.mp ((mul_eq_zero.mp h2').resolve_left hc5.ne')
    rw [h6_eq, ← neg_mul]
    exact mul_pos (by linarith [F.neg 2 1 (by decide)]) hC.2.2.1
  have hf3_0 : ⟪F.N 3, w05⟫ = 0 := by
    dsimp [w05]; rw [← F.hN 3 (x 5) (x 0), F.zero 3 5 (by decide), F.zero 3 0 (by decide), sub_self]
  have hd3_1 : 0 < ⟪F.N 3, d1⟫ := by
    dsimp [d1]; rw [← F.hN 3 (x 6) (x 1)]; exact sub_pos.mpr hnc
  have hf4 : ⟪F.N 4, w05⟫ < 0 := by
    dsimp [w05]; rw [← F.hN 4 (x 5) (x 0), F.zero 4 0 (by decide), sub_zero]
    exact F.neg 4 5 (by decide)
  have hf5 : ⟪F.N 5, w05⟫ < 0 := by
    dsimp [w05]; rw [← F.hN 5 (x 5) (x 0)]
    have ev5 := fac_eval F 5 5
    rw [F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)] at ev5
    rw [ev5]
    have hmul : (oblX0 x 5 - 1) * F.f 5 (x 0) =
        (0 + oblX0 x 5 * (F.f 5 (x 0) - 0) + oblX2 x 5 * (0 - 0) + oblX6 x 5 * (0 - 0)) -
          F.f 5 (x 0) := by ring
    rw [← hmul]
    exact mul_neg_of_pos_of_neg (sub_pos.mpr ha5) (F.neg 5 0 (by decide))
  have hf6 : 0 < ⟪F.N 6, w05⟫ := by
    dsimp [w05]; rw [← F.hN 6 (x 5) (x 0), F.zero 6 5 (by decide), zero_sub]
    linarith [F.neg 6 0 (by decide)]
  have hf7_lex : LexPos3 ⟪F.N 7, w05⟫ ⟪F.N 7, d1⟫ ⟪F.N 7, d2⟫ := by
    have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
    have hf7_0 : F.f 7 (x 0) = (1 + omega3 x) * F.f 7 (x 1) := by
      have ev7_3 := fac_eval F 7 3
      rw [F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at ev7_3
      have e3 := eq3 F
      have h7_id : oblX0 x 3 * (F.f 7 (x 0) - (1 + omega3 x) * F.f 7 (x 1)) = 0 := by
        linear_combination -ev7_3 + F.f 7 (x 1) * e3
      exact sub_eq_zero.mp ((mul_eq_zero.mp h7_id).resolve_left ha3.ne')
    have hw7 : ⟪F.N 7, w05⟫ = (-F.f 7 (x 1)) * Lam5 x := by
      dsimp [w05, Lam5]; rw [← F.hN 7 (x 5) (x 0)]
      have ev7_5 := fac_eval F 7 5
      rw [F.zero 7 2 (by decide), F.zero 7 6 (by decide), hf7_0] at ev7_5
      rw [ev7_5, hf7_0]; ring
    have hd7_1 : 0 < ⟪F.N 7, d1⟫ := by
      dsimp [d1]; rw [← F.hN 7 (x 6) (x 1), F.zero 7 6 (by decide), zero_sub]
      linarith [F.neg 7 1 (by decide)]
    rcases eq_or_lt_of_le hL with hL0 | hLpos
    · exact Or.inr ⟨by rw [hw7, ← hL0, mul_zero], Or.inl hd7_1⟩
    · exact Or.inl (by rw [hw7]; exact mul_pos (by linarith [F.neg 7 1 (by decide)]) hLpos)
  have hf8_lex : LexPos3 ⟪F.N 8, w05⟫ ⟪F.N 8, d1⟫ ⟪F.N 8, d2⟫ := by
    have hw8 : ⟪F.N 8, w05⟫ = F.f 8 (x 5) - F.f 8 (x 0) := by
      dsimp [w05]; rw [← F.hN 8 (x 5) (x 0)]
    have hd8_1 : 0 < ⟪F.N 8, d1⟫ := by
      dsimp [d1]; rw [← F.hN 8 (x 6) (x 1), F.zero 8 6 (by decide), zero_sub]
      linarith [F.neg 8 1 (by decide)]
    rcases eq_or_lt_of_le h346 with heq | hlt
    · exact Or.inr ⟨by rw [hw8, heq, sub_self], Or.inl hd8_1⟩
    · exact Or.inl (by rw [hw8]; linarith)
  have hfac_lex : ∀ t : Fin 9,
      LexPos3 (if pat t then ⟪F.N t, w05⟫ else -⟪F.N t, w05⟫)
              (if pat t then ⟪F.N t, d1⟫ else -⟪F.N t, d1⟫)
              (if pat t then ⟪F.N t, d2⟫ else -⟪F.N t, d2⟫) := by
    intro t; fin_cases t <;> simp [pat]
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by rw [hf2_0, neg_zero], Or.inl hd2_1⟩
    · exact Or.inr ⟨hf3_0, Or.inl hd3_1⟩
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inl hf6
    · exact hf7_lex
    · exact hf8_lex
  -- Case split on the lex sign of `⟪x 6 - x 5, (w05, d1, d2)⟫`:
  have hd2_pos : 0 < ⟪x 6 - x 5, d2⟫ := by
    dsimp [d2]
    exact real_inner_self_pos.mpr (sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide))
  by_cases hz65_0 : ⟪x 6 - x 5, w05⟫ = 0
  · by_cases hz65_1 : ⟪x 6 - x 5, d1⟫ < 0
    · -- Tie broken negatively at level 1 -> `SplitAny24 F`:
      exact Or.inr (e05p5u_split_le F ha5 hR46 hR04 hfac_lex hz
        (Or.inr ⟨by rw [neg_eq_zero]; exact hz65_0, Or.inl (neg_pos.mpr hz65_1)⟩))
    · -- Tie broken positively (`z5 <lex z6`) -> `LexAny F`:
      left
      have h65_lex : LexPos3 (⟪x 6, w05⟫ - ⟪x 5, w05⟫) (⟪x 6, d1⟫ - ⟪x 5, d1⟫)
          (⟪x 6, d2⟫ - ⟪x 5, d2⟫) := by
        rw [← inner_sub_left, ← inner_sub_left, ← inner_sub_left]
        rcases eq_or_lt_of_le (not_lt.mp hz65_1) with heq | hlt
        · exact Or.inr ⟨hz65_0, Or.inr ⟨heq.symm, hd2_pos⟩⟩
        · exact Or.inr ⟨hz65_0, Or.inl hlt⟩
      have hz05_lt : ⟪x 0, w05⟫ < ⟪x 5, w05⟫ := by
        refine sub_lt_zero.mp ?_
        have h_eq : ⟪x 0, w05⟫ - ⟪x 5, w05⟫ = -⟪w05, w05⟫ := by
          dsimp [w05]; rw [← inner_sub_left, ← neg_sub, inner_neg_left]
        have hw_ne : w05 ≠ 0 := sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide)
        rw [h_eq]
        exact neg_neg_of_pos (real_inner_self_pos.mpr hw_ne)
      refine ⟨5, inferInstance, c, {3, 6, 7, 8}, {0, 1, 2, 4, 5}, w05, d1, d2, by decide,
        hc_inj, (by unfold S0xCycUD; decide), ?_, ?_, ?_⟩
      · intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl
        · exact Or.inr ⟨hf3_0, Or.inl hd3_1⟩
        · exact Or.inl hf6
        · exact hf7_lex
        · exact hf8_lex
      · intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl
        · exact Or.inl (by linarith)
        · exact Or.inl (by linarith)
        · exact Or.inr ⟨by rw [hf2_0, neg_zero], Or.inl hd2_1⟩
        · exact Or.inl (by linarith)
        · exact Or.inl (by linarith)
      · refine robUniLex_five_twopeak _ ?_ ?_ ?_ h65_lex
        · have hc0 : c 0 = 0 := rfl
          have hc4 : c 4 = 5 := rfl
          rw [hc0, hc4]; exact hz05_lt
        · have hc1 : c 1 = 4 := rfl
          have hc4 : c 4 = 5 := rfl
          rw [hc1, hc4]; exact hz.1
        · have hc4 : c 4 = 5 := rfl
          have hc3 : c 3 = 2 := rfl
          rw [hc4, hc3]; exact hz.2
  · rcases lt_or_gt_of_ne hz65_0 with hz65_neg | hz65_pos
    · -- Strict `z6 < z5` -> `SplitAny24 F`:
      exact Or.inr (e05p5u_split_le F ha5 hR46 hR04 hfac_lex hz (Or.inl (neg_pos.mpr hz65_neg)))
    · -- Strict `z5 < z6` -> `LexAny F`:
      left
      have h65_lex : LexPos3 (⟪x 6, w05⟫ - ⟪x 5, w05⟫) (⟪x 6, d1⟫ - ⟪x 5, d1⟫)
          (⟪x 6, d2⟫ - ⟪x 5, d2⟫) := by
        rw [← inner_sub_left]; exact Or.inl hz65_pos
      have hz05_lt : ⟪x 0, w05⟫ < ⟪x 5, w05⟫ := by
        refine sub_lt_zero.mp ?_
        have h_eq : ⟪x 0, w05⟫ - ⟪x 5, w05⟫ = -⟪w05, w05⟫ := by
          dsimp [w05]; rw [← inner_sub_left, ← neg_sub, inner_neg_left]
        have hw_ne : w05 ≠ 0 := sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide)
        rw [h_eq]
        exact neg_neg_of_pos (real_inner_self_pos.mpr hw_ne)
      refine ⟨5, inferInstance, c, {3, 6, 7, 8}, {0, 1, 2, 4, 5}, w05, d1, d2, by decide,
        hc_inj, (by unfold S0xCycUD; decide), ?_, ?_, ?_⟩
      · intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl
        · exact Or.inr ⟨hf3_0, Or.inl hd3_1⟩
        · exact Or.inl hf6
        · exact hf7_lex
        · exact hf8_lex
      · intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl
        · exact Or.inl (by linarith)
        · exact Or.inl (by linarith)
        · exact Or.inr ⟨by rw [hf2_0, neg_zero], Or.inl hd2_1⟩
        · exact Or.inl (by linarith)
        · exact Or.inl (by linarith)
      · refine robUniLex_five_twopeak _ ?_ ?_ ?_ h65_lex
        · have hc0 : c 0 = 0 := rfl
          have hc4 : c 4 = 5 := rfl
          rw [hc0, hc4]; exact hz05_lt
        · have hc1 : c 1 = 4 := rfl
          have hc4 : c 4 = 5 := rfl
          rw [hc1, hc4]; exact hz.1
        · have hc4 : c 4 = 5 := rfl
          have hc3 : c 3 = 2 := rfl
          rw [hc4, hc3]; exact hz.2

/-- `E05P5U_le` with the hypothesis `0 ≤ Lam5` derived from `h346` (`lam5_nonneg_A1`). -/
theorem E05P5U_A1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (ha5 : 1 < oblX0 x 5) (ha4 : oblX0 x 4 ≤ 1)
    (h346 : F.f 8 (x 0) ≤ F.f 8 (x 5))
    (hz : ⟪x 4, x 5 - x 0⟫ < ⟪x 5, x 5 - x 0⟫ ∧
          ⟪x 5, x 5 - x 0⟫ < ⟪x 2, x 5 - x 0⟫) :
    LexAny F ∨ SplitAny24 F :=
  E05P5U_le F hC ha5 ha4 (lam5_nonneg_A1 F h346) h346 hz

/-! ### Facet signs at the T25 view `bT25 = x5 - x2` -/

theorem inner_bT25 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) :
    ⟪F.N t, bT25 x⟫ = F.f t (x 5) - F.f t (x 2) := by
  rw [bT25, F.inner_sub]

theorem t25_facets {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    ⟪F.N 0, bT25 x⟫ < 0 ∧ ⟪F.N 5, bT25 x⟫ < 0 ∧ ⟪F.N 7, bT25 x⟫ < 0 ∧ 0 < ⟪F.N 3, bT25 x⟫ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [inner_bT25, F.zero 0 2 (by decide)]; linarith [F.neg 0 5 (by decide)]
  · rw [inner_bT25, F.zero 5 2 (by decide)]; linarith [F.neg 5 5 (by decide)]
  · rw [inner_bT25, F.zero 7 2 (by decide)]; linarith [F.neg 7 5 (by decide)]
  · rw [inner_bT25, F.zero 3 5 (by decide)]; linarith [F.neg 3 2 (by decide)]

theorem t25_016 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    ⟪F.N 1, bT25 x⟫ < 0 ↔ 1 < oblX2 x 5 := by
  have ev := fac_eval F 1 5
  rw [F.zero 1 0 (by decide), F.zero 1 6 (by decide)] at ev
  have f2 : F.f 1 (x 2) < 0 := F.neg 1 2 (by decide)
  have e0 := F.zero 1 0 (by decide)
  have e1 : F.f 1 (x 1) = 0 := F.zero 1 1 (by decide)
  rw [e1] at ev
  rw [inner_bT25, ev]
  constructor
  · intro h; by_contra hle; push Not at hle; nlinarith
  · intro h; nlinarith

theorem t25_tilt_frame {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    LexPos3 (-⟪F.N 2, bT25 x⟫) (-⟪F.N 2, x 3 - x 5⟫) (-⟪F.N 2, x 0 - x 5⟫) ∧
    LexPos3 (-⟪F.N 6, bT25 x⟫) (-⟪F.N 6, x 3 - x 5⟫) (-⟪F.N 6, x 0 - x 5⟫) := by
  refine ⟨Or.inr ⟨by rw [bT25_N2 F, neg_zero], Or.inl ?_⟩,
    Or.inr ⟨by rw [bT25_N6 F, neg_zero], Or.inr ⟨?_, ?_⟩⟩⟩
  · rw [F.inner_sub, F.zero 2 5 (by decide)]; linarith [F.neg 2 3 (by decide)]
  · rw [F.inner_sub, F.zero 6 3 (by decide), F.zero 6 5 (by decide)]; simp
  · rw [F.inner_sub, F.zero 6 5 (by decide)]; linarith [F.neg 6 0 (by decide)]

/-! ### Facet signs at the T26 view `bT26` -/

theorem det3_rep0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (v : Fin 7) :
    x v - x 0 = (oblX0 x v - 1) • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) +
      oblX6 x v • (x 6 - x 1) := by
  have T := type24OfFac F
  have hv := T.rep v
  calc x v - x 0 = (x v - x 1) - (x 0 - x 1) := by abel
    _ = (oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1)) -
        (x 0 - x 1) := by rw [hv]; abel
    _ = _ := by module

/-- `bT26 = det24 * (c5 (x6 - x1) + (a5 + b5 - 1) (x2 - x1))`. -/
theorem bT26_frame_form {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    bT26 x = det24 x • (oblX6 x 5 • (x 6 - x 1) + (oblX0 x 5 + oblX2 x 5 - 1) • (x 2 - x 1)) := by
  have h50 := det3_rep0 F 5
  have e20 : (-1 : ℝ) • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) = x 2 - x 0 := by
    module
  have e21 : (0 : ℝ) • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) = x 2 - x 1 := by
    module
  have e61 : (0 : ℝ) • (x 0 - x 1) + (0 : ℝ) • (x 2 - x 1) + (1 : ℝ) • (x 6 - x 1) = x 6 - x 1 := by
    module
  have d21 : Split.det3 (x 2 - x 0) (x 5 - x 0) (x 2 - x 1) = oblX6 x 5 * det24 x := by
    have h := M4.det3_frame x (-1) 1 0 (oblX0 x 5 - 1) (oblX2 x 5) (oblX6 x 5) 0 1 0
    rw [e20, ← h50, e21] at h
    rw [Split.det3_eq_minimality, h]; ring
  have d61 : Split.det3 (x 2 - x 0) (x 5 - x 0) (x 6 - x 1) =
      -(oblX0 x 5 + oblX2 x 5 - 1) * det24 x := by
    have h := M4.det3_frame x (-1) 1 0 (oblX0 x 5 - 1) (oblX2 x 5) (oblX6 x 5) 0 0 1
    rw [e20, ← h50, e61] at h
    rw [Split.det3_eq_minimality, h]; ring
  unfold bT26
  rw [d21, d61]
  module

theorem inner_bT26 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) :
    ⟪F.N t, bT26 x⟫ = det24 x * (oblX6 x 5 * (F.f t (x 6) - F.f t (x 1)) +
      (oblX0 x 5 + oblX2 x 5 - 1) * (F.f t (x 2) - F.f t (x 1))) := by
  rw [bT26_frame_form F, inner_smul_right, inner_add_right, inner_smul_right, inner_smul_right,
    F.inner_sub, F.inner_sub]

/-- Facet signs at the T26 view.  `0 < det24 x` is the orientation of the frame: `bT26` is built from
`det3`, so the signs flip with `det24` (mirror image of the configuration). -/
theorem t26_facets {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hdet : 0 < det24 x)
    (ha5 : 1 < oblX0 x 5) :
    0 < ⟪F.N 6, bT26 x⟫ ∧ 0 < ⟪F.N 7, bT26 x⟫ ∧ ⟪F.N 3, bT26 x⟫ < 0 ∧ ⟪F.N 4, bT26 x⟫ < 0 := by
  have T := type24OfFac F
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [inner_bT26]
    apply mul_pos hdet
    have ev := fac_eval F 6 5
    rw [F.zero 6 5 (by decide), F.zero 6 2 (by decide)] at ev
    have f0 := F.neg 6 0 (by decide)
    have hF0 : 0 < oblX0 x 5 * (-F.f 6 (x 0)) := mul_pos (by linarith) (by linarith)
    rw [F.zero 6 2 (by decide)]
    linarith
  · rw [inner_bT26]
    apply mul_pos hdet
    rw [F.zero 7 6 (by decide), F.zero 7 2 (by decide)]
    nlinarith [F.neg 7 1 (by decide)]
  · rw [inner_bT26]
    apply mul_neg_of_pos_of_neg hdet
    have ev := fac_eval F 3 5
    rw [F.zero 3 5 (by decide), F.zero 3 0 (by decide)] at ev
    have f2 := F.neg 3 2 (by decide)
    have hf2 : 0 < (oblX0 x 5 - 1) * (-F.f 3 (x 2)) := mul_pos (by linarith) (by linarith)
    linarith
  · rw [inner_bT26]
    apply mul_neg_of_pos_of_neg hdet
    have ev := fac_eval F 4 5
    rw [F.zero 4 0 (by decide), F.zero 4 6 (by decide)] at ev
    have f5 := F.neg 4 5 (by decide)
    have f2 := F.neg 4 2 (by decide)
    have hf2 : 0 < (oblX0 x 5 - 1) * (-F.f 4 (x 2)) := mul_pos (by linarith) (by linarith)
    rw [F.zero 4 6 (by decide)]
    linarith

end Minimality.T24.A1
