module

public import Minimality.M4dType24
public import Minimality.M4cType24

@[expose] public section

/-!
# Type 24: A12 lemmas (`M4eType24`)

Formalizes the refereed A12 lemmas from `A12-REFEREE.md` §5:
1. `tie1_bound` (`E05-Tie1`): A1 tie closure U-bound at `z2(w05) = z5(w05) > z4(w05)`;
2. `lexAny_or_split_E3426` and `isRupert_of_E3426` (`E34-26`: A2, `a3 > a4`);
3. `nu346b`, `splitAny24_E3412`, and `isRupert_of_E3412` (`E34-12`: A2, `a3 ≤ a4`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.Gen Minimality.LexCell Minimality.H21 Minimality.H24.SAT
  Minimality.T24.SAT Minimality.T24.RCell Minimality.Split Minimality.T24.M4
  Minimality.T24.A7 Minimality.T24.A8

namespace Minimality.T24.A12

noncomputable def nu346b (x : Fin 7 → ℝ³) : ℝ :=
  oblX0 x 4 * (1 - oblX6 x 3) - oblX0 x 3 * (1 - oblX6 x 4)

/-! ### Helper: non-vanishing on a basis in `ℝ³` -/

private theorem basis_inner_ne_zero {u v w r : ℝ³}
    (hdet : det3 u v w ≠ 0) (hr : r ≠ 0)
    (hu : ⟪r, u⟫ = 0) (hv : ⟪r, v⟫ = 0) : ⟪r, w⟫ ≠ 0 := by
  intro hw
  have h0 : det3 u v w * r 0 = 0 := by
    have hu' : r 0 * u 0 + r 1 * u 1 + r 2 * u 2 = 0 := by
      simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
        mul_comm] using hu
    have hv' : r 0 * v 0 + r 1 * v 1 + r 2 * v 2 = 0 := by
      simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
        mul_comm] using hv
    have hw' : r 0 * w 0 + r 1 * w 1 + r 2 * w 2 = 0 := by
      simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
        mul_comm] using hw
    simp only [det3_expand]
    linear_combination (v 1 * w 2 - v 2 * w 1) * hu' + (w 1 * u 2 - w 2 * u 1) * hv' +
      (u 1 * v 2 - u 2 * v 1) * hw'
  have h1 : det3 u v w * r 1 = 0 := by
    have hu' : r 0 * u 0 + r 1 * u 1 + r 2 * u 2 = 0 := by
      simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
        mul_comm] using hu
    have hv' : r 0 * v 0 + r 1 * v 1 + r 2 * v 2 = 0 := by
      simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
        mul_comm] using hv
    have hw' : r 0 * w 0 + r 1 * w 1 + r 2 * w 2 = 0 := by
      simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
        mul_comm] using hw
    simp only [det3_expand]
    linear_combination (v 2 * w 0 - v 0 * w 2) * hu' + (w 2 * u 0 - w 0 * u 2) * hv' +
      (u 2 * v 0 - u 0 * v 2) * hw'
  have h2 : det3 u v w * r 2 = 0 := by
    have hu' : r 0 * u 0 + r 1 * u 1 + r 2 * u 2 = 0 := by
      simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
        mul_comm] using hu
    have hv' : r 0 * v 0 + r 1 * v 1 + r 2 * v 2 = 0 := by
      simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
        mul_comm] using hv
    have hw' : r 0 * w 0 + r 1 * w 1 + r 2 * w 2 = 0 := by
      simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
        mul_comm] using hw
    simp only [det3_expand]
    linear_combination (v 0 * w 1 - v 1 * w 0) * hu' + (w 0 * u 1 - w 1 * u 0) * hv' +
      (u 0 * v 1 - u 1 * v 0) * hw'
  have hr0 : r 0 = 0 := (mul_eq_zero.mp h0).resolve_left hdet
  have hr1 : r 1 = 0 := (mul_eq_zero.mp h1).resolve_left hdet
  have hr2 : r 2 = 0 := (mul_eq_zero.mp h2).resolve_left hdet
  apply hr; ext i; fin_cases i <;> assumption

/-! ### Part 1: `tie1_bound` (`E05-Tie1`) -/

private theorem tie1_tilt_exists {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha5 : 1 < oblX0 x 5) (ha4 : oblX0 x 4 < 1)
    (hpos : 0 < ⟪x 2 - x 5, x 4 - x 0⟫ ∨ 0 < ⟪x 2 - x 5, x 6 - x 2⟫) :
    ∃ lam1 lam2 : ℝ, 0 < lam1 ∧ 0 < lam2 ∧
      0 < ⟪x 2 - x 5, lam1 • (x 4 - x 0) + lam2 • (x 6 - x 2)⟫ ∧
      (⟪x 6 - x 5, x 5 - x 0⟫ = 0 →
        ⟪x 6 - x 5, lam1 • (x 4 - x 0) + lam2 • (x 6 - x 2)⟫ ≠ 0) := by
  have T := type24OfFac F
  let w05 := x 5 - x 0
  let w04 := x 4 - x 0
  let w26 := x 6 - x 2
  have hdet_w : det3 w05 w04 w26 = det24 x * (nC x - nB x) := by
    have hrep : ∀ v : Fin 7, x v - x 1 =
        oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1) := by
      intro v; rw [T.rep v]; abel
    have hw05 : w05 = (oblX0 x 5 - 1) • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) +
        oblX6 x 5 • (x 6 - x 1) := by
      dsimp [w05]; rw [show x 5 - x 0 = (x 5 - x 1) - (x 0 - x 1) by abel, hrep 5]; module
    have hw04 : w04 = (oblX0 x 4 - 1) • (x 0 - x 1) + oblX2 x 4 • (x 2 - x 1) +
        oblX6 x 4 • (x 6 - x 1) := by
      dsimp [w04]; rw [show x 4 - x 0 = (x 4 - x 1) - (x 0 - x 1) by abel, hrep 4]; module
    have hw26 : w26 = (0 : ℝ) • (x 0 - x 1) + (-1 : ℝ) • (x 2 - x 1) + (1 : ℝ) • (x 6 - x 1) := by
      dsimp [w26]; module
    conv_lhs => arg 1; rw [hw05]
    conv_lhs => arg 2; rw [hw04]
    conv_lhs => arg 3; rw [hw26]
    rw [M4.det3_frame x (oblX0 x 5 - 1) (oblX2 x 5) (oblX6 x 5)
      (oblX0 x 4 - 1) (oblX2 x 4) (oblX6 x 4) 0 (-1) 1]
    dsimp [nC, nB]; ring
  have hnc : 0 < nC x := nC_pos_of F ha4.le ha5
  have hnb : nB x < 0 := by
    have hc4 : 0 < oblX6 x 4 := T.X6_pos (v := 4) (by decide)
    have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
    dsimp [nB]; nlinarith
  have hdet_ne : det3 w05 w04 w26 ≠ 0 := by
    rw [hdet_w]; exact mul_ne_zero T.det_ne (by linarith)
  have h0_ex : ∃ l1 l2 : ℝ, 0 < l1 ∧ 0 < l2 ∧ 0 < ⟪x 2 - x 5, l1 • w04 + l2 • w26⟫ := by
    rcases hpos with h1 | h2
    · let a := ⟪x 2 - x 5, w04⟫
      let b := ⟪x 2 - x 5, w26⟫
      by_cases hb : 0 ≤ b
      · exact ⟨1, 1, zero_lt_one, zero_lt_one, by
          rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]; linarith⟩
      · push Not at hb
        refine ⟨1, a / (2 * (-b)), zero_lt_one, div_pos h1 (by linarith), ?_⟩
        rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
        have hcalc : 1 * a + (a / (2 * (-b))) * b = a / 2 := by field_simp [hb.ne]; ring
        dsimp [a, b] at hcalc ⊢; rw [hcalc]; linarith
    · let a := ⟪x 2 - x 5, w04⟫
      let b := ⟪x 2 - x 5, w26⟫
      by_cases ha : 0 ≤ a
      · exact ⟨1, 1, zero_lt_one, zero_lt_one, by
          rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]; linarith⟩
      · push Not at ha
        refine ⟨b / (2 * (-a)), 1, div_pos h2 (by linarith), zero_lt_one, ?_⟩
        rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
        have hcalc : (b / (2 * (-a))) * a + 1 * b = b / 2 := by field_simp [ha.ne]; ring
        dsimp [a, b] at hcalc ⊢; rw [hcalc]; linarith
  obtain ⟨l1, l2, hl1, hl2, hlpos⟩ := h0_ex
  by_cases hsub : ⟪x 6 - x 5, w05⟫ = 0
  · have h65_ne : x 6 - x 5 ≠ 0 := sub_ne_zero.mpr (T.inj.ne (by decide))
    by_cases hcur : ⟪x 6 - x 5, l1 • w04 + l2 • w26⟫ ≠ 0
    · exact ⟨l1, l2, hl1, hl2, hlpos, fun _ => hcur⟩
    · push Not at hcur
      have hnot_both : ⟪x 6 - x 5, w04⟫ ≠ 0 ∨ ⟪x 6 - x 5, w26⟫ ≠ 0 := by
        by_contra hboth; push Not at hboth
        exact basis_inner_ne_zero hdet_ne h65_ne hsub hboth.1 hboth.2
      have hcur' : l1 * ⟪x 6 - x 5, w04⟫ + l2 * ⟪x 6 - x 5, w26⟫ = 0 := by
        simpa only [inner_add_right, real_inner_smul_right] using hcur
      let v25 := ⟪x 2 - x 5, l1 • w04 + l2 • w26⟫
      rcases hnot_both with hw04_ne | hw26_ne
      · let d := if 0 ≤ ⟪x 2 - x 5, w04⟫ then 1 else v25 / (2 * (-⟪x 2 - x 5, w04⟫))
        have hd_pos : 0 < d := by
          dsimp [d]; split_ifs with h
          · exact zero_lt_one
          · exact div_pos hlpos (by linarith)
        refine ⟨l1 + d, l2, by linarith, hl2, ?_, fun _ => ?_⟩
        · simp only [add_smul, inner_add_right, real_inner_smul_right]
          dsimp [d] at hd_pos ⊢; split_ifs with h
          · have : 0 ≤ ⟪x 2 - x 5, w04⟫ := h
            have : v25 = l1 * ⟪x 2 - x 5, w04⟫ + l2 * ⟪x 2 - x 5, w26⟫ := by
              dsimp [v25]; simp only [inner_add_right, real_inner_smul_right]
            linarith
          · have ha_neg : ⟪x 2 - x 5, w04⟫ < 0 := lt_of_not_ge h
            have hcalc : v25 / (2 * (-⟪x 2 - x 5, w04⟫)) * ⟪x 2 - x 5, w04⟫ + v25 = v25 / 2 := by
              field_simp [ha_neg.ne]; ring
            have hv25 : v25 = l1 * ⟪x 2 - x 5, w04⟫ + l2 * ⟪x 2 - x 5, w26⟫ := by
              dsimp [v25]; simp only [inner_add_right, real_inner_smul_right]
            linarith
        · simp only [add_smul, inner_add_right, real_inner_smul_right]
          have : l1 * ⟪x 6 - x 5, w04⟫ + d * ⟪x 6 - x 5, w04⟫ + l2 * ⟪x 6 - x 5, w26⟫ =
              d * ⟪x 6 - x 5, w04⟫ := by linarith
          rw [this]
          exact mul_ne_zero hd_pos.ne' hw04_ne
      · let d := if 0 ≤ ⟪x 2 - x 5, w26⟫ then 1 else v25 / (2 * (-⟪x 2 - x 5, w26⟫))
        have hd_pos : 0 < d := by
          dsimp [d]; split_ifs with h
          · exact zero_lt_one
          · exact div_pos hlpos (by linarith)
        refine ⟨l1, l2 + d, hl1, by linarith, ?_, fun _ => ?_⟩
        · simp only [add_smul, inner_add_right, real_inner_smul_right]
          dsimp [d] at hd_pos ⊢; split_ifs with h
          · have : v25 = l1 * ⟪x 2 - x 5, w04⟫ + l2 * ⟪x 2 - x 5, w26⟫ := by
              dsimp [v25]; simp only [inner_add_right, real_inner_smul_right]
            linarith
          · have hb_neg : ⟪x 2 - x 5, w26⟫ < 0 := lt_of_not_ge h
            have hcalc : v25 + v25 / (2 * (-⟪x 2 - x 5, w26⟫)) * ⟪x 2 - x 5, w26⟫ = v25 / 2 := by
              field_simp [hb_neg.ne]; ring
            have hv25 : v25 = l1 * ⟪x 2 - x 5, w04⟫ + l2 * ⟪x 2 - x 5, w26⟫ := by
              dsimp [v25]; simp only [inner_add_right, real_inner_smul_right]
            linarith
        · simp only [add_smul, inner_add_right, real_inner_smul_right]
          have : l1 * ⟪x 6 - x 5, w04⟫ + (l2 * ⟪x 6 - x 5, w26⟫ + d * ⟪x 6 - x 5, w26⟫) =
              d * ⟪x 6 - x 5, w26⟫ := by linarith
          rw [this]
          exact mul_ne_zero hd_pos.ne' hw26_ne
  · exact ⟨l1, l2, hl1, hl2, hlpos, fun h => absurd h hsub⟩

private theorem robUniLex_five_twopeak_lex3 (z : ZMod 5 → ℝ × ℝ × ℝ)
    (h04 : (z 0).1 < (z 4).1) (h14 : (z 1).1 < (z 4).1)
    (h43 : LexLt3 (z 4) (z 3)) (h42 : LexLt3 (z 4) (z 2)) :
    RobUniLex z := by
  have h43_le : (z 4).1 ≤ (z 3).1 := by
    rcases h43 with h | ⟨h, _⟩ <;> linarith
  have h42_le : (z 4).1 ≤ (z 2).1 := by
    rcases h42 with h | ⟨h, _⟩ <;> linarith
  have h03 : LexLt3 (z 0) (z 3) := Or.inl (by linarith)
  have h02 : LexLt3 (z 0) (z 2) := Or.inl (by linarith)
  have h13 : LexLt3 (z 1) (z 3) := Or.inl (by linarith)
  have h12 : LexLt3 (z 1) (z 2) := Or.inl (by linarith)
  have h04' : LexLt3 (z 0) (z 4) := Or.inl (sub_pos.mpr h04)
  have h14' : LexLt3 (z 1) (z 4) := Or.inl (sub_pos.mpr h14)
  intro B b c d hb hbc hcd hd
  have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by revert B; decide
  have hbcd : (b = 1 ∧ c = 2 ∧ d = 3) ∨ (b = 1 ∧ c = 2 ∧ d = 4) ∨
      (b = 1 ∧ c = 3 ∧ d = 4) ∨ (b = 2 ∧ c = 3 ∧ d = 4) := by omega
  rcases hB with rfl | rfl | rfl | rfl | rfl <;>
    rcases hbcd with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    simp only [Nat.cast_one, Nat.cast_ofNat,
      show (0 : ZMod 5) + 1 = 1 from rfl, show (0 : ZMod 5) + 2 = 2 from rfl,
      show (0 : ZMod 5) + 3 = 3 from rfl, show (0 : ZMod 5) + 4 = 4 from rfl,
      show (1 : ZMod 5) + 1 = 2 from rfl, show (1 : ZMod 5) + 2 = 3 from rfl,
      show (1 : ZMod 5) + 3 = 4 from rfl, show (1 : ZMod 5) + 4 = 0 from rfl,
      show (2 : ZMod 5) + 1 = 3 from rfl, show (2 : ZMod 5) + 2 = 4 from rfl,
      show (2 : ZMod 5) + 3 = 0 from rfl, show (2 : ZMod 5) + 4 = 1 from rfl,
      show (3 : ZMod 5) + 1 = 4 from rfl, show (3 : ZMod 5) + 2 = 0 from rfl,
      show (3 : ZMod 5) + 3 = 1 from rfl, show (3 : ZMod 5) + 4 = 2 from rfl,
      show (4 : ZMod 5) + 1 = 0 from rfl, show (4 : ZMod 5) + 2 = 1 from rfl,
      show (4 : ZMod 5) + 3 = 2 from rfl, show (4 : ZMod 5) + 4 = 3 from rfl]
  all_goals first
    | exact Or.inl h02 | exact Or.inl h12 | exact Or.inl h13
    | exact Or.inr (Or.inl h03) | exact Or.inr (Or.inl h04')
    | exact Or.inr (Or.inl h14') | exact Or.inr (Or.inl h43)
    | exact Or.inr (Or.inr (Or.inl h03))
    | exact Or.inr (Or.inr (Or.inl h04')) | exact Or.inr (Or.inr (Or.inl h42))
    | exact Or.inr (Or.inr (Or.inl h43))
    | exact Or.inr (Or.inr (Or.inr h12))

theorem tie1_bound {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (ha5 : 1 < oblX0 x 5) (ha4 : oblX0 x 4 < 1)
    (hL : 0 ≤ Lam5 x) (h346 : F.f 8 (x 0) ≤ F.f 8 (x 5))
    (hU : ¬ Gen.LexAny F) (hS : ¬ SplitAny24 F)
    (htie : ⟪x 2 - x 1, x 5 - x 0⟫ = ⟪x 5 - x 1, x 5 - x 0⟫)
    (h45 : ⟪x 4 - x 1, x 5 - x 0⟫ < ⟪x 5 - x 1, x 5 - x 0⟫) :
    ⟪x 2 - x 5, x 4 - x 0⟫ ≤ 0 ∧ ⟪x 2 - x 5, x 6 - x 2⟫ ≤ 0 := by
  by_contra hneg
  have hpos : 0 < ⟪x 2 - x 5, x 4 - x 0⟫ ∨ 0 < ⟪x 2 - x 5, x 6 - x 2⟫ := by
    by_contra hno; push Not at hno; exact hneg hno
  obtain ⟨lam1, lam2, hlam1, hlam2, hd1_25, hsub⟩ := tie1_tilt_exists F ha5 ha4 hpos
  have T := type24OfFac F
  have hc4 : 0 < oblX6 x 4 := T.X6_pos (v := 4) (by decide)
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hnc : 0 < nC x := nC_pos_of F ha4.le ha5
  have hnb : nB x < 0 := by dsimp [nB]; nlinarith
  have hR46 : R46 x < 0 := R46_neg F ha5 hL
  have hR04 : R04 x < 0 := R04_neg F ha4.le ha5
  let w05 : ℝ³ := x 5 - x 0
  let d1 : ℝ³ := lam1 • (x 4 - x 0) + lam2 • (x 6 - x 2)
  let d2 : ℝ³ := x 6 - x 1
  let c : ZMod 5 → Fin 7 := ![0, 4, 6, 2, 5]
  let pat : Fin 9 → Bool := fun t => decide (t = 3 ∨ t = 6 ∨ t = 7 ∨ t = 8)
  have hc_inj : Function.Injective c := by
    intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)
  have hcyc_ok : S0xCycOK s0x_S24 c pat := by unfold S0xCycOK; decide
  have hf0 : ⟪F.N 0, w05⟫ < 0 := by
    dsimp [w05]; rw [← F.hN 0 (x 5) (x 0), F.zero 0 0 (by decide), sub_zero]
    exact F.neg 0 5 (by decide)
  have hf1 : ⟪F.N 1, w05⟫ < 0 := by
    dsimp [w05]; rw [← F.hN 1 (x 5) (x 0), F.zero 1 0 (by decide), sub_zero]
    exact F.neg 1 5 (by decide)
  have hf2_0 : ⟪F.N 2, w05⟫ = 0 := by
    dsimp [w05]; rw [← F.hN 2 (x 5) (x 0), F.zero 2 5 (by decide), F.zero 2 0 (by decide), sub_self]
  have hd2_1 : 0 < -⟪F.N 2, d1⟫ := by
    dsimp [d1]; rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    have h24 : ⟪F.N 2, x 4 - x 0⟫ < 0 := by
      rw [← F.hN 2 (x 4) (x 0), F.zero 2 0 (by decide), sub_zero]; exact F.neg 2 4 (by decide)
    have h26 : ⟪F.N 2, x 6 - x 2⟫ < 0 := by
      rw [← F.hN 2 (x 6) (x 2), F.zero 2 2 (by decide), sub_zero]; exact F.neg 2 6 (by decide)
    have h_pos : 0 < -(lam1 * ⟪F.N 2, x 4 - x 0⟫ + lam2 * ⟪F.N 2, x 6 - x 2⟫) := by
      nlinarith
    exact h_pos
  have hf3_0 : ⟪F.N 3, w05⟫ = 0 := by
    dsimp [w05]; rw [← F.hN 3 (x 5) (x 0), F.zero 3 5 (by decide), F.zero 3 0 (by decide), sub_self]
  have hd3_1 : 0 < ⟪F.N 3, d1⟫ := by
    dsimp [d1]; rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    have h34 : ⟪F.N 3, x 4 - x 0⟫ = 0 := by
      rw [← F.hN 3 (x 4) (x 0), F.zero 3 4 (by decide), F.zero 3 0 (by decide), sub_self]
    have h36 : 0 < ⟪F.N 3, x 6 - x 2⟫ := by
      rw [← F.hN 3 (x 6) (x 2)]
      have h16 : F.f 3 (x 1) < F.f 3 (x 6) := (nC_pos_iff F).mp hnc
      have h21 : F.f 3 (x 2) < F.f 3 (x 1) := by
        have hnb' : F.f 3 (x 2) < F.f 3 (x 1) := by
          have := (nB_pos_iff F).not.mp (not_lt.mpr hnb.le)
          -- use `fac_eval F 3 4` and `fac_eval F 3 5` directly:
          have ev34 := fac_eval F 3 4
          have ev35 := fac_eval F 3 5
          rw [F.zero 3 4 (by decide), F.zero 3 0 (by decide)] at ev34
          rw [F.zero 3 5 (by decide), F.zero 3 0 (by decide)] at ev35
          have hid : nC x * (F.f 3 (x 2) - F.f 3 (x 1)) = nB x * (F.f 3 (x 6) - F.f 3 (x 1)) := by
            dsimp [nC, nB]
            linear_combination (1 - oblX0 x 5) * ev34 - (1 - oblX0 x 4) * ev35
          have hpos_rhs : nB x * (F.f 3 (x 6) - F.f 3 (x 1)) < 0 :=
            mul_neg_of_neg_of_pos hnb (sub_pos.mpr h16)
          have hneg_lhs : F.f 3 (x 2) - F.f 3 (x 1) < 0 := by
            nlinarith
          linarith
        exact hnb'
      linarith
    rw [h34, mul_zero, zero_add]
    exact mul_pos hlam2 h36
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
    rcases eq_or_lt_of_le hL with hL0 | hLpos
    · have hd7_1 : 0 < ⟪F.N 7, d1⟫ := by
        dsimp [d1]; rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
        have h7_26 : ⟪F.N 7, x 6 - x 2⟫ = 0 := by
          rw [← F.hN 7 (x 6) (x 2), F.zero 7 6 (by decide), F.zero 7 2 (by decide), sub_self]
        have h7_04 : ⟪F.N 7, x 4 - x 0⟫ =
            (-F.f 7 (x 1)) * (oblX2 x 4 + oblX6 x 4 - omega3 x * (oblX0 x 4 - 1)) := by
          rw [← F.hN 7 (x 4) (x 0)]
          have ev7_4 := fac_eval F 7 4
          rw [F.zero 7 2 (by decide), F.zero 7 6 (by decide), hf7_0] at ev7_4
          rw [ev7_4, hf7_0]; ring
        have hR04_lam : (oblX0 x 5 - 1) * (oblX2 x 4 + oblX6 x 4 - omega3 x * (oblX0 x 4 - 1)) =
            -R04 x + (oblX0 x 4 - 1) * Lam5 x := by
          dsimp [R04, Lam5]; ring
        have hfac_pos : 0 < oblX2 x 4 + oblX6 x 4 - omega3 x * (oblX0 x 4 - 1) := by
          have hprod : 0 < (oblX0 x 5 - 1) * (oblX2 x 4 + oblX6 x 4 - omega3 x * (oblX0 x 4 - 1)) := by
            rw [hR04_lam, ← hL0]; linarith
          exact pos_of_mul_pos_right hprod (sub_pos.mpr ha5).le
        rw [h7_26, mul_zero, add_zero, h7_04]
        exact mul_pos hlam1 (mul_pos (by linarith [F.neg 7 1 (by decide)]) hfac_pos)
      exact Or.inr ⟨by rw [hw7, ← hL0, mul_zero], Or.inl hd7_1⟩
    · exact Or.inl (by rw [hw7]; exact mul_pos (by linarith [F.neg 7 1 (by decide)]) hLpos)
  have hf8_lex : LexPos3 ⟪F.N 8, w05⟫ ⟪F.N 8, d1⟫ ⟪F.N 8, d2⟫ := by
    have hw8 : ⟪F.N 8, w05⟫ = F.f 8 (x 5) - F.f 8 (x 0) := by
      dsimp [w05]; rw [← F.hN 8 (x 5) (x 0)]
    have hd8_1 : 0 < ⟪F.N 8, d1⟫ := by
      dsimp [d1]; rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      have h8_04 : 0 < ⟪F.N 8, x 4 - x 0⟫ := by
        rw [← F.hN 8 (x 4) (x 0), F.zero 8 4 (by decide), zero_sub]
        linarith [F.neg 8 0 (by decide)]
      have h8_26 : 0 < ⟪F.N 8, x 6 - x 2⟫ := by
        rw [← F.hN 8 (x 6) (x 2), F.zero 8 6 (by decide), zero_sub]
        linarith [F.neg 8 2 (by decide)]
      nlinarith
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
  -- Row determinants at `w05` and `d1`:
  have hrep : ∀ v : Fin 7, x v - x 1 =
      oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1) := by
    intro v; rw [T.rep v]; abel
  have h26 : x 2 - x 6 = (0 : ℝ) • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) + (-1 : ℝ) • (x 6 - x 1) := by
    module
  have h05 : x 0 - x 5 = (1 - oblX0 x 5) • (x 0 - x 1) + (-oblX2 x 5) • (x 2 - x 1) +
      (-oblX6 x 5) • (x 6 - x 1) := by
    rw [show x 0 - x 5 = (x 0 - x 1) - (x 5 - x 1) by abel, hrep 5]; module
  have h04 : x 4 - x 0 = (oblX0 x 4 - 1) • (x 0 - x 1) + oblX2 x 4 • (x 2 - x 1) +
      oblX6 x 4 • (x 6 - x 1) := by
    rw [show x 4 - x 0 = (x 4 - x 1) - (x 0 - x 1) by abel, hrep 4]; module
  have hw26 : x 6 - x 2 = (0 : ℝ) • (x 0 - x 1) + (-1 : ℝ) • (x 2 - x 1) + (1 : ℝ) • (x 6 - x 1) := by
    module
  have h05_d1 : det3 (x 0 - x 5) (x 2 - x 6) d1 =
      -(lam1 * det24 x * ((oblX2 x 5 + oblX6 x 5) * (1 - oblX0 x 4) +
        (oblX0 x 5 - 1) * (oblX2 x 4 + oblX6 x 4))) := by
    have hd1_eq : d1 =
        (lam1 * (oblX0 x 4 - 1)) • (x 0 - x 1) +
        (lam1 * oblX2 x 4 - lam2) • (x 2 - x 1) +
        (lam1 * oblX6 x 4 + lam2) • (x 6 - x 1) := by
      dsimp [d1]; rw [h04, hw26]; module
    conv_lhs => arg 1; rw [h05]
    conv_lhs => arg 2; rw [h26]
    conv_lhs => arg 3; rw [hd1_eq]
    rw [M4.det3_frame x (1 - oblX0 x 5) (-oblX2 x 5) (-oblX6 x 5) 0 1 (-1)
      (lam1 * (oblX0 x 4 - 1)) (lam1 * oblX2 x 4 - lam2) (lam1 * oblX6 x 4 + lam2)]
    ring
  have hrows := rows_P5 F
  have h05_w : det3 (x 0 - x 5) (x 2 - x 6) w05 = 0 := by
    have hw : w05 = (oblX0 x 5 - 1) • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) +
        oblX6 x 5 • (x 6 - x 1) := by
      dsimp [w05]; rw [show x 5 - x 0 = (x 5 - x 1) - (x 0 - x 1) by abel, hrep 5]; module
    conv_lhs => arg 1; rw [h05]
    conv_lhs => arg 2; rw [h26]
    conv_lhs => arg 3; rw [hw]
    rw [M4.det3_frame x (1 - oblX0 x 5) (-oblX2 x 5) (-oblX6 x 5) 0 1 (-1)
      (oblX0 x 5 - 1) (oblX2 x 5) (oblX6 x 5)]
    ring
  have h52_pos : 0 < oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1 := by linarith
  have h05_cpos : 0 < lam1 * ((oblX2 x 5 + oblX6 x 5) * (1 - oblX0 x 4) +
      (oblX0 x 5 - 1) * (oblX2 x 4 + oblX6 x 4)) := by
    have h1 : 0 < (oblX2 x 5 + oblX6 x 5) * (1 - oblX0 x 4) :=
      mul_pos (by linarith) (sub_pos.mpr ha4)
    have h2 : 0 < (oblX0 x 5 - 1) * (oblX2 x 4 + oblX6 x 4) :=
      mul_pos (sub_pos.mpr ha5) (by linarith)
    exact mul_pos hlam1 (by linarith)
  -- Depths at `(w05, d1, d2)`:
  have hz25_lex : LexPos3 (⟪x 2, w05⟫ - ⟪x 5, w05⟫) (⟪x 2, d1⟫ - ⟪x 5, d1⟫)
      (⟪x 2, d2⟫ - ⟪x 5, d2⟫) := by
    have h0 : ⟪x 2, w05⟫ - ⟪x 5, w05⟫ = 0 := by
      have h1 : ⟪x 2 - x 1, w05⟫ = ⟪x 5 - x 1, w05⟫ := htie
      rw [inner_sub_left, inner_sub_left] at h1
      linarith
    have h1 : 0 < ⟪x 2, d1⟫ - ⟪x 5, d1⟫ := by
      rw [← inner_sub_left]; exact hd1_25
    exact Or.inr ⟨h0, Or.inl h1⟩
  have hz45 : ⟪x 4, w05⟫ < ⟪x 5, w05⟫ := by
    have h1 := h45
    rw [inner_sub_left, inner_sub_left] at h1
    linarith
  have hz05 : ⟪x 0, w05⟫ < ⟪x 5, w05⟫ := by
    refine sub_lt_zero.mp ?_
    have h_eq : ⟪x 0, w05⟫ - ⟪x 5, w05⟫ = -⟪w05, w05⟫ := by
      dsimp [w05]; rw [← inner_sub_left, ← neg_sub, inner_neg_left]
    have hw_ne : w05 ≠ 0 := sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide)
    rw [h_eq]; exact neg_neg_of_pos (real_inner_self_pos.mpr hw_ne)
  have hd2_sq : 0 < det24 x * det24 x := mul_self_pos.mpr T.det_ne
  -- Case split on `⟪x 6 - x 5, (w05, d1)⟫`:
  by_cases hz65_0 : ⟪x 6 - x 5, w05⟫ = 0
  · have hz65_1_ne : ⟪x 6 - x 5, d1⟫ ≠ 0 := hsub hz65_0
    rcases lt_or_gt_of_ne hz65_1_ne with hz65_neg | hz65_pos
    · -- `z6 <lex z5` -> `SplitAny24 F`, contradicting `hS`:
      apply hS
      refine splitAny24_of_lex3' F (by decide) c hc_inj pat hcyc_ok w05 d1 d2 hfac_lex 2 4
        (by decide) (by decide) (det24 x) ?_
      intro i hia j hj hjc
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by decide +revert
      have hc0 : c 0 = 0 := rfl; have hc1 : c 1 = 4 := rfl; have hc2 : c 2 = 6 := rfl
      have hc3 : c 3 = 2 := rfl; have hc4 : c 4 = 5 := rfl
      have he0 : (0 : ZMod 5) + 1 = 1 := rfl; have he1 : (1 : ZMod 5) + 1 = 2 := rfl
      have he2 : (2 : ZMod 5) + 1 = 3 := rfl; have he3 : (3 : ZMod 5) + 1 = 4 := rfl
      have he4 : (4 : ZMod 5) + 1 = 0 := rfl
      rcases hi with rfl | rfl | rfl | rfl | rfl
      · rcases hj with rfl | rfl
        · refine ⟨-1, Or.inl (by rw [hc0, hc4, inner_sub_left]; linarith [hz05]), Or.inl ?_⟩
          rw [he0, he2, hc0, hc1, hc2, hc3, hrows.1]
          have h1 : det24 x * -1 * (det24 x * R04 x) = (det24 x * det24 x) * (-R04 x) := by ring
          rw [h1]; exact mul_pos hd2_sq (neg_pos.mpr hR04)
        · refine ⟨-1, Or.inl (by rw [he0, hc1, hc4, inner_sub_left]; linarith [hz45]), Or.inl ?_⟩
          rw [he0, he2, hc0, hc1, hc2, hc3, hrows.1]
          have h1 : det24 x * -1 * (det24 x * R04 x) = (det24 x * det24 x) * (-R04 x) := by ring
          rw [h1]; exact mul_pos hd2_sq (neg_pos.mpr hR04)
      · rcases hj with rfl | rfl
        · refine ⟨-1, Or.inl (by rw [hc1, hc4, inner_sub_left]; linarith [hz45]), Or.inl ?_⟩
          rw [he1, he2, hc1, hc2, hc3, hrows.2.1]
          have h1 : det24 x * -1 * (det24 x * R46 x) = (det24 x * det24 x) * (-R46 x) := by ring
          rw [h1]; exact mul_pos hd2_sq (neg_pos.mpr hR46)
        · refine ⟨-1, (by rw [he1, hc2, hc4]; simp only [neg_one_mul]; exact Or.inr ⟨by rw [neg_eq_zero]; exact hz65_0, Or.inl (neg_pos.mpr hz65_neg)⟩), Or.inl ?_⟩
          rw [he1, he2, hc1, hc2, hc3, hrows.2.1]
          have h1 : det24 x * -1 * (det24 x * R46 x) = (det24 x * det24 x) * (-R46 x) := by ring
          rw [h1]; exact mul_pos hd2_sq (neg_pos.mpr hR46)
      · exact absurd rfl hia
      · rcases hj with rfl | rfl
        · refine ⟨1, ?_, Or.inl ?_⟩
          · rw [hc3, hc4]
            simpa only [one_mul, inner_sub_left] using hz25_lex
          · rw [he3, he2, hc3, hc4, hc2, hrows.2.2.1]
            have h1 : det24 x * 1 * (det24 x * (oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1)) =
                (det24 x * det24 x) * (oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1) := by ring
            rw [h1]; exact mul_pos hd2_sq h52_pos
        · exact absurd he3 hjc
      · rcases hj with rfl | rfl
        · exact absurd rfl hjc
        · refine ⟨-1, Or.inl (by rw [he4, hc0, hc4, inner_sub_left]; linarith [hz05]),
            Or.inr ⟨by rw [he4, he2, hc4, hc0, hc2, hc3, h05_w, mul_zero], Or.inl ?_⟩⟩
          rw [he4, he2, hc4, hc0, hc2, hc3, h05_d1]
          have h1 : det24 x * -1 * -(lam1 * det24 x * ((oblX2 x 5 + oblX6 x 5) * (1 - oblX0 x 4) +
              (oblX0 x 5 - 1) * (oblX2 x 4 + oblX6 x 4))) =
              (det24 x * det24 x) * (lam1 * ((oblX2 x 5 + oblX6 x 5) * (1 - oblX0 x 4) +
              (oblX0 x 5 - 1) * (oblX2 x 4 + oblX6 x 4))) := by ring
          rw [h1]; exact mul_pos hd2_sq h05_cpos
    · -- `z5 <lex z6` -> `LexAny F`, contradicting `hU`:
      apply hU
      have h65_lex : LexPos3 (⟪x 6, w05⟫ - ⟪x 5, w05⟫) (⟪x 6, d1⟫ - ⟪x 5, d1⟫)
          (⟪x 6, d2⟫ - ⟪x 5, d2⟫) := by
        rw [← inner_sub_left, ← inner_sub_left]
        exact Or.inr ⟨hz65_0, Or.inl hz65_pos⟩
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
      · refine robUniLex_five_twopeak_lex3 _ ?_ ?_ ?_ h65_lex
        · change ⟪x (c 0), w05⟫ < ⟪x (c 4), w05⟫; simp [c]; exact hz05
        · change ⟪x (c 1), w05⟫ < ⟪x (c 4), w05⟫; simp [c]; exact hz45
        · change LexLt3 (⟪x (c 4), w05⟫, ⟪x (c 4), d1⟫, ⟪x (c 4), d2⟫)
            (⟪x (c 3), w05⟫, ⟪x (c 3), d1⟫, ⟪x (c 3), d2⟫)
          simp [c]; exact hz25_lex
  · rcases lt_or_gt_of_ne hz65_0 with hz65_neg | hz65_pos
    · apply hS
      refine splitAny24_of_lex3' F (by decide) c hc_inj pat hcyc_ok w05 d1 d2 hfac_lex 2 4
        (by decide) (by decide) (det24 x) ?_
      intro i hia j hj hjc
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by decide +revert
      have hc0 : c 0 = 0 := rfl; have hc1 : c 1 = 4 := rfl; have hc2 : c 2 = 6 := rfl
      have hc3 : c 3 = 2 := rfl; have hc4 : c 4 = 5 := rfl
      have he0 : (0 : ZMod 5) + 1 = 1 := rfl; have he1 : (1 : ZMod 5) + 1 = 2 := rfl
      have he2 : (2 : ZMod 5) + 1 = 3 := rfl; have he3 : (3 : ZMod 5) + 1 = 4 := rfl
      have he4 : (4 : ZMod 5) + 1 = 0 := rfl
      rcases hi with rfl | rfl | rfl | rfl | rfl
      · rcases hj with rfl | rfl
        · refine ⟨-1, Or.inl (by rw [hc0, hc4, inner_sub_left]; linarith [hz05]), Or.inl ?_⟩
          rw [he0, he2, hc0, hc1, hc2, hc3, hrows.1]
          have h1 : det24 x * -1 * (det24 x * R04 x) = (det24 x * det24 x) * (-R04 x) := by ring
          rw [h1]; exact mul_pos hd2_sq (neg_pos.mpr hR04)
        · refine ⟨-1, Or.inl (by rw [he0, hc1, hc4, inner_sub_left]; linarith [hz45]), Or.inl ?_⟩
          rw [he0, he2, hc0, hc1, hc2, hc3, hrows.1]
          have h1 : det24 x * -1 * (det24 x * R04 x) = (det24 x * det24 x) * (-R04 x) := by ring
          rw [h1]; exact mul_pos hd2_sq (neg_pos.mpr hR04)
      · rcases hj with rfl | rfl
        · refine ⟨-1, Or.inl (by rw [hc1, hc4, inner_sub_left]; linarith [hz45]), Or.inl ?_⟩
          rw [he1, he2, hc1, hc2, hc3, hrows.2.1]
          have h1 : det24 x * -1 * (det24 x * R46 x) = (det24 x * det24 x) * (-R46 x) := by ring
          rw [h1]; exact mul_pos hd2_sq (neg_pos.mpr hR46)
        · refine ⟨-1, Or.inl (by rw [he1, hc2, hc4, neg_one_mul]; exact neg_pos.mpr hz65_neg), Or.inl ?_⟩
          rw [he1, he2, hc1, hc2, hc3, hrows.2.1]
          have h1 : det24 x * -1 * (det24 x * R46 x) = (det24 x * det24 x) * (-R46 x) := by ring
          rw [h1]; exact mul_pos hd2_sq (neg_pos.mpr hR46)
      · exact absurd rfl hia
      · rcases hj with rfl | rfl
        · refine ⟨1, ?_, Or.inl ?_⟩
          · rw [hc3, hc4]
            simpa only [one_mul, inner_sub_left] using hz25_lex
          · rw [he3, he2, hc3, hc4, hc2, hrows.2.2.1]
            have h1 : det24 x * 1 * (det24 x * (oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1)) =
                (det24 x * det24 x) * (oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1) := by ring
            rw [h1]; exact mul_pos hd2_sq h52_pos
        · exact absurd he3 hjc
      · rcases hj with rfl | rfl
        · exact absurd rfl hjc
        · refine ⟨-1, Or.inl (by rw [he4, hc0, hc4, inner_sub_left]; linarith [hz05]),
            Or.inr ⟨by rw [he4, he2, hc4, hc0, hc2, hc3, h05_w, mul_zero], Or.inl ?_⟩⟩
          rw [he4, he2, hc4, hc0, hc2, hc3, h05_d1]
          have h1 : det24 x * -1 * -(lam1 * det24 x * ((oblX2 x 5 + oblX6 x 5) * (1 - oblX0 x 4) +
              (oblX0 x 5 - 1) * (oblX2 x 4 + oblX6 x 4))) =
              (det24 x * det24 x) * (lam1 * ((oblX2 x 5 + oblX6 x 5) * (1 - oblX0 x 4) +
              (oblX0 x 5 - 1) * (oblX2 x 4 + oblX6 x 4))) := by ring
          rw [h1]; exact mul_pos hd2_sq h05_cpos
    · apply hU
      have h65_lex : LexPos3 (⟪x 6, w05⟫ - ⟪x 5, w05⟫) (⟪x 6, d1⟫ - ⟪x 5, d1⟫)
          (⟪x 6, d2⟫ - ⟪x 5, d2⟫) := by
        rw [← inner_sub_left]; exact Or.inl hz65_pos
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
      · refine robUniLex_five_twopeak_lex3 _ ?_ ?_ ?_ h65_lex
        · change ⟪x (c 0), w05⟫ < ⟪x (c 4), w05⟫; simp [c]; exact hz05
        · change ⟪x (c 1), w05⟫ < ⟪x (c 4), w05⟫; simp [c]; exact hz45
        · change LexLt3 (⟪x (c 4), w05⟫, ⟪x (c 4), d1⟫, ⟪x (c 4), d2⟫)
            (⟪x (c 3), w05⟫, ⟪x (c 3), d1⟫, ⟪x (c 3), d2⟫)
          simp [c]; exact hz25_lex

/-! ### Part 2: `lexAny_or_split_E3426` and `isRupert_of_E3426` (`E34-26`) -/

theorem lexAny_or_split_E3426 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (ha5 : 1 < oblX0 x 5) (ha4 : oblX0 x 4 < 1)
    (hsig : F.f 8 (x 5) < F.f 8 (x 0))
    (ha : oblX0 x 4 < oblX0 x 3) (hb : oblX2 x 4 < oblX2 x 3) (hc : oblX6 x 4 < oblX6 x 3)
    (hz : max ⟪x 0 - x 1, x 3 - x 4⟫ ⟪x 4 - x 1, x 3 - x 4⟫ < ⟪x 5 - x 1, x 3 - x 4⟫ ∧
          ⟪x 5 - x 1, x 3 - x 4⟫ < ⟪x 2 - x 1, x 3 - x 4⟫) :
    Gen.LexAny F ∨ SplitAny24 F := by
  let _ := hC
  have T := type24OfFac F
  have hc4 : 0 < oblX6 x 4 := T.X6_pos (v := 4) (by decide)
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hnc : F.f 3 (x 1) < F.f 3 (x 6) := (nC_pos_iff F).mp (nC_pos_of F ha4.le ha5)
  have hR04 : R04 x < 0 := R04_neg F ha4.le ha5
  obtain ⟨s, t, hs, ht, hdec, hda, hdb, hdc⟩ := lemmaM_coords F
  have hs1 : 1 < s := by
    have ev8 := congrArg (fun v => ⟪F.N 8, v⟫) hdec
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
      ← F.hN 8 (x 3) (x 0), ← F.hN 8 (x 4) (x 0), ← F.hN 8 (x 5) (x 0),
      F.zero 8 3 (by decide), F.zero 8 4 (by decide), zero_sub] at ev8
    have hmul : (s - 1) * (-F.f 8 (x 0)) = t * (F.f 8 (x 0) - F.f 8 (x 5)) := by linarith
    have hpos_rhs : 0 < t * (F.f 8 (x 0) - F.f 8 (x 5)) := mul_pos ht (sub_pos.mpr hsig)
    have h80 : 0 < -F.f 8 (x 0) := neg_pos.mpr (F.neg 8 0 (by decide))
    have hs1' : 0 < s - 1 := pos_of_mul_pos_left (by linarith) h80.le
    linarith
  have hw43_dec : x 3 - x 4 = (s - 1) • (x 4 - x 0) + t • (x 5 - x 0) := by
    calc x 3 - x 4 = (x 3 - x 0) - (x 4 - x 0) := by abel
      _ = (s • (x 4 - x 0) + t • (x 5 - x 0)) - (x 4 - x 0) := by rw [hdec]
      _ = (s - 1) • (x 4 - x 0) + t • (x 5 - x 0) := by module
  let w43 : ℝ³ := x 3 - x 4
  let d1 : ℝ³ := x 6 - x 1
  let d2 : ℝ³ := x 6 - x 5
  let c : ZMod 5 → Fin 7 := ![0, 4, 6, 2, 5]
  let pat : Fin 9 → Bool := fun t => decide (t = 3 ∨ t = 6 ∨ t = 7 ∨ t = 8)
  have hc_inj : Function.Injective c := by
    intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)
  have hcyc_ok : S0xCycOK s0x_S24 c pat := by unfold S0xCycOK; decide
  have hf0 : ⟪F.N 0, w43⟫ < 0 := by
    dsimp [w43]; rw [← F.hN 0 (x 3) (x 4)]
    have ev3 := fac_eval F 0 3; have ev4 := fac_eval F 0 4
    rw [F.zero 0 0 (by decide), F.zero 0 1 (by decide), F.zero 0 2 (by decide)] at ev3 ev4
    have hmul : F.f 0 (x 3) - F.f 0 (x 4) = (oblX6 x 3 - oblX6 x 4) * F.f 0 (x 6) := by
      rw [ev3, ev4]; ring
    rw [hmul]
    exact mul_neg_of_pos_of_neg (sub_pos.mpr hc) (F.neg 0 6 (by decide))
  have hf1 : ⟪F.N 1, w43⟫ < 0 := by
    dsimp [w43]; rw [← F.hN 1 (x 3) (x 4)]
    have ev3 := fac_eval F 1 3; have ev4 := fac_eval F 1 4
    rw [F.zero 1 0 (by decide), F.zero 1 1 (by decide), F.zero 1 6 (by decide)] at ev3 ev4
    have hmul : F.f 1 (x 3) - F.f 1 (x 4) = (oblX2 x 3 - oblX2 x 4) * F.f 1 (x 2) := by
      rw [ev3, ev4]; ring
    rw [hmul]
    exact mul_neg_of_pos_of_neg (sub_pos.mpr hb) (F.neg 1 2 (by decide))
  have hf2 : ⟪F.N 2, w43⟫ < 0 := by
    dsimp [w43]; rw [hw43_dec, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      ← F.hN 2 (x 4) (x 0), ← F.hN 2 (x 5) (x 0), F.zero 2 0 (by decide), F.zero 2 5 (by decide),
      sub_self, sub_zero, mul_zero, add_zero]
    exact mul_neg_of_pos_of_neg (sub_pos.mpr hs1) (F.neg 2 4 (by decide))
  have hf3_0 : ⟪F.N 3, w43⟫ = 0 := by
    dsimp [w43]; rw [← F.hN 3 (x 3) (x 4), F.zero 3 3 (by decide), F.zero 3 4 (by decide), sub_self]
  have hd3_1 : 0 < ⟪F.N 3, d1⟫ := by
    dsimp [d1]; rw [← F.hN 3 (x 6) (x 1)]; exact sub_pos.mpr hnc
  have hf4 : ⟪F.N 4, w43⟫ < 0 := by
    dsimp [w43]; rw [hw43_dec, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      ← F.hN 4 (x 4) (x 0), ← F.hN 4 (x 5) (x 0), F.zero 4 0 (by decide), F.zero 4 4 (by decide),
      sub_self, sub_zero, mul_zero, zero_add]
    exact mul_neg_of_pos_of_neg ht (F.neg 4 5 (by decide))
  have hf5 : ⟪F.N 5, w43⟫ < 0 := by
    dsimp [w43]; rw [← F.hN 5 (x 3) (x 4)]
    have ev3 := fac_eval F 5 3; have ev4 := fac_eval F 5 4
    rw [F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)] at ev3 ev4
    have hmul : F.f 5 (x 3) - F.f 5 (x 4) = (oblX0 x 3 - oblX0 x 4) * F.f 5 (x 0) := by
      rw [ev3, ev4]; ring
    rw [hmul]
    exact mul_neg_of_pos_of_neg (sub_pos.mpr ha) (F.neg 5 0 (by decide))
  have hf6 : 0 < ⟪F.N 6, w43⟫ := by
    dsimp [w43]; rw [← F.hN 6 (x 3) (x 4), F.zero 6 3 (by decide), zero_sub]
    exact neg_pos.mpr (F.neg 6 4 (by decide))
  have hf7 : 0 < ⟪F.N 7, w43⟫ := by
    dsimp [w43]; rw [← F.hN 7 (x 3) (x 4), F.zero 7 3 (by decide), zero_sub]
    exact neg_pos.mpr (F.neg 7 4 (by decide))
  have hf8_0 : ⟪F.N 8, w43⟫ = 0 := by
    dsimp [w43]; rw [← F.hN 8 (x 3) (x 4), F.zero 8 3 (by decide), F.zero 8 4 (by decide), sub_self]
  have hd8_1 : 0 < ⟪F.N 8, d1⟫ := by
    dsimp [d1]; rw [← F.hN 8 (x 6) (x 1), F.zero 8 6 (by decide), zero_sub]
    exact neg_pos.mpr (F.neg 8 1 (by decide))
  have hfac_lex : ∀ t : Fin 9,
      LexPos3 (if pat t then ⟪F.N t, w43⟫ else -⟪F.N t, w43⟫)
              (if pat t then ⟪F.N t, d1⟫ else -⟪F.N t, d1⟫)
              (if pat t then ⟪F.N t, d2⟫ else -⟪F.N t, d2⟫) := by
    intro t; fin_cases t <;> simp [pat]
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨hf3_0, Or.inl hd3_1⟩
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inl hf6
    · exact Or.inl hf7
    · exact Or.inr ⟨hf8_0, Or.inl hd8_1⟩
  have hrep : ∀ v : Fin 7, x v - x 1 =
      oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1) := by
    intro v; rw [T.rep v]; abel
  have h26 : x 2 - x 6 = (0 : ℝ) • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) + (-1 : ℝ) • (x 6 - x 1) := by
    module
  have h40 : x 4 - x 0 = (oblX0 x 4 - 1) • (x 0 - x 1) + oblX2 x 4 • (x 2 - x 1) +
      oblX6 x 4 • (x 6 - x 1) := by
    rw [show x 4 - x 0 = (x 4 - x 1) - (x 0 - x 1) by abel, hrep 4]; module
  have h64 : x 6 - x 4 = (-oblX0 x 4) • (x 0 - x 1) + (-oblX2 x 4) • (x 2 - x 1) +
      (1 - oblX6 x 4) • (x 6 - x 1) := by
    rw [show x 6 - x 4 = (x 6 - x 1) - (x 4 - x 1) by abel, hrep 4]; module
  have h52 : x 5 - x 2 = oblX0 x 5 • (x 0 - x 1) + (oblX2 x 5 - 1) • (x 2 - x 1) +
      oblX6 x 5 • (x 6 - x 1) := by
    rw [show x 5 - x 2 = (x 5 - x 1) - (x 2 - x 1) by abel, hrep 5]; module
  have h05 : x 0 - x 5 = (1 - oblX0 x 5) • (x 0 - x 1) + (-oblX2 x 5) • (x 2 - x 1) +
      (-oblX6 x 5) • (x 6 - x 1) := by
    rw [show x 0 - x 5 = (x 0 - x 1) - (x 5 - x 1) by abel, hrep 5]; module
  have hw43_rep : w43 = (oblX0 x 3 - oblX0 x 4) • (x 0 - x 1) +
      (oblX2 x 3 - oblX2 x 4) • (x 2 - x 1) + (oblX6 x 3 - oblX6 x 4) • (x 6 - x 1) := by
    dsimp [w43]; rw [show x 3 - x 4 = (x 3 - x 1) - (x 4 - x 1) by abel, hrep 3, hrep 4]; module
  have hrow_04 : det3 (x 4 - x 0) (x 2 - x 6) w43 = t * det24 x * R04 x := by
    have h50 : x 5 - x 0 = (oblX0 x 5 - 1) • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) +
        oblX6 x 5 • (x 6 - x 1) := by
      rw [show x 5 - x 0 = (x 5 - x 1) - (x 0 - x 1) by abel, hrep 5]; module
    have hw_eq : w43 = ((s - 1) * (oblX0 x 4 - 1) + t * (oblX0 x 5 - 1)) • (x 0 - x 1) +
        ((s - 1) * oblX2 x 4 + t * oblX2 x 5) • (x 2 - x 1) +
        ((s - 1) * oblX6 x 4 + t * oblX6 x 5) • (x 6 - x 1) := by
      dsimp [w43]; rw [hw43_dec, h40, h50]; module
    conv_lhs => arg 1; rw [h40]
    conv_lhs => arg 2; rw [h26]
    conv_lhs => arg 3; rw [hw_eq]
    rw [M4.det3_frame x (oblX0 x 4 - 1) (oblX2 x 4) (oblX6 x 4) 0 1 (-1)
      ((s - 1) * (oblX0 x 4 - 1) + t * (oblX0 x 5 - 1))
      ((s - 1) * oblX2 x 4 + t * oblX2 x 5)
      ((s - 1) * oblX6 x 4 + t * oblX6 x 5)]
    dsimp [R04]; ring
  have hrow_46 : det3 (x 6 - x 4) (x 2 - x 6) w43 =
      det24 x * (-(oblX0 x 3 * (1 - oblX2 x 4 - oblX6 x 4 + omega3 x * oblX0 x 4))) := by
    have h7_eq : oblX0 x 3 * (1 - oblX2 x 4 - oblX6 x 4 + omega3 x * oblX0 x 4) =
        oblX0 x 3 * (1 - oblX2 x 4 - oblX6 x 4) - (1 - oblX2 x 3 - oblX6 x 3) * oblX0 x 4 := by
      dsimp [omega3]; have := ha3.ne'; field_simp; ring
    conv_lhs => arg 1; rw [h64]
    conv_lhs => arg 2; rw [h26]
    conv_lhs => arg 3; rw [hw43_rep]
    rw [M4.det3_frame x (-oblX0 x 4) (-oblX2 x 4) (1 - oblX6 x 4) 0 1 (-1)
      (oblX0 x 3 - oblX0 x 4) (oblX2 x 3 - oblX2 x 4) (oblX6 x 3 - oblX6 x 4)]
    have h1 : (-oblX0 x 4 * (1 * (oblX6 x 3 - oblX6 x 4) - -1 * (oblX2 x 3 - oblX2 x 4)) -
          -oblX2 x 4 * (0 * (oblX6 x 3 - oblX6 x 4) - -1 * (oblX0 x 3 - oblX0 x 4)) +
        (1 - oblX6 x 4) * (0 * (oblX2 x 3 - oblX2 x 4) - 1 * (oblX0 x 3 - oblX0 x 4))) * det24 x =
        det24 x * -(oblX0 x 3 * (1 - oblX2 x 4 - oblX6 x 4) -
          (1 - oblX2 x 3 - oblX6 x 3) * oblX0 x 4) := by ring
    rw [h1, ← h7_eq]
  have hf236_4 : 0 < 1 - oblX2 x 4 - oblX6 x 4 + omega3 x * oblX0 x 4 := by
    have ev7_3 := fac_eval F 7 3
    have ev7_4 := fac_eval F 7 4
    rw [F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at ev7_3
    rw [F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at ev7_4
    have e3 := eq3 F
    have h7_0 : F.f 7 (x 0) = (1 + omega3 x) * F.f 7 (x 1) := by
      have hid : oblX0 x 3 * (F.f 7 (x 0) - (1 + omega3 x) * F.f 7 (x 1)) = 0 := by
        linear_combination -ev7_3 + F.f 7 (x 1) * e3
      exact sub_eq_zero.mp ((mul_eq_zero.mp hid).resolve_left ha3.ne')
    rw [h7_0] at ev7_4
    have h4 : F.f 7 (x 4) = (1 - oblX2 x 4 - oblX6 x 4 + omega3 x * oblX0 x 4) * F.f 7 (x 1) := by
      rw [ev7_4]; ring
    have h74 : F.f 7 (x 4) < 0 := F.neg 7 4 (by decide)
    have h71 : F.f 7 (x 1) < 0 := F.neg 7 1 (by decide)
    nlinarith
  have h25_pos : 0 < oblX0 x 5 * (oblX2 x 3 - oblX2 x 4 + oblX6 x 3 - oblX6 x 4) +
      (oblX0 x 3 - oblX0 x 4) * (1 - oblX2 x 5 - oblX6 x 5) := by
    by_cases h1bc : 0 ≤ 1 - oblX2 x 5 - oblX6 x 5
    · have h1 : 0 < oblX0 x 5 * (oblX2 x 3 - oblX2 x 4 + oblX6 x 3 - oblX6 x 4) :=
        mul_pos (by linarith) (by linarith)
      have h2 : 0 ≤ (oblX0 x 3 - oblX0 x 4) * (1 - oblX2 x 5 - oblX6 x 5) :=
        mul_nonneg (sub_pos.mpr ha).le h1bc
      linarith
    · push Not at h1bc
      have hid : oblX0 x 5 * (oblX2 x 3 - oblX2 x 4 + oblX6 x 3 - oblX6 x 4) +
          (oblX0 x 3 - oblX0 x 4) * (1 - oblX2 x 5 - oblX6 x 5) =
          (s - 1) * (oblX0 x 5 * (oblX2 x 4 + oblX6 x 4) +
            (1 - oblX0 x 4) * (oblX2 x 5 + oblX6 x 5 - 1)) +
          t * (oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1) := by
        linear_combination oblX0 x 5 * (hdb + hdc) + (1 - oblX2 x 5 - oblX6 x 5) * hda
      rw [hid]
      have h1 : 0 < oblX0 x 5 * (oblX2 x 4 + oblX6 x 4) := mul_pos (by linarith) (by linarith)
      have h2 : 0 < (1 - oblX0 x 4) * (oblX2 x 5 + oblX6 x 5 - 1) :=
        mul_pos (sub_pos.mpr ha4) (by linarith)
      have h3 : 0 < t * (oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1) := mul_pos ht (by linarith)
      nlinarith
  have hrow_25' : det3 (x 5 - x 2) (x 2 - x 6) w43 =
      det24 x * (oblX0 x 5 * (oblX2 x 3 - oblX2 x 4 + oblX6 x 3 - oblX6 x 4) +
        (oblX0 x 3 - oblX0 x 4) * (1 - oblX2 x 5 - oblX6 x 5)) := by
    conv_lhs => arg 1; rw [h52]
    conv_lhs => arg 2; rw [h26]
    conv_lhs => arg 3; rw [hw43_rep]
    rw [M4.det3_frame x (oblX0 x 5) (oblX2 x 5 - 1) (oblX6 x 5) 0 1 (-1)
      (oblX0 x 3 - oblX0 x 4) (oblX2 x 3 - oblX2 x 4) (oblX6 x 3 - oblX6 x 4)]
    ring
  have hrow_05 : det3 (x 0 - x 5) (x 2 - x 6) w43 =
      -((s - 1) * det24 x * ((oblX2 x 5 + oblX6 x 5) * (1 - oblX0 x 4) +
        (oblX0 x 5 - 1) * (oblX2 x 4 + oblX6 x 4))) := by
    have h50 : x 5 - x 0 = (oblX0 x 5 - 1) • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) +
        oblX6 x 5 • (x 6 - x 1) := by
      rw [show x 5 - x 0 = (x 5 - x 1) - (x 0 - x 1) by abel, hrep 5]; module
    have hw_eq : w43 = ((s - 1) * (oblX0 x 4 - 1) + t * (oblX0 x 5 - 1)) • (x 0 - x 1) +
        ((s - 1) * oblX2 x 4 + t * oblX2 x 5) • (x 2 - x 1) +
        ((s - 1) * oblX6 x 4 + t * oblX6 x 5) • (x 6 - x 1) := by
      dsimp [w43]; rw [hw43_dec, h40, h50]; module
    conv_lhs => arg 1; rw [h05]
    conv_lhs => arg 2; rw [h26]
    conv_lhs => arg 3; rw [hw_eq]
    rw [M4.det3_frame x (1 - oblX0 x 5) (-oblX2 x 5) (-oblX6 x 5) 0 1 (-1)
      ((s - 1) * (oblX0 x 4 - 1) + t * (oblX0 x 5 - 1))
      ((s - 1) * oblX2 x 4 + t * oblX2 x 5)
      ((s - 1) * oblX6 x 4 + t * oblX6 x 5)]
    ring
  have h05_cpos : 0 < (s - 1) * ((oblX2 x 5 + oblX6 x 5) * (1 - oblX0 x 4) +
      (oblX0 x 5 - 1) * (oblX2 x 4 + oblX6 x 4)) := by
    have h1 : 0 < (oblX2 x 5 + oblX6 x 5) * (1 - oblX0 x 4) :=
      mul_pos (by linarith) (sub_pos.mpr ha4)
    have h2 : 0 < (oblX0 x 5 - 1) * (oblX2 x 4 + oblX6 x 4) :=
      mul_pos (sub_pos.mpr ha5) (by linarith)
    exact mul_pos (sub_pos.mpr hs1) (by linarith)
  have hz05 : ⟪x 0, w43⟫ < ⟪x 5, w43⟫ := by
    have h1 : ⟪x 0 - x 1, w43⟫ < ⟪x 5 - x 1, w43⟫ := lt_of_le_of_lt (le_max_left _ _) hz.1
    rw [inner_sub_left, inner_sub_left] at h1; linarith
  have hz45 : ⟪x 4, w43⟫ < ⟪x 5, w43⟫ := by
    have h1 : ⟪x 4 - x 1, w43⟫ < ⟪x 5 - x 1, w43⟫ := lt_of_le_of_lt (le_max_right _ _) hz.1
    rw [inner_sub_left, inner_sub_left] at h1; linarith
  have hz52 : ⟪x 5, w43⟫ < ⟪x 2, w43⟫ := by
    have h1 := hz.2; rw [inner_sub_left, inner_sub_left] at h1; linarith
  have hd2_pos : 0 < ⟪x 6 - x 5, d2⟫ := by
    dsimp [d2]
    exact real_inner_self_pos.mpr (sub_ne_zero.mpr (T.inj.ne (by decide)))
  have hd2_sq : 0 < det24 x * det24 x := mul_self_pos.mpr T.det_ne
  by_cases hz65_0 : ⟪x 6 - x 5, w43⟫ = 0
  · by_cases hz65_1 : ⟪x 6 - x 5, d1⟫ < 0
    · right
      refine splitAny24_of_lex3' F (by decide) c hc_inj pat hcyc_ok w43 d1 d2 hfac_lex 2 4
        (by decide) (by decide) (det24 x) ?_
      intro i hia j hj hjc
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by decide +revert
      have hc0 : c 0 = 0 := rfl; have hc1 : c 1 = 4 := rfl; have hc2 : c 2 = 6 := rfl
      have hc3 : c 3 = 2 := rfl; have hc4 : c 4 = 5 := rfl
      have he0 : (0 : ZMod 5) + 1 = 1 := rfl; have he1 : (1 : ZMod 5) + 1 = 2 := rfl
      have he2 : (2 : ZMod 5) + 1 = 3 := rfl; have he3 : (3 : ZMod 5) + 1 = 4 := rfl
      have he4 : (4 : ZMod 5) + 1 = 0 := rfl
      rcases hi with rfl | rfl | rfl | rfl | rfl
      · rcases hj with rfl | rfl
        · refine ⟨-1, Or.inl (by rw [hc0, hc4, inner_sub_left]; linarith [hz05]), Or.inl ?_⟩
          rw [he0, he2, hc0, hc1, hc2, hc3, hrow_04]
          have h1 : det24 x * -1 * (t * det24 x * R04 x) = (det24 x * det24 x) * (t * (-R04 x)) := by ring
          rw [h1]; exact mul_pos hd2_sq (mul_pos ht (neg_pos.mpr hR04))
        · refine ⟨-1, Or.inl (by rw [he0, hc1, hc4, inner_sub_left]; linarith [hz45]), Or.inl ?_⟩
          rw [he0, he2, hc0, hc1, hc2, hc3, hrow_04]
          have h1 : det24 x * -1 * (t * det24 x * R04 x) = (det24 x * det24 x) * (t * (-R04 x)) := by ring
          rw [h1]; exact mul_pos hd2_sq (mul_pos ht (neg_pos.mpr hR04))
      · rcases hj with rfl | rfl
        · refine ⟨-1, Or.inl (by rw [hc1, hc4, inner_sub_left]; linarith [hz45]), Or.inl ?_⟩
          rw [he1, he2, hc1, hc2, hc3, hrow_46]
          have h1 : det24 x * -1 * (det24 x * -(oblX0 x 3 * (1 - oblX2 x 4 - oblX6 x 4 + omega3 x * oblX0 x 4))) =
              (det24 x * det24 x) * (oblX0 x 3 * (1 - oblX2 x 4 - oblX6 x 4 + omega3 x * oblX0 x 4)) := by ring
          rw [h1]; exact mul_pos hd2_sq (mul_pos ha3 hf236_4)
        · refine ⟨-1, ?_, Or.inl ?_⟩
          · rw [he1, hc2, hc4]; simp only [neg_one_mul]
            exact Or.inr ⟨by rw [neg_eq_zero]; exact hz65_0, Or.inl (neg_pos.mpr hz65_1)⟩
          · rw [he1, he2, hc1, hc2, hc3, hrow_46]
            have h1 : det24 x * -1 * (det24 x * -(oblX0 x 3 * (1 - oblX2 x 4 - oblX6 x 4 + omega3 x * oblX0 x 4))) =
                (det24 x * det24 x) * (oblX0 x 3 * (1 - oblX2 x 4 - oblX6 x 4 + omega3 x * oblX0 x 4)) := by ring
            rw [h1]; exact mul_pos hd2_sq (mul_pos ha3 hf236_4)
      · exact absurd rfl hia
      · rcases hj with rfl | rfl
        · refine ⟨1, Or.inl (by rw [hc3, hc4, inner_sub_left]; linarith [hz52]), Or.inl ?_⟩
          rw [he3, he2, hc3, hc4, hc2, hrow_25']
          have h1 : det24 x * 1 * (det24 x * (oblX0 x 5 * (oblX2 x 3 - oblX2 x 4 + oblX6 x 3 - oblX6 x 4) +
              (oblX0 x 3 - oblX0 x 4) * (1 - oblX2 x 5 - oblX6 x 5))) =
              (det24 x * det24 x) * (oblX0 x 5 * (oblX2 x 3 - oblX2 x 4 + oblX6 x 3 - oblX6 x 4) +
              (oblX0 x 3 - oblX0 x 4) * (1 - oblX2 x 5 - oblX6 x 5)) := by ring
          rw [h1]; exact mul_pos hd2_sq h25_pos
        · exact absurd he3 hjc
      · rcases hj with rfl | rfl
        · exact absurd rfl hjc
        · refine ⟨-1, Or.inl (by rw [he4, hc0, hc4, inner_sub_left]; linarith [hz05]), Or.inl ?_⟩
          rw [he4, he2, hc4, hc0, hc2, hc3, hrow_05]
          have h1 : det24 x * -1 * -((s - 1) * det24 x * ((oblX2 x 5 + oblX6 x 5) * (1 - oblX0 x 4) +
              (oblX0 x 5 - 1) * (oblX2 x 4 + oblX6 x 4))) =
              (det24 x * det24 x) * ((s - 1) * ((oblX2 x 5 + oblX6 x 5) * (1 - oblX0 x 4) +
              (oblX0 x 5 - 1) * (oblX2 x 4 + oblX6 x 4))) := by ring
          rw [h1]; exact mul_pos hd2_sq h05_cpos
    · left
      have h65_lex : LexPos3 (⟪x 6, w43⟫ - ⟪x 5, w43⟫) (⟪x 6, d1⟫ - ⟪x 5, d1⟫)
          (⟪x 6, d2⟫ - ⟪x 5, d2⟫) := by
        rw [← inner_sub_left, ← inner_sub_left, ← inner_sub_left]
        rcases eq_or_lt_of_le (not_lt.mp hz65_1) with heq | hlt
        · exact Or.inr ⟨hz65_0, Or.inr ⟨heq.symm, hd2_pos⟩⟩
        · exact Or.inr ⟨hz65_0, Or.inl hlt⟩
      refine ⟨5, inferInstance, c, {3, 6, 7, 8}, {0, 1, 2, 4, 5}, w43, d1, d2, by decide,
        hc_inj, (by unfold S0xCycUD; decide), ?_, ?_, ?_⟩
      · intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl
        · exact Or.inr ⟨hf3_0, Or.inl hd3_1⟩
        · exact Or.inl hf6
        · exact Or.inl hf7
        · exact Or.inr ⟨hf8_0, Or.inl hd8_1⟩
      · intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl
        · exact Or.inl (by linarith)
        · exact Or.inl (by linarith)
        · exact Or.inl (by linarith)
        · exact Or.inl (by linarith)
        · exact Or.inl (by linarith)
      · refine robUniLex_five_twopeak _ ?_ ?_ ?_ h65_lex
        · change ⟪x (c 0), w43⟫ < ⟪x (c 4), w43⟫; simp [c]; exact hz05
        · change ⟪x (c 1), w43⟫ < ⟪x (c 4), w43⟫; simp [c]; exact hz45
        · change ⟪x (c 4), w43⟫ < ⟪x (c 3), w43⟫; simp [c]; exact hz52
  · rcases lt_or_gt_of_ne hz65_0 with hz65_neg | hz65_pos
    · right
      refine splitAny24_of_lex3' F (by decide) c hc_inj pat hcyc_ok w43 d1 d2 hfac_lex 2 4
        (by decide) (by decide) (det24 x) ?_
      intro i hia j hj hjc
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by decide +revert
      have hc0 : c 0 = 0 := rfl; have hc1 : c 1 = 4 := rfl; have hc2 : c 2 = 6 := rfl
      have hc3 : c 3 = 2 := rfl; have hc4 : c 4 = 5 := rfl
      have he0 : (0 : ZMod 5) + 1 = 1 := rfl; have he1 : (1 : ZMod 5) + 1 = 2 := rfl
      have he2 : (2 : ZMod 5) + 1 = 3 := rfl; have he3 : (3 : ZMod 5) + 1 = 4 := rfl
      have he4 : (4 : ZMod 5) + 1 = 0 := rfl
      rcases hi with rfl | rfl | rfl | rfl | rfl
      · rcases hj with rfl | rfl
        · refine ⟨-1, Or.inl (by rw [hc0, hc4, inner_sub_left]; linarith [hz05]), Or.inl ?_⟩
          rw [he0, he2, hc0, hc1, hc2, hc3, hrow_04]
          have h1 : det24 x * -1 * (t * det24 x * R04 x) = (det24 x * det24 x) * (t * (-R04 x)) := by ring
          rw [h1]; exact mul_pos hd2_sq (mul_pos ht (neg_pos.mpr hR04))
        · refine ⟨-1, Or.inl (by rw [he0, hc1, hc4, inner_sub_left]; linarith [hz45]), Or.inl ?_⟩
          rw [he0, he2, hc0, hc1, hc2, hc3, hrow_04]
          have h1 : det24 x * -1 * (t * det24 x * R04 x) = (det24 x * det24 x) * (t * (-R04 x)) := by ring
          rw [h1]; exact mul_pos hd2_sq (mul_pos ht (neg_pos.mpr hR04))
      · rcases hj with rfl | rfl
        · refine ⟨-1, Or.inl (by rw [hc1, hc4, inner_sub_left]; linarith [hz45]), Or.inl ?_⟩
          rw [he1, he2, hc1, hc2, hc3, hrow_46]
          have h1 : det24 x * -1 * (det24 x * -(oblX0 x 3 * (1 - oblX2 x 4 - oblX6 x 4 + omega3 x * oblX0 x 4))) =
              (det24 x * det24 x) * (oblX0 x 3 * (1 - oblX2 x 4 - oblX6 x 4 + omega3 x * oblX0 x 4)) := by ring
          rw [h1]; exact mul_pos hd2_sq (mul_pos ha3 hf236_4)
        · refine ⟨-1, Or.inl (by rw [he1, hc2, hc4, neg_one_mul]; exact neg_pos.mpr hz65_neg), Or.inl ?_⟩
          rw [he1, he2, hc1, hc2, hc3, hrow_46]
          have h1 : det24 x * -1 * (det24 x * -(oblX0 x 3 * (1 - oblX2 x 4 - oblX6 x 4 + omega3 x * oblX0 x 4))) =
              (det24 x * det24 x) * (oblX0 x 3 * (1 - oblX2 x 4 - oblX6 x 4 + omega3 x * oblX0 x 4)) := by ring
          rw [h1]; exact mul_pos hd2_sq (mul_pos ha3 hf236_4)
      · exact absurd rfl hia
      · rcases hj with rfl | rfl
        · refine ⟨1, Or.inl (by rw [hc3, hc4, inner_sub_left]; linarith [hz52]), Or.inl ?_⟩
          rw [he3, he2, hc3, hc4, hc2, hrow_25']
          have h1 : det24 x * 1 * (det24 x * (oblX0 x 5 * (oblX2 x 3 - oblX2 x 4 + oblX6 x 3 - oblX6 x 4) +
              (oblX0 x 3 - oblX0 x 4) * (1 - oblX2 x 5 - oblX6 x 5))) =
              (det24 x * det24 x) * (oblX0 x 5 * (oblX2 x 3 - oblX2 x 4 + oblX6 x 3 - oblX6 x 4) +
              (oblX0 x 3 - oblX0 x 4) * (1 - oblX2 x 5 - oblX6 x 5)) := by ring
          rw [h1]; exact mul_pos hd2_sq h25_pos
        · exact absurd he3 hjc
      · rcases hj with rfl | rfl
        · exact absurd rfl hjc
        · refine ⟨-1, Or.inl (by rw [he4, hc0, hc4, inner_sub_left]; linarith [hz05]), Or.inl ?_⟩
          rw [he4, he2, hc4, hc0, hc2, hc3, hrow_05]
          have h1 : det24 x * -1 * -((s - 1) * det24 x * ((oblX2 x 5 + oblX6 x 5) * (1 - oblX0 x 4) +
              (oblX0 x 5 - 1) * (oblX2 x 4 + oblX6 x 4))) =
              (det24 x * det24 x) * ((s - 1) * ((oblX2 x 5 + oblX6 x 5) * (1 - oblX0 x 4) +
              (oblX0 x 5 - 1) * (oblX2 x 4 + oblX6 x 4))) := by ring
          rw [h1]; exact mul_pos hd2_sq h05_cpos
    · left
      have h65_lex : LexPos3 (⟪x 6, w43⟫ - ⟪x 5, w43⟫) (⟪x 6, d1⟫ - ⟪x 5, d1⟫)
          (⟪x 6, d2⟫ - ⟪x 5, d2⟫) := by
        rw [← inner_sub_left]; exact Or.inl hz65_pos
      refine ⟨5, inferInstance, c, {3, 6, 7, 8}, {0, 1, 2, 4, 5}, w43, d1, d2, by decide,
        hc_inj, (by unfold S0xCycUD; decide), ?_, ?_, ?_⟩
      · intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl
        · exact Or.inr ⟨hf3_0, Or.inl hd3_1⟩
        · exact Or.inl hf6
        · exact Or.inl hf7
        · exact Or.inr ⟨hf8_0, Or.inl hd8_1⟩
      · intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl
        · exact Or.inl (by linarith)
        · exact Or.inl (by linarith)
        · exact Or.inl (by linarith)
        · exact Or.inl (by linarith)
        · exact Or.inl (by linarith)
      · refine robUniLex_five_twopeak _ ?_ ?_ ?_ h65_lex
        · change ⟪x (c 0), w43⟫ < ⟪x (c 4), w43⟫; simp [c]; exact hz05
        · change ⟪x (c 1), w43⟫ < ⟪x (c 4), w43⟫; simp [c]; exact hz45
        · change ⟪x (c 4), w43⟫ < ⟪x (c 3), w43⟫; simp [c]; exact hz52

theorem isRupert_of_E3426 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (ha5 : 1 < oblX0 x 5) (ha4 : oblX0 x 4 < 1)
    (hsig : F.f 8 (x 5) < F.f 8 (x 0))
    (ha : oblX0 x 4 < oblX0 x 3) (hb : oblX2 x 4 < oblX2 x 3) (hc : oblX6 x 4 < oblX6 x 3)
    (hz : max ⟪x 0 - x 1, x 3 - x 4⟫ ⟪x 4 - x 1, x 3 - x 4⟫ < ⟪x 5 - x 1, x 3 - x 4⟫ ∧
          ⟪x 5 - x 1, x 3 - x 4⟫ < ⟪x 2 - x 1, x 3 - x 4⟫) :
    IsRupert (univ.image x) := by
  rcases lexAny_or_split_E3426 F hC ha5 ha4 hsig ha hb hc hz with hL | hS
  · exact lexAny_isRupert F hL
  · exact splitAny24_isRupert F hS

/-! ### Part 3: `splitAny24_E3412` and `isRupert_of_E3412` (`E34-12`) -/

theorem splitAny24_E3412 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (ha5 : 1 < oblX0 x 5) (ha4 : oblX0 x 4 < 1)
    (hsig : F.f 8 (x 5) < F.f 8 (x 0))
    (ha : oblX0 x 3 ≤ oblX0 x 4) (hb : oblX2 x 4 < oblX2 x 3) (hc : oblX6 x 4 < oblX6 x 3)
    (hnu : nu346b x < 0)
    (hz : max 0 (max ⟪x 6 - x 1, x 3 - x 4⟫
            (max ⟪x 0 - x 1, x 3 - x 4⟫ ⟪x 4 - x 1, x 3 - x 4⟫)) < ⟪x 5 - x 1, x 3 - x 4⟫ ∧
          ⟪x 5 - x 1, x 3 - x 4⟫ < ⟪x 2 - x 1, x 3 - x 4⟫) :
    SplitAny24 F := by
  let _ := hC
  have T := type24OfFac F
  have hc4 : 0 < oblX6 x 4 := T.X6_pos (v := 4) (by decide)
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hnc : F.f 3 (x 1) < F.f 3 (x 6) := (nC_pos_iff F).mp (nC_pos_of F ha4.le ha5)
  have hnb : nB x < 0 := by dsimp [nB]; nlinarith
  obtain ⟨s, t, hs, ht, hdec, hda, hdb, hdc⟩ := lemmaM_coords F
  have hs1 : 1 < s := by
    have ev8 := congrArg (fun v => ⟪F.N 8, v⟫) hdec
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
      ← F.hN 8 (x 3) (x 0), ← F.hN 8 (x 4) (x 0), ← F.hN 8 (x 5) (x 0),
      F.zero 8 3 (by decide), F.zero 8 4 (by decide), zero_sub] at ev8
    have hmul : (s - 1) * (-F.f 8 (x 0)) = t * (F.f 8 (x 0) - F.f 8 (x 5)) := by linarith
    have hpos_rhs : 0 < t * (F.f 8 (x 0) - F.f 8 (x 5)) := mul_pos ht (sub_pos.mpr hsig)
    have h80 : 0 < -F.f 8 (x 0) := neg_pos.mpr (F.neg 8 0 (by decide))
    have hs1' : 0 < s - 1 := pos_of_mul_pos_left (by linarith) h80.le
    linarith
  have hw43_dec : x 3 - x 4 = (s - 1) • (x 4 - x 0) + t • (x 5 - x 0) := by
    calc x 3 - x 4 = (x 3 - x 0) - (x 4 - x 0) := by abel
      _ = (s • (x 4 - x 0) + t • (x 5 - x 0)) - (x 4 - x 0) := by rw [hdec]
      _ = (s - 1) • (x 4 - x 0) + t • (x 5 - x 0) := by module
  let w43 : ℝ³ := x 3 - x 4
  let d1 : ℝ³ := x 6 - x 1
  let d2 : ℝ³ := x 1 - x 0
  let c : ZMod 6 → Fin 7 := ![0, 4, 6, 1, 2, 5]
  let pat : Fin 9 → Bool := fun t => decide (t = 3 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8)
  have hc_inj : Function.Injective c := by
    intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)
  have hcyc_ok : S0xCycOK s0x_S24 c pat := by unfold S0xCycOK; decide
  have hf0 : ⟪F.N 0, w43⟫ < 0 := by
    dsimp [w43]; rw [← F.hN 0 (x 3) (x 4)]
    have ev3 := fac_eval F 0 3; have ev4 := fac_eval F 0 4
    rw [F.zero 0 0 (by decide), F.zero 0 1 (by decide), F.zero 0 2 (by decide)] at ev3 ev4
    have hmul : F.f 0 (x 3) - F.f 0 (x 4) = (oblX6 x 3 - oblX6 x 4) * F.f 0 (x 6) := by
      rw [ev3, ev4]; ring
    rw [hmul]; exact mul_neg_of_pos_of_neg (sub_pos.mpr hc) (F.neg 0 6 (by decide))
  have hf1 : ⟪F.N 1, w43⟫ < 0 := by
    dsimp [w43]; rw [← F.hN 1 (x 3) (x 4)]
    have ev3 := fac_eval F 1 3; have ev4 := fac_eval F 1 4
    rw [F.zero 1 0 (by decide), F.zero 1 1 (by decide), F.zero 1 6 (by decide)] at ev3 ev4
    have hmul : F.f 1 (x 3) - F.f 1 (x 4) = (oblX2 x 3 - oblX2 x 4) * F.f 1 (x 2) := by
      rw [ev3, ev4]; ring
    rw [hmul]; exact mul_neg_of_pos_of_neg (sub_pos.mpr hb) (F.neg 1 2 (by decide))
  have hf2 : ⟪F.N 2, w43⟫ < 0 := by
    dsimp [w43]; rw [hw43_dec, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      ← F.hN 2 (x 4) (x 0), ← F.hN 2 (x 5) (x 0), F.zero 2 0 (by decide), F.zero 2 5 (by decide),
      sub_self, sub_zero, mul_zero, add_zero]
    exact mul_neg_of_pos_of_neg (sub_pos.mpr hs1) (F.neg 2 4 (by decide))
  have hf3_0 : ⟪F.N 3, w43⟫ = 0 := by
    dsimp [w43]; rw [← F.hN 3 (x 3) (x 4), F.zero 3 3 (by decide), F.zero 3 4 (by decide), sub_self]
  have hd3_1 : 0 < ⟪F.N 3, d1⟫ := by
    dsimp [d1]; rw [← F.hN 3 (x 6) (x 1)]; exact sub_pos.mpr hnc
  have hf4 : ⟪F.N 4, w43⟫ < 0 := by
    dsimp [w43]; rw [hw43_dec, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      ← F.hN 4 (x 4) (x 0), ← F.hN 4 (x 5) (x 0), F.zero 4 0 (by decide), F.zero 4 4 (by decide),
      sub_self, sub_zero, mul_zero, zero_add]
    exact mul_neg_of_pos_of_neg ht (F.neg 4 5 (by decide))
  have hf5_lex : LexPos3 ⟪F.N 5, w43⟫ ⟪F.N 5, d1⟫ ⟪F.N 5, d2⟫ := by
    have hw5 : ⟪F.N 5, w43⟫ = (oblX0 x 3 - oblX0 x 4) * F.f 5 (x 0) := by
      dsimp [w43]; rw [← F.hN 5 (x 3) (x 4)]
      have ev3 := fac_eval F 5 3; have ev4 := fac_eval F 5 4
      rw [F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)] at ev3 ev4
      rw [ev3, ev4]; ring
    have hd5_1 : ⟪F.N 5, d1⟫ = 0 := by
      dsimp [d1]; rw [← F.hN 5 (x 6) (x 1), F.zero 5 6 (by decide), F.zero 5 1 (by decide), sub_self]
    have hd5_2 : 0 < ⟪F.N 5, d2⟫ := by
      dsimp [d2]; rw [← F.hN 5 (x 1) (x 0), F.zero 5 1 (by decide), zero_sub]
      exact neg_pos.mpr (F.neg 5 0 (by decide))
    rcases eq_or_lt_of_le ha with heq | hlt
    · exact Or.inr ⟨by rw [hw5, heq, sub_self, zero_mul], Or.inr ⟨hd5_1, hd5_2⟩⟩
    · exact Or.inl (by rw [hw5]; exact mul_pos_of_neg_of_neg (sub_neg.mpr hlt) (F.neg 5 0 (by decide)))
  have hf6 : 0 < ⟪F.N 6, w43⟫ := by
    dsimp [w43]; rw [← F.hN 6 (x 3) (x 4), F.zero 6 3 (by decide), zero_sub]
    exact neg_pos.mpr (F.neg 6 4 (by decide))
  have hf7 : 0 < ⟪F.N 7, w43⟫ := by
    dsimp [w43]; rw [← F.hN 7 (x 3) (x 4), F.zero 7 3 (by decide), zero_sub]
    exact neg_pos.mpr (F.neg 7 4 (by decide))
  have hf8_0 : ⟪F.N 8, w43⟫ = 0 := by
    dsimp [w43]; rw [← F.hN 8 (x 3) (x 4), F.zero 8 3 (by decide), F.zero 8 4 (by decide), sub_self]
  have hd8_1 : 0 < ⟪F.N 8, d1⟫ := by
    dsimp [d1]; rw [← F.hN 8 (x 6) (x 1), F.zero 8 6 (by decide), zero_sub]
    exact neg_pos.mpr (F.neg 8 1 (by decide))
  have hfac_lex : ∀ t : Fin 9,
      LexPos3 (if pat t then ⟪F.N t, w43⟫ else -⟪F.N t, w43⟫)
              (if pat t then ⟪F.N t, d1⟫ else -⟪F.N t, d1⟫)
              (if pat t then ⟪F.N t, d2⟫ else -⟪F.N t, d2⟫) := by
    intro t; fin_cases t <;> simp [pat]
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨hf3_0, Or.inl hd3_1⟩
    · exact Or.inl (by linarith)
    · exact hf5_lex
    · exact Or.inl hf6
    · exact Or.inl hf7
    · exact Or.inr ⟨hf8_0, Or.inl hd8_1⟩
  have hrep : ∀ v : Fin 7, x v - x 1 =
      oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1) := by
    intro v; rw [T.rep v]; abel
  have h21 : x 2 - x 1 = (0 : ℝ) • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) := by
    module
  have h40 : x 4 - x 0 = (oblX0 x 4 - 1) • (x 0 - x 1) + oblX2 x 4 • (x 2 - x 1) +
      oblX6 x 4 • (x 6 - x 1) := by
    rw [show x 4 - x 0 = (x 4 - x 1) - (x 0 - x 1) by abel, hrep 4]; module
  have h64 : x 6 - x 4 = (-oblX0 x 4) • (x 0 - x 1) + (-oblX2 x 4) • (x 2 - x 1) +
      (1 - oblX6 x 4) • (x 6 - x 1) := by
    rw [show x 6 - x 4 = (x 6 - x 1) - (x 4 - x 1) by abel, hrep 4]; module
  have h16 : x 1 - x 6 = (0 : ℝ) • (x 0 - x 1) + (0 : ℝ) • (x 2 - x 1) + (-1 : ℝ) • (x 6 - x 1) := by
    module
  have h52 : x 5 - x 2 = oblX0 x 5 • (x 0 - x 1) + (oblX2 x 5 - 1) • (x 2 - x 1) +
      oblX6 x 5 • (x 6 - x 1) := by
    rw [show x 5 - x 2 = (x 5 - x 1) - (x 2 - x 1) by abel, hrep 5]; module
  have h05 : x 0 - x 5 = (1 - oblX0 x 5) • (x 0 - x 1) + (-oblX2 x 5) • (x 2 - x 1) +
      (-oblX6 x 5) • (x 6 - x 1) := by
    rw [show x 0 - x 5 = (x 0 - x 1) - (x 5 - x 1) by abel, hrep 5]; module
  have hw43_rep : w43 = (oblX0 x 3 - oblX0 x 4) • (x 0 - x 1) +
      (oblX2 x 3 - oblX2 x 4) • (x 2 - x 1) + (oblX6 x 3 - oblX6 x 4) • (x 6 - x 1) := by
    dsimp [w43]; rw [show x 3 - x 4 = (x 3 - x 1) - (x 4 - x 1) by abel, hrep 3, hrep 4]; module
  have hrow_04 : det3 (x 4 - x 0) (x 2 - x 1) w43 = t * det24 x * nB x := by
    have h50 : x 5 - x 0 = (oblX0 x 5 - 1) • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) +
        oblX6 x 5 • (x 6 - x 1) := by
      rw [show x 5 - x 0 = (x 5 - x 1) - (x 0 - x 1) by abel, hrep 5]; module
    have hw_eq : w43 = ((s - 1) * (oblX0 x 4 - 1) + t * (oblX0 x 5 - 1)) • (x 0 - x 1) +
        ((s - 1) * oblX2 x 4 + t * oblX2 x 5) • (x 2 - x 1) +
        ((s - 1) * oblX6 x 4 + t * oblX6 x 5) • (x 6 - x 1) := by
      dsimp [w43]; rw [hw43_dec, h40, h50]; module
    conv_lhs => arg 1; rw [h40]
    conv_lhs => arg 2; rw [h21]
    conv_lhs => arg 3; rw [hw_eq]
    rw [M4.det3_frame x (oblX0 x 4 - 1) (oblX2 x 4) (oblX6 x 4) 0 1 0
      ((s - 1) * (oblX0 x 4 - 1) + t * (oblX0 x 5 - 1))
      ((s - 1) * oblX2 x 4 + t * oblX2 x 5)
      ((s - 1) * oblX6 x 4 + t * oblX6 x 5)]
    dsimp [nB]; ring
  have hrow_46 : det3 (x 6 - x 4) (x 2 - x 1) w43 = det24 x * nu346b x := by
    conv_lhs => arg 1; rw [h64]
    conv_lhs => arg 2; rw [h21]
    conv_lhs => arg 3; rw [hw43_rep]
    rw [M4.det3_frame x (-oblX0 x 4) (-oblX2 x 4) (1 - oblX6 x 4) 0 1 0
      (oblX0 x 3 - oblX0 x 4) (oblX2 x 3 - oblX2 x 4) (oblX6 x 3 - oblX6 x 4)]
    dsimp [nu346b]; ring
  have hrow_61_w : det3 (x 1 - x 6) (x 2 - x 1) w43 = det24 x * (-(oblX0 x 4 - oblX0 x 3)) := by
    conv_lhs => arg 1; rw [h16]
    conv_lhs => arg 2; rw [h21]
    conv_lhs => arg 3; rw [hw43_rep]
    rw [M4.det3_frame x 0 0 (-1) 0 1 0
      (oblX0 x 3 - oblX0 x 4) (oblX2 x 3 - oblX2 x 4) (oblX6 x 3 - oblX6 x 4)]
    ring
  have hrow_61_d1 : det3 (x 1 - x 6) (x 2 - x 1) d1 = 0 := by
    have hd1_rep : d1 = (0 : ℝ) • (x 0 - x 1) + (0 : ℝ) • (x 2 - x 1) + (1 : ℝ) • (x 6 - x 1) := by
      dsimp [d1]; module
    conv_lhs => arg 1; rw [h16]
    conv_lhs => arg 2; rw [h21]
    conv_lhs => arg 3; rw [hd1_rep]
    rw [M4.det3_frame x 0 0 (-1) 0 1 0 0 0 1]
    ring
  have hrow_61_d2 : det3 (x 1 - x 6) (x 2 - x 1) d2 = -det24 x := by
    have hd2_rep : d2 = (-1 : ℝ) • (x 0 - x 1) + (0 : ℝ) • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) := by
      dsimp [d2]; module
    conv_lhs => arg 1; rw [h16]
    conv_lhs => arg 2; rw [h21]
    conv_lhs => arg 3; rw [hd2_rep]
    rw [M4.det3_frame x 0 0 (-1) 0 1 0 (-1) 0 0]
    ring
  have hrow_25 : det3 (x 5 - x 2) (x 2 - x 1) w43 =
      det24 x * (oblX6 x 5 * (oblX0 x 4 - oblX0 x 3) +
        oblX0 x 5 * (oblX6 x 3 - oblX6 x 4)) := by
    conv_lhs => arg 1; rw [h52]
    conv_lhs => arg 2; rw [h21]
    conv_lhs => arg 3; rw [hw43_rep]
    rw [M4.det3_frame x (oblX0 x 5) (oblX2 x 5 - 1) (oblX6 x 5) 0 1 0
      (oblX0 x 3 - oblX0 x 4) (oblX2 x 3 - oblX2 x 4) (oblX6 x 3 - oblX6 x 4)]
    ring
  have hrow_05 : det3 (x 0 - x 5) (x 2 - x 1) w43 =
      det24 x * (-(oblX6 x 5 * (oblX0 x 4 - oblX0 x 3) +
        (oblX0 x 5 - 1) * (oblX6 x 3 - oblX6 x 4))) := by
    conv_lhs => arg 1; rw [h05]
    conv_lhs => arg 2; rw [h21]
    conv_lhs => arg 3; rw [hw43_rep]
    rw [M4.det3_frame x (1 - oblX0 x 5) (-oblX2 x 5) (-oblX6 x 5) 0 1 0
      (oblX0 x 3 - oblX0 x 4) (oblX2 x 3 - oblX2 x 4) (oblX6 x 3 - oblX6 x 4)]
    ring
  have h25_cpos : 0 < oblX6 x 5 * (oblX0 x 4 - oblX0 x 3) +
      oblX0 x 5 * (oblX6 x 3 - oblX6 x 4) := by
    have h1 : 0 ≤ oblX6 x 5 * (oblX0 x 4 - oblX0 x 3) := mul_nonneg hc5.le (sub_nonneg.mpr ha)
    have h2 : 0 < oblX0 x 5 * (oblX6 x 3 - oblX6 x 4) := mul_pos (by linarith) (sub_pos.mpr hc)
    linarith
  have h05_cpos : 0 < oblX6 x 5 * (oblX0 x 4 - oblX0 x 3) +
      (oblX0 x 5 - 1) * (oblX6 x 3 - oblX6 x 4) := by
    have h1 : 0 ≤ oblX6 x 5 * (oblX0 x 4 - oblX0 x 3) := mul_nonneg hc5.le (sub_nonneg.mpr ha)
    have h2 : 0 < (oblX0 x 5 - 1) * (oblX6 x 3 - oblX6 x 4) :=
      mul_pos (sub_pos.mpr ha5) (sub_pos.mpr hc)
    linarith
  have hz05 : ⟪x 0, w43⟫ < ⟪x 5, w43⟫ := by
    have h0 : ⟪x 0 - x 1, w43⟫ < ⟪x 5 - x 1, w43⟫ :=
      lt_of_le_of_lt (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hz.1
    rw [inner_sub_left, inner_sub_left] at h0; linarith
  have hz45 : ⟪x 4, w43⟫ < ⟪x 5, w43⟫ := by
    have h4 : ⟪x 4 - x 1, w43⟫ < ⟪x 5 - x 1, w43⟫ :=
      lt_of_le_of_lt (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hz.1
    rw [inner_sub_left, inner_sub_left] at h4; linarith
  have hz65 : ⟪x 6, w43⟫ < ⟪x 5, w43⟫ := by
    have h6 : ⟪x 6 - x 1, w43⟫ < ⟪x 5 - x 1, w43⟫ :=
      lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hz.1
    rw [inner_sub_left, inner_sub_left] at h6; linarith
  have hz15 : ⟪x 1, w43⟫ < ⟪x 5, w43⟫ := by
    have h1 : 0 < ⟪x 5 - x 1, w43⟫ := lt_of_le_of_lt (le_max_left _ _) hz.1
    rw [inner_sub_left] at h1; linarith
  have hz52 : ⟪x 5, w43⟫ < ⟪x 2, w43⟫ := by
    have h2 := hz.2; rw [inner_sub_left, inner_sub_left] at h2; linarith
  have hd2_sq : 0 < det24 x * det24 x := mul_self_pos.mpr T.det_ne
  refine splitAny24_of_lex3' F (by decide) c hc_inj pat hcyc_ok w43 d1 d2 hfac_lex 3 5
    (by decide) (by decide) (det24 x) ?_
  intro i hia j hj hjc
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by decide +revert
  have hc0 : c 0 = 0 := rfl; have hc1 : c 1 = 4 := rfl; have hc2 : c 2 = 6 := rfl
  have hc3 : c 3 = 1 := rfl; have hc4 : c 4 = 2 := rfl; have hc5 : c 5 = 5 := rfl
  have he0 : (0 : ZMod 6) + 1 = 1 := rfl; have he1 : (1 : ZMod 6) + 1 = 2 := rfl
  have he2 : (2 : ZMod 6) + 1 = 3 := rfl; have he3 : (3 : ZMod 6) + 1 = 4 := rfl
  have he4 : (4 : ZMod 6) + 1 = 5 := rfl; have he5 : (5 : ZMod 6) + 1 = 0 := rfl
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  · rcases hj with rfl | rfl
    · refine ⟨-1, Or.inl (by rw [hc0, hc5, inner_sub_left]; linarith [hz05]), Or.inl ?_⟩
      rw [he0, he3, hc0, hc1, hc3, hc4, hrow_04]
      have h1 : det24 x * -1 * (t * det24 x * nB x) = (det24 x * det24 x) * (t * (-nB x)) := by ring
      rw [h1]; exact mul_pos hd2_sq (mul_pos ht (neg_pos.mpr hnb))
    · refine ⟨-1, Or.inl (by rw [he0, hc1, hc5, inner_sub_left]; linarith [hz45]), Or.inl ?_⟩
      rw [he0, he3, hc0, hc1, hc3, hc4, hrow_04]
      have h1 : det24 x * -1 * (t * det24 x * nB x) = (det24 x * det24 x) * (t * (-nB x)) := by ring
      rw [h1]; exact mul_pos hd2_sq (mul_pos ht (neg_pos.mpr hnb))
  · rcases hj with rfl | rfl
    · refine ⟨-1, Or.inl (by rw [hc1, hc5, inner_sub_left]; linarith [hz45]), Or.inl ?_⟩
      rw [he1, he3, hc1, hc2, hc3, hc4, hrow_46]
      have h1 : det24 x * -1 * (det24 x * nu346b x) = (det24 x * det24 x) * (-nu346b x) := by ring
      rw [h1]; exact mul_pos hd2_sq (neg_pos.mpr hnu)
    · refine ⟨-1, Or.inl (by rw [he1, hc2, hc5, inner_sub_left]; linarith [hz65]), Or.inl ?_⟩
      rw [he1, he3, hc1, hc2, hc3, hc4, hrow_46]
      have h1 : det24 x * -1 * (det24 x * nu346b x) = (det24 x * det24 x) * (-nu346b x) := by ring
      rw [h1]; exact mul_pos hd2_sq (neg_pos.mpr hnu)
  · rcases hj with rfl | rfl
    · refine ⟨-1, Or.inl (by rw [hc2, hc5, inner_sub_left]; linarith [hz65]), ?_⟩
      rw [he2, he3, hc2, hc3, hc4]
      rcases eq_or_lt_of_le ha with heq | hlt
      · refine Or.inr ⟨by rw [hrow_61_w, heq, sub_self, neg_zero, mul_zero, mul_zero],
          Or.inr ⟨by rw [hrow_61_d1, mul_zero], ?_⟩⟩
        rw [hrow_61_d2]
        have h1 : det24 x * -1 * (-det24 x) = det24 x * det24 x := by ring
        rw [h1]; exact hd2_sq
      · refine Or.inl ?_
        rw [hrow_61_w]
        have h1 : det24 x * -1 * (det24 x * -(oblX0 x 4 - oblX0 x 3)) =
            (det24 x * det24 x) * (oblX0 x 4 - oblX0 x 3) := by ring
        rw [h1]; exact mul_pos hd2_sq (sub_pos.mpr hlt)
    · refine ⟨-1, Or.inl (by rw [he2, hc3, hc5, inner_sub_left]; linarith [hz15]), ?_⟩
      rw [he2, he3, hc2, hc3, hc4]
      rcases eq_or_lt_of_le ha with heq | hlt
      · refine Or.inr ⟨by rw [hrow_61_w, heq, sub_self, neg_zero, mul_zero, mul_zero],
          Or.inr ⟨by rw [hrow_61_d1, mul_zero], ?_⟩⟩
        rw [hrow_61_d2]
        have h1 : det24 x * -1 * (-det24 x) = det24 x * det24 x := by ring
        rw [h1]; exact hd2_sq
      · refine Or.inl ?_
        rw [hrow_61_w]
        have h1 : det24 x * -1 * (det24 x * -(oblX0 x 4 - oblX0 x 3)) =
            (det24 x * det24 x) * (oblX0 x 4 - oblX0 x 3) := by ring
        rw [h1]; exact mul_pos hd2_sq (sub_pos.mpr hlt)
  · exact absurd rfl hia
  · rcases hj with rfl | rfl
    · refine ⟨1, Or.inl (by rw [hc4, hc5, inner_sub_left]; linarith [hz52]), Or.inl ?_⟩
      rw [he4, he3, hc4, hc5, hc3, hrow_25]
      have h1 : det24 x * 1 * (det24 x * (oblX6 x 5 * (oblX0 x 4 - oblX0 x 3) +
          oblX0 x 5 * (oblX6 x 3 - oblX6 x 4))) =
          (det24 x * det24 x) * (oblX6 x 5 * (oblX0 x 4 - oblX0 x 3) +
          oblX0 x 5 * (oblX6 x 3 - oblX6 x 4)) := by ring
      rw [h1]; exact mul_pos hd2_sq h25_cpos
    · exact absurd rfl hjc
  · rcases hj with rfl | rfl
    · exact absurd rfl hjc
    · refine ⟨-1, Or.inl (by rw [he5, hc0, hc5, inner_sub_left]; linarith [hz05]), Or.inl ?_⟩
      rw [he5, he3, hc5, hc0, hc3, hc4, hrow_05]
      have h1 : det24 x * -1 * (det24 x * -(oblX6 x 5 * (oblX0 x 4 - oblX0 x 3) +
          (oblX0 x 5 - 1) * (oblX6 x 3 - oblX6 x 4))) =
          (det24 x * det24 x) * (oblX6 x 5 * (oblX0 x 4 - oblX0 x 3) +
          (oblX0 x 5 - 1) * (oblX6 x 3 - oblX6 x 4)) := by ring
      rw [h1]; exact mul_pos hd2_sq h05_cpos

theorem isRupert_of_E3412 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (ha5 : 1 < oblX0 x 5) (ha4 : oblX0 x 4 < 1)
    (hsig : F.f 8 (x 5) < F.f 8 (x 0))
    (ha : oblX0 x 3 ≤ oblX0 x 4) (hb : oblX2 x 4 < oblX2 x 3) (hc : oblX6 x 4 < oblX6 x 3)
    (hnu : nu346b x < 0)
    (hz : max 0 (max ⟪x 6 - x 1, x 3 - x 4⟫
            (max ⟪x 0 - x 1, x 3 - x 4⟫ ⟪x 4 - x 1, x 3 - x 4⟫)) < ⟪x 5 - x 1, x 3 - x 4⟫ ∧
          ⟪x 5 - x 1, x 3 - x 4⟫ < ⟪x 2 - x 1, x 3 - x 4⟫) :
    IsRupert (univ.image x) :=
  splitAny24_isRupert F (splitAny24_E3412 F hC ha5 ha4 hsig ha hb hc hnu hz)

end Minimality.T24.A12
