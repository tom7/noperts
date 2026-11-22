module

public import Minimality.M4eType24
public import Minimality.M4dType24
public import Minimality.M4cType24
public import Minimality.M4bType24
public import Minimality.M4Sym24

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.LexCell Minimality.H21 Minimality.H24.SAT
  Minimality.T24.SAT Minimality.T24.RCell Minimality.Split Minimality.T24.M4
  Minimality.T24.A7 Minimality.T24.A8

namespace Minimality.T24.A17

theorem e10_sym {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (h346 : F.f 8 (x 1) < F.f 8 (x 0)) (h235 : F.f 6 (x 1) < F.f 6 (x 0))
    (hU : ¬ LexAny F) :
    ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0 ∧ ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0 := by
  have T := type24OfFac F
  by_contra hcon
  have hpos : 0 < ⟪x 0 - x 1, x 2 - x 1⟫ ∨ 0 < ⟪x 0 - x 1, x 6 - x 1⟫ := by
    by_contra h; push Not at h; exact hcon ⟨h.1, h.2⟩
  have hA : 0 < ⟪x 0 - x 1, x 0 - x 1⟫ :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide))
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hb3 : 0 < oblX2 x 3 := T.X2_pos (v := 3) (by decide)
  have hc3 : 0 < oblX6 x 3 := T.X6_pos (v := 3) (by decide)
  have hb3c3 : 1 < oblX2 x 3 + oblX6 x 3 := by
    have := T.eq3
    have := hC.1
    nlinarith
  -- the level-0 depth of vertex 3
  have hz3 : ⟪x 3 - x 1, x 0 - x 1⟫ = oblX0 x 3 * ⟪x 0 - x 1, x 0 - x 1⟫ +
      oblX2 x 3 * ⟪x 0 - x 1, x 2 - x 1⟫ + oblX6 x 3 * ⟪x 0 - x 1, x 6 - x 1⟫ := by
    have h := T.rep 3
    have h' : x 3 - x 1 = oblX0 x 3 • (x 0 - x 1) + oblX2 x 3 • (x 2 - x 1) +
        oblX6 x 3 • (x 6 - x 1) := by
      rw [sub_eq_iff_eq_add']
      refine h.trans ?_
      abel
    rw [h', inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_left, real_inner_comm (x 0 - x 1) (x 2 - x 1),
      real_inner_comm (x 0 - x 1) (x 6 - x 1)]
  -- facing of 236 at `ea`
  have hf7 : ⟪F.N 7, x 0 - x 1⟫ < 0 := by
    have hrep : x 3 - x 1 = oblX0 x 3 • (x 0 - x 1) + oblX2 x 3 • (x 2 - x 1) +
        oblX6 x 3 • (x 6 - x 1) := by
      rw [sub_eq_iff_eq_add']
      refine (T.rep 3).trans ?_
      abel
    have e := F.hN 7 (x 3) (x 1)
    rw [hrep, inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
      inner_smul_right, ← F.hN 7 (x 0) (x 1), ← F.hN 7 (x 2) (x 1), ← F.hN 7 (x 6) (x 1),
      F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at e
    have h1 := F.neg 7 1 (by decide)
    have hω := T.eq3
    have hω3 := hC.1
    have key : (F.f 7 (x 0) - F.f 7 (x 1)) * oblX0 x 3 =
        F.f 7 (x 1) * (omega3 x * oblX0 x 3) := by
      linear_combination (-1 : ℝ) * e + F.f 7 (x 1) * hω
    rw [← F.hN]
    by_contra hge
    push Not at hge
    have h2 : 0 ≤ (F.f 7 (x 0) - F.f 7 (x 1)) * oblX0 x 3 := mul_nonneg hge ha3.le
    have h3 := mul_neg_of_neg_of_pos h1 (mul_pos hω3 ha3)
    linarith
  have hN0 : ⟪F.N 0, x 0 - x 1⟫ = 0 := by
    rw [← F.hN, F.zero 0 0 (by decide), F.zero 0 1 (by decide), sub_self]
  have hN1 : ⟪F.N 1, x 0 - x 1⟫ = 0 := by
    rw [← F.hN, F.zero 1 0 (by decide), F.zero 1 1 (by decide), sub_self]
  have hN2 : 0 < ⟪F.N 2, x 0 - x 1⟫ := by
    rw [← F.hN, F.zero 2 0 (by decide)]; linarith [F.neg 2 1 (by decide)]
  have hN3 : 0 < ⟪F.N 3, x 0 - x 1⟫ := by
    rw [← F.hN, F.zero 3 0 (by decide)]; linarith [F.neg 3 1 (by decide)]
  have hN4 : 0 < ⟪F.N 4, x 0 - x 1⟫ := by
    rw [← F.hN, F.zero 4 0 (by decide)]; linarith [F.neg 4 1 (by decide)]
  have hN5 : ⟪F.N 5, x 0 - x 1⟫ < 0 := by
    rw [← F.hN, F.zero 5 1 (by decide), sub_zero]; exact F.neg 5 0 (by decide)
  have hN6 : 0 < ⟪F.N 6, x 0 - x 1⟫ := by rw [← F.hN]; linarith
  have hN8 : 0 < ⟪F.N 8, x 0 - x 1⟫ := by rw [← F.hN]; linarith
  have hD0 : 0 < ⟪F.N 0, -(x 2 - x 1) - (x 6 - x 1)⟫ := by
    rw [inner_sub_right, inner_neg_right, ← F.hN, ← F.hN, F.zero 0 2 (by decide),
      F.zero 0 1 (by decide)]
    linarith [F.neg 0 6 (by decide)]
  have hD1 : 0 < ⟪F.N 1, -(x 2 - x 1) - (x 6 - x 1)⟫ := by
    rw [inner_sub_right, inner_neg_right, ← F.hN, ← F.hN, F.zero 1 6 (by decide),
      F.zero 1 1 (by decide)]
    linarith [F.neg 1 2 (by decide)]
  apply hU
  refine ⟨4, inferInstance, (![1, 2, 3, 6] : ZMod 4 → Fin 7), {0, 1, 2, 3, 4, 6, 8}, {5, 7},
    x 0 - x 1, -(x 2 - x 1) - (x 6 - x 1), 0, by decide,
    (by intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)),
    (by unfold S0xCycUD; decide), ?_, ?_, ?_⟩
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr ⟨hN0, Or.inl hD0⟩
    · exact Or.inr ⟨hN1, Or.inl hD1⟩
    · exact Or.inl hN2
    · exact Or.inl hN3
    · exact Or.inl hN4
    · exact Or.inl hN6
    · exact Or.inl hN8
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
  · have hz : ∀ v, ⟪x v, x 0 - x 1⟫ - ⟪x 1, x 0 - x 1⟫ = ⟪x v - x 1, x 0 - x 1⟫ := by
      intro v; rw [inner_sub_left]
    have g2 : ⟪x 2, x 0 - x 1⟫ - ⟪x 1, x 0 - x 1⟫ = ⟪x 0 - x 1, x 2 - x 1⟫ := by
      rw [hz, real_inner_comm]
    have g6 : ⟪x 6, x 0 - x 1⟫ - ⟪x 1, x 0 - x 1⟫ = ⟪x 0 - x 1, x 6 - x 1⟫ := by
      rw [hz, real_inner_comm]
    have g3 := hz 3
    rw [hz3] at g3
    refine robUniLex_four_of_mixed ?_ ?_
    · rcases hpos with h | h
      · exact ⟨((0 : ZMod 4), (1 : ZMod 4)), by decide,
          Or.inl (by dsimp only [Matrix.cons_val]; linarith)⟩
      · exact ⟨((0 : ZMod 4), (3 : ZMod 4)), by decide,
          Or.inl (by dsimp only [Matrix.cons_val]; linarith)⟩
    · rcases lt_or_ge ⟪x 0 - x 1, x 2 - x 1⟫ 0 with h | h
      · exact ⟨((0 : ZMod 4), (1 : ZMod 4)), by decide,
          Or.inl (by dsimp only [Matrix.cons_val]; linarith)⟩
      rcases lt_or_ge ⟪x 0 - x 1, x 6 - x 1⟫ 0 with h' | h'
      · exact ⟨((0 : ZMod 4), (3 : ZMod 4)), by decide,
          Or.inl (by dsimp only [Matrix.cons_val]; linarith)⟩
      have key : ⟪x 0 - x 1, x 2 - x 1⟫ < ⟪x 3, x 0 - x 1⟫ - ⟪x 1, x 0 - x 1⟫ ∨
          ⟪x 0 - x 1, x 6 - x 1⟫ < ⟪x 3, x 0 - x 1⟫ - ⟪x 1, x 0 - x 1⟫ := by
        by_contra hk
        push Not at hk
        obtain ⟨k1, k2⟩ := hk
        have hp : 0 < ⟪x 3, x 0 - x 1⟫ - ⟪x 1, x 0 - x 1⟫ := by
          rw [g3]; nlinarith [mul_pos ha3 hA, mul_nonneg hb3.le h, mul_nonneg hc3.le h']
        nlinarith [mul_nonneg hb3.le (sub_nonneg.mpr k1), mul_nonneg hc3.le (sub_nonneg.mpr k2),
          mul_pos (sub_pos.mpr hb3c3) hp, mul_pos ha3 hA]
      rcases key with k | k
      · exact ⟨((2 : ZMod 4), (1 : ZMod 4)), by decide,
          Or.inl (by dsimp only [Matrix.cons_val]; linarith)⟩
      · exact ⟨((2 : ZMod 4), (3 : ZMod 4)), by decide,
          Or.inl (by dsimp only [Matrix.cons_val]; linarith)⟩

theorem famA_rev {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (hnc : F.f 3 (x 1) < F.f 3 (x 6)) (h235 : F.f 6 (x 1) < F.f 6 (x 6))
    (hac : 0 < ⟪x 0 - x 1, x 6 - x 1⟫) (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0)
    (hU : ¬ LexAny F) : False := by
  have T := type24OfFac F
  have hB : 0 < ⟪x 2 - x 1, x 2 - x 1⟫ :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide))
  have hC6 : 0 < ⟪x 6 - x 1, x 6 - x 1⟫ :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide))
  -- tilt parameter
  obtain ⟨η, hη, hηB⟩ : ∃ η : ℝ, 0 < η ∧
      0 < η * ⟪x 0 - x 1, x 2 - x 1⟫ + ⟪x 2 - x 1, x 2 - x 1⟫ := by
    refine ⟨⟪x 2 - x 1, x 2 - x 1⟫ / (2 * (|⟪x 0 - x 1, x 2 - x 1⟫| + 1)), by positivity, ?_⟩
    have h1 : 0 < |⟪x 0 - x 1, x 2 - x 1⟫| + 1 := by positivity
    have h2 := neg_abs_le ⟪x 0 - x 1, x 2 - x 1⟫
    have h3 : ⟪x 2 - x 1, x 2 - x 1⟫ / (2 * (|⟪x 0 - x 1, x 2 - x 1⟫| + 1)) *
        (|⟪x 0 - x 1, x 2 - x 1⟫| + 1) = ⟪x 2 - x 1, x 2 - x 1⟫ / 2 := by
      field_simp
    have h4 : 0 < ⟪x 2 - x 1, x 2 - x 1⟫ / (2 * (|⟪x 0 - x 1, x 2 - x 1⟫| + 1)) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 h4.le]
  -- facing of 025 at `ec`
  have hf2 : ⟪F.N 2, x 6 - x 1⟫ < 0 := by
    have hrep : x 5 - x 1 = oblX0 x 5 • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) +
        oblX6 x 5 • (x 6 - x 1) := by
      rw [sub_eq_iff_eq_add']
      refine (T.rep 5).trans ?_
      abel
    have e := F.hN 2 (x 5) (x 1)
    rw [hrep, inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
      inner_smul_right, ← F.hN 2 (x 0) (x 1), ← F.hN 2 (x 2) (x 1), ← F.hN 2 (x 6) (x 1),
      F.zero 2 5 (by decide), F.zero 2 2 (by decide), F.zero 2 0 (by decide)] at e
    have h1 := F.neg 2 1 (by decide)
    have hω := T.eq5
    have hω5 := hC.2.2.1
    have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
    have key : (F.f 2 (x 6) - F.f 2 (x 1)) * oblX6 x 5 =
        F.f 2 (x 1) * (omega5 x * oblX6 x 5) := by
      linear_combination (-1 : ℝ) * e + F.f 2 (x 1) * hω
    rw [← F.hN]
    by_contra hge
    push Not at hge
    have h2 : 0 ≤ (F.f 2 (x 6) - F.f 2 (x 1)) * oblX6 x 5 := mul_nonneg hge hc5.le
    have h3 := mul_neg_of_neg_of_pos h1 (mul_pos hω5 hc5)
    linarith
  have hN0 : ⟪F.N 0, x 6 - x 1⟫ < 0 := by
    rw [← F.hN, F.zero 0 1 (by decide), sub_zero]; exact F.neg 0 6 (by decide)
  have hN1 : ⟪F.N 1, x 6 - x 1⟫ = 0 := by
    rw [← F.hN, F.zero 1 6 (by decide), F.zero 1 1 (by decide), sub_self]
  have hN5 : ⟪F.N 5, x 6 - x 1⟫ = 0 := by
    rw [← F.hN, F.zero 5 6 (by decide), F.zero 5 1 (by decide), sub_self]
  have hN3 : 0 < ⟪F.N 3, x 6 - x 1⟫ := by rw [← F.hN]; linarith
  have hN4 : 0 < ⟪F.N 4, x 6 - x 1⟫ := by
    rw [← F.hN, F.zero 4 6 (by decide)]; linarith [F.neg 4 1 (by decide)]
  have hN6 : 0 < ⟪F.N 6, x 6 - x 1⟫ := by rw [← F.hN]; linarith
  have hN7 : 0 < ⟪F.N 7, x 6 - x 1⟫ := by
    rw [← F.hN, F.zero 7 6 (by decide)]; linarith [F.neg 7 1 (by decide)]
  have hN8 : 0 < ⟪F.N 8, x 6 - x 1⟫ := by
    rw [← F.hN, F.zero 8 6 (by decide)]; linarith [F.neg 8 1 (by decide)]
  have hD1 : 0 < ⟪F.N 1, -(η • (x 0 - x 1)) - (x 2 - x 1)⟫ := by
    rw [inner_sub_right, inner_neg_right, inner_smul_right, ← F.hN, ← F.hN, F.zero 1 0 (by decide),
      F.zero 1 1 (by decide)]
    linarith [F.neg 1 2 (by decide)]
  have hD5 : 0 < ⟪F.N 5, -(η • (x 0 - x 1)) - (x 2 - x 1)⟫ := by
    rw [inner_sub_right, inner_neg_right, inner_smul_right, ← F.hN, ← F.hN, F.zero 5 2 (by decide),
      F.zero 5 1 (by decide)]
    have := F.neg 5 0 (by decide)
    nlinarith
  apply hU
  refine ⟨4, inferInstance, (![1, 0, 5, 2] : ZMod 4 → Fin 7), {1, 3, 4, 5, 6, 7, 8}, {0, 2},
    x 6 - x 1, -(η • (x 0 - x 1)) - (x 2 - x 1), 0, by decide,
    (by intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)),
    (by unfold S0xCycUD; decide), ?_, ?_, ?_⟩
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr ⟨hN1, Or.inl hD1⟩
    · exact Or.inl hN3
    · exact Or.inl hN4
    · exact Or.inr ⟨hN5, Or.inl hD5⟩
    · exact Or.inl hN6
    · exact Or.inl hN7
    · exact Or.inl hN8
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
  · have hz : ∀ v, ⟪x v, x 6 - x 1⟫ - ⟪x 1, x 6 - x 1⟫ = ⟪x v - x 1, x 6 - x 1⟫ := by
      intro v; rw [inner_sub_left]
    have g0 : ⟪x 0, x 6 - x 1⟫ - ⟪x 1, x 6 - x 1⟫ = ⟪x 0 - x 1, x 6 - x 1⟫ := hz 0
    have g2 : ⟪x 2, x 6 - x 1⟫ - ⟪x 1, x 6 - x 1⟫ = ⟪x 2 - x 1, x 6 - x 1⟫ := hz 2
    have l2 : ⟪x 2, -(η • (x 0 - x 1)) - (x 2 - x 1)⟫ - ⟪x 1, -(η • (x 0 - x 1)) - (x 2 - x 1)⟫ =
        -(η * ⟪x 0 - x 1, x 2 - x 1⟫) - ⟪x 2 - x 1, x 2 - x 1⟫ := by
      rw [← inner_sub_left, inner_sub_right, inner_neg_right, inner_smul_right, real_inner_comm]
    refine robUniLex_four_of_mixed ?_ ?_
    · exact ⟨((0 : ZMod 4), (1 : ZMod 4)), by decide,
        Or.inl (by dsimp only [Matrix.cons_val]; linarith)⟩
    · refine ⟨((0 : ZMod 4), (3 : ZMod 4)), by decide, ?_⟩
      dsimp only [Matrix.cons_val]
      rcases lt_or_eq_of_le hbc with h | h
      · exact Or.inl (by dsimp only; linarith)
      · exact Or.inr ⟨by dsimp only; linarith, Or.inl (by dsimp only; linarith)⟩

theorem robUniLex_five_a2 (z : ZMod 5 → ℝ × ℝ × ℝ)
    (h60 : LexLt3 (z 1) (z 0)) (h10 : (z 0).1 < (z 4).1) (h61 : (z 1).1 ≤ (z 0).1)
    (hch : (z 4).1 < (z 3).1 ∨ (z 2).1 < (z 3).1 ∨ (z 2).1 < (z 1).1) :
    RobUniLex z := by
  intro B b c d hb hbc hcd hd
  have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by revert B; decide
  have hbcd : (b = 1 ∧ c = 2 ∧ d = 3) ∨ (b = 1 ∧ c = 2 ∧ d = 4) ∨
      (b = 1 ∧ c = 3 ∧ d = 4) ∨ (b = 2 ∧ c = 3 ∧ d = 4) := by omega
  rcases hch with hc | hc | hc
  all_goals rcases hB with rfl | rfl | rfl | rfl | rfl <;>
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
    | exact Or.inr (Or.inl h60)
    | exact Or.inr (Or.inr (Or.inl h60))
    | exact Or.inl (Or.inl (by linarith))
    | exact Or.inr (Or.inl (Or.inl (by linarith)))
    | exact Or.inr (Or.inr (Or.inl (Or.inl (by linarith))))
    | exact Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))

theorem sgn63_pure (a3 c3 a5 c5 g0 g1 g5 : ℝ) (ha3 : 0 < a3) (hg0 : g0 < 0) (hg1 : g1 < 0)
    (hg5 : g5 < 0) (e3 : g1 + a3 * (g0 - g1) + c3 * (0 - g1) = 0)
    (e5 : g5 = g1 + a5 * (g0 - g1) + c5 * (0 - g1)) :
    0 < a3 + c3 - 1 ∧ 0 < a5 * c3 - a3 * c5 + a3 - a5 := by
  have h1 : g1 * (a3 + c3 - 1) = a3 * g0 := by linear_combination -e3
  have h2 : g1 * (a5 * c3 - a3 * c5 + a3 - a5) = a3 * g5 := by
    linear_combination (-a5) * e3 + (-a3) * e5
  constructor
  · by_contra h; push Not at h
    nlinarith [mul_nonneg_of_nonpos_of_nonpos hg1.le h, mul_neg_of_pos_of_neg ha3 hg0]
  · by_contra h; push Not at h
    nlinarith [mul_nonneg_of_nonpos_of_nonpos hg1.le h, mul_neg_of_pos_of_neg ha3 hg5]

theorem sgn50_pure (a3 c3 a5 c5 g6 g1 g3 : ℝ) (hc5 : 0 < c5) (hg6 : g6 < 0) (hg1 : g1 < 0)
    (hg3 : g3 < 0) (e5 : g1 + a5 * (0 - g1) + c5 * (g6 - g1) = 0)
    (e3 : g3 = g1 + a3 * (0 - g1) + c3 * (g6 - g1)) :
    0 < a5 + c5 - 1 ∧ 0 < a5 * c3 - a3 * c5 + c5 - c3 := by
  have h1 : g1 * (a5 + c5 - 1) = c5 * g6 := by linear_combination -e5
  have h2 : g1 * (a5 * c3 - a3 * c5 + c5 - c3) = c5 * g3 := by
    linear_combination (-c3) * e5 + (-c5) * e3
  constructor
  · by_contra h; push Not at h
    nlinarith [mul_nonneg_of_nonpos_of_nonpos hg1.le h, mul_neg_of_pos_of_neg hc5 hg6]
  · by_contra h; push Not at h
    nlinarith [mul_nonneg_of_nonpos_of_nonpos hg1.le h, mul_neg_of_pos_of_neg hc5 hg3]

theorem chord_a2_pure (a3 b3 c3 a5 b5 c5 gab gbc B : ℝ)
    (S1 : 0 < a5 + c5 - 1) (S2 : 0 < a5 * c3 - a3 * c5 + a3 - a5) (S3 : 0 < a3 + c3 - 1)
    (S4 : 0 < a5 * c3 - a3 * c5 + c5 - c3)
    (hpb : 0 < (a3 + c3 - 1) * b5 - (a5 + c5 - 1) * b3) (hB : 0 < B) (hgb : gbc < gab) :
    gab < a5 * gab + b5 * B + c5 * gbc ∨
      a3 * gab + b3 * B + c3 * gbc < a5 * gab + b5 * B + c5 * gbc ∨
      a3 * gab + b3 * B + c3 * gbc < gbc := by
  by_contra hcon
  push Not at hcon
  obtain ⟨k0, k3, k6⟩ := hcon
  have hW : (a5 * c3 - a3 * c5 + c5 - c3) * gbc + (a3 + c3 - 1) * (a5 * gab + b5 * B + c5 * gbc)
      - (a5 * c3 - a3 * c5 + a3 - a5) * gab
      - (a5 + c5 - 1) * (a3 * gab + b3 * B + c3 * gbc)
      = ((a3 + c3 - 1) * b5 - (a5 + c5 - 1) * b3) * B := by ring
  have hpos := mul_pos hpb hB
  rcases le_total gab (a3 * gab + b3 * B + c3 * gbc) with h | h
  · nlinarith [mul_nonneg S1.le (sub_nonneg.mpr h), mul_nonneg S4.le (sub_nonneg.mpr hgb.le),
      mul_nonneg S3.le (sub_nonneg.mpr k0)]
  · nlinarith [mul_nonneg S2.le (sub_nonneg.mpr h), mul_nonneg S4.le (sub_nonneg.mpr k6),
      mul_nonneg S3.le (sub_nonneg.mpr k3)]

theorem g63_pure (a3 b3 c3 a5 b5 c5 p7 p8 u8 q70 q80 q75 q85 : ℝ) (ha3 : 0 < a3) (hp7 : p7 < 0)
    (hβ : u8 < p8) (hq70 : q70 < 0) (hq80 : q80 < 0) (hq75 : q75 < 0) (hq85 : q85 < 0)
    (hp8 : p8 < 0)
    (e73 : 0 = p7 + a3 * (q70 - p7) + b3 * (0 - p7) + c3 * (0 - p7))
    (e83 : 0 = p8 + a3 * (q80 - p8) + b3 * (u8 - p8) + c3 * (0 - p8))
    (e75 : q75 = p7 + a5 * (q70 - p7) + b5 * (0 - p7) + c5 * (0 - p7))
    (e85 : q85 = p8 + a5 * (q80 - p8) + b5 * (u8 - p8) + c5 * (0 - p8)) :
    0 < a3 + c3 - 1 ∧ 0 < a5 * c3 - a3 * c5 + a3 - a5 := by
  have hp : 0 < p8 - u8 := sub_pos.mpr hβ
  have hp7' : 0 < -p7 := neg_pos.mpr hp7
  refine sgn63_pure a3 c3 a5 c5 ((p8 - u8) * q70 + (-p7) * q80) ((p8 - u8) * p7 + (-p7) * p8)
    ((p8 - u8) * q75 + (-p7) * q85) ha3 ?_ ?_ ?_ ?_ ?_
  · nlinarith [mul_neg_of_pos_of_neg hp hq70, mul_neg_of_pos_of_neg hp7' hq80]
  · nlinarith [mul_neg_of_pos_of_neg hp hp7, mul_neg_of_pos_of_neg hp7' hp8]
  · nlinarith [mul_neg_of_pos_of_neg hp hq75, mul_neg_of_pos_of_neg hp7' hq85]
  · linear_combination (u8 - p8) * e73 + p7 * e83
  · linear_combination (p8 - u8) * e75 + (-p7) * e85

theorem g50_pure (a3 b3 c3 a5 b5 c5 p2 p3 u3 q26 q36 q23 : ℝ) (hc5 : 0 < c5) (hp2 : p2 < 0)
    (hβ : u3 < p3) (hp3 : p3 < 0) (hq26 : q26 < 0) (hq36 : q36 < 0) (hq23 : q23 < 0)
    (e25 : 0 = p2 + a5 * (0 - p2) + b5 * (0 - p2) + c5 * (q26 - p2))
    (e35 : 0 = p3 + a5 * (0 - p3) + b5 * (u3 - p3) + c5 * (q36 - p3))
    (e23 : q23 = p2 + a3 * (0 - p2) + b3 * (0 - p2) + c3 * (q26 - p2))
    (e33 : 0 = p3 + a3 * (0 - p3) + b3 * (u3 - p3) + c3 * (q36 - p3)) :
    0 < a5 + c5 - 1 ∧ 0 < a5 * c3 - a3 * c5 + c5 - c3 := by
  have hp : 0 < p3 - u3 := sub_pos.mpr hβ
  have hp2' : 0 < -p2 := neg_pos.mpr hp2
  refine sgn50_pure a3 c3 a5 c5 ((p3 - u3) * q26 + (-p2) * q36) ((p3 - u3) * p2 + (-p2) * p3)
    ((p3 - u3) * q23) hc5 ?_ ?_ ?_ ?_ ?_
  · nlinarith [mul_neg_of_pos_of_neg hp hq26, mul_neg_of_pos_of_neg hp2' hq36]
  · nlinarith [mul_neg_of_pos_of_neg hp hp2, mul_neg_of_pos_of_neg hp2' hp3]
  · exact mul_neg_of_pos_of_neg hp hq23
  · linear_combination (u3 - p3) * e25 + p2 * e35
  · linear_combination (p3 - u3) * e23 + (-p2) * e33

theorem pb_pure (a3 b3 c3 a5 b5 c5 p3 u3 q36 : ℝ) (hβ : u3 < p3) (hq36 : q36 < 0)
    (S4 : 0 < a5 * c3 - a3 * c5 + c5 - c3)
    (e35 : 0 = p3 + a5 * (0 - p3) + b5 * (u3 - p3) + c5 * (q36 - p3))
    (e33 : 0 = p3 + a3 * (0 - p3) + b3 * (u3 - p3) + c3 * (q36 - p3)) :
    0 < (a3 + c3 - 1) * b5 - (a5 + c5 - 1) * b3 := by
  have key : ((a3 + c3 - 1) * b5 - (a5 + c5 - 1) * b3) * (u3 - p3) =
      (a5 * c3 - a3 * c5 + c5 - c3) * q36 := by
    linear_combination (-(a3 + c3 - 1)) * e35 + (a5 + c5 - 1) * e33
  by_contra h
  push Not at h
  nlinarith [mul_nonneg_of_nonpos_of_nonpos h (sub_nonpos.mpr hβ.le), mul_neg_of_pos_of_neg S4 hq36]

private theorem eta_aux {η s m A B : ℝ} (hη : 0 < η) (he : η * (2 * (s + 1)) = m) (hm : 0 < m)
    (hA : |A| ≤ s) (hB : m ≤ B) : 0 < η * A + B := by
  have h1 := (abs_le.1 hA).1
  have h2 := mul_le_mul_of_nonneg_left h1 hη.le
  nlinarith

/-- Two positive-constant conditions `0 < η A_i + B_i` hold for one small `η > 0`. -/
private theorem exists_eta2 {A1 B1 A2 B2 : ℝ} (h1 : 0 < B1) (h2 : 0 < B2) :
    ∃ η : ℝ, 0 < η ∧ 0 < η * A1 + B1 ∧ 0 < η * A2 + B2 := by
  have hs0 : 0 < |A1| + |A2| + 1 := by positivity
  have hm0 : 0 < min B1 B2 := lt_min h1 h2
  have hη : 0 < min B1 B2 / (2 * (|A1| + |A2| + 1)) := by positivity
  have e : min B1 B2 / (2 * (|A1| + |A2| + 1)) * (2 * (|A1| + |A2| + 1)) = min B1 B2 := by field_simp
  refine ⟨_, hη, eta_aux (s := |A1| + |A2|) hη (by linarith [e]) hm0 (by linarith [abs_nonneg A2]) (min_le_left _ _),
    eta_aux (s := |A1| + |A2|) hη (by linarith [e]) hm0 (by linarith [abs_nonneg A1]) (min_le_right _ _)⟩

private theorem g63_tie (a3 b3 c3 a5 b5 c5 p8 u8 q80 q85 : ℝ) (ha3 : 0 < a3) (hp8 : p8 < 0)
    (hq80 : q80 < 0) (hq85 : q85 < 0) (hu : u8 = p8)
    (e83 : 0 = p8 + a3 * (q80 - p8) + b3 * (u8 - p8) + c3 * (0 - p8))
    (e85 : q85 = p8 + a5 * (q80 - p8) + b5 * (u8 - p8) + c5 * (0 - p8)) :
    0 < a3 + c3 - 1 ∧ 0 < a5 * c3 - a3 * c5 + a3 - a5 := by
  subst hu
  constructor
  · have key : (a3 + c3 - 1) * u8 = a3 * q80 := by linear_combination e83
    by_contra h
    push Not at h
    nlinarith [mul_nonneg_of_nonpos_of_nonpos h hp8.le, mul_neg_of_pos_of_neg ha3 hq80]
  · have key : (a5 * c3 - a3 * c5 + a3 - a5) * u8 = a3 * q85 := by linear_combination a5 * e83 - a3 * e85
    by_contra h
    push Not at h
    nlinarith [mul_nonneg_of_nonpos_of_nonpos h hp8.le, mul_neg_of_pos_of_neg ha3 hq85]

theorem e12_A2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (hnb : F.f 3 (x 2) < F.f 3 (x 1)) (h346 : F.f 8 (x 2) ≤ F.f 8 (x 1))
    (hab : 0 < ⟪x 0 - x 1, x 2 - x 1⟫) (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0)
    (hU : ¬ LexAny F) : False := by
  have T := type24OfFac F
  have hB : 0 < ⟪x 2 - x 1, x 2 - x 1⟫ :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide))
  have hC6 : 0 < ⟪x 6 - x 1, x 6 - x 1⟫ :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide))
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  obtain ⟨η, hη, hηC, hη8⟩ : ∃ η : ℝ, 0 < η ∧
      0 < η * ⟪x 0 - x 1, x 6 - x 1⟫ + ⟪x 6 - x 1, x 6 - x 1⟫ ∧
      0 < η * (F.f 8 (x 0) - F.f 8 (x 1)) + (-F.f 8 (x 1)) :=
    exists_eta2 hC6 (by linarith [F.neg 8 1 (by decide)])
  -- the four edge signs of the pentagon projected along `eb`
  have h63 : 0 < oblX0 x 3 + oblX6 x 3 - 1 ∧
      0 < oblX0 x 5 * oblX6 x 3 - oblX0 x 3 * oblX6 x 5 + oblX0 x 3 - oblX0 x 5 := by
    have e73 := fac_eval F 7 3
    have e75 := fac_eval F 7 5
    have e83 := fac_eval F 8 3
    have e85 := fac_eval F 8 5
    rw [F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at e73
    rw [F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at e75
    rw [F.zero 8 3 (by decide), F.zero 8 6 (by decide)] at e83
    rw [F.zero 8 6 (by decide)] at e85
    rcases lt_or_eq_of_le h346 with h346_lt | h346_eq
    · exact g63_pure _ _ _ _ _ _ _ _ _ _ _ _ _ ha3 (F.neg 7 1 (by decide)) h346_lt
        (F.neg 7 0 (by decide)) (F.neg 8 0 (by decide)) (F.neg 7 5 (by decide))
        (F.neg 8 5 (by decide)) (F.neg 8 1 (by decide)) e73 e83 e75 e85
    · exact g63_tie _ _ _ _ _ _ _ _ _ _ ha3 (F.neg 8 1 (by decide)) (F.neg 8 0 (by decide))
        (F.neg 8 5 (by decide)) h346_eq e83 e85
  have h50 : 0 < oblX0 x 5 + oblX6 x 5 - 1 ∧
      0 < oblX0 x 5 * oblX6 x 3 - oblX0 x 3 * oblX6 x 5 + oblX6 x 5 - oblX6 x 3 := by
    have e25 := fac_eval F 2 5
    have e35 := fac_eval F 3 5
    have e23 := fac_eval F 2 3
    have e33 := fac_eval F 3 3
    rw [F.zero 2 5 (by decide), F.zero 2 0 (by decide), F.zero 2 2 (by decide)] at e25
    rw [F.zero 3 5 (by decide), F.zero 3 0 (by decide)] at e35
    rw [F.zero 2 0 (by decide), F.zero 2 2 (by decide)] at e23
    rw [F.zero 3 3 (by decide), F.zero 3 0 (by decide)] at e33
    exact g50_pure _ _ _ _ _ _ _ _ _ _ _ _ hc5 (F.neg 2 1 (by decide)) hnb
      (F.neg 3 1 (by decide)) (F.neg 2 6 (by decide)) (F.neg 3 6 (by decide))
      (F.neg 2 3 (by decide)) e25 e35 e23 e33
  have hpb : 0 < (oblX0 x 3 + oblX6 x 3 - 1) * oblX2 x 5 - (oblX0 x 5 + oblX6 x 5 - 1) * oblX2 x 3 := by
    have e35 := fac_eval F 3 5
    have e33 := fac_eval F 3 3
    rw [F.zero 3 5 (by decide), F.zero 3 0 (by decide)] at e35
    rw [F.zero 3 3 (by decide), F.zero 3 0 (by decide)] at e33
    exact pb_pure _ _ _ _ _ _ _ _ _ hnb (F.neg 3 6 (by decide)) h50.2 e35 e33
  -- facings at `eb`
  have hN0 : ⟪F.N 0, x 2 - x 1⟫ = 0 := by
    rw [← F.hN, F.zero 0 2 (by decide), F.zero 0 1 (by decide), sub_self]
  have hN1 : ⟪F.N 1, x 2 - x 1⟫ < 0 := by
    rw [← F.hN, F.zero 1 1 (by decide), sub_zero]; exact F.neg 1 2 (by decide)
  have hN2 : 0 < ⟪F.N 2, x 2 - x 1⟫ := by
    rw [← F.hN, F.zero 2 2 (by decide)]; linarith [F.neg 2 1 (by decide)]
  have hN3 : ⟪F.N 3, x 2 - x 1⟫ < 0 := by rw [← F.hN]; linarith
  have hN5 : ⟪F.N 5, x 2 - x 1⟫ = 0 := by
    rw [← F.hN, F.zero 5 2 (by decide), F.zero 5 1 (by decide), sub_self]
  have hN6 : 0 < ⟪F.N 6, x 2 - x 1⟫ := by
    rw [← F.hN, F.zero 6 2 (by decide)]; linarith [F.neg 6 1 (by decide)]
  have hN7 : 0 < ⟪F.N 7, x 2 - x 1⟫ := by
    rw [← F.hN, F.zero 7 2 (by decide)]; linarith [F.neg 7 1 (by decide)]
  have hN8 : ⟪F.N 8, x 2 - x 1⟫ ≤ 0 := by rw [← F.hN]; linarith
  have hN4 : ⟪F.N 4, x 2 - x 1⟫ < 0 := by
    have e := fac_eval F 4 4
    rw [F.zero 4 4 (by decide), F.zero 4 0 (by decide), F.zero 4 6 (by decide)] at e
    have h1 := F.neg 4 1 (by decide)
    have hω := T.eq4
    have hω4 := hC.2.1
    have key : (F.f 4 (x 2) - F.f 4 (x 1)) * oblX2 x 4 =
        F.f 4 (x 1) * (omega4 x * oblX2 x 4) := by
      linear_combination (-1 : ℝ) * e + F.f 4 (x 1) * hω
    rw [← F.hN]
    by_contra hge
    push Not at hge
    have h2 : 0 ≤ (F.f 4 (x 2) - F.f 4 (x 1)) * oblX2 x 4 := mul_nonneg hge hb4.le
    have h3 := mul_neg_of_neg_of_pos h1 (mul_pos hω4 hb4)
    linarith
  have hD0 : 0 < ⟪F.N 0, -(η • (x 0 - x 1)) - (x 6 - x 1)⟫ := by
    rw [inner_sub_right, inner_neg_right, inner_smul_right, ← F.hN, ← F.hN, F.zero 0 0 (by decide),
      F.zero 0 1 (by decide)]
    linarith [F.neg 0 6 (by decide)]
  have hD5 : 0 < ⟪F.N 5, -(η • (x 0 - x 1)) - (x 6 - x 1)⟫ := by
    rw [inner_sub_right, inner_neg_right, inner_smul_right, ← F.hN, ← F.hN, F.zero 5 6 (by decide),
      F.zero 5 1 (by decide)]
    have := F.neg 5 0 (by decide)
    nlinarith
  apply hU
  refine ⟨5, inferInstance, (![1, 6, 3, 5, 0] : ZMod 5 → Fin 7), {0, 2, 5, 6, 7}, {1, 3, 4, 8},
    x 2 - x 1, -(η • (x 0 - x 1)) - (x 6 - x 1), 0, by decide,
    (by intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)),
    (by unfold S0xCycUD; decide), ?_, ?_, ?_⟩
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact Or.inr ⟨hN0, Or.inl hD0⟩
    · exact Or.inl hN2
    · exact Or.inr ⟨hN5, Or.inl hD5⟩
    · exact Or.inl hN6
    · exact Or.inl hN7
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · rcases lt_or_eq_of_le h346 with h346_lt | h346_eq
      · exact Or.inl (by rw [← F.hN]; linarith)
      · refine Or.inr ⟨by rw [← F.hN, h346_eq]; ring, Or.inl ?_⟩
        have e0 := F.hN 8 (x 0) (x 1)
        have e6 := F.hN 8 (x 6) (x 1)
        rw [inner_sub_right, inner_neg_right, real_inner_smul_right, ← e0, ← e6, F.zero 8 6 (by decide)]
        linarith
  · -- the depths
    have hrep : ∀ v : Fin 7, x v - x 1 = oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) +
        oblX6 x v • (x 6 - x 1) := by
      intro v
      rw [sub_eq_iff_eq_add']
      refine (T.rep v).trans ?_
      abel
    have hz : ∀ v : Fin 7, ⟪x v, x 2 - x 1⟫ - ⟪x 1, x 2 - x 1⟫ =
        oblX0 x v * ⟪x 0 - x 1, x 2 - x 1⟫ + oblX2 x v * ⟪x 2 - x 1, x 2 - x 1⟫ +
          oblX6 x v * ⟪x 2 - x 1, x 6 - x 1⟫ := by
      intro v
      rw [← inner_sub_left, hrep v, inner_add_left, inner_add_left, real_inner_smul_left,
        real_inner_smul_left, real_inner_smul_left, real_inner_comm (x 2 - x 1) (x 6 - x 1)]
    have g0 : ⟪x 0, x 2 - x 1⟫ - ⟪x 1, x 2 - x 1⟫ = ⟪x 0 - x 1, x 2 - x 1⟫ := by
      rw [← inner_sub_left]
    have g6 : ⟪x 6, x 2 - x 1⟫ - ⟪x 1, x 2 - x 1⟫ = ⟪x 2 - x 1, x 6 - x 1⟫ := by
      rw [← inner_sub_left, real_inner_comm]
    have g3 := hz 3
    have g5 := hz 5
    have l6 : ⟪x 6, -(η • (x 0 - x 1)) - (x 6 - x 1)⟫ - ⟪x 1, -(η • (x 0 - x 1)) - (x 6 - x 1)⟫ =
        -(η * ⟪x 0 - x 1, x 6 - x 1⟫) - ⟪x 6 - x 1, x 6 - x 1⟫ := by
      rw [← inner_sub_left, inner_sub_right, inner_neg_right, inner_smul_right, real_inner_comm]
    have hchord := chord_a2_pure (oblX0 x 3) (oblX2 x 3) (oblX6 x 3) (oblX0 x 5) (oblX2 x 5)
      (oblX6 x 5) ⟪x 0 - x 1, x 2 - x 1⟫ ⟪x 2 - x 1, x 6 - x 1⟫ ⟪x 2 - x 1, x 2 - x 1⟫
      h50.1 h63.2 h63.1 h50.2 hpb hB (by linarith)
    refine robUniLex_five_a2 _ ?_ ?_ ?_ ?_
    · dsimp only [Matrix.cons_val]
      rcases lt_or_eq_of_le hbc with h | h
      · exact Or.inl (by dsimp only; linarith)
      · exact Or.inr ⟨by dsimp only; linarith, Or.inl (by dsimp only; linarith)⟩
    · dsimp only [Matrix.cons_val]; linarith
    · dsimp only [Matrix.cons_val]; linarith
    · dsimp only [Matrix.cons_val]
      rcases hchord with h | h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (Or.inl (by linarith))
      · exact Or.inr (Or.inr (by linarith))

theorem e12_A2_tie {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (hnb : F.f 3 (x 2) < F.f 3 (x 1)) (h346 : F.f 8 (x 2) = F.f 8 (x 1))
    (hab : 0 < ⟪x 0 - x 1, x 2 - x 1⟫) (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0)
    (hU : ¬ LexAny F) : False :=
  e12_A2 F hC hnb h346.le hab hbc hU

end Minimality.T24.A17
