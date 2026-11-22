module

public import Minimality.M4hType24

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

theorem eta_aux {η s m A B : ℝ} (hη : 0 < η) (he : η * (2 * (s + 1)) = m) (hm : 0 < m) (hA : |A| ≤ s)
    (hB : m ≤ B) : 0 < η * A + B := by
  have h1 := (abs_le.1 hA).1
  have h2 := mul_le_mul_of_nonneg_left h1 hη.le
  nlinarith

/-- Two positive-constant conditions `0 < η A_i + B_i` hold for one small `η > 0`. -/
theorem exists_eta2 {A1 B1 A2 B2 : ℝ} (h1 : 0 < B1) (h2 : 0 < B2) :
    ∃ η : ℝ, 0 < η ∧ 0 < η * A1 + B1 ∧ 0 < η * A2 + B2 := by
  have hs0 : 0 < |A1| + |A2| + 1 := by positivity
  have hm0 : 0 < min B1 B2 := lt_min h1 h2
  have hη : 0 < min B1 B2 / (2 * (|A1| + |A2| + 1)) := by positivity
  have e : min B1 B2 / (2 * (|A1| + |A2| + 1)) * (2 * (|A1| + |A2| + 1)) = min B1 B2 := by field_simp
  refine ⟨_, hη, eta_aux (s := |A1| + |A2|) hη (by linarith [e]) hm0 (by linarith [abs_nonneg A2]) (min_le_left _ _),
    eta_aux (s := |A1| + |A2|) hη (by linarith [e]) hm0 (by linarith [abs_nonneg A1]) (min_le_right _ _)⟩

theorem g63_tie (a3 b3 c3 a5 b5 c5 p8 u8 q80 q85 : ℝ) (ha3 : 0 < a3) (hp8 : p8 < 0) (hq80 : q80 < 0)
    (hq85 : q85 < 0) (hu : u8 = p8)
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

theorem e12_A2_tie {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (hnb : F.f 3 (x 2) < F.f 3 (x 1)) (h346 : F.f 8 (x 2) = F.f 8 (x 1))
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
    exact g63_tie _ _ _ _ _ _ _ _ _ _ ha3 (F.neg 8 1 (by decide)) (F.neg 8 0 (by decide))
      (F.neg 8 5 (by decide)) h346 e83 e85
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
  have hN8 : ⟪F.N 8, x 2 - x 1⟫ = 0 := by rw [← F.hN]; linarith
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
    · refine Or.inr ⟨by linarith, Or.inl ?_⟩
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


end Minimality.T24.A17
