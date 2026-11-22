import Minimality.M4bType24

/-!
# Type 24, region B: front-diagonal weak-shadow bounds at `v31` and `v30` (group v3031)

A31-REFEREE "Lean specs" items 1-2.  Convention: front vertices have the LARGER `z`.

* `v31_frontDiag`: diagonal `1-5` is in front of `0-2` along `v31` (needs `nC > 0`).
* `v31_front_bounds`: rim `(1,0,5,2)`, `nC > 0`, `b4 < b3 < b5`, `not LexAny`:
  `z5 >= z2`, `z5 >= z0`, `z1 >= z2`, `z1 >= z0` at `v31` (the last two are `v31_bound` and `-z0 >= 0`).
* `v30_frontDiag`, `v30_front_bounds`: rim `(1,0,4,6)`, `nB > 0`, `c5 < c3 < c4`:
  `z4 >= z6`, `z4 >= z0`, `z1 >= z6`, `z1 >= z0` at `v30`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.A10

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell
  Minimality.LexCell Minimality.Split Minimality.T24.M4 Minimality.T24.A7

/-- The vertex-1 frame expansion of `x v`. -/
theorem frame_rep {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (v : Fin 7) :
    x v = x 1 + (oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1)) := by
  have T := type24OfFac F
  have h : x v - x 1 = oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) +
      oblX6 x v • (x 6 - x 1) := by rw [T.rep v]; abel
  rw [← h]; abel

/-- `c4 (a5 + b5 - 1) + c5 (1 - a4 - b4) > 0` (facet `025` is negative at `x 4`). -/
theorem frontP31_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    0 < oblX6 x 4 * (oblX0 x 5 + oblX2 x 5 - 1) + oblX6 x 5 * (1 - oblX0 x 4 - oblX2 x 4) := by
  have T := type24OfFac F
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have f1 : F.f 2 (x 1) < 0 := F.neg 2 1 (by decide)
  have f4 : F.f 2 (x 4) < 0 := F.neg 2 4 (by decide)
  have e4 := fac_eval F 2 4
  have e5 := fac_eval F 2 5
  rw [F.zero 2 0 (by decide), F.zero 2 2 (by decide)] at e4 e5
  rw [F.zero 2 5 (by decide)] at e5
  have key : F.f 2 (x 1) * (oblX6 x 4 * (oblX0 x 5 + oblX2 x 5 - 1) +
      oblX6 x 5 * (1 - oblX0 x 4 - oblX2 x 4)) = oblX6 x 5 * F.f 2 (x 4) := by
    linear_combination (-oblX6 x 5) * e4 + oblX6 x 4 * e5
  by_contra hcon
  push Not at hcon
  nlinarith [mul_nonneg_of_nonpos_of_nonpos f1.le hcon, mul_neg_of_pos_of_neg hc5 f4]

/-- `b5 (a4 + c4 - 1) + b4 (1 - a5 - c5) > 0` (facet `046` is negative at `x 5`). -/
theorem frontP30_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    0 < oblX2 x 5 * (oblX0 x 4 + oblX6 x 4 - 1) + oblX2 x 4 * (1 - oblX0 x 5 - oblX6 x 5) := by
  have T := type24OfFac F
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have f1 : F.f 4 (x 1) < 0 := F.neg 4 1 (by decide)
  have f5 : F.f 4 (x 5) < 0 := F.neg 4 5 (by decide)
  have e4 := fac_eval F 4 4
  have e5 := fac_eval F 4 5
  rw [F.zero 4 0 (by decide), F.zero 4 6 (by decide)] at e4 e5
  rw [F.zero 4 4 (by decide)] at e4
  have key : F.f 4 (x 1) * (oblX2 x 5 * (oblX0 x 4 + oblX6 x 4 - 1) +
      oblX2 x 4 * (1 - oblX0 x 5 - oblX6 x 5)) = oblX2 x 4 * F.f 4 (x 5) := by
    linear_combination (-oblX2 x 4) * e5 + oblX2 x 5 * e4
  by_contra hcon
  push Not at hcon
  nlinarith [mul_nonneg_of_nonpos_of_nonpos f1.le hcon, mul_neg_of_pos_of_neg hb4 f5]

theorem v31_frontDiag {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hnc : F.f 3 (x 1) < F.f 3 (x 6)) :
    FrontDiag (x 1) (x 5) (x 0) (x 2) (v31 x) := by
  have T := type24OfFac F
  have hD : 0 < D45 x := d45_pos F
  have hnC : 0 < nC x := (nC_pos_iff F).mpr hnc
  have ha5 : 0 < oblX0 x 5 := T.X0_pos (v := 5) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hP := frontP31_pos F
  set Den : ℝ := D45 x * (oblX0 x 5 + oblX2 x 5) + oblX6 x 5 * nC x with hDen
  have hDenD : D45 x + oblX2 x 5 * (oblX6 x 4 * (oblX0 x 5 + oblX2 x 5 - 1) +
      oblX6 x 5 * (1 - oblX0 x 4 - oblX2 x 4)) = Den := by
    simp only [hDen, D45, nC]; ring
  have hDen_gt : D45 x < Den := by nlinarith [mul_pos hb5 hP]
  have hDen_pos : 0 < Den := lt_trans hD hDen_gt
  have hDen_b : D45 x * oblX2 x 5 ≤ Den := by
    nlinarith [mul_pos hD ha5, mul_pos hc5 hnC]
  have hden_ne : Den ≠ 0 := hDen_pos.ne'
  have hs0 : 0 ≤ D45 x / Den := (div_pos hD hDen_pos).le
  have hs1 : D45 x / Den ≤ 1 := (div_le_one hDen_pos).2 hDen_gt.le
  have ht0 : 0 ≤ D45 x / Den * oblX2 x 5 := (mul_pos (div_pos hD hDen_pos) hb5).le
  have ht1 : D45 x / Den * oblX2 x 5 ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one hDen_pos]; exact hDen_b
  have hγ : 0 < oblX6 x 5 / Den := div_pos hc5 hDen_pos
  refine ⟨D45 x / Den, D45 x / Den * oblX2 x 5, oblX6 x 5 / Den, hs0, hs1, ht0, ht1, hγ, ?_⟩
  have c0 : D45 x / Den * oblX0 x 5 - 1 + D45 x / Den * oblX2 x 5 = oblX6 x 5 / Den * (-nC x) := by
    field_simp; rw [hDen]; ring
  have c2 : D45 x / Den * oblX2 x 5 - D45 x / Den * oblX2 x 5 = oblX6 x 5 / Den * 0 := by ring
  have c6 : D45 x / Den * oblX6 x 5 = oblX6 x 5 / Den * D45 x := by ring
  have hx5 := frame_rep F 5
  have e : x 1 + (D45 x / Den) • (x 5 - x 1) - (x 0 + (D45 x / Den * oblX2 x 5) • (x 2 - x 0)) =
      (D45 x / Den * oblX0 x 5 - 1 + D45 x / Den * oblX2 x 5) • (x 0 - x 1) +
      (D45 x / Den * oblX2 x 5 - D45 x / Den * oblX2 x 5) • (x 2 - x 1) +
      (D45 x / Den * oblX6 x 5) • (x 6 - x 1) := by
    rw [hx5]
    simp only [add_sub_cancel_left]
    module
  rw [e, c0, c2, c6]
  simp only [v31]
  module

theorem v30_frontDiag {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hnb : F.f 3 (x 1) < F.f 3 (x 2)) :
    FrontDiag (x 1) (x 4) (x 0) (x 6) (v30 x) := by
  have T := type24OfFac F
  have hD : 0 < D45 x := d45_pos F
  have hnB : 0 < nB x := (nB_pos_iff F).mpr hnb
  have ha4 : 0 < oblX0 x 4 := T.X0_pos (v := 4) (by decide)
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hc4 : 0 < oblX6 x 4 := T.X6_pos (v := 4) (by decide)
  have hP := frontP30_pos F
  set Den : ℝ := D45 x * (oblX0 x 4 + oblX6 x 4) + oblX2 x 4 * nB x with hDen
  have hDenD : D45 x + oblX6 x 4 * (oblX2 x 5 * (oblX0 x 4 + oblX6 x 4 - 1) +
      oblX2 x 4 * (1 - oblX0 x 5 - oblX6 x 5)) = Den := by
    simp only [hDen, D45, nB]; ring
  have hDen_gt : D45 x < Den := by nlinarith [mul_pos hc4 hP]
  have hDen_pos : 0 < Den := lt_trans hD hDen_gt
  have hDen_b : D45 x * oblX6 x 4 ≤ Den := by
    nlinarith [mul_pos hD ha4, mul_pos hb4 hnB]
  have hs0 : 0 ≤ D45 x / Den := (div_pos hD hDen_pos).le
  have hs1 : D45 x / Den ≤ 1 := (div_le_one hDen_pos).2 hDen_gt.le
  have ht0 : 0 ≤ D45 x / Den * oblX6 x 4 := (mul_pos (div_pos hD hDen_pos) hc4).le
  have ht1 : D45 x / Den * oblX6 x 4 ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one hDen_pos]; exact hDen_b
  have hγ : 0 < oblX2 x 4 / Den := div_pos hb4 hDen_pos
  have hden_ne : Den ≠ 0 := hDen_pos.ne'
  refine ⟨D45 x / Den, D45 x / Den * oblX6 x 4, oblX2 x 4 / Den, hs0, hs1, ht0, ht1, hγ, ?_⟩
  have c0 : D45 x / Den * oblX0 x 4 - 1 + D45 x / Den * oblX6 x 4 = oblX2 x 4 / Den * (-nB x) := by
    field_simp; rw [hDen]; ring
  have c2 : D45 x / Den * oblX2 x 4 = oblX2 x 4 / Den * D45 x := by ring
  have c6 : D45 x / Den * oblX6 x 4 - D45 x / Den * oblX6 x 4 = 0 := by ring
  have hx4 := frame_rep F 4
  have e : x 1 + (D45 x / Den) • (x 4 - x 1) - (x 0 + (D45 x / Den * oblX6 x 4) • (x 6 - x 0)) =
      (D45 x / Den * oblX0 x 4 - 1 + D45 x / Den * oblX6 x 4) • (x 0 - x 1) +
      (D45 x / Den * oblX2 x 4) • (x 2 - x 1) +
      (D45 x / Den * oblX6 x 4 - D45 x / Den * oblX6 x 4) • (x 6 - x 1) := by
    rw [hx4]
    simp only [add_sub_cancel_left]
    module
  rw [e, c0, c2, c6]
  simp only [v30]
  module


/-- Front diagonal `1-5` over `0-2` at `v31` (rim `(1,0,5,2)`, `nC > 0`, `b4 < b3 < b5`):
`z5 >= z2`, `z5 >= z0`, `z1 >= z2` (= `v31_bound`), `z1 >= z0`, all at `v31`. -/
theorem v31_front_bounds {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (hnc : F.f 3 (x 1) < F.f 3 (x 6)) (hb : oblX2 x 4 < oblX2 x 3)
    (h35 : oblX2 x 3 < oblX2 x 5) (hL : ¬ LexAny F) :
    0 ≤ ⟪x 5 - x 2, v31 x⟫ ∧ 0 ≤ ⟪x 5 - x 0, v31 x⟫ ∧
      0 ≤ ⟪x 1 - x 2, v31 x⟫ ∧ 0 ≤ ⟪x 1 - x 0, v31 x⟫ := by
  have hfac := v31_facings F hC hnc hb
  have htilt := v31_tilt F
  have hdiag := v31_frontDiag F hnc
  have core : ∀ U Dn : Finset (Fin 9), S0xCycUD (k := 4) s0x_S24 (![0, 1, 2, 5] : ZMod 4 → Fin 7) U Dn →
      (∀ t ∈ U, LexPos3 ⟪F.N t, v31 x⟫ ⟪F.N t, x 0 - x 2⟫ ⟪F.N t, (0 : ℝ³)⟫) →
      (∀ t ∈ Dn, LexPos3 (-⟪F.N t, v31 x⟫) (-⟪F.N t, x 0 - x 2⟫) (-⟪F.N t, (0 : ℝ³)⟫)) →
      0 ≤ ⟪x 5 - x 2, v31 x⟫ ∧ 0 ≤ ⟪x 5 - x 0, v31 x⟫ ∧
        0 ≤ ⟪x 1 - x 2, v31 x⟫ ∧ 0 ≤ ⟪x 1 - x 0, v31 x⟫ := by
    intro U Dn hcyc hU hD
    have W : ∀ i j : ZMod 4, (j, i) ∈ Minimality.RimCell.diagPairs →
        0 ≤ ⟪x ((![0, 1, 2, 5] : ZMod 4 → Fin 7) i) - x ((![0, 1, 2, 5] : ZMod 4 → Fin 7) j), v31 x⟫ :=
      fun i j hij => weak_shadow_of_frontDiag F (![0, 1, 2, 5] : ZMod 4 → Fin 7)
        (by intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide))
        U Dn hcyc (v31 x) (x 0 - x 2) 0 hU hD hdiag hij hL
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [Matrix.cons_val] using W 3 2 (by decide)
    · simpa only [Matrix.cons_val] using W 3 0 (by decide)
    · simpa only [Matrix.cons_val] using W 1 2 (by decide)
    · simpa only [Matrix.cons_val] using W 1 0 (by decide)
  apply core {1, 3, 4, 5, 6, 7, 8} {0, 2} (by unfold S0xCycUD; decide)
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr ⟨hfac.2.1, Or.inl htilt.1⟩
    · exact Or.inr ⟨hfac.2.2.2.1, Or.inl htilt.2.1⟩
    · exact Or.inl hfac.2.2.2.2.1
    · exact Or.inl hfac.2.2.2.2.2.1
    · exact Or.inl (hfac.2.2.2.2.2.2.2.2.1 h35)
    · exact Or.inl hfac.2.2.2.2.2.2.1
    · exact Or.inl hfac.2.2.2.2.2.2.2.1
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact Or.inl (by linarith [hfac.1])
    · exact Or.inl (by linarith [hfac.2.2.1])

/-- Front diagonal `1-4` over `0-6` at `v30` (rim `(1,0,4,6)`, `nB > 0`, `c5 < c3 < c4`):
`z4 >= z6`, `z4 >= z0`, `z1 >= z6` (= `v30_bound`), `z1 >= z0`, all at `v30`. -/
theorem v30_front_bounds {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (hnb : F.f 3 (x 1) < F.f 3 (x 2)) (hc : oblX6 x 5 < oblX6 x 3)
    (h34 : oblX6 x 3 < oblX6 x 4) (hL : ¬ LexAny F) :
    0 ≤ ⟪x 4 - x 6, v30 x⟫ ∧ 0 ≤ ⟪x 4 - x 0, v30 x⟫ ∧
      0 ≤ ⟪x 1 - x 6, v30 x⟫ ∧ 0 ≤ ⟪x 1 - x 0, v30 x⟫ := by
  have hfac := v30_facings F hC hnb hc
  have htilt := v30_tilt F
  have hdiag := v30_frontDiag F hnb
  have core : ∀ U Dn : Finset (Fin 9), S0xCycUD (k := 4) s0x_S24 (![0, 1, 6, 4] : ZMod 4 → Fin 7) U Dn →
      (∀ t ∈ U, LexPos3 ⟪F.N t, v30 x⟫ ⟪F.N t, x 0 - x 6⟫ ⟪F.N t, (0 : ℝ³)⟫) →
      (∀ t ∈ Dn, LexPos3 (-⟪F.N t, v30 x⟫) (-⟪F.N t, x 0 - x 6⟫) (-⟪F.N t, (0 : ℝ³)⟫)) →
      0 ≤ ⟪x 4 - x 6, v30 x⟫ ∧ 0 ≤ ⟪x 4 - x 0, v30 x⟫ ∧
        0 ≤ ⟪x 1 - x 6, v30 x⟫ ∧ 0 ≤ ⟪x 1 - x 0, v30 x⟫ := by
    intro U Dn hcyc hU hD
    have W : ∀ i j : ZMod 4, (j, i) ∈ Minimality.RimCell.diagPairs →
        0 ≤ ⟪x ((![0, 1, 6, 4] : ZMod 4 → Fin 7) i) - x ((![0, 1, 6, 4] : ZMod 4 → Fin 7) j), v30 x⟫ :=
      fun i j hij => weak_shadow_of_frontDiag F (![0, 1, 6, 4] : ZMod 4 → Fin 7)
        (by intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide))
        U Dn hcyc (v30 x) (x 0 - x 6) 0 hU hD hdiag hij hL
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [Matrix.cons_val] using W 3 2 (by decide)
    · simpa only [Matrix.cons_val] using W 3 0 (by decide)
    · simpa only [Matrix.cons_val] using W 1 2 (by decide)
    · simpa only [Matrix.cons_val] using W 1 0 (by decide)
  apply core {0, 2, 3, 5, 6, 7, 8} {1, 4} (by unfold S0xCycUD; decide)
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr ⟨hfac.1, Or.inl htilt.1⟩
    · exact Or.inl hfac.2.2.1
    · exact Or.inr ⟨hfac.2.2.2.1, Or.inl htilt.2.1⟩
    · exact Or.inl hfac.2.2.2.2.2.1
    · exact Or.inl hfac.2.2.2.2.2.2.1
    · exact Or.inl hfac.2.2.2.2.2.2.2.1
    · exact Or.inl (hfac.2.2.2.2.2.2.2.2.1 h34)
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact Or.inl (by linarith [hfac.2.1])
    · exact Or.inl (by linarith [hfac.2.2.2.2.1])

end Minimality.T24.A10
