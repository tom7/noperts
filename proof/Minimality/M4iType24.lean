module

public import Minimality.M4hType24
public import Minimality.M4fType24
public import Minimality.M4Sym24
public import Minimality.GenQuad

@[expose] public section

/-!
# Type 24: A19 lemmas, part 1 (A19-REFEREE section 4: S1-S5, S8)

`nBC_pos` (a4 < 1 or a5 < 1 => nB > 0 or nC > 0), `nu235c_pos`, `nu346b_pos` (facet signs from the brackets),
`e16_sym` (at e_c with 0345 and 235 up, not LexAny => gac, gbc <= 0), `e12_sym` (sym24 twin), `v53_bound`
(Lemma V53-Q4, front pair with Gamma = nC Br > 0).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

open scoped RealInnerProductSpace
open Finset Filter

namespace Minimality.T24.A19

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell
  Minimality.LexCell Minimality.Split Minimality.T24.M4 Minimality.T24.A7 Minimality.T24.A8
  Minimality.T24.Sym

/-- S3 (I3 consequence): `nB > 0 ∨ nC > 0` when `a4 < 1 ∨ a5 < 1`. -/
theorem nBC_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (h : oblX0 x 4 < 1 ∨ oblX0 x 5 < 1) : 0 < nB x ∨ 0 < nC x := by
  have T := type24OfFac F
  have hD := d45_pos F
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc4 : 0 < oblX6 x 4 := T.X6_pos (v := 4) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have i1 : oblX2 x 4 * nB x + oblX6 x 4 * nC x = D45 x * (1 - oblX0 x 4) := by
    dsimp [nB, nC, D45]; ring
  have i2 : oblX2 x 5 * nB x + oblX6 x 5 * nC x = D45 x * (1 - oblX0 x 5) := by
    dsimp [nB, nC, D45]; ring
  by_contra hcon
  push Not at hcon
  obtain ⟨hB, hC⟩ := hcon
  rcases h with h | h
  · have := mul_pos hD (sub_pos.mpr h)
    nlinarith [mul_nonneg hb4.le (neg_nonneg.mpr hB), mul_nonneg hc4.le (neg_nonneg.mpr hC)]
  · have := mul_pos hD (sub_pos.mpr h)
    nlinarith [mul_nonneg hb5.le (neg_nonneg.mpr hB), mul_nonneg hc5.le (neg_nonneg.mpr hC)]

/-- S1 (I1): `nu235c > 0` as the facing of `235` at `e_c`. -/
theorem nu235c_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (h1356 : 0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3) (hnc : 0 ≤ nC x) :
    F.f 6 (x 1) < F.f 6 (x 6) := by
  have T := type24OfFac F
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have ha5 : 0 < oblX0 x 5 := T.X0_pos (v := 5) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hom3 : 0 < omega3 x := hC.1
  have hom5 : 0 < omega5 x := hC.2.2.1
  obtain ⟨s, t, hs, ht, -, h0, h2, h6⟩ := lemmaM_coords F
  have e3 := eq3 F
  have e5 := eq5 F
  have hsum : 0 < oblX0 x 5 + oblX2 x 5 - 1 := by
    rw [e5]; exact mul_pos hom5 hc5
  -- I1
  have I1 : oblX2 x 5 * (oblX0 x 5 * (1 - oblX2 x 3) - oblX0 x 3 * (1 - oblX2 x 5)) =
      (oblX0 x 5 + oblX2 x 5 - 1) * (oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3) +
        s * oblX0 x 5 * nC x := by
    have ha : oblX0 x 3 = 1 + s * (oblX0 x 4 - 1) + t * (oblX0 x 5 - 1) := by linarith
    rw [ha, h2]; dsimp [nC]; ring
  have hnu : 0 < oblX0 x 5 * (1 - oblX2 x 3) - oblX0 x 3 * (1 - oblX2 x 5) := by
    have : 0 < oblX2 x 5 * (oblX0 x 5 * (1 - oblX2 x 3) - oblX0 x 3 * (1 - oblX2 x 5)) := by
      rw [I1]; nlinarith [mul_pos hsum h1356, mul_nonneg (mul_pos hs ha5).le hnc]
    exact pos_of_mul_pos_right this hb5.le
  -- n_y > nu
  have hlt := T.lt236 (v := 5) (by decide)
  have hny : (oblX0 x 5 * oblX6 x 3 - oblX0 x 3 * oblX6 x 5) >
      oblX0 x 5 * (1 - oblX2 x 3) - oblX0 x 3 * (1 - oblX2 x 5) := by
    nlinarith [mul_pos ha3 (sub_pos.mpr hlt)]
  -- plane relation
  have P := F.neg 6 1 (by decide)
  have f2 := F.zero 6 2 (by decide)
  have f3 := F.zero 6 3 (by decide)
  have f5 := F.zero 6 5 (by decide)
  have ev3 := fac_eval F 6 3
  have ev5 := fac_eval F 6 5
  rw [f3, f2] at ev3
  rw [f5, f2] at ev5
  have key : (F.f 6 (x 6) - F.f 6 (x 1)) * (oblX0 x 5 * oblX6 x 3 - oblX0 x 3 * oblX6 x 5) =
      (-F.f 6 (x 1)) * (oblX0 x 5 * (1 - oblX2 x 3) - oblX0 x 3 * (1 - oblX2 x 5)) := by
    linear_combination oblX0 x 3 * ev5 - oblX0 x 5 * ev3
  by_contra hcon
  push Not at hcon
  have hny' : 0 < oblX0 x 5 * oblX6 x 3 - oblX0 x 3 * oblX6 x 5 := by linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hcon) hny'.le, mul_pos (neg_pos.mpr P) hnu]

/-- S2 (I2): `nu346b > 0` as the facing of `346` at `e_b`. -/
theorem nu346b_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (h1234 : oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0) (hnb : 0 ≤ nB x) :
    F.f 8 (x 1) < F.f 8 (x 2) := by
  have T := type24OfFac F
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have ha4 : 0 < oblX0 x 4 := T.X0_pos (v := 4) (by decide)
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hc4 : 0 < oblX6 x 4 := T.X6_pos (v := 4) (by decide)
  have hom4 : 0 < omega4 x := hC.2.1
  obtain ⟨s, t, hs, ht, -, h0, h2, h6⟩ := lemmaM_coords F
  have e4 := T.eq4
  have hsum : 0 < oblX0 x 4 + oblX6 x 4 - 1 := by
    have : oblX0 x 4 + oblX6 x 4 - 1 = omega4 x * oblX2 x 4 := by linarith
    rw [this]; exact mul_pos hom4 hb4
  have I2 : oblX6 x 4 * (oblX0 x 4 * (1 - oblX6 x 3) - oblX0 x 3 * (1 - oblX6 x 4)) =
      (oblX0 x 4 + oblX6 x 4 - 1) * (-(oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4)) +
        t * oblX0 x 4 * nB x := by
    have ha : oblX0 x 3 = 1 + s * (oblX0 x 4 - 1) + t * (oblX0 x 5 - 1) := by linarith
    rw [ha, h6]; dsimp [nB]; ring
  have hnu : 0 < oblX0 x 4 * (1 - oblX6 x 3) - oblX0 x 3 * (1 - oblX6 x 4) := by
    have : 0 < oblX6 x 4 * (oblX0 x 4 * (1 - oblX6 x 3) - oblX0 x 3 * (1 - oblX6 x 4)) := by
      rw [I2]; nlinarith [mul_pos hsum (neg_pos.mpr h1234), mul_nonneg (mul_pos ht ha4).le hnb]
    exact pos_of_mul_pos_right this hc4.le
  have hlt := T.lt236 (v := 4) (by decide)
  have e3 := eq3 F
  have hm : (oblX0 x 4 * oblX2 x 3 - oblX0 x 3 * oblX2 x 4) >
      oblX0 x 4 * (1 - oblX6 x 3) - oblX0 x 3 * (1 - oblX6 x 4) := by
    have hom3 : 0 < omega3 x := hC.1
    nlinarith [mul_pos ha3 (sub_pos.mpr hlt)]
  have P := F.neg 8 1 (by decide)
  have f3 := F.zero 8 3 (by decide)
  have f4 := F.zero 8 4 (by decide)
  have f6 := F.zero 8 6 (by decide)
  have ev3 := fac_eval F 8 3
  have ev4 := fac_eval F 8 4
  rw [f3, f6] at ev3
  rw [f4, f6] at ev4
  have key : (F.f 8 (x 2) - F.f 8 (x 1)) * (oblX0 x 4 * oblX2 x 3 - oblX0 x 3 * oblX2 x 4) =
      (-F.f 8 (x 1)) * (oblX0 x 4 * (1 - oblX6 x 3) - oblX0 x 3 * (1 - oblX6 x 4)) := by
    linear_combination oblX0 x 3 * ev4 - oblX0 x 4 * ev3
  by_contra hcon
  push Not at hcon
  have hm' : 0 < oblX0 x 4 * oblX2 x 3 - oblX0 x 3 * oblX2 x 4 := by linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hcon) hm'.le, mul_pos (neg_pos.mpr P) hnu]

/-- S4 (Lemma E16-Sym): the `e10_sym` argument at `e_c` (rim `![1, 0, 5, 2]`). -/
theorem e16_sym {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (hnc : F.f 3 (x 1) < F.f 3 (x 6)) (h235 : F.f 6 (x 1) < F.f 6 (x 6))
    (hU : ¬ LexAny F) :
    ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0 ∧ ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0 := by
  have T := type24OfFac F
  by_contra hcon
  have hpos : 0 < ⟪x 0 - x 1, x 6 - x 1⟫ ∨ 0 < ⟪x 2 - x 1, x 6 - x 1⟫ := by
    by_contra h; push Not at h; exact hcon ⟨h.1, h.2⟩
  have hC6 : 0 < ⟪x 6 - x 1, x 6 - x 1⟫ :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide))
  have ha5 : 0 < oblX0 x 5 := T.X0_pos (v := 5) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hab : 1 < oblX0 x 5 + oblX2 x 5 := by
    have := eq5 F
    have := hC.2.2.1
    nlinarith
  have hz5 : ⟪x 5 - x 1, x 6 - x 1⟫ = oblX0 x 5 * ⟪x 0 - x 1, x 6 - x 1⟫ +
      oblX2 x 5 * ⟪x 2 - x 1, x 6 - x 1⟫ + oblX6 x 5 * ⟪x 6 - x 1, x 6 - x 1⟫ := by
    have h' : x 5 - x 1 = oblX0 x 5 • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) +
        oblX6 x 5 • (x 6 - x 1) := by
      rw [sub_eq_iff_eq_add']
      refine (T.rep 5).trans ?_
      abel
    rw [h', inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_left]
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
  have hN6 : 0 < ⟪F.N 6, x 6 - x 1⟫ := by rw [← F.hN]; linarith
  have hN4 : 0 < ⟪F.N 4, x 6 - x 1⟫ := by
    rw [← F.hN, F.zero 4 6 (by decide)]; linarith [F.neg 4 1 (by decide)]
  have hN7 : 0 < ⟪F.N 7, x 6 - x 1⟫ := by
    rw [← F.hN, F.zero 7 6 (by decide)]; linarith [F.neg 7 1 (by decide)]
  have hN8 : 0 < ⟪F.N 8, x 6 - x 1⟫ := by
    rw [← F.hN, F.zero 8 6 (by decide)]; linarith [F.neg 8 1 (by decide)]
  have hD1 : 0 < ⟪F.N 1, -(x 0 - x 1) - (x 2 - x 1)⟫ := by
    rw [inner_sub_right, inner_neg_right, ← F.hN, ← F.hN, F.zero 1 0 (by decide),
      F.zero 1 1 (by decide)]
    linarith [F.neg 1 2 (by decide)]
  have hD5 : 0 < ⟪F.N 5, -(x 0 - x 1) - (x 2 - x 1)⟫ := by
    rw [inner_sub_right, inner_neg_right, ← F.hN, ← F.hN, F.zero 5 2 (by decide),
      F.zero 5 1 (by decide)]
    linarith [F.neg 5 0 (by decide)]
  apply hU
  refine ⟨4, inferInstance, (![1, 0, 5, 2] : ZMod 4 → Fin 7), {1, 3, 4, 5, 6, 7, 8}, {0, 2},
    x 6 - x 1, -(x 0 - x 1) - (x 2 - x 1), 0, by decide,
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
    have g0 := hz 0
    have g2 := hz 2
    have g5 := hz 5
    rw [hz5] at g5
    refine robUniLex_four_of_mixed ?_ ?_
    · rcases hpos with h | h
      · exact ⟨((0 : ZMod 4), (1 : ZMod 4)), by decide,
          Or.inl (by dsimp only [Matrix.cons_val]; linarith)⟩
      · exact ⟨((0 : ZMod 4), (3 : ZMod 4)), by decide,
          Or.inl (by dsimp only [Matrix.cons_val]; linarith)⟩
    · rcases lt_or_ge ⟪x 0 - x 1, x 6 - x 1⟫ 0 with h | h
      · exact ⟨((0 : ZMod 4), (1 : ZMod 4)), by decide,
          Or.inl (by dsimp only [Matrix.cons_val]; linarith)⟩
      rcases lt_or_ge ⟪x 2 - x 1, x 6 - x 1⟫ 0 with h' | h'
      · exact ⟨((0 : ZMod 4), (3 : ZMod 4)), by decide,
          Or.inl (by dsimp only [Matrix.cons_val]; linarith)⟩
      have key : ⟪x 0 - x 1, x 6 - x 1⟫ < ⟪x 5, x 6 - x 1⟫ - ⟪x 1, x 6 - x 1⟫ ∨
          ⟪x 2 - x 1, x 6 - x 1⟫ < ⟪x 5, x 6 - x 1⟫ - ⟪x 1, x 6 - x 1⟫ := by
        by_contra hk
        push Not at hk
        obtain ⟨k1, k2⟩ := hk
        have hp : 0 < ⟪x 5, x 6 - x 1⟫ - ⟪x 1, x 6 - x 1⟫ := by
          rw [g5]; nlinarith [mul_pos hc5 hC6, mul_nonneg ha5.le h, mul_nonneg hb5.le h']
        nlinarith [mul_nonneg ha5.le (sub_nonneg.mpr k1), mul_nonneg hb5.le (sub_nonneg.mpr k2),
          mul_pos (sub_pos.mpr hab) hp, mul_pos hc5 hC6]
      rcases key with k | k
      · exact ⟨((2 : ZMod 4), (1 : ZMod 4)), by decide,
          Or.inl (by dsimp only [Matrix.cons_val]; linarith)⟩
      · exact ⟨((2 : ZMod 4), (3 : ZMod 4)), by decide,
          Or.inl (by dsimp only [Matrix.cons_val]; linarith)⟩

/-- S5 (Lemma E12-Sym): the `Sym24` twin of `e16_sym`. -/
theorem e12_sym {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (hnb : F.f 3 (x 1) < F.f 3 (x 2)) (h346 : F.f 8 (x 1) < F.f 8 (x 2))
    (hU : ¬ LexAny F) :
    ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0 ∧ ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0 := by
  have h := e16_sym (sym24 F) ((cbarIn_comp_pi24 x).2 hC)
    (by simpa [sym24_f_apply] using hnb)
    (by simpa [sym24_f_apply] using h346)
    (fun h => hU (lexAny_sym F h))
  simpa [Function.comp_apply, real_inner_comm] using h

/-! ### S8: `v53_bound` -/

open Minimality.T24.A15

private theorem fac3_lin' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    (-F.f 3 (x 1)) * nC x = (F.f 3 (x 6) - F.f 3 (x 1)) * D45 x := by
  have f3_0 : F.f 3 (x 0) = 0 := F.zero 3 0 (by decide)
  have f3_4 : F.f 3 (x 4) = 0 := F.zero 3 4 (by decide)
  have f3_5 : F.f 3 (x 5) = 0 := F.zero 3 5 (by decide)
  have ev4 := fac_eval F 3 4
  have ev5 := fac_eval F 3 5
  rw [f3_4, f3_0] at ev4
  rw [f3_5, f3_0] at ev5
  dsimp [nC, D45]
  linear_combination oblX2 x 5 * ev4 - oblX2 x 4 * ev5

private theorem hrep0' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (v : Fin 7) :
    x v - x 0 = (oblX0 x v - 1) • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1) := by
  have T := type24OfFac F
  calc x v - x 0 = (x v - x 1) - (x 0 - x 1) := by abel
    _ = (oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1)) -
        (x 0 - x 1) := by rw [T.rep v]; abel
    _ = _ := by module

private theorem hrep1' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (v : Fin 7) :
    x v - x 1 = oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1) := by
  have T := type24OfFac F
  rw [T.rep v]; abel

theorem u53_inner {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) :
    ⟪F.N t, u53 x⟫ = (oblX0 x 5 - 1) * (F.f t (x 4) - F.f t (x 0)) +
      (1 - oblX0 x 4) * (F.f t (x 5) - F.f t (x 0)) := by
  have hr : u53 x = (oblX0 x 5 - 1) • (x 4 - x 0) + (1 - oblX0 x 4) • (x 5 - x 0) := by
    rw [hrep0' F 4, hrep0' F 5]; dsimp [u53, nC, nB]; module
  rw [hr, inner_add_right, inner_smul_right, inner_smul_right,
    ← F.hN t (x 4) (x 0), ← F.hN t (x 5) (x 0)]

theorem u53_inner' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) :
    ⟪F.N t, u53 x⟫ = nC x * (F.f t (x 2) - F.f t (x 1)) - nB x * (F.f t (x 6) - F.f t (x 1)) := by
  dsimp only [u53]
  rw [inner_sub_right, inner_smul_right, inner_smul_right,
    ← F.hN t (x 2) (x 1), ← F.hN t (x 6) (x 1)]

theorem u53_inner2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) (s τ : ℝ)
    (hdec : x 3 - x 0 = s • (x 4 - x 0) + τ • (x 5 - x 0))
    (h0 : oblX0 x 3 - 1 = s * (oblX0 x 4 - 1) + τ * (oblX0 x 5 - 1)) :
    (s - 1) * ⟪F.N t, u53 x⟫ = (oblX0 x 5 - 1) * (F.f t (x 3) - F.f t (x 4)) +
      (oblX0 x 4 - oblX0 x 3) * (F.f t (x 5) - F.f t (x 0)) := by
  have h := congrArg (fun w => ⟪F.N t, w⟫) hdec
  simp only [inner_add_right, inner_smul_right] at h
  rw [← F.hN t (x 3) (x 0), ← F.hN t (x 4) (x 0), ← F.hN t (x 5) (x 0)] at h
  rw [u53_inner F t]
  linear_combination (-(oblX0 x 5 - 1)) * h + (F.f t (x 5) - F.f t (x 0)) * h0

theorem br_key {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    oblX0 x 3 * F.f 7 (x 5) = F.f 7 (x 1) *
      (oblX0 x 5 * (oblX2 x 3 + oblX6 x 3 - 1) - oblX0 x 3 * (oblX2 x 5 + oblX6 x 5 - 1)) := by
  have ev3 := fac_eval F 7 3
  have ev5 := fac_eval F 7 5
  rw [F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at ev3
  rw [F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at ev5
  linear_combination oblX0 x 3 * ev5 - oblX0 x 5 * ev3

theorem v53_front {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha5 : 1 < oblX0 x 5) (ha : oblX0 x 3 < oblX0 x 4) (ha4 : oblX0 x 4 < 1) :
    FrontDiag (x 2) (x 3) (x 5) (x 6) (u53 x) := by
  have T := type24OfFac F
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc4 : 0 < oblX6 x 4 := T.X6_pos (v := 4) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hD : 0 < D45 x := d45_pos F
  have hnB : nB x < 0 := by dsimp [nB]; nlinarith
  have hnC : 0 < nC x := by dsimp [nC]; nlinarith
  have hnCD : nC x < D45 x := by
    have h1 : F.f 3 (x 1) < 0 := F.neg 3 1 (by decide)
    have h6 : F.f 3 (x 6) < 0 := F.neg 3 6 (by decide)
    have hl := fac3_lin' F
    have hp : 0 < (-F.f 3 (x 6)) * D45 x := mul_pos (by linarith) hD
    by_contra hcon
    push Not at hcon
    nlinarith [mul_nonneg (neg_nonneg.mpr h1.le) (sub_nonneg.mpr hcon)]
  -- Br > 0
  have hBr : 0 < oblX0 x 5 * (oblX2 x 3 + oblX6 x 3 - 1) - oblX0 x 3 * (oblX2 x 5 + oblX6 x 5 - 1) := by
    have key := br_key F
    have h7 : F.f 7 (x 5) < 0 := F.neg 7 5 (by decide)
    have h1 : F.f 7 (x 1) < 0 := F.neg 7 1 (by decide)
    by_contra hcon
    push Not at hcon
    nlinarith [mul_nonneg_of_nonpos_of_nonpos h1.le hcon, mul_pos ha3 (neg_pos.mpr h7)]
  have hrel := a3_rel F
  have hI5 : D45 x * (oblX0 x 5 - 1) + oblX2 x 5 * nB x + oblX6 x 5 * nC x = 0 := by
    dsimp [nB, nC, D45]; ring
  have hK : 0 < oblX0 x 5 * (D45 x - nB x) - oblX0 x 3 * (D45 x - nC x) := by
    nlinarith [mul_pos ha3 (sub_pos.mpr (lt_trans hnB hnC)), mul_pos (sub_pos.mpr (lt_trans ha (lt_trans ha4 ha5))) (sub_pos.mpr (lt_trans hnB hD))]
  set K := oblX0 x 5 * (D45 x - nB x) - oblX0 x 3 * (D45 x - nC x) with hKdef
  obtain ⟨s, hs⟩ : ∃ s, K * s = (nC x - nB x) * oblX0 x 5 := ⟨_, mul_div_cancel₀ _ hK.ne'⟩
  obtain ⟨w, hw⟩ : ∃ w, K * w = (nC x - nB x) * oblX0 x 3 := ⟨_, mul_div_cancel₀ _ hK.ne'⟩
  obtain ⟨γ, hg⟩ : ∃ γ, K * γ = oblX0 x 5 * (oblX2 x 3 + oblX6 x 3 - 1) -
      oblX0 x 3 * (oblX2 x 5 + oblX6 x 5 - 1) := ⟨_, mul_div_cancel₀ _ hK.ne'⟩
  have a5a3 : oblX0 x 3 < oblX0 x 5 := lt_trans ha (lt_trans ha4 ha5)
  have hs0 : 0 ≤ s := by
    by_contra h; push Not at h
    nlinarith [mul_pos hK (neg_pos.mpr h), mul_pos (sub_pos.mpr (lt_trans hnB hnC)) (lt_trans ha3 a5a3)]
  have hs1 : s ≤ 1 := by
    by_contra h; push Not at h
    nlinarith [mul_pos hK (sub_pos.mpr h), mul_pos (sub_pos.mpr a5a3) (sub_pos.mpr hnCD)]
  have hw0 : 0 ≤ w := by
    by_contra h; push Not at h
    nlinarith [mul_pos hK (neg_pos.mpr h), mul_pos (sub_pos.mpr (lt_trans hnB hnC)) ha3]
  have hw1 : w ≤ 1 := by
    by_contra h; push Not at h
    nlinarith [mul_pos hK (sub_pos.mpr h), mul_pos (sub_pos.mpr a5a3) (sub_pos.mpr (lt_trans hnB hD)),
      mul_pos (sub_pos.mpr (lt_trans hnB hnC)) ha3]
  have hγ : 0 < γ := by
    by_contra h; push Not at h
    nlinarith [mul_nonneg hK.le (neg_nonneg.mpr h)]
  have ca : s * oblX0 x 3 - w * oblX0 x 5 = 0 := by
    have : K * (s * oblX0 x 3 - w * oblX0 x 5) = 0 := by
      linear_combination oblX0 x 3 * hs - oblX0 x 5 * hw
    exact (mul_eq_zero.mp this).resolve_left hK.ne'
  have cb : s * oblX2 x 3 + (1 - s) - w * oblX2 x 5 - γ * nC x = 0 := by
    have : K * (s * oblX2 x 3 + (1 - s) - w * oblX2 x 5 - γ * nC x) = 0 := by
      linear_combination (oblX2 x 3 - 1) * hs - oblX2 x 5 * hw - nC x * hg - oblX0 x 5 * hrel + hKdef + oblX0 x 3 * hI5
    exact (mul_eq_zero.mp this).resolve_left hK.ne'
  have cc : s * oblX6 x 3 - w * oblX6 x 5 - (1 - w) + γ * nB x = 0 := by
    have : K * (s * oblX6 x 3 - w * oblX6 x 5 - (1 - w) + γ * nB x) = 0 := by
      linear_combination oblX6 x 3 * hs + (1 - oblX6 x 5) * hw + nB x * hg + oblX0 x 5 * hrel - hKdef - oblX0 x 3 * hI5
    exact (mul_eq_zero.mp this).resolve_left hK.ne'
  refine ⟨s, 1 - w, γ, hs0, hs1, by linarith, by linarith, hγ, ?_⟩
  have h3 := sub_eq_iff_eq_add'.mp (hrep1' F 3)
  have h5 := sub_eq_iff_eq_add'.mp (hrep1' F 5)
  have key : x 2 + s • (x 3 - x 2) - (x 5 + (1 - w) • (x 6 - x 5)) - γ • u53 x =
      (s * oblX0 x 3 - w * oblX0 x 5) • (x 0 - x 1) +
      (s * oblX2 x 3 + (1 - s) - w * oblX2 x 5 - γ * nC x) • (x 2 - x 1) +
      (s * oblX6 x 3 - w * oblX6 x 5 - (1 - w) + γ * nB x) • (x 6 - x 1) := by
    rw [h3, h5]; dsimp only [u53]; module
  rw [ca, cb, cc] at key
  simp only [zero_smul, add_zero] at key
  exact sub_eq_zero.mp key

/-- S8 (Lemma V53-Q4): front pair `(2, 3)` over `(5, 6)` at `u53`. -/
theorem v53_bound {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha5 : 1 < oblX0 x 5) (ha : oblX0 x 3 < oblX0 x 4) (ha4 : oblX0 x 4 < 1)
    (hsig : F.f 8 (x 5) < F.f 8 (x 0)) (hU : ¬ LexAny F) :
    max (z x (u53 x) 5) (z x (u53 x) 6) ≤ min (z x (u53 x) 2) (z x (u53 x) 3) := by
  have T := type24OfFac F
  by_contra hneg
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc4 : 0 < oblX6 x 4 := T.X6_pos (v := 4) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hD : 0 < D45 x := d45_pos F
  have hnB : nB x < 0 := by dsimp [nB]; nlinarith
  have hnC : 0 < nC x := by dsimp [nC]; nlinarith
  obtain ⟨σ, τ, hσ0, hτ0, hdec, h0, -, -⟩ := lemmaM_coords F
  have hf0 : F.f 8 (x 0) < 0 := F.neg 8 0 (by decide)
  have hσ1 : 1 < σ := by
    have h := congrArg (fun w => ⟪F.N 8, w⟫) hdec
    simp only [inner_add_right, inner_smul_right] at h
    rw [← F.hN 8 (x 3) (x 0), ← F.hN 8 (x 4) (x 0), ← F.hN 8 (x 5) (x 0),
      F.zero 8 3 (by decide), F.zero 8 4 (by decide)] at h
    by_contra hc
    push Not at hc
    nlinarith [mul_pos hτ0 (sub_pos.mpr hsig), mul_nonneg (sub_nonneg.mpr hc) (neg_nonneg.mpr hf0.le)]
  have hσ : 0 < σ - 1 := by linarith
  -- facings at u53
  have g0 : ⟪F.N 0, u53 x⟫ < 0 := by
    rw [u53_inner F, F.zero 0 0 (by decide)]
    nlinarith [mul_neg_of_pos_of_neg (sub_pos.mpr ha5) (F.neg 0 4 (by decide)),
      mul_neg_of_pos_of_neg (sub_pos.mpr ha4) (F.neg 0 5 (by decide))]
  have g1 : ⟪F.N 1, u53 x⟫ < 0 := by
    rw [u53_inner F, F.zero 1 0 (by decide)]
    nlinarith [mul_neg_of_pos_of_neg (sub_pos.mpr ha5) (F.neg 1 4 (by decide)),
      mul_neg_of_pos_of_neg (sub_pos.mpr ha4) (F.neg 1 5 (by decide))]
  have g2 : ⟪F.N 2, u53 x⟫ < 0 := by
    rw [u53_inner F, F.zero 2 0 (by decide), F.zero 2 5 (by decide)]
    nlinarith [mul_neg_of_pos_of_neg (sub_pos.mpr ha5) (F.neg 2 4 (by decide))]
  have g3 : ⟪F.N 3, u53 x⟫ = 0 := by
    rw [u53_inner F, F.zero 3 0 (by decide), F.zero 3 4 (by decide), F.zero 3 5 (by decide)]; ring
  have g4 : ⟪F.N 4, u53 x⟫ < 0 := by
    rw [u53_inner F, F.zero 4 0 (by decide), F.zero 4 4 (by decide)]
    nlinarith [mul_neg_of_pos_of_neg (sub_pos.mpr ha4) (F.neg 4 5 (by decide))]
  have g5 : ⟪F.N 5, u53 x⟫ = 0 := by
    rw [u53_inner' F, F.zero 5 2 (by decide), F.zero 5 1 (by decide), F.zero 5 6 (by decide)]; ring
  have g6 : 0 < ⟪F.N 6, u53 x⟫ := by
    have := u53_inner2 F 6 σ τ hdec h0
    rw [F.zero 6 3 (by decide), F.zero 6 5 (by decide)] at this
    have h4 := F.neg 6 4 (by decide)
    have h0' := F.neg 6 0 (by decide)
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg hσ.le (neg_nonneg.mpr hc), mul_pos (sub_pos.mpr ha5) (neg_pos.mpr h4),
      mul_pos (sub_pos.mpr ha) (neg_pos.mpr h0')]
  have g7 : 0 < ⟪F.N 7, u53 x⟫ := by
    rw [u53_inner' F, F.zero 7 2 (by decide), F.zero 7 6 (by decide)]
    nlinarith [mul_pos (neg_pos.mpr (F.neg 7 1 (by decide))) (sub_pos.mpr (lt_trans hnB hnC))]
  have g8 : ⟪F.N 8, u53 x⟫ < 0 := by
    have := u53_inner2 F 8 σ τ hdec h0
    rw [F.zero 8 3 (by decide), F.zero 8 4 (by decide)] at this
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg hσ.le hc, mul_pos (sub_pos.mpr ha) (sub_pos.mpr hsig)]
  -- tilt
  have hnCD : nC x < D45 x := by
    have h1 : F.f 3 (x 1) < 0 := F.neg 3 1 (by decide)
    have h6 : F.f 3 (x 6) < 0 := F.neg 3 6 (by decide)
    have hl := fac3_lin' F
    have hp : 0 < (-F.f 3 (x 6)) * D45 x := mul_pos (by linarith) hD
    by_contra hcon
    push Not at hcon
    nlinarith [mul_nonneg (neg_nonneg.mpr h1.le) (sub_nonneg.mpr hcon)]
  have hd3 : ⟪F.N 3, (x 0 - x 1) - (2 * D45 x / nC x) • (x 6 - x 1)⟫ < 0 := by
    rw [inner_sub_right, inner_smul_right, ← F.hN 3 (x 0) (x 1), ← F.hN 3 (x 6) (x 1),
      F.zero 3 0 (by decide)]
    have hl := fac3_lin' F
    have h1 : F.f 3 (x 1) < 0 := F.neg 3 1 (by decide)
    have : (2 * D45 x / nC x) * (F.f 3 (x 6) - F.f 3 (x 1)) = 2 * (-F.f 3 (x 1)) := by
      field_simp; linear_combination (-1) * hl
    rw [this]; linarith
  have hd5 : ⟪F.N 5, (x 0 - x 1) - (2 * D45 x / nC x) • (x 6 - x 1)⟫ < 0 := by
    rw [inner_sub_right, inner_smul_right, ← F.hN 5 (x 0) (x 1), ← F.hN 5 (x 6) (x 1),
      F.zero 5 6 (by decide), F.zero 5 1 (by decide)]
    linarith [F.neg 5 0 (by decide)]
  have hu0 : u53 x ≠ 0 := by
    intro h; rw [h, inner_zero_right] at g7; exact lt_irrefl _ g7
  have hfront := (v53_front F ha5 ha ha4).not_back hu0
  have hz : ∀ v, ⟪x v, u53 x⟫ - ⟪x 1, u53 x⟫ = z x (u53 x) v := by
    intro v; simp only [z, inner_sub_left]
  have hz2 := hz 2
  have hz3 := hz 3
  have hz5 := hz 5
  have hz6 := hz 6
  have hneg' : z x (u53 x) 2 < z x (u53 x) 5 ∨ z x (u53 x) 3 < z x (u53 x) 5 ∨
      z x (u53 x) 2 < z x (u53 x) 6 ∨ z x (u53 x) 3 < z x (u53 x) 6 := by
    by_contra h; push Not at h
    exact hneg (max_le (le_min h.1 h.2.1) (le_min h.2.2.1 h.2.2.2))
  have hfront' : ⟪x 5, u53 x⟫ < ⟪x 2, u53 x⟫ ∨ ⟪x 6, u53 x⟫ < ⟪x 2, u53 x⟫ ∨
      ⟪x 5, u53 x⟫ < ⟪x 3, u53 x⟫ ∨ ⟪x 6, u53 x⟫ < ⟪x 3, u53 x⟫ := by
    by_contra h; push Not at h
    exact hfront (max_le (le_min h.1 h.2.1) (le_min h.2.2.1 h.2.2.2))
  apply hU
  refine ⟨4, inferInstance, (![2, 5, 3, 6] : ZMod 4 → Fin 7), {6, 7}, {0, 1, 2, 3, 4, 5, 8},
    u53 x, (x 0 - x 1) - (2 * D45 x / nC x) • (x 6 - x 1), 0, by decide,
    (by intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)),
    (by unfold S0xCycUD; decide), ?_, ?_, ?_⟩
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact Or.inl g6
    · exact Or.inl g7
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, Or.inl (by linarith)⟩
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, Or.inl (by linarith)⟩
    · exact Or.inl (by linarith)
  · refine robUniLex_four_of_mixed ?_ ?_
    · rcases hneg' with h | h | h | h
      · exact ⟨((0 : ZMod 4), (1 : ZMod 4)), by decide,
          Or.inl (by dsimp only [Matrix.cons_val]; linarith)⟩
      · exact ⟨((2 : ZMod 4), (1 : ZMod 4)), by decide,
          Or.inl (by dsimp only [Matrix.cons_val]; linarith)⟩
      · exact ⟨((0 : ZMod 4), (3 : ZMod 4)), by decide,
          Or.inl (by dsimp only [Matrix.cons_val]; linarith)⟩
      · exact ⟨((2 : ZMod 4), (3 : ZMod 4)), by decide,
          Or.inl (by dsimp only [Matrix.cons_val]; linarith)⟩
    · rcases hfront' with h | h | h | h
      all_goals first
        | exact ⟨((0 : ZMod 4), (1 : ZMod 4)), by decide,
            Or.inl (by dsimp only [Matrix.cons_val]; linarith)⟩
        | exact ⟨((2 : ZMod 4), (1 : ZMod 4)), by decide,
            Or.inl (by dsimp only [Matrix.cons_val]; linarith)⟩
        | exact ⟨((0 : ZMod 4), (3 : ZMod 4)), by decide,
            Or.inl (by dsimp only [Matrix.cons_val]; linarith)⟩
        | exact ⟨((2 : ZMod 4), (3 : ZMod 4)), by decide,
            Or.inl (by dsimp only [Matrix.cons_val]; linarith)⟩

end Minimality.T24.A19
