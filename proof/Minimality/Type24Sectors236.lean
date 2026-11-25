module

public import Minimality.Type24HiddenCone
public import Minimality.RimCellClosed
public import Minimality.RDispatch24
public import Minimality.Type24SAT.Geo.Top

/-!
# Type 24: the chord-23 and chord-36 4-rims `0.2.3.4` and `0.5.3.6` of circle `236`

Formalizes the closed-cell region lemmas (`(i)`) and Q4 leaves (`(ii)`) for the two 4-rim sectors
of circle `236` (`0 2 3 4` = chord-23 sector `s > 1`, `0 5 3 6` = chord-36 sector `s < 0`) in
`Minimality.T24.EI`.
-/

@[expose] public section

set_option autoImplicit false

open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.EI

open Minimality Minimality.H21 Minimality.T24.SAT Minimality.RimCell Minimality.T24.HC

variable {x : Fin 7 → ℝ³}

/-! ## Cells and cycles -/

/-- Up facets of the cell of rim `0 2 3 4`: `025, 0345, 235`. -/
def UA : Finset (Fin 9) := {2, 3, 6}
/-- Down facets of the cell of rim `0 2 3 4`: `012, 016, 046, 126, 236, 346`. -/
def DnA : Finset (Fin 9) := {0, 1, 4, 5, 7, 8}
/-- Rim cycle `0 2 3 4`. -/
def cA : ZMod 4 → Fin 7 := ![0, 2, 3, 4]

/-- Up facets of the cell of rim `0 5 3 6`: `0345, 046, 346`. -/
def UB : Finset (Fin 9) := {3, 4, 8}
/-- Down facets of the cell of rim `0 5 3 6`: `012, 016, 025, 126, 235, 236`. -/
def DnB : Finset (Fin 9) := {0, 1, 2, 5, 6, 7}
/-- Rim cycle `0 5 3 6`. -/
def cB : ZMod 4 → Fin 7 := ![0, 5, 3, 6]

theorem cycA : S0xCycUD s0x_S24 cA UA DnA := by decide
theorem cycB : S0xCycUD s0x_S24 cB UB DnB := by decide

theorem injA : Function.Injective cA := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)
theorem injB : Function.Injective cB := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)

/-! ## The pivot views and the endpoints -/

/-- The pivot view `d_s = x 3 - ((1 - s) x 2 + s x 6)` (= `u_32 + s (x 2 - x 6)`). -/
noncomputable def pivotView (x : Fin 7 → ℝ³) (s : ℝ) : ℝ³ := x 3 - ((1 - s) • x 2 + s • x 6)

/-- The root in `s` of the affine function `s ↦ ⟪F.N t, d_s⟫`
(`⟪F.N t, d_s⟫ = ⟪F.N t, x 3 - x 2⟫ + s ⟪F.N t, x 2 - x 6⟫`; the divisor is nonzero at every use gated). -/
noncomputable def sRoot (F : S0xFac 9 s0x_S24 x) (t : Fin 9) : ℝ :=
  -⟪F.N t, x 3 - x 2⟫ / ⟪F.N t, x 2 - x 6⟫

/-- Left end of the chord-23 sector (rim `0 2 3 4`): `s = 1` (`u_36`) if `025` is weakly front there, else `s_27`
(view `M27`). -/
noncomputable def sLA (F : S0xFac 9 s0x_S24 x) : ℝ :=
  if 0 ≤ ⟪F.N 2, x 3 - x 6⟫ then 1 else sRoot F 2
/-- Right end of the chord-23 sector: `s = c3` (`c_oo`) if `0345` is weakly front there, else the `0345` flip
`s_3` (view `M73^+`). -/
noncomputable def sRA (F : S0xFac 9 s0x_S24 x) : ℝ :=
  if 0 ≤ ⟪F.N 3, pivotView x (oblX6 x 3)⟫ then oblX6 x 3 else sRoot F 3
/-- Left end of the chord-36 sector (rim `0 5 3 6`): `s = 1 - b3` (`c_0`) if `0345` is weakly front there, else the
`0345` flip `s_3` (view `M73^-`). -/
noncomputable def sLB (F : S0xFac 9 s0x_S24 x) : ℝ :=
  if 0 ≤ ⟪F.N 3, pivotView x (1 - oblX2 x 3)⟫ then 1 - oblX2 x 3 else sRoot F 3
/-- Right end of the chord-36 sector: `s = 0` (`u_32`) if `046` is weakly front there, else `s_74` (view `M74`). -/
noncomputable def sRB (F : S0xFac 9 s0x_S24 x) : ℝ :=
  if 0 ≤ ⟪F.N 4, x 3 - x 2⟫ then 0 else sRoot F 4

/-! ## Private affine helpers on `pivotView` -/

private theorem pivotView_eq (x : Fin 7 → ℝ³) (s : ℝ) :
    pivotView x s = (x 3 - x 2) + s • (x 2 - x 6) := by
  dsimp [pivotView]
  rw [sub_smul, one_smul, smul_sub]
  abel

private theorem pivotView_one (x : Fin 7 → ℝ³) : pivotView x 1 = x 3 - x 6 := by
  dsimp [pivotView]; simp

private theorem pivotView_zero (x : Fin 7 → ℝ³) : pivotView x 0 = x 3 - x 2 := by
  dsimp [pivotView]; simp

private theorem inner_pivotView (F : S0xFac 9 s0x_S24 x) (t : Fin 9) (s : ℝ) :
    ⟪F.N t, pivotView x s⟫ = ⟪F.N t, x 3 - x 2⟫ + s * ⟪F.N t, x 2 - x 6⟫ := by
  rw [pivotView_eq, inner_add_right, real_inner_smul_right]

private theorem inner_pivotView_sRoot (F : S0xFac 9 s0x_S24 x) (t : Fin 9)
    (hne : ⟪F.N t, x 2 - x 6⟫ ≠ 0) :
    ⟪F.N t, pivotView x (sRoot F t)⟫ = 0 := by
  rw [inner_pivotView, sRoot, div_mul_cancel₀ _ hne, add_neg_cancel]

private theorem inner_pivot_7 (F : S0xFac 9 s0x_S24 x) (s : ℝ) :
    ⟪F.N 7, pivotView x s⟫ = 0 := by
  rw [inner_pivotView, F.inner_sub, F.inner_sub,
    F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)]
  ring

private theorem inner_pivot_5 (F : S0xFac 9 s0x_S24 x) (s : ℝ) :
    ⟪F.N 5, pivotView x s⟫ = F.f 5 (x 3) := by
  rw [inner_pivotView, F.inner_sub, F.inner_sub,
    F.zero 5 2 (by decide), F.zero 5 6 (by decide)]
  ring

private theorem inner_pivot_6 (F : S0xFac 9 s0x_S24 x) (s : ℝ) :
    ⟪F.N 6, pivotView x s⟫ = s * (-F.f 6 (x 6)) := by
  rw [inner_pivotView, F.inner_sub, F.inner_sub,
    F.zero 6 3 (by decide), F.zero 6 2 (by decide)]
  ring

private theorem inner_pivot_8 (F : S0xFac 9 s0x_S24 x) (s : ℝ) :
    ⟪F.N 8, pivotView x s⟫ = (1 - s) * (-F.f 8 (x 2)) := by
  rw [inner_pivotView, F.inner_sub, F.inner_sub,
    F.zero 8 3 (by decide), F.zero 8 6 (by decide)]
  ring

private theorem inner_pivot_0 (F : S0xFac 9 s0x_S24 x) (s : ℝ) :
    ⟪F.N 0, pivotView x s⟫ = (oblX6 x 3 - s) * F.f 0 (x 6) := by
  have ev := M4.fac_eval F 0 3
  rw [F.zero 0 0 (by decide), F.zero 0 1 (by decide), F.zero 0 2 (by decide)] at ev
  rw [inner_pivotView, F.inner_sub, F.inner_sub, F.zero 0 2 (by decide), ev]
  ring

private theorem inner_pivot_1 (F : S0xFac 9 s0x_S24 x) (s : ℝ) :
    ⟪F.N 1, pivotView x s⟫ = (s - (1 - oblX2 x 3)) * F.f 1 (x 2) := by
  have ev := M4.fac_eval F 1 3
  rw [F.zero 1 0 (by decide), F.zero 1 1 (by decide), F.zero 1 6 (by decide)] at ev
  rw [inner_pivotView, F.inner_sub, F.inner_sub, F.zero 1 6 (by decide), ev]
  ring

private theorem inner_2_26_pos (F : S0xFac 9 s0x_S24 x) : 0 < ⟪F.N 2, x 2 - x 6⟫ := by
  rw [F.inner_sub, F.zero 2 2 (by decide), zero_sub, neg_pos]
  exact F.neg 2 6 (by decide)

private theorem inner_4_26_neg (F : S0xFac 9 s0x_S24 x) : ⟪F.N 4, x 2 - x 6⟫ < 0 := by
  rw [F.inner_sub, F.zero 4 6 (by decide), sub_zero]
  exact F.neg 4 2 (by decide)

private theorem inner_3_1_pos (F : S0xFac 9 s0x_S24 x) :
    0 < ⟪F.N 3, pivotView x 1⟫ := by
  rw [pivotView_one, F.inner_sub, F.zero 3 3 (by decide), zero_sub, neg_pos]
  exact F.neg 3 6 (by decide)

private theorem inner_3_0_pos (F : S0xFac 9 s0x_S24 x) :
    0 < ⟪F.N 3, pivotView x 0⟫ := by
  rw [pivotView_zero, F.inner_sub, F.zero 3 3 (by decide), zero_sub, neg_pos]
  exact F.neg 3 2 (by decide)

private theorem sLA_bounds (F : S0xFac 9 s0x_S24 x) :
    1 ≤ sLA F ∧ 0 ≤ ⟪F.N 2, pivotView x (sLA F)⟫ := by
  have hB2 := inner_2_26_pos F
  unfold sLA
  split_ifs with h
  · exact ⟨le_rfl, by rwa [pivotView_one]⟩
  · have hroot := inner_pivotView_sRoot F 2 hB2.ne'
    have h1 : ⟪F.N 2, pivotView x 1⟫ < 0 := by rw [pivotView_one]; exact lt_of_not_ge h
    rw [inner_pivotView] at hroot h1
    have hlt : 1 < sRoot F 2 := by
      by_contra hle; push Not at hle
      nlinarith
    exact ⟨hlt.le, (inner_pivotView_sRoot F 2 hB2.ne').ge⟩

private theorem sRA_bounds (F : S0xFac 9 s0x_S24 x) (hc : 1 < oblX6 x 3) :
    sRA F ≤ oblX6 x 3 ∧ 0 ≤ ⟪F.N 3, pivotView x (sRA F)⟫ := by
  unfold sRA
  split_ifs with h
  · exact ⟨le_rfl, h⟩
  · have h1 := inner_3_1_pos F
    have hc3 : ⟪F.N 3, pivotView x (oblX6 x 3)⟫ < 0 := lt_of_not_ge h
    rw [inner_pivotView] at h1 hc3
    have hB3 : ⟪F.N 3, x 2 - x 6⟫ < 0 := by
      have hdiff : (oblX6 x 3 - 1) * ⟪F.N 3, x 2 - x 6⟫ < 0 := by linarith
      exact neg_of_mul_neg_right hdiff (by linarith)
    have hroot := inner_pivotView_sRoot F 3 hB3.ne
    have hlt : sRoot F 3 < oblX6 x 3 := by
      rw [inner_pivotView] at hroot
      by_contra hle; push Not at hle
      nlinarith
    exact ⟨hlt.le, (inner_pivotView_sRoot F 3 hB3.ne).ge⟩

private theorem sLB_bounds (F : S0xFac 9 s0x_S24 x) (hb : 1 < oblX2 x 3) :
    1 - oblX2 x 3 ≤ sLB F ∧ 0 ≤ ⟪F.N 3, pivotView x (sLB F)⟫ := by
  unfold sLB
  split_ifs with h
  · exact ⟨le_rfl, h⟩
  · have h0 := inner_3_0_pos F
    have hb3 : ⟪F.N 3, pivotView x (1 - oblX2 x 3)⟫ < 0 := lt_of_not_ge h
    rw [inner_pivotView] at h0 hb3
    have hB3 : 0 < ⟪F.N 3, x 2 - x 6⟫ := by
      have hdiff : (oblX2 x 3 - 1) * ⟪F.N 3, x 2 - x 6⟫ > 0 := by linarith
      exact pos_of_mul_pos_right hdiff (by linarith)
    have hroot := inner_pivotView_sRoot F 3 hB3.ne'
    have hlt : 1 - oblX2 x 3 < sRoot F 3 := by
      rw [inner_pivotView] at hroot
      by_contra hle; push Not at hle
      nlinarith
    exact ⟨hlt.le, (inner_pivotView_sRoot F 3 hB3.ne').ge⟩

private theorem sRB_bounds (F : S0xFac 9 s0x_S24 x) :
    sRB F ≤ 0 ∧ 0 ≤ ⟪F.N 4, pivotView x (sRB F)⟫ := by
  have hB4 := inner_4_26_neg F
  unfold sRB
  split_ifs with h
  · exact ⟨le_rfl, by rwa [pivotView_zero]⟩
  · have hroot := inner_pivotView_sRoot F 4 hB4.ne
    have h0 : ⟪F.N 4, pivotView x 0⟫ < 0 := by rw [pivotView_zero]; exact lt_of_not_ge h
    rw [inner_pivotView] at hroot h0
    have hlt : sRoot F 4 < 0 := by
      by_contra hle; push Not at hle
      nlinarith
    exact ⟨hlt.le, (inner_pivotView_sRoot F 4 hB4.ne).ge⟩

private theorem cellLe_A_of_bounds (F : S0xFac 9 s0x_S24 x) {s : ℝ}
    (hs1 : 1 ≤ s) (hsc : s ≤ oblX6 x 3)
    (hf2 : 0 ≤ ⟪F.N 2, pivotView x s⟫) (hf3 : 0 ≤ ⟪F.N 3, pivotView x s⟫) :
    CellLe F UA DnA (pivotView x s) := by
  have T := M4.type24OfFac F
  have hb3 : 0 < oblX2 x 3 := T.X2_pos (v := 3) (by decide)
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · simp only [UA, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact hf2
    · exact hf3
    · rw [inner_pivot_6]
      have h66 : 0 < -F.f 6 (x 6) := by linarith [F.neg 6 6 (by decide)]
      nlinarith
  · simp only [DnA, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [inner_pivot_0]
      have h06 : F.f 0 (x 6) < 0 := F.neg 0 6 (by decide)
      nlinarith
    · rw [inner_pivot_1]
      have h12 : F.f 1 (x 2) < 0 := F.neg 1 2 (by decide)
      nlinarith
    · rw [inner_pivotView]
      have hB4 := inner_4_26_neg F
      have h40 : ⟪F.N 4, x 3 - x 2⟫ = ⟪F.N 4, pivotView x 1⟫ - ⟪F.N 4, x 2 - x 6⟫ := by
        rw [inner_pivotView]; ring
      have h41 : ⟪F.N 4, pivotView x 1⟫ = F.f 4 (x 3) := by
        rw [pivotView_one, F.inner_sub, F.zero 4 6 (by decide), sub_zero]
      have h43 : F.f 4 (x 3) < 0 := F.neg 4 3 (by decide)
      nlinarith
    · rw [inner_pivot_5]; exact (F.neg 5 3 (by decide)).le
    · rw [inner_pivot_7]
    · rw [inner_pivot_8]
      have h82 : 0 < -F.f 8 (x 2) := by linarith [F.neg 8 2 (by decide)]
      nlinarith

private theorem cellLe_B_of_bounds (F : S0xFac 9 s0x_S24 x) {s : ℝ}
    (hsb : 1 - oblX2 x 3 ≤ s) (hs0 : s ≤ 0)
    (hf3 : 0 ≤ ⟪F.N 3, pivotView x s⟫) (hf4 : 0 ≤ ⟪F.N 4, pivotView x s⟫) :
    CellLe F UB DnB (pivotView x s) := by
  have T := M4.type24OfFac F
  have hc3 : 0 < oblX6 x 3 := T.X6_pos (v := 3) (by decide)
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · simp only [UB, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact hf3
    · exact hf4
    · rw [inner_pivot_8]
      have h82 : 0 < -F.f 8 (x 2) := by linarith [F.neg 8 2 (by decide)]
      nlinarith
  · simp only [DnB, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [inner_pivot_0]
      have h06 : F.f 0 (x 6) < 0 := F.neg 0 6 (by decide)
      nlinarith
    · rw [inner_pivot_1]
      have h12 : F.f 1 (x 2) < 0 := F.neg 1 2 (by decide)
      nlinarith
    · rw [inner_pivotView]
      have hB2 := inner_2_26_pos F
      have h20 : ⟪F.N 2, x 3 - x 2⟫ = F.f 2 (x 3) := by
        rw [F.inner_sub, F.zero 2 2 (by decide), sub_zero]
      have h23 : F.f 2 (x 3) < 0 := F.neg 2 3 (by decide)
      nlinarith
    · rw [inner_pivot_5]; exact (F.neg 5 3 (by decide)).le
    · rw [inner_pivot_6]
      have h66 : 0 < -F.f 6 (x 6) := by linarith [F.neg 6 6 (by decide)]
      nlinarith
    · rw [inner_pivot_7]

private theorem pivot_convex_pos (F : S0xFac 9 s0x_S24 x) (t : Fin 9) {a b c : ℝ}
    (hab : a ≤ b) (hbc : b < c) (ha : 0 < ⟪F.N t, pivotView x a⟫)
    (hc : 0 ≤ ⟪F.N t, pivotView x c⟫) : 0 < ⟪F.N t, pivotView x b⟫ := by
  have hac : 0 < c - a := by linarith
  have hsum : (c - a) * ⟪F.N t, pivotView x b⟫ =
      (c - b) * ⟪F.N t, pivotView x a⟫ + (b - a) * ⟪F.N t, pivotView x c⟫ := by
    simp only [inner_pivotView]; ring
  have hpos : 0 < (c - a) * ⟪F.N t, pivotView x b⟫ := by
    rw [hsum]; exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) ha) (mul_nonneg (by linarith) hc)
  exact pos_of_mul_pos_right hpos hac.le

private theorem pivot_convex_pos' (F : S0xFac 9 s0x_S24 x) (t : Fin 9) {a b c : ℝ}
    (hab : a < b) (hbc : b ≤ c) (ha : 0 ≤ ⟪F.N t, pivotView x a⟫)
    (hc : 0 < ⟪F.N t, pivotView x c⟫) : 0 < ⟪F.N t, pivotView x b⟫ := by
  have hac : 0 < c - a := by linarith
  have hsum : (c - a) * ⟪F.N t, pivotView x b⟫ =
      (c - b) * ⟪F.N t, pivotView x a⟫ + (b - a) * ⟪F.N t, pivotView x c⟫ := by
    simp only [inner_pivotView]; ring
  have hpos : 0 < (c - a) * ⟪F.N t, pivotView x b⟫ := by
    rw [hsum]; exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) ha) (mul_pos (by linarith) hc)
  exact pos_of_mul_pos_right hpos hac.le

/-! ## (i) Region lemmas -/

/-- **EI-A (i), left end.** `d_{s_L}` is a closed-cell point of the cell of rim `0 2 3 4`. -/
theorem regionA_left (F : S0xFac 9 s0x_S24 x) (hc : 1 < oblX6 x 3) (hlt : sLA F < sRA F) :
    CellLe F UA DnA (pivotView x (sLA F)) := by
  obtain ⟨hs1, hf2⟩ := sLA_bounds F
  obtain ⟨hRc, hf3R⟩ := sRA_bounds F hc
  have hf3L : 0 < ⟪F.N 3, pivotView x (sLA F)⟫ :=
    pivot_convex_pos F 3 hs1 hlt (inner_3_1_pos F) hf3R
  exact cellLe_A_of_bounds F hs1 (hlt.le.trans hRc) hf2 hf3L.le

/-- **EI-A (i), right end.** `d_{s_R}` is a closed-cell point of the cell of rim `0 2 3 4`. -/
theorem regionA_right (F : S0xFac 9 s0x_S24 x) (hc : 1 < oblX6 x 3) (hlt : sLA F < sRA F) :
    CellLe F UA DnA (pivotView x (sRA F)) := by
  obtain ⟨hs1, hf2L⟩ := sLA_bounds F
  obtain ⟨hRc, hf3R⟩ := sRA_bounds F hc
  have hB2 := inner_2_26_pos F
  have hf2R : 0 ≤ ⟪F.N 2, pivotView x (sRA F)⟫ := by
    rw [inner_pivotView] at hf2L ⊢
    nlinarith
  exact cellLe_A_of_bounds F (hs1.trans hlt.le) hRc hf2R hf3R

/-- **EI-A (i), interior.** At the sum of the two ends every facet of the cell except `236` is strict, and `236`
is weakly down (it is edge-on). -/
theorem regionA_mid (F : S0xFac 9 s0x_S24 x) (hc : 1 < oblX6 x 3) (hlt : sLA F < sRA F) :
    (∀ t ∈ UA, 0 < ⟪F.N t, pivotView x (sLA F) + pivotView x (sRA F)⟫) ∧
      ⟪F.N 7, pivotView x (sLA F) + pivotView x (sRA F)⟫ ≤ 0 ∧
      ∀ t ∈ DnA, t ≠ 7 → ⟪F.N t, pivotView x (sLA F) + pivotView x (sRA F)⟫ < 0 := by
  have T := M4.type24OfFac F
  have hb3 : 0 < oblX2 x 3 := T.X2_pos (v := 3) (by decide)
  obtain ⟨hs1, hf2L⟩ := sLA_bounds F
  obtain ⟨hRc, hf3R⟩ := sRA_bounds F hc
  have hL_le := regionA_left F hc hlt
  have hR_le := regionA_right F hc hlt
  have hB2 := inner_2_26_pos F
  have h1 := inner_3_1_pos F
  refine ⟨fun t ht => ?_, ?_, fun t ht ht7 => ?_⟩
  · rw [inner_add_right]
    simp only [UA, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · have hf2R : 0 < ⟪F.N 2, pivotView x (sRA F)⟫ := by
        rw [inner_pivotView] at hf2L ⊢; nlinarith
      exact add_pos_of_nonneg_of_pos hf2L hf2R
    · have hf3L : 0 < ⟪F.N 3, pivotView x (sLA F)⟫ :=
        pivot_convex_pos F 3 hs1 hlt (inner_3_1_pos F) hf3R
      exact add_pos_of_pos_of_nonneg hf3L hf3R
    · have h6L : 0 < ⟪F.N 6, pivotView x (sLA F)⟫ := by
        rw [inner_pivot_6]; have : 0 < -F.f 6 (x 6) := by linarith [F.neg 6 6 (by decide)]
        nlinarith
      exact add_pos_of_pos_of_nonneg h6L (hR_le.1 6 (by decide))
  · rw [inner_add_right, inner_pivot_7, inner_pivot_7, add_zero]
  · rw [inner_add_right]
    simp only [DnA, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · have h0L : ⟪F.N 0, pivotView x (sLA F)⟫ < 0 := by
        rw [inner_pivot_0]; have := F.neg 0 6 (by decide); nlinarith
      exact add_lt_of_neg_of_le h0L (hR_le.2 0 (by decide))
    · have h1L : ⟪F.N 1, pivotView x (sLA F)⟫ < 0 := by
        rw [inner_pivot_1]; have := F.neg 1 2 (by decide); nlinarith
      exact add_lt_of_neg_of_le h1L (hR_le.2 1 (by decide))
    · have h4L : ⟪F.N 4, pivotView x (sLA F)⟫ < 0 := by
        rw [inner_pivotView]
        have hB4 := inner_4_26_neg F
        have h40 : ⟪F.N 4, x 3 - x 2⟫ = ⟪F.N 4, pivotView x 1⟫ - ⟪F.N 4, x 2 - x 6⟫ := by
          rw [inner_pivotView]; ring
        have h41 : ⟪F.N 4, pivotView x 1⟫ = F.f 4 (x 3) := by
          rw [pivotView_one, F.inner_sub, F.zero 4 6 (by decide), sub_zero]
        have h43 : F.f 4 (x 3) < 0 := F.neg 4 3 (by decide)
        nlinarith
      exact add_lt_of_neg_of_le h4L (hR_le.2 4 (by decide))
    · have h5L : ⟪F.N 5, pivotView x (sLA F)⟫ < 0 := by
        rw [inner_pivot_5]; exact F.neg 5 3 (by decide)
      exact add_lt_of_neg_of_le h5L (hR_le.2 5 (by decide))
    · exact absurd rfl ht7
    · have h8R : ⟪F.N 8, pivotView x (sRA F)⟫ < 0 := by
        rw [inner_pivot_8]; have : 0 < -F.f 8 (x 2) := by linarith [F.neg 8 2 (by decide)]
        nlinarith
      exact add_lt_of_le_of_neg (hL_le.2 8 (by decide)) h8R

/-- **EI-B (i), left end.** `d_{s_L}` is a closed-cell point of the cell of rim `0 5 3 6`. -/
theorem regionB_left (F : S0xFac 9 s0x_S24 x) (hb : 1 < oblX2 x 3) (hlt : sLB F < sRB F) :
    CellLe F UB DnB (pivotView x (sLB F)) := by
  obtain ⟨hsb, hf3L⟩ := sLB_bounds F hb
  obtain ⟨hs0, hf4R⟩ := sRB_bounds F
  have hB4 := inner_4_26_neg F
  have hf4L : 0 ≤ ⟪F.N 4, pivotView x (sLB F)⟫ := by
    rw [inner_pivotView] at hf4R ⊢
    nlinarith
  exact cellLe_B_of_bounds F hsb (hlt.le.trans hs0) hf3L hf4L

/-- **EI-B (i), right end.** `d_{s_R}` is a closed-cell point of the cell of rim `0 5 3 6`. -/
theorem regionB_right (F : S0xFac 9 s0x_S24 x) (hb : 1 < oblX2 x 3) (hlt : sLB F < sRB F) :
    CellLe F UB DnB (pivotView x (sRB F)) := by
  obtain ⟨hsb, hf3L⟩ := sLB_bounds F hb
  obtain ⟨hs0, hf4R⟩ := sRB_bounds F
  have hf3R : 0 < ⟪F.N 3, pivotView x (sRB F)⟫ :=
    pivot_convex_pos' F 3 hlt hs0 hf3L (inner_3_0_pos F)
  exact cellLe_B_of_bounds F (hsb.trans hlt.le) hs0 hf3R.le hf4R

/-- **EI-B (i), interior.** As `regionA_mid` for the cell of rim `0 5 3 6`. -/
theorem regionB_mid (F : S0xFac 9 s0x_S24 x) (hb : 1 < oblX2 x 3) (hlt : sLB F < sRB F) :
    (∀ t ∈ UB, 0 < ⟪F.N t, pivotView x (sLB F) + pivotView x (sRB F)⟫) ∧
      ⟪F.N 7, pivotView x (sLB F) + pivotView x (sRB F)⟫ ≤ 0 ∧
      ∀ t ∈ DnB, t ≠ 7 → ⟪F.N t, pivotView x (sLB F) + pivotView x (sRB F)⟫ < 0 := by
  have T := M4.type24OfFac F
  have hc3 : 0 < oblX6 x 3 := T.X6_pos (v := 3) (by decide)
  obtain ⟨hsb, hf3L⟩ := sLB_bounds F hb
  obtain ⟨hs0, hf4R⟩ := sRB_bounds F
  have hL_le := regionB_left F hb hlt
  have hR_le := regionB_right F hb hlt
  have hB4 := inner_4_26_neg F
  have h0 := inner_3_0_pos F
  refine ⟨fun t ht => ?_, ?_, fun t ht ht7 => ?_⟩
  · rw [inner_add_right]
    simp only [UB, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · have hf3R : 0 < ⟪F.N 3, pivotView x (sRB F)⟫ :=
        pivot_convex_pos' F 3 hlt hs0 hf3L (inner_3_0_pos F)
      exact add_pos_of_nonneg_of_pos hf3L hf3R
    · have hf4L : 0 < ⟪F.N 4, pivotView x (sLB F)⟫ := by
        rw [inner_pivotView] at hf4R ⊢; nlinarith
      exact add_pos_of_pos_of_nonneg hf4L hf4R
    · have h8R : 0 < ⟪F.N 8, pivotView x (sRB F)⟫ := by
        rw [inner_pivot_8]; have : 0 < -F.f 8 (x 2) := by linarith [F.neg 8 2 (by decide)]
        nlinarith
      exact add_pos_of_nonneg_of_pos (hL_le.1 8 (by decide)) h8R
  · rw [inner_add_right, inner_pivot_7, inner_pivot_7, add_zero]
  · rw [inner_add_right]
    simp only [DnB, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · have h0R : ⟪F.N 0, pivotView x (sRB F)⟫ < 0 := by
        rw [inner_pivot_0]; have := F.neg 0 6 (by decide); nlinarith
      exact add_lt_of_le_of_neg (hL_le.2 0 (by decide)) h0R
    · have h1R : ⟪F.N 1, pivotView x (sRB F)⟫ < 0 := by
        rw [inner_pivot_1]; have := F.neg 1 2 (by decide); nlinarith
      exact add_lt_of_le_of_neg (hL_le.2 1 (by decide)) h1R
    · have h2R : ⟪F.N 2, pivotView x (sRB F)⟫ < 0 := by
        rw [inner_pivotView]
        have hB2 := inner_2_26_pos F
        have h20 : ⟪F.N 2, x 3 - x 2⟫ = F.f 2 (x 3) := by
          rw [F.inner_sub, F.zero 2 2 (by decide), sub_zero]
        have h23 : F.f 2 (x 3) < 0 := F.neg 2 3 (by decide)
        nlinarith
      exact add_lt_of_le_of_neg (hL_le.2 2 (by decide)) h2R
    · have h5R : ⟪F.N 5, pivotView x (sRB F)⟫ < 0 := by
        rw [inner_pivot_5]; exact F.neg 5 3 (by decide)
      exact add_lt_of_le_of_neg (hL_le.2 5 (by decide)) h5R
    · have h6L : ⟪F.N 6, pivotView x (sLB F)⟫ < 0 := by
        rw [inner_pivot_6]; have := F.neg 6 6 (by decide); nlinarith
      exact add_lt_of_neg_of_le h6L (hR_le.2 6 (by decide))
    · exact absurd rfl ht7

/-! ## (i) assembled (proved from the region lemmas) -/

theorem n7_neg (F : S0xFac 9 s0x_S24 x) : ⟪F.N 7, x 0 - x 2⟫ < 0 := by
  rw [F.inner_sub, F.zero 7 2 (by decide)]
  have := F.neg 7 0 (by decide)
  linarith

/-- A cell point (facet `236` DOWN) from a midpoint strict off `236` (tilt toward `-F.N 7` along `x 0 - x 2`). -/
theorem cellAt_of_mid_neg (F : S0xFac 9 s0x_S24 x) {U Dn : Finset (Fin 9)} {u : ℝ³}
    (hU : ∀ t ∈ U, 0 < ⟪F.N t, u⟫) (h70 : ⟪F.N 7, u⟫ ≤ 0)
    (hD : ∀ t ∈ Dn, t ≠ 7 → ⟪F.N t, u⟫ < 0) : ∃ a, CellAt F U Dn a := by
  refine exists_cellAt_of_lex (u₀ := u) (v := x 0 - x 2) (fun t ht => ?_) (fun t ht => ?_)
  · exact Or.inl (hU t ht)
  · by_cases h : t = 7
    · subst h
      rcases h70.lt_or_eq with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by linarith, by linarith [n7_neg F]⟩
    · exact Or.inl (by linarith [hD t ht h])

/-- **EI-A (i).** Both ends are closed-cell points of the cell of rim `0 2 3 4`, and the cell is nonempty. -/
theorem regionA (F : S0xFac 9 s0x_S24 x) (hc : 1 < oblX6 x 3) (hlt : sLA F < sRA F) :
    CellLe F UA DnA (pivotView x (sLA F)) ∧ CellLe F UA DnA (pivotView x (sRA F)) ∧
      ∃ a, CellAt F UA DnA a := by
  obtain ⟨h1, h2, h3⟩ := regionA_mid F hc hlt
  exact ⟨regionA_left F hc hlt, regionA_right F hc hlt,
    cellAt_of_mid_neg F h1 h2 h3⟩

/-- **EI-B (i).** Both ends are closed-cell points of the cell of rim `0 5 3 6`, and the cell is nonempty. -/
theorem regionB (F : S0xFac 9 s0x_S24 x) (hb : 1 < oblX2 x 3) (hlt : sLB F < sRB F) :
    CellLe F UB DnB (pivotView x (sLB F)) ∧ CellLe F UB DnB (pivotView x (sRB F)) ∧
      ∃ a, CellAt F UB DnB a := by
  obtain ⟨h1, h2, h3⟩ := regionB_mid F hb hlt
  exact ⟨regionB_left F hb hlt, regionB_right F hb hlt,
    cellAt_of_mid_neg F h1 h2 h3⟩

/-! ## (ii) The leaves (proved from (i) and `isRupert_of_closedCell_q4`)

`hn` = "not D_A at both ends", `hp` = "not D_B at both ends" (Carbon Thm 2.1): for the 4-cycle `c`,
`D_A(g)` is `∀ p ∈ diagPairs, 0 ≤ ⟪x (c p.1) - x (c p.2), g⟫`, `D_B(g)` the same with `≤ 0`.  (This is
the criterion of the exact "iff": a robust leaf exists on the piece iff `hn` and `hp`; the implication
proved below is the direction a Lean certificate needs.) -/

/-- **EI-A (ii), the `0 2 3 4` leaf.** Some diagonal form negative at an end and some positive at an end. -/
theorem isRupert_pieceA (F : S0xFac 9 s0x_S24 x) (hc : 1 < oblX6 x 3) (hlt : sLA F < sRA F)
    (hn : (∃ p ∈ diagPairs, ⟪x (cA p.1) - x (cA p.2), pivotView x (sLA F)⟫ < 0) ∨
      ∃ p ∈ diagPairs, ⟪x (cA p.1) - x (cA p.2), pivotView x (sRA F)⟫ < 0)
    (hp : (∃ p ∈ diagPairs, 0 < ⟪x (cA p.1) - x (cA p.2), pivotView x (sLA F)⟫) ∨
      ∃ p ∈ diagPairs, 0 < ⟪x (cA p.1) - x (cA p.2), pivotView x (sRA F)⟫) :
    IsRupert (univ.image x) := by
  obtain ⟨hL, hR, a, ha⟩ := regionA F hc hlt
  have hx := Minimality.H24.SAT.inj_of_fac F
  rcases hn with hn | hn <;> rcases hp with hp | hp
  · exact isRupert_of_closedCell_q4 F hx injA cycA ha hL hL hn hp
  · exact isRupert_of_closedCell_q4 F hx injA cycA ha hL hR hn hp
  · exact isRupert_of_closedCell_q4 F hx injA cycA ha hR hL hn hp
  · exact isRupert_of_closedCell_q4 F hx injA cycA ha hR hR hn hp

/-- **EI-B (ii), the `0 5 3 6` leaf.** Same for the chord-36 sector. -/
theorem isRupert_pieceB (F : S0xFac 9 s0x_S24 x) (hb : 1 < oblX2 x 3) (hlt : sLB F < sRB F)
    (hn : (∃ p ∈ diagPairs, ⟪x (cB p.1) - x (cB p.2), pivotView x (sLB F)⟫ < 0) ∨
      ∃ p ∈ diagPairs, ⟪x (cB p.1) - x (cB p.2), pivotView x (sRB F)⟫ < 0)
    (hp : (∃ p ∈ diagPairs, 0 < ⟪x (cB p.1) - x (cB p.2), pivotView x (sLB F)⟫) ∨
      ∃ p ∈ diagPairs, 0 < ⟪x (cB p.1) - x (cB p.2), pivotView x (sRB F)⟫) :
    IsRupert (univ.image x) := by
  obtain ⟨hL, hR, a, ha⟩ := regionB F hb hlt
  have hx := Minimality.H24.SAT.inj_of_fac F
  rcases hn with hn | hn <;> rcases hp with hp | hp
  · exact isRupert_of_closedCell_q4 F hx injB cycB ha hL hL hn hp
  · exact isRupert_of_closedCell_q4 F hx injB cycB ha hL hR hn hp
  · exact isRupert_of_closedCell_q4 F hx injB cycB ha hR hL hn hp
  · exact isRupert_of_closedCell_q4 F hx injB cycB ha hR hR hn hp

end Minimality.T24.EI
