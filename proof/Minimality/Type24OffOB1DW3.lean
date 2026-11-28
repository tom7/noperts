module

public import Minimality.Type24OffOB1DW2

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.T24.Stmt Minimality.T24.Q45
  Minimality.T24.Reg Minimality.T24.A19

/-!
# Type 24 off `OB1`: the double wall reduces to a special stratum (job OSPEC22)

nopert229 notes/OPENSPECIAL-STRATEGY.md section 2j.  On the double wall `a4 = a5 = 1` (frame signs, `0 < s, t`,
`1 < s + t`) the bottom edge `d = x 6 - x 2` is a fixed combination of the top edges (`dw3_comb`):

  `Δ d = (b5 + c5) e4 - (b4 + c4) e5`,  `Δ = b5 c4 - b4 c5 > 0`  (`e4 = x 4 - x 0`, `e5 = x 5 - x 0`).

So `⟪e4, e5⟫ ≤ 0` forces `⟪d, e4⟫ > 0`, and then the Bs view's rim `0 5 2 6` is `RobUniLex` (`0` below `5`, `6`
below `2` at level 1, a level-2 tie break when `⟪e4, e5⟫ = 0`): `dw3_bsCond`.  For `⟪e4, e5⟫ > 0` the Bs view works
when `⟪d, e4⟫ < 0`, its mirror when `⟪d, e5⟫ > 0` (`dw3_bsCondSym`).  What is left (`DwSpec`) is the region
`⟪e4, e5⟫ > 0`, `⟪d, e4⟫ ≥ 0 ≥ ⟪d, e5⟫`, where the residue letters of `dw_letters_of_resP` force the two
junction letters `⟪x 2 - x 5, e4⟫ ≤ 0`, `⟪x 6 - x 4, e5⟫ ≤ 0` (`dw3_split`; no use of `DwHorizOK` or of the
classes).  With `¬ DwHorizOK` this is a special position (`dw3_spec_codim`): `⟪x 2 - x 5, e4⟫ = 0`, or
`⟪x 6 - x 4, e5⟫ = 0`, or the two junction forms are proportional on the cone (a common root).

Residue: `Q45ResWQ` (= `Q45ResWP` with the double-wall piece inside `DwSpec`, `q45ResWQ_of_P`),
**`OpenSpecialQ`**, equivalent to `OpenSpecialP` (`openSpecialQ_iff_P`); chains `..._Q`.
-/

namespace Minimality.T24.OSpec

variable {x : Fin 7 → ℝ³}

section DwSpecial
open Minimality.LexCell

/-- On the double wall: `e4 = b4 g2 + c4 g6`. -/
theorem dw3_e (F : S0xFac 9 s0x_S24 x) {v : Fin 7} (hv : oblX0 x v = 1) :
    x v - x 0 = oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1) := by
  have T := M4.type24OfFac F
  have r := T.rep v
  rw [hv, one_smul] at r
  rw [show x v - x 0 = (x v - x 1) - (x 0 - x 1) by abel, r]; abel

/-- **The bottom edge `2 6` in the top frame**: `Δ (x 6 - x 2) = (b5 + c5) e4 - (b4 + c4) e5`. -/
theorem dw3_comb (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1) :
    (oblX2 x 5 * oblX6 x 4 - oblX2 x 4 * oblX6 x 5) • (x 6 - x 2) =
      (oblX2 x 5 + oblX6 x 5) • (x 4 - x 0) - (oblX2 x 4 + oblX6 x 4) • (x 5 - x 0) := by
  rw [dw3_e F hw4, dw3_e F hw5]
  rw [show x 6 - x 2 = (x 6 - x 1) - (x 2 - x 1) by abel]
  module

/-- `Δ > 0` from the frame signs `b3`, `b4` and the positivity of the frame coordinates. -/
theorem dw3_delta_pos (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1)
    (b3 : 0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4)
    (b4 : 0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5) :
    0 < oblX2 x 5 * oblX6 x 4 - oblX2 x 4 * oblX6 x 5 := by
  have T := M4.type24OfFac F
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (by decide)
  rw [hw4, hw5] at b3 b4
  nlinarith [mul_pos (sub_pos.2 (by linarith : oblX2 x 4 < oblX2 x 5)) (T.X6_pos (v := 4) (by decide)),
    mul_pos hb4 (sub_pos.2 (by linarith : oblX6 x 5 < oblX6 x 4))]

theorem dw3_e4_ne (F : S0xFac 9 s0x_S24 x) : x 4 - x 0 ≠ 0 := by
  intro h
  have h0 := F.zero 2 0 (by decide)
  have h4 := F.neg 2 4 (by decide)
  have e := F.inner_sub 2 4 0
  rw [h, inner_zero_right, h0] at e
  linarith

theorem dw3_e5_ne (F : S0xFac 9 s0x_S24 x) : x 5 - x 0 ≠ 0 := by
  intro h
  have h0 := F.zero 4 0 (by decide)
  have h5 := F.neg 4 5 (by decide)
  have e := F.inner_sub 4 5 0
  rw [h, inner_zero_right, h0] at e
  linarith

/-- **The Bs view on the double wall**: rim `0 5 2 6` from `⟪e4, e5⟫ ≤ 0 < ⟪d, e4⟫` (`0` below `5`, possibly by the
level-2 tie break, and `6` below `2`) or from `⟪d, e4⟫ < 0 < ⟪e4, e5⟫` (`5` below `0`, `2` below `6`). -/
theorem dw3_bsCond (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1) {t : ℝ} (ht1 : t < 1)
    (h : (⟪x 4 - x 0, x 5 - x 0⟫ ≤ 0 ∧ 0 < ⟪x 6 - x 2, x 4 - x 0⟫) ∨
      (0 < ⟪x 4 - x 0, x 5 - x 0⟫ ∧ ⟪x 6 - x 2, x 4 - x 0⟫ < 0)) : BsCond F t := by
  refine ⟨Or.inr ⟨hw4, hw5⟩, Or.inl ht1.le, fun _ => ?_, fun h1 => absurd h1 (not_le.2 ht1)⟩
  have i50 : ⟪x 5, x 0 - x 4⟫ - ⟪x 0, x 0 - x 4⟫ = -⟪x 4 - x 0, x 5 - x 0⟫ := by
    rw [← inner_sub_left, ← neg_sub (x 4) (x 0), inner_neg_right, real_inner_comm (x 4 - x 0) (x 5 - x 0)]
  have i26 : ⟪x 2, x 0 - x 4⟫ - ⟪x 6, x 0 - x 4⟫ = ⟪x 6 - x 2, x 4 - x 0⟫ := by
    rw [← inner_sub_left, ← inner_neg_neg, neg_sub, neg_sub]
  have i55 : 0 < ⟪x 5, x 5 - x 0⟫ - ⟪x 0, x 5 - x 0⟫ := by
    rw [← inner_sub_left]; exact real_inner_self_pos.2 (dw3_e5_ne F)
  rcases h with ⟨hg, hd⟩ | ⟨hg, hd⟩
  · refine robUniLex_four_of_mixed ⟨(0, 1), by decide, ?_⟩ ⟨(2, 3), by decide, ?_⟩
    · show LexPos3 (⟪x 5, x 0 - x 4⟫ - ⟪x 0, x 0 - x 4⟫) (⟪x 5, x 5 - x 0⟫ - ⟪x 0, x 5 - x 0⟫) _
      rcases hg.lt_or_eq with hg | hg
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by linarith, Or.inl i55⟩
    · show LexPos3 (⟪x 2, x 0 - x 4⟫ - ⟪x 6, x 0 - x 4⟫) _ _
      exact Or.inl (by linarith)
  · refine robUniLex_four_of_mixed ⟨(2, 3), by decide, ?_⟩ ⟨(0, 1), by decide, ?_⟩
    · show LexPos3 (⟪x 6, x 0 - x 4⟫ - ⟪x 2, x 0 - x 4⟫) _ _
      exact Or.inl (by linarith)
    · show LexPos3 (⟪x 0, x 0 - x 4⟫ - ⟪x 5, x 0 - x 4⟫) _ _
      exact Or.inl (by linarith)

/-- **The mirror Bs view on the double wall**: rim `0 4 6 2` of the view `(x 0 - x 5, x 4 - x 0, ·)` from
`⟪e4, e5⟫ > 0` (`4` below `0`) and `⟪d, e5⟫ > 0` (`6` below `2`). -/
theorem dw3_bsCondSym (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1) {s : ℝ} (hs1 : s < 1)
    (hg : 0 < ⟪x 4 - x 0, x 5 - x 0⟫) (hd : 0 < ⟪x 6 - x 2, x 5 - x 0⟫) : BsCondSym F s := by
  refine ⟨Or.inr ⟨hw5, hw4⟩, Or.inl hs1.le, fun _ => ?_, fun h1 => absurd h1 (not_le.2 hs1)⟩
  have i40 : ⟪x 0, x 0 - x 5⟫ - ⟪x 4, x 0 - x 5⟫ = ⟪x 4 - x 0, x 5 - x 0⟫ := by
    rw [← inner_sub_left, ← inner_neg_neg, neg_sub, neg_sub]
  have i26 : ⟪x 2, x 0 - x 5⟫ - ⟪x 6, x 0 - x 5⟫ = ⟪x 6 - x 2, x 5 - x 0⟫ := by
    rw [← inner_sub_left, ← inner_neg_neg, neg_sub, neg_sub]
  refine robUniLex_four_of_mixed ⟨(2, 3), by decide, ?_⟩ ⟨(0, 1), by decide, ?_⟩
  · show LexPos3 (⟪x (Sym.pi24 6), x (Sym.pi24 0) - x (Sym.pi24 4)⟫ -
        ⟪x (Sym.pi24 2), x (Sym.pi24 0) - x (Sym.pi24 4)⟫) _ _
    simp only [Sym.pi24_0, Sym.pi24_2, Sym.pi24_4, Sym.pi24_6]
    exact Or.inl (by linarith)
  · show LexPos3 (⟪x (Sym.pi24 0), x (Sym.pi24 0) - x (Sym.pi24 4)⟫ -
        ⟪x (Sym.pi24 5), x (Sym.pi24 0) - x (Sym.pi24 4)⟫) _ _
    simp only [Sym.pi24_0, Sym.pi24_4, Sym.pi24_5]
    exact Or.inl (by linarith)

/-- **The special double-wall stratum**: the angle at `0` acute, `⟪d, e4⟫ ≥ 0 ≥ ⟪d, e5⟫` (both Bs views fail),
and the two junction letters `⟪x 2 - x 5, e4⟫`, `⟪x 6 - x 4, e5⟫` nonpositive. -/
def DwSpec (x : Fin 7 → ℝ³) : Prop :=
  0 < ⟪x 4 - x 0, x 5 - x 0⟫ ∧ 0 ≤ ⟪x 6 - x 2, x 4 - x 0⟫ ∧ ⟪x 6 - x 2, x 5 - x 0⟫ ≤ 0 ∧
    ⟪x 2 - x 5, x 4 - x 0⟫ ≤ 0 ∧ ⟪x 6 - x 4, x 5 - x 0⟫ ≤ 0

/-- **The double-wall split**: with the residue letters of `dw_letters_of_resP`, the Bs view, its mirror, or the
special stratum `DwSpec`. -/
theorem dw3_split (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1)
    (b3 : 0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4)
    (b4 : 0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5) {s t : ℝ} (hs1 : s < 1) (ht1 : t < 1)
    (L4 : ⟪x 6 - x 0, x 4 - x 0⟫ ≤ 0 ∨ ⟪x 2 - x 5, x 4 - x 0⟫ ≤ 0)
    (L5 : ⟪x 2 - x 0, x 5 - x 0⟫ ≤ 0 ∨ ⟪x 6 - x 4, x 5 - x 0⟫ ≤ 0) :
    BsCond F t ∨ BsCondSym F s ∨ DwSpec x := by
  have T := M4.type24OfFac F
  have hΔ := dw3_delta_pos F hw4 hw5 b3 b4
  have hB : 0 < oblX2 x 4 + oblX6 x 4 := by
    linarith [T.X2_pos (v := 4) (by decide), T.X6_pos (v := 4) (by decide)]
  have hA : 0 < oblX2 x 5 + oblX6 x 5 := by
    linarith [T.X2_pos (v := 5) (by decide), T.X6_pos (v := 5) (by decide)]
  have K := congrArg (fun v => ⟪v, x 4 - x 0⟫) (dw3_comb F hw4 hw5)
  rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_comm (x 4 - x 0) (x 5 - x 0)] at K
  have hE4 : 0 < ⟪x 4 - x 0, x 4 - x 0⟫ := real_inner_self_pos.2 (dw3_e4_ne F)
  by_cases hg : ⟪x 4 - x 0, x 5 - x 0⟫ ≤ 0
  · left
    refine dw3_bsCond F hw4 hw5 ht1 (Or.inl ⟨hg, ?_⟩)
    have : 0 < (oblX2 x 5 * oblX6 x 4 - oblX2 x 4 * oblX6 x 5) * ⟪x 6 - x 2, x 4 - x 0⟫ := by
      rw [K]
      nlinarith [mul_pos hA hE4, mul_nonneg hB.le (neg_nonneg.2 hg)]
    exact pos_of_mul_pos_right this hΔ.le
  push Not at hg
  by_cases hd4 : ⟪x 6 - x 2, x 4 - x 0⟫ < 0
  · exact Or.inl (dw3_bsCond F hw4 hw5 ht1 (Or.inr ⟨hg, hd4⟩))
  push Not at hd4
  by_cases hd5 : 0 < ⟪x 6 - x 2, x 5 - x 0⟫
  · exact Or.inr (Or.inl (dw3_bsCondSym F hw4 hw5 hs1 hg hd5))
  push Not at hd5
  refine Or.inr (Or.inr ⟨hg, hd4, hd5, ?_, ?_⟩)
  · rcases L4 with h | h
    · have e : x 6 - x 0 = (x 6 - x 2) + (x 5 - x 0) + (x 2 - x 5) := by abel
      rw [e, inner_add_left, inner_add_left] at h
      linarith [real_inner_comm (x 4 - x 0) (x 5 - x 0)]
    · exact h
  · rcases L5 with h | h
    · have e : x 2 - x 0 = (x 6 - x 4) - (x 6 - x 2) + (x 4 - x 0) := by abel
      rw [e, inner_add_left, inner_sub_left] at h
      have := real_inner_comm (x 4 - x 0) (x 5 - x 0)
      have := real_inner_self_pos.2 (dw3_e5_ne F)
      linarith
    · exact h

/-- **The special stratum is special position**: on `DwSpec` without `DwHorizOK`, a junction letter vanishes at a
cone ray or the two junction forms are proportional on the cone (`p1 q2 = p2 q1`; a common root). -/
theorem dw3_spec_codim (hS : DwSpec x) (hH : ¬ DwHorizOK x) :
    ⟪x 2 - x 5, x 4 - x 0⟫ = 0 ∨ ⟪x 6 - x 4, x 5 - x 0⟫ = 0 ∨
      ⟪x 6 - x 4, x 4 - x 0⟫ * ⟪x 2 - x 5, x 5 - x 0⟫ = ⟪x 6 - x 4, x 5 - x 0⟫ * ⟪x 2 - x 5, x 4 - x 0⟫ := by
  obtain ⟨-, -, -, hq1, hp2⟩ := hS
  set p1 := ⟪x 6 - x 4, x 4 - x 0⟫
  set p2 := ⟪x 6 - x 4, x 5 - x 0⟫
  set q1 := ⟪x 2 - x 5, x 4 - x 0⟫
  set q2 := ⟪x 2 - x 5, x 5 - x 0⟫
  have ev : ∀ (v : ℝ³) (α β : ℝ), ⟪v, dwM x α β⟫ = α * ⟪v, x 4 - x 0⟫ + β * ⟪v, x 5 - x 0⟫ := by
    intro v α β; rw [dwM, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  by_contra hc
  push Not at hc
  obtain ⟨hq1', hp2', hdet⟩ := hc
  have hq1n : q1 < 0 := lt_of_le_of_ne hq1 hq1'
  have hp2n : p2 < 0 := lt_of_le_of_ne hp2 hp2'
  have hp1 : 0 < p1 := by
    by_contra h; push Not at h
    refine hH ⟨(|q2| + 1) / (-q1), 1, div_pos (by positivity) (by linarith), one_pos, Or.inr ⟨?_, ?_⟩⟩
    · rw [ev]; nlinarith [div_pos (by positivity : (0:ℝ) < |q2| + 1) (by linarith : 0 < -q1)]
    · rw [ev]
      have e : (|q2| + 1) / (-q1) * q1 = -(|q2| + 1) := by field_simp
      show (|q2| + 1) / (-q1) * q1 + 1 * q2 < 0
      rw [e]; linarith [le_abs_self q2]
  have hq2 : 0 < q2 := by
    by_contra h; push Not at h
    refine hH ⟨1, (|p1| + 1) / (-p2), one_pos, div_pos (by positivity) (by linarith), Or.inr ⟨?_, ?_⟩⟩
    · rw [ev]
      have e : (|p1| + 1) / (-p2) * p2 = -(|p1| + 1) := by field_simp
      show 1 * p1 + (|p1| + 1) / (-p2) * p2 < 0
      rw [e]; linarith [le_abs_self p1]
    · rw [ev]; nlinarith [div_pos (by positivity : (0:ℝ) < |p1| + 1) (by linarith : 0 < -p2)]
  have hα : 0 < -2 * p2 * q2 := by nlinarith
  have hβ : 0 < p1 * q2 + p2 * q1 := by nlinarith [mul_pos hp1 hq2, mul_pos_of_neg_of_neg hp2n hq1n]
  have e1 : ⟪x 6 - x 4, dwM x (-2 * p2 * q2) (p1 * q2 + p2 * q1)⟫ = p2 * (p2 * q1 - p1 * q2) := by
    rw [ev]; ring
  have e2 : ⟪x 2 - x 5, dwM x (-2 * p2 * q2) (p1 * q2 + p2 * q1)⟫ = q2 * (p1 * q2 - p2 * q1) := by
    rw [ev]; ring
  rcases lt_or_gt_of_ne hdet with h | h
  · exact hH ⟨_, _, hα, hβ, Or.inr ⟨by rw [e1]; nlinarith, by rw [e2]; nlinarith⟩⟩
  · exact hH ⟨_, _, hα, hβ, Or.inl ⟨by rw [e1]; nlinarith, by rw [e2]; nlinarith⟩⟩

/-! ### The residue after the Bs reduction of the double wall -/

/-- `Q45ResWP` with its double-wall piece inside the special stratum `DwSpec`. -/
def Q45ResWQ (F : S0xFac 9 s0x_S24 x) : Prop :=
  Q45ResWP F ∧ (oblX0 x 4 = 1 → oblX0 x 5 = 1 → DwSpec x ∧ ¬ DwHorizOK x)

/-- **On the double wall `Q45ResWP` lies in `DwSpec`** (frame signs; `dw3_split`, the Bs cuts of `Q45ResSTB`). -/
theorem q45ResWQ_of_P {F : S0xFac 9 s0x_S24 x}
    (b1 : oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0)
    (b2 : 0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3)
    (b3 : 0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4)
    (b4 : 0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5) (h : Q45ResWP F) : Q45ResWQ F := by
  refine ⟨h, fun hw4 hw5 => ⟨?_, (not_dwHoriz_of_resP hw4 hw5 b1 b2 h).1⟩⟩
  obtain ⟨L4, L5⟩ := dw_letters_of_resP hw4 hw5 b1 b2 h
  obtain ⟨s, t, hs, ht, -, hd, hP⟩ := h
  have hs1 := dw_s_lt_one F ht hd hw4 hw5 b1
  have ht1 := dw_t_lt_one F hs hd hw4 hw5 b2
  have hB := hP.1.1.1.1.1.1.2
  rcases dw3_split F hw4 hw5 b3 b4 hs1 ht1 L4 L5 with h | h | h
  · exact (hB.1 h).elim
  · exact (hB.2.1 h).elim
  · exact h

/-- [OPEN] **The special piece with the double wall reduced to its special stratum, Rupert form**: `OpenSpecialP`
with `Q45ResWQ` in place of `Q45ResWP` (equivalent to it: `openSpecialQ_iff_P`). -/
def OpenSpecialQ : Prop := ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), ¬ H24K.SAT.OB1 x →
  1 ≤ oblX0 x 4 → 1 ≤ oblX0 x 5 →
  oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0 →
  0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3 →
  0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4 →
  0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5 →
  Q45ResWQ F → HoleFull x F → IsRupert (univ.image x)

/-- [PROVED] `OpenSpecialQ ↔ OpenSpecialP` (`q45ResWQ_of_P`; the other direction is `Q45ResWQ ⊆ Q45ResWP`). -/
theorem openSpecialQ_iff_P : OpenSpecialQ ↔ OpenSpecialP :=
  ⟨fun h x F hO h4 h5 b1 b2 b3 b4 hr hF => h x F hO h4 h5 b1 b2 b3 b4 (q45ResWQ_of_P b1 b2 b3 b4 hr) hF,
    fun h x F hO h4 h5 b1 b2 b3 b4 hr hF => h x F hO h4 h5 b1 b2 b3 b4 hr.1 hF⟩

/-- [PROVED] Generic + special (double wall reduced to `DwSpec`) assemble to `Open24Rupert`. -/
theorem open24Rupert_of_split_Q (h1 : OpenOB1) (h2 : OpenSpecialQ) : Open24Rupert :=
  open24Rupert_of_split_P h1 (openSpecialQ_iff_P.1 h2)

end DwSpecial

end Minimality.T24.OSpec

namespace Minimality.T24.Cell

/-- [PROVED] `CellCoverEmpty L` and `OSpec.OpenSpecialQ` give `Stmt.Open24Rupert` (OSPEC22). -/
theorem open24Rupert_of_cellCoverEmpty_Q {L : List Cell24} (hN : CellCoverEmpty L) (hS : OSpec.OpenSpecialQ) :
    Open24Rupert :=
  OSpec.open24Rupert_of_split_Q (openOB1_of_cellCoverEmpty hN) hS

/-- [PROVED] Headline chain with `cells28` after OSPEC22: `CellCoverEmpty cells28` and `OSpec.OpenSpecialQ` give
`Open24Rupert`. -/
theorem open24Rupert_of_cellCoverEmpty28_Q (hN : CellCoverEmpty cells28) (hS : OSpec.OpenSpecialQ) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmpty_Q hN hS

end Minimality.T24.Cell
