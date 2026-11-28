module

public import Minimality.Type24OffOB1DW2
public import Minimality.Type24Wall3Cover

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

**OSPEC23** (section `DwSpecE26`, notes section 2k): on `DwSpec` without `DwHorizOK` the e26 view (`τ > 0`) or its
mirror (`τ < 0`) is a lex cell, `τ = ⟪x 0 - x 1, x 2 - x 6⟫` (`dw4_e26`, `dw4_e26_sym`, `lexAny_of_dwSpec`).  On the
double wall `0345` is down at level 2 and `126` up (parallel faces); `236` is up because its dihedral sign is
`⟪x 3 - x 6, m*⟫` with `m* = -⟪d, e5⟫ e4 + ⟪d, e4⟫ e5` the horizontal normal of the bottom edge `2 6` (two Cramer
identities, `dw4_up7`), and `⟪x 3 - x 6, m*⟫ ≤ 0` would make both junctions rise at `m*` (`3` extreme along `m*`, from
the facet `236`): `DwHorizOK` inside the cone, a `DwSpec` letter on a boundary ray (`dw4_x3_pos`).  The rim `0 1 6 3 5`
has `6 < 1` (the angle at `6` is acute on `DwSpec`, `dw4_angles`), `1 < 0` (`τ > 0`), `3 < 5` and `0 ≠ 5`
(`robUniLex_five_dw4`).  Residue `Q45ResWQT` (double-wall piece inside `τ = 0`, codim 2), **`OpenSpecialQT`**
(`openSpecialQT_iff_Q`), chains `..._QT`, also for the `E` / `EP` / `E4` cell chains (`openSpecialO_of_QT`).
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

section DwSpecE26
open Minimality.LexCell

/-- The horizontal normal of the bottom edge `2 6` in the cone `(e4, e5)`: `m* = -⟪d, e5⟫ e4 + ⟪d, e4⟫ e5`
(`d = x 6 - x 2`; `⟪d, m*⟫ = 0`). -/
noncomputable def dwMs (x : Fin 7 → ℝ³) : ℝ³ := dwM x (-⟪x 6 - x 2, x 5 - x 0⟫) ⟪x 6 - x 2, x 4 - x 0⟫

theorem dwMs_inner (v : ℝ³) : ⟪v, dwMs x⟫ =
    -⟪x 6 - x 2, x 5 - x 0⟫ * ⟪v, x 4 - x 0⟫ + ⟪x 6 - x 2, x 4 - x 0⟫ * ⟪v, x 5 - x 0⟫ := by
  rw [dwMs, dwM, inner_add_right, real_inner_smul_right, real_inner_smul_right]

theorem dwMs_d : ⟪x 6 - x 2, dwMs x⟫ = 0 := by rw [dwMs_inner]; ring

/-- On the double wall a top vertex `v` has `⟪x v - x 0, m*⟫ = (b_v + c_v) κ`, `κ = ⟪x 2 - x 1, m*⟫`. -/
theorem dw4_ms_top (F : S0xFac 9 s0x_S24 x) {v : Fin 7} (hv : oblX0 x v = 1) :
    ⟪x v - x 0, dwMs x⟫ = (oblX2 x v + oblX6 x v) * ⟪x 2 - x 1, dwMs x⟫ := by
  have h6 : ⟪x 6 - x 1, dwMs x⟫ = ⟪x 2 - x 1, dwMs x⟫ := by
    have e : x 6 - x 1 = (x 6 - x 2) + (x 2 - x 1) := by abel
    rw [e, inner_add_left, dwMs_d, zero_add]
  rw [dw3_e F hv, inner_add_left, real_inner_smul_left, real_inner_smul_left, h6]; ring

/-- `x 6 ≠ x 2`. -/
theorem dw4_d_ne (F : S0xFac 9 s0x_S24 x) : x 6 - x 2 ≠ 0 := by
  intro h
  have e := F.inner_sub 0 6 2
  rw [h, inner_zero_right, F.zero 0 2 (by decide)] at e
  linarith [F.neg 0 6 (by decide)]

/-- `⟪d, e4⟫` and `⟪d, e5⟫` do not both vanish (`dw3_comb`). -/
theorem dw4_d_not_both (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1)
    (b3 : 0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4)
    (b4 : 0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5)
    (h4 : ⟪x 6 - x 2, x 4 - x 0⟫ = 0) (h5 : ⟪x 6 - x 2, x 5 - x 0⟫ = 0) : False := by
  have hΔ := dw3_delta_pos F hw4 hw5 b3 b4
  have K : (oblX2 x 5 * oblX6 x 4 - oblX2 x 4 * oblX6 x 5) * ⟪x 6 - x 2, x 6 - x 2⟫ =
      (oblX2 x 5 + oblX6 x 5) * ⟪x 6 - x 2, x 4 - x 0⟫ - (oblX2 x 4 + oblX6 x 4) * ⟪x 6 - x 2, x 5 - x 0⟫ := by
    rw [← real_inner_smul_right, dw3_comb F hw4 hw5, inner_sub_right, real_inner_smul_right, real_inner_smul_right]
  rw [h4, h5] at K
  have hd : 0 < ⟪x 6 - x 2, x 6 - x 2⟫ := real_inner_self_pos.2 (dw4_d_ne F)
  nlinarith [mul_pos hΔ hd]

/-- **`κ = ⟪x 2 - x 1, m*⟫ > 0`** on `DwSpec` (the cone `(e4, e5)` contains `m*`, `⟪e4, m*⟫ > 0`). -/
theorem dw4_kappa_pos (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1)
    (b3 : 0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4)
    (b4 : 0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5) (hS : DwSpec x) :
    0 < ⟪x 2 - x 1, dwMs x⟫ := by
  obtain ⟨hg, hd4, hd5, -, -⟩ := hS
  have T := M4.type24OfFac F
  have hl4 : 0 < oblX2 x 4 + oblX6 x 4 := by
    linarith [T.X2_pos (v := 4) (by decide), T.X6_pos (v := 4) (by decide)]
  have hE4 : 0 < ⟪x 4 - x 0, x 4 - x 0⟫ := real_inner_self_pos.2 (dw3_e4_ne F)
  have he : 0 < ⟪x 4 - x 0, dwMs x⟫ := by
    rw [dwMs_inner]
    rcases hd5.lt_or_eq with h5 | h5
    · nlinarith [mul_pos (neg_pos.2 h5) hE4, mul_nonneg hd4 hg.le]
    · rcases hd4.lt_or_eq with h4 | h4
      · rw [h5]; nlinarith [mul_pos h4 hg]
      · exact (dw4_d_not_both F hw4 hw5 b3 b4 h4.symm h5).elim
  rw [dw4_ms_top F hw4] at he
  exact pos_of_mul_pos_right he hl4.le

/-- **`3` is extreme along `m*` in the top face** (the facet `236`: `b3 + c3 > b4 + c4`, `b5 + c5`). -/
theorem dw4_three_ext (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1) {s t : ℝ}
    (hd : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (b3 : 0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4)
    (b4 : 0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5) (hS : DwSpec x) :
    0 < ⟪x 3 - x 4, dwMs x⟫ ∧ 0 < ⟪x 3 - x 5, dwMs x⟫ := by
  have hw3 : oblX0 x 3 = 1 := by rw [obl3_a F hd, hw4, hw5]; ring
  have hk := dw4_kappa_pos F hw4 hw5 b3 b4 hS
  have f1 : F.f 7 (x 1) < 0 := F.neg 7 1 (by decide)
  have ev : ∀ v : Fin 7, oblX0 x v = 1 → F.f 7 (x v) = F.f 7 (x 0) - (oblX2 x v + oblX6 x v) * F.f 7 (x 1) := by
    intro v hv
    have e := M4.fac_eval F 7 v
    rw [F.zero 7 2 (by decide), F.zero 7 6 (by decide), hv] at e
    linarith
  have e3 := ev 3 hw3
  rw [F.zero 7 3 (by decide)] at e3
  have e4 := ev 4 hw4
  have e5 := ev 5 hw5
  have n4 : F.f 7 (x 4) < 0 := F.neg 7 4 (by decide)
  have n5 : F.f 7 (x 5) < 0 := F.neg 7 5 (by decide)
  have l4 : oblX2 x 4 + oblX6 x 4 < oblX2 x 3 + oblX6 x 3 := by nlinarith
  have l5 : oblX2 x 5 + oblX6 x 5 < oblX2 x 3 + oblX6 x 3 := by nlinarith
  have q : ∀ v : Fin 7, oblX0 x v = 1 →
      ⟪x 3 - x v, dwMs x⟫ = (oblX2 x 3 + oblX6 x 3 - (oblX2 x v + oblX6 x v)) * ⟪x 2 - x 1, dwMs x⟫ := by
    intro v hv
    have e : x 3 - x v = (x 3 - x 0) - (x v - x 0) := by abel
    rw [e, inner_sub_left, dw4_ms_top F hw3, dw4_ms_top F hv]; ring
  rw [q 4 hw4, q 5 hw5]
  exact ⟨mul_pos (by linarith) hk, mul_pos (by linarith) hk⟩

/-- **`⟪x 3 - x 6, m*⟫ > 0` on `DwSpec` without `DwHorizOK`**: otherwise both junctions rise at `m*` (`3` extreme),
which is `DwHorizOK` when `m*` is inside the cone, and contradicts a `DwSpec` letter on a boundary ray. -/
theorem dw4_x3_pos (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1) {s t : ℝ}
    (hd : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (b3 : 0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4)
    (b4 : 0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5) (hS : DwSpec x) (hH : ¬ DwHorizOK x) :
    0 < ⟪x 3 - x 6, dwMs x⟫ := by
  obtain ⟨h34, h35⟩ := dw4_three_ext F hw4 hw5 hd b3 b4 hS
  obtain ⟨-, hd4, hd5, hq1, hp2⟩ := hS
  by_contra hc
  push Not at hc
  have hp : 0 < ⟪x 6 - x 4, dwMs x⟫ := by
    have e : x 6 - x 4 = (x 3 - x 4) - (x 3 - x 6) := by abel
    rw [e, inner_sub_left]; linarith
  have hq : 0 < ⟪x 2 - x 5, dwMs x⟫ := by
    have e : x 2 - x 5 = (x 3 - x 5) - (x 3 - x 6) - (x 6 - x 2) := by abel
    rw [e, inner_sub_left, inner_sub_left, dwMs_d]; linarith
  rcases hd5.lt_or_eq with h5 | h5
  · rcases hd4.lt_or_eq with h4 | h4
    · exact hH ⟨_, _, neg_pos.2 h5, h4, Or.inl ⟨hp, hq⟩⟩
    · rw [dwMs_inner, ← h4] at hq
      nlinarith
  · rw [dwMs_inner, h5] at hp
    nlinarith

/-- Coordinate identities for the dihedral sign. -/
theorem dw4_bac (a b c d : ℝ³) : ⟪a, cross b (cross c d)⟫ = ⟪a, c⟫ * ⟪b, d⟫ - ⟪a, d⟫ * ⟪b, c⟫ := by
  simp only [t234_inner3, cross_apply_zero, cross_apply_one, cross_apply_two]; ring

theorem dw4_cyc2 (a b c : ℝ³) : ⟪a, cross b c⟫ = ⟪b, cross c a⟫ := by
  simp only [t234_inner3, cross_apply_zero, cross_apply_one, cross_apply_two]; ring

/-- **`236` is up in the e26 view when `⟪x 3 - x 6, m*⟫ > 0`** (two Cramer identities: `N7 ∥ (x2 - x6) × (x3 - x6)`,
`N3 ∥ e4 × e5`, so `O1 O2 ⟪N7, N3⟫ = -⟪x3 - x6, m*⟫ f3(x1) f7(x0)`; `O1 O2 > 0` by `e26_orient`). -/
theorem dw4_up7 (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (hs : 0 < s)
    (hd : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) (h : 0 < ⟪x 3 - x 6, dwMs x⟫) : E26Up F 7 := by
  have o := (e26_orient F hs hd).2
  have n7d : ⟪F.N 7, x 2 - x 6⟫ = 0 := by
    rw [F.inner_sub 7 2 6, F.zero 7 2 (by decide), F.zero 7 6 (by decide)]; ring
  have n7y : ⟪F.N 7, x 3 - x 6⟫ = 0 := by
    rw [F.inner_sub 7 3 6, F.zero 7 3 (by decide), F.zero 7 6 (by decide)]; ring
  have n7a : ⟪F.N 7, x 0 - x 6⟫ < 0 := by
    rw [F.inner_sub 7 0 6, F.zero 7 6 (by decide)]; linarith [F.neg 7 0 (by decide)]
  have n3e4 : ⟪F.N 3, x 4 - x 0⟫ = 0 := by
    rw [F.inner_sub 3 4 0, F.zero 3 4 (by decide), F.zero 3 0 (by decide)]; ring
  have n3e5 : ⟪F.N 3, x 5 - x 0⟫ = 0 := by
    rw [F.inner_sub 3 5 0, F.zero 3 5 (by decide), F.zero 3 0 (by decide)]; ring
  have n3g : ⟪F.N 3, x 1 - x 0⟫ < 0 := by
    rw [F.inner_sub 3 1 0, F.zero 3 0 (by decide)]; linarith [F.neg 3 1 (by decide)]
  have c1 := t234_cramer (F.N 7) (x 0 - x 6) (x 2 - x 6) (F.N 3) (x 3 - x 6)
  rw [n7y, n7d] at c1
  have c2 := t234_cramer (F.N 3) (x 1 - x 0) (x 4 - x 0) (cross (x 3 - x 6) (x 2 - x 6)) (x 5 - x 0)
  rw [n3e5, n3e4] at c2
  have r1 : ⟪x 3 - x 6, cross (x 2 - x 6) (F.N 3)⟫ = ⟪F.N 3, cross (x 3 - x 6) (x 2 - x 6)⟫ :=
    e26_triple_cyc _ _ _
  have r2 := dw4_bac (x 5 - x 0) (x 4 - x 0) (x 3 - x 6) (x 2 - x 6)
  have r3 : ⟪x 0 - x 6, cross (x 2 - x 6) (x 3 - x 6)⟫ = ⟪x 2 - x 6, cross (x 3 - x 6) (x 0 - x 6)⟫ :=
    dw4_cyc2 _ _ _
  have r4 : ⟪x 1 - x 0, cross (x 4 - x 0) (x 5 - x 0)⟫ = ⟪x 4 - x 0, cross (x 5 - x 0) (x 1 - x 0)⟫ :=
    dw4_cyc2 _ _ _
  have r5 := dwMs_inner (x := x) (x 3 - x 6)
  have hm : ⟪x 5 - x 0, x 3 - x 6⟫ * ⟪x 4 - x 0, x 2 - x 6⟫ - ⟪x 5 - x 0, x 2 - x 6⟫ * ⟪x 4 - x 0, x 3 - x 6⟫ =
      -⟪x 3 - x 6, dwMs x⟫ := by
    rw [r5]
    have a1 : ⟪x 4 - x 0, x 2 - x 6⟫ = -⟪x 6 - x 2, x 4 - x 0⟫ := by
      rw [real_inner_comm, ← neg_sub (x 6) (x 2), inner_neg_left]
    have a2 : ⟪x 5 - x 0, x 2 - x 6⟫ = -⟪x 6 - x 2, x 5 - x 0⟫ := by
      rw [real_inner_comm, ← neg_sub (x 6) (x 2), inner_neg_left]
    rw [a1, a2, real_inner_comm (x 4 - x 0) (x 3 - x 6), real_inner_comm (x 5 - x 0) (x 3 - x 6)]; ring
  set O1 := ⟪x 4 - x 0, cross (x 5 - x 0) (x 1 - x 0)⟫
  set O2 := ⟪x 2 - x 6, cross (x 3 - x 6) (x 0 - x 6)⟫
  set W := ⟪F.N 3, cross (x 3 - x 6) (x 2 - x 6)⟫
  set n73 := ⟪F.N 7, F.N 3⟫
  -- c1: O2 n73 = -W f7(x0); c2: O1 W = ⟪y, m*⟫ f3(x1)
  have e1 : O2 * n73 = -(W * ⟪F.N 7, x 0 - x 6⟫) := by rw [← r3, ← r1]; linarith
  have e2 : O1 * W = ⟪x 3 - x 6, dwMs x⟫ * ⟪F.N 3, x 1 - x 0⟫ := by
    rw [← r4]; rw [r2, hm] at c2; linarith
  have key : (O1 * O2) * n73 = -(⟪x 3 - x 6, dwMs x⟫ * ⟪F.N 3, x 1 - x 0⟫ * ⟪F.N 7, x 0 - x 6⟫) := by
    calc (O1 * O2) * n73 = O1 * (O2 * n73) := by ring
      _ = -((O1 * W) * ⟪F.N 7, x 0 - x 6⟫) := by rw [e1]; ring
      _ = _ := by rw [e2]
  have hp : 0 < ⟪x 3 - x 6, dwMs x⟫ * ⟪F.N 3, x 1 - x 0⟫ * ⟪F.N 7, x 0 - x 6⟫ :=
    mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg h n3g) n7a
  have hn : n73 < 0 := by
    by_contra hc; push Not at hc
    nlinarith [mul_nonneg o.le hc]
  refine Or.inr ⟨n7d, Or.inl ?_⟩
  rw [inner_neg_right]; linarith

/-- **The two bottom angles at `2` and `6` are acute on `DwSpec`** (`⟪d, e4⟫ ≥ 0 ≥ ⟪d, e5⟫`, frame signs). -/
theorem dw4_angles (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1) (hS : DwSpec x) :
    0 < ⟪x 1 - x 6, x 2 - x 6⟫ ∧ 0 < ⟪x 1 - x 2, x 6 - x 2⟫ := by
  obtain ⟨-, hd4, hd5, -, -⟩ := hS
  have T := M4.type24OfFac F
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (by decide)
  have hc4 : 0 < oblX6 x 4 := T.X6_pos (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (by decide)
  set X := ⟪x 1 - x 6, x 2 - x 6⟫
  set Y := ⟪x 1 - x 2, x 6 - x 2⟫
  have g2 : ⟪x 6 - x 2, x 2 - x 1⟫ = -Y := by
    rw [real_inner_comm, ← neg_sub (x 1) (x 2), inner_neg_left]
  have g6 : ⟪x 6 - x 2, x 6 - x 1⟫ = X := by
    rw [← neg_sub (x 2) (x 6), ← neg_sub (x 1) (x 6), inner_neg_neg, real_inner_comm]
  have hXY : X + Y = ⟪x 6 - x 2, x 6 - x 2⟫ := by
    have e : x 6 - x 2 = (x 6 - x 1) - (x 2 - x 1) := by abel
    have e' : ⟪x 6 - x 2, x 6 - x 2⟫ = ⟪x 6 - x 2, x 6 - x 1⟫ - ⟪x 6 - x 2, x 2 - x 1⟫ := by
      conv_lhs => rw [show x 6 - x 2 = (x 6 - x 1) - (x 2 - x 1) by abel]
      rw [inner_sub_right]
      rw [show (x 6 - x 1) - (x 2 - x 1) = x 6 - x 2 by abel]
    rw [e', g2, g6]; ring
  have hdd : 0 < ⟪x 6 - x 2, x 6 - x 2⟫ := real_inner_self_pos.2 (dw4_d_ne F)
  have k : ∀ v : Fin 7, oblX0 x v = 1 → ⟪x 6 - x 2, x v - x 0⟫ = oblX6 x v * X - oblX2 x v * Y := by
    intro v hv
    rw [dw3_e F hv, inner_add_right, real_inner_smul_right, real_inner_smul_right, g2, g6]; ring
  rw [k 4 hw4] at hd4
  rw [k 5 hw5] at hd5
  constructor
  · by_contra hc; push Not at hc
    nlinarith [mul_nonneg hb4.le (by nlinarith : (0:ℝ) ≤ -Y)]
  · by_contra hc; push Not at hc
    nlinarith [mul_nonneg hc5.le (by nlinarith : (0:ℝ) ≤ -X)]

/-- **A 5-cycle with `z1 < z0`, `z2 < z1`, `z3 < z4` and `z0`, `z4` comparable is `RobUniLex`** (case `z0 < z4`
with the derived `z1, z2 < z4`; case `z4 < z0` with `z3 < z0`). -/
theorem robUniLex_five_dw4 (z : ZMod 5 → ℝ × ℝ × ℝ) (h10 : LexLt3 (z 1) (z 0)) (h21 : LexLt3 (z 2) (z 1))
    (h20 : LexLt3 (z 2) (z 0)) (h34 : LexLt3 (z 3) (z 4))
    (hc : (LexLt3 (z 0) (z 4) ∧ LexLt3 (z 1) (z 4) ∧ LexLt3 (z 2) (z 4)) ∨
      (LexLt3 (z 4) (z 0) ∧ LexLt3 (z 3) (z 0))) : RobUniLex z := by
  intro B b c d hb hbc hcd hd
  have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by revert B; decide
  have hbcd : (b = 1 ∧ c = 2 ∧ d = 3) ∨ (b = 1 ∧ c = 2 ∧ d = 4) ∨
      (b = 1 ∧ c = 3 ∧ d = 4) ∨ (b = 2 ∧ c = 3 ∧ d = 4) := by omega
  rcases hc with ⟨h04, h14, h24⟩ | ⟨h40, h30⟩ <;>
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
    | exact Or.inl ‹_›
    | exact Or.inr (Or.inl ‹_›)
    | exact Or.inr (Or.inr (Or.inl ‹_›))
    | exact Or.inr (Or.inr (Or.inr ‹_›))

/-- **The e26 view on the special double-wall stratum** (`τ = ⟪x 0 - x 1, x 2 - x 6⟫ > 0`): `126` up (parallel
to `0345`), `0345` down (level 2), `236` up (`dw4_up7`, `dw4_x3_pos`), and the rim `0 1 6 3 5` with `6 < 1 < 0`
(the acute angle at `6`, `τ > 0`) and `3 < 5`, `0 ≠ 5` (`DwSpec`) is `RobUniLex`. -/
theorem dw4_e26 (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1) {s t : ℝ} (hs : 0 < s)
    (ht1 : t < 1) (hd : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (b3 : 0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4)
    (b4 : 0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5) (hS : DwSpec x) (hH : ¬ DwHorizOK x)
    (hτ : 0 < ⟪x 0 - x 1, x 2 - x 6⟫) : E26ViewOK F := by
  have h7 := dw4_up7 F hs hd (dw4_x3_pos F hw4 hw5 hd b3 b4 hS hH)
  have h5 : E26Up F 5 := by
    refine Or.inr ⟨by rw [F.inner_sub 5 2 6, F.zero 5 2 (by decide), F.zero 5 6 (by decide)]; ring, Or.inl ?_⟩
    rw [inner_neg_right]; linarith [bs_n53_neg F hw4 hw5]
  have hw3 : oblX0 x 3 = 1 := by rw [obl3_a F hd, hw4, hw5]; ring
  have hf26 : F.f 3 (x 2) ≤ F.f 3 (x 6) := by
    have e2 := M4.fac_eval F 3 2
    have e6 := M4.fac_eval F 3 6
    -- `f3` is constant on the bottom plane `a = 0`: from `x 4`, `x 5` on the top face
    have e4 := M4.fac_eval F 3 4
    have e5 := M4.fac_eval F 3 5
    rw [F.zero 3 4 (by decide), F.zero 3 0 (by decide), hw4] at e4
    rw [F.zero 3 5 (by decide), F.zero 3 0 (by decide), hw5] at e5
    have T := M4.type24OfFac F
    have hb4 : 0 < oblX2 x 4 := T.X2_pos (by decide)
    have hc5 : 0 < oblX6 x 5 := T.X6_pos (by decide)
    rw [hw4, hw5] at b3 b4
    have hΔ : 0 < oblX2 x 5 * oblX6 x 4 - oblX2 x 4 * oblX6 x 5 := by
      nlinarith [mul_pos (sub_pos.2 (by linarith : oblX2 x 4 < oblX2 x 5)) (T.X6_pos (v := 4) (by decide)),
        mul_pos hb4 (sub_pos.2 (by linarith : oblX6 x 5 < oblX6 x 4))]
    set A := F.f 3 (x 2) - F.f 3 (x 1)
    set B := F.f 3 (x 6) - F.f 3 (x 1)
    have hA : A = 0 := by
      have : (oblX2 x 5 * oblX6 x 4 - oblX2 x 4 * oblX6 x 5) * A = 0 := by linear_combination -(oblX6 x 4) * e5 + oblX6 x 5 * e4
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · exact h
    have hB : B = 0 := by
      have : (oblX2 x 5 * oblX6 x 4 - oblX2 x 4 * oblX6 x 5) * B = 0 := by linear_combination -(oblX2 x 5) * e4 + oblX2 x 4 * e5
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · exact h
    linarith
  obtain ⟨a6, -⟩ := dw4_angles F hw4 hw5 hS
  obtain ⟨hg, hd4, hd5, -, -⟩ := hS
  -- level-1 facts, `D' = x 2 - x 6`
  have l10 : ⟪x 1, x 2 - x 6⟫ < ⟪x 0, x 2 - x 6⟫ := by rw [inner_sub_left] at hτ; linarith
  have l61 : ⟪x 6, x 2 - x 6⟫ < ⟪x 1, x 2 - x 6⟫ := by rw [inner_sub_left] at a6; linarith
  have l35 : ⟪x 3, x 2 - x 6⟫ < ⟪x 5, x 2 - x 6⟫ := by
    have e : x 5 - x 3 = (1 - t) • (x 5 - x 0) - s • (x 4 - x 0) := by
      rw [show x 5 - x 3 = (x 5 - x 0) - (x 3 - x 0) by abel, hd]; module
    have h' : ⟪x 5 - x 3, x 2 - x 6⟫ = s * ⟪x 6 - x 2, x 4 - x 0⟫ - (1 - t) * ⟪x 6 - x 2, x 5 - x 0⟫ := by
      rw [e, inner_sub_left, real_inner_smul_left, real_inner_smul_left, ← neg_sub (x 6) (x 2), inner_neg_right,
        inner_neg_right, real_inner_comm (x 5 - x 0), real_inner_comm (x 4 - x 0)]; ring
    have : 0 < ⟪x 5 - x 3, x 2 - x 6⟫ := by
      rw [h']
      rcases hd5.lt_or_eq with h5' | h5'
      · nlinarith [mul_nonneg hs.le hd4, mul_pos (sub_pos.2 ht1) (neg_pos.2 h5')]
      · rcases hd4.lt_or_eq with h4' | h4'
        · rw [h5']; nlinarith [mul_pos hs h4']
        · exact (dw4_d_not_both F hw4 hw5 b3 b4 h4'.symm h5').elim
    rw [inner_sub_left] at this; linarith
  have f2 : ∀ v w : Fin 7, v ∈ s0x_S24 3 → w ∈ s0x_S24 3 → ⟪x v, -F.N 3⟫ = ⟪x w, -F.N 3⟫ := by
    intro v w hv hw
    have e := F.inner_sub 3 v w
    rw [F.zero 3 v hv, F.zero 3 w hw, real_inner_comm, inner_sub_left] at e
    rw [inner_neg_right, inner_neg_right]; linarith
  refine ⟨h5, h7, Or.inr ⟨e26_dn3 F hf26, ?_⟩⟩
  refine robUniLex_five_dw4 (e26Z F rimEB) (lexLt3_of_fst l10) (lexLt3_of_fst l61)
    (lexLt3_of_fst (by show ⟪x 6, x 2 - x 6⟫ < ⟪x 0, x 2 - x 6⟫; linarith)) (lexLt3_of_fst l35) ?_
  rcases hd5.lt_or_eq with h5' | h5'
  · have l05 : ⟪x 0, x 2 - x 6⟫ < ⟪x 5, x 2 - x 6⟫ := by
      have : ⟪x 5 - x 0, x 2 - x 6⟫ = -⟪x 6 - x 2, x 5 - x 0⟫ := by
        rw [real_inner_comm, ← neg_sub (x 6) (x 2), inner_neg_left]
      rw [inner_sub_left] at this; linarith
    refine Or.inl ⟨lexLt3_of_fst l05, lexLt3_of_fst ?_, lexLt3_of_fst ?_⟩
    · show ⟪x 1, x 2 - x 6⟫ < ⟪x 5, x 2 - x 6⟫; linarith
    · show ⟪x 6, x 2 - x 6⟫ < ⟪x 5, x 2 - x 6⟫; linarith
  · have e50 : ⟪x 5, x 2 - x 6⟫ = ⟪x 0, x 2 - x 6⟫ := by
      have : ⟪x 5 - x 0, x 2 - x 6⟫ = -⟪x 6 - x 2, x 5 - x 0⟫ := by
        rw [real_inner_comm, ← neg_sub (x 6) (x 2), inner_neg_left]
      rw [inner_sub_left, h5', neg_zero] at this; linarith
    have k50 : ⟪x 5, x 0 - x 4⟫ < ⟪x 0, x 0 - x 4⟫ := by
      have : ⟪x 5 - x 0, x 0 - x 4⟫ = -⟪x 4 - x 0, x 5 - x 0⟫ := by
        rw [show x 0 - x 4 = -(x 4 - x 0) by abel, inner_neg_right, real_inner_comm]
      rw [inner_sub_left] at this; linarith
    refine Or.inr ⟨lexLt3_of_thd e50 (f2 5 0 (by decide) (by decide)) k50, lexLt3_of_fst ?_⟩
    show ⟪x 3, x 2 - x 6⟫ < ⟪x 0, x 2 - x 6⟫; linarith


/-- `DwSpec` is mirror symmetric (`π = (2 6)(4 5)`). -/
theorem dwSpec_sym (hS : DwSpec x) : DwSpec (x ∘ Sym.pi24) := by
  obtain ⟨hg, hd4, hd5, hq1, hp2⟩ := hS
  simp only [DwSpec, Function.comp_apply, Sym.pi24_0, Sym.pi24_2, Sym.pi24_4, Sym.pi24_5, Sym.pi24_6]
  have a4 : ⟪x 2 - x 6, x 4 - x 0⟫ = -⟪x 6 - x 2, x 4 - x 0⟫ := by rw [← neg_sub (x 6) (x 2), inner_neg_left]
  have a5 : ⟪x 2 - x 6, x 5 - x 0⟫ = -⟪x 6 - x 2, x 5 - x 0⟫ := by rw [← neg_sub (x 6) (x 2), inner_neg_left]
  refine ⟨by rw [real_inner_comm]; exact hg, by rw [a5]; linarith, by rw [a4]; linarith, hp2, hq1⟩

/-- `DwHorizOK` is mirror symmetric. -/
theorem not_dwHoriz_sym (hH : ¬ DwHorizOK x) : ¬ DwHorizOK (x ∘ Sym.pi24) := by
  rintro ⟨α, β, hα, hβ, h⟩
  have e : dwM (x ∘ Sym.pi24) α β = dwM x β α := by
    simp only [dwM, Function.comp_apply, Sym.pi24_0, Sym.pi24_4, Sym.pi24_5]; abel
  simp only [e, Function.comp_apply, Sym.pi24_2, Sym.pi24_4, Sym.pi24_5, Sym.pi24_6] at h
  exact hH ⟨β, α, hβ, hα, h.imp (fun h => ⟨h.2, h.1⟩) (fun h => ⟨h.2, h.1⟩)⟩

/-- **The mirror e26 view on the special stratum** (`τ < 0`): `dw4_e26` for `π24 x`. -/
theorem dw4_e26_sym (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1) {s t : ℝ} (ht : 0 < t)
    (hs1 : s < 1) (hd : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (b3 : 0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4)
    (b4 : 0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5) (hS : DwSpec x) (hH : ¬ DwHorizOK x)
    (hτ : ⟪x 0 - x 1, x 2 - x 6⟫ < 0) : E26ViewOK (Sym.sym24 F) := by
  have o4 : oblX0 (x ∘ Sym.pi24) 4 = oblX0 x 5 := by rw [Sym.oblX0_comp_pi24]; simp
  have o5 : oblX0 (x ∘ Sym.pi24) 5 = oblX0 x 4 := by rw [Sym.oblX0_comp_pi24]; simp
  have p4 : oblX2 (x ∘ Sym.pi24) 4 = oblX6 x 5 := by rw [Sym.oblX2_comp_pi24]; simp
  have p5 : oblX2 (x ∘ Sym.pi24) 5 = oblX6 x 4 := by rw [Sym.oblX2_comp_pi24]; simp
  have q4 : oblX6 (x ∘ Sym.pi24) 4 = oblX2 x 5 := by rw [Sym.oblX6_comp_pi24]; simp
  have q5 : oblX6 (x ∘ Sym.pi24) 5 = oblX2 x 4 := by rw [Sym.oblX6_comp_pi24]; simp
  refine dw4_e26 (Sym.sym24 F) (by rw [o4, hw5]) (by rw [o5, hw4]) (s := t) (t := s) ht hs1 ?_ ?_ ?_
    (dwSpec_sym hS) (not_dwHoriz_sym hH) ?_
  · simp only [Function.comp_apply, Sym.pi24_0, Sym.pi24_3, Sym.pi24_4, Sym.pi24_5]
    rw [hd]; abel
  · rw [o4, o5, p4, p5]; linarith
  · rw [o4, o5, q4, q5]; linarith
  · simp only [Function.comp_apply, Sym.pi24_0, Sym.pi24_1, Sym.pi24_2, Sym.pi24_6]
    rw [← neg_sub (x 2) (x 6), inner_neg_right]; linarith

/-! ### The residue after the e26 views on `DwSpec`: the double-wall piece is the codim-2 stratum `τ = 0` -/

/-- `Q45ResWQ` with its double-wall piece inside `τ = ⟪x 0 - x 1, x 2 - x 6⟫ = 0`. -/
def Q45ResWQT (F : S0xFac 9 s0x_S24 x) : Prop :=
  Q45ResWQ F ∧ (oblX0 x 4 = 1 → oblX0 x 5 = 1 → ⟪x 0 - x 1, x 2 - x 6⟫ = 0)

/-- **On `DwSpec` without `DwHorizOK` and `τ ≠ 0` one of the e26 views is a lex cell.** -/
theorem lexAny_of_dwSpec (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1)
    (b1 : oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0)
    (b2 : 0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3)
    (b3 : 0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4)
    (b4 : 0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hd : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) (hS : DwSpec x) (hH : ¬ DwHorizOK x)
    (hτ : ⟪x 0 - x 1, x 2 - x 6⟫ ≠ 0) : Gen.LexAny F := by
  have hs1 := dw_s_lt_one F ht hd hw4 hw5 b1
  have ht1 := dw_t_lt_one F hs hd hw4 hw5 b2
  rcases lt_or_gt_of_ne hτ with h | h
  · exact lexAny_of_e26View_sym F (dw4_e26_sym F hw4 hw5 ht hs1 hd b3 b4 hS hH h)
  · exact lexAny_of_e26View F (dw4_e26 F hw4 hw5 hs ht1 hd b3 b4 hS hH h)

/-- [OPEN] **The special piece with the double wall reduced to `DwSpec ∩ {τ = 0}`, Rupert form**: `OpenSpecialQ`
with `Q45ResWQT` in place of `Q45ResWQ` (equivalent to it: `openSpecialQT_iff_Q`). -/
def OpenSpecialQT : Prop := ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), ¬ H24K.SAT.OB1 x →
  1 ≤ oblX0 x 4 → 1 ≤ oblX0 x 5 →
  oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0 →
  0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3 →
  0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4 →
  0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5 →
  Q45ResWQT F → HoleFull x F → IsRupert (univ.image x)

/-- [PROVED] `OpenSpecialQT ↔ OpenSpecialQ` (`lexAny_of_dwSpec`: off `τ = 0` the double-wall piece of `Q45ResWQ` is
`LexAny`, excluded by `HoleFull`). -/
theorem openSpecialQT_iff_Q : OpenSpecialQT ↔ OpenSpecialQ := by
  constructor
  · intro h x F hO h4 h5 b1 b2 b3 b4 hr hF
    refine h x F hO h4 h5 b1 b2 b3 b4 ⟨hr, fun hw4 hw5 => ?_⟩ hF
    by_contra hτ
    obtain ⟨⟨s, t, hs, ht, -, hd, -⟩, hQ⟩ := hr
    obtain ⟨hS, hH⟩ := hQ hw4 hw5
    exact hF.1.2.2.2.1 (lexAny_of_dwSpec F hw4 hw5 b1 b2 b3 b4 hs ht hd hS hH hτ)
  · exact fun h x F hO h4 h5 b1 b2 b3 b4 hr hF => h x F hO h4 h5 b1 b2 b3 b4 hr.1 hF

/-- [PROVED] Generic + special (double wall reduced to `DwSpec ∩ {τ = 0}`) assemble to `Open24Rupert`. -/
theorem open24Rupert_of_split_QT (h1 : OpenOB1) (h2 : OpenSpecialQT) : Open24Rupert :=
  open24Rupert_of_split_Q h1 (openSpecialQT_iff_Q.1 h2)

/-- [PROVED] `OpenSpecialP → OpenSpecialO` (the converse of `openSpecialP_of_openSpecialO`: off `Q45ResWP` a point
of `Q45ResWO` is `LexAny`, `q45_resP_local`). -/
theorem openSpecialO_of_P (h : OpenSpecialP) : OpenSpecialO := by
  intro x F hO h4 h5 b1 b2 b3 b4 hr hF
  obtain ⟨s, t, hs, ht, hst, hd, hr⟩ := hr
  rcases q45_resP_local F hs ht hst hd hr with hL | hr
  · exact (hF.1.2.2.2.1 hL).elim
  · exact h x F hO h4 h5 b1 b2 b3 b4 ⟨s, t, hs, ht, hst, hd, hr⟩ hF

/-- [PROVED] `OpenSpecialQT → OpenSpecialO`, for the cell chains that take `OpenSpecialO`. -/
theorem openSpecialO_of_QT (h : OpenSpecialQT) : OpenSpecialO :=
  openSpecialO_of_P (openSpecialQ_iff_P.1 (openSpecialQT_iff_Q.1 h))

end DwSpecE26

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

/-- [PROVED] `CellCoverEmpty L` and `OSpec.OpenSpecialQT` give `Stmt.Open24Rupert` (OSPEC23). -/
theorem open24Rupert_of_cellCoverEmpty_QT {L : List Cell24} (hN : CellCoverEmpty L) (hS : OSpec.OpenSpecialQT) :
    Open24Rupert :=
  OSpec.open24Rupert_of_split_QT (openOB1_of_cellCoverEmpty hN) hS

/-- [PROVED] Headline chain with `cells28` after OSPEC23. -/
theorem open24Rupert_of_cellCoverEmpty28_QT (hN : CellCoverEmpty cells28) (hS : OSpec.OpenSpecialQT) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmpty_QT hN hS

/-- [PROVED] The `E` cell chain with `OSpec.OpenSpecialQT` (OSPEC23). -/
theorem open24Rupert_of_cellCoverEmptyE28_QT (hN : CellCoverEmptyE cells28) (hS : OSpec.OpenSpecialQT) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmptyE28_O hN (OSpec.openSpecialO_of_QT hS)

/-- [PROVED] The `EP` cell chain with `OSpec.OpenSpecialQT` (OSPEC23). -/
theorem open24Rupert_of_cellCoverEmptyEP28_QT (hN : CellCoverEmptyEP cells28) (hS : OSpec.OpenSpecialQT) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmptyEP28_O hN (OSpec.openSpecialO_of_QT hS)

/-- [PROVED] Headline chain after WALL3 and OSPEC23: `CellCoverEmptyE4 cells28` and `OSpec.OpenSpecialQT`. -/
theorem open24Rupert_of_cellCoverEmptyE4_28_QT (hN : CellCoverEmptyE4 cells28) (hS : OSpec.OpenSpecialQT) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmptyE4_28_O hN (OSpec.openSpecialO_of_QT hS)

end Minimality.T24.Cell
