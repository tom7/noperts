module

public import Minimality.Type24OffOB1DW3

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.T24.Stmt Minimality.T24.Q45
  Minimality.T24.Reg Minimality.T24.A19

/-!
# Type 24 off `OB1`: the Bs rim on `s = 1` from one sign (job OSPEC25)

nopert229 notes/OPENSPECIAL-STRATEGY.md section 2l.  On `s = 1` (`x 3 - x 4 = t e5`, `e4 = x 4 - x 0`,
`e5 = x 5 - x 0`) and the tie `TBs1` (`⟪x 2, e5⟫ = ⟪x 6, e5⟫`) the MIRROR Bs view `(x 0 - x 5, x 4 - x 0, -N3)` has
its facet signs derived (`126` up for `a5 > 1` or on the double wall, `236` down since its `t` is `s = 1 ≤ 1`, `235`
up: rim `0 4 3 6 2`), and its rim needs only three level-1 comparisons along `-e5`:

  `3` below `4` (`⟪x 3 - x 4, e5⟫ = t |e5|² > 0`), `6` below `3` (`⟪x 3 - x 6, e5⟫ < 0`), `2` below `0`
  (`⟪x 2 - x 0, e5⟫ > 0`, automatic when the face angle at `0` is not obtuse: `⟪x 2 - x 0, e5⟫ = ⟪x 6 - x 0, e5⟫ >
  ⟪x 3 - x 0, e5⟫ = ⟪e4, e5⟫ + t |e5|²`).

A 5-cycle with `z3 < z2 < z1` and `z4 < z0` is `RobUniLex` whatever `z0` vs `z1` and `z3` vs `z4`
(`robUniLex_five_bs1`), so `BsCondSym` holds (`bsCondSym_of_s1`); `t = 1` with `TCt1` is the same for the main Bs view
(`bsCond_of_t1`).  This is the complement of the e26 letter `⟪x 3 - x 6, e5⟫ > 0` of `E26CondI` (OSPEC17): on the
`s = 1` / `TBs1` piece the two views' sign letters are now complementary, and a residue point there has
`⟪x 3 - x 6, e5⟫ ≥ 0` or an obtuse angle at `0` (`Bs1Res`), besides `¬ E26CondI` (`not_e26CondI_of_resS`).

Residue: `Q45ResWR2` (= `Q45ResWQT` with `Bs1Res`), **`OpenSpecialR2`** (equivalent to `OpenSpecialQT`,
`openSpecialR2_iff_QT`), chains `..._R2` (split, cell, 28, E, EP, E4) and `openSpecialQ_of_R2` for the chains that
take `OpenSpecialQ`.
-/

namespace Minimality.T24.OSpec

variable {x : Fin 7 → ℝ³}

section Bs1
open Minimality.LexCell

/-- **A 5-cycle with `z3 < z2 < z1`, `z3 < z1` and `z4 < z0` is `RobUniLex`** (every alternating quadruple has an
even position strictly below an odd one; no comparison of `z0, z1` or of `z3, z4` is needed). -/
theorem robUniLex_five_bs1 (z : ZMod 5 → ℝ × ℝ × ℝ) (h21 : LexLt3 (z 2) (z 1)) (h32 : LexLt3 (z 3) (z 2))
    (h31 : LexLt3 (z 3) (z 1)) (h40 : LexLt3 (z 4) (z 0)) : RobUniLex z := by
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
    | exact Or.inl ‹_›
    | exact Or.inr (Or.inl ‹_›)
    | exact Or.inr (Or.inr (Or.inl ‹_›))
    | exact Or.inr (Or.inr (Or.inr ‹_›))

/-- Level-1 differences as one inner product. -/
theorem bs1_isub (a b c d : ℝ³) : ⟪a, c - d⟫ - ⟪b, c - d⟫ = ⟪b - a, d - c⟫ := by
  rw [← inner_sub_left, ← inner_neg_neg, neg_sub, neg_sub]

/-- `x 5 ≠ x 0` (facet `235` contains `5`, not `0`). -/
theorem bs1_e5_ne (F : S0xFac 9 s0x_S24 x) : x 5 - x 0 ≠ 0 := by
  intro h0
  have e := F.inner_sub 6 5 0
  rw [h0, inner_zero_right, F.zero 6 5 (by decide)] at e
  linarith [F.neg 6 0 (by decide)]

/-- `x 4 ≠ x 0` (facet `346` contains `4`, not `0`). -/
theorem bs1_e4_ne (F : S0xFac 9 s0x_S24 x) : x 4 - x 0 ≠ 0 := by
  intro h0
  have e := F.inner_sub 8 4 0
  rw [h0, inner_zero_right, F.zero 8 4 (by decide)] at e
  linarith [F.neg 8 0 (by decide)]

/-- **The mirror Bs view on `s = 1`, `TBs1`**: with `6` below `3` and `2` below `0` along `e5` (and `126` up:
`a5 > 1` or the double wall) the mirror Bs view `(x 0 - x 5, x 4 - x 0, -N3)` is a lex cell, rim `0 4 3 6 2`. -/
theorem bsCondSym_of_s1 (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (hs : s = 1) (ht0 : 0 < t)
    (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (h36 : ⟪x 3 - x 6, x 5 - x 0⟫ < 0) (h20 : 0 < ⟪x 2 - x 0, x 5 - x 0⟫)
    (ha : 1 < oblX0 x 5 ∨ (oblX0 x 5 = 1 ∧ oblX0 x 4 = 1)) : BsCondSym F s := by
  refine ⟨ha, Or.inl hs.le, fun h => absurd h (by rw [hs]; exact lt_irrefl 1), fun _ => ?_⟩
  have h34 : x 3 - x 4 = t • (x 5 - x 0) := by
    rw [show x 3 - x 4 = (x 3 - x 0) - (x 4 - x 0) by abel, hdec, hs, one_smul]; abel
  have hE5 : 0 < ⟪x 5 - x 0, x 5 - x 0⟫ := real_inner_self_pos.2 (bs1_e5_ne F)
  -- level-1 depths `⟪x v, x 0 - x 5⟫`
  have A : ⟪x 3, x 0 - x 5⟫ < ⟪x 4, x 0 - x 5⟫ := by
    have := bs1_isub (x 4) (x 3) (x 0) (x 5)
    rw [show x 3 - x 4 = t • (x 5 - x 0) from h34, real_inner_smul_left] at this
    nlinarith [mul_pos ht0 hE5]
  have B : ⟪x 6, x 0 - x 5⟫ < ⟪x 3, x 0 - x 5⟫ := by
    have := bs1_isub (x 3) (x 6) (x 0) (x 5)
    rw [← neg_sub (x 3) (x 6), inner_neg_left] at this
    linarith
  have C : ⟪x 2, x 0 - x 5⟫ < ⟪x 0, x 0 - x 5⟫ := by
    have := bs1_isub (x 0) (x 2) (x 0) (x 5)
    linarith
  refine robUniLex_five_bs1 _ ?_ ?_ ?_ ?_
  · show LexPos3 (⟪x (Sym.pi24 5), x (Sym.pi24 0) - x (Sym.pi24 4)⟫ -
        ⟪x (Sym.pi24 3), x (Sym.pi24 0) - x (Sym.pi24 4)⟫) _ _
    simp only [Sym.pi24_0, Sym.pi24_3, Sym.pi24_4, Sym.pi24_5]
    exact Or.inl (by linarith)
  · show LexPos3 (⟪x (Sym.pi24 3), x (Sym.pi24 0) - x (Sym.pi24 4)⟫ -
        ⟪x (Sym.pi24 2), x (Sym.pi24 0) - x (Sym.pi24 4)⟫) _ _
    simp only [Sym.pi24_0, Sym.pi24_2, Sym.pi24_3, Sym.pi24_4]
    exact Or.inl (by linarith)
  · show LexPos3 (⟪x (Sym.pi24 5), x (Sym.pi24 0) - x (Sym.pi24 4)⟫ -
        ⟪x (Sym.pi24 2), x (Sym.pi24 0) - x (Sym.pi24 4)⟫) _ _
    simp only [Sym.pi24_0, Sym.pi24_2, Sym.pi24_4, Sym.pi24_5]
    exact Or.inl (by linarith)
  · show LexPos3 (⟪x (Sym.pi24 0), x (Sym.pi24 0) - x (Sym.pi24 4)⟫ -
        ⟪x (Sym.pi24 6), x (Sym.pi24 0) - x (Sym.pi24 4)⟫) _ _
    simp only [Sym.pi24_0, Sym.pi24_4, Sym.pi24_6]
    exact Or.inl (by linarith)

/-- `2` below `0` along `e5` is automatic on `s = 1`, `TBs1` when `6` is below `3` and the angle at `0` is not
obtuse: `⟪x 2 - x 0, e5⟫ = ⟪x 6 - x 0, e5⟫ > ⟪x 3 - x 0, e5⟫ = ⟪e4, e5⟫ + t |e5|²`. -/
theorem bs1_h20 {s t : ℝ} (hs : s = 1) (ht0 : 0 < t) (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hT : Q45TieLocusBs1 x) (h36 : ⟪x 3 - x 6, x 5 - x 0⟫ < 0) (hg : 0 ≤ ⟪x 4 - x 0, x 5 - x 0⟫) :
    0 < ⟪x 2 - x 0, x 5 - x 0⟫ := by
  unfold Q45TieLocusBs1 at hT
  have e3 : ⟪x 3 - x 0, x 5 - x 0⟫ = ⟪x 4 - x 0, x 5 - x 0⟫ + t * ⟪x 5 - x 0, x 5 - x 0⟫ := by
    rw [hdec, hs, one_smul, inner_add_left, real_inner_smul_left]
  have e6 : ⟪x 3 - x 6, x 5 - x 0⟫ = ⟪x 3 - x 0, x 5 - x 0⟫ - ⟪x 6 - x 0, x 5 - x 0⟫ := by
    rw [← inner_sub_left]; congr 1; abel
  have e2 : ⟪x 2 - x 0, x 5 - x 0⟫ = ⟪x 6 - x 0, x 5 - x 0⟫ := by
    rw [inner_sub_left, inner_sub_left, hT]
  have hE5 : 0 ≤ ⟪x 5 - x 0, x 5 - x 0⟫ := real_inner_self_nonneg
  nlinarith [mul_nonneg ht0.le hE5]

/-- **The main Bs view on `t = 1`, `TCt1`** (the mirror statement): with `2` below `3` and `6` below `0` along `e4`
(and `126` up: `a4 > 1` or the double wall) the Bs view `(x 0 - x 4, x 5 - x 0, -N3)` is a lex cell, rim
`0 5 3 2 6`. -/
theorem bsCond_of_t1 (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (hs0 : 0 < s) (ht : t = 1)
    (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (h32 : ⟪x 3 - x 2, x 4 - x 0⟫ < 0) (h60 : 0 < ⟪x 6 - x 0, x 4 - x 0⟫)
    (ha : 1 < oblX0 x 4 ∨ (oblX0 x 4 = 1 ∧ oblX0 x 5 = 1)) : BsCond F t := by
  refine ⟨ha, Or.inl ht.le, fun h => absurd h (by rw [ht]; exact lt_irrefl 1), fun _ => ?_⟩
  have h35 : x 3 - x 5 = s • (x 4 - x 0) := by
    rw [show x 3 - x 5 = (x 3 - x 0) - (x 5 - x 0) by abel, hdec, ht, one_smul]; abel
  have hE4 : 0 < ⟪x 4 - x 0, x 4 - x 0⟫ := real_inner_self_pos.2 (bs1_e4_ne F)
  have A : ⟪x 3, x 0 - x 4⟫ < ⟪x 5, x 0 - x 4⟫ := by
    have := bs1_isub (x 5) (x 3) (x 0) (x 4)
    rw [h35, real_inner_smul_left] at this
    nlinarith [mul_pos hs0 hE4]
  have B : ⟪x 2, x 0 - x 4⟫ < ⟪x 3, x 0 - x 4⟫ := by
    have := bs1_isub (x 3) (x 2) (x 0) (x 4)
    rw [← neg_sub (x 3) (x 2), inner_neg_left] at this
    linarith
  have C : ⟪x 6, x 0 - x 4⟫ < ⟪x 0, x 0 - x 4⟫ := by
    have := bs1_isub (x 0) (x 6) (x 0) (x 4)
    linarith
  refine robUniLex_five_bs1 _ ?_ ?_ ?_ ?_
  · show LexPos3 (⟪x 5, x 0 - x 4⟫ - ⟪x 3, x 0 - x 4⟫) _ _
    exact Or.inl (by linarith)
  · show LexPos3 (⟪x 3, x 0 - x 4⟫ - ⟪x 2, x 0 - x 4⟫) _ _
    exact Or.inl (by linarith)
  · show LexPos3 (⟪x 5, x 0 - x 4⟫ - ⟪x 2, x 0 - x 4⟫) _ _
    exact Or.inl (by linarith)
  · show LexPos3 (⟪x 0, x 0 - x 4⟫ - ⟪x 6, x 0 - x 4⟫) _ _
    exact Or.inl (by linarith)

/-- `6` below `0` along `e4` is automatic on `t = 1`, `TCt1` when `2` is below `3` and the angle at `0` is not
obtuse (mirror of `bs1_h20`). -/
theorem bs1_h60 {s t : ℝ} (hs0 : 0 < s) (ht : t = 1) (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hT : Q45TieLocusCt1 x) (h32 : ⟪x 3 - x 2, x 4 - x 0⟫ < 0) (hg : 0 ≤ ⟪x 4 - x 0, x 5 - x 0⟫) :
    0 < ⟪x 6 - x 0, x 4 - x 0⟫ := by
  unfold Q45TieLocusCt1 at hT
  have e3 : ⟪x 3 - x 0, x 4 - x 0⟫ = s * ⟪x 4 - x 0, x 4 - x 0⟫ + ⟪x 4 - x 0, x 5 - x 0⟫ := by
    rw [hdec, ht, one_smul, inner_add_left, real_inner_smul_left, real_inner_comm (x 4 - x 0) (x 5 - x 0)]
  have e2 : ⟪x 3 - x 2, x 4 - x 0⟫ = ⟪x 3 - x 0, x 4 - x 0⟫ - ⟪x 2 - x 0, x 4 - x 0⟫ := by
    rw [← inner_sub_left]; congr 1; abel
  have e6 : ⟪x 6 - x 0, x 4 - x 0⟫ = ⟪x 2 - x 0, x 4 - x 0⟫ := by
    rw [inner_sub_left, inner_sub_left, hT]
  have hE4 : 0 ≤ ⟪x 4 - x 0, x 4 - x 0⟫ := real_inner_self_nonneg
  nlinarith [mul_nonneg hs0.le hE4]

/-! ### The residue: the `s = 1` / `t = 1` tie letters made explicit -/

/-- What a residue point satisfies on the ties `TBs1` (`s = 1`) and `TCt1` (`t = 1`) with `126` up: `6` not below
`3` along `e5`, or an obtuse angle at `0` with `2` not below `0` (mirror on `t = 1`). -/
def Bs1Res (x : Fin 7 → ℝ³) (s t : ℝ) : Prop :=
  (s = 1 → Q45TieLocusBs1 x → (1 < oblX0 x 5 ∨ (oblX0 x 5 = 1 ∧ oblX0 x 4 = 1)) →
    0 ≤ ⟪x 3 - x 6, x 5 - x 0⟫ ∨ (⟪x 4 - x 0, x 5 - x 0⟫ < 0 ∧ ⟪x 2 - x 0, x 5 - x 0⟫ ≤ 0)) ∧
  (t = 1 → Q45TieLocusCt1 x → (1 < oblX0 x 4 ∨ (oblX0 x 4 = 1 ∧ oblX0 x 5 = 1)) →
    0 ≤ ⟪x 3 - x 2, x 4 - x 0⟫ ∨ (⟪x 4 - x 0, x 5 - x 0⟫ < 0 ∧ ⟪x 6 - x 0, x 4 - x 0⟫ ≤ 0))

/-- **Off both Bs cuts the tie letters hold** (`bsCondSym_of_s1`, `bsCond_of_t1`, `bs1_h20`, `bs1_h60`). -/
theorem bs1Res_of (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (hs0 : 0 < s) (ht0 : 0 < t)
    (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) (hB : ¬ BsCond F t) (hBs : ¬ BsCondSym F s) :
    Bs1Res x s t := by
  constructor
  · intro hs hT ha
    by_contra hc
    push Not at hc
    obtain ⟨h36, hc2⟩ := hc
    have h20 : 0 < ⟪x 2 - x 0, x 5 - x 0⟫ := by
      by_cases hg : 0 ≤ ⟪x 4 - x 0, x 5 - x 0⟫
      · exact bs1_h20 hs ht0 hdec hT h36 hg
      · exact hc2 (lt_of_not_ge hg)
    exact hBs (bsCondSym_of_s1 F hs ht0 hdec h36 h20 ha)
  · intro ht hT ha
    by_contra hc
    push Not at hc
    obtain ⟨h32, hc2⟩ := hc
    have h60 : 0 < ⟪x 6 - x 0, x 4 - x 0⟫ := by
      by_cases hg : 0 ≤ ⟪x 4 - x 0, x 5 - x 0⟫
      · exact bs1_h60 hs0 ht hdec hT h32 hg
      · exact hc2 (lt_of_not_ge hg)
    exact hB (bsCond_of_t1 F hs0 ht hdec h32 h60 ha)

/-- `Q45ResWQT` with the explicit tie letters `Bs1Res` at its decomposition. -/
def Q45ResWR2 (F : S0xFac 9 s0x_S24 x) : Prop :=
  Q45ResWQT F ∧ ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0) ∧ Bs1Res x s t

/-- **`Q45ResWQT ⊆ Q45ResWR2`** (the Bs cuts of `Q45ResSTB` at the residue's own decomposition). -/
theorem q45ResWR2_of_QT {F : S0xFac 9 s0x_S24 x} (h : Q45ResWQT F) : Q45ResWR2 F := by
  refine ⟨h, ?_⟩
  obtain ⟨s, t, hs, ht, -, hd, hP⟩ := h.1.1
  have hB := hP.1.1.1.1.1.1.2
  exact ⟨s, t, hs, ht, hd, bs1Res_of F hs ht hd hB.1 hB.2.1⟩

/-- [OPEN] **The special piece with the `s = 1` / `t = 1` tie letters explicit, Rupert form**: `OpenSpecialQT` with
`Q45ResWR2` in place of `Q45ResWQT` (equivalent to it: `openSpecialR2_iff_QT`). -/
def OpenSpecialR2 : Prop := ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), ¬ H24K.SAT.OB1 x →
  1 ≤ oblX0 x 4 → 1 ≤ oblX0 x 5 →
  oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0 →
  0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3 →
  0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4 →
  0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5 →
  Q45ResWR2 F → HoleFull x F → IsRupert (univ.image x)

/-- [PROVED] `OpenSpecialR2 ↔ OpenSpecialQT` (`q45ResWR2_of_QT`; the other direction is `Q45ResWR2 ⊆ Q45ResWQT`). -/
theorem openSpecialR2_iff_QT : OpenSpecialR2 ↔ OpenSpecialQT :=
  ⟨fun h x F hO h4 h5 b1 b2 b3 b4 hr hF => h x F hO h4 h5 b1 b2 b3 b4 (q45ResWR2_of_QT hr) hF,
    fun h x F hO h4 h5 b1 b2 b3 b4 hr hF => h x F hO h4 h5 b1 b2 b3 b4 hr.1 hF⟩

/-- [PROVED] `OpenSpecialR2 → OpenSpecialQ`, for the chains that take `OpenSpecialQ` (e.g. WALL5's `E10` chain). -/
theorem openSpecialQ_of_R2 (h : OpenSpecialR2) : OpenSpecialQ :=
  openSpecialQT_iff_Q.1 (openSpecialR2_iff_QT.1 h)

/-- [PROVED] `OpenSpecialR2 → OpenSpecialO`, for the cell chains that take `OpenSpecialO`. -/
theorem openSpecialO_of_R2 (h : OpenSpecialR2) : OpenSpecialO :=
  openSpecialO_of_QT (openSpecialR2_iff_QT.1 h)

/-- [PROVED] Generic + special (tie letters explicit) assemble to `Open24Rupert`. -/
theorem open24Rupert_of_split_R2 (h1 : OpenOB1) (h2 : OpenSpecialR2) : Open24Rupert :=
  open24Rupert_of_split_QT h1 (openSpecialR2_iff_QT.1 h2)

end Bs1

end Minimality.T24.OSpec

namespace Minimality.T24.Cell

/-- [PROVED] `CellCoverEmpty L` and `OSpec.OpenSpecialR2` give `Stmt.Open24Rupert` (OSPEC25). -/
theorem open24Rupert_of_cellCoverEmpty_R2 {L : List Cell24} (hN : CellCoverEmpty L) (hS : OSpec.OpenSpecialR2) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmpty_QT hN (OSpec.openSpecialR2_iff_QT.1 hS)

/-- [PROVED] Headline chain with `cells28` after OSPEC25. -/
theorem open24Rupert_of_cellCoverEmpty28_R2 (hN : CellCoverEmpty cells28) (hS : OSpec.OpenSpecialR2) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmpty_R2 hN hS

/-- [PROVED] The `E` cell chain with `OSpec.OpenSpecialR2` (OSPEC25). -/
theorem open24Rupert_of_cellCoverEmptyE28_R2 (hN : CellCoverEmptyE cells28) (hS : OSpec.OpenSpecialR2) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmptyE28_QT hN (OSpec.openSpecialR2_iff_QT.1 hS)

/-- [PROVED] The `EP` cell chain with `OSpec.OpenSpecialR2` (OSPEC25). -/
theorem open24Rupert_of_cellCoverEmptyEP28_R2 (hN : CellCoverEmptyEP cells28) (hS : OSpec.OpenSpecialR2) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmptyEP28_QT hN (OSpec.openSpecialR2_iff_QT.1 hS)

/-- [PROVED] Headline chain after WALL3 and OSPEC25: `CellCoverEmptyE4 cells28` and `OSpec.OpenSpecialR2`. -/
theorem open24Rupert_of_cellCoverEmptyE4_28_R2 (hN : CellCoverEmptyE4 cells28) (hS : OSpec.OpenSpecialR2) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmptyE4_28_QT hN (OSpec.openSpecialR2_iff_QT.1 hS)

end Minimality.T24.Cell
