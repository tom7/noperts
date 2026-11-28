module

public import Minimality.Type24Cells28

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.T24.Stmt Minimality.T24.Q45
  Minimality.T24.Reg Minimality.T24.A19

/-!
# Type 24 off `OB1`: horizontal views on the double wall (job OSPEC20)

nopert229 notes/OPENSPECIAL-STRATEGY.md section 2h.  On the double wall `a4 = a5 = 1` the faces `126` (`a = 0`) and
`0345` (`a = 1`) are parallel, and every direction `m = α e4 + β e5` (`e4 = x 4 - x 0`, `e5 = x 5 - x 0`) is
horizontal.  For `α, β > 0` (and `0 < s, t < 1 < s + t`) every facet sign of the views `(m, N3, N3)` and
`(-m, N3, N3)` is derived: `012 016 025 046` are down at `m` at level 1 (through `0`), `235 236 346` up (`dw_n6`,
`dw_n7`, `dw_n8`: affine relations on the top face), `0345` / `126` are decided at level 2 (`bs_n53_neg`).  The rims
are `2 5 0 4 6` at `m` (`rimHA`; the top chain `5 0 4` is never peaked at `0`, `dw_vA`) and `1 2 5 3 4 6` at `-m`
(`rimKD`, the K0D rim; `3` is never peaked, `dw_vB`, and `1` never a valley, `dw_lamB`).  So each view is a lex cell
as soon as its two junctions rise: `⟪x 6 - x 4, m⟫` and `⟪x 2 - x 5, m⟫` both positive (`lexAny_of_horizA`) or both
negative (`lexAny_of_horizB`).  `DwHorizOK`: some `α, β > 0` does one of the two.  The K0D view (`α = 1, β = 0`)
is the boundary case of `horizB`, the Bs view (`m = -e4`) a boundary case of the same family.

Residue: `Q45ResSTO` (= `Q45ResSTN` minus `DwHorizCut`), `Q45ResWO`, **`OpenSpecialO`** (implied by `OpenSpecialN`);
on the double wall with the frame signs the residue piece is exactly `¬ DwHorizOK` (`not_dwHorizOK_of_resO`).
-/

namespace Minimality.T24.OSpec

variable {x : Fin 7 → ℝ³}

section HorizDW
open Minimality.LexCell

/-- The horizontal direction `α e4 + β e5` of the double wall. -/
noncomputable def dwM (x : Fin 7 → ℝ³) (α β : ℝ) : ℝ³ := α • (x 4 - x 0) + β • (x 5 - x 0)

theorem dwM_inner (F : S0xFac 9 s0x_S24 x) (u : Fin 9) (α β : ℝ) :
    ⟪F.N u, dwM x α β⟫ = α * (F.f u (x 4) - F.f u (x 0)) + β * (F.f u (x 5) - F.f u (x 0)) := by
  rw [dwM, inner_add_right, real_inner_smul_right, real_inner_smul_right, F.inner_sub u 4 0, F.inner_sub u 5 0]

/-- Every facet function is affine on the top face: `f(x 3) - f(x 0) = s (f(x 4) - f(x 0)) + t (f(x 5) - f(x 0))`. -/
theorem dw_aff (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (u : Fin 9) :
    F.f u (x 3) - F.f u (x 0) = s * (F.f u (x 4) - F.f u (x 0)) + t * (F.f u (x 5) - F.f u (x 0)) := by
  have h := congrArg (fun v => ⟪F.N u, v⟫) hdec
  simp only [inner_add_right, real_inner_smul_right] at h
  rwa [F.inner_sub u 3 0, F.inner_sub u 4 0, F.inner_sub u 5 0] at h

/-- A facet through `0` but not `4`, `5` is down at `m` (level 1). -/
theorem dw_n_of_mem0 (F : S0xFac 9 s0x_S24 x) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (u : Fin 9)
    (h0 : (0 : Fin 7) ∈ s0x_S24 u) (h4 : (4 : Fin 7) ∉ s0x_S24 u) (h5 : (5 : Fin 7) ∉ s0x_S24 u) :
    ⟪F.N u, dwM x α β⟫ < 0 := by
  rw [dwM_inner, F.zero u 0 h0]
  nlinarith [F.neg u 4 h4, F.neg u 5 h5]

/-- `025` is down at `m` (level 1). -/
theorem dw_n2 (F : S0xFac 9 s0x_S24 x) {α β : ℝ} (hα : 0 < α) : ⟪F.N 2, dwM x α β⟫ < 0 := by
  rw [dwM_inner, F.zero 2 0 (by decide), F.zero 2 5 (by decide)]
  nlinarith [F.neg 2 4 (by decide)]

/-- `046` is down at `m` (level 1). -/
theorem dw_n4 (F : S0xFac 9 s0x_S24 x) {α β : ℝ} (hβ : 0 < β) : ⟪F.N 4, dwM x α β⟫ < 0 := by
  rw [dwM_inner, F.zero 4 0 (by decide), F.zero 4 4 (by decide)]
  nlinarith [F.neg 4 5 (by decide)]

/-- `0345` is edge-on at `m`. -/
theorem dw_n3 (F : S0xFac 9 s0x_S24 x) (α β : ℝ) : ⟪F.N 3, dwM x α β⟫ = 0 := by
  rw [dwM_inner, F.zero 3 0 (by decide), F.zero 3 4 (by decide), F.zero 3 5 (by decide)]; ring

/-- `126` is edge-on at `m` on the double wall. -/
theorem dw_n5 (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1) (α β : ℝ) :
    ⟪F.N 5, dwM x α β⟫ = 0 := by
  rw [dwM_inner, bs_f5_obl F 4, bs_f5_obl F 5, hw4, hw5]; ring

/-- `235` is up at `m` (level 1; `t < 1`). -/
theorem dw_n6 (F : S0xFac 9 s0x_S24 x) {s t α β : ℝ} (hs0 : 0 < s) (ht1 : t < 1) (hα : 0 < α) (hβ : 0 < β)
    (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) : 0 < ⟪F.N 6, dwM x α β⟫ := by
  have e := dw_aff F hdec 6
  rw [F.zero 6 3 (by decide), F.zero 6 5 (by decide)] at e
  have h0 := F.neg 6 0 (by decide)
  have hA : 0 < F.f 6 (x 4) - F.f 6 (x 0) := by
    by_contra hc; push Not at hc; nlinarith [mul_pos hs0 hα]
  rw [dwM_inner, F.zero 6 5 (by decide)]
  nlinarith [mul_pos hα hA]

/-- `346` is up at `m` (level 1; `s < 1`). -/
theorem dw_n8 (F : S0xFac 9 s0x_S24 x) {s t α β : ℝ} (hs1 : s < 1) (ht0 : 0 < t) (hα : 0 < α) (hβ : 0 < β)
    (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) : 0 < ⟪F.N 8, dwM x α β⟫ := by
  have e := dw_aff F hdec 8
  rw [F.zero 8 3 (by decide), F.zero 8 4 (by decide)] at e
  have h0 := F.neg 8 0 (by decide)
  have hB : 0 < F.f 8 (x 5) - F.f 8 (x 0) := by
    by_contra hc; push Not at hc; nlinarith [mul_pos ht0 hβ]
  rw [dwM_inner, F.zero 8 4 (by decide)]
  nlinarith [mul_pos hβ hB]

/-- `236` is up at `m` (level 1): `(s + t - 1) (f7(x 4) - f7(x 0)) = (t - 1) f7(x 4) - t f7(x 5) > 0` and the mirror
identity for `x 5`. -/
theorem dw_n7 (F : S0xFac 9 s0x_S24 x) {s t α β : ℝ} (hs0 : 0 < s) (ht0 : 0 < t) (hs1 : s < 1) (ht1 : t < 1)
    (hst : 1 < s + t) (hα : 0 < α) (hβ : 0 < β)
    (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) : 0 < ⟪F.N 7, dwM x α β⟫ := by
  have e := dw_aff F hdec 7
  rw [F.zero 7 3 (by decide)] at e
  have h4 := F.neg 7 4 (by decide)
  have h5 := F.neg 7 5 (by decide)
  have iA : (s + t - 1) * (F.f 7 (x 4) - F.f 7 (x 0)) = (t - 1) * F.f 7 (x 4) - t * F.f 7 (x 5) := by
    linear_combination (-1 : ℝ) * e
  have iB : (s + t - 1) * (F.f 7 (x 5) - F.f 7 (x 0)) = (s - 1) * F.f 7 (x 5) - s * F.f 7 (x 4) := by
    linear_combination (-1 : ℝ) * e
  have hA : 0 < F.f 7 (x 4) - F.f 7 (x 0) := by
    by_contra hc; push Not at hc
    nlinarith [mul_pos (sub_pos.2 ht1) (neg_pos.2 h4), mul_pos ht0 (neg_pos.2 h5), mul_nonneg (sub_pos.2 hst).le (neg_nonneg.2 hc)]
  have hB : 0 < F.f 7 (x 5) - F.f 7 (x 0) := by
    by_contra hc; push Not at hc
    nlinarith [mul_pos (sub_pos.2 hs1) (neg_pos.2 h5), mul_pos hs0 (neg_pos.2 h4), mul_nonneg (sub_pos.2 hst).le (neg_nonneg.2 hc)]
  rw [dwM_inner]
  nlinarith [mul_pos hα hA, mul_pos hβ hB]

theorem dwM_ne (F : S0xFac 9 s0x_S24 x) {α β : ℝ} (hα : 0 < α) : dwM x α β ≠ 0 := by
  intro h
  have := dw_n2 F (β := β) hα
  rw [h, inner_zero_right] at this
  exact lt_irrefl _ this

/-- `0` is below `5` or `4` at `m` (level 1): `|m|² = α ⟪e4, m⟫ + β ⟪e5, m⟫ > 0`. -/
theorem dw_vA (F : S0xFac 9 s0x_S24 x) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ⟪x 0, dwM x α β⟫ < ⟪x 5, dwM x α β⟫ ∨ ⟪x 0, dwM x α β⟫ < ⟪x 4, dwM x α β⟫ := by
  have hE : 0 < ⟪dwM x α β, dwM x α β⟫ := real_inner_self_pos.mpr (dwM_ne F hα)
  have hsum : ⟪dwM x α β, dwM x α β⟫ = α * ⟪x 4 - x 0, dwM x α β⟫ + β * ⟪x 5 - x 0, dwM x α β⟫ := by
    conv_lhs => rw [dwM]
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    rfl
  rw [inner_sub_left, inner_sub_left] at hsum
  by_contra hc
  push Not at hc
  nlinarith [mul_le_mul_of_nonneg_left (sub_nonpos.2 hc.1) hβ.le, mul_le_mul_of_nonneg_left (sub_nonpos.2 hc.2) hα.le]

/-- `3` is below `5` or `4` at `-m` (level 1), for `0 < s, t < 1 < s + t`. -/
theorem dw_vB (F : S0xFac 9 s0x_S24 x) {s t α β : ℝ} (hs0 : 0 < s) (ht0 : 0 < t) (hs1 : s < 1) (ht1 : t < 1)
    (hst : 1 < s + t) (hα : 0 < α) (hβ : 0 < β)
    (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) :
    ⟪x 3, -dwM x α β⟫ < ⟪x 5, -dwM x α β⟫ ∨ ⟪x 3, -dwM x α β⟫ < ⟪x 4, -dwM x α β⟫ := by
  set m := dwM x α β with hm
  have hE : 0 < ⟪m, m⟫ := real_inner_self_pos.mpr (dwM_ne F hα)
  set p := ⟪x 4 - x 0, m⟫
  set q := ⟪x 5 - x 0, m⟫
  have hmdef : m = α • (x 4 - x 0) + β • (x 5 - x 0) := by rw [hm, dwM]
  have hsum : ⟪m, m⟫ = α * p + β * q := by
    calc ⟪m, m⟫ = ⟪α • (x 4 - x 0) + β • (x 5 - x 0), m⟫ := by rw [← hmdef]
      _ = α * p + β * q := by rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have g3 : ⟪x 3 - x 0, m⟫ = s * p + t * q := by
    rw [hdec, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have g5 : ⟪x 5, -m⟫ - ⟪x 3, -m⟫ = s * p - (1 - t) * q := by
    rw [inner_neg_right, inner_neg_right, ← sub_eq_zero]
    have : ⟪x 5 - x 0, m⟫ - ⟪x 3 - x 0, m⟫ = q - (s * p + t * q) := by rw [g3]
    rw [inner_sub_left, inner_sub_left] at this
    linarith
  have g4 : ⟪x 4, -m⟫ - ⟪x 3, -m⟫ = t * q - (1 - s) * p := by
    rw [inner_neg_right, inner_neg_right, ← sub_eq_zero]
    have : ⟪x 4 - x 0, m⟫ - ⟪x 3 - x 0, m⟫ = p - (s * p + t * q) := by rw [g3]
    rw [inner_sub_left, inner_sub_left] at this
    linarith
  by_contra hc
  push Not at hc
  have a5 : s * p - (1 - t) * q ≤ 0 := by linarith [hc.1]
  have a4 : t * q - (1 - s) * p ≤ 0 := by linarith [hc.2]
  rcases le_or_gt p 0 with hp | hp
  · have hq : q ≤ 0 := by nlinarith
    nlinarith
  · have hq : 0 < q := by nlinarith
    nlinarith [mul_pos hp hq, mul_pos hs0 hp, mul_pos ht0 hq]

/-- `1` is above `6` or `2` at `-m` (level 1): `m = B (x 2 - x 1) + C (x 6 - x 1)` with `B, C > 0` on the double
wall, so `|m|² = B ⟪x 2 - x 1, m⟫ + C ⟪x 6 - x 1, m⟫ > 0`. -/
theorem dw_lamB (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) :
    ⟪x 6, -dwM x α β⟫ < ⟪x 1, -dwM x α β⟫ ∨ ⟪x 2, -dwM x α β⟫ < ⟪x 1, -dwM x α β⟫ := by
  have T := M4.type24OfFac F
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (by decide)
  have hc4 : 0 < oblX6 x 4 := T.X6_pos (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (by decide)
  have r4 := T.rep 4
  have r5 := T.rep 5
  rw [hw4] at r4
  rw [hw5] at r5
  set m := dwM x α β with hm
  have e : m = (α * oblX2 x 4 + β * oblX2 x 5) • (x 2 - x 1) + (α * oblX6 x 4 + β * oblX6 x 5) • (x 6 - x 1) := by
    rw [hm, dwM, r4, r5]; module
  have hE : 0 < ⟪m, m⟫ := real_inner_self_pos.mpr (dwM_ne F hα)
  have hsum : ⟪m, m⟫ = (α * oblX2 x 4 + β * oblX2 x 5) * ⟪x 2 - x 1, m⟫ +
      (α * oblX6 x 4 + β * oblX6 x 5) * ⟪x 6 - x 1, m⟫ := by
    conv_lhs => rw [e]
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    conv_lhs => rw [← e]
  have hB : 0 < α * oblX2 x 4 + β * oblX2 x 5 := by positivity
  have hC : 0 < α * oblX6 x 4 + β * oblX6 x 5 := by positivity
  rw [inner_sub_left, inner_sub_left] at hsum
  by_contra hc
  push Not at hc
  simp only [inner_neg_right] at hc
  nlinarith [mul_le_mul_of_nonneg_left (show ⟪x 6, m⟫ - ⟪x 1, m⟫ ≤ 0 by linarith [hc.1]) hC.le,
    mul_le_mul_of_nonneg_left (show ⟪x 2, m⟫ - ⟪x 1, m⟫ ≤ 0 by linarith [hc.2]) hB.le]

/-- **A 5-cycle with `z1 < z0`, `z3 < z4` and `z2` below a neighbour (level 1) is `RobUniLex`** (`z4`, `z0` the
only candidate peaks, adjacent). -/
theorem robUniLex_five_dwA (z : ZMod 5 → ℝ × ℝ × ℝ) (h10 : (z 1).1 < (z 0).1) (h34 : (z 3).1 < (z 4).1)
    (hV : (z 2).1 < (z 1).1 ∨ (z 2).1 < (z 3).1) : RobUniLex z := by
  have L : ∀ i j : ZMod 5, (z i).1 < (z j).1 → LexLt3 (z i) (z j) := fun i j h => Or.inl (by linarith)
  have l10 := L 1 0 h10
  have l34 := L 3 4 h34
  rcases hV with h | h
  · have l21 := L 2 1 h
    have l20 := L 2 0 (by linarith)
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
  · have l23 := L 2 3 h
    have l24 := L 2 4 (by linarith)
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

/-- Rim `2 5 0 4 6` of the horizontal view `(m, N3, N3)` (facets `0345 235 236 346` up, `012 016 025 046 126`
down). -/
def rimHA : ZMod 5 → Fin 7 := ![2, 5, 0, 4, 6]
def UHA : Finset (Fin 9) := {3, 6, 7, 8}
def DnHA : Finset (Fin 9) := {0, 1, 2, 4, 5}

theorem rimHA_cyc : S0xCycUD s0x_S24 rimHA UHA DnHA := by decide
theorem rimHA_inj : Function.Injective rimHA := by decide

/-- **Horizontal view A on the double wall**: for `α, β > 0` with both junctions rising
(`⟪x 6 - x 4, m⟫ > 0`, `⟪x 2 - x 5, m⟫ > 0`, `m = α e4 + β e5`) the view `(m, N3, N3)` is a lex cell, rim
`2 5 0 4 6`. -/
theorem lexAny_of_horizA (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1) {s t α β : ℝ}
    (hs0 : 0 < s) (ht0 : 0 < t) (hs1 : s < 1) (ht1 : t < 1) (hst : 1 < s + t)
    (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) (hα : 0 < α) (hβ : 0 < β)
    (j6 : 0 < ⟪x 6 - x 4, dwM x α β⟫) (j2 : 0 < ⟪x 2 - x 5, dwM x α β⟫) : Gen.LexAny F := by
  have hN3 : 0 < ⟪F.N 3, F.N 3⟫ := real_inner_self_pos.mpr (n3_ne_zero F)
  have h53 := bs_n53_neg F hw4 hw5
  refine ⟨5, inferInstance, rimHA, UHA, DnHA, dwM x α β, F.N 3, F.N 3, by norm_num, rimHA_inj, rimHA_cyc,
    ?_, ?_, ?_⟩
  · intro u hu
    simp only [UHA, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact Or.inr ⟨dw_n3 F α β, Or.inl hN3⟩
    · exact Or.inl (dw_n6 F hs0 ht1 hα hβ hdec)
    · exact Or.inl (dw_n7 F hs0 ht0 hs1 ht1 hst hα hβ hdec)
    · exact Or.inl (dw_n8 F hs1 ht0 hα hβ hdec)
  · intro u hu
    simp only [DnHA, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (neg_pos.2 (dw_n_of_mem0 F hα hβ 0 (by decide) (by decide) (by decide)))
    · exact Or.inl (neg_pos.2 (dw_n_of_mem0 F hα hβ 1 (by decide) (by decide) (by decide)))
    · exact Or.inl (neg_pos.2 (dw_n2 F hα))
    · exact Or.inl (neg_pos.2 (dw_n4 F hβ))
    · exact Or.inr ⟨by rw [dw_n5 F hw4 hw5]; ring, Or.inl (by linarith)⟩
  · rw [inner_sub_left] at j6 j2
    apply robUniLex_five_dwA
    · show ⟪x 5, dwM x α β⟫ < ⟪x 2, dwM x α β⟫; linarith
    · show ⟪x 4, dwM x α β⟫ < ⟪x 6, dwM x α β⟫; linarith
    · rcases dw_vA F hα hβ with h | h
      · exact Or.inl h
      · exact Or.inr h

/-- **Horizontal view B on the double wall**: for `α, β > 0` with both junctions falling at `m`
(`⟪x 6 - x 4, m⟫ < 0`, `⟪x 2 - x 5, m⟫ < 0`) the view `(-m, N3, N3)` is a lex cell, rim `1 2 5 3 4 6`
(the K0D rim; the K0D view is the boundary case `m = e4`). -/
theorem lexAny_of_horizB (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1) {s t α β : ℝ}
    (hs0 : 0 < s) (ht0 : 0 < t) (hs1 : s < 1) (ht1 : t < 1) (hst : 1 < s + t)
    (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) (hα : 0 < α) (hβ : 0 < β)
    (j6 : ⟪x 6 - x 4, dwM x α β⟫ < 0) (j2 : ⟪x 2 - x 5, dwM x α β⟫ < 0) : Gen.LexAny F := by
  have hN3 : 0 < ⟪F.N 3, F.N 3⟫ := real_inner_self_pos.mpr (n3_ne_zero F)
  have h53 := bs_n53_neg F hw4 hw5
  refine ⟨6, inferInstance, rimKD, UKD, DnKD, -dwM x α β, F.N 3, F.N 3, by norm_num, rimKD_inj, rimKD_cyc,
    ?_, ?_, ?_⟩
  · intro u hu
    simp only [UKD, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (by rw [inner_neg_right]; exact neg_pos.2 (dw_n_of_mem0 F hα hβ 0 (by decide) (by decide) (by decide)))
    · exact Or.inl (by rw [inner_neg_right]; exact neg_pos.2 (dw_n_of_mem0 F hα hβ 1 (by decide) (by decide) (by decide)))
    · exact Or.inl (by rw [inner_neg_right]; exact neg_pos.2 (dw_n2 F hα))
    · exact Or.inr ⟨by rw [inner_neg_right, dw_n3 F α β]; ring, Or.inl hN3⟩
    · exact Or.inl (by rw [inner_neg_right]; exact neg_pos.2 (dw_n4 F hβ))
  · intro u hu
    simp only [DnKD, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact Or.inr ⟨by rw [inner_neg_right, dw_n5 F hw4 hw5]; ring, Or.inl (by linarith)⟩
    · exact Or.inl (by rw [inner_neg_right, neg_neg]; exact dw_n6 F hs0 ht1 hα hβ hdec)
    · exact Or.inl (by rw [inner_neg_right, neg_neg]; exact dw_n7 F hs0 ht0 hs1 ht1 hst hα hβ hdec)
    · exact Or.inl (by rw [inner_neg_right, neg_neg]; exact dw_n8 F hs1 ht0 hα hβ hdec)
  · have hV := dw_vB F hs0 ht0 hs1 ht1 hst hα hβ hdec
    have hL := dw_lamB F hw4 hw5 hα hβ
    rw [inner_sub_left] at j6 j2
    have L : ∀ p q : ℝ × ℝ × ℝ, p.1 < q.1 → LexLt3 p q := fun p q h => Or.inl (by linarith)
    apply robUniLex_six_dw
    · rcases hV with h | h
      · exact Or.inl (L _ _ h)
      · exact Or.inr (L _ _ h)
    · rcases hL with h | h
      · exact Or.inl (L _ _ h)
      · exact Or.inr (L _ _ h)
    · refine Or.inl (L _ _ ?_)
      show ⟪x 4, -dwM x α β⟫ < ⟪x 6, -dwM x α β⟫
      rw [inner_neg_right, inner_neg_right]; linarith
    · refine Or.inl (L _ _ ?_)
      show ⟪x 5, -dwM x α β⟫ < ⟪x 2, -dwM x α β⟫
      rw [inner_neg_right, inner_neg_right]; linarith

/-- **The horizontal double-wall condition**: some `m = α e4 + β e5` (`α, β > 0`) has both junction products
`⟪x 6 - x 4, m⟫`, `⟪x 2 - x 5, m⟫` of the same strict sign. -/
def DwHorizOK (x : Fin 7 → ℝ³) : Prop :=
  ∃ α β : ℝ, 0 < α ∧ 0 < β ∧
    ((0 < ⟪x 6 - x 4, dwM x α β⟫ ∧ 0 < ⟪x 2 - x 5, dwM x α β⟫) ∨
      (⟪x 6 - x 4, dwM x α β⟫ < 0 ∧ ⟪x 2 - x 5, dwM x α β⟫ < 0))

/-- **`DwHorizOK` gives a lex cell on the double wall** (`0 < s, t < 1 < s + t`). -/
theorem lexAny_of_dwHoriz (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1) {s t : ℝ}
    (hs0 : 0 < s) (ht0 : 0 < t) (hs1 : s < 1) (ht1 : t < 1) (hst : 1 < s + t)
    (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) (h : DwHorizOK x) : Gen.LexAny F := by
  obtain ⟨α, β, hα, hβ, ⟨j6, j2⟩ | ⟨j6, j2⟩⟩ := h
  · exact lexAny_of_horizA F hw4 hw5 hs0 ht0 hs1 ht1 hst hdec hα hβ j6 j2
  · exact lexAny_of_horizB F hw4 hw5 hs0 ht0 hs1 ht1 hst hdec hα hβ j6 j2

/-! ### The residue after the horizontal double-wall views -/

/-- The horizontal double-wall cut at `(s, t)`. -/
def DwHorizCut (x : Fin 7 → ℝ³) (s t : ℝ) : Prop :=
  oblX0 x 4 = 1 ∧ oblX0 x 5 = 1 ∧ s < 1 ∧ t < 1 ∧ DwHorizOK x

/-- `Q45ResSTN` where no horizontal double-wall view applies. -/
def Q45ResSTO (F : S0xFac 9 s0x_S24 x) (s t : ℝ) : Prop :=
  Q45ResSTN F s t ∧ ¬ DwHorizCut x s t

/-- The branch-tagged residue after OSPEC20. -/
def Q45ResWO (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ 1 < s + t ∧ x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0) ∧ Q45ResSTO F s t

theorem q45_resO_local (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (hs0 : 0 < s) (ht0 : 0 < t) (hst : 1 < s + t)
    (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) (h : Q45ResSTN F s t) :
    Gen.LexAny F ∨ Q45ResSTO F s t := by
  by_cases hA : DwHorizCut x s t
  · obtain ⟨h4, h5, hs1, ht1, hH⟩ := hA
    exact Or.inl (lexAny_of_dwHoriz F h4 h5 hs0 ht0 hs1 ht1 hst hdec hH)
  exact Or.inr ⟨h, hA⟩

/-- `Q45ResWO ⊆ Q45ResWN`. -/
theorem q45ResWN_of_O {F : S0xFac 9 s0x_S24 x} (h : Q45ResWO F) : Q45ResWN F := by
  obtain ⟨s, t, hs, ht, hst, hd, h, -⟩ := h
  exact ⟨s, t, hs, ht, hst, hd, h⟩

/-- On the double wall with the frame signs `b1`, `b2` a point of `Q45ResWO` fails `DwHorizOK` (the cut is exactly
`DwHorizOK` there: `s, t < 1` are automatic, `dw_s_lt_one`, `dw_t_lt_one`). -/
theorem not_dwHorizOK_of_resO {F : S0xFac 9 s0x_S24 x} (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1)
    (b1 : oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0)
    (b2 : 0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3) (h : Q45ResWO F) : ¬ DwHorizOK x := by
  obtain ⟨s, t, hs, ht, -, hd, -, hc⟩ := h
  exact fun hH => hc ⟨hw4, hw5, dw_s_lt_one F ht hd hw4 hw5 b1, dw_t_lt_one F hs hd hw4 hw5 b2, hH⟩

/-- **Global form**: on the corner every point has `LexAny`, `AnyFaceChord`, is Rupert, or lies in `Q45ResWO`. -/
theorem q45_resO (F : S0xFac 9 s0x_S24 x) (h4 : 1 ≤ oblX0 x 4) (h5 : 1 ≤ oblX0 x 5) :
    Gen.LexAny F ∨ Gen.AnyFaceChord F ∨ IsRupert (univ.image x) ∨ Q45ResWO F := by
  rcases q45_resN F h4 h5 with h | h | h | ⟨s, t, hs0, ht, hst, hd, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · rcases q45_resO_local F hs0 ht hst hd h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr ⟨s, t, hs0, ht, hst, hd, h⟩))

/-- [OPEN] **The special piece after the horizontal double-wall views, Rupert form**: `OpenSpecialN` with
`Q45ResWO` in place of `Q45ResWN` (implied by it: `openSpecialO_of_openSpecialN`). -/
def OpenSpecialO : Prop := ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), ¬ H24K.SAT.OB1 x →
  1 ≤ oblX0 x 4 → 1 ≤ oblX0 x 5 →
  oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0 →
  0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3 →
  0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4 →
  0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5 →
  Q45ResWO F → HoleFull x F → IsRupert (univ.image x)

/-- [PROVED] `OpenSpecialN → OpenSpecialO` (`Q45ResWO ⊆ Q45ResWN`). -/
theorem openSpecialO_of_openSpecialN (h : OpenSpecialN) : OpenSpecialO :=
  fun x F hO h4 h5 b1 b2 b3 b4 hr hF => h x F hO h4 h5 b1 b2 b3 b4 (q45ResWN_of_O hr) hF

/-- Every `Hole24` point off `OB1` is Rupert, given `OpenSpecialO`. -/
theorem hole24_offOB1_O {F : S0xFac 9 s0x_S24 x} (h : Hole24 x F) (hO : ¬ H24K.SAT.OB1 x)
    (hS : OpenSpecialO) : IsRupert (univ.image x) := by
  obtain ⟨b1, b2, b3⟩ := resid24_frame_signs h.2.2.1 hO
  have b4 := resid24_b1245 h.2.2.1 hO
  obtain ⟨-, h4, h5⟩ := offWall_of_hole24 h hO
  have hF := holeFull_of_hole24 h
  rcases q45_resO F h4 h5 with hL | hA | hR | hr
  · exact (hF.1.2.2.2.1 hL).elim
  · exact (hF.1.2.2.1 hA).elim
  · exact hR
  · exact hS x F hO h4 h5 b1 b2 b3 b4 hr hF

/-- [PROVED] Generic + special (after the horizontal double-wall views) assemble to `Open24Rupert`. -/
theorem open24Rupert_of_split_O (h1 : OpenOB1) (h2 : OpenSpecialO) : Open24Rupert := by
  intro x fs hh hH
  by_cases hO : H24K.SAT.OB1 x
  · exact (h1 x _ hO (holeFull_of_hole24 hH)).elim
  · exact hole24_offOB1_O hH hO h2

end HorizDW

end Minimality.T24.OSpec

namespace Minimality.T24.Cell

/-- Every `Hole24` point is Rupert, given `CellCoverEmpty L` and `OSpec.OpenSpecialO` (OSPEC20, the horizontal
double-wall views). -/
theorem rupert_of_cellCoverEmpty_O {L : List Cell24} (hN : CellCoverEmpty L) (hS : OSpec.OpenSpecialO) :
    ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), Hole24 x F → IsRupert (univ.image x) := by
  intro x F hH
  by_cases hO : H24K.SAT.OB1 x
  · exact (hN x F hH.1.1 hO (hole24_cellCoverResidue L hH)).elim
  · exact OSpec.hole24_offOB1_O hH hO hS

/-- [PROVED] `CellCoverEmpty L` and `OSpec.OpenSpecialO` give `Stmt.Open24Rupert`. -/
theorem open24Rupert_of_cellCoverEmpty_O {L : List Cell24} (hN : CellCoverEmpty L) (hS : OSpec.OpenSpecialO) :
    Open24Rupert :=
  OSpec.open24Rupert_of_split_O (openOB1_of_cellCoverEmpty hN) hS

/-- [PROVED] Headline chain with `cells28` after OSPEC20: `CellCoverEmpty cells28` and `OSpec.OpenSpecialO` give
`Open24Rupert`. -/
theorem open24Rupert_of_cellCoverEmpty28_O (hN : CellCoverEmpty cells28) (hS : OSpec.OpenSpecialO) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmpty_O hN hS

end Minimality.T24.Cell
