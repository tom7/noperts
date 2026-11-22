module

public import Minimality.M4eType24
public import Minimality.M4dType24
public import Minimality.M4cType24
public import Minimality.M4bType24
public import Minimality.M4Sym24
public import Minimality.GenQuad

@[expose] public section

/-!
# Type 24: A15 lemmas (nopert229 out/bottleneck/p4/sat/A15-REFEREE.md, section 5)

`u37_eq` (Identity E-37, both forms), `u37_e37b` (E-37B, Lemma M form), `u37_bound` (Theorem U37 as a U-bound:
not LexAny forces `0 <= z0` at `u37`, under C-bar, `a4 <= 1 < a5`, `c3 < 1` and the two OB1 signs `gac, gbc <= 0`),
`u37_tie` (via A12 `tie1_bound`), `lexAny_or_split_E3426_full` (E34-26 with the weaker depth condition).
V53-Q4 (`u53` is defined) is not done: its front-pair coefficient Gamma > 0 is open.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

open scoped RealInnerProductSpace
open Finset Filter

namespace Minimality.T24.A15

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell
  Minimality.LexCell Minimality.Split Minimality.T24.M4 Minimality.T24.A7 Minimality.T24.A8
  Minimality.T24.Sym

/-- Depth of vertex `v` in direction `u`, in the frame at vertex 1. -/
noncomputable def z (x : Fin 7 → ℝ³) (u : ℝ³) (v : Fin 7) : ℝ := ⟪x v - x 1, u⟫

noncomputable def Lam4' (x : Fin 7 → ℝ³) : ℝ :=
  omega3 x * (1 - oblX0 x 4) + oblX2 x 4 + oblX6 x 4

noncomputable def u37 (x : Fin 7 → ℝ³) : ℝ³ :=
  (nC x - nB x) • (x 0 - x 1) + (D45 x + omega3 x * nC x) • (x 2 - x 1) -
    (D45 x + omega3 x * nB x) • (x 6 - x 1)

noncomputable def u53 (x : Fin 7 → ℝ³) : ℝ³ := nC x • (x 2 - x 1) - nB x • (x 6 - x 1)

private theorem fac3_lin {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    (-F.f 3 (x 1)) * nC x = (F.f 3 (x 6) - F.f 3 (x 1)) * D45 x ∧
    (-F.f 3 (x 1)) * nB x = (F.f 3 (x 2) - F.f 3 (x 1)) * D45 x := by
  have f3_0 : F.f 3 (x 0) = 0 := F.zero 3 0 (by decide)
  have f3_4 : F.f 3 (x 4) = 0 := F.zero 3 4 (by decide)
  have f3_5 : F.f 3 (x 5) = 0 := F.zero 3 5 (by decide)
  have ev4 := fac_eval F 3 4
  have ev5 := fac_eval F 3 5
  rw [f3_4, f3_0] at ev4
  rw [f3_5, f3_0] at ev5
  dsimp [nC, nB, D45]
  constructor
  · linear_combination oblX2 x 5 * ev4 - oblX2 x 4 * ev5
  · linear_combination oblX6 x 4 * ev5 - oblX6 x 5 * ev4

/-- `a3`-relation from `f_{0345}(x 3) = 0`: `D45 (a3 - 1) + b3 nB + c3 nC = 0`. -/
theorem a3_rel {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    D45 x * (oblX0 x 3 - 1) + oblX2 x 3 * nB x + oblX6 x 3 * nC x = 0 := by
  have T := type24OfFac F
  have h1 : F.f 3 (x 1) < 0 := F.neg 3 1 (by decide)
  have f30 : F.f 3 (x 0) = 0 := F.zero 3 0 (by decide)
  have ev3 := fac_eval F 3 3
  rw [F.zero 3 3 (by decide), f30] at ev3
  obtain ⟨L1, L2⟩ := fac3_lin F
  have hX : (-F.f 3 (x 1)) * (D45 x * (oblX0 x 3 - 1) + oblX2 x 3 * nB x + oblX6 x 3 * nC x) = 0 := by
    linear_combination oblX2 x 3 * L2 + oblX6 x 3 * L1 + D45 x * (-1) * ev3
  exact (mul_eq_zero.mp hX).resolve_left (by linarith)

/-- The two forms of `D45 + omega3 nB`. -/
theorem a3_id {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    oblX0 x 3 * (D45 x + omega3 x * nB x) =
      (D45 x - nC x) * oblX6 x 3 + (D45 x - nB x) * (1 - oblX6 x 3) := by
  have T := type24OfFac F
  have ha3 : oblX0 x 3 ≠ 0 := (T.X0_pos (v := 3) (by decide)).ne'
  have e3 := eq3 F
  have hr := a3_rel F
  have hom : oblX0 x 3 * omega3 x = oblX2 x 3 + oblX6 x 3 - 1 := by
    simp only [omega3]; field_simp
  calc oblX0 x 3 * (D45 x + omega3 x * nB x)
      = oblX0 x 3 * D45 x + (oblX0 x 3 * omega3 x) * nB x := by ring
    _ = _ := by rw [hom]; linear_combination hr

private theorem hrep0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (v : Fin 7) :
    x v - x 0 = (oblX0 x v - 1) • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1) := by
  have T := type24OfFac F
  calc x v - x 0 = (x v - x 1) - (x 0 - x 1) := by abel
    _ = (oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1)) -
        (x 0 - x 1) := by rw [T.rep v]; abel
    _ = _ := by module

private theorem hrep1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (v : Fin 7) :
    x v - x 1 = oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1) := by
  have T := type24OfFac F
  rw [T.rep v]; abel

theorem u37_eq1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    u37 x = Lam4' x • (x 5 - x 0) - Lam5 x • (x 4 - x 0) := by
  rw [hrep0 F 5, hrep0 F 4]
  dsimp [u37, Lam4', Lam5, D45, nB, nC]
  module

theorem u37_eq2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    oblX0 x 3 • u37 x = (D45 x - nC x) • (x 2 - x 3) - (D45 x - nB x) • (x 6 - x 3) := by
  have e3 := eq3 F
  have hr := a3_rel F
  have hom : oblX0 x 3 * omega3 x = oblX2 x 3 + oblX6 x 3 - 1 := by
    have T := type24OfFac F
    have ha3 : oblX0 x 3 ≠ 0 := (T.X0_pos (v := 3) (by decide)).ne'
    simp only [omega3]; field_simp
  have h2 : x 2 - x 3 = (x 2 - x 1) - (x 3 - x 1) := by abel
  have h6 : x 6 - x 3 = (x 6 - x 1) - (x 3 - x 1) := by abel
  rw [h2, h6, hrep1 F 3]
  dsimp only [u37]
  match_scalars
  · ring
  · linear_combination (-1 : ℝ) * hr - (nC x) * hom + a3_id F
  · linear_combination hr + (nC x) * hom
  · linear_combination (-1 : ℝ) * a3_id F

theorem u37_eq {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    u37 x = Lam4' x • (x 5 - x 0) - Lam5 x • (x 4 - x 0) ∧
    oblX0 x 3 • u37 x = (D45 x - nC x) • (x 2 - x 3) - (D45 x - nB x) • (x 6 - x 3) :=
  ⟨u37_eq1 F, u37_eq2 F⟩

/-- `1 + omega3 - Lam4' = 1 + omega3 a4 - b4 - c4 > 0` (`= -f_{236}(x4)` up to the scale). -/
theorem lam4p_lt {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    Lam4' x < 1 + omega3 x := by
  have T := type24OfFac F
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
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
  have hpos : 0 < 1 - oblX2 x 4 - oblX6 x 4 + omega3 x * oblX0 x 4 := by nlinarith
  dsimp [Lam4']; nlinarith

theorem lam4p_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (ha4 : oblX0 x 4 ≤ 1) : 0 < Lam4' x := by
  have T := type24OfFac F
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hc4 : 0 < oblX6 x 4 := T.X6_pos (v := 4) (by decide)
  have := mul_nonneg hC.1.le (sub_nonneg.mpr ha4)
  dsimp [Lam4']; linarith

theorem u37_e37b {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (ha4 : oblX0 x 4 ≤ 1) :
    ∃ t : ℝ, 0 < t ∧
      Lam4' x • (x 3 - x 0) - t • u37 x = (1 + omega3 x) • (x 4 - x 0) ∧
      0 < Lam4' x ∧ Lam4' x < 1 + omega3 x := by
  obtain ⟨s, t, hs, ht, hdec, ha, hb, hc⟩ := lemmaM_coords F
  have e3 := eq3 F
  have hkey : 1 + omega3 x = s * Lam4' x + t * Lam5 x := by
    dsimp [Lam4', Lam5]
    linear_combination (-1 : ℝ) * e3 - omega3 x * ha + hb + hc
  refine ⟨t, ht, ?_, lam4p_pos F hC ha4, lam4p_lt F⟩
  rw [hdec, u37_eq1 F, hkey]
  module

/-! ### Facings at `u37` -/

theorem u37_inner {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) :
    ⟪F.N t, u37 x⟫ = (nC x - nB x) * (F.f t (x 0) - F.f t (x 1)) +
      (D45 x + omega3 x * nC x) * (F.f t (x 2) - F.f t (x 1)) -
      (D45 x + omega3 x * nB x) * (F.f t (x 6) - F.f t (x 1)) := by
  dsimp only [u37]
  rw [inner_sub_right, inner_add_right, inner_smul_right, inner_smul_right, inner_smul_right,
    ← F.hN t (x 0) (x 1), ← F.hN t (x 2) (x 1), ← F.hN t (x 6) (x 1)]

theorem u37_inner1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) :
    ⟪F.N t, u37 x⟫ = Lam4' x * (F.f t (x 5) - F.f t (x 0)) - Lam5 x * (F.f t (x 4) - F.f t (x 0)) := by
  rw [u37_eq1 F, inner_sub_right, inner_smul_right, inner_smul_right,
    ← F.hN t (x 5) (x 0), ← F.hN t (x 4) (x 0)]

theorem u37_inner2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) :
    oblX0 x 3 * ⟪F.N t, u37 x⟫ = (D45 x - nC x) * (F.f t (x 2) - F.f t (x 3)) -
      (D45 x - nB x) * (F.f t (x 6) - F.f t (x 3)) := by
  have h := congrArg (fun w => ⟪F.N t, w⟫) (u37_eq2 F)
  rw [inner_smul_right, inner_sub_right, inner_smul_right, inner_smul_right,
    ← F.hN t (x 2) (x 3), ← F.hN t (x 6) (x 3)] at h
  exact h

/-- Sign data of the frame quantities for `u37`. -/
theorem u37_signs {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha4 : oblX0 x 4 ≤ 1) (ha5 : 1 < oblX0 x 5) (hc3 : oblX6 x 3 < 1) :
    nB x < 0 ∧ 0 < nC x ∧ nC x < D45 x ∧ 0 < D45 x + omega3 x * nB x := by
  have T := type24OfFac F
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hc4 : 0 < oblX6 x 4 := T.X6_pos (v := 4) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hc3p : 0 < oblX6 x 3 := T.X6_pos (v := 3) (by decide)
  have hD : 0 < D45 x := d45_pos F
  have hnB : nB x < 0 := by
    dsimp [nB]; nlinarith
  have hnC : 0 < nC x := by
    dsimp [nC]; nlinarith
  have hnCD : nC x < D45 x := by
    have h1 : F.f 3 (x 1) < 0 := F.neg 3 1 (by decide)
    have h6 : F.f 3 (x 6) < 0 := F.neg 3 6 (by decide)
    have hl := (fac3_lin F).1
    have : (-F.f 3 (x 1)) * (D45 x - nC x) = (-F.f 3 (x 6)) * D45 x := by linear_combination -hl
    have hp : 0 < (-F.f 3 (x 6)) * D45 x := mul_pos (by linarith) hD
    have : 0 < (-F.f 3 (x 1)) * (D45 x - nC x) := by linarith
    by_contra hcon
    push Not at hcon
    nlinarith
  refine ⟨hnB, hnC, hnCD, ?_⟩
  have hid := a3_id F
  have hpos : 0 < (D45 x - nC x) * oblX6 x 3 + (D45 x - nB x) * (1 - oblX6 x 3) := by
    have := mul_pos (sub_pos.mpr hnCD) hc3p
    have := mul_pos (by linarith : 0 < D45 x - nB x) (sub_pos.mpr hc3)
    linarith
  rw [← hid] at hpos
  exact pos_of_mul_pos_right hpos ha3.le

/-! ### The 5-cycle lemma -/

theorem robUniLex_five_u37 (z : ZMod 5 → ℝ × ℝ × ℝ)
    (h01 : (z 0).1 < (z 1).1) (h12 : (z 1).1 < (z 2).1)
    (h4 : (z 4).1 < max (z 0).1 (z 3).1) :
    RobUniLex z := by
  intro B b c d hb hbc hcd hd
  have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by revert B; decide
  have hbcd : (b = 1 ∧ c = 2 ∧ d = 3) ∨ (b = 1 ∧ c = 2 ∧ d = 4) ∨
      (b = 1 ∧ c = 3 ∧ d = 4) ∨ (b = 2 ∧ c = 3 ∧ d = 4) := by omega
  rcases lt_max_iff.mp h4 with h40 | h43
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
    | exact Or.inl (Or.inl (by linarith))
    | exact Or.inr (Or.inl (Or.inl (by linarith)))
    | exact Or.inr (Or.inr (Or.inl (Or.inl (by linarith))))
    | exact Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))

theorem key_gen (ea eb ec : ℝ³) (ua ub uc : ℝ) :
    ua * ⟪ea, ua • ea + ub • eb - uc • ec⟫ + ub * ⟪eb, ua • ea + ub • eb - uc • ec⟫ =
      ⟪ua • ea + ub • eb, ua • ea + ub • eb⟫ - uc * (ua * ⟪ea, ec⟫ + ub * ⟪eb, ec⟫) := by
  simp only [inner_add_left, inner_add_right, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [real_inner_comm ea eb]
  ring

/-! ### Theorem U37 -/

theorem u37_bound {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (hac : ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0) (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0)
    (ha4 : oblX0 x 4 ≤ 1) (ha5 : 1 < oblX0 x 5) (hc3 : oblX6 x 3 < 1)
    (hU : ¬ Gen.LexAny F) : 0 ≤ z x (u37 x) 0 := by
  by_contra hcon
  push Not at hcon
  have T := type24OfFac F
  have hom3 : 0 < omega3 x := hC.1
  have hom5 : 0 < omega5 x := hC.2.2.1
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  obtain ⟨hnB, hnC, hnCD, hDn⟩ := u37_signs F ha4 ha5 hc3
  have hD : 0 < D45 x := d45_pos F
  obtain ⟨t, ht, he, hL0, hL1⟩ := u37_e37b F hC ha4
  have hub : 0 < D45 x + omega3 x * nC x := by nlinarith
  have hua : 0 < nC x - nB x := by linarith
  have hDnB : 0 < D45 x - nB x := by linarith
  have hDnC : 0 < D45 x - nC x := by linarith
  -- facings
  have hf0 : 0 < ⟪F.N 0, u37 x⟫ := by
    rw [u37_inner F 0, F.zero 0 0 (by decide), F.zero 0 1 (by decide), F.zero 0 2 (by decide)]
    have h6 := F.neg 0 6 (by decide)
    nlinarith [mul_pos hDn (neg_pos.mpr h6)]
  have hf1 : ⟪F.N 1, u37 x⟫ < 0 := by
    rw [u37_inner F 1, F.zero 1 0 (by decide), F.zero 1 1 (by decide), F.zero 1 6 (by decide)]
    have h2 := F.neg 1 2 (by decide)
    nlinarith [mul_pos hub (neg_pos.mpr h2)]
  have hf5 : ⟪F.N 5, u37 x⟫ < 0 := by
    rw [u37_inner F 5, F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)]
    have h0 := F.neg 5 0 (by decide)
    nlinarith [mul_pos hua (neg_pos.mpr h0)]
  have hF2 : 0 < ⟪F.N 2, u37 x⟫ := by
    have h6_eq : F.f 2 (x 6) - F.f 2 (x 1) = F.f 2 (x 1) * omega5 x := by
      have f2_0 := F.zero 2 0 (by decide)
      have f2_5 := F.zero 2 5 (by decide)
      have f2_2 := F.zero 2 2 (by decide)
      have ev25 := fac_eval F 2 5
      rw [f2_5, f2_0, f2_2] at ev25
      have := eq5 F
      have h1' : F.f 2 (x 1) * (1 - oblX0 x 5 - oblX2 x 5) +
          oblX6 x 5 * (F.f 2 (x 6) - F.f 2 (x 1)) = 0 := by
        linear_combination -ev25
      have h2' : oblX6 x 5 * ((F.f 2 (x 6) - F.f 2 (x 1)) - F.f 2 (x 1) * omega5 x) = 0 := by
        linear_combination h1' + F.f 2 (x 1) * this
      exact sub_eq_zero.mp ((mul_eq_zero.mp h2').resolve_left hc5.ne')
    rw [u37_inner F 2, F.zero 2 0 (by decide), F.zero 2 2 (by decide), h6_eq]
    have h1 := F.neg 2 1 (by decide)
    have : 0 < (-F.f 2 (x 1)) * ((nC x - nB x) + (D45 x + omega3 x * nC x) +
        omega5 x * (D45 x + omega3 x * nB x)) :=
      mul_pos (by linarith) (by nlinarith)
    nlinarith
  have hLam : 0 < Lam5 x := by
    have h4 := F.neg 2 4 (by decide)
    have := u37_inner1 F 2
    rw [F.zero 2 5 (by decide), F.zero 2 0 (by decide)] at this
    by_contra hle
    push Not at hle
    nlinarith
  have hf3 : ⟪F.N 3, u37 x⟫ = 0 := by
    rw [u37_inner1 F 3, F.zero 3 5 (by decide), F.zero 3 0 (by decide), F.zero 3 4 (by decide)]
    ring
  have hf4 : ⟪F.N 4, u37 x⟫ < 0 := by
    rw [u37_inner1 F 4, F.zero 4 0 (by decide), F.zero 4 4 (by decide)]
    have h5 := F.neg 4 5 (by decide)
    nlinarith [mul_pos hL0 (neg_pos.mpr h5)]
  have hf6 : 0 < ⟪F.N 6, u37 x⟫ := by
    have h := u37_inner2 F 6
    rw [F.zero 6 2 (by decide), F.zero 6 3 (by decide)] at h
    have h6 := F.neg 6 6 (by decide)
    have : 0 < oblX0 x 3 * ⟪F.N 6, u37 x⟫ := by
      rw [h]; nlinarith [mul_pos hDnB (neg_pos.mpr h6)]
    exact pos_of_mul_pos_right this ha3.le
  have hf7 : ⟪F.N 7, u37 x⟫ = 0 := by
    have h := u37_inner2 F 7
    rw [F.zero 7 2 (by decide), F.zero 7 3 (by decide), F.zero 7 6 (by decide)] at h
    have : oblX0 x 3 * ⟪F.N 7, u37 x⟫ = 0 := by rw [h]; ring
    exact (mul_eq_zero.mp this).resolve_left ha3.ne'
  have hf8 : ⟪F.N 8, u37 x⟫ < 0 := by
    have h := u37_inner2 F 8
    rw [F.zero 8 3 (by decide), F.zero 8 6 (by decide)] at h
    have h2 := F.neg 8 2 (by decide)
    have : oblX0 x 3 * ⟪F.N 8, u37 x⟫ < 0 := by
      rw [h]; nlinarith [mul_pos hDnC (neg_pos.mpr h2)]
    by_contra hle; push Not at hle
    nlinarith
  -- tilt `x 4 - x 6`
  have hd3 : 0 < ⟪F.N 3, x 4 - x 6⟫ := by
    rw [← F.hN 3 (x 4) (x 6), F.zero 3 4 (by decide)]
    linarith [F.neg 3 6 (by decide)]
  have hd7 : ⟪F.N 7, x 4 - x 6⟫ < 0 := by
    rw [← F.hN 7 (x 4) (x 6), F.zero 7 6 (by decide)]
    linarith [F.neg 7 4 (by decide)]
  have hu_ne : u37 x ≠ 0 := by
    intro h0; rw [h0, inner_zero_right] at hf5; exact lt_irrefl _ hf5
  have hu_pos : 0 < ⟪u37 x, u37 x⟫ := real_inner_self_pos.mpr hu_ne
  -- depths
  have hz2 : 0 < z x (u37 x) 2 := by
    have key := key_gen (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) (nC x - nB x)
      (D45 x + omega3 x * nC x) (D45 x + omega3 x * nB x)
    have hz1 : z x (u37 x) 1 = 0 := by simp [z]
    change (nC x - nB x) * ⟪x 0 - x 1, u37 x⟫ + (D45 x + omega3 x * nC x) * ⟪x 2 - x 1, u37 x⟫ = _ at key
    have h1 := real_inner_self_nonneg
      (x := (nC x - nB x) • (x 0 - x 1) + (D45 x + omega3 x * nC x) • (x 2 - x 1))
    have h2 : (D45 x + omega3 x * nB x) *
          ((nC x - nB x) * ⟪x 0 - x 1, x 6 - x 1⟫ + (D45 x + omega3 x * nC x) * ⟪x 2 - x 1, x 6 - x 1⟫) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hDn.le (by nlinarith)
    by_contra hle; push Not at hle
    have hz0' : ⟪x 0 - x 1, u37 x⟫ < 0 := hcon
    have hz2' : ⟪x 2 - x 1, u37 x⟫ ≤ 0 := hle
    nlinarith [mul_pos hua (neg_pos.mpr hz0'), mul_nonneg hub.le (neg_nonneg.mpr hz2')]
  have hz4 : z x (u37 x) 4 < max (z x (u37 x) 0) (z x (u37 x) 3) := by
    have e : ⟪Lam4' x • (x 3 - x 0) - t • u37 x, u37 x⟫ = ⟪(1 + omega3 x) • (x 4 - x 0), u37 x⟫ := by
      rw [he]
    simp only [inner_sub_left, real_inner_smul_left] at e
    have e34 : ⟪x 3, u37 x⟫ - ⟪x 0, u37 x⟫ = z x (u37 x) 3 - z x (u37 x) 0 := by
      simp only [z, inner_sub_left]; ring
    have e44 : ⟪x 4, u37 x⟫ - ⟪x 0, u37 x⟫ = z x (u37 x) 4 - z x (u37 x) 0 := by
      simp only [z, inner_sub_left]; ring
    have e : Lam4' x * (z x (u37 x) 3 - z x (u37 x) 0) - t * ⟪u37 x, u37 x⟫ =
        (1 + omega3 x) * (z x (u37 x) 4 - z x (u37 x) 0) := by
      rw [← e34, ← e44]; linarith
    rcases le_total (z x (u37 x) 0) (z x (u37 x) 3) with h03 | h30
    · rw [max_eq_right h03]
      nlinarith [mul_pos ht hu_pos, mul_nonneg (sub_nonneg.mpr h03) (sub_nonneg.mpr hL1.le)]
    · rw [max_eq_left h30]
      nlinarith [mul_pos ht hu_pos, mul_nonneg (sub_nonneg.mpr h30) hL0.le]
  have hz1 : z x (u37 x) 1 = 0 := by simp [z]
  have hshift : ∀ v : Fin 7, ⟪x v, u37 x⟫ = z x (u37 x) v + ⟪x 1, u37 x⟫ := by
    intro v; simp only [z, inner_sub_left]; ring
  apply hU
  refine ⟨5, inferInstance, (![0, 1, 2, 3, 4] : ZMod 5 → Fin 7), {0, 2, 3, 6}, {1, 4, 5, 7, 8},
    u37 x, x 4 - x 6, 0, by decide,
    (by intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)),
    (by unfold S0xCycUD; decide), ?_, ?_, ?_⟩
  · intro t' ht'
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht'
    rcases ht' with rfl | rfl | rfl | rfl
    · exact Or.inl hf0
    · exact Or.inl hF2
    · exact Or.inr ⟨hf3, Or.inl hd3⟩
    · exact Or.inl hf6
  · intro t' ht'
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht'
    rcases ht' with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (neg_pos.mpr hf1)
    · exact Or.inl (neg_pos.mpr hf4)
    · exact Or.inl (neg_pos.mpr hf5)
    · exact Or.inr ⟨by rw [hf7, neg_zero], Or.inl (neg_pos.mpr hd7)⟩
    · exact Or.inl (neg_pos.mpr hf8)
  · refine robUniLex_five_u37 _ ?_ ?_ ?_
    · dsimp only [Matrix.cons_val]; rw [hshift 0, hshift 1]; linarith [hz1]
    · dsimp only [Matrix.cons_val]; rw [hshift 1, hshift 2]; linarith [hz1]
    · dsimp only [Matrix.cons_val]
      rw [hshift 4, hshift 0, hshift 3]
      rcases lt_max_iff.mp hz4 with h40 | h43
      · exact lt_max_of_lt_left (by linarith)
      · exact lt_max_of_lt_right (by linarith)

/-- Tie corollary: at the A1 tie `z2(w05) = z5(w05)`, `z5(u37) ≤ z2(u37)`. -/
theorem u37_tie {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (ha5 : 1 < oblX0 x 5) (ha4 : oblX0 x 4 < 1)
    (hL : 0 ≤ Lam5 x) (h346 : F.f 8 (x 0) ≤ F.f 8 (x 5))
    (hU : ¬ Gen.LexAny F) (hS : ¬ SplitAny24 F)
    (htie : z x (x 5 - x 0) 2 = z x (x 5 - x 0) 5)
    (h45 : z x (x 5 - x 0) 4 < z x (x 5 - x 0) 5) :
    z x (u37 x) 5 ≤ z x (u37 x) 2 := by
  have hb := (A12.tie1_bound F hC ha5 ha4 hL h346 hU hS htie h45).1
  have e : z x (u37 x) 2 - z x (u37 x) 5 =
      Lam4' x * (z x (x 5 - x 0) 2 - z x (x 5 - x 0) 5) - Lam5 x * ⟪x 2 - x 5, x 4 - x 0⟫ := by
    have h25 : z x (u37 x) 2 - z x (u37 x) 5 = ⟪x 2 - x 5, u37 x⟫ := by
      simp only [z, ← inner_sub_left]; congr 1; abel
    have h25' : z x (x 5 - x 0) 2 - z x (x 5 - x 0) 5 = ⟪x 2 - x 5, x 5 - x 0⟫ := by
      simp only [z, ← inner_sub_left]; congr 1; abel
    rw [h25, h25', u37_eq1 F, inner_sub_right, real_inner_smul_right, real_inner_smul_right]
  rw [htie, sub_self, mul_zero, zero_sub] at e
  nlinarith [mul_nonneg hL (neg_nonneg.mpr hb)]

/-! ### E34-26-Full -/

/-- Lex order on depth triples as a linear order. -/
def iota3 (p : ℝ × ℝ × ℝ) : ℝ ×ₗ ℝ ×ₗ ℝ := toLex (p.1, toLex p.2)

theorem lexLt3_iff (p q : ℝ × ℝ × ℝ) : LexLt3 p q ↔ iota3 p < iota3 q := by
  obtain ⟨p1, p2, p3⟩ := p
  obtain ⟨q1, q2, q3⟩ := q
  simp only [LexLt3, LexPos3, iota3, Prod.Lex.toLex_lt_toLex, sub_pos]
  constructor
  · rintro (h | ⟨h, h' | ⟨h', h''⟩⟩)
    · exact Or.inl h
    · exact Or.inr ⟨(sub_eq_zero.mp h).symm, Or.inl (by linarith)⟩
    · exact Or.inr ⟨(sub_eq_zero.mp h).symm, Or.inr ⟨(sub_eq_zero.mp h').symm, by linarith⟩⟩
  · rintro (h | ⟨h, h' | ⟨h', h''⟩⟩)
    · exact Or.inl h
    · exact Or.inr ⟨by linarith, Or.inl (by linarith)⟩
    · exact Or.inr ⟨by linarith, Or.inr ⟨by linarith, by linarith⟩⟩

theorem five_E34_lin {α : Type*} [LinearOrder α] (z : ZMod 5 → α)
    (h04 : z 0 < z 4) (h43 : z 4 < z 3) (h41 : z 4 < z 1) (h2 : z 3 < z 2 ∨ z 1 < z 2) :
    ∀ (B : ZMod 5) (b c d : ℕ), 0 < b → b < c → c < d → d < 5 →
      z B < z (B + b) ∨ z (B + c) < z (B + b) ∨ z B < z (B + d) ∨ z (B + c) < z (B + d) := by
  intro B b c d hb hbc hcd hd
  have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by revert B; decide
  have hbcd : (b = 1 ∧ c = 2 ∧ d = 3) ∨ (b = 1 ∧ c = 2 ∧ d = 4) ∨
      (b = 1 ∧ c = 3 ∧ d = 4) ∨ (b = 2 ∧ c = 3 ∧ d = 4) := by omega
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
  all_goals (by_contra hh; simp only [not_or, not_lt] at hh; rcases h2 with h2 | h2 <;> order)

theorem robUniLex_five_E34 (z : ZMod 5 → ℝ × ℝ × ℝ)
    (h04 : LexLt3 (z 0) (z 4)) (h43 : LexLt3 (z 4) (z 3)) (h41 : LexLt3 (z 4) (z 1))
    (h2 : LexLt3 (z 3) (z 2) ∨ LexLt3 (z 1) (z 2)) : RobUniLex z := by
  intro B b c d hb hbc hcd hd
  have := five_E34_lin (fun i => iota3 (z i)) ((lexLt3_iff _ _).mp h04) ((lexLt3_iff _ _).mp h43)
    ((lexLt3_iff _ _).mp h41)
    (h2.imp (fun h => (lexLt3_iff _ _).mp h) (fun h => (lexLt3_iff _ _).mp h)) B b c d hb hbc hcd hd
  simpa only [lexLt3_iff] using this

theorem lexAny_or_split_E3426_full {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (ha5 : 1 < oblX0 x 5) (ha4 : oblX0 x 4 < 1)
    (hsig : F.f 8 (x 5) < F.f 8 (x 0))
    (ha : oblX0 x 4 < oblX0 x 3) (hb : oblX2 x 4 < oblX2 x 3) (hc : oblX6 x 4 < oblX6 x 3)
    (hz : z x (x 3 - x 4) 5 < z x (x 3 - x 4) 2 ∧ z x (x 3 - x 4) 0 < z x (x 3 - x 4) 5 ∧
      (z x (x 3 - x 4) 4 < z x (x 3 - x 4) 5 ∨
        min (z x (x 3 - x 4) 2) (z x (x 3 - x 4) 4) < z x (x 3 - x 4) 6)) :
    Gen.LexAny F ∨ SplitAny24 F := by
  by_cases h45 : z x (x 3 - x 4) 4 < z x (x 3 - x 4) 5
  · exact A12.lexAny_or_split_E3426 F hC ha5 ha4 hsig ha hb hc ⟨max_lt hz.2.1 h45, hz.1⟩
  left
  have h26 : min (z x (x 3 - x 4) 2) (z x (x 3 - x 4) 4) < z x (x 3 - x 4) 6 :=
    hz.2.2.resolve_left h45
  push Not at h45
  let _ := hC
  have T := type24OfFac F
  have hc4 : 0 < oblX6 x 4 := T.X6_pos (v := 4) (by decide)
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hnc : F.f 3 (x 1) < F.f 3 (x 6) := (nC_pos_iff F).mp (nC_pos_of F ha4.le ha5)
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
  have hd3_z : ⟪F.N 3, x 4 - x 5⟫ = 0 := by
    rw [← F.hN 3 (x 4) (x 5), F.zero 3 4 (by decide), F.zero 3 5 (by decide), sub_self]
  have hd8_z : 0 < ⟪F.N 8, x 4 - x 5⟫ := by
    rw [← F.hN 8 (x 4) (x 5), F.zero 8 4 (by decide)]
    linarith [F.neg 8 5 (by decide)]
  have hd2_pos : 0 < ⟪x 4 - x 5, x 4 - x 5⟫ :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr (T.inj.ne (by decide)))
  have hz0 : z x w43 0 < z x w43 5 := hz.2.1
  have hz5 : z x w43 5 < z x w43 2 := hz.1
  have hw : ∀ v : Fin 7, ⟪x v, w43⟫ = z x w43 v + ⟪x 1, w43⟫ := by
    intro v; simp only [z, inner_sub_left]; ring
  refine ⟨5, inferInstance, c, {3, 6, 7, 8}, {0, 1, 2, 4, 5}, w43, x 4 - x 5, d1, by decide,
    hc_inj, (by unfold S0xCycUD; decide), ?_, ?_, ?_⟩
  · intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact Or.inr ⟨hf3_0, Or.inr ⟨hd3_z, hd3_1⟩⟩
    · exact Or.inl hf6
    · exact Or.inl hf7
    · exact Or.inr ⟨hf8_0, Or.inl hd8_z⟩
  · intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
  · refine robUniLex_five_E34 _ ?_ ?_ ?_ ?_
    · refine Or.inl ?_
      change 0 < ⟪x 5, w43⟫ - ⟪x 0, w43⟫
      rw [hw 5, hw 0]; linarith
    · refine Or.inl ?_
      change 0 < ⟪x 2, w43⟫ - ⟪x 5, w43⟫
      rw [hw 2, hw 5]; linarith
    · show LexPos3 (⟪x (c 1), w43⟫ - ⟪x (c 4), w43⟫) (⟪x (c 1), x 4 - x 5⟫ - ⟪x (c 4), x 4 - x 5⟫)
        (⟪x (c 1), d1⟫ - ⟪x (c 4), d1⟫)
      have hc1 : c 1 = 4 := rfl
      have hc4 : c 4 = 5 := rfl
      rw [hc1, hc4, ← inner_sub_left, ← inner_sub_left, ← inner_sub_left]
      have e45 : ⟪x 4 - x 5, w43⟫ = z x w43 4 - z x w43 5 := by
        simp only [z, ← inner_sub_left]; congr 1; abel
      rcases eq_or_lt_of_le h45 with h | h
      · exact Or.inr ⟨by rw [e45]; linarith, Or.inl hd2_pos⟩
      · exact Or.inl (by rw [e45]; linarith)
    · rcases min_lt_iff.mp h26 with h | h
      · refine Or.inl (Or.inl ?_)
        change 0 < ⟪x 6, w43⟫ - ⟪x 2, w43⟫
        rw [hw 6, hw 2]; linarith
      · refine Or.inr (Or.inl ?_)
        change 0 < ⟪x 6, w43⟫ - ⟪x 4, w43⟫
        rw [hw 6, hw 4]; linarith

end Minimality.T24.A15
