module

public import Minimality.M4dType24
public import Minimality.GenQuad
public import Minimality.SplitRows
public import Minimality.SplitLeaf
public import Minimality.Q45
public import Minimality.Type24Regions

/-!
# Type 24, region B corner (`c3 ≥ 1, c4 ≥ 1`): `u05 = x 0 - x 5` (`-w05`)

Formalizes the referee-confirmed pieces of Carbon A34 (`A34-REFEREE.md` §5):
- **L1** (`u05_facings`, `u05_rim_pos`, `u05_rim_neg`): facet signs at `u05 = x 0 - x 5`
  and `StrictRimN` statements for `(1,2,5,3,4,6)` and `(1,2,0,4,6)` via `Split.rim_of_fac`.
- **L2** (`u05_guard_id`, `u05_guard_pos`, `u05_z0_pos`, `u05_z3_eq`, `u05_collapse`,
  `u05_collapse_contrapos`, `C46_eq`, `C40_eq`, `C52_eq`, `C50_eq`): collapse on
  `(1,2,5,3,4,6)` and contrapositive depth cone.
- **L3** (`u05_rises_e12`, `u05_rises_e61`, `u05_split_p4_e12`, `u05_split_p5_e12`,
  `u05_split_p4_e61`, `u05_split_p5_e61`): rise determinant formulas and `SplitRows`
  equivalences on `(1,2,5,3,4,6)`.
- **L7a, L7b** (`u07_saddle_elim_id`, `psi_05_46_26_id`): pure ring identities.
- **L8** (`f126_x4_lt_x0_iff`, `f126_x5_lt_x0_iff`, `q45HalfHyp_false_of_B`): `Q45HalfHyp`
  sign equivalences and region-B discharge.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality.T24.A10

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell
  Minimality.LexCell Minimality.Split Minimality.T24.M4 Minimality.T24.A7
  Minimality.T24.Q45 Minimality.T24.Reg

/-! ### L1: Facet signs and rims at `u05 = x 0 - x 5` -/

/-- The primary corner view `u05 := x 0 - x 5 = (1 - a5, -b5, -c5)` (`= -w05`). -/
noncomputable def u05 (x : Fin 7 → ℝ³) : ℝ³ := x 0 - x 5

/-- **L1 facet signs at `u05 = x 0 - x 5`**:
- `012 +` (`0 < ⟪F.N 0, u05 x⟫`): uses `c5 > 0` (from `F` via `T.X6_pos`).
- `016 +` (`0 < ⟪F.N 1, u05 x⟫`): uses `b5 > 0` (from `F` via `T.X2_pos`).
- `046 +` (`0 < ⟪F.N 4, u05 x⟫`): uses `ha5 : a5 < 1`, `hC : CbarIn x` (`om4 * om5 > 1`), `c5 > 0`.
- `126 -` (`⟪F.N 5, u05 x⟫ < 0`): uses `ha5 : a5 < 1`.
- `235 -` (`⟪F.N 6, u05 x⟫ < 0`): unconditional from `F` (`f6(x5) = 0, f6(x0) < 0`).
- `236 -` (`⟪F.N 7, u05 x⟫ < 0`): uses `ha5 : a5 < 1`, `hC : CbarIn x` (`om3 > 0, om5 > 0`), `c5 > 0`.
- `346 -` (`⟪F.N 8, u05 x⟫ < 0`): uses `hsig : F.f 8 (x 0) < F.f 8 (x 5)` (`σ < 1`).
- `025 = 0`, `0345 = 0`: unconditional from `F` (`0, 5 ∈ S 2, S 3`). -/
theorem u05_facings {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (ha5 : oblX0 x 5 < 1) (hsig : F.f 8 (x 0) < F.f 8 (x 5)) :
    0 < ⟪F.N 0, u05 x⟫ ∧ 0 < ⟪F.N 1, u05 x⟫ ∧ 0 < ⟪F.N 4, u05 x⟫ ∧
    ⟪F.N 5, u05 x⟫ < 0 ∧ ⟪F.N 6, u05 x⟫ < 0 ∧ ⟪F.N 7, u05 x⟫ < 0 ∧
    ⟪F.N 8, u05 x⟫ < 0 ∧ ⟪F.N 2, u05 x⟫ = 0 ∧ ⟪F.N 3, u05 x⟫ = 0 := by
  have T := type24OfFac F
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hd5 : 0 < 1 - oblX0 x 5 := sub_pos.mpr ha5
  have hom3 : 0 < omega3 x := hC.1
  have hom4 : 0 < omega4 x := hC.2.1
  have hom5 : 0 < omega5 x := hC.2.2.1
  have hom45 : 1 < omega4 x * omega5 x := by
    have hD : Delta24 x = omega3 x * omega4 x * omega5 x - omega3 x - omega4 x - omega5 x - 2 := rfl
    have hD0 : 0 ≤ Delta24 x := hC.2.2.2
    nlinarith
  have h5e : oblX0 x 5 + oblX2 x 5 - 1 = omega5 x * oblX6 x 5 := by linarith [eq5 F]
  have hf := fun t v => fac_eval F t v
  have h0 : 0 < ⟪F.N 0, u05 x⟫ := by
    rw [u05, ← F.hN 0 (x 0) (x 5), F.zero 0 0 (by decide), zero_sub, hf 0 5,
      F.zero 0 1 (by decide), F.zero 0 0 (by decide), F.zero 0 2 (by decide)]
    have hn : 0 < -F.f 0 (x 6) := by linarith [F.neg 0 6 (by decide)]
    nlinarith
  have h1 : 0 < ⟪F.N 1, u05 x⟫ := by
    rw [u05, ← F.hN 1 (x 0) (x 5), F.zero 1 0 (by decide), zero_sub, hf 1 5,
      F.zero 1 1 (by decide), F.zero 1 0 (by decide), F.zero 1 6 (by decide)]
    have hn : 0 < -F.f 1 (x 2) := by linarith [F.neg 1 2 (by decide)]
    nlinarith
  have h4 : 0 < ⟪F.N 4, u05 x⟫ := by
    rw [u05, ← F.hN 4 (x 0) (x 5), F.zero 4 0 (by decide), zero_sub, hf 4 5,
      F.zero 4 0 (by decide), F.zero 4 6 (by decide)]
    have h41 : F.f 4 (x 1) < 0 := F.neg 4 1 (by decide)
    have h42 : F.f 4 (x 2) - F.f 4 (x 1) = omega4 x * F.f 4 (x 1) := by
      have hf4 := hf 4 4
      rw [F.zero 4 4 (by decide), F.zero 4 0 (by decide), F.zero 4 6 (by decide)] at hf4
      have e4 := eq4 F
      have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
      nlinarith
    have h4v : F.f 4 (x 1) + oblX0 x 5 * (0 - F.f 4 (x 1)) + oblX2 x 5 * (F.f 4 (x 2) - F.f 4 (x 1)) +
        oblX6 x 5 * (0 - F.f 4 (x 1)) =
        ((omega4 x + 1) * (1 - oblX0 x 5) + (omega4 x * omega5 x - 1) * oblX6 x 5) * F.f 4 (x 1) := by
      rw [h42]; linear_combination F.f 4 (x 1) * omega4 x * h5e
    rw [h4v]
    have hpos : 0 < (omega4 x + 1) * (1 - oblX0 x 5) + (omega4 x * omega5 x - 1) * oblX6 x 5 := by
      nlinarith
    nlinarith
  have h5 : ⟪F.N 5, u05 x⟫ < 0 := by
    rw [u05, ← F.hN 5 (x 0) (x 5), hf 5 5, F.zero 5 1 (by decide), F.zero 5 2 (by decide),
      F.zero 5 6 (by decide)]
    have h50 : F.f 5 (x 0) < 0 := F.neg 5 0 (by decide)
    nlinarith
  have h6 : ⟪F.N 6, u05 x⟫ < 0 := by
    rw [u05, ← F.hN 6 (x 0) (x 5), F.zero 6 5 (by decide), sub_zero]
    exact F.neg 6 0 (by decide)
  have h7 : ⟪F.N 7, u05 x⟫ < 0 := by
    rw [u05, ← F.hN 7 (x 0) (x 5), hf 7 5, F.zero 7 2 (by decide), F.zero 7 6 (by decide)]
    have h71 : F.f 7 (x 1) < 0 := F.neg 7 1 (by decide)
    have h70 : F.f 7 (x 0) = (omega3 x + 1) * F.f 7 (x 1) := by
      have hf3 := hf 7 3
      rw [F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at hf3
      have e3 := eq3 F
      have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
      nlinarith
    have h7v : F.f 7 (x 0) - (F.f 7 (x 1) + oblX0 x 5 * (F.f 7 (x 0) - F.f 7 (x 1)) +
        oblX2 x 5 * (0 - F.f 7 (x 1)) + oblX6 x 5 * (0 - F.f 7 (x 1))) =
        ((omega3 x + 1) * (1 - oblX0 x 5) + (omega5 x + 1) * oblX6 x 5) * F.f 7 (x 1) := by
      rw [h70]; linear_combination F.f 7 (x 1) * h5e
    rw [h7v]
    have hpos : 0 < (omega3 x + 1) * (1 - oblX0 x 5) + (omega5 x + 1) * oblX6 x 5 := by
      nlinarith
    nlinarith
  have h8 : ⟪F.N 8, u05 x⟫ < 0 := by
    rw [u05, ← F.hN 8 (x 0) (x 5)]; linarith [hsig]
  have h2 : ⟪F.N 2, u05 x⟫ = 0 := by
    rw [u05, ← F.hN 2 (x 0) (x 5), F.zero 2 0 (by decide), F.zero 2 5 (by decide), sub_zero]
  have h3 : ⟪F.N 3, u05 x⟫ = 0 := by
    rw [u05, ← F.hN 3 (x 0) (x 5), F.zero 3 0 (by decide), F.zero 3 5 (by decide), sub_zero]
  exact ⟨h0, h1, h4, h5, h6, h7, h8, h2, h3⟩

/-- The 6-rim cycle `(1, 2, 5, 3, 4, 6)` at `{025+, 0345+}` of `u05`. -/
def c05Pos : ZMod 6 → Fin 7 := ![1, 2, 5, 3, 4, 6]

/-- The 5-rim cycle `(1, 2, 0, 4, 6)` at `{025-, 0345-}` of `u05`. -/
def c05Neg : ZMod 5 → Fin 7 := ![1, 2, 0, 4, 6]

theorem c05Pos_inj : Function.Injective c05Pos := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)

theorem c05Neg_inj : Function.Injective c05Neg := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)

/-- **L1 positive rim `(1, 2, 5, 3, 4, 6)`** via `Split.rim_of_fac` on `u05 x + ε • (x 0 - x 1)`. -/
theorem u05_rim_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (ha5 : oblX0 x 5 < 1) (hsig : F.f 8 (x 0) < F.f 8 (x 5)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      StrictRimN x (u05 x + ε • (x 0 - x 1)) c05Pos ∨
      StrictRimN x (u05 x + ε • (x 0 - x 1)) (fun i => c05Pos (-i)) := by
  have T := type24OfFac F
  have hfac := u05_facings F hC ha5 hsig
  let pat : Fin 9 → Bool := fun t => decide (t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4)
  have hcyc : S0xCycOK s0x_S24 c05Pos pat := by unfold S0xCycOK; decide
  have hn2 : 0 < ⟪F.N 2, x 0 - x 1⟫ := by
    rw [← F.hN 2 (x 0) (x 1), F.zero 2 0 (by decide), zero_sub]
    linarith [F.neg 2 1 (by decide)]
  have hn3 : 0 < ⟪F.N 3, x 0 - x 1⟫ := by
    rw [← F.hN 3 (x 0) (x 1), F.zero 3 0 (by decide), zero_sub]
    linarith [F.neg 3 1 (by decide)]
  have hF : ∀ᶠ ε in 𝓝[>] (0 : ℝ), StrictFac F pat (u05 x + ε • (x 0 - x 1)) := by
    refine eventually_all.2 fun t => ?_
    fin_cases t
    · filter_upwards [eventually_pos_affine (Or.inl hfac.1)] with ε hε
      refine ⟨fun _ => ?_, fun h => by simp [pat] at h⟩
      rw [inner_add_right, real_inner_smul_right]; exact hε
    · filter_upwards [eventually_pos_affine (Or.inl hfac.2.1)] with ε hε
      refine ⟨fun _ => ?_, fun h => by simp [pat] at h⟩
      rw [inner_add_right, real_inner_smul_right]; exact hε
    · filter_upwards [eventually_pos_affine (Or.inr ⟨hfac.2.2.2.2.2.2.2.1, hn2⟩)] with ε hε
      refine ⟨fun _ => ?_, fun h => by simp [pat] at h⟩
      rw [inner_add_right, real_inner_smul_right]; exact hε
    · filter_upwards [eventually_pos_affine (Or.inr ⟨hfac.2.2.2.2.2.2.2.2, hn3⟩)] with ε hε
      refine ⟨fun _ => ?_, fun h => by simp [pat] at h⟩
      rw [inner_add_right, real_inner_smul_right]; exact hε
    · filter_upwards [eventually_pos_affine (Or.inl hfac.2.2.1)] with ε hε
      refine ⟨fun _ => ?_, fun h => by simp [pat] at h⟩
      rw [inner_add_right, real_inner_smul_right]; exact hε
    · filter_upwards [eventually_pos_affine (B := -⟪F.N 5, x 0 - x 1⟫) (Or.inl (neg_pos.mpr hfac.2.2.2.1))] with ε hε
      refine ⟨fun h => by simp [pat] at h, fun _ => ?_⟩
      dsimp; rw [inner_add_right, real_inner_smul_right]; linarith
    · filter_upwards [eventually_pos_affine (B := -⟪F.N 6, x 0 - x 1⟫) (Or.inl (neg_pos.mpr hfac.2.2.2.2.1))] with ε hε
      refine ⟨fun h => by simp [pat] at h, fun _ => ?_⟩
      dsimp; rw [inner_add_right, real_inner_smul_right]; linarith
    · filter_upwards [eventually_pos_affine (B := -⟪F.N 7, x 0 - x 1⟫) (Or.inl (neg_pos.mpr hfac.2.2.2.2.2.1))] with ε hε
      refine ⟨fun h => by simp [pat] at h, fun _ => ?_⟩
      dsimp; rw [inner_add_right, real_inner_smul_right]; linarith
    · filter_upwards [eventually_pos_affine (B := -⟪F.N 8, x 0 - x 1⟫) (Or.inl (neg_pos.mpr hfac.2.2.2.2.2.2.1))] with ε hε
      refine ⟨fun h => by simp [pat] at h, fun _ => ?_⟩
      dsimp; rw [inner_add_right, real_inner_smul_right]; linarith
  filter_upwards [hF] with ε hε
  exact rim_of_fac F T.inj c05Pos_inj (by norm_num) hcyc hε

/-- **L1 negative rim `(1, 2, 0, 4, 6)`** via `Split.rim_of_fac` on `u05 x + ε • (x 1 - x 0)`. -/
theorem u05_rim_neg {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (ha5 : oblX0 x 5 < 1) (hsig : F.f 8 (x 0) < F.f 8 (x 5)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      StrictRimN x (u05 x + ε • (x 1 - x 0)) c05Neg ∨
      StrictRimN x (u05 x + ε • (x 1 - x 0)) (fun i => c05Neg (-i)) := by
  have T := type24OfFac F
  have hfac := u05_facings F hC ha5 hsig
  let pat : Fin 9 → Bool := fun t => decide (t = 0 ∨ t = 1 ∨ t = 4)
  have hcyc : S0xCycOK s0x_S24 c05Neg pat := by unfold S0xCycOK; decide
  have hn2 : 0 < -⟪F.N 2, x 1 - x 0⟫ := by
    rw [← F.hN 2 (x 1) (x 0), F.zero 2 0 (by decide), sub_zero]
    linarith [F.neg 2 1 (by decide)]
  have hn3 : 0 < -⟪F.N 3, x 1 - x 0⟫ := by
    rw [← F.hN 3 (x 1) (x 0), F.zero 3 0 (by decide), sub_zero]
    linarith [F.neg 3 1 (by decide)]
  have hF : ∀ᶠ ε in 𝓝[>] (0 : ℝ), StrictFac F pat (u05 x + ε • (x 1 - x 0)) := by
    refine eventually_all.2 fun t => ?_
    fin_cases t
    · filter_upwards [eventually_pos_affine (Or.inl hfac.1)] with ε hε
      refine ⟨fun _ => ?_, fun h => by simp [pat] at h⟩
      rw [inner_add_right, real_inner_smul_right]; exact hε
    · filter_upwards [eventually_pos_affine (Or.inl hfac.2.1)] with ε hε
      refine ⟨fun _ => ?_, fun h => by simp [pat] at h⟩
      rw [inner_add_right, real_inner_smul_right]; exact hε
    · filter_upwards [eventually_pos_affine (A := -⟪F.N 2, u05 x⟫) (B := -⟪F.N 2, x 1 - x 0⟫) (Or.inr ⟨by linarith [hfac.2.2.2.2.2.2.2.1], hn2⟩)] with ε hε
      refine ⟨fun h => by simp [pat] at h, fun _ => ?_⟩
      dsimp; rw [inner_add_right, real_inner_smul_right]; linarith
    · filter_upwards [eventually_pos_affine (A := -⟪F.N 3, u05 x⟫) (B := -⟪F.N 3, x 1 - x 0⟫) (Or.inr ⟨by linarith [hfac.2.2.2.2.2.2.2.2], hn3⟩)] with ε hε
      refine ⟨fun h => by simp [pat] at h, fun _ => ?_⟩
      dsimp; rw [inner_add_right, real_inner_smul_right]; linarith
    · filter_upwards [eventually_pos_affine (Or.inl hfac.2.2.1)] with ε hε
      refine ⟨fun _ => ?_, fun h => by simp [pat] at h⟩
      rw [inner_add_right, real_inner_smul_right]; exact hε
    · filter_upwards [eventually_pos_affine (B := -⟪F.N 5, x 1 - x 0⟫) (Or.inl (neg_pos.mpr hfac.2.2.2.1))] with ε hε
      refine ⟨fun h => by simp [pat] at h, fun _ => ?_⟩
      dsimp; rw [inner_add_right, real_inner_smul_right]; linarith
    · filter_upwards [eventually_pos_affine (B := -⟪F.N 6, x 1 - x 0⟫) (Or.inl (neg_pos.mpr hfac.2.2.2.2.1))] with ε hε
      refine ⟨fun h => by simp [pat] at h, fun _ => ?_⟩
      dsimp; rw [inner_add_right, real_inner_smul_right]; linarith
    · filter_upwards [eventually_pos_affine (B := -⟪F.N 7, x 1 - x 0⟫) (Or.inl (neg_pos.mpr hfac.2.2.2.2.2.1))] with ε hε
      refine ⟨fun h => by simp [pat] at h, fun _ => ?_⟩
      dsimp; rw [inner_add_right, real_inner_smul_right]; linarith
    · filter_upwards [eventually_pos_affine (B := -⟪F.N 8, x 1 - x 0⟫) (Or.inl (neg_pos.mpr hfac.2.2.2.2.2.2.1))] with ε hε
      refine ⟨fun h => by simp [pat] at h, fun _ => ?_⟩
      dsimp; rw [inner_add_right, real_inner_smul_right]; linarith
  filter_upwards [hF] with ε hε
  exact rim_of_fac F T.inj c05Neg_inj (by norm_num) hcyc hε

/-! ### L2: Collapse at `u05` on `(1, 2, 5, 3, 4, 6)` -/

private theorem u05_rep {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    u05 x = (1 - oblX0 x 5) • (x 0 - x 1) - oblX2 x 5 • (x 2 - x 1) -
      oblX6 x 5 • (x 6 - x 1) := by
  have T := type24OfFac F
  have h5 := T.rep 5
  dsimp [u05]
  rw [show x 0 - x 5 = (x 0 - x 1) - (x 5 - x 1) by abel, h5]
  module

/-- **L2 guard identity**: `-b5 z2(u05) - c5 z6(u05) = ||(0, b5, c5)||_G^2 + d5 (b5 al + c5 be)`. -/
theorem u05_guard_id {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    -oblX2 x 5 * ⟪x 2 - x 1, u05 x⟫ - oblX6 x 5 * ⟪x 6 - x 1, u05 x⟫ =
      ⟪oblX2 x 5 • (x 2 - x 1) + oblX6 x 5 • (x 6 - x 1),
        oblX2 x 5 • (x 2 - x 1) + oblX6 x 5 • (x 6 - x 1)⟫ +
        (1 - oblX0 x 5) * (oblX2 x 5 * (-⟪x 0 - x 1, x 2 - x 1⟫) +
          oblX6 x 5 * (-⟪x 0 - x 1, x 6 - x 1⟫)) := by
  rw [u05_rep F]
  set e0 := x 0 - x 1
  set e2 := x 2 - x 1
  set e6 := x 6 - x 1
  simp only [inner_sub_right, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_comm e2 e0, real_inner_comm e6 e0, real_inner_comm e6 e2]
  ring

/-- **L2 guard positivity**: on `OB1` with `a5 < 1`, `-b5 z2(u05) - c5 z6(u05) > 0`
(so `z2(u05) ≥ 0` and `z6(u05) ≥ 0` cannot both hold). -/
theorem u05_guard_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (ha5 : oblX0 x 5 < 1)
    (hab : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0) (hac : ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0) :
    0 < -oblX2 x 5 * ⟪x 2 - x 1, u05 x⟫ - oblX6 x 5 * ⟪x 6 - x 1, u05 x⟫ := by
  have T := type24OfFac F
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hd5 : 0 < 1 - oblX0 x 5 := sub_pos.mpr ha5
  have hne : oblX2 x 5 • (x 2 - x 1) + oblX6 x 5 • (x 6 - x 1) ≠ 0 := by
    intro h0
    have hdet0 : vol3 (x 0 - x 1) (oblX2 x 5 • (x 2 - x 1) + oblX6 x 5 • (x 6 - x 1)) (x 6 - x 1) = 0 := by
      rw [h0]; simp [vol3]
    have hdet1 : vol3 (x 0 - x 1) (oblX2 x 5 • (x 2 - x 1) + oblX6 x 5 • (x 6 - x 1)) (x 6 - x 1) =
        oblX2 x 5 * det24 x := by
      simp only [vol3, det24, PiLp.inner_apply, Fin.sum_univ_three, Split.cross_0, Split.cross_1,
        Split.cross_2, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    have : oblX2 x 5 * det24 x = 0 := by linarith
    rcases mul_eq_zero.mp this with h2 | hd
    · linarith
    · exact T.det_ne hd
  have hnorm : 0 < ⟪oblX2 x 5 • (x 2 - x 1) + oblX6 x 5 • (x 6 - x 1),
      oblX2 x 5 • (x 2 - x 1) + oblX6 x 5 • (x 6 - x 1)⟫ := real_inner_self_pos.mpr hne
  rw [u05_guard_id F]
  nlinarith [mul_nonneg hb5.le (neg_nonneg.mpr hab), mul_nonneg hc5.le (neg_nonneg.mpr hac)]

/-- **L2 `z0(u05) > 0`** on `OB1` with `a5 < 1`. -/
theorem u05_z0_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (ha5 : oblX0 x 5 < 1)
    (hab : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0) (hac : ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0) :
    0 < ⟪x 0 - x 1, u05 x⟫ := by
  have T := type24OfFac F
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hd5 : 0 < 1 - oblX0 x 5 := sub_pos.mpr ha5
  have hA : 0 < ⟪x 0 - x 1, x 0 - x 1⟫ :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide))
  rw [u05_rep F, inner_sub_right, inner_sub_right, inner_smul_right, inner_smul_right,
    inner_smul_right]
  nlinarith

/-- **L2 `z3` decomposition**: `z3(u05) = -(σ + τ - 1) z0(u05) + σ z4(u05) + τ z5(u05)`. -/
theorem u05_z3_eq {x : Fin 7 → ℝ³} {σ τ : ℝ}
    (hdec : x 3 - x 0 = σ • (x 4 - x 0) + τ • (x 5 - x 0)) :
    ⟪x 3 - x 1, u05 x⟫ =
      -(σ + τ - 1) * ⟪x 0 - x 1, u05 x⟫ + σ * ⟪x 4 - x 1, u05 x⟫ + τ * ⟪x 5 - x 1, u05 x⟫ := by
  have h31 : x 3 - x 1 =
      -(σ + τ - 1) • (x 0 - x 1) + σ • (x 4 - x 1) + τ • (x 5 - x 1) := by
    have : x 3 - x 1 = (x 3 - x 0) + (x 0 - x 1) := by abel
    rw [this, hdec]
    module
  rw [h31]
  simp only [inner_add_left, real_inner_smul_left]

/-- **L2 collapse at `u05`** on the 6-rim `(1, 2, 5, 3, 4, 6)`:
`z4(u05) < min 0 z6(u05)` and `z5(u05) < min 0 z2(u05)` imply `LexAny F`. -/
theorem u05_collapse {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (ha5 : oblX0 x 5 < 1) (hsig : F.f 8 (x 0) < F.f 8 (x 5))
    (hab : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0) (hac : ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0)
    (h4 : ⟪x 4 - x 1, u05 x⟫ < min 0 ⟪x 6 - x 1, u05 x⟫)
    (h5 : ⟪x 5 - x 1, u05 x⟫ < min 0 ⟪x 2 - x 1, u05 x⟫) :
    Minimality.Gen.LexAny F := by
  have T := type24OfFac F
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hz0 : 0 < ⟪x 0 - x 1, u05 x⟫ := u05_z0_pos F ha5 hab hac
  have hguard : 0 < -oblX2 x 5 * ⟪x 2 - x 1, u05 x⟫ - oblX6 x 5 * ⟪x 6 - x 1, u05 x⟫ :=
    u05_guard_pos F ha5 hab hac
  have hz2_or_z6 : ⟪x 2 - x 1, u05 x⟫ < 0 ∨ ⟪x 6 - x 1, u05 x⟫ < 0 := by
    by_contra hn
    push Not at hn
    nlinarith
  have h40 : ⟪x 4 - x 1, u05 x⟫ < 0 := lt_of_lt_of_le h4 (min_le_left _ _)
  have h46 : ⟪x 4 - x 1, u05 x⟫ < ⟪x 6 - x 1, u05 x⟫ := lt_of_lt_of_le h4 (min_le_right _ _)
  have h50 : ⟪x 5 - x 1, u05 x⟫ < 0 := lt_of_lt_of_le h5 (min_le_left _ _)
  have h52 : ⟪x 5 - x 1, u05 x⟫ < ⟪x 2 - x 1, u05 x⟫ := lt_of_lt_of_le h5 (min_le_right _ _)
  obtain ⟨σ, τ, hσ, hτ, hdec, -, -, -⟩ := lemmaM_coords F
  have h1st : 1 < σ + τ := by
    have hev := congrArg (fun v => ⟪F.N 7, v⟫) hdec
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
      ← F.hN 7 (x 3) (x 0), ← F.hN 7 (x 4) (x 0), ← F.hN 7 (x 5) (x 0),
      F.zero 7 3 (by decide)] at hev
    have h70 : 0 < -F.f 7 (x 0) := by linarith [F.neg 7 0 (by decide)]
    have h74 : 0 < -F.f 7 (x 4) := by linarith [F.neg 7 4 (by decide)]
    have h75 : 0 < -F.f 7 (x 5) := by linarith [F.neg 7 5 (by decide)]
    nlinarith
  have hz3_eq := u05_z3_eq (σ := σ) (τ := τ) hdec
  have hz345 : ⟪x 3 - x 1, u05 x⟫ < max ⟪x 4 - x 1, u05 x⟫ ⟪x 5 - x 1, u05 x⟫ := by
    have hM : max ⟪x 4 - x 1, u05 x⟫ ⟪x 5 - x 1, u05 x⟫ < 0 := max_lt h40 h50
    have h4M : ⟪x 4 - x 1, u05 x⟫ ≤ max ⟪x 4 - x 1, u05 x⟫ ⟪x 5 - x 1, u05 x⟫ := le_max_left _ _
    have h5M : ⟪x 5 - x 1, u05 x⟫ ≤ max ⟪x 4 - x 1, u05 x⟫ ⟪x 5 - x 1, u05 x⟫ := le_max_right _ _
    nlinarith [mul_pos (sub_pos.mpr h1st) (neg_pos.mpr hM), mul_pos (sub_pos.mpr h1st) hz0]
  have hfac := u05_facings F hC ha5 hsig
  have hn2 : 0 < ⟪F.N 2, x 0 - x 1⟫ := by
    rw [← F.hN 2 (x 0) (x 1), F.zero 2 0 (by decide), zero_sub]
    linarith [F.neg 2 1 (by decide)]
  have hn3 : 0 < ⟪F.N 3, x 0 - x 1⟫ := by
    rw [← F.hN 3 (x 0) (x 1), F.zero 3 0 (by decide), zero_sub]
    linarith [F.neg 3 1 (by decide)]
  have hcyc : S0xCycUD s0x_S24 c05Pos ({0, 1, 2, 3, 4} : Finset (Fin 9))
      ({5, 6, 7, 8} : Finset (Fin 9)) := by
    unfold S0xCycUD; decide
  have hU : ∀ t ∈ ({0, 1, 2, 3, 4} : Finset (Fin 9)),
      LexPos3 ⟪F.N t, u05 x⟫ ⟪F.N t, x 0 - x 1⟫ ⟪F.N t, (0 : ℝ³)⟫ := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl hfac.1
    · exact Or.inl hfac.2.1
    · exact Or.inr ⟨hfac.2.2.2.2.2.2.2.1, Or.inl hn2⟩
    · exact Or.inr ⟨hfac.2.2.2.2.2.2.2.2, Or.inl hn3⟩
    · exact Or.inl hfac.2.2.1
  have hD : ∀ t ∈ ({5, 6, 7, 8} : Finset (Fin 9)),
      LexPos3 (-⟪F.N t, u05 x⟫) (-⟪F.N t, x 0 - x 1⟫) (-⟪F.N t, (0 : ℝ³)⟫) := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact Or.inl (by linarith [hfac.2.2.2.1])
    · exact Or.inl (by linarith [hfac.2.2.2.2.1])
    · exact Or.inl (by linarith [hfac.2.2.2.2.2.1])
    · exact Or.inl (by linarith [hfac.2.2.2.2.2.2.1])
  have wshift : ∀ v : Fin 7, ⟪x v, u05 x⟫ = ⟪x 1, u05 x⟫ + ⟪x v - x 1, u05 x⟫ := fun v => by
    rw [inner_sub_left]; ring
  have cl : ∀ (i j k l : Fin 7),
      (⟪x i, u05 x⟫ < ⟪x k, u05 x⟫ ∨ ⟪x i, u05 x⟫ < ⟪x l, u05 x⟫ ∨
        ⟪x j, u05 x⟫ < ⟪x k, u05 x⟫ ∨ ⟪x j, u05 x⟫ < ⟪x l, u05 x⟫) →
      Minimality.GenQuad.LexClause (x k) (x l) (x i) (x j) (u05 x) (x 0 - x 1) 0 := by
    intro i j k l h
    apply Minimality.GenQuad.lexClause_of_notM
    rintro ⟨h1, h2, h3, h4'⟩
    rcases h with h | h | h | h <;> linarith
  have hz1 : ⟪x 1 - x 1, u05 x⟫ = 0 := by simp
  have cl' : ∀ (i j k l : Fin 7),
      (⟪x i - x 1, u05 x⟫ < ⟪x k - x 1, u05 x⟫ ∨ ⟪x i - x 1, u05 x⟫ < ⟪x l - x 1, u05 x⟫ ∨
        ⟪x j - x 1, u05 x⟫ < ⟪x k - x 1, u05 x⟫ ∨ ⟪x j - x 1, u05 x⟫ < ⟪x l - x 1, u05 x⟫) →
      Minimality.GenQuad.LexClause (x k) (x l) (x i) (x j) (u05 x) (x 0 - x 1) 0 := by
    intro i j k l h
    apply cl
    rcases h with h | h | h | h
    · left; linarith [wshift i, wshift k]
    · right; left; linarith [wshift i, wshift l]
    · right; right; left; linarith [wshift j, wshift k]
    · right; right; right; linarith [wshift j, wshift l]
  refine Minimality.GenQuad.lexAny_of_clauses F (k := 6) (by norm_num) c05Pos_inj hcyc
    (u05 x) (x 0 - x 1) 0 hU hD ?_
  have hz3_lt : ⟪x 3 - x 1, u05 x⟫ < ⟪x 4 - x 1, u05 x⟫ ∨
      ⟪x 3 - x 1, u05 x⟫ < ⟪x 5 - x 1, u05 x⟫ := lt_max_iff.mp hz345
  refine Minimality.GenQuad.clauses_six (p := fun i => x (c05Pos i))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
  · simp only [c05Pos, Matrix.cons_val]
    first
      | exact cl' _ _ _ _ (by first
          | (left; linarith [hz1, h40, h46, h50, h52])
          | (right; left; linarith [hz1, h40, h46, h50, h52])
          | (right; right; left; linarith [hz1, h40, h46, h50, h52])
          | (right; right; right; linarith [hz1, h40, h46, h50, h52]))
      | (rcases hz3_lt with h3 | h3 <;> rcases hz2_or_z6 with hz | hz <;>
          exact cl' _ _ _ _ (by first
            | (left; linarith [hz1, h40, h46, h50, h52, h3, hz])
            | (right; left; linarith [hz1, h40, h46, h50, h52, h3, hz])
            | (right; right; left; linarith [hz1, h40, h46, h50, h52, h3, hz])
            | (right; right; right; linarith [hz1, h40, h46, h50, h52, h3, hz])))

/-- **L2 contrapositive (`C46 ∨ C40 ∨ C52 ∨ C50`)**: if `¬ LexAny F`, at least one of
`z6(u05) ≤ z4(u05)`, `0 ≤ z4(u05)`, `z2(u05) ≤ z5(u05)`, `0 ≤ z5(u05)` holds. -/
theorem u05_collapse_contrapos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (ha5 : oblX0 x 5 < 1) (hsig : F.f 8 (x 0) < F.f 8 (x 5))
    (hab : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0) (hac : ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0)
    (hL : ¬ Minimality.Gen.LexAny F) :
    ⟪x 6 - x 1, u05 x⟫ ≤ ⟪x 4 - x 1, u05 x⟫ ∨ 0 ≤ ⟪x 4 - x 1, u05 x⟫ ∨
    ⟪x 2 - x 1, u05 x⟫ ≤ ⟪x 5 - x 1, u05 x⟫ ∨ 0 ≤ ⟪x 5 - x 1, u05 x⟫ := by
  by_contra hc
  push Not at hc
  exact hL (u05_collapse F hC ha5 hsig hab hac (lt_min hc.2.1 hc.1) (lt_min hc.2.2.2 hc.2.2.1))

/-- **L2 Gram identity for `C46`**: `z4(u05) - z6(u05)` in `(A, B, C, al, be, ga)`. -/
theorem C46_eq (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) :
    ⟪x 4 - x 1, u05 x⟫ - ⟪x 6 - x 1, u05 x⟫ =
      oblX0 x 4 * (1 - oblX0 x 5) * ⟪x 0 - x 1, x 0 - x 1⟫ -
      oblX2 x 4 * oblX2 x 5 * ⟪x 2 - x 1, x 2 - x 1⟫ -
      (oblX6 x 4 - 1) * oblX6 x 5 * ⟪x 6 - x 1, x 6 - x 1⟫ +
      (oblX0 x 4 * oblX2 x 5 - oblX2 x 4 * (1 - oblX0 x 5)) * (-⟪x 0 - x 1, x 2 - x 1⟫) +
      (oblX0 x 4 * oblX6 x 5 - (oblX6 x 4 - 1) * (1 - oblX0 x 5)) * (-⟪x 0 - x 1, x 6 - x 1⟫) +
      (oblX2 x 4 * oblX6 x 5 + (oblX6 x 4 - 1) * oblX2 x 5) * (-⟪x 2 - x 1, x 6 - x 1⟫) := by
  have T := type24OfFac F
  have h4 := T.rep 4
  rw [show x 4 - x 1 = oblX0 x 4 • (x 0 - x 1) + oblX2 x 4 • (x 2 - x 1) +
      oblX6 x 4 • (x 6 - x 1) by rw [h4]; abel, u05_rep F]
  set e0 := x 0 - x 1
  set e2 := x 2 - x 1
  set e6 := x 6 - x 1
  simp only [inner_add_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm e2 e0, real_inner_comm e6 e0, real_inner_comm e6 e2]
  ring

/-- **L2 Gram identity for `C40`**: `z4(u05)` in `(A, B, C, al, be, ga)`. -/
theorem C40_eq (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) :
    ⟪x 4 - x 1, u05 x⟫ =
      oblX0 x 4 * (1 - oblX0 x 5) * ⟪x 0 - x 1, x 0 - x 1⟫ -
      oblX2 x 4 * oblX2 x 5 * ⟪x 2 - x 1, x 2 - x 1⟫ -
      oblX6 x 4 * oblX6 x 5 * ⟪x 6 - x 1, x 6 - x 1⟫ +
      (oblX0 x 4 * oblX2 x 5 - oblX2 x 4 * (1 - oblX0 x 5)) * (-⟪x 0 - x 1, x 2 - x 1⟫) +
      (oblX0 x 4 * oblX6 x 5 - oblX6 x 4 * (1 - oblX0 x 5)) * (-⟪x 0 - x 1, x 6 - x 1⟫) +
      (oblX2 x 4 * oblX6 x 5 + oblX6 x 4 * oblX2 x 5) * (-⟪x 2 - x 1, x 6 - x 1⟫) := by
  have T := type24OfFac F
  have h4 := T.rep 4
  rw [show x 4 - x 1 = oblX0 x 4 • (x 0 - x 1) + oblX2 x 4 • (x 2 - x 1) +
      oblX6 x 4 • (x 6 - x 1) by rw [h4]; abel, u05_rep F]
  set e0 := x 0 - x 1
  set e2 := x 2 - x 1
  set e6 := x 6 - x 1
  simp only [inner_add_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm e2 e0, real_inner_comm e6 e0, real_inner_comm e6 e2]
  ring

/-- **L2 Gram identity for `C52`**: `z5(u05) - z2(u05)` in `(A, B, C, al, be, ga)`. -/
theorem C52_eq (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) :
    ⟪x 5 - x 1, u05 x⟫ - ⟪x 2 - x 1, u05 x⟫ =
      oblX0 x 5 * (1 - oblX0 x 5) * ⟪x 0 - x 1, x 0 - x 1⟫ -
      oblX2 x 5 * (oblX2 x 5 - 1) * ⟪x 2 - x 1, x 2 - x 1⟫ -
      oblX6 x 5 ^ 2 * ⟪x 6 - x 1, x 6 - x 1⟫ +
      (oblX0 x 5 * oblX2 x 5 - (oblX2 x 5 - 1) * (1 - oblX0 x 5)) * (-⟪x 0 - x 1, x 2 - x 1⟫) +
      (oblX0 x 5 - (1 - oblX0 x 5)) * oblX6 x 5 * (-⟪x 0 - x 1, x 6 - x 1⟫) +
      (2 * oblX2 x 5 - 1) * oblX6 x 5 * (-⟪x 2 - x 1, x 6 - x 1⟫) := by
  have T := type24OfFac F
  have h5 := T.rep 5
  rw [show x 5 - x 1 = oblX0 x 5 • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) +
      oblX6 x 5 • (x 6 - x 1) by rw [h5]; abel, u05_rep F]
  set e0 := x 0 - x 1
  set e2 := x 2 - x 1
  set e6 := x 6 - x 1
  simp only [inner_add_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm e2 e0, real_inner_comm e6 e0, real_inner_comm e6 e2]
  ring

/-- **L2 Gram identity for `C50`**: `z5(u05)` in `(A, B, C, al, be, ga)`. -/
theorem C50_eq (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) :
    ⟪x 5 - x 1, u05 x⟫ =
      oblX0 x 5 * (1 - oblX0 x 5) * ⟪x 0 - x 1, x 0 - x 1⟫ -
      oblX2 x 5 ^ 2 * ⟪x 2 - x 1, x 2 - x 1⟫ -
      oblX6 x 5 ^ 2 * ⟪x 6 - x 1, x 6 - x 1⟫ +
      (oblX0 x 5 - (1 - oblX0 x 5)) * oblX2 x 5 * (-⟪x 0 - x 1, x 2 - x 1⟫) +
      (oblX0 x 5 - (1 - oblX0 x 5)) * oblX6 x 5 * (-⟪x 0 - x 1, x 6 - x 1⟫) +
      2 * oblX2 x 5 * oblX6 x 5 * (-⟪x 2 - x 1, x 6 - x 1⟫) := by
  have T := type24OfFac F
  have h5 := T.rep 5
  rw [show x 5 - x 1 = oblX0 x 5 • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) +
      oblX6 x 5 • (x 6 - x 1) by rw [h5]; abel, u05_rep F]
  set e0 := x 0 - x 1
  set e2 := x 2 - x 1
  set e6 := x 6 - x 1
  simp only [inner_add_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm e2 e0, real_inner_comm e6 e0, real_inner_comm e6 e2]
  ring

/-! ### L3: Rise formulas and `SplitRows` equivalences on `(1, 2, 5, 3, 4, 6)` -/

private theorem det3_frame_edge {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (v w : Fin 7) :
    Split.det3 (x v - x w) (x 2 - x 1) (u05 x) =
      -det24 x * ((1 - oblX0 x 5) * (oblX6 x v - oblX6 x w) +
        oblX6 x 5 * (oblX0 x v - oblX0 x w)) := by
  have T := type24OfFac F
  have hv : x v - x w = (oblX0 x v - oblX0 x w) • (x 0 - x 1) +
      (oblX2 x v - oblX2 x w) • (x 2 - x 1) + (oblX6 x v - oblX6 x w) • (x 6 - x 1) := by
    rw [show x v - x w = (x v - x 1) - (x w - x 1) by abel, T.rep v, T.rep w]; module
  rw [hv, u05_rep F]
  simp only [Split.det3, det24, vol3, H21.inner3, Split.cross_0, Split.cross_1,
    Split.cross_2, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  ring

private theorem det3_frame_edge61 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (v w : Fin 7) :
    Split.det3 (x v - x w) (x 1 - x 6) (u05 x) =
      -det24 x * ((1 - oblX0 x 5) * (oblX2 x v - oblX2 x w) +
        oblX2 x 5 * (oblX0 x v - oblX0 x w)) := by
  have T := type24OfFac F
  have hv : x v - x w = (oblX0 x v - oblX0 x w) • (x 0 - x 1) +
      (oblX2 x v - oblX2 x w) • (x 2 - x 1) + (oblX6 x v - oblX6 x w) • (x 6 - x 1) := by
    rw [show x v - x w = (x v - x 1) - (x w - x 1) by abel, T.rep v, T.rep w]; module
  rw [hv, u05_rep F]
  simp only [Split.det3, det24, vol3, H21.inner3, Split.cross_0, Split.cross_1,
    Split.cross_2, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- **L3 rise formulas for `e12`** (`a = 0`, edge `1 → 2`) along `c05Pos = ![1, 2, 5, 3, 4, 6]`
at `u05 x`. -/
theorem u05_rises_e12 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {σ τ : ℝ}
    (hdec : x 3 - x 0 = σ • (x 4 - x 0) + τ • (x 5 - x 0)) :
    Split.det3 (x 5 - x 2) (x 2 - x 1) (u05 x) = -det24 x * oblX6 x 5 ∧
    Split.det3 (x 3 - x 5) (x 2 - x 1) (u05 x) = -det24 x * (σ * nB x) ∧
    Split.det3 (x 4 - x 3) (x 2 - x 1) (u05 x) = -det24 x * ((1 - σ) * nB x) ∧
    Split.det3 (x 6 - x 4) (x 2 - x 1) (u05 x) =
      det24 x * (oblX6 x 5 * oblX0 x 4 + (1 - oblX0 x 5) * (oblX6 x 4 - 1)) ∧
    Split.det3 (x 1 - x 6) (x 2 - x 1) (u05 x) = det24 x * (1 - oblX0 x 5) := by
  have T := type24OfFac F
  have h31 : x 3 - x 1 =
      (1 - σ - τ) • (x 0 - x 1) + σ • (x 4 - x 1) + τ • (x 5 - x 1) := by
    have : x 3 - x 1 = (x 3 - x 0) + (x 0 - x 1) := by abel
    rw [this, hdec]; module
  have hlin := congrArg (fun v => vol3 v (x 2 - x 1) (x 6 - x 1)) h31
  have ha3 : oblX0 x 3 = (1 - σ - τ) + σ * oblX0 x 4 + τ * oblX0 x 5 := by
    have h0' : vol3 (x 3 - x 1) (x 2 - x 1) (x 6 - x 1) =
        (1 - σ - τ) * det24 x + σ * vol3 (x 4 - x 1) (x 2 - x 1) (x 6 - x 1) +
        τ * vol3 (x 5 - x 1) (x 2 - x 1) (x 6 - x 1) := by
      rw [hlin]; simp only [vol3, det24, Split.inner3, Split.cross_0, Split.cross_1, Split.cross_2,
        PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    simp only [oblX0]
    rw [h0']; field_simp [T.det_ne]
  have hc3 : oblX6 x 3 = σ * oblX6 x 4 + τ * oblX6 x 5 := by
    have hlin6 := congrArg (fun v => vol3 (x 0 - x 1) (x 2 - x 1) v) h31
    have h6' : vol3 (x 0 - x 1) (x 2 - x 1) (x 3 - x 1) =
        σ * vol3 (x 0 - x 1) (x 2 - x 1) (x 4 - x 1) +
        τ * vol3 (x 0 - x 1) (x 2 - x 1) (x 5 - x 1) := by
      rw [hlin6]; simp only [vol3, Split.inner3, Split.cross_0, Split.cross_1, Split.cross_2,
        PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    simp only [oblX6]
    rw [h6']; field_simp [T.det_ne]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [det3_frame_edge F 5 2, Type24.oblX0_two, Type24.oblX6_two]; ring
  · rw [det3_frame_edge F 3 5, ha3, hc3]; dsimp [nB]; ring
  · rw [det3_frame_edge F 4 3, ha3, hc3]; dsimp [nB]; ring
  · rw [det3_frame_edge F 6 4, Type24.oblX0_six, T.oblX6_six]; ring
  · rw [det3_frame_edge F 1 6, Type24.oblX0_one, Type24.oblX6_one, Type24.oblX0_six, T.oblX6_six]; ring

/-- **L3 rise formulas for `e61`** (`a = 5`, edge `6 → 1`) along `c05Pos = ![1, 2, 5, 3, 4, 6]`
at `u05 x`. -/
theorem u05_rises_e61 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {σ τ : ℝ}
    (hdec : x 3 - x 0 = σ • (x 4 - x 0) + τ • (x 5 - x 0)) :
    Split.det3 (x 2 - x 1) (x 1 - x 6) (u05 x) = -det24 x * (1 - oblX0 x 5) ∧
    Split.det3 (x 5 - x 2) (x 1 - x 6) (u05 x) = -det24 x * (oblX6 x 5 * omega5 x) ∧
    Split.det3 (x 3 - x 5) (x 1 - x 6) (u05 x) = -det24 x * (-σ * nC x) ∧
    Split.det3 (x 4 - x 3) (x 1 - x 6) (u05 x) = -det24 x * (-(1 - σ) * nC x) ∧
    Split.det3 (x 6 - x 4) (x 1 - x 6) (u05 x) =
      det24 x * (oblX2 x 5 * oblX0 x 4 + (1 - oblX0 x 5) * oblX2 x 4) := by
  have T := type24OfFac F
  have h31 : x 3 - x 1 =
      (1 - σ - τ) • (x 0 - x 1) + σ • (x 4 - x 1) + τ • (x 5 - x 1) := by
    have : x 3 - x 1 = (x 3 - x 0) + (x 0 - x 1) := by abel
    rw [this, hdec]; module
  have ha3 : oblX0 x 3 = (1 - σ - τ) + σ * oblX0 x 4 + τ * oblX0 x 5 := by
    have hlin := congrArg (fun v => vol3 v (x 2 - x 1) (x 6 - x 1)) h31
    have h0' : vol3 (x 3 - x 1) (x 2 - x 1) (x 6 - x 1) =
        (1 - σ - τ) * det24 x + σ * vol3 (x 4 - x 1) (x 2 - x 1) (x 6 - x 1) +
        τ * vol3 (x 5 - x 1) (x 2 - x 1) (x 6 - x 1) := by
      rw [hlin]; simp only [vol3, det24, Split.inner3, Split.cross_0, Split.cross_1, Split.cross_2,
        PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    simp only [oblX0]
    rw [h0']; field_simp [T.det_ne]
  have hb3 : oblX2 x 3 = σ * oblX2 x 4 + τ * oblX2 x 5 := by
    have hlin2 := congrArg (fun v => vol3 (x 0 - x 1) v (x 6 - x 1)) h31
    have h2' : vol3 (x 0 - x 1) (x 3 - x 1) (x 6 - x 1) =
        σ * vol3 (x 0 - x 1) (x 4 - x 1) (x 6 - x 1) +
        τ * vol3 (x 0 - x 1) (x 5 - x 1) (x 6 - x 1) := by
      rw [hlin2]; simp only [vol3, Split.inner3, Split.cross_0, Split.cross_1, Split.cross_2,
        PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    simp only [oblX2]
    rw [h2']; field_simp [T.det_ne]
  have h5e : oblX0 x 5 + oblX2 x 5 - 1 = omega5 x * oblX6 x 5 := by linarith [eq5 F]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [det3_frame_edge61 F 2 1, Type24.oblX0_two, T.oblX2_two, Type24.oblX0_one, Type24.oblX2_one]; ring
  · rw [det3_frame_edge61 F 5 2, Type24.oblX0_two, T.oblX2_two]
    linear_combination -det24 x * h5e
  · rw [det3_frame_edge61 F 3 5, ha3, hb3]; dsimp [nC]; ring
  · rw [det3_frame_edge61 F 4 3, ha3, hb3]; dsimp [nC]; ring
  · rw [det3_frame_edge61 F 6 4, Type24.oblX0_six, Type24.oblX2_six]; ring

/-- **L3 `SplitRows` equivalence for `p4/e12` (`nB > 0`)**. -/
theorem u05_split_p4_e12 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha5 : oblX0 x 5 < 1) (hc4 : 1 ≤ oblX6 x 4) (hnB : 0 < nB x)
    {σ τ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hdec : x 3 - x 0 = σ • (x 4 - x 0) + τ • (x 5 - x 0)) :
    (SplitRows (fun i => x (c05Pos i)) (u05 x) 0 4 (det24 x) ∨
     SplitRows (fun i => x (c05Pos i)) (u05 x) 0 4 (-det24 x)) ↔
    ((max 0 ⟪x 6 - x 1, u05 x⟫ < ⟪x 4 - x 1, u05 x⟫ ∧
      ⟪x 4 - x 1, u05 x⟫ < min ⟪x 2 - x 1, u05 x⟫ (min ⟪x 5 - x 1, u05 x⟫ ⟪x 3 - x 1, u05 x⟫)) ∨
     (max ⟪x 2 - x 1, u05 x⟫ (max ⟪x 5 - x 1, u05 x⟫ ⟪x 3 - x 1, u05 x⟫) < ⟪x 4 - x 1, u05 x⟫ ∧
      ⟪x 4 - x 1, u05 x⟫ < min 0 ⟪x 6 - x 1, u05 x⟫)) := by
  have T := type24OfFac F
  have ha4 : 0 < oblX0 x 4 := T.X0_pos (v := 4) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hd5 : 0 < 1 - oblX0 x 5 := sub_pos.mpr ha5
  have hr := u05_rises_e12 F hdec
  have hd2 : 0 < det24 x * det24 x := mul_self_pos.mpr T.det_ne
  have hs1 : 0 < oblX6 x 5 := hc5
  have hs2 : 0 < σ * nB x := mul_pos hσ0 hnB
  have hs3 : 0 < (1 - σ) * nB x := mul_pos (sub_pos.mpr hσ1) hnB
  have hs4 : 0 < oblX6 x 5 * oblX0 x 4 + (1 - oblX0 x 5) * (oblX6 x 4 - 1) := by nlinarith
  have hs5 : 0 < 1 - oblX0 x 5 := hd5
  have h14 : ⟪x 1 - x 4, u05 x⟫ = -⟪x 4 - x 1, u05 x⟫ := by
    rw [show x 1 - x 4 = -(x 4 - x 1) by abel, inner_neg_left]
  have hdiff : ∀ v : Fin 7, ⟪x v - x 4, u05 x⟫ = ⟪x v - x 1, u05 x⟫ - ⟪x 4 - x 1, u05 x⟫ := by
    intro v; rw [show x v - x 4 = (x v - x 1) - (x 4 - x 1) by abel, inner_sub_left]
  have hpos_iff : SplitRows (fun i => x (c05Pos i)) (u05 x) 0 4 (-det24 x) ↔
      (max 0 ⟪x 6 - x 1, u05 x⟫ < ⟪x 4 - x 1, u05 x⟫ ∧
       ⟪x 4 - x 1, u05 x⟫ < min ⟪x 2 - x 1, u05 x⟫ (min ⟪x 5 - x 1, u05 x⟫ ⟪x 3 - x 1, u05 x⟫)) := by
    constructor
    · intro h
      have h12 := h 1 1 (by decide) (Or.inl rfl) (by decide)
      have h15 := h 1 2 (by decide) (Or.inr rfl) (by decide)
      have h23 := h 2 3 (by decide) (Or.inr rfl) (by decide)
      have h46 := h 4 5 (by decide) (Or.inr rfl) (by decide)
      have h51 := h 5 0 (by decide) (Or.inr rfl) (by decide)
      try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
      simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide,
        show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide,
        show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide,
        show (5 + 1 : ZMod 6) = 0 by decide] at h12 h15 h23 h46 h51
      rw [hr.1] at h12 h15
      rw [hr.2.1] at h23
      rw [hr.2.2.2.1] at h46
      rw [hr.2.2.2.2] at h51
      rw [hdiff 2] at h12; rw [hdiff 5] at h15; rw [hdiff 3] at h23; rw [hdiff 6] at h46
      rw [h14] at h51
      have k2 : 0 < ⟪x 2 - x 1, u05 x⟫ - ⟪x 4 - x 1, u05 x⟫ :=
        pos_of_mul_pos_left (by linear_combination h12) (mul_pos hd2 hs1).le
      have k5 : 0 < ⟪x 5 - x 1, u05 x⟫ - ⟪x 4 - x 1, u05 x⟫ :=
        pos_of_mul_pos_left (by linear_combination h15) (mul_pos hd2 hs1).le
      have k3 : 0 < ⟪x 3 - x 1, u05 x⟫ - ⟪x 4 - x 1, u05 x⟫ :=
        pos_of_mul_pos_left (by linear_combination h23) (mul_pos hd2 hs2).le
      have k6 : 0 < -(⟪x 6 - x 1, u05 x⟫ - ⟪x 4 - x 1, u05 x⟫) :=
        pos_of_mul_pos_left (by linear_combination h46) (mul_pos hd2 hs4).le
      have k1 : 0 < ⟪x 4 - x 1, u05 x⟫ :=
        pos_of_mul_pos_left (by linear_combination h51) (mul_pos hd2 hs5).le
      exact ⟨max_lt k1 (by linarith), lt_min (by linarith) (lt_min (by linarith) (by linarith))⟩
    · rintro ⟨hlo, hhi⟩ i j hi hj hjc
      have h1 : 0 < ⟪x 4 - x 1, u05 x⟫ := lt_of_le_of_lt (le_max_left _ _) hlo
      have h6 : ⟪x 6 - x 1, u05 x⟫ < ⟪x 4 - x 1, u05 x⟫ := lt_of_le_of_lt (le_max_right _ _) hlo
      have h2 : ⟪x 4 - x 1, u05 x⟫ < ⟪x 2 - x 1, u05 x⟫ := lt_of_lt_of_le hhi (min_le_left _ _)
      have h5 : ⟪x 4 - x 1, u05 x⟫ < ⟪x 5 - x 1, u05 x⟫ :=
        lt_of_lt_of_le hhi (le_trans (min_le_right _ _) (min_le_left _ _))
      have h3 : ⟪x 4 - x 1, u05 x⟫ < ⟪x 3 - x 1, u05 x⟫ :=
        lt_of_lt_of_le hhi (le_trans (min_le_right _ _) (min_le_right _ _))
      have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
        fin_cases i <;> first
          | exact Or.inl rfl | exact Or.inr (Or.inl rfl)
          | exact Or.inr (Or.inr (Or.inl rfl)) | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
          | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
          | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd rfl hi
      · rcases hj with rfl | rfl
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide]
          rw [hr.1, hdiff 2]
          calc 0 < (det24 x * det24 x) * ((⟪x 2 - x 1, u05 x⟫ - ⟪x 4 - x 1, u05 x⟫) * oblX6 x 5) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h2) hs1)
            _ = _ := by ring
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide]
          rw [hr.1, hdiff 5]
          calc 0 < (det24 x * det24 x) * ((⟪x 5 - x 1, u05 x⟫ - ⟪x 4 - x 1, u05 x⟫) * oblX6 x 5) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h5) hs1)
            _ = _ := by ring
      · rcases hj with rfl | rfl
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (2 + 1 : ZMod 6) = 3 by decide]
          rw [hr.2.1, hdiff 5]
          calc 0 < (det24 x * det24 x) * ((⟪x 5 - x 1, u05 x⟫ - ⟪x 4 - x 1, u05 x⟫) * (σ * nB x)) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h5) hs2)
            _ = _ := by ring
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (2 + 1 : ZMod 6) = 3 by decide]
          rw [hr.2.1, hdiff 3]
          calc 0 < (det24 x * det24 x) * ((⟪x 3 - x 1, u05 x⟫ - ⟪x 4 - x 1, u05 x⟫) * (σ * nB x)) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h3) hs2)
            _ = _ := by ring
      · rcases hj with rfl | rfl
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (3 + 1 : ZMod 6) = 4 by decide]
          rw [hr.2.2.1, hdiff 3]
          calc 0 < (det24 x * det24 x) * ((⟪x 3 - x 1, u05 x⟫ - ⟪x 4 - x 1, u05 x⟫) * ((1 - σ) * nB x)) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h3) hs3)
            _ = _ := by ring
        · exact absurd (by decide : (3 + 1 : ZMod 6) = 4) hjc
      · rcases hj with rfl | rfl
        · exact absurd rfl hjc
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (4 + 1 : ZMod 6) = 5 by decide]
          rw [hr.2.2.2.1, hdiff 6]
          calc 0 < (det24 x * det24 x) * ((⟪x 4 - x 1, u05 x⟫ - ⟪x 6 - x 1, u05 x⟫) *
                (oblX6 x 5 * oblX0 x 4 + (1 - oblX0 x 5) * (oblX6 x 4 - 1))) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h6) hs4)
            _ = _ := by ring
      · rcases hj with rfl | rfl
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.2.2.2.2, hdiff 6]
          calc 0 < (det24 x * det24 x) * ((⟪x 4 - x 1, u05 x⟫ - ⟪x 6 - x 1, u05 x⟫) * (1 - oblX0 x 5)) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h6) hs5)
            _ = _ := by ring
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.2.2.2.2, h14]
          calc 0 < (det24 x * det24 x) * (⟪x 4 - x 1, u05 x⟫ * (1 - oblX0 x 5)) :=
                mul_pos hd2 (mul_pos h1 hs5)
            _ = _ := by ring
  have hneg_iff : SplitRows (fun i => x (c05Pos i)) (u05 x) 0 4 (det24 x) ↔
      (max ⟪x 2 - x 1, u05 x⟫ (max ⟪x 5 - x 1, u05 x⟫ ⟪x 3 - x 1, u05 x⟫) < ⟪x 4 - x 1, u05 x⟫ ∧
       ⟪x 4 - x 1, u05 x⟫ < min 0 ⟪x 6 - x 1, u05 x⟫) := by
    constructor
    · intro h
      have h12 := h 1 1 (by decide) (Or.inl rfl) (by decide)
      have h15 := h 1 2 (by decide) (Or.inr rfl) (by decide)
      have h23 := h 2 3 (by decide) (Or.inr rfl) (by decide)
      have h46 := h 4 5 (by decide) (Or.inr rfl) (by decide)
      have h51 := h 5 0 (by decide) (Or.inr rfl) (by decide)
      try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
      simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide,
        show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide,
        show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at h12 h15 h23 h46 h51
      rw [hr.1] at h12 h15; rw [hr.2.1] at h23; rw [hr.2.2.2.1] at h46; rw [hr.2.2.2.2] at h51
      rw [hdiff 2] at h12; rw [hdiff 5] at h15; rw [hdiff 3] at h23; rw [hdiff 6] at h46
      rw [h14] at h51
      have k2 : 0 < -(⟪x 2 - x 1, u05 x⟫ - ⟪x 4 - x 1, u05 x⟫) :=
        pos_of_mul_pos_left (by linear_combination h12) (mul_pos hd2 hs1).le
      have k5 : 0 < -(⟪x 5 - x 1, u05 x⟫ - ⟪x 4 - x 1, u05 x⟫) :=
        pos_of_mul_pos_left (by linear_combination h15) (mul_pos hd2 hs1).le
      have k3 : 0 < -(⟪x 3 - x 1, u05 x⟫ - ⟪x 4 - x 1, u05 x⟫) :=
        pos_of_mul_pos_left (by linear_combination h23) (mul_pos hd2 hs2).le
      have k6 : 0 < ⟪x 6 - x 1, u05 x⟫ - ⟪x 4 - x 1, u05 x⟫ :=
        pos_of_mul_pos_left (by linear_combination h46) (mul_pos hd2 hs4).le
      have k1 : 0 < -⟪x 4 - x 1, u05 x⟫ :=
        pos_of_mul_pos_left (by linear_combination h51) (mul_pos hd2 hs5).le
      exact ⟨max_lt (by linarith) (max_lt (by linarith) (by linarith)), lt_min (by linarith) (by linarith)⟩
    · rintro ⟨hlo, hhi⟩ i j hi hj hjc
      have h2 : ⟪x 2 - x 1, u05 x⟫ < ⟪x 4 - x 1, u05 x⟫ := lt_of_le_of_lt (le_max_left _ _) hlo
      have h5 : ⟪x 5 - x 1, u05 x⟫ < ⟪x 4 - x 1, u05 x⟫ :=
        lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hlo
      have h3 : ⟪x 3 - x 1, u05 x⟫ < ⟪x 4 - x 1, u05 x⟫ :=
        lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hlo
      have h1 : ⟪x 4 - x 1, u05 x⟫ < 0 := lt_of_lt_of_le hhi (min_le_left _ _)
      have h6 : ⟪x 4 - x 1, u05 x⟫ < ⟪x 6 - x 1, u05 x⟫ := lt_of_lt_of_le hhi (min_le_right _ _)
      have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
        fin_cases i <;> first
          | exact Or.inl rfl | exact Or.inr (Or.inl rfl)
          | exact Or.inr (Or.inr (Or.inl rfl)) | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
          | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
          | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd rfl hi
      · rcases hj with rfl | rfl
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide]
          rw [hr.1, hdiff 2]
          calc 0 < (det24 x * det24 x) * ((⟪x 4 - x 1, u05 x⟫ - ⟪x 2 - x 1, u05 x⟫) * oblX6 x 5) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h2) hs1)
            _ = _ := by ring
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide]
          rw [hr.1, hdiff 5]
          calc 0 < (det24 x * det24 x) * ((⟪x 4 - x 1, u05 x⟫ - ⟪x 5 - x 1, u05 x⟫) * oblX6 x 5) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h5) hs1)
            _ = _ := by ring
      · rcases hj with rfl | rfl
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (2 + 1 : ZMod 6) = 3 by decide]
          rw [hr.2.1, hdiff 5]
          calc 0 < (det24 x * det24 x) * ((⟪x 4 - x 1, u05 x⟫ - ⟪x 5 - x 1, u05 x⟫) * (σ * nB x)) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h5) hs2)
            _ = _ := by ring
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (2 + 1 : ZMod 6) = 3 by decide]
          rw [hr.2.1, hdiff 3]
          calc 0 < (det24 x * det24 x) * ((⟪x 4 - x 1, u05 x⟫ - ⟪x 3 - x 1, u05 x⟫) * (σ * nB x)) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h3) hs2)
            _ = _ := by ring
      · rcases hj with rfl | rfl
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (3 + 1 : ZMod 6) = 4 by decide]
          rw [hr.2.2.1, hdiff 3]
          calc 0 < (det24 x * det24 x) * ((⟪x 4 - x 1, u05 x⟫ - ⟪x 3 - x 1, u05 x⟫) * ((1 - σ) * nB x)) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h3) hs3)
            _ = _ := by ring
        · exact absurd (by decide : (3 + 1 : ZMod 6) = 4) hjc
      · rcases hj with rfl | rfl
        · exact absurd rfl hjc
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (4 + 1 : ZMod 6) = 5 by decide]
          rw [hr.2.2.2.1, hdiff 6]
          calc 0 < (det24 x * det24 x) * ((⟪x 6 - x 1, u05 x⟫ - ⟪x 4 - x 1, u05 x⟫) *
                (oblX6 x 5 * oblX0 x 4 + (1 - oblX0 x 5) * (oblX6 x 4 - 1))) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h6) hs4)
            _ = _ := by ring
      · rcases hj with rfl | rfl
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.2.2.2.2, hdiff 6]
          calc 0 < (det24 x * det24 x) * ((⟪x 6 - x 1, u05 x⟫ - ⟪x 4 - x 1, u05 x⟫) * (1 - oblX0 x 5)) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h6) hs5)
            _ = _ := by ring
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.2.2.2.2, h14]
          calc 0 < (det24 x * det24 x) * ((-⟪x 4 - x 1, u05 x⟫) * (1 - oblX0 x 5)) :=
                mul_pos hd2 (mul_pos (neg_pos.mpr h1) hs5)
            _ = _ := by ring
  exact or_comm.trans (or_congr hpos_iff hneg_iff)

/-- **L3 `SplitRows` equivalence for `p5/e12` (`nB < 0`)**. -/
theorem u05_split_p5_e12 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha5 : oblX0 x 5 < 1) (hc4 : 1 ≤ oblX6 x 4) (hnB : nB x < 0)
    {σ τ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hdec : x 3 - x 0 = σ • (x 4 - x 0) + τ • (x 5 - x 0)) :
    (SplitRows (fun i => x (c05Pos i)) (u05 x) 0 2 (det24 x) ∨
     SplitRows (fun i => x (c05Pos i)) (u05 x) 0 2 (-det24 x)) ↔
    ((max 0 (max ⟪x 3 - x 1, u05 x⟫ (max ⟪x 4 - x 1, u05 x⟫ ⟪x 6 - x 1, u05 x⟫)) <
        ⟪x 5 - x 1, u05 x⟫ ∧ ⟪x 5 - x 1, u05 x⟫ < ⟪x 2 - x 1, u05 x⟫) ∨
     (⟪x 2 - x 1, u05 x⟫ < ⟪x 5 - x 1, u05 x⟫ ∧
        ⟪x 5 - x 1, u05 x⟫ <
          min 0 (min ⟪x 3 - x 1, u05 x⟫ (min ⟪x 4 - x 1, u05 x⟫ ⟪x 6 - x 1, u05 x⟫)))) := by
  have T := type24OfFac F
  have ha4 : 0 < oblX0 x 4 := T.X0_pos (v := 4) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hd5 : 0 < 1 - oblX0 x 5 := sub_pos.mpr ha5
  have hr := u05_rises_e12 F hdec
  have hd2 : 0 < det24 x * det24 x := mul_self_pos.mpr T.det_ne
  have hs1 : 0 < oblX6 x 5 := hc5
  have hs2 : 0 < -(σ * nB x) := by nlinarith
  have hs3 : 0 < -((1 - σ) * nB x) := by nlinarith
  have hs4 : 0 < oblX6 x 5 * oblX0 x 4 + (1 - oblX0 x 5) * (oblX6 x 4 - 1) := by nlinarith
  have hs5 : 0 < 1 - oblX0 x 5 := hd5
  have h15 : ⟪x 1 - x 5, u05 x⟫ = -⟪x 5 - x 1, u05 x⟫ := by
    rw [show x 1 - x 5 = -(x 5 - x 1) by abel, inner_neg_left]
  have hdiff : ∀ v : Fin 7, ⟪x v - x 5, u05 x⟫ = ⟪x v - x 1, u05 x⟫ - ⟪x 5 - x 1, u05 x⟫ := by
    intro v; rw [show x v - x 5 = (x v - x 1) - (x 5 - x 1) by abel, inner_sub_left]
  have hpos_iff : SplitRows (fun i => x (c05Pos i)) (u05 x) 0 2 (-det24 x) ↔
      (max 0 (max ⟪x 3 - x 1, u05 x⟫ (max ⟪x 4 - x 1, u05 x⟫ ⟪x 6 - x 1, u05 x⟫)) <
        ⟪x 5 - x 1, u05 x⟫ ∧ ⟪x 5 - x 1, u05 x⟫ < ⟪x 2 - x 1, u05 x⟫) := by
    constructor
    · intro h
      have h12 := h 1 1 (by decide) (Or.inl rfl) (by decide)
      have h23 := h 2 3 (by decide) (Or.inr rfl) (by decide)
      have h34 := h 3 4 (by decide) (Or.inr rfl) (by decide)
      have h46 := h 4 5 (by decide) (Or.inr rfl) (by decide)
      have h51 := h 5 0 (by decide) (Or.inr rfl) (by decide)
      try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
      simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide,
        show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide,
        show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide,
        show (5 + 1 : ZMod 6) = 0 by decide] at h12 h23 h34 h46 h51
      rw [hr.1] at h12; rw [hr.2.1] at h23; rw [hr.2.2.1] at h34; rw [hr.2.2.2.1] at h46; rw [hr.2.2.2.2] at h51
      rw [hdiff 2] at h12; rw [hdiff 3] at h23; rw [hdiff 4] at h34; rw [hdiff 6] at h46; rw [h15] at h51
      have k2 : 0 < ⟪x 2 - x 1, u05 x⟫ - ⟪x 5 - x 1, u05 x⟫ :=
        pos_of_mul_pos_left (by linear_combination h12) (mul_pos hd2 hs1).le
      have k3 : 0 < -(⟪x 3 - x 1, u05 x⟫ - ⟪x 5 - x 1, u05 x⟫) :=
        pos_of_mul_pos_left (by linear_combination h23) (mul_pos hd2 hs2).le
      have k4 : 0 < -(⟪x 4 - x 1, u05 x⟫ - ⟪x 5 - x 1, u05 x⟫) :=
        pos_of_mul_pos_left (by linear_combination h34) (mul_pos hd2 hs3).le
      have k6 : 0 < -(⟪x 6 - x 1, u05 x⟫ - ⟪x 5 - x 1, u05 x⟫) :=
        pos_of_mul_pos_left (by linear_combination h46) (mul_pos hd2 hs4).le
      have k1 : 0 < ⟪x 5 - x 1, u05 x⟫ :=
        pos_of_mul_pos_left (by linear_combination h51) (mul_pos hd2 hs5).le
      exact ⟨max_lt k1 (max_lt (by linarith) (max_lt (by linarith) (by linarith))), by linarith⟩
    · rintro ⟨hlo, hhi⟩ i j hi hj hjc
      have h1 : 0 < ⟪x 5 - x 1, u05 x⟫ := lt_of_le_of_lt (le_max_left _ _) hlo
      have h3 : ⟪x 3 - x 1, u05 x⟫ < ⟪x 5 - x 1, u05 x⟫ :=
        lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hlo
      have h4 : ⟪x 4 - x 1, u05 x⟫ < ⟪x 5 - x 1, u05 x⟫ :=
        lt_of_le_of_lt (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hlo
      have h6 : ⟪x 6 - x 1, u05 x⟫ < ⟪x 5 - x 1, u05 x⟫ :=
        lt_of_le_of_lt (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hlo
      have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
        fin_cases i <;> first
          | exact Or.inl rfl | exact Or.inr (Or.inl rfl)
          | exact Or.inr (Or.inr (Or.inl rfl)) | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
          | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
          | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd rfl hi
      · rcases hj with rfl | rfl
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide]
          rw [hr.1, hdiff 2]
          calc 0 < (det24 x * det24 x) * ((⟪x 2 - x 1, u05 x⟫ - ⟪x 5 - x 1, u05 x⟫) * oblX6 x 5) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr hhi) hs1)
            _ = _ := by ring
        · exact absurd (by decide : (1 + 1 : ZMod 6) = 2) hjc
      · rcases hj with rfl | rfl
        · exact absurd rfl hjc
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (2 + 1 : ZMod 6) = 3 by decide]
          rw [hr.2.1, hdiff 3]
          calc 0 < (det24 x * det24 x) * ((⟪x 5 - x 1, u05 x⟫ - ⟪x 3 - x 1, u05 x⟫) * (-(σ * nB x))) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h3) hs2)
            _ = _ := by ring
      · rcases hj with rfl | rfl
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (3 + 1 : ZMod 6) = 4 by decide]
          rw [hr.2.2.1, hdiff 3]
          calc 0 < (det24 x * det24 x) * ((⟪x 5 - x 1, u05 x⟫ - ⟪x 3 - x 1, u05 x⟫) * (-((1 - σ) * nB x))) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h3) hs3)
            _ = _ := by ring
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (3 + 1 : ZMod 6) = 4 by decide]
          rw [hr.2.2.1, hdiff 4]
          calc 0 < (det24 x * det24 x) * ((⟪x 5 - x 1, u05 x⟫ - ⟪x 4 - x 1, u05 x⟫) * (-((1 - σ) * nB x))) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h4) hs3)
            _ = _ := by ring
      · rcases hj with rfl | rfl
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (4 + 1 : ZMod 6) = 5 by decide]
          rw [hr.2.2.2.1, hdiff 4]
          calc 0 < (det24 x * det24 x) * ((⟪x 5 - x 1, u05 x⟫ - ⟪x 4 - x 1, u05 x⟫) *
                (oblX6 x 5 * oblX0 x 4 + (1 - oblX0 x 5) * (oblX6 x 4 - 1))) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h4) hs4)
            _ = _ := by ring
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (4 + 1 : ZMod 6) = 5 by decide]
          rw [hr.2.2.2.1, hdiff 6]
          calc 0 < (det24 x * det24 x) * ((⟪x 5 - x 1, u05 x⟫ - ⟪x 6 - x 1, u05 x⟫) *
                (oblX6 x 5 * oblX0 x 4 + (1 - oblX0 x 5) * (oblX6 x 4 - 1))) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h6) hs4)
            _ = _ := by ring
      · rcases hj with rfl | rfl
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.2.2.2.2, hdiff 6]
          calc 0 < (det24 x * det24 x) * ((⟪x 5 - x 1, u05 x⟫ - ⟪x 6 - x 1, u05 x⟫) * (1 - oblX0 x 5)) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h6) hs5)
            _ = _ := by ring
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.2.2.2.2, h15]
          calc 0 < (det24 x * det24 x) * (⟪x 5 - x 1, u05 x⟫ * (1 - oblX0 x 5)) :=
                mul_pos hd2 (mul_pos h1 hs5)
            _ = _ := by ring
  have hneg_iff : SplitRows (fun i => x (c05Pos i)) (u05 x) 0 2 (det24 x) ↔
      (⟪x 2 - x 1, u05 x⟫ < ⟪x 5 - x 1, u05 x⟫ ∧
        ⟪x 5 - x 1, u05 x⟫ <
          min 0 (min ⟪x 3 - x 1, u05 x⟫ (min ⟪x 4 - x 1, u05 x⟫ ⟪x 6 - x 1, u05 x⟫))) := by
    constructor
    · intro h
      have h12 := h 1 1 (by decide) (Or.inl rfl) (by decide)
      have h23 := h 2 3 (by decide) (Or.inr rfl) (by decide)
      have h34 := h 3 4 (by decide) (Or.inr rfl) (by decide)
      have h46 := h 4 5 (by decide) (Or.inr rfl) (by decide)
      have h51 := h 5 0 (by decide) (Or.inr rfl) (by decide)
      try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
      simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide,
        show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide,
        show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide,
        show (5 + 1 : ZMod 6) = 0 by decide] at h12 h23 h34 h46 h51
      rw [hr.1] at h12; rw [hr.2.1] at h23; rw [hr.2.2.1] at h34; rw [hr.2.2.2.1] at h46; rw [hr.2.2.2.2] at h51
      rw [hdiff 2] at h12; rw [hdiff 3] at h23; rw [hdiff 4] at h34; rw [hdiff 6] at h46; rw [h15] at h51
      have k2 : 0 < -(⟪x 2 - x 1, u05 x⟫ - ⟪x 5 - x 1, u05 x⟫) :=
        pos_of_mul_pos_left (by linear_combination h12) (mul_pos hd2 hs1).le
      have k3 : 0 < ⟪x 3 - x 1, u05 x⟫ - ⟪x 5 - x 1, u05 x⟫ :=
        pos_of_mul_pos_left (by linear_combination h23) (mul_pos hd2 hs2).le
      have k4 : 0 < ⟪x 4 - x 1, u05 x⟫ - ⟪x 5 - x 1, u05 x⟫ :=
        pos_of_mul_pos_left (by linear_combination h34) (mul_pos hd2 hs3).le
      have k6 : 0 < ⟪x 6 - x 1, u05 x⟫ - ⟪x 5 - x 1, u05 x⟫ :=
        pos_of_mul_pos_left (by linear_combination h46) (mul_pos hd2 hs4).le
      have k1 : 0 < -⟪x 5 - x 1, u05 x⟫ :=
        pos_of_mul_pos_left (by linear_combination h51) (mul_pos hd2 hs5).le
      exact ⟨by linarith, lt_min (by linarith) (lt_min (by linarith) (lt_min (by linarith) (by linarith)))⟩
    · rintro ⟨hlo, hhi⟩ i j hi hj hjc
      have h1 : ⟪x 5 - x 1, u05 x⟫ < 0 := lt_of_lt_of_le hhi (min_le_left _ _)
      have h3 : ⟪x 5 - x 1, u05 x⟫ < ⟪x 3 - x 1, u05 x⟫ :=
        lt_of_lt_of_le hhi (le_trans (min_le_right _ _) (min_le_left _ _))
      have h4 : ⟪x 5 - x 1, u05 x⟫ < ⟪x 4 - x 1, u05 x⟫ :=
        lt_of_lt_of_le hhi (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
      have h6 : ⟪x 5 - x 1, u05 x⟫ < ⟪x 6 - x 1, u05 x⟫ :=
        lt_of_lt_of_le hhi (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
      have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
        fin_cases i <;> first
          | exact Or.inl rfl | exact Or.inr (Or.inl rfl)
          | exact Or.inr (Or.inr (Or.inl rfl)) | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
          | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
          | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd rfl hi
      · rcases hj with rfl | rfl
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide]
          rw [hr.1, hdiff 2]
          calc 0 < (det24 x * det24 x) * ((⟪x 5 - x 1, u05 x⟫ - ⟪x 2 - x 1, u05 x⟫) * oblX6 x 5) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr hlo) hs1)
            _ = _ := by ring
        · exact absurd (by decide : (1 + 1 : ZMod 6) = 2) hjc
      · rcases hj with rfl | rfl
        · exact absurd rfl hjc
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (2 + 1 : ZMod 6) = 3 by decide]
          rw [hr.2.1, hdiff 3]
          calc 0 < (det24 x * det24 x) * ((⟪x 3 - x 1, u05 x⟫ - ⟪x 5 - x 1, u05 x⟫) * (-(σ * nB x))) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h3) hs2)
            _ = _ := by ring
      · rcases hj with rfl | rfl
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (3 + 1 : ZMod 6) = 4 by decide]
          rw [hr.2.2.1, hdiff 3]
          calc 0 < (det24 x * det24 x) * ((⟪x 3 - x 1, u05 x⟫ - ⟪x 5 - x 1, u05 x⟫) * (-((1 - σ) * nB x))) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h3) hs3)
            _ = _ := by ring
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (3 + 1 : ZMod 6) = 4 by decide]
          rw [hr.2.2.1, hdiff 4]
          calc 0 < (det24 x * det24 x) * ((⟪x 4 - x 1, u05 x⟫ - ⟪x 5 - x 1, u05 x⟫) * (-((1 - σ) * nB x))) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h4) hs3)
            _ = _ := by ring
      · rcases hj with rfl | rfl
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (4 + 1 : ZMod 6) = 5 by decide]
          rw [hr.2.2.2.1, hdiff 4]
          calc 0 < (det24 x * det24 x) * ((⟪x 4 - x 1, u05 x⟫ - ⟪x 5 - x 1, u05 x⟫) *
                (oblX6 x 5 * oblX0 x 4 + (1 - oblX0 x 5) * (oblX6 x 4 - 1))) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h4) hs4)
            _ = _ := by ring
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (4 + 1 : ZMod 6) = 5 by decide]
          rw [hr.2.2.2.1, hdiff 6]
          calc 0 < (det24 x * det24 x) * ((⟪x 6 - x 1, u05 x⟫ - ⟪x 5 - x 1, u05 x⟫) *
                (oblX6 x 5 * oblX0 x 4 + (1 - oblX0 x 5) * (oblX6 x 4 - 1))) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h6) hs4)
            _ = _ := by ring
      · rcases hj with rfl | rfl
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.2.2.2.2, hdiff 6]
          calc 0 < (det24 x * det24 x) * ((⟪x 6 - x 1, u05 x⟫ - ⟪x 5 - x 1, u05 x⟫) * (1 - oblX0 x 5)) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h6) hs5)
            _ = _ := by ring
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.2.2.2.2, h15]
          calc 0 < (det24 x * det24 x) * ((-⟪x 5 - x 1, u05 x⟫) * (1 - oblX0 x 5)) :=
                mul_pos hd2 (mul_pos (neg_pos.mpr h1) hs5)
            _ = _ := by ring
  exact or_comm.trans (or_congr hpos_iff hneg_iff)

/-- **L3 `SplitRows` equivalence for `p4/e61` (`nC < 0`)**. -/
theorem u05_split_p4_e61 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (ha5 : oblX0 x 5 < 1) (hnC : nC x < 0)
    {σ τ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hdec : x 3 - x 0 = σ • (x 4 - x 0) + τ • (x 5 - x 0)) :
    (SplitRows (fun i => x (c05Pos i)) (u05 x) 5 4 (det24 x) ∨
     SplitRows (fun i => x (c05Pos i)) (u05 x) 5 4 (-det24 x)) ↔
    ((⟪x 6 - x 1, u05 x⟫ < ⟪x 4 - x 1, u05 x⟫ ∧
      ⟪x 4 - x 1, u05 x⟫ < min 0 (min ⟪x 2 - x 1, u05 x⟫ (min ⟪x 5 - x 1, u05 x⟫ ⟪x 3 - x 1, u05 x⟫))) ∨
     (max 0 (max ⟪x 2 - x 1, u05 x⟫ (max ⟪x 5 - x 1, u05 x⟫ ⟪x 3 - x 1, u05 x⟫)) < ⟪x 4 - x 1, u05 x⟫ ∧
      ⟪x 4 - x 1, u05 x⟫ < ⟪x 6 - x 1, u05 x⟫)) := by
  have T := type24OfFac F
  have ha4 : 0 < oblX0 x 4 := T.X0_pos (v := 4) (by decide)
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hd5 : 0 < 1 - oblX0 x 5 := sub_pos.mpr ha5
  have hom5 : 0 < omega5 x := hC.2.2.1
  have hr := u05_rises_e61 F hdec
  have hd2 : 0 < det24 x * det24 x := mul_self_pos.mpr T.det_ne
  have hs0 : 0 < 1 - oblX0 x 5 := hd5
  have hs1 : 0 < oblX6 x 5 * omega5 x := mul_pos hc5 hom5
  have hs2 : 0 < -σ * nC x := by nlinarith
  have hs3 : 0 < -(1 - σ) * nC x := by nlinarith
  have hs4 : 0 < oblX2 x 5 * oblX0 x 4 + (1 - oblX0 x 5) * oblX2 x 4 := by nlinarith
  have h14 : ⟪x 1 - x 4, u05 x⟫ = -⟪x 4 - x 1, u05 x⟫ := by
    rw [show x 1 - x 4 = -(x 4 - x 1) by abel, inner_neg_left]
  have hdiff : ∀ v : Fin 7, ⟪x v - x 4, u05 x⟫ = ⟪x v - x 1, u05 x⟫ - ⟪x 4 - x 1, u05 x⟫ := by
    intro v; rw [show x v - x 4 = (x v - x 1) - (x 4 - x 1) by abel, inner_sub_left]
  have hpos_iff : SplitRows (fun i => x (c05Pos i)) (u05 x) 5 4 (-det24 x) ↔
      (⟪x 6 - x 1, u05 x⟫ < ⟪x 4 - x 1, u05 x⟫ ∧
       ⟪x 4 - x 1, u05 x⟫ < min 0 (min ⟪x 2 - x 1, u05 x⟫ (min ⟪x 5 - x 1, u05 x⟫ ⟪x 3 - x 1, u05 x⟫))) := by
    constructor
    · intro h
      have h01 := h 0 0 (by decide) (Or.inl rfl) (by decide)
      have h02 := h 0 1 (by decide) (Or.inr rfl) (by decide)
      have h15 := h 1 2 (by decide) (Or.inr rfl) (by decide)
      have h23 := h 2 3 (by decide) (Or.inr rfl) (by decide)
      have h46 := h 4 5 (by decide) (Or.inr rfl) (by decide)
      try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
      simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide,
        show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide,
        show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide] at h01 h02 h15 h23 h46
      rw [hr.1] at h01 h02; rw [hr.2.1] at h15; rw [hr.2.2.1] at h23; rw [hr.2.2.2.2] at h46
      rw [h14] at h01; rw [hdiff 2] at h02; rw [hdiff 5] at h15; rw [hdiff 3] at h23; rw [hdiff 6] at h46
      have k1 : 0 < -⟪x 4 - x 1, u05 x⟫ :=
        pos_of_mul_pos_left (by linear_combination h01) (mul_pos hd2 hs0).le
      have k2 : 0 < ⟪x 2 - x 1, u05 x⟫ - ⟪x 4 - x 1, u05 x⟫ :=
        pos_of_mul_pos_left (by linear_combination h02) (mul_pos hd2 hs0).le
      have k5 : 0 < ⟪x 5 - x 1, u05 x⟫ - ⟪x 4 - x 1, u05 x⟫ :=
        pos_of_mul_pos_left (by linear_combination h15) (mul_pos hd2 hs1).le
      have k3 : 0 < ⟪x 3 - x 1, u05 x⟫ - ⟪x 4 - x 1, u05 x⟫ :=
        pos_of_mul_pos_left (by linear_combination h23) (mul_pos hd2 hs2).le
      have k6 : 0 < -(⟪x 6 - x 1, u05 x⟫ - ⟪x 4 - x 1, u05 x⟫) :=
        pos_of_mul_pos_left (by linear_combination h46) (mul_pos hd2 hs4).le
      exact ⟨by linarith, lt_min (by linarith) (lt_min (by linarith) (lt_min (by linarith) (by linarith)))⟩
    · rintro ⟨h6, hhi⟩ i j hi hj hjc
      have h1 : ⟪x 4 - x 1, u05 x⟫ < 0 := lt_of_lt_of_le hhi (min_le_left _ _)
      have h2 : ⟪x 4 - x 1, u05 x⟫ < ⟪x 2 - x 1, u05 x⟫ :=
        lt_of_lt_of_le hhi (le_trans (min_le_right _ _) (min_le_left _ _))
      have h5 : ⟪x 4 - x 1, u05 x⟫ < ⟪x 5 - x 1, u05 x⟫ :=
        lt_of_lt_of_le hhi (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
      have h3 : ⟪x 4 - x 1, u05 x⟫ < ⟪x 3 - x 1, u05 x⟫ :=
        lt_of_lt_of_le hhi (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
      have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
        fin_cases i <;> first
          | exact Or.inl rfl | exact Or.inr (Or.inl rfl)
          | exact Or.inr (Or.inr (Or.inl rfl)) | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
          | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
          | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl
      · rcases hj with rfl | rfl
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.1, h14]
          calc 0 < (det24 x * det24 x) * ((-⟪x 4 - x 1, u05 x⟫) * (1 - oblX0 x 5)) :=
                mul_pos hd2 (mul_pos (neg_pos.mpr h1) hs0)
            _ = _ := by ring
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.1, hdiff 2]
          calc 0 < (det24 x * det24 x) * ((⟪x 2 - x 1, u05 x⟫ - ⟪x 4 - x 1, u05 x⟫) * (1 - oblX0 x 5)) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h2) hs0)
            _ = _ := by ring
      · rcases hj with rfl | rfl
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (1 + 1 : ZMod 6) = 2 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.2.1, hdiff 2]
          calc 0 < (det24 x * det24 x) * ((⟪x 2 - x 1, u05 x⟫ - ⟪x 4 - x 1, u05 x⟫) * (oblX6 x 5 * omega5 x)) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h2) hs1)
            _ = _ := by ring
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (1 + 1 : ZMod 6) = 2 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.2.1, hdiff 5]
          calc 0 < (det24 x * det24 x) * ((⟪x 5 - x 1, u05 x⟫ - ⟪x 4 - x 1, u05 x⟫) * (oblX6 x 5 * omega5 x)) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h5) hs1)
            _ = _ := by ring
      · rcases hj with rfl | rfl
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (2 + 1 : ZMod 6) = 3 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.2.2.1, hdiff 5]
          calc 0 < (det24 x * det24 x) * ((⟪x 5 - x 1, u05 x⟫ - ⟪x 4 - x 1, u05 x⟫) * (-σ * nC x)) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h5) hs2)
            _ = _ := by ring
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (2 + 1 : ZMod 6) = 3 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.2.2.1, hdiff 3]
          calc 0 < (det24 x * det24 x) * ((⟪x 3 - x 1, u05 x⟫ - ⟪x 4 - x 1, u05 x⟫) * (-σ * nC x)) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h3) hs2)
            _ = _ := by ring
      · rcases hj with rfl | rfl
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (3 + 1 : ZMod 6) = 4 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.2.2.2.1, hdiff 3]
          calc 0 < (det24 x * det24 x) * ((⟪x 3 - x 1, u05 x⟫ - ⟪x 4 - x 1, u05 x⟫) * (-(1 - σ) * nC x)) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h3) hs3)
            _ = _ := by ring
        · exact absurd (by decide : (3 + 1 : ZMod 6) = 4) hjc
      · rcases hj with rfl | rfl
        · exact absurd rfl hjc
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.2.2.2.2, hdiff 6]
          calc 0 < (det24 x * det24 x) * ((⟪x 4 - x 1, u05 x⟫ - ⟪x 6 - x 1, u05 x⟫) *
                (oblX2 x 5 * oblX0 x 4 + (1 - oblX0 x 5) * oblX2 x 4)) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h6) hs4)
            _ = _ := by ring
      · exact absurd rfl hi
  have hneg_iff : SplitRows (fun i => x (c05Pos i)) (u05 x) 5 4 (det24 x) ↔
      (max 0 (max ⟪x 2 - x 1, u05 x⟫ (max ⟪x 5 - x 1, u05 x⟫ ⟪x 3 - x 1, u05 x⟫)) < ⟪x 4 - x 1, u05 x⟫ ∧
       ⟪x 4 - x 1, u05 x⟫ < ⟪x 6 - x 1, u05 x⟫) := by
    constructor
    · intro h
      have h01 := h 0 0 (by decide) (Or.inl rfl) (by decide)
      have h02 := h 0 1 (by decide) (Or.inr rfl) (by decide)
      have h15 := h 1 2 (by decide) (Or.inr rfl) (by decide)
      have h23 := h 2 3 (by decide) (Or.inr rfl) (by decide)
      have h46 := h 4 5 (by decide) (Or.inr rfl) (by decide)
      try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
      simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide,
        show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide,
        show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at h01 h02 h15 h23 h46
      rw [hr.1] at h01 h02; rw [hr.2.1] at h15; rw [hr.2.2.1] at h23; rw [hr.2.2.2.2] at h46
      rw [h14] at h01; rw [hdiff 2] at h02; rw [hdiff 5] at h15; rw [hdiff 3] at h23; rw [hdiff 6] at h46
      have k1 : 0 < ⟪x 4 - x 1, u05 x⟫ :=
        pos_of_mul_pos_left (by linear_combination h01) (mul_pos hd2 hs0).le
      have k2 : 0 < -(⟪x 2 - x 1, u05 x⟫ - ⟪x 4 - x 1, u05 x⟫) :=
        pos_of_mul_pos_left (by linear_combination h02) (mul_pos hd2 hs0).le
      have k5 : 0 < -(⟪x 5 - x 1, u05 x⟫ - ⟪x 4 - x 1, u05 x⟫) :=
        pos_of_mul_pos_left (by linear_combination h15) (mul_pos hd2 hs1).le
      have k3 : 0 < -(⟪x 3 - x 1, u05 x⟫ - ⟪x 4 - x 1, u05 x⟫) :=
        pos_of_mul_pos_left (by linear_combination h23) (mul_pos hd2 hs2).le
      have k6 : 0 < ⟪x 6 - x 1, u05 x⟫ - ⟪x 4 - x 1, u05 x⟫ :=
        pos_of_mul_pos_left (by linear_combination h46) (mul_pos hd2 hs4).le
      exact ⟨max_lt k1 (max_lt (by linarith) (max_lt (by linarith) (by linarith))), by linarith⟩
    · rintro ⟨hlo, h6⟩ i j hi hj hjc
      have h1 : 0 < ⟪x 4 - x 1, u05 x⟫ := lt_of_le_of_lt (le_max_left _ _) hlo
      have h2 : ⟪x 2 - x 1, u05 x⟫ < ⟪x 4 - x 1, u05 x⟫ :=
        lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hlo
      have h5 : ⟪x 5 - x 1, u05 x⟫ < ⟪x 4 - x 1, u05 x⟫ :=
        lt_of_le_of_lt (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hlo
      have h3 : ⟪x 3 - x 1, u05 x⟫ < ⟪x 4 - x 1, u05 x⟫ :=
        lt_of_le_of_lt (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hlo
      have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
        fin_cases i <;> first
          | exact Or.inl rfl | exact Or.inr (Or.inl rfl)
          | exact Or.inr (Or.inr (Or.inl rfl)) | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
          | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
          | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl
      · rcases hj with rfl | rfl
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.1, h14]
          calc 0 < (det24 x * det24 x) * (⟪x 4 - x 1, u05 x⟫ * (1 - oblX0 x 5)) :=
                mul_pos hd2 (mul_pos h1 hs0)
            _ = _ := by ring
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.1, hdiff 2]
          calc 0 < (det24 x * det24 x) * ((⟪x 4 - x 1, u05 x⟫ - ⟪x 2 - x 1, u05 x⟫) * (1 - oblX0 x 5)) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h2) hs0)
            _ = _ := by ring
      · rcases hj with rfl | rfl
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (1 + 1 : ZMod 6) = 2 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.2.1, hdiff 2]
          calc 0 < (det24 x * det24 x) * ((⟪x 4 - x 1, u05 x⟫ - ⟪x 2 - x 1, u05 x⟫) * (oblX6 x 5 * omega5 x)) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h2) hs1)
            _ = _ := by ring
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (1 + 1 : ZMod 6) = 2 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.2.1, hdiff 5]
          calc 0 < (det24 x * det24 x) * ((⟪x 4 - x 1, u05 x⟫ - ⟪x 5 - x 1, u05 x⟫) * (oblX6 x 5 * omega5 x)) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h5) hs1)
            _ = _ := by ring
      · rcases hj with rfl | rfl
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (2 + 1 : ZMod 6) = 3 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.2.2.1, hdiff 5]
          calc 0 < (det24 x * det24 x) * ((⟪x 4 - x 1, u05 x⟫ - ⟪x 5 - x 1, u05 x⟫) * (-σ * nC x)) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h5) hs2)
            _ = _ := by ring
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (2 + 1 : ZMod 6) = 3 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.2.2.1, hdiff 3]
          calc 0 < (det24 x * det24 x) * ((⟪x 4 - x 1, u05 x⟫ - ⟪x 3 - x 1, u05 x⟫) * (-σ * nC x)) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h3) hs2)
            _ = _ := by ring
      · rcases hj with rfl | rfl
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (3 + 1 : ZMod 6) = 4 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.2.2.2.1, hdiff 3]
          calc 0 < (det24 x * det24 x) * ((⟪x 4 - x 1, u05 x⟫ - ⟪x 3 - x 1, u05 x⟫) * (-(1 - σ) * nC x)) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h3) hs3)
            _ = _ := by ring
        · exact absurd (by decide : (3 + 1 : ZMod 6) = 4) hjc
      · rcases hj with rfl | rfl
        · exact absurd rfl hjc
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.2.2.2.2, hdiff 6]
          calc 0 < (det24 x * det24 x) * ((⟪x 6 - x 1, u05 x⟫ - ⟪x 4 - x 1, u05 x⟫) *
                (oblX2 x 5 * oblX0 x 4 + (1 - oblX0 x 5) * oblX2 x 4)) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h6) hs4)
            _ = _ := by ring
      · exact absurd rfl hi
  exact or_comm.trans (or_congr hpos_iff hneg_iff)

/-- **L3 `SplitRows` equivalence for `p5/e61` (`nC > 0`)**. -/
theorem u05_split_p5_e61 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (ha5 : oblX0 x 5 < 1) (hnC : 0 < nC x)
    {σ τ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hdec : x 3 - x 0 = σ • (x 4 - x 0) + τ • (x 5 - x 0)) :
    (SplitRows (fun i => x (c05Pos i)) (u05 x) 5 2 (det24 x) ∨
     SplitRows (fun i => x (c05Pos i)) (u05 x) 5 2 (-det24 x)) ↔
    ((max ⟪x 3 - x 1, u05 x⟫ (max ⟪x 4 - x 1, u05 x⟫ ⟪x 6 - x 1, u05 x⟫) < ⟪x 5 - x 1, u05 x⟫ ∧
      ⟪x 5 - x 1, u05 x⟫ < min 0 ⟪x 2 - x 1, u05 x⟫) ∨
     (max 0 ⟪x 2 - x 1, u05 x⟫ < ⟪x 5 - x 1, u05 x⟫ ∧
      ⟪x 5 - x 1, u05 x⟫ < min ⟪x 3 - x 1, u05 x⟫ (min ⟪x 4 - x 1, u05 x⟫ ⟪x 6 - x 1, u05 x⟫))) := by
  have T := type24OfFac F
  have ha4 : 0 < oblX0 x 4 := T.X0_pos (v := 4) (by decide)
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hd5 : 0 < 1 - oblX0 x 5 := sub_pos.mpr ha5
  have hom5 : 0 < omega5 x := hC.2.2.1
  have hr := u05_rises_e61 F hdec
  have hd2 : 0 < det24 x * det24 x := mul_self_pos.mpr T.det_ne
  have hs0 : 0 < 1 - oblX0 x 5 := hd5
  have hs1 : 0 < oblX6 x 5 * omega5 x := mul_pos hc5 hom5
  have hs2 : 0 < σ * nC x := mul_pos hσ0 hnC
  have hs3 : 0 < (1 - σ) * nC x := mul_pos (sub_pos.mpr hσ1) hnC
  have hs4 : 0 < oblX2 x 5 * oblX0 x 4 + (1 - oblX0 x 5) * oblX2 x 4 := by nlinarith
  have h15 : ⟪x 1 - x 5, u05 x⟫ = -⟪x 5 - x 1, u05 x⟫ := by
    rw [show x 1 - x 5 = -(x 5 - x 1) by abel, inner_neg_left]
  have hdiff : ∀ v : Fin 7, ⟪x v - x 5, u05 x⟫ = ⟪x v - x 1, u05 x⟫ - ⟪x 5 - x 1, u05 x⟫ := by
    intro v; rw [show x v - x 5 = (x v - x 1) - (x 5 - x 1) by abel, inner_sub_left]
  have hpos_iff : SplitRows (fun i => x (c05Pos i)) (u05 x) 5 2 (-det24 x) ↔
      (max ⟪x 3 - x 1, u05 x⟫ (max ⟪x 4 - x 1, u05 x⟫ ⟪x 6 - x 1, u05 x⟫) < ⟪x 5 - x 1, u05 x⟫ ∧
       ⟪x 5 - x 1, u05 x⟫ < min 0 ⟪x 2 - x 1, u05 x⟫) := by
    constructor
    · intro h
      have h01 := h 0 0 (by decide) (Or.inl rfl) (by decide)
      have h02 := h 0 1 (by decide) (Or.inr rfl) (by decide)
      have h23 := h 2 3 (by decide) (Or.inr rfl) (by decide)
      have h34 := h 3 4 (by decide) (Or.inr rfl) (by decide)
      have h46 := h 4 5 (by decide) (Or.inr rfl) (by decide)
      try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
      simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide,
        show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide,
        show (4 + 1 : ZMod 6) = 5 by decide] at h01 h02 h23 h34 h46
      rw [hr.1] at h01 h02; rw [hr.2.2.1] at h23; rw [hr.2.2.2.1] at h34; rw [hr.2.2.2.2] at h46
      rw [h15] at h01; rw [hdiff 2] at h02; rw [hdiff 3] at h23; rw [hdiff 4] at h34; rw [hdiff 6] at h46
      have k1 : 0 < -⟪x 5 - x 1, u05 x⟫ :=
        pos_of_mul_pos_left (by linear_combination h01) (mul_pos hd2 hs0).le
      have k2 : 0 < ⟪x 2 - x 1, u05 x⟫ - ⟪x 5 - x 1, u05 x⟫ :=
        pos_of_mul_pos_left (by linear_combination h02) (mul_pos hd2 hs0).le
      have k3 : 0 < -(⟪x 3 - x 1, u05 x⟫ - ⟪x 5 - x 1, u05 x⟫) :=
        pos_of_mul_pos_left (by linear_combination h23) (mul_pos hd2 hs2).le
      have k4 : 0 < -(⟪x 4 - x 1, u05 x⟫ - ⟪x 5 - x 1, u05 x⟫) :=
        pos_of_mul_pos_left (by linear_combination h34) (mul_pos hd2 hs3).le
      have k6 : 0 < -(⟪x 6 - x 1, u05 x⟫ - ⟪x 5 - x 1, u05 x⟫) :=
        pos_of_mul_pos_left (by linear_combination h46) (mul_pos hd2 hs4).le
      exact ⟨max_lt (by linarith) (max_lt (by linarith) (by linarith)), lt_min (by linarith) (by linarith)⟩
    · rintro ⟨hlo, hhi⟩ i j hi hj hjc
      have h3 : ⟪x 3 - x 1, u05 x⟫ < ⟪x 5 - x 1, u05 x⟫ := lt_of_le_of_lt (le_max_left _ _) hlo
      have h4 : ⟪x 4 - x 1, u05 x⟫ < ⟪x 5 - x 1, u05 x⟫ :=
        lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hlo
      have h6 : ⟪x 6 - x 1, u05 x⟫ < ⟪x 5 - x 1, u05 x⟫ :=
        lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hlo
      have h1 : ⟪x 5 - x 1, u05 x⟫ < 0 := lt_of_lt_of_le hhi (min_le_left _ _)
      have h2 : ⟪x 5 - x 1, u05 x⟫ < ⟪x 2 - x 1, u05 x⟫ := lt_of_lt_of_le hhi (min_le_right _ _)
      have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
        fin_cases i <;> first
          | exact Or.inl rfl | exact Or.inr (Or.inl rfl)
          | exact Or.inr (Or.inr (Or.inl rfl)) | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
          | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
          | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl
      · rcases hj with rfl | rfl
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.1, h15]
          calc 0 < (det24 x * det24 x) * ((-⟪x 5 - x 1, u05 x⟫) * (1 - oblX0 x 5)) :=
                mul_pos hd2 (mul_pos (neg_pos.mpr h1) hs0)
            _ = _ := by ring
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.1, hdiff 2]
          calc 0 < (det24 x * det24 x) * ((⟪x 2 - x 1, u05 x⟫ - ⟪x 5 - x 1, u05 x⟫) * (1 - oblX0 x 5)) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h2) hs0)
            _ = _ := by ring
      · rcases hj with rfl | rfl
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (1 + 1 : ZMod 6) = 2 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.2.1, hdiff 2]
          calc 0 < (det24 x * det24 x) * ((⟪x 2 - x 1, u05 x⟫ - ⟪x 5 - x 1, u05 x⟫) * (oblX6 x 5 * omega5 x)) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h2) hs1)
            _ = _ := by ring
        · exact absurd (by decide : (1 + 1 : ZMod 6) = 2) hjc
      · rcases hj with rfl | rfl
        · exact absurd rfl hjc
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (2 + 1 : ZMod 6) = 3 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.2.2.1, hdiff 3]
          calc 0 < (det24 x * det24 x) * ((⟪x 5 - x 1, u05 x⟫ - ⟪x 3 - x 1, u05 x⟫) * (σ * nC x)) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h3) hs2)
            _ = _ := by ring
      · rcases hj with rfl | rfl
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (3 + 1 : ZMod 6) = 4 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.2.2.2.1, hdiff 3]
          calc 0 < (det24 x * det24 x) * ((⟪x 5 - x 1, u05 x⟫ - ⟪x 3 - x 1, u05 x⟫) * ((1 - σ) * nC x)) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h3) hs3)
            _ = _ := by ring
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (3 + 1 : ZMod 6) = 4 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.2.2.2.1, hdiff 4]
          calc 0 < (det24 x * det24 x) * ((⟪x 5 - x 1, u05 x⟫ - ⟪x 4 - x 1, u05 x⟫) * ((1 - σ) * nC x)) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h4) hs3)
            _ = _ := by ring
      · rcases hj with rfl | rfl
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.2.2.2.2, hdiff 4]
          calc 0 < (det24 x * det24 x) * ((⟪x 5 - x 1, u05 x⟫ - ⟪x 4 - x 1, u05 x⟫) *
                (oblX2 x 5 * oblX0 x 4 + (1 - oblX0 x 5) * oblX2 x 4)) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h4) hs4)
            _ = _ := by ring
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.2.2.2.2, hdiff 6]
          calc 0 < (det24 x * det24 x) * ((⟪x 5 - x 1, u05 x⟫ - ⟪x 6 - x 1, u05 x⟫) *
                (oblX2 x 5 * oblX0 x 4 + (1 - oblX0 x 5) * oblX2 x 4)) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h6) hs4)
            _ = _ := by ring
      · exact absurd rfl hi
  have hneg_iff : SplitRows (fun i => x (c05Pos i)) (u05 x) 5 2 (det24 x) ↔
      (max 0 ⟪x 2 - x 1, u05 x⟫ < ⟪x 5 - x 1, u05 x⟫ ∧
       ⟪x 5 - x 1, u05 x⟫ < min ⟪x 3 - x 1, u05 x⟫ (min ⟪x 4 - x 1, u05 x⟫ ⟪x 6 - x 1, u05 x⟫)) := by
    constructor
    · intro h
      have h01 := h 0 0 (by decide) (Or.inl rfl) (by decide)
      have h02 := h 0 1 (by decide) (Or.inr rfl) (by decide)
      have h23 := h 2 3 (by decide) (Or.inr rfl) (by decide)
      have h34 := h 3 4 (by decide) (Or.inr rfl) (by decide)
      have h46 := h 4 5 (by decide) (Or.inr rfl) (by decide)
      try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
      simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide,
        show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide,
        show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at h01 h02 h23 h34 h46
      rw [hr.1] at h01 h02; rw [hr.2.2.1] at h23; rw [hr.2.2.2.1] at h34; rw [hr.2.2.2.2] at h46
      rw [h15] at h01; rw [hdiff 2] at h02; rw [hdiff 3] at h23; rw [hdiff 4] at h34; rw [hdiff 6] at h46
      have k1 : 0 < ⟪x 5 - x 1, u05 x⟫ :=
        pos_of_mul_pos_left (by linear_combination h01) (mul_pos hd2 hs0).le
      have k2 : 0 < -(⟪x 2 - x 1, u05 x⟫ - ⟪x 5 - x 1, u05 x⟫) :=
        pos_of_mul_pos_left (by linear_combination h02) (mul_pos hd2 hs0).le
      have k3 : 0 < ⟪x 3 - x 1, u05 x⟫ - ⟪x 5 - x 1, u05 x⟫ :=
        pos_of_mul_pos_left (by linear_combination h23) (mul_pos hd2 hs2).le
      have k4 : 0 < ⟪x 4 - x 1, u05 x⟫ - ⟪x 5 - x 1, u05 x⟫ :=
        pos_of_mul_pos_left (by linear_combination h34) (mul_pos hd2 hs3).le
      have k6 : 0 < ⟪x 6 - x 1, u05 x⟫ - ⟪x 5 - x 1, u05 x⟫ :=
        pos_of_mul_pos_left (by linear_combination h46) (mul_pos hd2 hs4).le
      exact ⟨max_lt k1 (by linarith), lt_min (by linarith) (lt_min (by linarith) (by linarith))⟩
    · rintro ⟨hlo, hhi⟩ i j hi hj hjc
      have h1 : 0 < ⟪x 5 - x 1, u05 x⟫ := lt_of_le_of_lt (le_max_left _ _) hlo
      have h2 : ⟪x 2 - x 1, u05 x⟫ < ⟪x 5 - x 1, u05 x⟫ := lt_of_le_of_lt (le_max_right _ _) hlo
      have h3 : ⟪x 5 - x 1, u05 x⟫ < ⟪x 3 - x 1, u05 x⟫ := lt_of_lt_of_le hhi (min_le_left _ _)
      have h4 : ⟪x 5 - x 1, u05 x⟫ < ⟪x 4 - x 1, u05 x⟫ :=
        lt_of_lt_of_le hhi (le_trans (min_le_right _ _) (min_le_left _ _))
      have h6 : ⟪x 5 - x 1, u05 x⟫ < ⟪x 6 - x 1, u05 x⟫ :=
        lt_of_lt_of_le hhi (le_trans (min_le_right _ _) (min_le_right _ _))
      have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
        fin_cases i <;> first
          | exact Or.inl rfl | exact Or.inr (Or.inl rfl)
          | exact Or.inr (Or.inr (Or.inl rfl)) | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
          | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
          | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl
      · rcases hj with rfl | rfl
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.1, h15]
          calc 0 < (det24 x * det24 x) * (⟪x 5 - x 1, u05 x⟫ * (1 - oblX0 x 5)) :=
                mul_pos hd2 (mul_pos h1 hs0)
            _ = _ := by ring
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (0 + 1 : ZMod 6) = 1 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.1, hdiff 2]
          calc 0 < (det24 x * det24 x) * ((⟪x 5 - x 1, u05 x⟫ - ⟪x 2 - x 1, u05 x⟫) * (1 - oblX0 x 5)) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h2) hs0)
            _ = _ := by ring
      · rcases hj with rfl | rfl
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (1 + 1 : ZMod 6) = 2 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.2.1, hdiff 2]
          calc 0 < (det24 x * det24 x) * ((⟪x 5 - x 1, u05 x⟫ - ⟪x 2 - x 1, u05 x⟫) * (oblX6 x 5 * omega5 x)) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h2) hs1)
            _ = _ := by ring
        · exact absurd (by decide : (1 + 1 : ZMod 6) = 2) hjc
      · rcases hj with rfl | rfl
        · exact absurd rfl hjc
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (2 + 1 : ZMod 6) = 3 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.2.2.1, hdiff 3]
          calc 0 < (det24 x * det24 x) * ((⟪x 3 - x 1, u05 x⟫ - ⟪x 5 - x 1, u05 x⟫) * (σ * nC x)) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h3) hs2)
            _ = _ := by ring
      · rcases hj with rfl | rfl
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (3 + 1 : ZMod 6) = 4 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.2.2.2.1, hdiff 3]
          calc 0 < (det24 x * det24 x) * ((⟪x 3 - x 1, u05 x⟫ - ⟪x 5 - x 1, u05 x⟫) * ((1 - σ) * nC x)) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h3) hs3)
            _ = _ := by ring
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (3 + 1 : ZMod 6) = 4 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.2.2.2.1, hdiff 4]
          calc 0 < (det24 x * det24 x) * ((⟪x 4 - x 1, u05 x⟫ - ⟪x 5 - x 1, u05 x⟫) * ((1 - σ) * nC x)) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h4) hs3)
            _ = _ := by ring
      · rcases hj with rfl | rfl
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.2.2.2.2, hdiff 4]
          calc 0 < (det24 x * det24 x) * ((⟪x 4 - x 1, u05 x⟫ - ⟪x 5 - x 1, u05 x⟫) *
                (oblX2 x 5 * oblX0 x 4 + (1 - oblX0 x 5) * oblX2 x 4)) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h4) hs4)
            _ = _ := by ring
        try simp only [show (0 + 1 : ZMod 6) = 1 by decide, show (1 + 1 : ZMod 6) = 2 by decide, show (2 + 1 : ZMod 6) = 3 by decide, show (3 + 1 : ZMod 6) = 4 by decide, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide] at *
        · simp only [c05Pos, Matrix.cons_val, show (4 + 1 : ZMod 6) = 5 by decide, show (5 + 1 : ZMod 6) = 0 by decide]
          rw [hr.2.2.2.2, hdiff 6]
          calc 0 < (det24 x * det24 x) * ((⟪x 6 - x 1, u05 x⟫ - ⟪x 5 - x 1, u05 x⟫) *
                (oblX2 x 5 * oblX0 x 4 + (1 - oblX0 x 5) * oblX2 x 4)) :=
                mul_pos hd2 (mul_pos (sub_pos.mpr h6) hs4)
            _ = _ := by ring
      · exact absurd rfl hi
  exact or_comm.trans (or_congr hpos_iff hneg_iff)

/-! ### L7a, L7b: Pure ring identities -/

/-- **L7a (`U07-Saddle-Elim`)**: eliminates `A` and `C` between `U07_34` and `U07_04`. -/
theorem u07_saddle_elim_id
    (a3 b3 c3 om3 a4 b4 c4 a5 b5 c5 σ τ A B _C al be ga : ℝ)
    (ha3 : a3 = (1 - σ - τ) + σ * a4 + τ * a5)
    (hb3 : b3 = σ * b4 + τ * b5)
    (hc3 : c3 = σ * c4 + τ * c5) :
    let U07_34 := -(a4 - a3) * A + (b3 - b4) * om3 * B -
      ((b3 - b4) - (a4 - a3) * om3) * al - (c3 - c4) * be - (c3 - c4) * om3 * ga
    let U07_04 := (1 - a4) * A - b4 * om3 * B -
      ((1 - a4) * om3 - b4) * al + c4 * be + c4 * om3 * ga
    let nB := (1 - a5) * c4 - (1 - a4) * c5
    let nC := -(1 - a5) * b4 + (1 - a4) * b5
    (1 - a4) * U07_34 + (a4 - a3) * U07_04 =
      τ * (om3 * nC * B - nC * al + nB * be + om3 * nB * ga) := by
  subst ha3 hb3 hc3; ring

/-- **L7b (`L1 C46 + L2 U46_60 + L3 T26_26`)**: eliminates `A` from `C46` via `U46_60` and
cancels `C` in the `U46_60` term via `T26_26`. -/
theorem psi_05_46_26_id
    (om3 om4 om5 a4 b4 c4 a5 b5 c5 A B C al be ga : ℝ) :
    let d5 := 1 - a5
    let s4 := c4 - 1
    let C46 := a4 * d5 * A - b4 * b5 * B - s4 * c5 * C +
      (a4 * b5 - b4 * d5) * al + (a4 * c5 - s4 * d5) * be + (b4 * c5 + s4 * b5) * ga
    let U46_60 := -(om4 + 1) * A + (om3 * om4 - 1) * C +
      (om3 + 1) * al + (om3 * om4 - om4 - 2) * be - (om3 + 1) * ga
    let T26_26 := om5 * B - C + (om5 - 1) * ga
    (om4 + 1) * C46 + a4 * d5 * U46_60 + a4 * d5 * (om3 * om4 - 1) * T26_26 =
      -((om4 + 1) * b4 * b5 - a4 * d5 * om5 * (om3 * om4 - 1)) * B -
      (om4 + 1) * s4 * c5 * C +
      ((om4 + 1) * (a4 * b5 - b4 * d5) + a4 * d5 * (om3 + 1)) * al +
      ((om4 + 1) * (a4 * c5 - s4 * d5) + a4 * d5 * (om3 * om4 - om4 - 2)) * be +
      ((om4 + 1) * (b4 * c5 + s4 * b5) - a4 * d5 * (om3 + 1) +
        a4 * d5 * (om3 * om4 - 1) * (om5 - 1)) * ga := by
  ring

/-! ### L8: `Q45HalfHyp` equivalences and region-B discharge -/

/-- Unconditional sign equivalence: `f126(x 4) < f126(x 0) ↔ 1 < a4`. -/
theorem f126_x4_lt_x0_iff {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    F.f 5 (x 4) < F.f 5 (x 0) ↔ 1 < oblX0 x 4 := by
  have h0 : F.f 5 (x 0) < 0 := F.neg 5 0 (by decide)
  have e4 : F.f 5 (x 4) = oblX0 x 4 * F.f 5 (x 0) := by
    rw [fac_eval F 5 4, F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)]
    ring
  rw [e4]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- Unconditional sign equivalence: `f126(x 5) < f126(x 0) ↔ 1 < a5`. -/
theorem f126_x5_lt_x0_iff {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    F.f 5 (x 5) < F.f 5 (x 0) ↔ 1 < oblX0 x 5 := by
  have h0 : F.f 5 (x 0) < 0 := F.neg 5 0 (by decide)
  have e5 : F.f 5 (x 5) = oblX0 x 5 * F.f 5 (x 0) := by
    rw [fac_eval F 5 5, F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)]
    ring
  rw [e5]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **L8 region-B discharge**: when `a4 ≤ 1` and `a5 < 1`, `Q45HalfHyp F s t` fails whenever
`(D1 * D2 < 0 ∧ s ≤ 1) ∨ (0 < D1 * D2 ∧ t ≤ 1) ∨ D1 = 0`. -/
theorem q45HalfHyp_false_of_B {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha4 : oblX0 x 4 ≤ 1) (ha5 : oblX0 x 5 < 1) {s t : ℝ}
    (hbranch :
      (det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) < 0 ∧
        s ≤ 1) ∨
      (0 < det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) ∧
        t ≤ 1) ∨
      det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) = 0) :
    ¬ Q45HalfHyp F s t := by
  intro hq
  rcases hbranch with ⟨hd, hs⟩ | ⟨hd, ht⟩ | hd
  · have h5 := (hq.1 hd).1 hs
    rw [← F.hN 5 (x 5) (x 0)] at h5
    linarith [(f126_x5_lt_x0_iff F).mp (sub_lt_zero.mp h5)]
  · have h4 := (hq.2.1 hd).1 ht
    rw [← F.hN 5 (x 4) (x 0)] at h4
    linarith [(f126_x4_lt_x0_iff F).mp (sub_lt_zero.mp h4)]
  · have h4 := (hq.2.2 hd).1
    rw [← F.hN 5 (x 4) (x 0)] at h4
    linarith [(f126_x4_lt_x0_iff F).mp (sub_lt_zero.mp h4)]

end Minimality.T24.A10
