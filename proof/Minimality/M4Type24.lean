module

public import Minimality.RCell24
public import Minimality.Type24
public import Minimality.RDispatch24
public import Minimality.SameView
public import Minimality.LexCell
public import Minimality.SplitLeaf
public import Minimality.RimFromSigns
public import Minimality.FrontDiag

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset Filter
open scoped Topology

namespace Minimality.T24.M4

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell
  Minimality.LexCell Minimality.Split

/-- `κ5` from M4 Step 3. -/
noncomputable def kappa5 (x : Fin 7 → ℝ³) : ℝ :=
  oblX6 x 3 * (omega3 x * oblX0 x 5 - oblX2 x 5) + oblX6 x 5 * (1 - oblX6 x 3)

/-! ### L0: Frame bridge from `S0xFac 9 s0x_S24 x` to `Type24 x` -/

noncomputable def face16OfFac {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (t : Fin 9) {S : Finset (Fin 7)} (hS : S = s0x_S24 t) : Face16 x S where
  f := F.f t
  N := F.N t
  hN := F.hN t
  zero := fun i hi => F.zero t i (hS ▸ hi)
  neg := fun i hi => F.neg t i (hS ▸ hi)

/-- Build `Type24 x` from `F : S0xFac 9 s0x_S24 x` (facets `0, 1, 5, 7, 4, 2`). -/
noncomputable def type24OfFac {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Type24 x where
  t012 := face16OfFac F 0 (by decide)
  t016 := face16OfFac F 1 (by decide)
  t126 := face16OfFac F 5 (by decide)
  t236 := face16OfFac F 7 (by decide)
  t046 := face16OfFac F 4 (by decide)
  t025 := face16OfFac F 2 (by decide)

theorem fac_eval {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) (v : Fin 7) :
    F.f t (x v) = F.f t (x 1) + oblX0 x v * (F.f t (x 0) - F.f t (x 1)) +
      oblX2 x v * (F.f t (x 2) - F.f t (x 1)) + oblX6 x v * (F.f t (x 6) - F.f t (x 1)) := by
  have T := type24OfFac F
  have hrep := T.rep v
  have h1 : x v - x 1 = oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) +
      oblX6 x v • (x 6 - x 1) := by
    rw [hrep]; abel
  have e := congrArg (fun w => ⟪F.N t, w⟫) h1
  rw [← F.hN t (x v) (x 1), inner_add_right, inner_add_right,
    inner_smul_right, inner_smul_right, inner_smul_right,
    ← F.hN t (x 0) (x 1), ← F.hN t (x 2) (x 1), ← F.hN t (x 6) (x 1)] at e
  linarith

theorem inner_rep {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (v : Fin 7) (u : ℝ³) :
    ⟪x v - x 1, u⟫ = oblX0 x v * ⟪x 0 - x 1, u⟫ + oblX2 x v * ⟪x 2 - x 1, u⟫ +
      oblX6 x v * ⟪x 6 - x 1, u⟫ := by
  have T := type24OfFac F
  have h1 : x v - x 1 = oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) +
      oblX6 x v • (x 6 - x 1) := by
    rw [T.rep v]; abel
  rw [h1, inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_smul_left]

theorem eq3 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    oblX2 x 3 + oblX6 x 3 - omega3 x * oblX0 x 3 = 1 := by
  have T := type24OfFac F
  have ha : oblX0 x 3 ≠ 0 := (T.X0_pos (v := 3) (by decide)).ne'
  simp only [omega3]
  field_simp [ha]
  ring

theorem eq4 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    oblX0 x 4 + oblX6 x 4 - 1 = omega4 x * oblX2 x 4 := by
  have T := type24OfFac F
  have hb : oblX2 x 4 ≠ 0 := (T.X2_pos (v := 4) (by decide)).ne'
  simp only [omega4]
  field_simp [hb]

theorem eq5 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    oblX0 x 5 + oblX2 x 5 - 1 = omega5 x * oblX6 x 5 := by
  have T := type24OfFac F
  have hc : oblX6 x 5 ≠ 0 := (T.X6_pos (v := 5) (by decide)).ne'
  simp only [omega5]
  field_simp [hc]

theorem det3_frame (x : Fin 7 → ℝ³) (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℝ) :
    det3 (a0 • (x 0 - x 1) + a1 • (x 2 - x 1) + a2 • (x 6 - x 1))
         (b0 • (x 0 - x 1) + b1 • (x 2 - x 1) + b2 • (x 6 - x 1))
         (c0 • (x 0 - x 1) + c1 • (x 2 - x 1) + c2 • (x 6 - x 1)) =
      (a0 * (b1 * c2 - b2 * c1) - a1 * (b0 * c2 - b2 * c0) + a2 * (b0 * c1 - b1 * c0)) *
        det24 x := by
  simpa [det24] using det3_comb (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) a0 a1 a2 b0 b1 b2 c0 c1 c2

/-! ### L1: Cross product positivity `0 < c3 * b5 - c5 * b3` -/

theorem cross35_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    0 < oblX6 x 3 * oblX2 x 5 - oblX6 x 5 * oblX2 x 3 := by
  have T := type24OfFac F
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  -- `F.f 3` vanishes on `0, 3, 4, 5` and is negative on `1, 2, 6`.
  have f3_1 : F.f 3 (x 1) < 0 := F.neg 3 1 (by decide)
  have f3_2 : F.f 3 (x 2) < 0 := F.neg 3 2 (by decide)
  have f3_6 : F.f 3 (x 6) < 0 := F.neg 3 6 (by decide)
  have f3_0 : F.f 3 (x 0) = 0 := F.zero 3 0 (by decide)
  have f3_4 : F.f 3 (x 4) = 0 := F.zero 3 4 (by decide)
  have f3_5 : F.f 3 (x 5) = 0 := F.zero 3 5 (by decide)
  have ev4 := fac_eval F 3 4
  have ev5 := fac_eval F 3 5
  rw [f3_4, f3_0] at ev4
  rw [f3_5, f3_0] at ev5
  set α := -F.f 3 (x 1)
  set β := F.f 3 (x 2) - F.f 3 (x 1)
  set γ := F.f 3 (x 6) - F.f 3 (x 1)
  have hα : 0 < α := by linarith
  have h4 : α * (oblX0 x 4 - 1) + β * oblX2 x 4 + γ * oblX6 x 4 = 0 := by
    dsimp [α, β, γ]; linarith
  have h5 : α * (oblX0 x 5 - 1) + β * oblX2 x 5 + γ * oblX6 x 5 = 0 := by
    dsimp [α, β, γ]; linarith
  -- Eliminate `α`: `α * F025(y4) = ...` where `F025(y4) < 0` since `4 ∉ {0, 2, 5}`.
  have h025_4 : oblX0 x 4 + oblX2 x 4 - omega5 x * oblX6 x 4 < 1 := by
    have hneg : F.f 2 (x 4) < 0 := F.neg 2 4 (by decide)
    have h1 : F.f 2 (x 1) < 0 := F.neg 2 1 (by decide)
    have h0 : F.f 2 (x 0) = 0 := F.zero 2 0 (by decide)
    have h2 : F.f 2 (x 2) = 0 := F.zero 2 2 (by decide)
    have h5' : F.f 2 (x 5) = 0 := F.zero 2 5 (by decide)
    have ev24 := fac_eval F 2 4
    have ev25 := fac_eval F 2 5
    rw [h0, h2] at ev24
    rw [h5', h0, h2] at ev25
    have h6_eq : F.f 2 (x 6) - F.f 2 (x 1) = F.f 2 (x 1) * omega5 x := by
      have := eq5 F
      have hc5' : oblX6 x 5 ≠ 0 := hc5.ne'
      have h1' : F.f 2 (x 1) * (1 - oblX0 x 5 - oblX2 x 5) +
          oblX6 x 5 * (F.f 2 (x 6) - F.f 2 (x 1)) = 0 := by
        linear_combination -ev25
      have h2' : oblX6 x 5 * ((F.f 2 (x 6) - F.f 2 (x 1)) - F.f 2 (x 1) * omega5 x) = 0 := by
        linear_combination h1' + F.f 2 (x 1) * this
      exact sub_eq_zero.mp ((mul_eq_zero.mp h2').resolve_left hc5')
    have e24 : (-F.f 2 (x 1)) * (oblX0 x 4 + oblX2 x 4 - omega5 x * oblX6 x 4 - 1) = F.f 2 (x 4) := by
      rw [ev24, h6_eq]; ring
    have hpos1 : 0 < -F.f 2 (x 1) := by linarith
    nlinarith
  have hD45 : 0 < oblX2 x 5 * oblX6 x 4 - oblX2 x 4 * oblX6 x 5 := by
    have e_comb : (α - β) * (oblX2 x 5 * oblX6 x 4 - oblX2 x 4 * oblX6 x 5) +
        α * oblX6 x 5 * (oblX0 x 4 + oblX2 x 4 - omega5 x * oblX6 x 4 - 1) = 0 := by
      have := eq5 F
      linear_combination oblX6 x 5 * h4 - oblX6 x 4 * h5 + α * oblX6 x 4 * this
    have hαβ : α - β = -F.f 3 (x 2) := by dsimp [α, β]; ring
    have hαβ_pos : 0 < α - β := by rw [hαβ]; linarith
    have hrhs_pos : 0 < -α * oblX6 x 5 * (oblX0 x 4 + oblX2 x 4 - omega5 x * oblX6 x 4 - 1) := by
      have : α * oblX6 x 5 * (oblX0 x 4 + oblX2 x 4 - omega5 x * oblX6 x 4 - 1) < 0 :=
        mul_neg_of_pos_of_neg (mul_pos hα hc5) (by linarith)
      linarith
    nlinarith
  -- Now use Lemma M (`lemmaM_quad_decomp`) to express `(b3, c3)` as `s (b4, c4) + t (b5, c5)`!
  obtain ⟨s, t, hs, -, -, hdec⟩ := Minimality.T24.RimFromSigns.lemmaM_quad_decomp F
  have hdec1 : x 3 - x 1 = (1 - s - t) • (x 0 - x 1) + s • (x 4 - x 1) + t • (x 5 - x 1) := by
    have : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0) := hdec
    calc x 3 - x 1 = (x 0 - x 1) + (x 3 - x 0) := by abel
      _ = (x 0 - x 1) + (s • (x 4 - x 0) + t • (x 5 - x 0)) := by rw [this]
      _ = (1 - s - t) • (x 0 - x 1) + s • (x 4 - x 1) + t • (x 5 - x 1) := by
          rw [show x 4 - x 0 = (x 4 - x 1) - (x 0 - x 1) from by abel,
              show x 5 - x 0 = (x 5 - x 1) - (x 0 - x 1) from by abel]
          module
  -- Extract `oblX2` and `oblX6` by linearity of `vol3`:
  have hb3 : oblX2 x 3 = s * oblX2 x 4 + t * oblX2 x 5 := by
    have hd := T.det_ne
    simp only [oblX2]
    have hv : vol3 (x 0 - x 1) (x 3 - x 1) (x 6 - x 1) =
        s * vol3 (x 0 - x 1) (x 4 - x 1) (x 6 - x 1) +
        t * vol3 (x 0 - x 1) (x 5 - x 1) (x 6 - x 1) := by
      rw [hdec1]
      simp only [vol3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [hv]; ring
  have hc3 : oblX6 x 3 = s * oblX6 x 4 + t * oblX6 x 5 := by
    simp only [oblX6]
    have hv : vol3 (x 0 - x 1) (x 2 - x 1) (x 3 - x 1) =
        s * vol3 (x 0 - x 1) (x 2 - x 1) (x 4 - x 1) +
        t * vol3 (x 0 - x 1) (x 2 - x 1) (x 5 - x 1) := by
      rw [hdec1]
      simp only [vol3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [hv]; ring
  have hid : oblX6 x 3 * oblX2 x 5 - oblX6 x 5 * oblX2 x 3 =
      s * (oblX2 x 5 * oblX6 x 4 - oblX2 x 4 * oblX6 x 5) := by
    rw [hb3, hc3]; ring
  rw [hid]
  exact mul_pos hs hD45

/-! ### L2: Nine facet signs at `w02 = x 2 - x 0` -/

theorem w02_facings {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (h346 : F.f 8 (x 2) < F.f 8 (x 0)) :
    ⟪F.N 0, x 2 - x 0⟫ = 0 ∧ ⟪F.N 1, x 2 - x 0⟫ < 0 ∧ ⟪F.N 2, x 2 - x 0⟫ = 0 ∧
    ⟪F.N 3, x 2 - x 0⟫ < 0 ∧ ⟪F.N 4, x 2 - x 0⟫ < 0 ∧ 0 < ⟪F.N 5, x 2 - x 0⟫ ∧
    0 < ⟪F.N 6, x 2 - x 0⟫ ∧ 0 < ⟪F.N 7, x 2 - x 0⟫ ∧ ⟪F.N 8, x 2 - x 0⟫ < 0 := by
  have hf : ∀ t : Fin 9, ⟪F.N t, x 2 - x 0⟫ = F.f t (x 2) - F.f t (x 0) :=
    fun t => (F.hN t (x 2) (x 0)).symm
  simp only [hf]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [F.zero 0 2 (by decide), F.zero 0 0 (by decide), sub_self]
  · rw [F.zero 1 0 (by decide), sub_zero]; exact F.neg 1 2 (by decide)
  · rw [F.zero 2 2 (by decide), F.zero 2 0 (by decide), sub_self]
  · rw [F.zero 3 0 (by decide), sub_zero]; exact F.neg 3 2 (by decide)
  · rw [F.zero 4 0 (by decide), sub_zero]; exact F.neg 4 2 (by decide)
  · rw [F.zero 5 2 (by decide), zero_sub, neg_pos]; exact F.neg 5 0 (by decide)
  · rw [F.zero 6 2 (by decide), zero_sub, neg_pos]; exact F.neg 6 0 (by decide)
  · rw [F.zero 7 2 (by decide), zero_sub, neg_pos]; exact F.neg 7 0 (by decide)
  · linarith

/-! ### L3: Convexity / pencil inequalities at `w02` (gap G3 fix) -/

theorem w02_convex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (hc3 : oblX6 x 3 < 1) (h346 : F.f 8 (x 2) < F.f 8 (x 0)) :
    1 < oblX0 x 5 + oblX2 x 5 ∧
    0 < (1 - oblX6 x 5) * (oblX0 x 3 + oblX2 x 3) - (1 - oblX6 x 3) * (oblX0 x 5 + oblX2 x 5) ∧
    0 < (oblX6 x 5 - oblX6 x 3) * (1 - (oblX0 x 5 + oblX2 x 5)) +
        oblX6 x 5 * ((oblX0 x 5 + oblX2 x 5) - (oblX0 x 3 + oblX2 x 3)) ∧
    oblX6 x 5 < oblX6 x 3 := by
  have T := type24OfFac F
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hY5 : 1 < oblX0 x 5 + oblX2 x 5 := by
    have e := eq5 F
    nlinarith [hC.2.2.1]
  -- Pencil `H'` vanishing on `x 3, x 6` and constant along `w02 = x 2 - x 0`:
  -- `H'(y) = (F.f 8 (x 0) - F.f 8 (x 2)) * F.f 7 y + (-F.f 7 (x 0)) * F.f 8 y`.
  have h80_2 : 0 < F.f 8 (x 0) - F.f 8 (x 2) := by linarith
  have h70 : 0 < -F.f 7 (x 0) := by linarith [F.neg 7 0 (by decide)]
  let H' : ℝ³ → ℝ := fun y => (F.f 8 (x 0) - F.f 8 (x 2)) * F.f 7 y + (-F.f 7 (x 0)) * F.f 8 y
  have hH'0 : H' (x 0) = H' (x 2) := by
    dsimp [H']
    rw [F.zero 7 2 (by decide)]
    ring
  have hH'1 : H' (x 1) < 0 := by
    dsimp [H']
    have h71 : F.f 7 (x 1) < 0 := F.neg 7 1 (by decide)
    have h81 : F.f 8 (x 1) < 0 := F.neg 8 1 (by decide)
    nlinarith
  have hH'5 : H' (x 5) < 0 := by
    dsimp [H']
    have h75 : F.f 7 (x 5) < 0 := F.neg 7 5 (by decide)
    have h85 : F.f 8 (x 5) < 0 := F.neg 8 5 (by decide)
    nlinarith
  have hH'3 : H' (x 3) = 0 := by
    dsimp [H']
    rw [F.zero 7 3 (by decide), F.zero 8 3 (by decide)]
    ring
  have hH'6 : H' (x 6) = 0 := by
    dsimp [H']
    rw [F.zero 7 6 (by decide), F.zero 8 6 (by decide)]
    ring
  have hH'_eval : ∀ v : Fin 7,
      H' (x v) = H' (x 1) + (oblX0 x v + oblX2 x v) * (H' (x 0) - H' (x 1)) +
        oblX6 x v * (H' (x 6) - H' (x 1)) := by
    intro v
    dsimp [H']
    have ev7 := fac_eval F 7 v
    have ev8 := fac_eval F 8 v
    rw [ev7, ev8]
    have h02 : (F.f 8 (x 0) - F.f 8 (x 2)) * (F.f 7 (x 2) - F.f 7 (x 1)) +
        (-F.f 7 (x 0)) * (F.f 8 (x 2) - F.f 8 (x 1)) = H' (x 0) - H' (x 1) := by
      dsimp [H']; rw [F.zero 7 2 (by decide)]; ring
    calc (F.f 8 (x 0) - F.f 8 (x 2)) * (F.f 7 (x 1) + oblX0 x v * (F.f 7 (x 0) - F.f 7 (x 1)) +
            oblX2 x v * (F.f 7 (x 2) - F.f 7 (x 1)) + oblX6 x v * (F.f 7 (x 6) - F.f 7 (x 1))) +
          (-F.f 7 (x 0)) * (F.f 8 (x 1) + oblX0 x v * (F.f 8 (x 0) - F.f 8 (x 1)) +
            oblX2 x v * (F.f 8 (x 2) - F.f 8 (x 1)) + oblX6 x v * (F.f 8 (x 6) - F.f 8 (x 1)))
        = H' (x 1) + oblX0 x v * (H' (x 0) - H' (x 1)) + oblX2 x v * (H' (x 2) - H' (x 1)) +
            oblX6 x v * (H' (x 6) - H' (x 1)) := by dsimp [H']; ring
      _ = H' (x 1) + (oblX0 x v + oblX2 x v) * (H' (x 0) - H' (x 1)) +
            oblX6 x v * (H' (x 6) - H' (x 1)) := by rw [← hH'0]; ring
  have hY3 : 0 < oblX0 x 3 + oblX2 x 3 :=
    add_pos (T.X0_pos (v := 3) (by decide)) (T.X2_pos (v := 3) (by decide))
  have hii : 0 < (1 - oblX6 x 5) * (oblX0 x 3 + oblX2 x 3) -
      (1 - oblX6 x 3) * (oblX0 x 5 + oblX2 x 5) := by
    have e3 := hH'_eval 3
    have e5 := hH'_eval 5
    rw [hH'3, hH'6, zero_sub] at e3
    rw [hH'6, zero_sub] at e5
    have hid : (oblX0 x 3 + oblX2 x 3) * H' (x 5) =
        H' (x 1) * ((1 - oblX6 x 5) * (oblX0 x 3 + oblX2 x 3) -
          (1 - oblX6 x 3) * (oblX0 x 5 + oblX2 x 5)) := by
      linear_combination (oblX0 x 3 + oblX2 x 3) * e5 - (oblX0 x 5 + oblX2 x 5) * e3
    have hprod_neg : H' (x 1) * ((1 - oblX6 x 5) * (oblX0 x 3 + oblX2 x 3) -
        (1 - oblX6 x 3) * (oblX0 x 5 + oblX2 x 5)) < 0 := by
      rw [← hid]; exact mul_neg_of_pos_of_neg hY3 hH'5
    nlinarith
  -- Pencil `H` vanishing on `x 3, x 5` and constant along `w02`:
  -- `H(y) = (-F.f 3 (x 2)) * F.f 6 y + (-F.f 6 (x 0)) * F.f 3 y`.
  have h32 : 0 < -F.f 3 (x 2) := by linarith [F.neg 3 2 (by decide)]
  have h60 : 0 < -F.f 6 (x 0) := by linarith [F.neg 6 0 (by decide)]
  let H : ℝ³ → ℝ := fun y => (-F.f 3 (x 2)) * F.f 6 y + (-F.f 6 (x 0)) * F.f 3 y
  have hH0 : H (x 0) = H (x 2) := by
    dsimp [H]
    rw [F.zero 3 0 (by decide), F.zero 6 2 (by decide)]
    ring
  have hH2 : H (x 2) < 0 := by
    dsimp [H]
    rw [F.zero 6 2 (by decide)]
    nlinarith [F.neg 3 2 (by decide)]
  have hH6 : H (x 6) < 0 := by
    dsimp [H]
    nlinarith [F.neg 6 6 (by decide), F.neg 3 6 (by decide)]
  have hH3 : H (x 3) = 0 := by
    dsimp [H]; rw [F.zero 6 3 (by decide), F.zero 3 3 (by decide)]; ring
  have hH5 : H (x 5) = 0 := by
    dsimp [H]; rw [F.zero 6 5 (by decide), F.zero 3 5 (by decide)]; ring
  have hH_eval : ∀ v : Fin 7,
      H (x v) = H (x 1) + (oblX0 x v + oblX2 x v) * (H (x 0) - H (x 1)) +
        oblX6 x v * (H (x 6) - H (x 1)) := by
    intro v
    dsimp [H]
    rw [fac_eval F 6 v, fac_eval F 3 v]
    have h1 : (-F.f 3 (x 2)) * F.f 6 (x 1) + (-F.f 6 (x 0)) * F.f 3 (x 1) = H (x 1) := rfl
    calc (-F.f 3 (x 2)) * (F.f 6 (x 1) + oblX0 x v * (F.f 6 (x 0) - F.f 6 (x 1)) +
            oblX2 x v * (F.f 6 (x 2) - F.f 6 (x 1)) + oblX6 x v * (F.f 6 (x 6) - F.f 6 (x 1))) +
          (-F.f 6 (x 0)) * (F.f 3 (x 1) + oblX0 x v * (F.f 3 (x 0) - F.f 3 (x 1)) +
            oblX2 x v * (F.f 3 (x 2) - F.f 3 (x 1)) + oblX6 x v * (F.f 3 (x 6) - F.f 3 (x 1)))
        = H (x 1) + oblX0 x v * (H (x 0) - H (x 1)) + oblX2 x v * (H (x 2) - H (x 1)) +
            oblX6 x v * (H (x 6) - H (x 1)) := by dsimp [H]; ring
      _ = H (x 1) + (oblX0 x v + oblX2 x v) * (H (x 0) - H (x 1)) +
            oblX6 x v * (H (x 6) - H (x 1)) := by rw [← hH0]; ring
  have hQ2 : 0 < (oblX6 x 5 - oblX6 x 3) * (1 - (oblX0 x 5 + oblX2 x 5)) +
      oblX6 x 5 * ((oblX0 x 5 + oblX2 x 5) - (oblX0 x 3 + oblX2 x 3)) := by
    have e3 := hH_eval 3
    have e5 := hH_eval 5
    rw [hH3] at e3
    rw [hH5] at e5
    have hlin : H (x 2) * ((1 - oblX6 x 5) * (oblX0 x 3 + oblX2 x 3) -
          (1 - oblX6 x 3) * (oblX0 x 5 + oblX2 x 5)) =
        H (x 6) * ((oblX6 x 5 - oblX6 x 3) * (1 - (oblX0 x 5 + oblX2 x 5)) +
          oblX6 x 5 * ((oblX0 x 5 + oblX2 x 5) - (oblX0 x 3 + oblX2 x 3))) := by
      have hcomb : H (x 0) * ((1 - oblX6 x 5) * (oblX0 x 3 + oblX2 x 3) -
            (1 - oblX6 x 3) * (oblX0 x 5 + oblX2 x 5)) =
          H (x 6) * ((oblX6 x 5 - oblX6 x 3) * (1 - (oblX0 x 5 + oblX2 x 5)) +
            oblX6 x 5 * ((oblX0 x 5 + oblX2 x 5) - (oblX0 x 3 + oblX2 x 3))) := by
        linear_combination
          -(1 - oblX0 x 5 - oblX2 x 5 - oblX6 x 5) * e3 +
          (1 - oblX0 x 3 - oblX2 x 3 - oblX6 x 3) * e5
      rw [hH0] at hcomb
      exact hcomb
    have hneg_lhs : H (x 2) * ((1 - oblX6 x 5) * (oblX0 x 3 + oblX2 x 3) -
        (1 - oblX6 x 3) * (oblX0 x 5 + oblX2 x 5)) < 0 :=
      mul_neg_of_neg_of_pos hH2 hii
    have hneg_rhs : H (x 6) * ((oblX6 x 5 - oblX6 x 3) * (1 - (oblX0 x 5 + oblX2 x 5)) +
        oblX6 x 5 * ((oblX0 x 5 + oblX2 x 5) - (oblX0 x 3 + oblX2 x 3))) < 0 := by
      rw [← hlin]; exact hneg_lhs
    by_contra hc
    push Not at hc
    have : 0 ≤ H (x 6) * ((oblX6 x 5 - oblX6 x 3) * (1 - (oblX0 x 5 + oblX2 x 5)) +
        oblX6 x 5 * ((oblX0 x 5 + oblX2 x 5) - (oblX0 x 3 + oblX2 x 3))) :=
      mul_nonneg_of_nonpos_of_nonpos hH6.le hc
    linarith
  have hc53 : oblX6 x 5 < oblX6 x 3 := by
    by_contra h
    push Not at h
    have h1 : 0 ≤ oblX6 x 5 - oblX6 x 3 := by linarith
    have h2 : 1 - (oblX0 x 5 + oblX2 x 5) < 0 := by linarith
    have h3 : (1 - oblX6 x 3) * (oblX0 x 5 + oblX2 x 5) < (1 - oblX6 x 5) * (oblX0 x 3 + oblX2 x 3) := by
      linarith
    have h4 : 0 < 1 - oblX6 x 3 := by linarith
    have h5 : 1 - oblX6 x 5 ≤ 1 - oblX6 x 3 := by linarith
    have h6 : (1 - oblX6 x 3) * (oblX0 x 5 + oblX2 x 5) < (1 - oblX6 x 3) * (oblX0 x 3 + oblX2 x 3) := by
      nlinarith
    have h7 : oblX0 x 5 + oblX2 x 5 < oblX0 x 3 + oblX2 x 3 := by nlinarith
    have h8 : 0 < (oblX0 x 3 + oblX2 x 3) - (oblX0 x 5 + oblX2 x 5) := by linarith
    linarith [hQ2, mul_nonpos_of_nonneg_of_nonpos h1 h2.le, mul_pos hc5 h8]
  exact ⟨hY5, hii, hQ2, hc53⟩

/-! ### L4: Eight `det3` row formulas on `![1, 2, 5, 3, 6]` at `w02 = x 2 - x 0` -/

theorem w02_rows {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    let c : ZMod 5 → Fin 7 := ![1, 2, 5, 3, 6]
    let w02 := x 2 - x 0
    let Y3 := oblX0 x 3 + oblX2 x 3
    let Y5 := oblX0 x 5 + oblX2 x 5
    let ii := (1 - oblX6 x 5) * Y3 - (1 - oblX6 x 3) * Y5
    det3 (x (c 1) - x (c 0)) (x (c 4) - x (c 3)) w02 = det24 x * (-(1 - oblX6 x 3)) ∧
    det3 (x (c 2) - x (c 1)) (x (c 4) - x (c 3)) w02 = det24 x * (-oblX6 x 5 * Y3 - (1 - oblX6 x 3) * (Y5 - 1)) ∧
    det3 (x (c 3) - x (c 2)) (x (c 4) - x (c 3)) w02 = det24 x * (-ii) ∧
    det3 (x (c 0) - x (c 4)) (x (c 4) - x (c 3)) w02 = det24 x * (oblX0 x 3 + oblX2 x 3) ∧
    det3 (x (c 2) - x (c 1)) (x (c 1) - x (c 0)) w02 = det24 x * oblX6 x 5 ∧
    det3 (x (c 3) - x (c 2)) (x (c 1) - x (c 0)) w02 = det24 x * (oblX6 x 3 - oblX6 x 5) ∧
    det3 (x (c 4) - x (c 3)) (x (c 1) - x (c 0)) w02 = det24 x * (1 - oblX6 x 3) ∧
    det3 (x (c 0) - x (c 4)) (x (c 1) - x (c 0)) w02 = det24 x * (-1) := by
  have T := type24OfFac F
  have hrep : ∀ v : Fin 7, x v - x 1 =
      oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1) :=
    fun v => by rw [T.rep v]; abel
  have hw : x 2 - x 0 = (-1 : ℝ) • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) := by
    simp only [neg_smul, one_smul, zero_smul, add_zero]; abel
  have h36 : x 6 - x 3 = (-oblX0 x 3) • (x 0 - x 1) + (-oblX2 x 3) • (x 2 - x 1) +
      (1 - oblX6 x 3) • (x 6 - x 1) := by
    calc x 6 - x 3 = (x 6 - x 1) - (x 3 - x 1) := by abel
      _ = (x 6 - x 1) - (oblX0 x 3 • (x 0 - x 1) + oblX2 x 3 • (x 2 - x 1) + oblX6 x 3 • (x 6 - x 1)) := by
          rw [hrep 3]
      _ = _ := by simp only [sub_smul, neg_smul, one_smul]; abel
  have h25 : x 5 - x 2 = (oblX0 x 5) • (x 0 - x 1) + (oblX2 x 5 - 1) • (x 2 - x 1) +
      (oblX6 x 5) • (x 6 - x 1) := by
    calc x 5 - x 2 = (x 5 - x 1) - (x 2 - x 1) := by abel
      _ = (oblX0 x 5 • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) + oblX6 x 5 • (x 6 - x 1)) - (x 2 - x 1) := by
          rw [hrep 5]
      _ = _ := by simp only [sub_smul, one_smul]; abel
  have h53 : x 3 - x 5 = (oblX0 x 3 - oblX0 x 5) • (x 0 - x 1) +
      (oblX2 x 3 - oblX2 x 5) • (x 2 - x 1) + (oblX6 x 3 - oblX6 x 5) • (x 6 - x 1) := by
    calc x 3 - x 5 = (x 3 - x 1) - (x 5 - x 1) := by abel
      _ = _ := by rw [hrep 3, hrep 5]; simp only [sub_smul]; abel
  have h61 : x 1 - x 6 = (0 : ℝ) • (x 0 - x 1) + (0 : ℝ) • (x 2 - x 1) + (-1 : ℝ) • (x 6 - x 1) := by
    simp only [zero_smul, zero_add, neg_smul, one_smul]; abel
  have h12 : x 2 - x 1 = (0 : ℝ) • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) := by simp
  dsimp only
  simp only [Matrix.cons_val]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · conv_lhs => rw [h12, h36, hw]
    rw [det3_frame]; ring
  · conv_lhs => arg 1; rw [h25]
    conv_lhs => arg 2; rw [h36]
    conv_lhs => arg 3; rw [hw]
    rw [det3_frame]; ring
  · conv_lhs => arg 1; rw [h53]
    conv_lhs => arg 2; rw [h36]
    conv_lhs => arg 3; rw [hw]
    rw [det3_frame]; ring
  · conv_lhs => arg 1; rw [h61]
    conv_lhs => arg 2; rw [h36]
    conv_lhs => arg 3; rw [hw]
    rw [det3_frame]; ring
  · conv_lhs => arg 1; rw [h25]
    conv_lhs => arg 2; rw [h12]
    conv_lhs => arg 3; rw [hw]
    rw [det3_frame]; ring
  · conv_lhs => arg 1; rw [h53]
    conv_lhs => arg 2; rw [h12]
    conv_lhs => arg 3; rw [hw]
    rw [det3_frame]; ring
  · conv_lhs => arg 1; rw [h36]
    conv_lhs => arg 2; rw [h12]
    conv_lhs => arg 3; rw [hw]
    rw [det3_frame]; ring
  · conv_lhs => arg 1; rw [h61]
    conv_lhs => arg 2; rw [h12]
    conv_lhs => arg 3; rw [hw]
    rw [det3_frame]; ring

/-! ### L5: Generic lex-triple `SplitAny24` packing lemma -/

theorem splitAny24_of_lex3 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    {k : ℕ} [NeZero k] (hk : 3 ≤ k) (c : ZMod k → Fin 7) (hc : Function.Injective c)
    (pat : Fin 9 → Bool) (hcyc : S0xCycOK s0x_S24 c pat)
    (b d1 d2 : ℝ³)
    (hfac : ∀ t : Fin 9,
      LexPos3 (if pat t then ⟪F.N t, b⟫ else -⟪F.N t, b⟫)
              (if pat t then ⟪F.N t, d1⟫ else -⟪F.N t, d1⟫)
              (if pat t then ⟪F.N t, d2⟫ else -⟪F.N t, d2⟫))
    (a cc : ZMod k) (hca : cc ≠ a) (hca1 : cc ≠ a + 1) (σ : ℝ)
    (hrows : ∀ i : ZMod k, i ≠ a → ∀ j : ZMod k, (j = i ∨ j = i + 1) → j ≠ cc →
      ∃ s : ℝ,
        LexPos3 (s * ⟪x (c j) - x (c cc), b⟫) (s * ⟪x (c j) - x (c cc), d1⟫)
                (s * ⟪x (c j) - x (c cc), d2⟫) ∧
        0 < σ * s * det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a)) b) :
    SplitAny24 F := by
  have hev_fac : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ t : Fin 9, 0 < (if pat t then ⟪F.N t, b + ε • d1 + ε ^ 2 • d2⟫ else
        -⟪F.N t, b + ε • d1 + ε ^ 2 • d2⟫) := by
    rw [eventually_all]
    intro t
    filter_upwards [ev_lexPos3 (hfac t)] with ε hε
    by_cases ht : pat t <;> simp only [ht, ↓reduceIte, Bool.false_eq_true] at hε ⊢ <;>
      simp only [inner_add_right, inner_smul_right] <;> linarith
  have hev_rows : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ i j : ZMod k, i ≠ a → (j = i ∨ j = i + 1) → j ≠ cc →
        0 < σ * (⟪x (c j) - x (c cc), b + ε • d1 + ε ^ 2 • d2⟫ *
          det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a))
            (b + ε • d1 + ε ^ 2 • d2)) := by
    rw [eventually_all]; intro i
    rw [eventually_all]; intro j
    by_cases hia : i ≠ a
    · by_cases hj : j = i ∨ j = i + 1
      · by_cases hjc : j ≠ cc
        · obtain ⟨s, hlex, hdet⟩ := hrows i hia j hj hjc
          have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
              0 < s * ⟪x (c j) - x (c cc), b + ε • d1 + ε ^ 2 • d2⟫ := by
            filter_upwards [ev_lexPos3 hlex] with ε hε
            simp only [inner_add_right, inner_smul_right]
            linarith
          have hc_det : Continuous fun ε : ℝ =>
              σ * s * det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a))
                (b + ε • d1 + ε ^ 2 • d2) := by
            simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
            fun_prop
          have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
              0 < σ * s * det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a))
                (b + ε • d1 + ε ^ 2 • d2) :=
            (hc_det.continuousAt.eventually (lt_mem_nhds (by simpa using hdet))).filter_mono
              nhdsWithin_le_nhds
          filter_upwards [h1, h2] with ε hε1 hε2 _ _ _
          have hs_ne : s ≠ 0 := by rintro rfl; simp at hdet
          have hprod : 0 < (s * ⟪x (c j) - x (c cc), b + ε • d1 + ε ^ 2 • d2⟫) *
              (σ * s * det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a))
                (b + ε • d1 + ε ^ 2 • d2)) := mul_pos hε1 hε2
          have hs2 : 0 < s * s := mul_self_pos.mpr hs_ne
          nlinarith
        · exact Eventually.of_forall fun _ _ _ h => absurd h hjc
      · exact Eventually.of_forall fun _ _ h => absurd h hj
    · exact Eventually.of_forall fun _ h => absurd h hia
  obtain ⟨ε, ⟨hfac_ε, hrows_ε⟩, _⟩ := ((hev_fac.and hev_rows).and self_mem_nhdsWithin).exists
  have hdet_eq : ∀ u v w : ℝ³, Minimality.Split.det3 u v w = Minimality.det3 u v w := by
    intro u v w
    simp [Minimality.Split.det3, Minimality.det3_expand, Minimality.Split.inner3,
      PiLp.inner_apply, Fin.sum_univ_three]
  refine ⟨k, inferInstance, c, pat, b + ε • d1 + ε ^ 2 • d2, 0, a, cc, σ, hk, hc, hcyc, ?_,
    hca, hca1, fun i j hia hj hjc => by
      simpa only [hdet_eq] using hrows_ε i j hia hj hjc⟩
  intro t
  have ht := hfac_ε t
  constructor
  · intro hpt; simp only [hpt, ↓reduceIte] at ht; exact Or.inl ht
  · intro hpt; simp only [hpt, Bool.false_eq_true, ↓reduceIte] at ht; exact Or.inl ht

/-! ### L6: Leaf packers at `w02` -/

theorem lexAny_R1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (d1 d2 : ℝ³)
    (hU : ∀ t ∈ ({5, 6, 7} : Finset (Fin 9)), LexPos3 ⟪F.N t, x 2 - x 0⟫ ⟪F.N t, d1⟫ ⟪F.N t, d2⟫)
    (hD : ∀ t ∈ ({0, 1, 2, 3, 8} : Finset (Fin 9)),
      LexPos3 (-⟪F.N t, x 2 - x 0⟫) (-⟪F.N t, d1⟫) (-⟪F.N t, d2⟫))
    (hR : RobUniLex (fun i : ZMod 5 =>
      let v := (![1, 2, 5, 3, 6] : ZMod 5 → Fin 7) i
      (⟪x v, x 2 - x 0⟫, ⟪x v, d1⟫, ⟪x v, d2⟫))) :
    LexAny F :=
  ⟨5, inferInstance, (![1, 2, 5, 3, 6] : ZMod 5 → Fin 7), {5, 6, 7}, {0, 1, 2, 3, 8},
    x 2 - x 0, d1, d2, by decide,
    (by intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)),
    (by unfold S0xCycUD; decide), hU, hD, hR⟩

theorem lexAny_R2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (h346 : F.f 8 (x 2) < F.f 8 (x 0))
    (hR : RobUniLex (fun i : ZMod 5 =>
      let v := (![1, 0, 5, 3, 6] : ZMod 5 → Fin 7) i
      (⟪x v, x 2 - x 0⟫, ⟪x v, 2 • x 2 - x 1 - x 5⟫, (0 : ℝ)))) :
    LexAny F := by
  have hw := w02_facings F h346
  refine ⟨5, inferInstance, (![1, 0, 5, 3, 6] : ZMod 5 → Fin 7), {0, 2, 5, 6, 7}, {1, 3, 8},
    x 2 - x 0, 2 • x 2 - x 1 - x 5, 0, by decide,
    (by intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)),
    (by unfold S0xCycUD; decide), ?_, ?_, by simpa only [inner_zero_right] using hR⟩
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · refine Or.inr ⟨hw.1, Or.inl ?_⟩
      have he : 2 • x 2 - x 1 - x 5 = (x 2 - x 1) + (x 2 - x 5) := by abel
      rw [he, inner_add_right, ← F.hN 0 (x 2) (x 1), ← F.hN 0 (x 2) (x 5),
        F.zero 0 2 (by decide), F.zero 0 1 (by decide)]
      linarith [F.neg 0 5 (by decide)]
    · refine Or.inr ⟨hw.2.2.1, Or.inl ?_⟩
      have he : 2 • x 2 - x 1 - x 5 = (x 2 - x 1) + (x 2 - x 5) := by abel
      rw [he, inner_add_right, ← F.hN 2 (x 2) (x 1), ← F.hN 2 (x 2) (x 5),
        F.zero 2 2 (by decide), F.zero 2 5 (by decide)]
      linarith [F.neg 2 1 (by decide)]
    · exact Or.inl hw.2.2.2.2.2.1
    · exact Or.inl hw.2.2.2.2.2.2.1
    · exact Or.inl hw.2.2.2.2.2.2.2.1
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact Or.inl (by linarith [hw.2.1])
    · exact Or.inl (by linarith [hw.2.2.2.1])
    · exact Or.inl (by linarith [hw.2.2.2.2.2.2.2.2])

private theorem hfac_R1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (h346 : F.f 8 (x 2) < F.f 8 (x 0)) (d2 : ℝ³) :
    let pat : Fin 9 → Bool := fun t => decide (t = 5 ∨ t = 6 ∨ t = 7)
    let dm : ℝ³ := x 5 + x 1 - 2 • x 2
    ∀ t : Fin 9,
      LexPos3 (if pat t then ⟪F.N t, x 2 - x 0⟫ else -⟪F.N t, x 2 - x 0⟫)
              (if pat t then ⟪F.N t, dm⟫ else -⟪F.N t, dm⟫)
              (if pat t then ⟪F.N t, d2⟫ else -⟪F.N t, d2⟫) := by
  have hw := w02_facings F h346
  intro pat dm t
  fin_cases t <;> simp [pat]
  · refine Or.inr ⟨by linarith [hw.1], Or.inl ?_⟩
    dsimp [dm]
    have e : -⟪F.N 0, x 5 + x 1 - 2 • x 2⟫ =
        -(⟪F.N 0, x 5 - x 2⟫ + ⟪F.N 0, x 1 - x 2⟫) := by
      simp only [inner_sub_right, inner_add_right, two_smul]; ring
    rw [e, ← F.hN 0 (x 5) (x 2), ← F.hN 0 (x 1) (x 2),
      F.zero 0 2 (by decide), F.zero 0 1 (by decide), sub_zero, sub_self, add_zero]
    linarith [F.neg 0 5 (by decide)]
  · exact Or.inl (by linarith [hw.2.1])
  · refine Or.inr ⟨by linarith [hw.2.2.1], Or.inl ?_⟩
    dsimp [dm]
    have e : -⟪F.N 2, x 5 + x 1 - 2 • x 2⟫ =
        -(⟪F.N 2, x 5 - x 2⟫ + ⟪F.N 2, x 1 - x 2⟫) := by
      simp only [inner_sub_right, inner_add_right, two_smul]; ring
    rw [e, ← F.hN 2 (x 5) (x 2), ← F.hN 2 (x 1) (x 2),
      F.zero 2 2 (by decide), F.zero 2 5 (by decide), sub_self, sub_zero, zero_add]
    linarith [F.neg 2 1 (by decide)]
  · exact Or.inl (by linarith [hw.2.2.2.1])
  · exact Or.inl (by linarith [hw.2.2.2.2.1])
  · exact Or.inl hw.2.2.2.2.2.1
  · exact Or.inl hw.2.2.2.2.2.2.1
  · exact Or.inl hw.2.2.2.2.2.2.2.1
  · exact Or.inl (by linarith [hw.2.2.2.2.2.2.2.2])

theorem split_R1_piv6_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (hc3 : oblX6 x 3 < 1) (h346 : F.f 8 (x 2) < F.f 8 (x 0))
    (h16 : LexPos3 (⟪x 6 - x 1, x 2 - x 0⟫)
                   (⟪x 6 - x 1, x 5 + x 1 - 2 • x 2⟫)
                   (⟪x 6 - x 1, x 6 - x 1⟫))
    (hz2 : ⟪x 6 - x 1, x 2 - x 0⟫ < ⟪x 2 - x 1, x 2 - x 0⟫)
    (hz5 : ⟪x 6 - x 1, x 2 - x 0⟫ < ⟪x 5 - x 1, x 2 - x 0⟫)
    (hz3 : ⟪x 6 - x 1, x 2 - x 0⟫ < ⟪x 3 - x 1, x 2 - x 0⟫) :
    SplitAny24 F := by
  have T := type24OfFac F
  have hconv := w02_convex F hC hc3 h346
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hd2 : 0 < det24 x * det24 x := mul_self_pos.mpr T.det_ne
  have hrows := w02_rows F
  dsimp only at hrows
  refine splitAny24_of_lex3 F (k := 5) (by decide) (![1, 2, 5, 3, 6] : ZMod 5 → Fin 7)
    (by intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide))
    (fun t => decide (t = 5 ∨ t = 6 ∨ t = 7)) (by unfold S0xCycOK; decide)
    (x 2 - x 0) (x 5 + x 1 - 2 • x 2) (x 6 - x 1) (hfac_R1 F h346 (x 6 - x 1))
    0 4 (by decide) (by decide) (det24 x) ?_
  intro i hia j hj hjc
  have hz26 : 0 < ⟪x 2 - x 6, x 2 - x 0⟫ := by
    rw [show x 2 - x 6 = (x 2 - x 1) - (x 6 - x 1) from by abel, inner_sub_left]; linarith
  have hz56 : 0 < ⟪x 5 - x 6, x 2 - x 0⟫ := by
    rw [show x 5 - x 6 = (x 5 - x 1) - (x 6 - x 1) from by abel, inner_sub_left]; linarith
  have hz36 : 0 < ⟪x 3 - x 6, x 2 - x 0⟫ := by
    rw [show x 3 - x 6 = (x 3 - x 1) - (x 6 - x 1) from by abel, inner_sub_left]; linarith
  have hi : ∀ i : ZMod 5, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by decide
  rcases hi i with rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hia
  · rcases hj with rfl | rfl
    · refine ⟨1, Or.inl (by simpa only [Matrix.cons_val, one_mul] using hz26), ?_⟩
      rw [show (1 : ZMod 5) + 1 = 2 from rfl, show (0 : ZMod 5) + 1 = 1 from rfl, hrows.2.2.2.2.1,
        show det24 x * 1 * (det24 x * oblX6 x 5) = (det24 x * det24 x) * oblX6 x 5 by ring]
      exact mul_pos hd2 hc5
    · refine ⟨1, Or.inl (by simpa only [Matrix.cons_val, show (1 : ZMod 5) + 1 = 2 from rfl,
          one_mul] using hz56), ?_⟩
      rw [show (1 : ZMod 5) + 1 = 2 from rfl, show (0 : ZMod 5) + 1 = 1 from rfl, hrows.2.2.2.2.1,
        show det24 x * 1 * (det24 x * oblX6 x 5) = (det24 x * det24 x) * oblX6 x 5 by ring]
      exact mul_pos hd2 hc5
  · rcases hj with rfl | rfl
    · refine ⟨1, Or.inl (by simpa only [Matrix.cons_val, one_mul] using hz56), ?_⟩
      rw [show (2 : ZMod 5) + 1 = 3 from rfl, show (0 : ZMod 5) + 1 = 1 from rfl, hrows.2.2.2.2.2.1,
        show det24 x * 1 * (det24 x * (oblX6 x 3 - oblX6 x 5)) =
          (det24 x * det24 x) * (oblX6 x 3 - oblX6 x 5) by ring]
      exact mul_pos hd2 (by linarith [hconv.2.2.2])
    · refine ⟨1, Or.inl (by simpa only [Matrix.cons_val, show (2 : ZMod 5) + 1 = 3 from rfl,
          one_mul] using hz36), ?_⟩
      rw [show (2 : ZMod 5) + 1 = 3 from rfl, show (0 : ZMod 5) + 1 = 1 from rfl, hrows.2.2.2.2.2.1,
        show det24 x * 1 * (det24 x * (oblX6 x 3 - oblX6 x 5)) =
          (det24 x * det24 x) * (oblX6 x 3 - oblX6 x 5) by ring]
      exact mul_pos hd2 (by linarith [hconv.2.2.2])
  · rcases hj with rfl | rfl
    · refine ⟨1, Or.inl (by simpa only [Matrix.cons_val, one_mul] using hz36), ?_⟩
      rw [show (3 : ZMod 5) + 1 = 4 from rfl, show (0 : ZMod 5) + 1 = 1 from rfl, hrows.2.2.2.2.2.2.1,
        show det24 x * 1 * (det24 x * (1 - oblX6 x 3)) =
          (det24 x * det24 x) * (1 - oblX6 x 3) by ring]
      exact mul_pos hd2 (by linarith)
    · exact absurd rfl hjc
  · rcases hj with rfl | rfl
    · exact absurd rfl hjc
    · refine ⟨-1, ?_, ?_⟩
      · simp only [Matrix.cons_val, show (4 : ZMod 5) + 1 = 0 from rfl, neg_mul, one_mul]
        have he1 : -(⟪x 1 - x 6, x 2 - x 0⟫) = ⟪x 6 - x 1, x 2 - x 0⟫ := by
          rw [← neg_sub, inner_neg_left, neg_neg]
        have he2 : -(⟪x 1 - x 6, x 5 + x 1 - 2 • x 2⟫) = ⟪x 6 - x 1, x 5 + x 1 - 2 • x 2⟫ := by
          rw [← neg_sub, inner_neg_left, neg_neg]
        have he3 : -(⟪x 1 - x 6, x 6 - x 1⟫) = ⟪x 6 - x 1, x 6 - x 1⟫ := by
          rw [← neg_sub, inner_neg_left, neg_neg]
        rw [he1, he2, he3]; exact h16
      · rw [show (4 : ZMod 5) + 1 = 0 from rfl, show (0 : ZMod 5) + 1 = 1 from rfl,
          hrows.2.2.2.2.2.2.2, show det24 x * -1 * (det24 x * -1) = det24 x * det24 x by ring]
        exact hd2

theorem split_R1_piv6 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (hc3 : oblX6 x 3 < 1) (h346 : F.f 8 (x 2) < F.f 8 (x 0))
    (hz6_pos : 0 < ⟪x 6 - x 1, x 2 - x 0⟫)
    (hz6_lt : ⟪x 6 - x 1, x 2 - x 0⟫ < min ⟪x 2 - x 1, x 2 - x 0⟫
      (min ⟪x 5 - x 1, x 2 - x 0⟫ ⟪x 3 - x 1, x 2 - x 0⟫)) :
    SplitAny24 F :=
  split_R1_piv6_lex F hC hc3 h346 (Or.inl hz6_pos)
    (lt_of_lt_of_le hz6_lt (min_le_left _ _))
    (lt_of_lt_of_le hz6_lt (le_trans (min_le_right _ _) (min_le_left _ _)))
    (lt_of_lt_of_le hz6_lt (le_trans (min_le_right _ _) (min_le_right _ _)))

theorem split_R1_piv1_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (hc3 : oblX6 x 3 < 1) (h346 : F.f 8 (x 2) < F.f 8 (x 0))
    (hz2_pos : 0 < ⟪x 2 - x 1, x 2 - x 0⟫)
    (hz5_pos : 0 < ⟪x 5 - x 1, x 2 - x 0⟫)
    (hz3_pos : 0 < ⟪x 3 - x 1, x 2 - x 0⟫)
    (hz6_lex : LexPos3 (-⟪x 6 - x 1, x 2 - x 0⟫)
                       (-⟪x 6 - x 1, x 5 + x 1 - 2 • x 2⟫)
                       (-⟪x 6 - x 1, x 6 - x 1⟫)) :
    SplitAny24 F := by
  have T := type24OfFac F
  have hconv := w02_convex F hC hc3 h346
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hY3 : 0 < oblX0 x 3 + oblX2 x 3 :=
    add_pos (T.X0_pos (v := 3) (by decide)) (T.X2_pos (v := 3) (by decide))
  have hd2 : 0 < det24 x * det24 x := mul_self_pos.mpr T.det_ne
  have hrows := w02_rows F
  dsimp only at hrows
  refine splitAny24_of_lex3 F (k := 5) (by decide) (![1, 2, 5, 3, 6] : ZMod 5 → Fin 7)
    (by intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide))
    (fun t => decide (t = 5 ∨ t = 6 ∨ t = 7)) (by unfold S0xCycOK; decide)
    (x 2 - x 0) (x 5 + x 1 - 2 • x 2) (x 6 - x 1) (hfac_R1 F h346 (x 6 - x 1))
    3 0 (by decide) (by decide) (-det24 x) ?_
  intro i hia j hj hjc
  have hi : ∀ i : ZMod 5, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by decide
  rcases hi i with rfl | rfl | rfl | rfl | rfl
  · rcases hj with rfl | rfl
    · exact absurd rfl hjc
    · refine ⟨1, Or.inl (by simpa only [Matrix.cons_val, show (0 : ZMod 5) + 1 = 1 from rfl,
          one_mul] using hz2_pos), ?_⟩
      rw [show (0 : ZMod 5) + 1 = 1 from rfl, show (3 : ZMod 5) + 1 = 4 from rfl, hrows.1,
        show -det24 x * 1 * (det24 x * -(1 - oblX6 x 3)) =
          (det24 x * det24 x) * (1 - oblX6 x 3) by ring]
      exact mul_pos hd2 (by linarith)
  · rcases hj with rfl | rfl
    · refine ⟨1, Or.inl (by simpa only [Matrix.cons_val, one_mul] using hz2_pos), ?_⟩
      rw [show (1 : ZMod 5) + 1 = 2 from rfl, show (3 : ZMod 5) + 1 = 4 from rfl, hrows.2.1,
        show -det24 x * 1 * (det24 x * (-oblX6 x 5 * (oblX0 x 3 + oblX2 x 3) -
          (1 - oblX6 x 3) * (oblX0 x 5 + oblX2 x 5 - 1))) =
          (det24 x * det24 x) * (oblX6 x 5 * (oblX0 x 3 + oblX2 x 3) +
          (1 - oblX6 x 3) * (oblX0 x 5 + oblX2 x 5 - 1)) by ring]
      exact mul_pos hd2 (add_pos (mul_pos hc5 hY3) (mul_pos (by linarith) (by linarith [hconv.1])))
    · refine ⟨1, Or.inl (by simpa only [Matrix.cons_val, show (1 : ZMod 5) + 1 = 2 from rfl,
          one_mul] using hz5_pos), ?_⟩
      rw [show (1 : ZMod 5) + 1 = 2 from rfl, show (3 : ZMod 5) + 1 = 4 from rfl, hrows.2.1,
        show -det24 x * 1 * (det24 x * (-oblX6 x 5 * (oblX0 x 3 + oblX2 x 3) -
          (1 - oblX6 x 3) * (oblX0 x 5 + oblX2 x 5 - 1))) =
          (det24 x * det24 x) * (oblX6 x 5 * (oblX0 x 3 + oblX2 x 3) +
          (1 - oblX6 x 3) * (oblX0 x 5 + oblX2 x 5 - 1)) by ring]
      exact mul_pos hd2 (add_pos (mul_pos hc5 hY3) (mul_pos (by linarith) (by linarith [hconv.1])))
  · rcases hj with rfl | rfl
    · refine ⟨1, Or.inl (by simpa only [Matrix.cons_val, one_mul] using hz5_pos), ?_⟩
      rw [show (2 : ZMod 5) + 1 = 3 from rfl, show (3 : ZMod 5) + 1 = 4 from rfl, hrows.2.2.1,
        show -det24 x * 1 * (det24 x * -((1 - oblX6 x 5) * (oblX0 x 3 + oblX2 x 3) -
          (1 - oblX6 x 3) * (oblX0 x 5 + oblX2 x 5))) =
          (det24 x * det24 x) * ((1 - oblX6 x 5) * (oblX0 x 3 + oblX2 x 3) -
          (1 - oblX6 x 3) * (oblX0 x 5 + oblX2 x 5)) by ring]
      exact mul_pos hd2 hconv.2.1
    · refine ⟨1, Or.inl (by simpa only [Matrix.cons_val, show (2 : ZMod 5) + 1 = 3 from rfl,
          one_mul] using hz3_pos), ?_⟩
      rw [show (2 : ZMod 5) + 1 = 3 from rfl, show (3 : ZMod 5) + 1 = 4 from rfl, hrows.2.2.1,
        show -det24 x * 1 * (det24 x * -((1 - oblX6 x 5) * (oblX0 x 3 + oblX2 x 3) -
          (1 - oblX6 x 3) * (oblX0 x 5 + oblX2 x 5))) =
          (det24 x * det24 x) * ((1 - oblX6 x 5) * (oblX0 x 3 + oblX2 x 3) -
          (1 - oblX6 x 3) * (oblX0 x 5 + oblX2 x 5)) by ring]
      exact mul_pos hd2 hconv.2.1
  · exact absurd rfl hia
  · rcases hj with rfl | rfl
    · refine ⟨-1, ?_, ?_⟩
      · simp only [Matrix.cons_val, neg_mul, one_mul]
        exact hz6_lex
      · rw [show (4 : ZMod 5) + 1 = 0 from rfl, show (3 : ZMod 5) + 1 = 4 from rfl, hrows.2.2.2.1,
          show -det24 x * -1 * (det24 x * (oblX0 x 3 + oblX2 x 3)) =
            (det24 x * det24 x) * (oblX0 x 3 + oblX2 x 3) by ring]
        exact mul_pos hd2 hY3
    · exact absurd rfl hjc

theorem split_R1_piv1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (hc3 : oblX6 x 3 < 1) (h346 : F.f 8 (x 2) < F.f 8 (x 0))
    (hz2_pos : 0 < ⟪x 2 - x 1, x 2 - x 0⟫)
    (hz5_pos : 0 < ⟪x 5 - x 1, x 2 - x 0⟫)
    (hz3_pos : 0 < ⟪x 3 - x 1, x 2 - x 0⟫)
    (hz6_neg : ⟪x 6 - x 1, x 2 - x 0⟫ < 0) :
    SplitAny24 F :=
  split_R1_piv1_lex F hC hc3 h346 hz2_pos hz5_pos hz3_pos (Or.inl (by linarith))

/-! ### L7: ZMod 5 `RobUniLex` lemmas (including gap G1 fix) -/

theorem robUni5_caseA (z : Fin 7 → ℝ) (d1 : Fin 7 → ℝ)
    (hz12 : z 1 < z 2) (hz31 : z 3 ≤ z 1) (hz6 : z 6 < z 3) (hz5 : z 3 < z 5) :
    RobUniLex (fun i : ZMod 5 =>
      let v := (![1, 2, 5, 3, 6] : ZMod 5 → Fin 7) i
      (z v, d1 v, (0 : ℝ))) := by
  intro B b c d hb hbc hcd hd
  have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by revert B; decide
  have hbcd : (b = 1 ∧ c = 2 ∧ d = 3) ∨ (b = 1 ∧ c = 2 ∧ d = 4) ∨
      (b = 1 ∧ c = 3 ∧ d = 4) ∨ (b = 2 ∧ c = 3 ∧ d = 4) := by omega
  rcases hB with rfl | rfl | rfl | rfl | rfl <;>
    rcases hbcd with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    simp only [Nat.cast_one, Nat.cast_ofNat, Matrix.cons_val,
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

theorem robUni5_caseB (z : Fin 7 → ℝ) (d1 d2 : Fin 7 → ℝ)
    (hz12 : z 1 < z 2) (hz5 : z 2 ≤ z 5) (hz6a : z 2 ≤ z 6) (hz6b : z 6 < z 3)
    (hd : z 5 = z 2 → d1 2 < d1 5) :
    RobUniLex (fun i : ZMod 5 =>
      let v := (![1, 2, 5, 3, 6] : ZMod 5 → Fin 7) i
      (z v, d1 v, d2 v)) := by
  intro B b c d hb hbc hcd hd'
  have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by revert B; decide
  have hbcd : (b = 1 ∧ c = 2 ∧ d = 3) ∨ (b = 1 ∧ c = 2 ∧ d = 4) ∨
      (b = 1 ∧ c = 3 ∧ d = 4) ∨ (b = 2 ∧ c = 3 ∧ d = 4) := by omega
  have h25 : LexLt3 (z 2, d1 2, d2 2) (z 5, d1 5, d2 5) := by
    rcases eq_or_lt_of_le hz5 with h | h
    · exact Or.inr ⟨sub_eq_zero.mpr h.symm, Or.inl (sub_pos.mpr (hd h.symm))⟩
    · exact Or.inl (sub_pos.mpr h)
  rcases hB with rfl | rfl | rfl | rfl | rfl <;>
    rcases hbcd with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    simp only [Nat.cast_one, Nat.cast_ofNat, Matrix.cons_val,
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
    | exact Or.inl h25
    | exact Or.inr (Or.inl h25)
    | exact Or.inr (Or.inr (Or.inl h25))
    | exact Or.inr (Or.inr (Or.inr h25))
    | exact Or.inl (Or.inl (by linarith))
    | exact Or.inr (Or.inl (Or.inl (by linarith)))
    | exact Or.inr (Or.inr (Or.inl (Or.inl (by linarith))))
    | exact Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))

theorem robUni5_unimodal (z : ZMod 5 → ℝ) (d1 : ZMod 5 → ℝ)
    (h01 : z 0 < z 1) (h12 : z 1 < z 2) (h23 : z 2 < z 3) (h43 : z 4 < z 3) (h04 : z 0 < z 4) :
    RobUniLex (fun i => (z i, d1 i, (0 : ℝ))) := by
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
    | exact Or.inl (Or.inl (by linarith))
    | exact Or.inr (Or.inl (Or.inl (by linarith)))
    | exact Or.inr (Or.inr (Or.inl (Or.inl (by linarith))))
    | exact Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))

/-! ### L8: `w02` dichotomy -/

theorem w02_dichotomy {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (hab : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0)
    (hc3 : oblX6 x 3 < 1) (h346 : F.f 8 (x 2) < F.f 8 (x 0))
    (hL : ¬ LexAny F) (hS : ¬ SplitAny24 F) :
    oblX6 x 3 * ⟪x 5 - x 1, x 2 - x 0⟫ ≤ oblX6 x 5 * ⟪x 3 - x 1, x 2 - x 0⟫ ∨
      ⟪x 3 - x 1, x 2 - x 0⟫ ≤ ⟪x 6 - x 1, x 2 - x 0⟫ := by
  by_contra hcon
  push Not at hcon
  rcases hcon with ⟨h35, hz63⟩
  have T := type24OfFac F
  have hconv := w02_convex F hC hc3 h346
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hc3_pos : 0 < oblX6 x 3 := T.X6_pos (v := 3) (by decide)
  have hz1 : ⟪x 1 - x 1, x 2 - x 0⟫ = 0 := by simp
  have hx21_pos : 0 < ⟪x 2 - x 1, x 2 - x 1⟫ :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide))
  have hx01_pos : 0 < ⟪x 0 - x 1, x 0 - x 1⟫ :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide))
  have hz2_pos : 0 < ⟪x 2 - x 1, x 2 - x 0⟫ := by
    have e : x 2 - x 0 = (x 2 - x 1) - (x 0 - x 1) := by abel
    rw [e, inner_sub_right]
    linarith [real_inner_comm (x 0 - x 1) (x 2 - x 1)]
  have hz0_neg : ⟪x 0 - x 1, x 2 - x 0⟫ < 0 := by
    have e : x 2 - x 0 = (x 2 - x 1) - (x 0 - x 1) := by abel
    rw [e, inner_sub_right]
    linarith
  let z : Fin 7 → ℝ := fun v => ⟪x v - x 1, x 2 - x 0⟫
  have hz_shift : ∀ v : Fin 7, ⟪x v, x 2 - x 0⟫ = z v + ⟪x 1, x 2 - x 0⟫ := by
    intro v; dsimp [z]; rw [inner_sub_left]; ring
  rcases le_or_gt (z 3) 0 with hz3 | hz3
  · -- Case `z 3 ≤ 0`: `z 5 > z 3`, `lexAny_R1` + `robUni5_caseA`.
    have hz5 : z 3 < z 5 := by
      have : oblX6 x 3 * z 3 ≤ oblX6 x 5 * z 3 :=
        mul_le_mul_of_nonpos_right hconv.2.2.2.le hz3
      nlinarith
    apply hL
    let dm : ℝ³ := x 5 + x 1 - 2 • x 2
    refine lexAny_R1 F dm 0 ?_ ?_ ?_
    · intro t ht
      have hw := w02_facings F h346
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact Or.inl hw.2.2.2.2.2.1
      · exact Or.inl hw.2.2.2.2.2.2.1
      · exact Or.inl hw.2.2.2.2.2.2.2.1
    · intro t ht
      have hw := w02_facings F h346
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl
      · refine Or.inr ⟨by linarith [hw.1], Or.inl ?_⟩
        dsimp [dm]
        have e : -⟪F.N 0, x 5 + x 1 - 2 • x 2⟫ =
            -(⟪F.N 0, x 5 - x 2⟫ + ⟪F.N 0, x 1 - x 2⟫) := by
          simp only [inner_sub_right, inner_add_right, two_smul]; ring
        rw [e, ← F.hN 0 (x 5) (x 2), ← F.hN 0 (x 1) (x 2),
          F.zero 0 2 (by decide), F.zero 0 1 (by decide), sub_zero, sub_self, add_zero]
        linarith [F.neg 0 5 (by decide)]
      · exact Or.inl (by linarith [hw.2.1])
      · refine Or.inr ⟨by linarith [hw.2.2.1], Or.inl ?_⟩
        dsimp [dm]
        have e : -⟪F.N 2, x 5 + x 1 - 2 • x 2⟫ =
            -(⟪F.N 2, x 5 - x 2⟫ + ⟪F.N 2, x 1 - x 2⟫) := by
          simp only [inner_sub_right, inner_add_right, two_smul]; ring
        rw [e, ← F.hN 2 (x 5) (x 2), ← F.hN 2 (x 1) (x 2),
          F.zero 2 2 (by decide), F.zero 2 5 (by decide), sub_self, sub_zero, zero_add]
        linarith [F.neg 2 1 (by decide)]
      · exact Or.inl (by linarith [hw.2.2.2.1])
      · exact Or.inl (by linarith [hw.2.2.2.2.2.2.2.2])
    · have h := robUni5_caseA (fun v => z v + ⟪x 1, x 2 - x 0⟫)
        (fun v => ⟪x v, dm⟫) (by linarith) (by linarith) (by linarith) (by linarith)
      simp only [← hz_shift] at h
      simpa only [inner_zero_right] using h
  · -- Case `0 < z 3`:
    have hz5_pos : 0 < z 5 := by nlinarith
    rcases lt_trichotomy (z 6) 0 with hz6 | hz6 | hz6
    · exact absurd (split_R1_piv1 F hC hc3 h346 hz2_pos hz5_pos hz3 hz6) hS
    · -- `z 6 = 0`: tie-break with `d2 = x 6 - x 1`.
      have hx61_pos : 0 < ⟪x 6 - x 1, x 6 - x 1⟫ :=
        real_inner_self_pos.mpr (sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide))
      rcases le_or_gt 0 ⟪x 6 - x 1, x 5 + x 1 - 2 • x 2⟫ with hdm | hdm
      · have h16 : LexPos3 (z 6) ⟪x 6 - x 1, x 5 + x 1 - 2 • x 2⟫ ⟪x 6 - x 1, x 6 - x 1⟫ := by
          rcases eq_or_lt_of_le hdm with h0 | hpos
          · exact Or.inr ⟨hz6, Or.inr ⟨h0.symm, hx61_pos⟩⟩
          · exact Or.inr ⟨hz6, Or.inl hpos⟩
        exact absurd (split_R1_piv6_lex F hC hc3 h346 h16 (by linarith) (by linarith) (by linarith)) hS
      · exact absurd (split_R1_piv1_lex F hC hc3 h346 hz2_pos hz5_pos hz3
          (Or.inr ⟨by linarith, Or.inl (by linarith)⟩)) hS
    · rcases lt_or_ge (z 6) (min (z 2) (min (z 5) (z 3))) with hz6_lt | hz6_ge
      · exact absurd (split_R1_piv6 F hC hc3 h346 hz6 hz6_lt) hS
      · have hmin : min (z 2) (z 5) ≤ z 6 := by
          rcases le_total (z 2) (min (z 5) (z 3)) with h | h
          · rw [min_eq_left h] at hz6_ge
            exact le_trans (min_le_left _ _) hz6_ge
          · rw [min_eq_right h] at hz6_ge
            rcases le_total (z 5) (z 3) with h53 | h35'
            · rw [min_eq_left h53] at hz6_ge
              exact le_trans (min_le_right _ _) hz6_ge
            · rw [min_eq_right h35'] at hz6_ge
              exact absurd hz6_ge (not_le_of_gt hz63)
        rcases le_or_gt (z 2) (z 5) with hz25 | hz52
        · -- `z 2 ≤ z 6 < z 3`, `z 2 ≤ z 5`: `lexAny_R1` with `(x 5 - x 2, x 1 - x 2)`.
          have hz26 : z 2 ≤ z 6 := le_trans (le_min (le_refl _) hz25) hmin
          apply hL
          refine lexAny_R1 F (x 5 - x 2) (x 1 - x 2) ?_ ?_ ?_
          · intro t ht
            have hw := w02_facings F h346
            simp only [Finset.mem_insert, Finset.mem_singleton] at ht
            rcases ht with rfl | rfl | rfl
            · exact Or.inl hw.2.2.2.2.2.1
            · exact Or.inl hw.2.2.2.2.2.2.1
            · exact Or.inl hw.2.2.2.2.2.2.2.1
          · intro t ht
            have hw := w02_facings F h346
            simp only [Finset.mem_insert, Finset.mem_singleton] at ht
            rcases ht with rfl | rfl | rfl | rfl | rfl
            · refine Or.inr ⟨by linarith [hw.1], Or.inl ?_⟩
              rw [← F.hN 0 (x 5) (x 2), F.zero 0 2 (by decide), sub_zero]
              linarith [F.neg 0 5 (by decide)]
            · exact Or.inl (by linarith [hw.2.1])
            · refine Or.inr ⟨by linarith [hw.2.2.1], Or.inr ⟨?_, ?_⟩⟩
              · rw [← F.hN 2 (x 5) (x 2), F.zero 2 5 (by decide), F.zero 2 2 (by decide), sub_self, neg_zero]
              · rw [← F.hN 2 (x 1) (x 2), F.zero 2 2 (by decide), sub_zero]
                linarith [F.neg 2 1 (by decide)]
            · exact Or.inl (by linarith [hw.2.2.2.1])
            · exact Or.inl (by linarith [hw.2.2.2.2.2.2.2.2])
          · have hx52 : 0 < ⟪x 5 - x 2, x 5 - x 2⟫ :=
              real_inner_self_pos.mpr (sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide))
            have hd25 : ⟪x 2, x 5 - x 2⟫ < ⟪x 5, x 5 - x 2⟫ := by
              rw [← sub_pos, ← inner_sub_left]; exact hx52
            have h := robUni5_caseB (fun v => z v + ⟪x 1, x 2 - x 0⟫)
              (fun v => ⟪x v, x 5 - x 2⟫) (fun v => ⟪x v, x 1 - x 2⟫)
              (by linarith) (by linarith) (by linarith) (by linarith)
              (fun _ => hd25)
            simp only [← hz_shift] at h
            exact h
        · -- `z 5 < z 2`, `z 5 ≤ z 6 < z 3`: `lexAny_R2` with `z(0) < z(1) < z(5) < z(3)` and `z(1) < z(6) < z(3)`.
          have hz56 : z 5 ≤ z 6 := by
            rw [min_eq_right (le_of_lt hz52)] at hmin
            exact hmin
          apply hL
          refine lexAny_R2 F h346 ?_
          intro B b c d hb hbc hcd hd
          have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by revert B; decide
          have hbcd : (b = 1 ∧ c = 2 ∧ d = 3) ∨ (b = 1 ∧ c = 2 ∧ d = 4) ∨
              (b = 1 ∧ c = 3 ∧ d = 4) ∨ (b = 2 ∧ c = 3 ∧ d = 4) := by omega
          rcases hB with rfl | rfl | rfl | rfl | rfl <;>
            rcases hbcd with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
            simp only [Nat.cast_one, Nat.cast_ofNat, Matrix.cons_val,
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
            | exact Or.inl (Or.inl (by dsimp only; linarith [hz_shift 0, hz_shift 1, hz_shift 5, hz_shift 3, hz_shift 6]))
            | exact Or.inr (Or.inl (Or.inl (by dsimp only; linarith [hz_shift 0, hz_shift 1, hz_shift 5, hz_shift 3, hz_shift 6])))
            | exact Or.inr (Or.inr (Or.inl (Or.inl (by dsimp only; linarith [hz_shift 0, hz_shift 1, hz_shift 5, hz_shift 3, hz_shift 6]))))
            | exact Or.inr (Or.inr (Or.inr (Or.inl (by dsimp only; linarith [hz_shift 0, hz_shift 1, hz_shift 5, hz_shift 3, hz_shift 6]))))

/-! ### L9: U-Q4 bound at `u07 = (x 0 - x 1) + omega3 x • (x 2 - x 1)` -/

theorem u07_bound {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (hc3 : oblX6 x 3 < 1) (hL : ¬ LexAny F) :
    0 ≤ omega3 x * ⟪x 2 - x 1, x 2 - x 0⟫ - (-⟪x 0 - x 1, x 2 - x 0⟫) := by
  by_contra hcon
  push Not at hcon
  have T := type24OfFac F
  have hom3 : 0 < omega3 x := hC.1
  have hom4 : 0 < omega4 x := hC.2.1
  have hom34 : 1 < omega3 x * omega4 x :=
    Minimality.omega_prod_gt_one hC.1 hC.2.1 hC.2.2.1 hC.2.2.2
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hc3_pos : 0 < oblX6 x 3 := T.X6_pos (v := 3) (by decide)
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hc4 : 0 < oblX6 x 4 := T.X6_pos (v := 4) (by decide)
  let u07 : ℝ³ := (x 0 - x 1) + omega3 x • (x 2 - x 1)
  have hz20 : ⟪x 2 - x 0, u07⟫ < 0 := by
    have e : ⟪x 2 - x 0, u07⟫ = omega3 x * ⟪x 2 - x 1, x 2 - x 0⟫ - (-⟪x 0 - x 1, x 2 - x 0⟫) := by
      dsimp [u07]
      rw [inner_add_right, inner_smul_right,
        real_inner_comm (x 2 - x 0) (x 0 - x 1), real_inner_comm (x 2 - x 0) (x 2 - x 1)]
      ring
    linarith
  have hu07_ne : u07 ≠ 0 := by
    intro h0; rw [h0, inner_zero_right] at hz20; exact lt_irrefl _ hz20
  -- Facings at `(u07, x 6 - x 1, 0)` on `c := ![0, 2, 6, 4]`, `U := {2, 3, 7, 8}`, `Dn := {0, 4, 5}`:
  have hu0 : ⟪F.N 0, u07⟫ = 0 := by
    dsimp [u07]
    rw [inner_add_right, inner_smul_right, ← F.hN 0 (x 0) (x 1), ← F.hN 0 (x 2) (x 1),
      F.zero 0 0 (by decide), F.zero 0 1 (by decide), F.zero 0 2 (by decide)]
    ring
  have hu7 : ⟪F.N 7, u07⟫ = 0 := by
    have ev := fac_eval F 7 3
    rw [F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at ev
    have e3 := eq3 F
    have hprod : oblX0 x 3 * ⟪F.N 7, u07⟫ = 0 := by
      dsimp [u07]
      rw [inner_add_right, inner_smul_right, ← F.hN 7 (x 0) (x 1), ← F.hN 7 (x 2) (x 1),
        F.zero 7 2 (by decide)]
      linear_combination -ev + F.f 7 (x 1) * e3
    exact (mul_eq_zero.mp hprod).resolve_left ha3.ne'
  have hu2 : 0 < ⟪F.N 2, u07⟫ := by
    dsimp [u07]
    rw [inner_add_right, inner_smul_right, ← F.hN 2 (x 0) (x 1), ← F.hN 2 (x 2) (x 1),
      F.zero 2 0 (by decide), F.zero 2 2 (by decide)]
    have : 0 < -F.f 2 (x 1) := by linarith [F.neg 2 1 (by decide)]
    nlinarith
  have hu3 : 0 < ⟪F.N 3, u07⟫ := by
    have ev := fac_eval F 3 3
    rw [F.zero 3 3 (by decide), F.zero 3 0 (by decide)] at ev
    have e3 := eq3 F
    have hprod : oblX0 x 3 * ⟪F.N 3, u07⟫ =
        (oblX6 x 3 - 1) * F.f 3 (x 2) - oblX6 x 3 * F.f 3 (x 6) := by
      dsimp [u07]
      rw [inner_add_right, inner_smul_right, ← F.hN 3 (x 0) (x 1), ← F.hN 3 (x 2) (x 1),
        F.zero 3 0 (by decide)]
      linear_combination -ev + (F.f 3 (x 1) - F.f 3 (x 2)) * e3
    have hpos : 0 < (oblX6 x 3 - 1) * F.f 3 (x 2) - oblX6 x 3 * F.f 3 (x 6) := by
      have h32 : F.f 3 (x 2) < 0 := F.neg 3 2 (by decide)
      have h36 : F.f 3 (x 6) < 0 := F.neg 3 6 (by decide)
      nlinarith
    rw [← hprod] at hpos
    exact pos_of_mul_pos_right hpos ha3.le
  have hu8 : 0 < ⟪F.N 8, u07⟫ := by
    have ev := fac_eval F 8 3
    rw [F.zero 8 3 (by decide), F.zero 8 6 (by decide)] at ev
    have e3 := eq3 F
    have hprod : oblX0 x 3 * ⟪F.N 8, u07⟫ = (oblX6 x 3 - 1) * F.f 8 (x 2) := by
      dsimp [u07]
      rw [inner_add_right, inner_smul_right, ← F.hN 8 (x 0) (x 1), ← F.hN 8 (x 2) (x 1)]
      linear_combination -ev + (F.f 8 (x 1) - F.f 8 (x 2)) * e3
    have hpos : 0 < (oblX6 x 3 - 1) * F.f 8 (x 2) :=
      mul_pos_of_neg_of_neg (by linarith) (F.neg 8 2 (by decide))
    rw [← hprod] at hpos
    exact pos_of_mul_pos_right hpos ha3.le
  have hu4 : ⟪F.N 4, u07⟫ < 0 := by
    have ev := fac_eval F 4 4
    rw [F.zero 4 4 (by decide), F.zero 4 0 (by decide), F.zero 4 6 (by decide)] at ev
    have e4 := eq4 F
    have hprod : oblX2 x 4 * ⟪F.N 4, u07⟫ =
        oblX2 x 4 * F.f 4 (x 1) * (omega3 x * omega4 x - 1) := by
      dsimp [u07]
      rw [inner_add_right, inner_smul_right, ← F.hN 4 (x 0) (x 1), ← F.hN 4 (x 2) (x 1),
        F.zero 4 0 (by decide)]
      linear_combination -omega3 x * ev + omega3 x * F.f 4 (x 1) * e4
    have hneg : oblX2 x 4 * F.f 4 (x 1) * (omega3 x * omega4 x - 1) < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hb4 (F.neg 4 1 (by decide))) (by linarith)
    rw [← hprod] at hneg
    by_contra h; push Not at h
    nlinarith [mul_nonneg hb4.le h]
  have hu5 : ⟪F.N 5, u07⟫ < 0 := by
    dsimp [u07]
    rw [inner_add_right, inner_smul_right, ← F.hN 5 (x 0) (x 1), ← F.hN 5 (x 2) (x 1),
      F.zero 5 1 (by decide), F.zero 5 2 (by decide), sub_zero, sub_self, mul_zero, add_zero]
    exact F.neg 5 0 (by decide)
  -- Front diagonal `24` over `06` at `u07`:
  set den : ℝ := (1 + omega3 x) + oblX2 x 4 * (omega3 x * omega4 x - 1)
  have hden_pos : 0 < den := by
    dsimp [den]; nlinarith [mul_pos hb4 (show 0 < omega3 x * omega4 x - 1 by linarith)]
  set s : ℝ := (1 + omega3 x) / den
  set t : ℝ := s * oblX6 x 4
  set γ : ℝ := oblX2 x 4 * (1 + omega4 x) / den
  have hs0 : 0 < s := div_pos (by linarith) hden_pos
  have hs1 : s < 1 := by
    rw [div_lt_one hden_pos]
    dsimp [den]; nlinarith [mul_pos hb4 (show 0 < omega3 x * omega4 x - 1 by linarith)]
  have ht0 : 0 < t := mul_pos hs0 hc4
  have ht1 : t < 1 := by
    have h236_4 : oblX2 x 4 + oblX6 x 4 - omega3 x * oblX0 x 4 < 1 := by
      have ev := fac_eval F 7 4
      rw [F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at ev
      have e3 := eq3 F
      have h70 : F.f 7 (x 0) - F.f 7 (x 1) = omega3 x * F.f 7 (x 1) := by
        have ev3 := fac_eval F 7 3
        rw [F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at ev3
        have : oblX0 x 3 * ((F.f 7 (x 0) - F.f 7 (x 1)) - omega3 x * F.f 7 (x 1)) = 0 := by
          linear_combination -ev3 + F.f 7 (x 1) * e3
        exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ha3.ne')
      have h71 : 0 < -F.f 7 (x 1) := by linarith [F.neg 7 1 (by decide)]
      have hprod : (-F.f 7 (x 1)) * (oblX2 x 4 + oblX6 x 4 - omega3 x * oblX0 x 4 - 1) = F.f 7 (x 4) := by
        rw [ev, h70]; ring
      nlinarith [F.neg 7 4 (by decide)]
    -- From `h236_4` and `eq4 F`: `(1 + omega3) * c4 < (1 + omega3) + b4 * (omega3 * omega4 - 1) = den`!
    have hlt_den : (1 + omega3 x) * oblX6 x 4 < den := by
      have := eq4 F
      dsimp [den]
      nlinarith
    dsimp [t, s]
    rw [div_mul_eq_mul_div, div_lt_one hden_pos]
    exact hlt_den
  have hγ0 : 0 < γ := div_pos (mul_pos hb4 (by linarith)) hden_pos
  have hdiag_vec : (x 2 + s • (x 4 - x 2)) - (x 0 + t • (x 6 - x 0)) = γ • u07 := by
    have hrep4 : x 4 - x 1 = oblX0 x 4 • (x 0 - x 1) + oblX2 x 4 • (x 2 - x 1) +
        oblX6 x 4 • (x 6 - x 1) := by rw [T.rep 4]; abel
    have hshift : (x 2 + s • (x 4 - x 2)) - (x 0 + t • (x 6 - x 0)) =
        (1 - s) • (x 2 - x 1) + s • (x 4 - x 1) - (1 - t) • (x 0 - x 1) - t • (x 6 - x 1) := by
      simp only [sub_smul, one_smul, smul_sub]; abel
    rw [hshift, hrep4]
    have e4 := eq4 F
    have hden_ne : den ≠ 0 := hden_pos.ne'
    have c0 : s * oblX0 x 4 - (1 - t) = γ := by
      dsimp [s, t, γ]
      field_simp [hden_ne]
      dsimp [den]
      linear_combination (1 + omega3 x) * e4
    have c2 : (1 - s) + s * oblX2 x 4 = γ * omega3 x := by
      dsimp [s, γ]
      field_simp [hden_ne]
      dsimp [den]; ring
    have c6 : s * oblX6 x 4 - t = 0 := by dsimp [t]; ring
    dsimp [u07]
    calc (1 - s) • (x 2 - x 1) +
          s • (oblX0 x 4 • (x 0 - x 1) + oblX2 x 4 • (x 2 - x 1) + oblX6 x 4 • (x 6 - x 1)) -
          (1 - t) • (x 0 - x 1) - t • (x 6 - x 1)
        = (s * oblX0 x 4 - (1 - t)) • (x 0 - x 1) + ((1 - s) + s * oblX2 x 4) • (x 2 - x 1) +
          (s * oblX6 x 4 - t) • (x 6 - x 1) := by
          simp only [smul_add, smul_smul, add_smul, sub_smul]; abel
      _ = γ • (x 0 - x 1) + (γ * omega3 x) • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) := by
          rw [c0, c2, c6]
      _ = γ • ((x 0 - x 1) + omega3 x • (x 2 - x 1)) := by
          simp only [zero_smul, add_zero, smul_add, smul_smul]
  -- Take inner product with `u07`:
  have hdiag_pos : 0 < (1 - s) * (1 - t) * (⟪x 2, u07⟫ - ⟪x 0, u07⟫) +
      (1 - s) * t * (⟪x 2, u07⟫ - ⟪x 6, u07⟫) +
      s * (1 - t) * (⟪x 4, u07⟫ - ⟪x 0, u07⟫) +
      s * t * (⟪x 4, u07⟫ - ⟪x 6, u07⟫) := by
    have hinner := congrArg (fun w => ⟪w, u07⟫) hdiag_vec
    have hrhs : 0 < ⟪γ • u07, u07⟫ := by
      rw [real_inner_smul_left]
      exact mul_pos hγ0 (real_inner_self_pos.mpr hu07_ne)
    rw [← hinner] at hrhs
    have hlhs : ⟪(x 2 + s • (x 4 - x 2)) - (x 0 + t • (x 6 - x 0)), u07⟫ =
        (1 - s) * (1 - t) * (⟪x 2, u07⟫ - ⟪x 0, u07⟫) +
        (1 - s) * t * (⟪x 2, u07⟫ - ⟪x 6, u07⟫) +
        s * (1 - t) * (⟪x 4, u07⟫ - ⟪x 0, u07⟫) +
        s * t * (⟪x 4, u07⟫ - ⟪x 6, u07⟫) := by
      simp only [inner_sub_left, inner_add_left, real_inner_smul_left]; ring
    linarith
  have hex_pos : ∃ q ∈ Minimality.RimCell.diagPairs,
      LexLt3 (⟪x ((![0, 2, 6, 4] : ZMod 4 → Fin 7) q.1), u07⟫,
              ⟪x ((![0, 2, 6, 4] : ZMod 4 → Fin 7) q.1), x 6 - x 1⟫, (0 : ℝ))
             (⟪x ((![0, 2, 6, 4] : ZMod 4 → Fin 7) q.2), u07⟫,
              ⟪x ((![0, 2, 6, 4] : ZMod 4 → Fin 7) q.2), x 6 - x 1⟫, (0 : ℝ)) := by
    by_contra hno
    push Not at hno
    have h01 : ⟪x 2, u07⟫ - ⟪x 0, u07⟫ ≤ 0 := by
      by_contra h; push Not at h
      exact hno (0, 1) (by decide) (Or.inl (by simp [Matrix.cons_val]; linarith))
    have h21 : ⟪x 2, u07⟫ - ⟪x 6, u07⟫ ≤ 0 := by
      by_contra h; push Not at h
      exact hno (2, 1) (by decide) (Or.inl (by simp [Matrix.cons_val]; linarith))
    have h03 : ⟪x 4, u07⟫ - ⟪x 0, u07⟫ ≤ 0 := by
      by_contra h; push Not at h
      exact hno (0, 3) (by decide) (Or.inl (by simp [Matrix.cons_val]; linarith))
    have h23 : ⟪x 4, u07⟫ - ⟪x 6, u07⟫ ≤ 0 := by
      by_contra h; push Not at h
      exact hno (2, 3) (by decide) (Or.inl (by simp [Matrix.cons_val]; linarith))
    nlinarith [mul_pos (sub_pos.mpr hs1) (sub_pos.mpr ht1),
      mul_pos (sub_pos.mpr hs1) ht0, mul_pos hs0 (sub_pos.mpr ht1), mul_pos hs0 ht0]
  have hex_neg : ∃ p ∈ Minimality.RimCell.diagPairs,
      LexLt3 (⟪x ((![0, 2, 6, 4] : ZMod 4 → Fin 7) p.2), u07⟫,
              ⟪x ((![0, 2, 6, 4] : ZMod 4 → Fin 7) p.2), x 6 - x 1⟫, (0 : ℝ))
             (⟪x ((![0, 2, 6, 4] : ZMod 4 → Fin 7) p.1), u07⟫,
              ⟪x ((![0, 2, 6, 4] : ZMod 4 → Fin 7) p.1), x 6 - x 1⟫, (0 : ℝ)) := by
    refine ⟨(0, 1), by decide, Or.inl ?_⟩
    simp only [Matrix.cons_val]
    rw [← sub_pos, ← inner_sub_left, show x 0 - x 2 = -(x 2 - x 0) from by abel, inner_neg_left]
    linarith [hz20]
  apply hL
  refine ⟨4, inferInstance, (![0, 2, 6, 4] : ZMod 4 → Fin 7), {2, 3, 7, 8}, {0, 4, 5},
    u07, x 6 - x 1, 0, by decide,
    (by intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)),
    (by unfold S0xCycUD; decide), ?_, ?_,
    by simpa [inner_zero_right] using robUniLex_four_of_mixed hex_pos hex_neg⟩
  · intro tf ht
    fin_cases tf <;> dsimp only at ht ⊢ <;> (try exact absurd ht (by decide))
    · exact Or.inl (show 0 < ⟪F.N ⟨2, by decide⟩, u07⟫ from hu2)
    · exact Or.inl (show 0 < ⟪F.N ⟨3, by decide⟩, u07⟫ from hu3)
    · refine Or.inr ⟨show ⟪F.N ⟨7, by decide⟩, u07⟫ = 0 from hu7, Or.inl ?_⟩
      change 0 < ⟪F.N 7, x 6 - x 1⟫
      rw [← F.hN 7 (x 6) (x 1), F.zero 7 6 (by decide), zero_sub, neg_pos]
      exact F.neg 7 1 (by decide)
    · exact Or.inl (show 0 < ⟪F.N ⟨8, by decide⟩, u07⟫ from hu8)
  · intro tf ht
    fin_cases tf <;> dsimp only at ht ⊢ <;> (try exact absurd ht (by decide))
    · refine Or.inr ⟨by linarith [show ⟪F.N ⟨0, by decide⟩, u07⟫ = 0 from hu0], Or.inl ?_⟩
      change 0 < -⟪F.N 0, x 6 - x 1⟫
      rw [← F.hN 0 (x 6) (x 1), F.zero 0 1 (by decide), sub_zero, neg_pos]
      exact F.neg 0 6 (by decide)
    · exact Or.inl (by linarith [show ⟪F.N ⟨4, by decide⟩, u07⟫ < 0 from hu4])
    · exact Or.inl (by linarith [show ⟪F.N ⟨5, by decide⟩, u07⟫ < 0 from hu5])

/-! ### L10: `m4half` (Steps 1–3) and `isRupert_of_m4half` -/

theorem m4half {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (hab : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0)
    (h346 : F.f 8 (x 2) < F.f 8 (x 0)) (hc3 : oblX6 x 3 < 1) (hk5 : kappa5 x < 0)
    (hL : ¬ LexAny F) (hS : ¬ SplitAny24 F) :
    0 ≤ ⟪x 6 - x 2, x 2 - x 0⟫ := by
  have hdich := w02_dichotomy F hC hab hc3 h346 hL hS
  have hu07 := u07_bound F hC hc3 hL
  set p := -⟪x 0 - x 1, x 2 - x 0⟫
  set q := ⟪x 2 - x 1, x 2 - x 0⟫
  set z3 := ⟪x 3 - x 1, x 2 - x 0⟫
  set z5 := ⟪x 5 - x 1, x 2 - x 0⟫
  set z6 := ⟪x 6 - x 1, x 2 - x 0⟫
  have T := type24OfFac F
  have hx21_pos : 0 < ⟪x 2 - x 1, x 2 - x 1⟫ :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide))
  have hx01_pos : 0 < ⟪x 0 - x 1, x 0 - x 1⟫ :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide))
  have hq_pos : 0 < q := by
    dsimp [q]; have e : x 2 - x 0 = (x 2 - x 1) - (x 0 - x 1) := by abel
    rw [e, inner_sub_right, real_inner_comm (x 0 - x 1) (x 2 - x 1)]; linarith
  have hp_pos : 0 < p := by
    dsimp [p]; have e : x 2 - x 0 = (x 2 - x 1) - (x 0 - x 1) := by abel
    rw [e, inner_sub_right]; linarith
  have hp_le : p ≤ omega3 x * q := by linarith
  have hz3_rep : z3 = -oblX0 x 3 * p + oblX2 x 3 * q + oblX6 x 3 * z6 := by
    dsimp [z3, p, q, z6]; rw [inner_rep F 3]; ring
  have hz5_rep : z5 = -oblX0 x 5 * p + oblX2 x 5 * q + oblX6 x 5 * z6 := by
    dsimp [z5, p, q, z6]; rw [inner_rep F 5]; ring
  -- Identity F1: `c3 * z5 - c5 * z3 = (c3 * b5 - c5 * b3) * q - (c3 * a5 - c5 * a3) * p`.
  have hF1 : oblX6 x 3 * z5 - oblX6 x 5 * z3 =
      (oblX6 x 3 * oblX2 x 5 - oblX6 x 5 * oblX2 x 3) * q -
      (oblX6 x 3 * oblX0 x 5 - oblX6 x 5 * oblX0 x 3) * p := by
    rw [hz3_rep, hz5_rep]; ring
  -- Identity F2: `a3 * (omega3 * q - p) = (z3 - z6) - (1 - c3) * (q - z6)`.
  have hF2 : oblX0 x 3 * (omega3 x * q - p) = (z3 - z6) - (1 - oblX6 x 3) * (q - z6) := by
    have e3 := eq3 F
    rw [hz3_rep]
    linear_combination -q * e3
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hcross : 0 < oblX6 x 3 * oblX2 x 5 - oblX6 x 5 * oblX2 x 3 := cross35_pos F
  -- Key `κ5` identity: `(c3 * b5 - c5 * b3) - (c3 * a5 - c5 * a3) * omega3 = -κ5`.
  have hkap_id : (oblX6 x 3 * oblX2 x 5 - oblX6 x 5 * oblX2 x 3) -
      (oblX6 x 3 * oblX0 x 5 - oblX6 x 5 * oblX0 x 3) * omega3 x = -kappa5 x := by
    have e3 := eq3 F
    dsimp [kappa5]
    linear_combination -oblX6 x 5 * e3
  have hz3_le_z6 : z3 ≤ z6 := by
    rcases hdich with hle | hle
    · -- `c3 * z5 ≤ c5 * z3`, so `F1 ≤ 0`. Gap G2: split on `K = c3 * a5 - c5 * a3`.
      set D := oblX6 x 3 * oblX2 x 5 - oblX6 x 5 * oblX2 x 3
      set K := oblX6 x 3 * oblX0 x 5 - oblX6 x 5 * oblX0 x 3
      have hDq_le : D * q ≤ K * p := by linarith
      rcases le_or_gt K 0 with hK | hK
      · exact absurd hDq_le (not_le.mpr (lt_of_le_of_lt (mul_nonpos_of_nonpos_of_nonneg hK hp_pos.le)
          (mul_pos hcross hq_pos)))
      · have h1 : D * q ≤ K * (omega3 x * q) := le_trans hDq_le (mul_le_mul_of_nonneg_left hp_le hK.le)
        have h2 : (D - K * omega3 x) * q ≤ 0 := by linarith
        have h3 : 0 < D - K * omega3 x := by rw [hkap_id]; linarith
        exact absurd h2 (not_le.mpr (mul_pos h3 hq_pos))
    · exact hle
  -- Now `F2` gives `0 ≤ (1 - c3) * (z6 - q)`:
  have hF2_nonneg : 0 ≤ (1 - oblX6 x 3) * (z6 - q) := by
    have : 0 ≤ oblX0 x 3 * (omega3 x * q - p) := mul_nonneg ha3.le hu07
    linarith
  have hq_le_z6 : q ≤ z6 := by
    by_contra h
    push Not at h
    have := mul_pos (show 0 < 1 - oblX6 x 3 by linarith) (show 0 < q - z6 by linarith)
    linarith
  have e : ⟪x 6 - x 2, x 2 - x 0⟫ = z6 - q := by
    dsimp [z6, q]; rw [← inner_sub_left]; congr 1; abel
  linarith

theorem isRupert_of_m4half {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (hab : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0)
    (h346 : F.f 8 (x 2) < F.f 8 (x 0)) (hc3 : oblX6 x 3 < 1) (hk5 : kappa5 x < 0)
    (hz : ⟪x 6 - x 2, x 2 - x 0⟫ < 0) :
    IsRupert (Finset.univ.image x) := by
  by_cases hL : LexAny F
  · exact lexAny_isRupert F hL
  · by_cases hS : SplitAny24 F
    · exact splitAny24_isRupert F hS
    · exact absurd (m4half F hC hab h346 hc3 hk5 hL hS) (not_le.mpr hz)

end Minimality.T24.M4

