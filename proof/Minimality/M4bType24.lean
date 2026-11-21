module

public import Minimality.M4Type24

/-!
# Type 24 — V31, V30, Diagonal Corollary, and E05-P5 (Task CB)

Formalizes the referee-verified lemmas from `A7-REFEREE.md`:
- `v31_bound` (V31) and `v30_bound` (V30), including gap fixes G1 (all three
  violating quadruples in the 5-rim) and G2 (the exact `b5 z3 + (b3 - b5) z0 - b3 z5` identity).
- `diag_of_bc_zero` (when `⟪x 2 - x 1, x 6 - x 1⟫ = 0`, `¬ LexAny F` forces
  `⟪x 0 - x 1, x 2 - x 1⟫ = 0 ∧ ⟪x 0 - x 1, x 6 - x 1⟫ = 0`).
- `splitAny24_E05P5` and `isRupert_of_E05P5` (the `a5 > 1`, `σ < 1` leaf on rim
  `![0, 4, 6, 2, 5]`, pivot `5`, edge `26`, tilt `x 6 - x 1`).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset Filter
open scoped Topology

namespace Minimality.T24.A7

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell
  Minimality.LexCell Minimality.Split Minimality.T24.M4

/-! ### A0: Definitions, `D45 > 0`, Lemma M coordinates, and facet-value equivalences -/

noncomputable def D45 (x : Fin 7 → ℝ³) : ℝ :=
  oblX2 x 5 * oblX6 x 4 - oblX2 x 4 * oblX6 x 5

noncomputable def nB (x : Fin 7 → ℝ³) : ℝ :=
  oblX6 x 4 * (1 - oblX0 x 5) - oblX6 x 5 * (1 - oblX0 x 4)

noncomputable def nC (x : Fin 7 → ℝ³) : ℝ :=
  oblX2 x 5 * (1 - oblX0 x 4) - oblX2 x 4 * (1 - oblX0 x 5)

noncomputable def Lam5 (x : Fin 7 → ℝ³) : ℝ :=
  oblX2 x 5 + oblX6 x 5 + omega3 x * (1 - oblX0 x 5)

noncomputable def R46 (x : Fin 7 → ℝ³) : ℝ :=
  -(oblX2 x 5 + oblX6 x 5) * oblX0 x 4 + (1 - oblX0 x 5) * (1 - oblX2 x 4 - oblX6 x 4)

noncomputable def R04 (x : Fin 7 → ℝ³) : ℝ :=
  (oblX2 x 5 + oblX6 x 5) * (oblX0 x 4 - 1) + (1 - oblX0 x 5) * (oblX2 x 4 + oblX6 x 4)

noncomputable def v31 (x : Fin 7 → ℝ³) : ℝ³ :=
  -nC x • (x 0 - x 1) + D45 x • (x 6 - x 1)

noncomputable def v30 (x : Fin 7 → ℝ³) : ℝ³ :=
  -nB x • (x 0 - x 1) + D45 x • (x 2 - x 1)

theorem d45_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : 0 < D45 x := by
  have T := type24OfFac F
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have f3_1 : F.f 3 (x 1) < 0 := F.neg 3 1 (by decide)
  have f3_2 : F.f 3 (x 2) < 0 := F.neg 3 2 (by decide)
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
  have e_comb : (α - β) * D45 x +
      α * oblX6 x 5 * (oblX0 x 4 + oblX2 x 4 - omega5 x * oblX6 x 4 - 1) = 0 := by
    have := eq5 F
    dsimp [D45]
    linear_combination oblX6 x 5 * h4 - oblX6 x 4 * h5 + α * oblX6 x 4 * this
  have hαβ : α - β = -F.f 3 (x 2) := by dsimp [α, β]; ring
  have hαβ_pos : 0 < α - β := by rw [hαβ]; linarith
  have hrhs_pos : 0 < -α * oblX6 x 5 * (oblX0 x 4 + oblX2 x 4 - omega5 x * oblX6 x 4 - 1) := by
    have : α * oblX6 x 5 * (oblX0 x 4 + oblX2 x 4 - omega5 x * oblX6 x 4 - 1) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos hα hc5) (by linarith)
    linarith
  nlinarith

theorem lemmaM_coords {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    ∃ s t : ℝ, 0 < s ∧ 0 < t ∧
      x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0) ∧
      oblX0 x 3 - 1 = s * (oblX0 x 4 - 1) + t * (oblX0 x 5 - 1) ∧
      oblX2 x 3 = s * oblX2 x 4 + t * oblX2 x 5 ∧
      oblX6 x 3 = s * oblX6 x 4 + t * oblX6 x 5 := by
  have T := type24OfFac F
  obtain ⟨s, t, hs, ht, -, hdec⟩ := Minimality.T24.RimFromSigns.lemmaM_quad_decomp F
  have hx0 : x 0 - x 0 = 0 := sub_self _
  have hrep : ∀ v : Fin 7, x v - x 0 =
      (oblX0 x v - 1) • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1) := by
    intro v
    have hv := T.rep v
    calc x v - x 0 = (x v - x 1) - (x 0 - x 1) := by abel
      _ = (oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1)) -
          (x 0 - x 1) := by rw [hv]; abel
      _ = (oblX0 x v - 1) • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1) := by
          module
  have hdec1 : (oblX0 x 3 - 1) • (x 0 - x 1) + oblX2 x 3 • (x 2 - x 1) + oblX6 x 3 • (x 6 - x 1) =
      (s * (oblX0 x 4 - 1) + t * (oblX0 x 5 - 1)) • (x 0 - x 1) +
      (s * oblX2 x 4 + t * oblX2 x 5) • (x 2 - x 1) +
      (s * oblX6 x 4 + t * oblX6 x 5) • (x 6 - x 1) := by
    calc _ = x 3 - x 0 := (hrep 3).symm
      _ = s • (x 4 - x 0) + t • (x 5 - x 0) := hdec
      _ = s • ((oblX0 x 4 - 1) • (x 0 - x 1) + oblX2 x 4 • (x 2 - x 1) + oblX6 x 4 • (x 6 - x 1)) +
          t • ((oblX0 x 5 - 1) • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) + oblX6 x 5 • (x 6 - x 1)) := by
            rw [hrep 4, hrep 5]
      _ = _ := by module
  have hd := T.det_ne
  have ha3 : oblX0 x 3 - 1 = s * (oblX0 x 4 - 1) + t * (oblX0 x 5 - 1) := by
    have h := congrArg (fun w => det3 w (x 2 - x 1) (x 6 - x 1)) hdec1
    have hL : det3 ((oblX0 x 3 - 1) • (x 0 - x 1) + oblX2 x 3 • (x 2 - x 1) +
        oblX6 x 3 • (x 6 - x 1)) (x 2 - x 1) (x 6 - x 1) = (oblX0 x 3 - 1) * det24 x := by
      simpa using M4.det3_frame x (oblX0 x 3 - 1) (oblX2 x 3) (oblX6 x 3) 0 1 0 0 0 1
    have hR : det3 ((s * (oblX0 x 4 - 1) + t * (oblX0 x 5 - 1)) • (x 0 - x 1) +
        (s * oblX2 x 4 + t * oblX2 x 5) • (x 2 - x 1) +
        (s * oblX6 x 4 + t * oblX6 x 5) • (x 6 - x 1)) (x 2 - x 1) (x 6 - x 1) =
        (s * (oblX0 x 4 - 1) + t * (oblX0 x 5 - 1)) * det24 x := by
      simpa using M4.det3_frame x (s * (oblX0 x 4 - 1) + t * (oblX0 x 5 - 1))
        (s * oblX2 x 4 + t * oblX2 x 5) (s * oblX6 x 4 + t * oblX6 x 5) 0 1 0 0 0 1
    rw [hL, hR] at h
    exact mul_right_cancel₀ hd h
  have hb3 : oblX2 x 3 = s * oblX2 x 4 + t * oblX2 x 5 := by
    have h := congrArg (fun w => det3 (x 0 - x 1) w (x 6 - x 1)) hdec1
    have hL : det3 (x 0 - x 1) ((oblX0 x 3 - 1) • (x 0 - x 1) + oblX2 x 3 • (x 2 - x 1) +
        oblX6 x 3 • (x 6 - x 1)) (x 6 - x 1) = oblX2 x 3 * det24 x := by
      simpa using M4.det3_frame x 1 0 0 (oblX0 x 3 - 1) (oblX2 x 3) (oblX6 x 3) 0 0 1
    have hR : det3 (x 0 - x 1) ((s * (oblX0 x 4 - 1) + t * (oblX0 x 5 - 1)) • (x 0 - x 1) +
        (s * oblX2 x 4 + t * oblX2 x 5) • (x 2 - x 1) +
        (s * oblX6 x 4 + t * oblX6 x 5) • (x 6 - x 1)) (x 6 - x 1) =
        (s * oblX2 x 4 + t * oblX2 x 5) * det24 x := by
      simpa using M4.det3_frame x 1 0 0 (s * (oblX0 x 4 - 1) + t * (oblX0 x 5 - 1))
        (s * oblX2 x 4 + t * oblX2 x 5) (s * oblX6 x 4 + t * oblX6 x 5) 0 0 1
    rw [hL, hR] at h
    exact mul_right_cancel₀ hd h
  have hc3 : oblX6 x 3 = s * oblX6 x 4 + t * oblX6 x 5 := by
    have h := congrArg (fun w => det3 (x 0 - x 1) (x 2 - x 1) w) hdec1
    have hL : det3 (x 0 - x 1) (x 2 - x 1) ((oblX0 x 3 - 1) • (x 0 - x 1) +
        oblX2 x 3 • (x 2 - x 1) + oblX6 x 3 • (x 6 - x 1)) = oblX6 x 3 * det24 x := by
      simpa using M4.det3_frame x 1 0 0 0 1 0 (oblX0 x 3 - 1) (oblX2 x 3) (oblX6 x 3)
    have hR : det3 (x 0 - x 1) (x 2 - x 1) ((s * (oblX0 x 4 - 1) + t * (oblX0 x 5 - 1)) • (x 0 - x 1) +
        (s * oblX2 x 4 + t * oblX2 x 5) • (x 2 - x 1) +
        (s * oblX6 x 4 + t * oblX6 x 5) • (x 6 - x 1)) =
        (s * oblX6 x 4 + t * oblX6 x 5) * det24 x := by
      simpa using M4.det3_frame x 1 0 0 0 1 0 (s * (oblX0 x 4 - 1) + t * (oblX0 x 5 - 1))
        (s * oblX2 x 4 + t * oblX2 x 5) (s * oblX6 x 4 + t * oblX6 x 5)
    rw [hL, hR] at h
    exact mul_right_cancel₀ hd h
  exact ⟨s, t, hs, ht, hdec, ha3, hb3, hc3⟩

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

theorem nC_pos_iff {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    0 < nC x ↔ F.f 3 (x 1) < F.f 3 (x 6) := by
  have h1 : 0 < -F.f 3 (x 1) := by linarith [F.neg 3 1 (by decide)]
  have hD : 0 < D45 x := d45_pos F
  have hlin := (fac3_lin F).1
  constructor
  · intro h
    have : 0 < (F.f 3 (x 6) - F.f 3 (x 1)) * D45 x := by
      rw [← hlin]; exact mul_pos h1 h
    nlinarith
  · intro h
    have : 0 < (-F.f 3 (x 1)) * nC x := by
      rw [hlin]; exact mul_pos (sub_pos.mpr h) hD
    nlinarith

theorem nB_pos_iff {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    0 < nB x ↔ F.f 3 (x 1) < F.f 3 (x 2) := by
  have h1 : 0 < -F.f 3 (x 1) := by linarith [F.neg 3 1 (by decide)]
  have hD : 0 < D45 x := d45_pos F
  have hlin := (fac3_lin F).2
  constructor
  · intro h
    have : 0 < (F.f 3 (x 2) - F.f 3 (x 1)) * D45 x := by
      rw [← hlin]; exact mul_pos h1 h
    nlinarith
  · intro h
    have : 0 < (-F.f 3 (x 1)) * nB x := by
      rw [hlin]; exact mul_pos (sub_pos.mpr h) hD
    nlinarith

/-! ### V1–V6: Theorem V31 -/

theorem v31_eq {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    v31 x = oblX2 x 5 • (x 4 - x 0) - oblX2 x 4 • (x 5 - x 0) := by
  have T := type24OfFac F
  have hrep : ∀ v : Fin 7, x v - x 0 =
      (oblX0 x v - 1) • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1) := by
    intro v
    calc x v - x 0 = (x v - x 1) - (x 0 - x 1) := by abel
      _ = (oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1)) -
          (x 0 - x 1) := by rw [T.rep v]; abel
      _ = _ := by module
  rw [hrep 4, hrep 5]
  dsimp [v31, nC, D45]
  module

theorem v31_facings {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (hnc : F.f 3 (x 1) < F.f 3 (x 6)) (hb : oblX2 x 4 < oblX2 x 3) :
    ⟪F.N 0, v31 x⟫ < 0 ∧
    ⟪F.N 1, v31 x⟫ = 0 ∧
    ⟪F.N 2, v31 x⟫ < 0 ∧
    ⟪F.N 3, v31 x⟫ = 0 ∧
    0 < ⟪F.N 4, v31 x⟫ ∧
    0 < ⟪F.N 5, v31 x⟫ ∧
    0 < ⟪F.N 7, v31 x⟫ ∧
    0 < ⟪F.N 8, v31 x⟫ ∧
    ((oblX2 x 3 < oblX2 x 5 → 0 < ⟪F.N 6, v31 x⟫) ∧
     (oblX2 x 3 = oblX2 x 5 → ⟪F.N 6, v31 x⟫ = 0) ∧
     (oblX2 x 5 < oblX2 x 3 → ⟪F.N 6, v31 x⟫ < 0)) := by
  have T := type24OfFac F
  have hD : 0 < D45 x := d45_pos F
  have hnC : 0 < nC x := (nC_pos_iff F).mpr hnc
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hom3 : 0 < omega3 x := hC.1
  have hframe : ∀ t : Fin 9,
      ⟪F.N t, v31 x⟫ = -nC x * (F.f t (x 0) - F.f t (x 1)) +
        D45 x * (F.f t (x 6) - F.f t (x 1)) := by
    intro t
    dsimp [v31]
    rw [inner_add_right, inner_smul_right, inner_smul_right,
      ← F.hN t (x 0) (x 1), ← F.hN t (x 6) (x 1)]
  have h45 : ∀ t : Fin 9,
      ⟪F.N t, v31 x⟫ = oblX2 x 5 * (F.f t (x 4) - F.f t (x 0)) -
        oblX2 x 4 * (F.f t (x 5) - F.f t (x 0)) := by
    intro t
    rw [v31_eq F, inner_sub_right, inner_smul_right, inner_smul_right,
      ← F.hN t (x 4) (x 0), ← F.hN t (x 5) (x 0)]
  obtain ⟨s, t, hs, ht, hdec, -, hb3, -⟩ := lemmaM_coords F
  have hsv : s • v31 x = oblX2 x 5 • (x 3 - x 5) + (oblX2 x 5 - oblX2 x 3) • (x 5 - x 0) := by
    have hv := v31_eq F
    have h1 : s • v31 x = oblX2 x 5 • (s • (x 4 - x 0)) - (s * oblX2 x 4) • (x 5 - x 0) := by
      rw [hv]; module
    have h2 : s • (x 4 - x 0) = (x 3 - x 0) - t • (x 5 - x 0) := by
      rw [hdec]; abel
    have h3 : s * oblX2 x 4 = oblX2 x 3 - t * oblX2 x 5 := by linarith
    rw [h1, h2, h3]
    module
  have htv : t • v31 x = (oblX2 x 3 - oblX2 x 4) • (x 4 - x 0) - oblX2 x 4 • (x 3 - x 4) := by
    have hv := v31_eq F
    have h1 : t • v31 x = (t * oblX2 x 5) • (x 4 - x 0) - oblX2 x 4 • (t • (x 5 - x 0)) := by
      rw [hv]; module
    have h2 : t • (x 5 - x 0) = (x 3 - x 0) - s • (x 4 - x 0) := by
      rw [hdec]; abel
    have h3 : t * oblX2 x 5 = oblX2 x 3 - s * oblX2 x 4 := by linarith
    rw [h1, h2, h3]
    module
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- t = 0 (`012`)
    rw [hframe 0, F.zero 0 0 (by decide), F.zero 0 1 (by decide), sub_self, mul_zero, zero_add,
      sub_zero]
    exact mul_neg_of_pos_of_neg hD (F.neg 0 6 (by decide))
  · -- t = 1 (`016`)
    rw [hframe 1, F.zero 1 0 (by decide), F.zero 1 1 (by decide), F.zero 1 6 (by decide)]
    ring
  · -- t = 2 (`025`)
    rw [h45 2, F.zero 2 0 (by decide), F.zero 2 5 (by decide), sub_zero, sub_self, mul_zero, sub_zero]
    exact mul_neg_of_pos_of_neg hb5 (F.neg 2 4 (by decide))
  · -- t = 3 (`0345`)
    rw [h45 3, F.zero 3 0 (by decide), F.zero 3 4 (by decide), F.zero 3 5 (by decide)]
    ring
  · -- t = 4 (`046`)
    rw [h45 4, F.zero 4 0 (by decide), F.zero 4 4 (by decide), sub_self, mul_zero, zero_sub, sub_zero]
    nlinarith [F.neg 4 5 (by decide)]
  · -- t = 5 (`126`)
    rw [hframe 5, F.zero 5 1 (by decide), F.zero 5 6 (by decide), sub_self, mul_zero, add_zero,
      sub_zero]
    nlinarith [F.neg 5 0 (by decide)]
  · -- t = 7 (`236`)
    have f7_1 : F.f 7 (x 1) < 0 := F.neg 7 1 (by decide)
    have ev7 := fac_eval F 7 3
    rw [F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at ev7
    have e3 := eq3 F
    have ha3 : oblX0 x 3 ≠ 0 := (T.X0_pos (v := 3) (by decide)).ne'
    have h7_id : oblX0 x 3 * (F.f 7 (x 0) - (1 + omega3 x) * F.f 7 (x 1)) = 0 := by
      linear_combination -ev7 + F.f 7 (x 1) * e3
    have hf7_0 : F.f 7 (x 0) = (1 + omega3 x) * F.f 7 (x 1) :=
      sub_eq_zero.mp ((mul_eq_zero.mp h7_id).resolve_left ha3)
    rw [hframe 7, F.zero 7 6 (by decide), hf7_0]
    have hprod : (-F.f 7 (x 1)) * (omega3 x * nC x + D45 x) =
        -nC x * ((1 + omega3 x) * F.f 7 (x 1) - F.f 7 (x 1)) + D45 x * (0 - F.f 7 (x 1)) := by
      ring
    rw [← hprod]
    exact mul_pos (by linarith) (add_pos (mul_pos hom3 hnC) hD)
  · -- t = 8 (`346`)
    have h8 : t * ⟪F.N 8, v31 x⟫ = (oblX2 x 3 - oblX2 x 4) * (-F.f 8 (x 0)) := by
      calc t * ⟪F.N 8, v31 x⟫ = ⟪F.N 8, t • v31 x⟫ := (inner_smul_right _ _ _).symm
        _ = (oblX2 x 3 - oblX2 x 4) * (F.f 8 (x 4) - F.f 8 (x 0)) -
            oblX2 x 4 * (F.f 8 (x 3) - F.f 8 (x 4)) := by
          rw [htv, inner_sub_right, inner_smul_right, inner_smul_right,
            ← F.hN 8 (x 4) (x 0), ← F.hN 8 (x 3) (x 4)]
        _ = (oblX2 x 3 - oblX2 x 4) * (-F.f 8 (x 0)) := by
          rw [F.zero 8 3 (by decide), F.zero 8 4 (by decide)]; ring
    have hrhs : 0 < (oblX2 x 3 - oblX2 x 4) * (-F.f 8 (x 0)) :=
      mul_pos (sub_pos.mpr hb) (by linarith [F.neg 8 0 (by decide)])
    nlinarith
  · -- t = 6 (`235`), `b3 < b5`
    intro h35
    have h6 : s * ⟪F.N 6, v31 x⟫ = (oblX2 x 5 - oblX2 x 3) * (-F.f 6 (x 0)) := by
      calc s * ⟪F.N 6, v31 x⟫ = ⟪F.N 6, s • v31 x⟫ := (inner_smul_right _ _ _).symm
        _ = oblX2 x 5 * (F.f 6 (x 3) - F.f 6 (x 5)) +
            (oblX2 x 5 - oblX2 x 3) * (F.f 6 (x 5) - F.f 6 (x 0)) := by
          rw [hsv, inner_add_right, inner_smul_right, inner_smul_right,
            ← F.hN 6 (x 3) (x 5), ← F.hN 6 (x 5) (x 0)]
        _ = (oblX2 x 5 - oblX2 x 3) * (-F.f 6 (x 0)) := by
          rw [F.zero 6 3 (by decide), F.zero 6 5 (by decide)]; ring
    have hrhs : 0 < (oblX2 x 5 - oblX2 x 3) * (-F.f 6 (x 0)) :=
      mul_pos (sub_pos.mpr h35) (by linarith [F.neg 6 0 (by decide)])
    nlinarith
  · -- t = 6 (`235`), `b3 = b5`
    intro h35
    have h6 : s * ⟪F.N 6, v31 x⟫ = (oblX2 x 5 - oblX2 x 3) * (-F.f 6 (x 0)) := by
      calc s * ⟪F.N 6, v31 x⟫ = ⟪F.N 6, s • v31 x⟫ := (inner_smul_right _ _ _).symm
        _ = oblX2 x 5 * (F.f 6 (x 3) - F.f 6 (x 5)) +
            (oblX2 x 5 - oblX2 x 3) * (F.f 6 (x 5) - F.f 6 (x 0)) := by
          rw [hsv, inner_add_right, inner_smul_right, inner_smul_right,
            ← F.hN 6 (x 3) (x 5), ← F.hN 6 (x 5) (x 0)]
        _ = (oblX2 x 5 - oblX2 x 3) * (-F.f 6 (x 0)) := by
          rw [F.zero 6 3 (by decide), F.zero 6 5 (by decide)]; ring
    rw [h35, sub_self, zero_mul] at h6
    exact (mul_eq_zero.mp h6).resolve_left hs.ne'
  · -- t = 6 (`235`), `b5 < b3`
    intro h53
    have h6 : s * ⟪F.N 6, v31 x⟫ = (oblX2 x 5 - oblX2 x 3) * (-F.f 6 (x 0)) := by
      calc s * ⟪F.N 6, v31 x⟫ = ⟪F.N 6, s • v31 x⟫ := (inner_smul_right _ _ _).symm
        _ = oblX2 x 5 * (F.f 6 (x 3) - F.f 6 (x 5)) +
            (oblX2 x 5 - oblX2 x 3) * (F.f 6 (x 5) - F.f 6 (x 0)) := by
          rw [hsv, inner_add_right, inner_smul_right, inner_smul_right,
            ← F.hN 6 (x 3) (x 5), ← F.hN 6 (x 5) (x 0)]
        _ = (oblX2 x 5 - oblX2 x 3) * (-F.f 6 (x 0)) := by
          rw [F.zero 6 3 (by decide), F.zero 6 5 (by decide)]; ring
    have hrhs : (oblX2 x 5 - oblX2 x 3) * (-F.f 6 (x 0)) < 0 :=
      mul_neg_of_neg_of_pos (sub_neg.mpr h53) (by linarith [F.neg 6 0 (by decide)])
    nlinarith

theorem v31_tilt {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    0 < ⟪F.N 1, x 0 - x 2⟫ ∧ 0 < ⟪F.N 3, x 0 - x 2⟫ ∧ ⟪F.N 6, x 0 - x 2⟫ < 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← F.hN 1 (x 0) (x 2), F.zero 1 0 (by decide), zero_sub]
    linarith [F.neg 1 2 (by decide)]
  · rw [← F.hN 3 (x 0) (x 2), F.zero 3 0 (by decide), zero_sub]
    linarith [F.neg 3 2 (by decide)]
  · rw [← F.hN 6 (x 0) (x 2), F.zero 6 2 (by decide), sub_zero]
    exact F.neg 6 0 (by decide)

theorem v31_depths {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (hac : ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0)
    (hnc : F.f 3 (x 1) < F.f 3 (x 6)) (hb : oblX2 x 4 < oblX2 x 3) :
    ⟪x 0 - x 1, v31 x⟫ < 0 ∧
    0 < ⟪v31 x, v31 x⟫ ∧
    ∃ s : ℝ, 0 < s ∧
      oblX2 x 5 * ⟪x 3 - x 1, v31 x⟫ + (oblX2 x 3 - oblX2 x 5) * ⟪x 0 - x 1, v31 x⟫ -
        oblX2 x 3 * ⟪x 5 - x 1, v31 x⟫ = s * ⟪v31 x, v31 x⟫ := by
  have T := type24OfFac F
  have hD : 0 < D45 x := d45_pos F
  have hnC : 0 < nC x := (nC_pos_iff F).mpr hnc
  have hv_ne : v31 x ≠ 0 := by
    intro h0
    have hf0 := (v31_facings F hC hnc hb).1
    rw [h0, inner_zero_right] at hf0
    exact lt_irrefl 0 hf0
  have hv_pos : 0 < ⟪v31 x, v31 x⟫ := real_inner_self_pos.mpr hv_ne
  have hx01_pos : 0 < ⟪x 0 - x 1, x 0 - x 1⟫ :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide))
  have hz0 : ⟪x 0 - x 1, v31 x⟫ < 0 := by
    dsimp [v31]
    rw [inner_add_right, inner_smul_right, inner_smul_right]
    have := mul_nonpos_of_nonneg_of_nonpos hD.le hac
    nlinarith
  obtain ⟨s, t, hs, -, hdec, -, hb3, -⟩ := lemmaM_coords F
  have hsv : s • v31 x = oblX2 x 5 • (x 3 - x 5) + (oblX2 x 5 - oblX2 x 3) • (x 5 - x 0) := by
    have hv := v31_eq F
    have h1 : s • v31 x = oblX2 x 5 • (s • (x 4 - x 0)) - (s * oblX2 x 4) • (x 5 - x 0) := by
      rw [hv]; module
    have h2 : s • (x 4 - x 0) = (x 3 - x 0) - t • (x 5 - x 0) := by
      rw [hdec]; abel
    have h3 : s * oblX2 x 4 = oblX2 x 3 - t * oblX2 x 5 := by linarith
    rw [h1, h2, h3]
    module
  have hid : oblX2 x 5 * ⟪x 3 - x 1, v31 x⟫ + (oblX2 x 3 - oblX2 x 5) * ⟪x 0 - x 1, v31 x⟫ -
      oblX2 x 3 * ⟪x 5 - x 1, v31 x⟫ = s * ⟪v31 x, v31 x⟫ := by
    have h1 : s * ⟪v31 x, v31 x⟫ = ⟪s • v31 x, v31 x⟫ := (real_inner_smul_left _ _ _).symm
    have hs1 : ⟪x 3 - x 5, v31 x⟫ = ⟪x 3 - x 1, v31 x⟫ - ⟪x 5 - x 1, v31 x⟫ := by
      rw [show x 3 - x 5 = (x 3 - x 1) - (x 5 - x 1) by abel, inner_sub_left]
    have hs2 : ⟪x 5 - x 0, v31 x⟫ = ⟪x 5 - x 1, v31 x⟫ - ⟪x 0 - x 1, v31 x⟫ := by
      rw [show x 5 - x 0 = (x 5 - x 1) - (x 0 - x 1) by abel, inner_sub_left]
    rw [hsv, inner_add_left, real_inner_smul_left, real_inner_smul_left, hs1, hs2] at h1
    linarith
  exact ⟨hz0, hv_pos, s, hs, hid⟩

theorem robUniLex_five_v31 (z : ZMod 5 → ℝ × ℝ × ℝ)
    (h10 : (z 1).1 < (z 0).1) (h04 : (z 0).1 < (z 4).1)
    (h2 : (z 2).1 < max (z 1).1 (z 3).1) :
    RobUniLex z := by
  intro B b c d hb hbc hcd hd
  have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by revert B; decide
  have hbcd : (b = 1 ∧ c = 2 ∧ d = 3) ∨ (b = 1 ∧ c = 2 ∧ d = 4) ∨
      (b = 1 ∧ c = 3 ∧ d = 4) ∨ (b = 2 ∧ c = 3 ∧ d = 4) := by omega
  rcases lt_max_iff.mp h2 with h21 | h23
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

theorem v31_bound {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (hac : ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0)
    (hnc : F.f 3 (x 1) < F.f 3 (x 6)) (hb : oblX2 x 4 < oblX2 x 3)
    (hU : ¬ LexAny F) :
    ⟪x 2 - x 1, v31 x⟫ ≤ 0 := by
  by_contra hcon
  push Not at hcon
  have T := type24OfFac F
  have hfac := v31_facings F hC hnc hb
  have htilt := v31_tilt F
  have ⟨hz0, hv_pos, s, hs, hid⟩ := v31_depths F hC hac hnc hb
  have hshift : ∀ v : Fin 7, ⟪x v, v31 x⟫ = ⟪x v - x 1, v31 x⟫ + ⟪x 1, v31 x⟫ := by
    intro v; rw [inner_sub_left]; ring
  rcases lt_or_ge (oblX2 x 3) (oblX2 x 5) with h35 | h53
  · -- 4-rim `![1, 0, 5, 2]` with `U = {1, 3, 4, 5, 6, 7, 8}`, `Dn = {0, 2}`, tilt `x 0 - x 2`.
    apply hU
    refine ⟨4, inferInstance, (![1, 0, 5, 2] : ZMod 4 → Fin 7), {1, 3, 4, 5, 6, 7, 8}, {0, 2},
      v31 x, x 0 - x 2, 0, by decide,
      (by intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)),
      (by unfold S0xCycUD; decide), ?_, ?_, ?_⟩
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
    · refine robUniLex_four_of_mixed _ ⟨(0, 3), by decide, ?_⟩ ⟨(0, 1), by decide, ?_⟩
      · exact Or.inl (by dsimp only [Matrix.cons_val]; rw [hshift 1, hshift 2]; simp only [sub_self, inner_zero_left]; linarith)
      · exact Or.inl (by dsimp only [Matrix.cons_val]; rw [hshift 0, hshift 1]; simp only [sub_self, inner_zero_left]; linarith)
  · -- 5-rim `![1, 0, 5, 3, 2]` with `U = {1, 3, 4, 5, 7, 8}`, `Dn = {0, 2, 6}`, tilt `x 0 - x 2`.
    have hz5 : ⟪x 5 - x 1, v31 x⟫ < max ⟪x 0 - x 1, v31 x⟫ ⟪x 3 - x 1, v31 x⟫ := by
      have hb3_pos : 0 < oblX2 x 3 := T.X2_pos (v := 3) (by decide)
      have hb5_pos : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
      have hlt : oblX2 x 3 * ⟪x 5 - x 1, v31 x⟫ <
          oblX2 x 5 * ⟪x 3 - x 1, v31 x⟫ + (oblX2 x 3 - oblX2 x 5) * ⟪x 0 - x 1, v31 x⟫ := by
        have hsp : 0 < s * ⟪v31 x, v31 x⟫ := mul_pos hs hv_pos
        linarith
      rcases le_total ⟪x 0 - x 1, v31 x⟫ ⟪x 3 - x 1, v31 x⟫ with h03 | h30
      · rw [max_eq_right h03]
        have hle : oblX2 x 5 * ⟪x 3 - x 1, v31 x⟫ +
            (oblX2 x 3 - oblX2 x 5) * ⟪x 0 - x 1, v31 x⟫ ≤
            oblX2 x 3 * ⟪x 3 - x 1, v31 x⟫ := by
          have : (oblX2 x 3 - oblX2 x 5) * ⟪x 0 - x 1, v31 x⟫ ≤
              (oblX2 x 3 - oblX2 x 5) * ⟪x 3 - x 1, v31 x⟫ :=
            mul_le_mul_of_nonneg_left h03 (sub_nonneg.mpr h53)
          linarith
        nlinarith
      · rw [max_eq_left h30]
        have hle : oblX2 x 5 * ⟪x 3 - x 1, v31 x⟫ +
            (oblX2 x 3 - oblX2 x 5) * ⟪x 0 - x 1, v31 x⟫ ≤
            oblX2 x 3 * ⟪x 0 - x 1, v31 x⟫ := by
          have : oblX2 x 5 * ⟪x 3 - x 1, v31 x⟫ ≤ oblX2 x 5 * ⟪x 0 - x 1, v31 x⟫ :=
            mul_le_mul_of_nonneg_left h30 hb5_pos.le
          linarith
        nlinarith
    apply hU
    refine ⟨5, inferInstance, (![1, 0, 5, 3, 2] : ZMod 5 → Fin 7), {1, 3, 4, 5, 7, 8}, {0, 2, 6},
      v31 x, x 0 - x 2, 0, by decide,
      (by intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)),
      (by unfold S0xCycUD; decide), ?_, ?_, ?_⟩
    · intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inr ⟨hfac.2.1, Or.inl htilt.1⟩
      · exact Or.inr ⟨hfac.2.2.2.1, Or.inl htilt.2.1⟩
      · exact Or.inl hfac.2.2.2.2.1
      · exact Or.inl hfac.2.2.2.2.2.1
      · exact Or.inl hfac.2.2.2.2.2.2.1
      · exact Or.inl hfac.2.2.2.2.2.2.2.1
    · intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact Or.inl (by linarith [hfac.1])
      · exact Or.inl (by linarith [hfac.2.2.1])
      · rcases eq_or_lt_of_le h53 with heq | hlt
        · exact Or.inr ⟨by rw [hfac.2.2.2.2.2.2.2.2.2.1 heq.symm, neg_zero],
            Or.inl (by linarith [htilt.2.2])⟩
        · exact Or.inl (by linarith [hfac.2.2.2.2.2.2.2.2.2.2 hlt])
    · refine robUniLex_five_v31 _ ?_ ?_ ?_
      · dsimp only [Matrix.cons_val]; rw [hshift 0, hshift 1]; simp only [sub_self, inner_zero_left]; linarith
      · dsimp only [Matrix.cons_val]; rw [hshift 1, hshift 2]; simp only [sub_self, inner_zero_left]; linarith
      · dsimp only [Matrix.cons_val]
        rw [hshift 5, hshift 0, hshift 3]
        rcases lt_max_iff.mp hz5 with h50 | h53'
        · exact lt_max_of_lt_left (by linarith)
        · exact lt_max_of_lt_right (by linarith)

/-! ### V7: Theorem V30 (twin of V31) and Diagonal Corollary -/

theorem v30_eq {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    v30 x = oblX6 x 4 • (x 5 - x 0) - oblX6 x 5 • (x 4 - x 0) := by
  have T := type24OfFac F
  have hrep : ∀ v : Fin 7, x v - x 0 =
      (oblX0 x v - 1) • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1) := by
    intro v
    calc x v - x 0 = (x v - x 1) - (x 0 - x 1) := by abel
      _ = (oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1)) -
          (x 0 - x 1) := by rw [T.rep v]; abel
      _ = _ := by module
  rw [hrep 4, hrep 5]
  dsimp [v30, nB, D45]
  module

theorem v30_facings {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (hnb : F.f 3 (x 1) < F.f 3 (x 2)) (hc : oblX6 x 5 < oblX6 x 3) :
    ⟪F.N 0, v30 x⟫ = 0 ∧
    ⟪F.N 1, v30 x⟫ < 0 ∧
    0 < ⟪F.N 2, v30 x⟫ ∧
    ⟪F.N 3, v30 x⟫ = 0 ∧
    ⟪F.N 4, v30 x⟫ < 0 ∧
    0 < ⟪F.N 5, v30 x⟫ ∧
    0 < ⟪F.N 6, v30 x⟫ ∧
    0 < ⟪F.N 7, v30 x⟫ ∧
    ((oblX6 x 3 < oblX6 x 4 → 0 < ⟪F.N 8, v30 x⟫) ∧
     (oblX6 x 3 = oblX6 x 4 → ⟪F.N 8, v30 x⟫ = 0) ∧
     (oblX6 x 4 < oblX6 x 3 → ⟪F.N 8, v30 x⟫ < 0)) := by
  have T := type24OfFac F
  have hD : 0 < D45 x := d45_pos F
  have hnB : 0 < nB x := (nB_pos_iff F).mpr hnb
  have hc4 : 0 < oblX6 x 4 := T.X6_pos (v := 4) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hom4 : 0 < omega4 x := hC.2.1
  have hframe : ∀ t : Fin 9,
      ⟪F.N t, v30 x⟫ = -nB x * (F.f t (x 0) - F.f t (x 1)) +
        D45 x * (F.f t (x 2) - F.f t (x 1)) := by
    intro t
    dsimp [v30]
    rw [inner_add_right, inner_smul_right, inner_smul_right,
      ← F.hN t (x 0) (x 1), ← F.hN t (x 2) (x 1)]
  have h45 : ∀ t : Fin 9,
      ⟪F.N t, v30 x⟫ = oblX6 x 4 * (F.f t (x 5) - F.f t (x 0)) -
        oblX6 x 5 * (F.f t (x 4) - F.f t (x 0)) := by
    intro t
    rw [v30_eq F, inner_sub_right, inner_smul_right, inner_smul_right,
      ← F.hN t (x 5) (x 0), ← F.hN t (x 4) (x 0)]
  obtain ⟨s, t, hs, ht, hdec, -, -, hc3⟩ := lemmaM_coords F
  have htv : t • v30 x = oblX6 x 4 • (x 3 - x 4) + (oblX6 x 4 - oblX6 x 3) • (x 4 - x 0) := by
    have hv := v30_eq F
    have h1 : t • v30 x = (t * oblX6 x 4) • (x 5 - x 0) - oblX6 x 5 • (t • (x 4 - x 0)) := by
      rw [hv]; module
    have h1' : t • v30 x = oblX6 x 4 • (t • (x 5 - x 0)) - (t * oblX6 x 5) • (x 4 - x 0) := by
      rw [hv]; module
    have h2 : t • (x 5 - x 0) = (x 3 - x 0) - s • (x 4 - x 0) := by
      rw [hdec]; abel
    have h3 : t * oblX6 x 5 = oblX6 x 3 - s * oblX6 x 4 := by linarith
    rw [h1', h2, h3]
    module
  have hsv : s • v30 x = (oblX6 x 3 - oblX6 x 5) • (x 5 - x 0) - oblX6 x 5 • (x 3 - x 5) := by
    have hv := v30_eq F
    have h1 : s • v30 x = (s * oblX6 x 4) • (x 5 - x 0) - oblX6 x 5 • (s • (x 4 - x 0)) := by
      rw [hv]; module
    have h2 : s • (x 4 - x 0) = (x 3 - x 0) - t • (x 5 - x 0) := by
      rw [hdec]; abel
    have h3 : s * oblX6 x 4 = oblX6 x 3 - t * oblX6 x 5 := by linarith
    rw [h1, h2, h3]
    module
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- t = 0 (`012`)
    rw [hframe 0, F.zero 0 0 (by decide), F.zero 0 1 (by decide), F.zero 0 2 (by decide)]
    ring
  · -- t = 1 (`016`)
    rw [hframe 1, F.zero 1 0 (by decide), F.zero 1 1 (by decide), sub_self, mul_zero, zero_add,
      sub_zero]
    exact mul_neg_of_pos_of_neg hD (F.neg 1 2 (by decide))
  · -- t = 2 (`025`)
    rw [h45 2, F.zero 2 0 (by decide), F.zero 2 5 (by decide), sub_self, mul_zero, zero_sub, sub_zero]
    nlinarith [F.neg 2 4 (by decide)]
  · -- t = 3 (`0345`)
    rw [h45 3, F.zero 3 0 (by decide), F.zero 3 4 (by decide), F.zero 3 5 (by decide)]
    ring
  · -- t = 4 (`046`)
    rw [h45 4, F.zero 4 0 (by decide), F.zero 4 4 (by decide), sub_zero, sub_self, mul_zero, sub_zero]
    exact mul_neg_of_pos_of_neg hc4 (F.neg 4 5 (by decide))
  · -- t = 5 (`126`)
    rw [hframe 5, F.zero 5 1 (by decide), F.zero 5 2 (by decide), sub_self, mul_zero, add_zero,
      sub_zero]
    nlinarith [F.neg 5 0 (by decide)]
  · -- t = 6 (`235`)
    have h6 : s * ⟪F.N 6, v30 x⟫ = (oblX6 x 3 - oblX6 x 5) * (-F.f 6 (x 0)) := by
      calc s * ⟪F.N 6, v30 x⟫ = ⟪F.N 6, s • v30 x⟫ := (inner_smul_right _ _ _).symm
        _ = (oblX6 x 3 - oblX6 x 5) * (F.f 6 (x 5) - F.f 6 (x 0)) -
            oblX6 x 5 * (F.f 6 (x 3) - F.f 6 (x 5)) := by
          rw [hsv, inner_sub_right, inner_smul_right, inner_smul_right,
            ← F.hN 6 (x 5) (x 0), ← F.hN 6 (x 3) (x 5)]
        _ = (oblX6 x 3 - oblX6 x 5) * (-F.f 6 (x 0)) := by
          rw [F.zero 6 3 (by decide), F.zero 6 5 (by decide)]; ring
    have hrhs : 0 < (oblX6 x 3 - oblX6 x 5) * (-F.f 6 (x 0)) :=
      mul_pos (sub_pos.mpr hc) (by linarith [F.neg 6 0 (by decide)])
    nlinarith
  · -- t = 7 (`236`)
    have f7_1 : F.f 7 (x 1) < 0 := F.neg 7 1 (by decide)
    have ev7 := fac_eval F 7 3
    rw [F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at ev7
    have e3 := eq3 F
    have ha3 : oblX0 x 3 ≠ 0 := (T.X0_pos (v := 3) (by decide)).ne'
    have h7_id : oblX0 x 3 * (F.f 7 (x 0) - (1 + omega3 x) * F.f 7 (x 1)) = 0 := by
      linear_combination -ev7 + F.f 7 (x 1) * e3
    have hf7_0 : F.f 7 (x 0) = (1 + omega3 x) * F.f 7 (x 1) :=
      sub_eq_zero.mp ((mul_eq_zero.mp h7_id).resolve_left ha3)
    rw [hframe 7, F.zero 7 2 (by decide), hf7_0]
    have hprod : (-F.f 7 (x 1)) * (omega3 x * nB x + D45 x) =
        -nB x * ((1 + omega3 x) * F.f 7 (x 1) - F.f 7 (x 1)) + D45 x * (0 - F.f 7 (x 1)) := by
      ring
    rw [← hprod]
    exact mul_pos (by linarith) (add_pos (mul_pos hC.1 hnB) hD)
  · -- t = 8 (`346`), `c3 < c4`
    intro h34
    have h8 : t * ⟪F.N 8, v30 x⟫ = (oblX6 x 4 - oblX6 x 3) * (-F.f 8 (x 0)) := by
      calc t * ⟪F.N 8, v30 x⟫ = ⟪F.N 8, t • v30 x⟫ := (inner_smul_right _ _ _).symm
        _ = oblX6 x 4 * (F.f 8 (x 3) - F.f 8 (x 4)) +
            (oblX6 x 4 - oblX6 x 3) * (F.f 8 (x 4) - F.f 8 (x 0)) := by
          rw [htv, inner_add_right, inner_smul_right, inner_smul_right,
            ← F.hN 8 (x 3) (x 4), ← F.hN 8 (x 4) (x 0)]
        _ = (oblX6 x 4 - oblX6 x 3) * (-F.f 8 (x 0)) := by
          rw [F.zero 8 3 (by decide), F.zero 8 4 (by decide)]; ring
    have hrhs : 0 < (oblX6 x 4 - oblX6 x 3) * (-F.f 8 (x 0)) :=
      mul_pos (sub_pos.mpr h34) (by linarith [F.neg 8 0 (by decide)])
    nlinarith
  · -- t = 8 (`346`), `c3 = c4`
    intro h34
    have h8 : t * ⟪F.N 8, v30 x⟫ = (oblX6 x 4 - oblX6 x 3) * (-F.f 8 (x 0)) := by
      calc t * ⟪F.N 8, v30 x⟫ = ⟪F.N 8, t • v30 x⟫ := (inner_smul_right _ _ _).symm
        _ = oblX6 x 4 * (F.f 8 (x 3) - F.f 8 (x 4)) +
            (oblX6 x 4 - oblX6 x 3) * (F.f 8 (x 4) - F.f 8 (x 0)) := by
          rw [htv, inner_add_right, inner_smul_right, inner_smul_right,
            ← F.hN 8 (x 3) (x 4), ← F.hN 8 (x 4) (x 0)]
        _ = (oblX6 x 4 - oblX6 x 3) * (-F.f 8 (x 0)) := by
          rw [F.zero 8 3 (by decide), F.zero 8 4 (by decide)]; ring
    rw [h34, sub_self, zero_mul] at h8
    exact (mul_eq_zero.mp h8).resolve_left ht.ne'
  · -- t = 8 (`346`), `c4 < c3`
    intro h43
    have h8 : t * ⟪F.N 8, v30 x⟫ = (oblX6 x 4 - oblX6 x 3) * (-F.f 8 (x 0)) := by
      calc t * ⟪F.N 8, v30 x⟫ = ⟪F.N 8, t • v30 x⟫ := (inner_smul_right _ _ _).symm
        _ = oblX6 x 4 * (F.f 8 (x 3) - F.f 8 (x 4)) +
            (oblX6 x 4 - oblX6 x 3) * (F.f 8 (x 4) - F.f 8 (x 0)) := by
          rw [htv, inner_add_right, inner_smul_right, inner_smul_right,
            ← F.hN 8 (x 3) (x 4), ← F.hN 8 (x 4) (x 0)]
        _ = (oblX6 x 4 - oblX6 x 3) * (-F.f 8 (x 0)) := by
          rw [F.zero 8 3 (by decide), F.zero 8 4 (by decide)]; ring
    have hrhs : (oblX6 x 4 - oblX6 x 3) * (-F.f 8 (x 0)) < 0 :=
      mul_neg_of_neg_of_pos (sub_neg.mpr h43) (by linarith [F.neg 8 0 (by decide)])
    nlinarith

theorem v30_tilt {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    0 < ⟪F.N 0, x 0 - x 6⟫ ∧ 0 < ⟪F.N 3, x 0 - x 6⟫ ∧ ⟪F.N 8, x 0 - x 6⟫ < 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← F.hN 0 (x 0) (x 6), F.zero 0 0 (by decide), zero_sub]
    linarith [F.neg 0 6 (by decide)]
  · rw [← F.hN 3 (x 0) (x 6), F.zero 3 0 (by decide), zero_sub]
    linarith [F.neg 3 6 (by decide)]
  · rw [← F.hN 8 (x 0) (x 6), F.zero 8 6 (by decide), sub_zero]
    exact F.neg 8 0 (by decide)

theorem v30_depths {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (hab : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0)
    (hnb : F.f 3 (x 1) < F.f 3 (x 2)) (hc : oblX6 x 5 < oblX6 x 3) :
    ⟪x 0 - x 1, v30 x⟫ < 0 ∧
    0 < ⟪v30 x, v30 x⟫ ∧
    ∃ t : ℝ, 0 < t ∧
      oblX6 x 4 * ⟪x 3 - x 1, v30 x⟫ + (oblX6 x 3 - oblX6 x 4) * ⟪x 0 - x 1, v30 x⟫ -
        oblX6 x 3 * ⟪x 4 - x 1, v30 x⟫ = t * ⟪v30 x, v30 x⟫ := by
  have T := type24OfFac F
  have hD : 0 < D45 x := d45_pos F
  have hnB : 0 < nB x := (nB_pos_iff F).mpr hnb
  have hv_ne : v30 x ≠ 0 := by
    intro h0
    have hf1 := (v30_facings F hC hnb hc).2.1
    rw [h0, inner_zero_right] at hf1
    exact lt_irrefl 0 hf1
  have hv_pos : 0 < ⟪v30 x, v30 x⟫ := real_inner_self_pos.mpr hv_ne
  have hx01_pos : 0 < ⟪x 0 - x 1, x 0 - x 1⟫ :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide))
  have hz0 : ⟪x 0 - x 1, v30 x⟫ < 0 := by
    dsimp [v30]
    rw [inner_add_right, inner_smul_right, inner_smul_right]
    have := mul_nonpos_of_nonneg_of_nonpos hD.le hab
    nlinarith
  obtain ⟨s, t, -, ht, hdec, -, -, hc3⟩ := lemmaM_coords F
  have htv : t • v30 x = oblX6 x 4 • (x 3 - x 4) + (oblX6 x 4 - oblX6 x 3) • (x 4 - x 0) := by
    have hv := v30_eq F
    have h1 : t • v30 x = oblX6 x 4 • (t • (x 5 - x 0)) - (t * oblX6 x 5) • (x 4 - x 0) := by
      rw [hv]; module
    have h2 : t • (x 5 - x 0) = (x 3 - x 0) - s • (x 4 - x 0) := by
      rw [hdec]; abel
    have h3 : t * oblX6 x 5 = oblX6 x 3 - s * oblX6 x 4 := by linarith
    rw [h1, h2, h3]
    module
  have hid : oblX6 x 4 * ⟪x 3 - x 1, v30 x⟫ + (oblX6 x 3 - oblX6 x 4) * ⟪x 0 - x 1, v30 x⟫ -
      oblX6 x 3 * ⟪x 4 - x 1, v30 x⟫ = t * ⟪v30 x, v30 x⟫ := by
    have h1 : t * ⟪v30 x, v30 x⟫ = ⟪t • v30 x, v30 x⟫ := (real_inner_smul_left _ _ _).symm
    have hs1 : ⟪x 3 - x 4, v30 x⟫ = ⟪x 3 - x 1, v30 x⟫ - ⟪x 4 - x 1, v30 x⟫ := by
      rw [show x 3 - x 4 = (x 3 - x 1) - (x 4 - x 1) by abel, inner_sub_left]
    have hs2 : ⟪x 4 - x 0, v30 x⟫ = ⟪x 4 - x 1, v30 x⟫ - ⟪x 0 - x 1, v30 x⟫ := by
      rw [show x 4 - x 0 = (x 4 - x 1) - (x 0 - x 1) by abel, inner_sub_left]
    rw [htv, inner_add_left, real_inner_smul_left, real_inner_smul_left, hs1, hs2] at h1
    linarith
  exact ⟨hz0, hv_pos, t, ht, hid⟩

theorem v30_bound {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (hab : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0)
    (hnb : F.f 3 (x 1) < F.f 3 (x 2)) (hc : oblX6 x 5 < oblX6 x 3)
    (hU : ¬ LexAny F) :
    ⟪x 6 - x 1, v30 x⟫ ≤ 0 := by
  by_contra hcon
  push Not at hcon
  have T := type24OfFac F
  have hfac := v30_facings F hC hnb hc
  have htilt := v30_tilt F
  have ⟨hz0, hv_pos, t, ht, hid⟩ := v30_depths F hC hab hnb hc
  have hshift : ∀ v : Fin 7, ⟪x v, v30 x⟫ = ⟪x v - x 1, v30 x⟫ + ⟪x 1, v30 x⟫ := by
    intro v; rw [inner_sub_left]; ring
  rcases lt_or_ge (oblX6 x 3) (oblX6 x 4) with h34 | h43
  · -- 4-rim `![1, 0, 4, 6]` with `U = {0, 2, 3, 5, 6, 7, 8}`, `Dn = {1, 4}`, tilt `x 0 - x 6`.
    apply hU
    refine ⟨4, inferInstance, (![1, 0, 4, 6] : ZMod 4 → Fin 7), {0, 2, 3, 5, 6, 7, 8}, {1, 4},
      v30 x, x 0 - x 6, 0, by decide,
      (by intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)),
      (by unfold S0xCycUD; decide), ?_, ?_, ?_⟩
    · intro t ht'
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht'
      rcases ht' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inr ⟨hfac.1, Or.inl htilt.1⟩
      · exact Or.inl hfac.2.2.1
      · exact Or.inr ⟨hfac.2.2.2.1, Or.inl htilt.2.1⟩
      · exact Or.inl hfac.2.2.2.2.2.1
      · exact Or.inl hfac.2.2.2.2.2.2.1
      · exact Or.inl hfac.2.2.2.2.2.2.2.1
      · exact Or.inl (hfac.2.2.2.2.2.2.2.2.1 h34)
    · intro t ht'
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht'
      rcases ht' with rfl | rfl
      · exact Or.inl (by linarith [hfac.2.1])
      · exact Or.inl (by linarith [hfac.2.2.2.2.1])
    · refine robUniLex_four_of_mixed _ ⟨(0, 3), by decide, ?_⟩ ⟨(0, 1), by decide, ?_⟩
      · exact Or.inl (by dsimp only [Matrix.cons_val]; rw [hshift 1, hshift 6]; simp only [sub_self, inner_zero_left]; linarith)
      · exact Or.inl (by dsimp only [Matrix.cons_val]; rw [hshift 0, hshift 1]; simp only [sub_self, inner_zero_left]; linarith)
  · -- 5-rim `![1, 0, 4, 3, 6]` with `U = {0, 2, 3, 5, 6, 7}`, `Dn = {1, 4, 8}`, tilt `x 0 - x 6`.
    have hz4 : ⟪x 4 - x 1, v30 x⟫ < max ⟪x 0 - x 1, v30 x⟫ ⟪x 3 - x 1, v30 x⟫ := by
      have hc3_pos : 0 < oblX6 x 3 := T.X6_pos (v := 3) (by decide)
      have hc4_pos : 0 < oblX6 x 4 := T.X6_pos (v := 4) (by decide)
      have hlt : oblX6 x 3 * ⟪x 4 - x 1, v30 x⟫ <
          oblX6 x 4 * ⟪x 3 - x 1, v30 x⟫ + (oblX6 x 3 - oblX6 x 4) * ⟪x 0 - x 1, v30 x⟫ := by
        have hsp : 0 < t * ⟪v30 x, v30 x⟫ := mul_pos ht hv_pos
        linarith
      rcases le_total ⟪x 0 - x 1, v30 x⟫ ⟪x 3 - x 1, v30 x⟫ with h03 | h30
      · rw [max_eq_right h03]
        have hle : oblX6 x 4 * ⟪x 3 - x 1, v30 x⟫ +
            (oblX6 x 3 - oblX6 x 4) * ⟪x 0 - x 1, v30 x⟫ ≤
            oblX6 x 3 * ⟪x 3 - x 1, v30 x⟫ := by
          have : (oblX6 x 3 - oblX6 x 4) * ⟪x 0 - x 1, v30 x⟫ ≤
              (oblX6 x 3 - oblX6 x 4) * ⟪x 3 - x 1, v30 x⟫ :=
            mul_le_mul_of_nonneg_left h03 (sub_nonneg.mpr h43)
          linarith
        nlinarith
      · rw [max_eq_left h30]
        have hle : oblX6 x 4 * ⟪x 3 - x 1, v30 x⟫ +
            (oblX6 x 3 - oblX6 x 4) * ⟪x 0 - x 1, v30 x⟫ ≤
            oblX6 x 3 * ⟪x 0 - x 1, v30 x⟫ := by
          have : oblX6 x 4 * ⟪x 3 - x 1, v30 x⟫ ≤ oblX6 x 4 * ⟪x 0 - x 1, v30 x⟫ :=
            mul_le_mul_of_nonneg_left h30 hc4_pos.le
          linarith
        nlinarith
    apply hU
    refine ⟨5, inferInstance, (![1, 0, 4, 3, 6] : ZMod 5 → Fin 7), {0, 2, 3, 5, 6, 7}, {1, 4, 8},
      v30 x, x 0 - x 6, 0, by decide,
      (by intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)),
      (by unfold S0xCycUD; decide), ?_, ?_, ?_⟩
    · intro t ht'
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht'
      rcases ht' with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inr ⟨hfac.1, Or.inl htilt.1⟩
      · exact Or.inl hfac.2.2.1
      · exact Or.inr ⟨hfac.2.2.2.1, Or.inl htilt.2.1⟩
      · exact Or.inl hfac.2.2.2.2.2.1
      · exact Or.inl hfac.2.2.2.2.2.2.1
      · exact Or.inl hfac.2.2.2.2.2.2.2.1
    · intro t ht'
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht'
      rcases ht' with rfl | rfl | rfl
      · exact Or.inl (by linarith [hfac.2.1])
      · exact Or.inl (by linarith [hfac.2.2.2.2.1])
      · rcases eq_or_lt_of_le h43 with heq | hlt
        · exact Or.inr ⟨by rw [hfac.2.2.2.2.2.2.2.2.2.1 heq.symm, neg_zero],
            Or.inl (by linarith [htilt.2.2])⟩
        · exact Or.inl (by linarith [hfac.2.2.2.2.2.2.2.2.2.2 hlt])
    · refine robUniLex_five_v31 _ ?_ ?_ ?_
      · dsimp only [Matrix.cons_val]; rw [hshift 0, hshift 1]; simp only [sub_self, inner_zero_left]; linarith
      · dsimp only [Matrix.cons_val]; rw [hshift 1, hshift 6]; simp only [sub_self, inner_zero_left]; linarith
      · dsimp only [Matrix.cons_val]
        rw [hshift 4, hshift 0, hshift 3]
        rcases lt_max_iff.mp hz4 with h40 | h43'
        · exact lt_max_of_lt_left (by linarith)
        · exact lt_max_of_lt_right (by linarith)

theorem diag_of_bc_zero {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (hac : ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0) (hab : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0)
    (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ = 0)
    (hnc : F.f 3 (x 1) < F.f 3 (x 6)) (hnb : F.f 3 (x 1) < F.f 3 (x 2))
    (hb : oblX2 x 4 < oblX2 x 3) (hc : oblX6 x 5 < oblX6 x 3)
    (hU : ¬ LexAny F) :
    ⟪x 0 - x 1, x 2 - x 1⟫ = 0 ∧ ⟪x 0 - x 1, x 6 - x 1⟫ = 0 := by
  have hv31 := v31_bound F hC hac hnc hb hU
  have hv30 := v30_bound F hC hab hnb hc hU
  have hnC : 0 < nC x := (nC_pos_iff F).mpr hnc
  have hnB : 0 < nB x := (nB_pos_iff F).mpr hnb
  have h1 : -nC x * ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0 := by
    dsimp [v31] at hv31
    rw [inner_add_right, inner_smul_right, inner_smul_right, hbc, mul_zero, add_zero,
      show ⟪x 2 - x 1, x 0 - x 1⟫ = ⟪x 0 - x 1, x 2 - x 1⟫ from real_inner_comm _ _] at hv31
    exact hv31
  have h2 : -nB x * ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0 := by
    dsimp [v30] at hv30
    rw [inner_add_right, inner_smul_right, inner_smul_right,
      show ⟪x 6 - x 1, x 2 - x 1⟫ = ⟪x 2 - x 1, x 6 - x 1⟫ from real_inner_comm _ _,
      hbc, mul_zero, add_zero,
      show ⟪x 6 - x 1, x 0 - x 1⟫ = ⟪x 0 - x 1, x 6 - x 1⟫ from real_inner_comm _ _] at hv30
    exact hv30
  exact ⟨by nlinarith, by nlinarith⟩

/-! ### P1–P4: Leaf E05-P5 (`a5 > 1`, `σ < 1`, rim `0 4 6 2 5`, pivot `5`, edge `26`) -/

theorem w05_facings_P5 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha5 : 1 < oblX0 x 5) (hL : 0 < Lam5 x)
    (h346 : F.f 8 (x 0) < F.f 8 (x 5)) :
    ⟪F.N 0, x 5 - x 0⟫ < 0 ∧
    ⟪F.N 1, x 5 - x 0⟫ < 0 ∧
    ⟪F.N 2, x 5 - x 0⟫ = 0 ∧
    ⟪F.N 3, x 5 - x 0⟫ = 0 ∧
    ⟪F.N 4, x 5 - x 0⟫ < 0 ∧
    ⟪F.N 5, x 5 - x 0⟫ < 0 ∧
    0 < ⟪F.N 6, x 5 - x 0⟫ ∧
    0 < ⟪F.N 7, x 5 - x 0⟫ ∧
    0 < ⟪F.N 8, x 5 - x 0⟫ := by
  have T := type24OfFac F
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← F.hN 0 (x 5) (x 0), F.zero 0 0 (by decide), sub_zero]; exact F.neg 0 5 (by decide)
  · rw [← F.hN 1 (x 5) (x 0), F.zero 1 0 (by decide), sub_zero]; exact F.neg 1 5 (by decide)
  · rw [← F.hN 2 (x 5) (x 0), F.zero 2 5 (by decide), F.zero 2 0 (by decide), sub_self]
  · rw [← F.hN 3 (x 5) (x 0), F.zero 3 5 (by decide), F.zero 3 0 (by decide), sub_self]
  · rw [← F.hN 4 (x 5) (x 0), F.zero 4 0 (by decide), sub_zero]; exact F.neg 4 5 (by decide)
  · -- t = 5 (`126`): `(a5 - 1) * F.f 5 (x 0) < 0`
    rw [← F.hN 5 (x 5) (x 0)]
    have ev5 := fac_eval F 5 5
    rw [F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)] at ev5
    rw [ev5]
    have hmul : (oblX0 x 5 - 1) * F.f 5 (x 0) =
        (0 + oblX0 x 5 * (F.f 5 (x 0) - 0) + oblX2 x 5 * (0 - 0) + oblX6 x 5 * (0 - 0)) -
          F.f 5 (x 0) := by ring
    rw [← hmul]
    exact mul_neg_of_pos_of_neg (sub_pos.mpr ha5) (F.neg 5 0 (by decide))
  · -- t = 6 (`235`)
    rw [← F.hN 6 (x 5) (x 0), F.zero 6 5 (by decide), zero_sub]
    linarith [F.neg 6 0 (by decide)]
  · -- t = 7 (`236`): `(-F.f 7 (x 1)) * Lam5 x > 0`
    rw [← F.hN 7 (x 5) (x 0)]
    have ev7_3 := fac_eval F 7 3
    rw [F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at ev7_3
    have e3 := eq3 F
    have ha3 : oblX0 x 3 ≠ 0 := (T.X0_pos (v := 3) (by decide)).ne'
    have h7_id : oblX0 x 3 * (F.f 7 (x 0) - (1 + omega3 x) * F.f 7 (x 1)) = 0 := by
      linear_combination -ev7_3 + F.f 7 (x 1) * e3
    have hf7_0 : F.f 7 (x 0) = (1 + omega3 x) * F.f 7 (x 1) :=
      sub_eq_zero.mp ((mul_eq_zero.mp h7_id).resolve_left ha3)
    have ev7_5 := fac_eval F 7 5
    rw [F.zero 7 2 (by decide), F.zero 7 6 (by decide), hf7_0] at ev7_5
    have hdiff : F.f 7 (x 5) - (1 + omega3 x) * F.f 7 (x 1) = (-F.f 7 (x 1)) * Lam5 x := by
      dsimp [Lam5]; rw [ev7_5]; ring
    rw [hf7_0, hdiff]
    exact mul_pos (by linarith [F.neg 7 1 (by decide)]) hL
  · -- t = 8 (`346`)
    rw [← F.hN 8 (x 5) (x 0)]; linarith

theorem rows_P5 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    det3 (x 4 - x 0) (x 2 - x 6) (x 5 - x 0) = det24 x * R04 x ∧
    det3 (x 6 - x 4) (x 2 - x 6) (x 5 - x 0) = det24 x * R46 x ∧
    det3 (x 5 - x 2) (x 2 - x 6) (x 5 - x 0) =
      det24 x * (oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1) ∧
    det3 (x 0 - x 5) (x 2 - x 6) (x 6 - x 1) = det24 x * (1 - oblX0 x 5) := by
  have T := type24OfFac F
  have hrep : ∀ v : Fin 7, x v - x 1 =
      oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1) := by
    intro v; rw [T.rep v]; abel
  have hw : x 5 - x 0 = (oblX0 x 5 - 1) • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) +
      oblX6 x 5 • (x 6 - x 1) := by
    rw [show x 5 - x 0 = (x 5 - x 1) - (x 0 - x 1) by abel, hrep 5]; module
  have h26 : x 2 - x 6 = 0 • (x 0 - x 1) + 1 • (x 2 - x 1) + (-1 : ℝ) • (x 6 - x 1) := by
    module
  have h40 : x 4 - x 0 = (oblX0 x 4 - 1) • (x 0 - x 1) + oblX2 x 4 • (x 2 - x 1) +
      oblX6 x 4 • (x 6 - x 1) := by
    rw [show x 4 - x 0 = (x 4 - x 1) - (x 0 - x 1) by abel, hrep 4]; module
  have h64 : x 6 - x 4 = (-oblX0 x 4) • (x 0 - x 1) + (-oblX2 x 4) • (x 2 - x 1) +
      (1 - oblX6 x 4) • (x 6 - x 1) := by
    rw [show x 6 - x 4 = (x 6 - x 1) - (x 4 - x 1) by abel, hrep 4]; module
  have h52 : x 5 - x 2 = oblX0 x 5 • (x 0 - x 1) + (oblX2 x 5 - 1) • (x 2 - x 1) +
      oblX6 x 5 • (x 6 - x 1) := by
    rw [show x 5 - x 2 = (x 5 - x 1) - (x 2 - x 1) by abel, hrep 5]; module
  have h05 : x 0 - x 5 = (1 - oblX0 x 5) • (x 0 - x 1) + (-oblX2 x 5) • (x 2 - x 1) +
      (-oblX6 x 5) • (x 6 - x 1) := by
    rw [show x 0 - x 5 = (x 0 - x 1) - (x 5 - x 1) by abel, hrep 5]; module
  have h61 : x 6 - x 1 = 0 • (x 0 - x 1) + 0 • (x 2 - x 1) + 1 • (x 6 - x 1) := by module
  refine ⟨?_, ?_, ?_, ?_⟩
  · conv_lhs => arg 1; rw [h40]
    conv_lhs => arg 2; rw [h26]
    conv_lhs => arg 3; rw [hw]
    erw [M4.det3_frame x (oblX0 x 4 - 1) (oblX2 x 4) (oblX6 x 4) 0 1 (-1)
      (oblX0 x 5 - 1) (oblX2 x 5) (oblX6 x 5)]
    dsimp [R04]; ring
  · conv_lhs => arg 1; rw [h64]
    conv_lhs => arg 2; rw [h26]
    conv_lhs => arg 3; rw [hw]
    erw [M4.det3_frame x (-oblX0 x 4) (-oblX2 x 4) (1 - oblX6 x 4) 0 1 (-1)
      (oblX0 x 5 - 1) (oblX2 x 5) (oblX6 x 5)]
    dsimp [R46]; ring
  · conv_lhs => arg 1; rw [h52]
    conv_lhs => arg 2; rw [h26]
    conv_lhs => arg 3; rw [hw]
    erw [M4.det3_frame x (oblX0 x 5) (oblX2 x 5 - 1) (oblX6 x 5) 0 1 (-1)
      (oblX0 x 5 - 1) (oblX2 x 5) (oblX6 x 5)]
    ring
  · conv_lhs => arg 1; rw [h05]
    conv_lhs => arg 2; rw [h26]
    conv_lhs => arg 3; rw [h61]
    erw [M4.det3_frame x (1 - oblX0 x 5) (-oblX2 x 5) (-oblX6 x 5) 0 1 (-1) 0 0 1]
    ring

private theorem det3_P5_tie_row (x : Fin 7 → ℝ³) (ε : ℝ) :
    det3 (x 0 - x 5) (x 2 - x 6) ((x 5 - x 0) + ε • (x 6 - x 1)) =
      ε * det3 (x 0 - x 5) (x 2 - x 6) (x 6 - x 1) := by
  simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  ring

private theorem hev_neg_aux (x : Fin 7 → ℝ³) (w05 d1 u a b : ℝ³)
    (hu : ⟪u, w05⟫ < 0) (hdet0 : det24 x * det3 a b w05 < 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < det24 x * (⟪u, w05 + ε • d1⟫ * det3 a b (w05 + ε • d1)) := by
  have hc1 : Continuous fun ε : ℝ => ⟪u, w05 + ε • d1⟫ := by fun_prop
  have hc2 : Continuous fun ε : ℝ => det24 x * det3 a b (w05 + ε • d1) := by
    simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; fun_prop
  have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪u, w05 + ε • d1⟫ < 0 :=
    (hc1.continuousAt.eventually (gt_mem_nhds (by simpa only [zero_smul, add_zero] using hu))).filter_mono nhdsWithin_le_nhds
  have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), det24 x * det3 a b (w05 + ε • d1) < 0 :=
    (hc2.continuousAt.eventually (gt_mem_nhds (by simpa only [zero_smul, add_zero] using hdet0))).filter_mono nhdsWithin_le_nhds
  filter_upwards [h1, h2] with ε hε1 hε2
  have := mul_pos_of_neg_of_neg hε1 hε2; linarith

private theorem hev_pos_aux (x : Fin 7 → ℝ³) (w05 d1 u a b : ℝ³)
    (hu : 0 < ⟪u, w05⟫) (hdet0 : 0 < det24 x * det3 a b w05) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < det24 x * (⟪u, w05 + ε • d1⟫ * det3 a b (w05 + ε • d1)) := by
  have hc1 : Continuous fun ε : ℝ => ⟪u, w05 + ε • d1⟫ := by fun_prop
  have hc2 : Continuous fun ε : ℝ => det24 x * det3 a b (w05 + ε • d1) := by
    simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; fun_prop
  have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪u, w05 + ε • d1⟫ :=
    (hc1.continuousAt.eventually (lt_mem_nhds (by simpa only [zero_smul, add_zero] using hu))).filter_mono nhdsWithin_le_nhds
  have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < det24 x * det3 a b (w05 + ε • d1) :=
    (hc2.continuousAt.eventually (lt_mem_nhds (by simpa only [zero_smul, add_zero] using hdet0))).filter_mono nhdsWithin_le_nhds
  filter_upwards [h1, h2] with ε hε1 hε2
  have := mul_pos hε1 hε2; linarith

theorem splitAny24_E05P5 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (ha5 : 1 < oblX0 x 5) (hL : 0 < Lam5 x)
    (h346 : F.f 8 (x 0) < F.f 8 (x 5)) (hnc : F.f 3 (x 1) < F.f 3 (x 6))
    (hR46 : R46 x < 0) (hR04 : R04 x < 0)
    (hz : ⟪x 4 - x 1, x 5 - x 0⟫ < ⟪x 5 - x 1, x 5 - x 0⟫ ∧
          ⟪x 6 - x 1, x 5 - x 0⟫ < ⟪x 5 - x 1, x 5 - x 0⟫ ∧
          ⟪x 5 - x 1, x 5 - x 0⟫ < ⟪x 2 - x 1, x 5 - x 0⟫) :
    SplitAny24 F := by
  have T := type24OfFac F
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hd2 : 0 < det24 x * det24 x := mul_self_pos.mpr T.det_ne
  have hfac := w05_facings_P5 F ha5 hL h346
  have hrows := rows_P5 F
  let c : ZMod 5 → Fin 7 := ![0, 4, 6, 2, 5]
  let pat : Fin 9 → Bool := fun t => decide (t = 3 ∨ t = 6 ∨ t = 7 ∨ t = 8)
  let w05 : ℝ³ := x 5 - x 0
  let d1 : ℝ³ := x 6 - x 1
  -- Tilt signs at `d1 = x 6 - x 1` for the two edge-on facets `2` (`025`) and `3` (`0345`):
  have hd1_2 : 0 < -⟪F.N 2, d1⟫ := by
    dsimp [d1]
    rw [← F.hN 2 (x 6) (x 1)]
    have ev25 := fac_eval F 2 5
    rw [F.zero 2 5 (by decide), F.zero 2 0 (by decide), F.zero 2 2 (by decide)] at ev25
    have e5 := eq5 F
    have h1' : F.f 2 (x 1) * (1 - oblX0 x 5 - oblX2 x 5) +
        oblX6 x 5 * (F.f 2 (x 6) - F.f 2 (x 1)) = 0 := by
      linear_combination -ev25
    have h2' : oblX6 x 5 * ((F.f 2 (x 6) - F.f 2 (x 1)) - F.f 2 (x 1) * omega5 x) = 0 := by
      linear_combination h1' + F.f 2 (x 1) * e5
    have h6_eq : F.f 2 (x 6) - F.f 2 (x 1) = F.f 2 (x 1) * omega5 x :=
      sub_eq_zero.mp ((mul_eq_zero.mp h2').resolve_left hc5.ne')
    rw [h6_eq, ← neg_mul]
    exact mul_pos (by linarith [F.neg 2 1 (by decide)]) hC.2.2.1
  have hd1_3 : 0 < ⟪F.N 3, d1⟫ := by
    dsimp [d1]; rw [← F.hN 3 (x 6) (x 1)]; exact sub_pos.mpr hnc
  have hlex_fac : ∀ t : Fin 9,
      LexPos3 (if pat t then ⟪F.N t, w05⟫ else -⟪F.N t, w05⟫)
              (if pat t then ⟪F.N t, d1⟫ else -⟪F.N t, d1⟫) 0 := by
    intro t
    fin_cases t <;> simp [pat]
    · exact Or.inl (by linarith [hfac.1])
    · exact Or.inl (by linarith [hfac.2.1])
    · exact Or.inr ⟨by rw [hfac.2.2.1, neg_zero], Or.inl hd1_2⟩
    · exact Or.inr ⟨hfac.2.2.2.1, Or.inl hd1_3⟩
    · exact Or.inl (by linarith [hfac.2.2.2.2.1])
    · exact Or.inl (by linarith [hfac.2.2.2.2.2.1])
    · exact Or.inl hfac.2.2.2.2.2.2.1
    · exact Or.inl hfac.2.2.2.2.2.2.2.1
    · exact Or.inl hfac.2.2.2.2.2.2.2.2
  have hev_fac : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ t : Fin 9, 0 < (if pat t then ⟪F.N t, w05 + ε • d1⟫ else -⟪F.N t, w05 + ε • d1⟫) := by
    rw [eventually_all]
    intro t
    filter_upwards [ev_lexPos3 (hlex_fac t)] with ε hε
    by_cases ht : pat t <;> simp only [ht, ↓reduceIte, Bool.false_eq_true] at hε ⊢ <;>
      simp only [inner_add_right, inner_smul_right, mul_zero, add_zero] at hε ⊢ <;> linarith
  have hz05 : ⟪x 0 - x 5, w05⟫ < 0 := by
    have : ⟪x 0 - x 5, w05⟫ = -⟪w05, w05⟫ := by
      dsimp [w05]; rw [← neg_sub, inner_neg_left]
    have hw_ne : w05 ≠ 0 := sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide)
    linarith [real_inner_self_pos.mpr hw_ne]
  have hz45 : ⟪x 4 - x 5, w05⟫ < 0 := by
    rw [show x 4 - x 5 = (x 4 - x 1) - (x 5 - x 1) by abel, inner_sub_left]; linarith [hz.1]
  have hz65 : ⟪x 6 - x 5, w05⟫ < 0 := by
    rw [show x 6 - x 5 = (x 6 - x 1) - (x 5 - x 1) by abel, inner_sub_left]; linarith [hz.2.1]
  have hz25 : 0 < ⟪x 2 - x 5, w05⟫ := by
    rw [show x 2 - x 5 = (x 2 - x 1) - (x 5 - x 1) by abel, inner_sub_left]; linarith [hz.2.2]
  have hev_rows : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ i j : ZMod 5, i ≠ 2 → (j = i ∨ j = i + 1) → j ≠ 4 →
        0 < det24 x * (⟪x (c j) - x (c 4), w05 + ε • d1⟫ *
          det3 (x (c (i + 1)) - x (c i)) (x (c (2 + 1)) - x (c 2)) (w05 + ε • d1)) := by
    rw [eventually_all]; intro i
    rw [eventually_all]; intro j
    have hc0 : c 0 = 0 := rfl
    have hc1 : c 1 = 4 := rfl
    have hc2 : c 2 = 6 := rfl
    have hc3 : c 3 = 2 := rfl
    have hc4 : c 4 = 5 := rfl
    have he0 : (0 : ZMod 5) + 1 = 1 := rfl
    have he1 : (1 : ZMod 5) + 1 = 2 := rfl
    have he2 : (2 : ZMod 5) + 1 = 3 := rfl
    have he3 : (3 : ZMod 5) + 1 = 4 := rfl
    have he4 : (4 : ZMod 5) + 1 = 0 := rfl
    have hi : ∀ i : ZMod 5, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by decide
    rcases hi i with rfl | rfl | rfl | rfl | rfl
    · by_cases hj : j = 0 ∨ j = 0 + 1
      · rcases hj with rfl | rfl
        · simp only [he0, he2, hc0, hc1, hc2, hc3, hc4]
          have hdet0 : det24 x * det3 (x 4 - x 0) (x 2 - x 6) w05 < 0 := by
            dsimp [w05]; rw [hrows.1, ← mul_assoc]; exact mul_neg_of_pos_of_neg hd2 hR04
          exact (hev_neg_aux x w05 d1 _ _ _ hz05 hdet0).mono fun ε hε _ _ _ => hε
        · simp only [he0, he2, hc0, hc1, hc2, hc3, hc4]
          have hdet0 : det24 x * det3 (x 4 - x 0) (x 2 - x 6) w05 < 0 := by
            dsimp [w05]; rw [hrows.1, ← mul_assoc]; exact mul_neg_of_pos_of_neg hd2 hR04
          exact (hev_neg_aux x w05 d1 _ _ _ hz45 hdet0).mono fun ε hε _ _ _ => hε
      · exact Eventually.of_forall fun _ _ h => absurd h hj
    · by_cases hj : j = 1 ∨ j = 1 + 1
      · rcases hj with rfl | rfl
        · simp only [he1, he2, hc1, hc2, hc3, hc4]
          have hdet0 : det24 x * det3 (x 6 - x 4) (x 2 - x 6) w05 < 0 := by
            dsimp [w05]; rw [hrows.2.1, ← mul_assoc]; exact mul_neg_of_pos_of_neg hd2 hR46
          exact (hev_neg_aux x w05 d1 _ _ _ hz45 hdet0).mono fun ε hε _ _ _ => hε
        · simp only [he1, he2, hc1, hc2, hc3, hc4]
          have hdet0 : det24 x * det3 (x 6 - x 4) (x 2 - x 6) w05 < 0 := by
            dsimp [w05]; rw [hrows.2.1, ← mul_assoc]; exact mul_neg_of_pos_of_neg hd2 hR46
          exact (hev_neg_aux x w05 d1 _ _ _ hz65 hdet0).mono fun ε hε _ _ _ => hε
      · exact Eventually.of_forall fun _ _ h => absurd h hj
    · exact Eventually.of_forall fun _ h => absurd rfl h
    · by_cases hj : j = 3 ∨ j = 3 + 1
      · rcases hj with rfl | rfl
        · simp only [he3, he2, hc2, hc3, hc4]
          have hdet0 : 0 < det24 x * det3 (x 5 - x 2) (x 2 - x 6) w05 := by
            dsimp [w05]; rw [hrows.2.2.1, ← mul_assoc]
            exact mul_pos hd2 (by linarith only [ha5, hb5, hc5])
          exact (hev_pos_aux x w05 d1 _ _ _ hz25 hdet0).mono fun ε hε _ _ _ => hε
        · exact Eventually.of_forall fun _ _ _ h => absurd rfl h
      · exact Eventually.of_forall fun _ _ h => absurd h hj
    · by_cases hj : j = 4 ∨ j = 4 + 1
      · rcases hj with rfl | rfl
        · exact Eventually.of_forall fun _ _ _ h => absurd rfl h
        · have hc1_fn : Continuous fun ε : ℝ => ⟪x 0 - x 5, w05 + ε • d1⟫ := by fun_prop
          have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪x 0 - x 5, w05 + ε • d1⟫ < 0 :=
            (hc1_fn.continuousAt.eventually (gt_mem_nhds (by simpa only [zero_smul, add_zero] using hz05))).filter_mono nhdsWithin_le_nhds
          have hdet_eq : ∀ ε : ℝ,
              det24 x * det3 (x 0 - x 5) (x 2 - x 6) (w05 + ε • d1) =
              ε * ((det24 x * det24 x) * (1 - oblX0 x 5)) := by
            intro ε
            dsimp [w05, d1]
            rw [det3_P5_tie_row, hrows.2.2.2]
            ring
          simp only [he4, he2, hc0, hc2, hc3, hc4]
          filter_upwards [h1, self_mem_nhdsWithin] with ε hε1 (hε_pos : 0 < ε) _ _ _
          have h2 : det24 x * det3 (x 0 - x 5) (x 2 - x 6) (w05 + ε • d1) < 0 := by
            rw [hdet_eq ε]
            exact mul_neg_of_pos_of_neg hε_pos (mul_neg_of_pos_of_neg hd2 (sub_neg.mpr ha5))
          rw [mul_left_comm]
          exact mul_pos_of_neg_of_neg hε1 h2
      · exact Eventually.of_forall fun _ _ h => absurd h hj
  obtain ⟨ε, ⟨hfac_ε, hrows_ε⟩, _⟩ := ((hev_fac.and hev_rows).and self_mem_nhdsWithin).exists
  have hdet_eq : ∀ u v w : ℝ³, Minimality.Split.det3 u v w = Minimality.det3 u v w := by
    intro u v w
    simp [Minimality.Split.det3, Minimality.det3_expand]
  refine ⟨5, inferInstance, c, pat, w05 + ε • d1, 0, 2, 4, det24 x, by decide,
    (by intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)),
    (by unfold S0xCycOK; decide), ?_, by decide, by decide,
    fun i j hia hj hjc => by simpa only [hdet_eq] using hrows_ε i j hia hj hjc⟩
  intro t
  have ht := hfac_ε t
  constructor
  · intro hpt; simp only [hpt, ↓reduceIte] at ht; exact Or.inl ht
  · intro hpt; simp only [hpt, Bool.false_eq_true, ↓reduceIte] at ht; exact Or.inl ht

theorem isRupert_of_E05P5 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (ha5 : 1 < oblX0 x 5) (hL : 0 < Lam5 x)
    (h346 : F.f 8 (x 0) < F.f 8 (x 5)) (hnc : F.f 3 (x 1) < F.f 3 (x 6))
    (hR46 : R46 x < 0) (hR04 : R04 x < 0)
    (hz : ⟪x 4 - x 1, x 5 - x 0⟫ < ⟪x 5 - x 1, x 5 - x 0⟫ ∧
          ⟪x 6 - x 1, x 5 - x 0⟫ < ⟪x 5 - x 1, x 5 - x 0⟫ ∧
          ⟪x 5 - x 1, x 5 - x 0⟫ < ⟪x 2 - x 1, x 5 - x 0⟫) :
    IsRupert (Finset.univ.image x) :=
  splitAny24_isRupert F (splitAny24_E05P5 F hC ha5 hL h346 hnc hR46 hR04 hz)

end Minimality.T24.A7
