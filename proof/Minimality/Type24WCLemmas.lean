module

public import Minimality.Type24WCOrder
public import Minimality.Type24SAT.K24.CornerOB1

/-!
# Carbon A83 Lemmas L1, L2, L3, L5 for the `w_C` certificate (`FO1`–`FO4`)

* **FO1 (`L1`):**
  - `wc_cramer_signs`: `CbarIn x → oblX2 x 3 < 1 → oblX0 x 3 * oblX6 x 5 - oblX0 x 5 * oblX6 x 3 < 0 ∧ oblX0 x 3 * oblX2 x 4 - oblX0 x 4 * oblX2 x 3 < 0`.
  - `wc_wallI_pos_368`: `CbarIn x → oblX2 x 3 < 1 → ∀ t ∈ {3, 6, 8}, 0 < ⟪F.N t, capView x 1 0 (omega3 x)⟫`.
  - `wc_window_nonempty`: `CbarIn x → oblX2 x 3 < 1 → cLo x < omega3 x` and every `cc ∈ Set.Ioo (cLo x) (omega3 x)` satisfies `hw5, hw3, h368_pos, h368_neg, h368_zero` of `wc_edgePlaneAny`.
* **FO3 (`L3`):**
  - `wc_apex_gap`: `CbarIn x → OB1 x → oblX2 x 3 < 1 → oblX2 x 5 < 1 → cc ∈ Set.Ioo (cLo x) (omega3 x) → wcYHat x 2 2 cc < wcYHat x 1 2 cc`.
* **FO2 (`L2`):**
  - `wcCertAt_of_yHat`: scale-free `sh = -1` reduction of `WCCertAt x F cc` for both signs of `det24 x`.
* **FO4 (`L5`):**
  - `wc_r60_z1_z3_nonneg`: `HoleLeaf x F → OB1 x → oblX2 x 3 ≤ 1 → oblX2 x 5 ≤ 1 → cLo x < r60 → r60 < omega3 x → ⟪x 0 - x 6, capView x 1 0 r60⟫ = 0 → 0 ≤ ⟪x 5 - x 6, capView x 1 0 r60⟫ ∧ 0 ≤ ⟪x 3 - x 6, capView x 1 0 r60⟫`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace Topology
open Finset Filter
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.M4
open Minimality.T24.HC Minimality.T24.TwoCone Minimality.H24K.SAT

namespace Minimality.T24.WC

section Defs

/-- Pure-shape lower bound `r_8^*(x)` from facet `8` (`{3, 4, 6}`). -/
noncomputable def wcR8 (x : Fin 7 → ℝ³) : ℝ :=
  (oblX2 x 4 * (1 - oblX6 x 3) - oblX2 x 3 * (1 - oblX6 x 4)) /
    (oblX0 x 4 * oblX2 x 3 - oblX0 x 3 * oblX2 x 4)

/-- Pure-shape lower bound `r_6^*(x)` from facet `6` (`{2, 3, 5}`). -/
noncomputable def wcR6 (x : Fin 7 → ℝ³) : ℝ :=
  if 0 < oblX0 x 5 * (1 - oblX2 x 3) - oblX0 x 3 * (1 - oblX2 x 5) then
    ((1 - oblX2 x 3) * oblX6 x 5 - (1 - oblX2 x 5) * oblX6 x 3) /
      (oblX0 x 5 * (1 - oblX2 x 3) - oblX0 x 3 * (oblX2 x 5 |> fun b5 => 1 - b5))
  else 0

/-- Exact lower ceiling `c_c^lo(x)` of the `wcCell_eventually` window. -/
noncomputable def cLo (x : Fin 7 → ℝ³) : ℝ :=
  max (1 / omega5 x) (max (wcR8 x) (wcR6 x))

/-- Relative depth `z_j(c_c) = ⟪x (wcRim j) - x 6, capView x 1 0 cc⟫`. -/
noncomputable def wcZ (x : Fin 7 → ℝ³) (j : ZMod 5) (cc : ℝ) : ℝ :=
  ⟪x (wcRim j) - x 6, capView x 1 0 cc⟫

/-- Shape weights `delta = ![-b5, -(1 - b5), 1 - b3, b3, 0]` on `wcRim`. -/
noncomputable def wcDelta (x : Fin 7 → ℝ³) : ZMod 5 → ℝ :=
  ![-oblX2 x 5, -(1 - oblX2 x 5), 1 - oblX2 x 3, oblX2 x 3, 0]

/-- Rescaled linearized spin coordinate `yHat_{i,j}(c_c)`. -/
noncomputable def wcYHat (x : Fin 7 → ℝ³) (i j : ZMod 5) (cc : ℝ) : ℝ :=
  ⟪Split.Slope.linSpinVec (fun t => x (wcRim t)) 4 i j, capView x 1 0 cc⟫ / wcDelta x i

end Defs

/-! ## FO1: Carbon A83 Lemma L1 -/

private theorem fac6_eq {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (v : Fin 7) (hv : v ∈ s0x_S24 6) :
    oblX0 x v * ⟪F.N 6, x 0 - x 1⟫ + oblX6 x v * ⟪F.N 6, x 6 - x 1⟫ =
      (1 - oblX2 x v) * (-F.f 6 (x 1)) := by
  have ev := M4.fac_eval F 6 v
  rw [F.zero 6 v hv, F.zero 6 2 (by decide)] at ev
  simp only [F.inner_sub]
  linarith

private theorem fac8_eq {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (v : Fin 7) (hv : v ∈ s0x_S24 8) :
    oblX0 x v * ⟪F.N 8, x 0 - x 1⟫ + oblX2 x v * ⟪F.N 8, x 2 - x 1⟫ =
      (1 - oblX6 x v) * (-F.f 8 (x 1)) := by
  have ev := M4.fac_eval F 8 v
  rw [F.zero 8 v hv, F.zero 8 6 (by decide)] at ev
  simp only [F.inner_sub]
  linarith

private theorem fac7_lt {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (v : Fin 7) (hv : v ∉ s0x_S24 7) :
    oblX2 x v + oblX6 x v - 1 < omega3 x * oblX0 x v := by
  have hkap7 : 0 < -F.f 7 (x 1) := neg_pos.mpr (F.neg 7 1 (by decide))
  have ev3 := M4.fac_eval F 7 3
  rw [F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at ev3
  have e3 : oblX2 x 3 + oblX6 x 3 - 1 = omega3 x * oblX0 x 3 := by
    have := M4.eq3 F; linarith
  have hN7a : oblX0 x 3 * (F.f 7 (x 0) - F.f 7 (x 1)) =
      oblX0 x 3 * (omega3 x * F.f 7 (x 1)) := by
    linear_combination -ev3 + F.f 7 (x 1) * e3
  have ha3 : oblX0 x 3 ≠ 0 := ((M4.type24OfFac F).X0_pos (v := 3) (by decide)).ne'
  have hfa : F.f 7 (x 0) - F.f 7 (x 1) = omega3 x * F.f 7 (x 1) :=
    mul_left_cancel₀ ha3 hN7a
  have ev := M4.fac_eval F 7 v
  rw [F.zero 7 2 (by decide), F.zero 7 6 (by decide), hfa] at ev
  have hneg := F.neg 7 v hv
  have hmul : (-F.f 7 (x 1)) * (oblX2 x v + oblX6 x v - 1 - omega3 x * oblX0 x v) < 0 := by
    have heq : (-F.f 7 (x 1)) * (oblX2 x v + oblX6 x v - 1 - omega3 x * oblX0 x v) = F.f 7 (x v) := by
      linear_combination -ev
    rw [heq]; exact hneg
  by_contra hle
  push Not at hle
  have := mul_nonneg hkap7.le (sub_nonneg.mpr hle)
  linarith

private theorem wc_cramer_signs_raw {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    oblX0 x 3 * oblX6 x 5 - oblX0 x 5 * oblX6 x 3 < 0 ∧
    oblX0 x 3 * oblX2 x 4 - oblX0 x 4 * oblX2 x 3 < 0 := by
  have T := M4.type24OfFac F
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have ha4 : 0 < oblX0 x 4 := T.X0_pos (v := 4) (by decide)
  have ha5 : 0 < oblX0 x 5 := T.X0_pos (v := 5) (by decide)
  -- Part 1: a3 * c5 - a5 * c3 < 0
  have hc53 : oblX0 x 3 * oblX6 x 5 - oblX0 x 5 * oblX6 x 3 < 0 := by
    have h63 := fac6_eq F 3 (by decide)
    have h65 := fac6_eq F 5 (by decide)
    have hkap6 : 0 < -F.f 6 (x 1) := neg_pos.mpr (F.neg 6 1 (by decide))
    have h66 : 0 < -F.f 6 (x 6) := neg_pos.mpr (F.neg 6 6 (by decide))
    have hkap_diff : -F.f 6 (x 1) - ⟪F.N 6, x 6 - x 1⟫ = -F.f 6 (x 6) := by
      rw [F.inner_sub]; ring
    have h75 := fac7_lt F 5 (by decide)
    have e3 := M4.eq3 F
    have hω : oblX0 x 3 * (oblX2 x 5 + oblX6 x 5 - 1) <
        oblX0 x 5 * (oblX2 x 3 + oblX6 x 3 - 1) := by
      have h1 := mul_lt_mul_of_pos_left h75 ha3
      linear_combination h1 - oblX0 x 5 * e3
    have hcr : (oblX0 x 3 * oblX6 x 5 - oblX0 x 5 * oblX6 x 3) * ⟪F.N 6, x 6 - x 1⟫ =
        (oblX0 x 3 * (1 - oblX2 x 5) - oblX0 x 5 * (1 - oblX2 x 3)) * (-F.f 6 (x 1)) := by
      linear_combination oblX0 x 3 * h65 - oblX0 x 5 * h63
    have hprod : (oblX0 x 3 * oblX6 x 5 - oblX0 x 5 * oblX6 x 3) * (-F.f 6 (x 6)) < 0 := by
      have hsub : oblX0 x 3 * oblX6 x 5 - oblX0 x 5 * oblX6 x 3 -
          (oblX0 x 3 * (1 - oblX2 x 5) - oblX0 x 5 * (1 - oblX2 x 3)) < 0 := by
        linarith
      have heq : (oblX0 x 3 * oblX6 x 5 - oblX0 x 5 * oblX6 x 3) * (-F.f 6 (x 6)) =
          (oblX0 x 3 * oblX6 x 5 - oblX0 x 5 * oblX6 x 3 -
            (oblX0 x 3 * (1 - oblX2 x 5) - oblX0 x 5 * (1 - oblX2 x 3))) * (-F.f 6 (x 1)) := by
        linear_combination -hcr - (oblX0 x 3 * oblX6 x 5 - oblX0 x 5 * oblX6 x 3) * hkap_diff
      rw [heq]; exact mul_neg_of_neg_of_pos hsub hkap6
    by_contra hge
    push Not at hge
    have := mul_nonneg hge h66.le
    linarith
  -- Part 2: a3 * b4 - a4 * b3 < 0
  have hb43 : oblX0 x 3 * oblX2 x 4 - oblX0 x 4 * oblX2 x 3 < 0 := by
    have h83 := fac8_eq F 3 (by decide)
    have h84 := fac8_eq F 4 (by decide)
    have hkap8 : 0 < -F.f 8 (x 1) := neg_pos.mpr (F.neg 8 1 (by decide))
    have h82 : 0 < -F.f 8 (x 2) := neg_pos.mpr (F.neg 8 2 (by decide))
    have hkap_diff : -F.f 8 (x 1) - ⟪F.N 8, x 2 - x 1⟫ = -F.f 8 (x 2) := by
      rw [F.inner_sub]; ring
    have h74 := fac7_lt F 4 (by decide)
    have e3 := M4.eq3 F
    have hω : oblX0 x 3 * (oblX2 x 4 + oblX6 x 4 - 1) <
        oblX0 x 4 * (oblX2 x 3 + oblX6 x 3 - 1) := by
      have h1 := mul_lt_mul_of_pos_left h74 ha3
      linear_combination h1 - oblX0 x 4 * e3
    have hcr : (oblX0 x 3 * oblX2 x 4 - oblX0 x 4 * oblX2 x 3) * ⟪F.N 8, x 2 - x 1⟫ =
        (oblX0 x 3 * (1 - oblX6 x 4) - oblX0 x 4 * (1 - oblX6 x 3)) * (-F.f 8 (x 1)) := by
      linear_combination oblX0 x 3 * h84 - oblX0 x 4 * h83
    have hprod : (oblX0 x 3 * oblX2 x 4 - oblX0 x 4 * oblX2 x 3) * (-F.f 8 (x 2)) < 0 := by
      have hsub : oblX0 x 3 * oblX2 x 4 - oblX0 x 4 * oblX2 x 3 -
          (oblX0 x 3 * (1 - oblX6 x 4) - oblX0 x 4 * (1 - oblX6 x 3)) < 0 := by
        linarith
      have heq : (oblX0 x 3 * oblX2 x 4 - oblX0 x 4 * oblX2 x 3) * (-F.f 8 (x 2)) =
          (oblX0 x 3 * oblX2 x 4 - oblX0 x 4 * oblX2 x 3 -
            (oblX0 x 3 * (1 - oblX6 x 4) - oblX0 x 4 * (1 - oblX6 x 3))) * (-F.f 8 (x 1)) := by
        linear_combination -hcr - (oblX0 x 3 * oblX2 x 4 - oblX0 x 4 * oblX2 x 3) * hkap_diff
      rw [heq]; exact mul_neg_of_neg_of_pos hsub hkap8
    by_contra hge
    push Not at hge
    have := mul_nonneg hge h82.le
    linarith
  exact ⟨hc53, hb43⟩

/-- **FO1(a) (Cramer sign conditions):** `CbarIn x` and `oblX2 x 3 < 1` give
`a3 * c5 - a5 * c3 < 0` and `a3 * b4 - a4 * b3 < 0`. -/
theorem wc_cramer_signs {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (_hC : CbarIn x)
    (_hb3 : oblX2 x 3 < 1) :
    oblX0 x 3 * oblX6 x 5 - oblX0 x 5 * oblX6 x 3 < 0 ∧
    oblX0 x 3 * oblX2 x 4 - oblX0 x 4 * oblX2 x 3 < 0 :=
  wc_cramer_signs_raw F

/-- **FO1(b) (Upper ceiling positivity on facets `{3, 6, 8}`):** `CbarIn x` and `oblX2 x 3 < 1`
imply `0 < ⟪F.N t, capView x 1 0 (omega3 x)⟫` for all `t ∈ {3, 6, 8}`. -/
theorem wc_wallI_pos_368 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (_hC : CbarIn x)
    (hb3 : oblX2 x 3 < 1) :
    ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)), 0 < ⟪F.N t, capView x 1 0 (omega3 x)⟫ := by
  intro t ht
  have T := M4.type24OfFac F
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hb3_pos : 0 < oblX2 x 3 := T.X2_pos (v := 3) (by decide)
  have ht3 : 3 ∈ s0x_S24 t := by
    simp only [mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl <;> decide
  have ev := M4.fac_eval F t 3
  rw [F.zero t 3 ht3] at ev
  have e3 := M4.eq3 F
  have hid : oblX0 x 3 * ⟪F.N t, capView x 1 0 (omega3 x)⟫ =
      (oblX2 x 3 - 1) * F.f t (x 6) - oblX2 x 3 * F.f t (x 2) := by
    dsimp [capView]
    simp only [inner_add_right, real_inner_smul_right, F.inner_sub]
    linear_combination -ev + (F.f t (x 1) - F.f t (x 6)) * e3
  have hrhs : 0 < (oblX2 x 3 - 1) * F.f t (x 6) - oblX2 x 3 * F.f t (x 2) := by
    simp only [mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · have h6 : F.f 3 (x 6) < 0 := F.neg 3 6 (by decide)
      have h2 : F.f 3 (x 2) < 0 := F.neg 3 2 (by decide)
      nlinarith
    · have h6 : F.f 6 (x 6) < 0 := F.neg 6 6 (by decide)
      have h2 : F.f 6 (x 2) = 0 := F.zero 6 2 (by decide)
      rw [h2]; nlinarith
    · have h6 : F.f 8 (x 6) = 0 := F.zero 8 6 (by decide)
      have h2 : F.f 8 (x 2) < 0 := F.neg 8 2 (by decide)
      rw [h6]; nlinarith
  rw [← hid] at hrhs
  exact pos_of_mul_pos_right hrhs ha3.le

/-- **FO1(c) (Nonempty window `(cLo x, omega3 x)`):** `CbarIn x` and `oblX2 x 3 < 1` imply
`cLo x < omega3 x`, and every `cc ∈ Set.Ioo (cLo x) (omega3 x)` satisfies all five window
hypotheses (`hw5`, `hw3`, `h368_pos`, `h368_neg`, `h368_zero`) of `wc_edgePlaneAny`. -/
theorem wc_window_nonempty {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (hb3 : oblX2 x 3 < 1) :
    cLo x < omega3 x ∧
    ∀ cc ∈ Set.Ioo (cLo x) (omega3 x),
      1 / omega5 x < cc ∧ cc < omega3 x ∧
      (∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
        0 < ⟪F.N t, x 6 - x 1⟫ → -⟪F.N t, x 0 - x 1⟫ / ⟪F.N t, x 6 - x 1⟫ < cc) ∧
      (∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
        ⟪F.N t, x 6 - x 1⟫ < 0 → cc < -⟪F.N t, x 0 - x 1⟫ / ⟪F.N t, x 6 - x 1⟫) ∧
      (∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
        ⟪F.N t, x 6 - x 1⟫ = 0 → 0 < ⟪F.N t, x 0 - x 1⟫) := by
  have hcram := wc_cramer_signs F hC hb3
  have hwall := wc_wallI_pos_368 F hC hb3
  have hw35 : 1 < omega3 x * omega5 x :=
    omega_prod_gt_one hC.1 hC.2.2.1 hC.2.1 (by
      have := hC.2.2.2
      unfold Delta24 at this
      nlinarith [hC.1, hC.2.1, hC.2.2.1])
  have hw5_lt_w3 : 1 / omega5 x < omega3 x := by
    rw [div_lt_iff₀ hC.2.2.1]
    linarith
  -- Facet 8 gives `0 < ⟪F.N 8, x 6 - x 1⟫` and `-⟪F.N 8, x 0 - x 1⟫ / ⟪F.N 8, x 6 - x 1⟫ = wcR8 x`
  have h8c : 0 < ⟪F.N 8, x 6 - x 1⟫ := by
    rw [F.inner_sub, F.zero 8 6 (by decide), zero_sub]
    exact neg_pos.mpr (F.neg 8 1 (by decide))
  have h8_eq : -⟪F.N 8, x 0 - x 1⟫ / ⟪F.N 8, x 6 - x 1⟫ = wcR8 x := by
    have h83 := fac8_eq F 3 (by decide)
    have h84 := fac8_eq F 4 (by decide)
    have hkap8 : -F.f 8 (x 1) = ⟪F.N 8, x 6 - x 1⟫ := by
      rw [F.inner_sub, F.zero 8 6 (by decide)]; ring
    rw [hkap8] at h83 h84
    have hden : oblX0 x 4 * oblX2 x 3 - oblX0 x 3 * oblX2 x 4 ≠ 0 := by linarith [hcram.2]
    have hcr : (oblX0 x 4 * oblX2 x 3 - oblX0 x 3 * oblX2 x 4) * (-⟪F.N 8, x 0 - x 1⟫) =
        (oblX2 x 4 * (1 - oblX6 x 3) - oblX2 x 3 * (1 - oblX6 x 4)) * ⟪F.N 8, x 6 - x 1⟫ := by
      linear_combination oblX2 x 4 * h83 - oblX2 x 3 * h84
    dsimp [wcR8]
    rw [div_eq_div_iff h8c.ne' hden]
    linarith only [hcr]
  have hw8_pos : 0 < ⟪F.N 8, capView x 1 0 (omega3 x)⟫ := hwall 8 (by decide)
  have hr8_lt : wcR8 x < omega3 x := by
    rw [← h8_eq, div_lt_iff₀ h8c]
    dsimp [capView] at hw8_pos
    rw [one_smul, zero_smul, add_zero, inner_add_right, real_inner_smul_right] at hw8_pos
    linarith
  -- Facet 6: if `0 < ⟪F.N 6, x 6 - x 1⟫`, then `0 < denom6` and `-N6a / N6c = wcR6 x < omega3 x`
  have h6_pos_eq : 0 < ⟪F.N 6, x 6 - x 1⟫ →
      -⟪F.N 6, x 0 - x 1⟫ / ⟪F.N 6, x 6 - x 1⟫ = wcR6 x ∧ wcR6 x < omega3 x := by
    intro h6c
    have h63 := fac6_eq F 3 (by decide)
    have h65 := fac6_eq F 5 (by decide)
    have hkap6 : 0 < -F.f 6 (x 1) := neg_pos.mpr (F.neg 6 1 (by decide))
    have hden_eq : (oblX0 x 5 * (1 - oblX2 x 3) - oblX0 x 3 * (1 - oblX2 x 5)) * (-F.f 6 (x 1)) =
        -(oblX0 x 3 * oblX6 x 5 - oblX0 x 5 * oblX6 x 3) * ⟪F.N 6, x 6 - x 1⟫ := by
      linear_combination oblX0 x 3 * h65 - oblX0 x 5 * h63
    have hden_pos : 0 < oblX0 x 5 * (1 - oblX2 x 3) - oblX0 x 3 * (1 - oblX2 x 5) := by
      have hmul : 0 < (oblX0 x 5 * (1 - oblX2 x 3) - oblX0 x 3 * (1 - oblX2 x 5)) * (-F.f 6 (x 1)) := by
        rw [hden_eq]; exact mul_pos (neg_pos.mpr hcram.1) h6c
      exact pos_of_mul_pos_left hmul hkap6.le
    have hnum_eq : -(oblX0 x 3 * oblX6 x 5 - oblX0 x 5 * oblX6 x 3) * (-⟪F.N 6, x 0 - x 1⟫) =
        ((1 - oblX2 x 3) * oblX6 x 5 - (1 - oblX2 x 5) * oblX6 x 3) * (-F.f 6 (x 1)) := by
      linear_combination oblX6 x 5 * h63 - oblX6 x 3 * h65
    have heq : -⟪F.N 6, x 0 - x 1⟫ / ⟪F.N 6, x 6 - x 1⟫ = wcR6 x := by
      dsimp [wcR6]
      simp only [hden_pos, ↓reduceIte]
      have hcr1 : -(oblX0 x 3 * oblX6 x 5 - oblX0 x 5 * oblX6 x 3) ≠ 0 := by linarith [hcram.1]
      rw [div_eq_div_iff h6c.ne' hden_pos.ne']
      apply mul_left_cancel₀ hkap6.ne'
      linear_combination (-⟪F.N 6, x 0 - x 1⟫) * hden_eq + ⟪F.N 6, x 6 - x 1⟫ * hnum_eq
    have hw6_pos : 0 < ⟪F.N 6, capView x 1 0 (omega3 x)⟫ := hwall 6 (by decide)
    dsimp [capView] at hw6_pos
    rw [one_smul, zero_smul, add_zero, inner_add_right, real_inner_smul_right] at hw6_pos
    have hlt : wcR6 x < omega3 x := by
      rw [← heq, div_lt_iff₀ h6c]; linarith
    exact ⟨heq, hlt⟩
  have hr6_lt : wcR6 x < omega3 x := by
    by_cases h6c : 0 < ⟪F.N 6, x 6 - x 1⟫
    · exact (h6_pos_eq h6c).2
    · have hkap6 : 0 < -F.f 6 (x 1) := neg_pos.mpr (F.neg 6 1 (by decide))
      have h63 := fac6_eq F 3 (by decide)
      have h65 := fac6_eq F 5 (by decide)
      have hden_eq : (oblX0 x 5 * (1 - oblX2 x 3) - oblX0 x 3 * (1 - oblX2 x 5)) * (-F.f 6 (x 1)) =
          -(oblX0 x 3 * oblX6 x 5 - oblX0 x 5 * oblX6 x 3) * ⟪F.N 6, x 6 - x 1⟫ := by
        linear_combination oblX0 x 3 * h65 - oblX0 x 5 * h63
      have hden_le : oblX0 x 5 * (1 - oblX2 x 3) - oblX0 x 3 * (1 - oblX2 x 5) ≤ 0 := by
        have hle : (oblX0 x 5 * (1 - oblX2 x 3) - oblX0 x 3 * (1 - oblX2 x 5)) * (-F.f 6 (x 1)) ≤ 0 := by
          rw [hden_eq]
          exact mul_nonpos_of_nonneg_of_nonpos (neg_pos.mpr hcram.1).le (not_lt.mp h6c)
        exact nonpos_of_mul_nonpos_left hle hkap6
      dsimp [wcR6]
      simp only [not_lt.mpr hden_le, ↓reduceIte]
      exact hC.1
  have hlo_lt_hi : cLo x < omega3 x := by
    dsimp [cLo]
    exact max_lt hw5_lt_w3 (max_lt hr8_lt hr6_lt)
  refine ⟨hlo_lt_hi, fun cc hcc => ?_⟩
  have hcc_lo : cLo x < cc := hcc.1
  have hcc_hi : cc < omega3 x := hcc.2
  have hw5 : 1 / omega5 x < cc := lt_of_le_of_lt (le_max_left _ _) hcc_lo
  have hcc_pos : 0 < cc := lt_trans (one_div_pos.mpr hC.2.2.1) hw5
  have hr8_cc : wcR8 x < cc :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hcc_lo
  have hr6_cc : wcR6 x < cc :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hcc_lo
  have hcap_val : ∀ t : Fin 9, ⟪F.N t, capView x 1 0 (omega3 x)⟫ =
      ⟪F.N t, x 0 - x 1⟫ + omega3 x * ⟪F.N t, x 6 - x 1⟫ := by
    intro t
    dsimp [capView]
    rw [one_smul, zero_smul, add_zero, inner_add_right, real_inner_smul_right]
  refine ⟨hw5, hcc_hi, ?_, ?_, ?_⟩
  · intro t ht hpos
    simp only [mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · have h3a : 0 < ⟪F.N 3, x 0 - x 1⟫ := by
        rw [F.inner_sub, F.zero 3 0 (by decide), zero_sub]
        exact neg_pos.mpr (F.neg 3 1 (by decide))
      have hdiv : -⟪F.N 3, x 0 - x 1⟫ / ⟪F.N 3, x 6 - x 1⟫ < 0 :=
        div_neg_of_neg_of_pos (neg_neg_of_pos h3a) hpos
      linarith
    · rw [(h6_pos_eq hpos).1]; exact hr6_cc
    · rw [h8_eq]; exact hr8_cc
  · intro t ht hneg
    have hpos_w3 := hwall t ht
    rw [hcap_val t] at hpos_w3
    rw [lt_div_iff_of_neg hneg]
    nlinarith
  · intro t ht hzero
    have hpos_w3 := hwall t ht
    rw [hcap_val t, hzero, mul_zero, add_zero] at hpos_w3
    exact hpos_w3

/-! ## FO3: Carbon A83 Lemma L3 -/

/-- **FO3 (Unconditional apex gap `yHat_{2,2} < yHat_{1,2}`):** under `CbarIn x`, `OB1 x`,
`oblX2 x 3 < 1`, `oblX2 x 5 < 1`, and `cc ∈ Set.Ioo (cLo x) (omega3 x)`, `wcYHat x 2 2 cc < wcYHat x 1 2 cc`. -/
theorem wc_apex_gap {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hOB1 : OB1 x)
    (hb3 : oblX2 x 3 < 1) (hb5 : oblX2 x 5 < 1) {cc : ℝ} (hcc : cc ∈ Set.Ioo (cLo x) (omega3 x)) :
    wcYHat x 2 2 cc < wcYHat x 1 2 cc := by
  have T := M4.type24OfFac F
  have hdet : det24 x ≠ 0 := T.det_ne
  have hb3_pos : 0 < oblX2 x 3 := T.X2_pos (v := 3) (by decide)
  have hb5_pos : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have h1b3 : 0 < 1 - oblX2 x 3 := sub_pos.mpr hb3
  have h1b5 : 0 < 1 - oblX2 x 5 := sub_pos.mpr hb5
  have hcram := wc_cramer_signs F hC hb3
  have hwin := (wc_window_nonempty F hC hb3).2 cc hcc
  -- `0 < ⟪F.N 6, capView x 1 0 cc⟫`
  have hN6_pos : 0 < ⟪F.N 6, capView x 1 0 cc⟫ := by
    dsimp [capView]
    rw [one_smul, zero_smul, add_zero, inner_add_right, real_inner_smul_right]
    rcases lt_trichotomy ⟪F.N 6, x 6 - x 1⟫ 0 with hn | hz | hp
    · have := hwin.2.2.2.1 6 (by decide) hn
      rw [lt_div_iff_of_neg hn] at this; linarith
    · have := hwin.2.2.2.2 6 (by decide) hz
      rw [hz, mul_zero, add_zero]; exact this
    · have := hwin.2.2.1 6 (by decide) hp
      rw [div_lt_iff₀ hp] at this; linarith
  -- Gram entries at vertex `1`
  let ea := x 0 - x 1
  let eb := x 2 - x 1
  let ec := x 6 - x 1
  let ga := ⟪ea, ea⟫
  let gc := ⟪ec, ec⟫
  let Gab := ⟪ea, eb⟫
  let Gac := ⟪ea, ec⟫
  let Gbc := ⟪eb, ec⟫
  have hea0 : ea ≠ 0 := by
    intro h0; apply hdet
    simp only [det24, vol3, ea, h0, PiLp.zero_apply]; ring
  have hec0 : ec ≠ 0 := by
    intro h0; apply hdet
    simp only [det24, vol3, ec, h0, PiLp.zero_apply]; ring
  have hga : 0 < ga := real_inner_self_pos.mpr hea0
  have hgc : 0 < gc := real_inner_self_pos.mpr hec0
  have hcs : 0 < ga * gc - Gac ^ 2 := by
    by_contra hle; push Not at hle
    have hnorm : ⟪gc • ea - Gac • ec, gc • ea - Gac • ec⟫ ≤ 0 := by
      have hcomm : ⟪ec, ea⟫ = ⟪ea, ec⟫ := real_inner_comm _ _
      have hid : ⟪gc • ea - Gac • ec, gc • ea - Gac • ec⟫ = gc * (ga * gc - Gac ^ 2) := by
        simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
        rw [hcomm]
        dsimp only [ga, gc, Gac]; ring
      rw [hid]
      exact mul_nonpos_of_nonneg_of_nonpos hgc.le hle
    have hvec : gc • ea - Gac • ec = 0 :=
      inner_self_eq_zero.mp (le_antisymm hnorm (real_inner_self_nonneg (x := gc • ea - Gac • ec)))
    have heq : gc • ea = Gac • ec := sub_eq_zero.mp hvec
    have hvol : vol3 (gc • ea) eb ec = 0 := by
      rw [heq]
      simp only [vol3, PiLp.smul_apply, smul_eq_mul]; ring
    have hvol2 : vol3 (gc • ea) eb ec = gc * det24 x := by
      simp only [det24, vol3, ea, eb, ec, PiLp.smul_apply, smul_eq_mul]; ring
    rw [hvol] at hvol2
    rcases mul_eq_zero.mp hvol2.symm with h | h
    · linarith
    · exact hdet h
  let Q_apex : ℝ := (ga * gc - Gac ^ 2) - ga * Gbc - gc * Gab + Gab * Gac + Gac * Gbc
  have hQ_pos : 0 < Q_apex := by
    have h1 : Gab ≤ 0 := hOB1.1
    have h2 : Gac ≤ 0 := hOB1.2.1
    have h3 : Gbc ≤ 0 := hOB1.2.2
    dsimp only [Q_apex]
    nlinarith
  -- Compute `(A235 * cc - C235) < 0` from `wc_cramer_signs` and `0 < ⟪F.N 6, w0⟫`
  let A235 : ℝ := oblX0 x 3 * (1 - oblX2 x 5) - oblX0 x 5 * (1 - oblX2 x 3)
  let C235 : ℝ := oblX6 x 3 * (1 - oblX2 x 5) - oblX6 x 5 * (1 - oblX2 x 3)
  have hkap6 : 0 < -F.f 6 (x 1) := neg_pos.mpr (F.neg 6 1 (by decide))
  have hAC_sign : A235 * cc - C235 < 0 := by
    have h63 := fac6_eq F 3 (by decide)
    have h65 := fac6_eq F 5 (by decide)
    have hN6w : ⟪F.N 6, capView x 1 0 cc⟫ = ⟪F.N 6, ea⟫ + cc * ⟪F.N 6, ec⟫ := by
      dsimp [capView, ea, ec]
      rw [one_smul, zero_smul, add_zero, inner_add_right, real_inner_smul_right]
    have hid : (A235 * cc - C235) * (-F.f 6 (x 1)) =
        (oblX0 x 3 * oblX6 x 5 - oblX0 x 5 * oblX6 x 3) * ⟪F.N 6, capView x 1 0 cc⟫ := by
      rw [hN6w]
      dsimp only [A235, C235, ea, ec]
      linear_combination -(cc * oblX0 x 3 - oblX6 x 3) * h65 + (cc * oblX0 x 5 - oblX6 x 5) * h63
    have hrhs : (oblX0 x 3 * oblX6 x 5 - oblX0 x 5 * oblX6 x 3) * ⟪F.N 6, capView x 1 0 cc⟫ < 0 :=
      mul_neg_of_neg_of_pos hcram.1 hN6_pos
    rw [← hid] at hrhs
    exact neg_of_mul_neg_left hrhs hkap6.le
  -- Algebraic identity for `wcYHat x 1 2 cc - wcYHat x 2 2 cc`
  have hx5 : x 5 - x 1 = oblX0 x 5 • ea + oblX2 x 5 • eb + oblX6 x 5 • ec := by
    rw [T.rep 5]; dsimp only [ea, eb, ec]; abel
  have hx3 : x 3 - x 1 = oblX0 x 3 • ea + oblX2 x 3 • eb + oblX6 x 3 • ec := by
    rw [T.rep 3]; dsimp only [ea, eb, ec]; abel
  have hdelta1 : wcDelta x 1 = -(1 - oblX2 x 5) := by simp [wcDelta]
  have hdelta2 : wcDelta x 2 = 1 - oblX2 x 3 := by simp [wcDelta]
  have hdiff_id : wcYHat x 1 2 cc - wcYHat x 2 2 cc =
      -((A235 * cc - C235) * Q_apex) / ((1 - oblX2 x 3) * (1 - oblX2 x 5)) := by
    have hnum : (1 - oblX2 x 3) *
        ⟪Split.Slope.linSpinVec (fun t => x (wcRim t)) 4 1 2, capView x 1 0 cc⟫ +
        (1 - oblX2 x 5) *
        ⟪Split.Slope.linSpinVec (fun t => x (wcRim t)) 4 2 2, capView x 1 0 cc⟫ =
        (A235 * cc - C235) * Q_apex := by
      dsimp only [Split.Slope.linSpinVec, capView]
      have hw : (1 : ℝ) • (x 0 - x 1) + (0 : ℝ) • (x 2 - x 1) + cc • (x 6 - x 1) =
          ea + cc • ec := by dsimp only [ea, ec]; module
      rw [hw]
      have hE1 : x 2 - x 5 = (eb - ec) - (x 5 - x 1 - ec) := by dsimp only [eb, ec]; abel
      have hE2 : x 3 - x 2 = (x 3 - x 1 - eb) := by dsimp only [eb]; abel
      have h26 : x 2 - x 6 = eb - ec := by dsimp only [eb, ec]; abel
      have h06 : x 0 - x 6 = ea - ec := by dsimp only [ea, ec]; abel
      have hrim1 : (1 : ZMod 5) + 1 = 2 := by decide
      have hrim2 : (2 : ZMod 5) + 1 = 3 := by decide
      have hrim4 : (4 : ZMod 5) + 1 = 0 := by decide
      rw [hrim1, hrim2, hrim4]
      dsimp [wcRim]
      rw [hE1, hE2, h26, h06, hx5, hx3]
      have hc1 : ⟪eb, ea⟫ = ⟪ea, eb⟫ := real_inner_comm _ _
      have hc2 : ⟪ec, ea⟫ = ⟪ea, ec⟫ := real_inner_comm _ _
      have hc3 : ⟪ec, eb⟫ = ⟪eb, ec⟫ := real_inner_comm _ _
      simp only [inner_sub_left, inner_add_left, inner_sub_right, inner_add_right,
        real_inner_smul_left, real_inner_smul_right, hc1, hc2, hc3]
      dsimp only [A235, C235, Q_apex, ga, gc, Gab, Gac, Gbc]
      ring
    dsimp [wcYHat]
    rw [hdelta1, hdelta2]
    field_simp [h1b3.ne', h1b5.ne']
    linarith [hnum]
  have hpos : 0 < wcYHat x 1 2 cc - wcYHat x 2 2 cc := by
    rw [hdiff_id]
    exact div_pos (neg_pos.mpr (mul_neg_of_neg_of_pos hAC_sign hQ_pos)) (mul_pos h1b3 h1b5)
  linarith

/-! ## FO2: Carbon A83 Lemma L2 -/

/-- **FO2 (`sh = -1` reduction of `WCCertAt`):** under `CbarIn x`, `oblX2 x 3 < 1`, `oblX2 x 5 < 1`,
`cc ∈ Set.Ioo (cLo x) (omega3 x)`, and `⟪x 0 - x 6, capView x 1 0 cc⟫ ≠ 0`, scale-free
separation of `wcYHat x i j cc` (`i ∈ {2, 3}`) from `wcYHat x p q cc` (`p ∈ {0, 1}`) yields
`WCCertAt x F cc` for both signs of `det24 x`. -/
theorem wcCertAt_of_yHat {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (hb3 : oblX2 x 3 < 1) (hb5 : oblX2 x 5 < 1) {cc : ℝ} (hcc : cc ∈ Set.Ioo (cLo x) (omega3 x))
    (hr60 : ⟪x 0 - x 6, capView x 1 0 cc⟫ ≠ 0) (αHat μHat : ℝ)
    (hB : ∀ i ∈ ({2, 3} : Finset (ZMod 5)), ∀ j : ZMod 5, (j = i ∨ j = i + 1) →
      wcYHat x i j cc - μHat * wcZ x j cc < αHat)
    (hO : ∀ p ∈ ({0, 1} : Finset (ZMod 5)), ∀ q : ZMod 5, (q = p ∨ q = p + 1) →
      αHat < wcYHat x p q cc - μHat * wcZ x q cc) :
    WCCertAt x F cc := by
  have T := M4.type24OfFac F
  have hdet : det24 x ≠ 0 := T.det_ne
  have hb3_pos : 0 < oblX2 x 3 := T.X2_pos (v := 3) (by decide)
  have hb5_pos : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have h1b3 : 0 < 1 - oblX2 x 3 := sub_pos.mpr hb3
  have h1b5 : 0 < 1 - oblX2 x 5 := sub_pos.mpr hb5
  have hwin := (wc_window_nonempty F hC hb3).2 cc hcc
  have hcc_pos : 0 < cc := lt_trans (one_div_pos.mpr hC.2.2.1) hwin.1
  have h1cc_pos : 0 < 1 + cc := by linarith
  let K : ℝ := (1 + cc) * det24 x
  have hK_ne : K ≠ 0 := mul_ne_zero h1cc_pos.ne' hdet
  have hrim := wc_det3_rim x hdet cc
  have hdet_eq : ∀ i : ZMod 5, i ≠ 4 →
      Split.det3 (x (wcRim (i + 1)) - x (wcRim i))
        (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 0 cc) = K * wcDelta x i := by
    intro i hi
    fin_cases i
    · exact hrim.1
    · exact hrim.2.1
    · exact hrim.2.2.1
    · exact hrim.2.2.2
    · exact absurd rfl hi
  have hdelta_ne : ∀ i : ZMod 5, i ≠ 4 → wcDelta x i ≠ 0 := by
    intro i hi; fin_cases i
    · simp [wcDelta]; linarith
    · simp [wcDelta]; linarith
    · simp [wcDelta]; linarith
    · simp [wcDelta]; linarith
    · exact absurd rfl hi
  have hD0 : ⟪x (wcRim (4 + 1)) - x (wcRim 4), capView x 1 0 cc⟫ ≠ 0 := hr60
  have hc_ne0 : ∀ i : ZMod 5, i ≠ 4 →
      Split.det3 (x (wcRim (i + 1)) - x (wcRim i))
        (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 0 cc) ≠ 0 := by
    intro i hi
    rw [hdet_eq i hi]
    exact mul_ne_zero hK_ne (hdelta_ne i hi)
  have hcases5 : ∀ k : ZMod 5, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := fun k => by
    fin_cases k <;> dsimp <;> first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr (Or.inl rfl))
      | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      | exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  refine ⟨hwin.1, hwin.2.1, hwin.2.2.1, hwin.2.2.2.1, hwin.2.2.2.2, hD0, hc_ne0,
    -1, αHat / K, μHat / K, Or.inr rfl, ?_, ?_⟩
  · intro i j hi hj hc_pos
    rw [hdet_eq i hi] at hc_pos ⊢
    have hval : -(-1 : ℝ) * ⟪Split.Slope.linSpinVec (fun t => x (wcRim t)) 4 i j,
          capView x 1 0 cc⟫ / (K * wcDelta x i) -
        (μHat / K) * ⟪x (wcRim j) - x (wcRim 4), capView x 1 0 cc⟫ =
        (wcYHat x i j cc - μHat * wcZ x j cc) / K := by
      have hrim4 : wcRim 4 = 6 := rfl
      dsimp [wcYHat, wcZ]
      rw [hrim4]
      field_simp [hK_ne, hdelta_ne i hi]
    rw [hval]
    rcases lt_or_gt_of_ne hdet with hdet_neg | hdet_pos
    · have hK_neg : K < 0 := mul_neg_of_pos_of_neg h1cc_pos hdet_neg
      have hdel_neg : wcDelta x i < 0 := neg_of_mul_pos_right hc_pos hK_neg.le
      have hi01 : i ∈ ({0, 1} : Finset (ZMod 5)) := by
        rcases hcases5 i with rfl | rfl | rfl | rfl | rfl <;> simp [wcDelta] at hdel_neg <;>
          first | decide | linarith
      simp only [div_eq_mul_inv]
      exact mul_lt_mul_of_neg_right (hO i hi01 j hj) (inv_lt_zero.mpr hK_neg)
    · have hK_pos : 0 < K := mul_pos h1cc_pos hdet_pos
      have hdel_pos : 0 < wcDelta x i := pos_of_mul_pos_right hc_pos hK_pos.le
      have hi23 : i ∈ ({2, 3} : Finset (ZMod 5)) := by
        rcases hcases5 i with rfl | rfl | rfl | rfl | rfl <;> simp [wcDelta] at hdel_pos <;>
          first | decide | linarith
      exact div_lt_div_of_pos_right (hB i hi23 j hj) hK_pos
  · intro p q hp hq hc_neg
    rw [hdet_eq p hp] at hc_neg ⊢
    have hval : -(-1 : ℝ) * ⟪Split.Slope.linSpinVec (fun t => x (wcRim t)) 4 p q,
          capView x 1 0 cc⟫ / (K * wcDelta x p) -
        (μHat / K) * ⟪x (wcRim q) - x (wcRim 4), capView x 1 0 cc⟫ =
        (wcYHat x p q cc - μHat * wcZ x q cc) / K := by
      have hrim4 : wcRim 4 = 6 := rfl
      dsimp [wcYHat, wcZ]
      rw [hrim4]
      field_simp [hK_ne, hdelta_ne p hp]
    rw [hval]
    rcases lt_or_gt_of_ne hdet with hdet_neg | hdet_pos
    · have hK_neg : K < 0 := mul_neg_of_pos_of_neg h1cc_pos hdet_neg
      have hdel_pos : 0 < wcDelta x p := pos_of_mul_neg_right hc_neg hK_neg.le
      have hp23 : p ∈ ({2, 3} : Finset (ZMod 5)) := by
        rcases hcases5 p with rfl | rfl | rfl | rfl | rfl <;> simp [wcDelta] at hdel_pos <;>
          first | decide | linarith
      simp only [div_eq_mul_inv]
      exact mul_lt_mul_of_neg_right (hB p hp23 q hq) (inv_lt_zero.mpr hK_neg)
    · have hK_pos : 0 < K := mul_pos h1cc_pos hdet_pos
      have hdel_neg : wcDelta x p < 0 := neg_of_mul_neg_right hc_neg hK_pos.le
      have hp01 : p ∈ ({0, 1} : Finset (ZMod 5)) := by
        rcases hcases5 p with rfl | rfl | rfl | rfl | rfl <;> simp [wcDelta] at hdel_neg <;>
          first | decide | linarith
      exact div_lt_div_of_pos_right (hO p hp01 q hq) hK_pos

/-! ## FO4: Carbon A83 Lemma L5 (`RobUni` exclusion at `r60`) -/

private theorem robUni_2104 {z : ZMod 5 → ℝ}
    (h21 : z 2 < z 1) (h10 : z 1 < z 0) (h04 : z 0 < z 4) (h23 : z 2 < z 3) :
    H21.RobUni z := by
  have hdec : ∀ (r : Fin 8) (B b c d : Fin 5),
      1 ≤ r.val → 0 < b.val → b.val < c.val → c.val < d.val →
      let ord : Fin 5 → ℕ := ![4, 2, 0, r.val, 6]
      ¬ (ord (B + b) ≤ ord B ∧ ord (B + b) ≤ ord (B + c) ∧
         ord (B + d) ≤ ord B ∧ ord (B + d) ≤ ord (B + c)) := by
    decide
  have hcases : ∀ k : ZMod 5, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := fun k => by
    fin_cases k <;> dsimp <;> first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr (Or.inl rfl))
      | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      | exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  have hr : ∃ r : Fin 8, 1 ≤ r.val ∧ ∀ i j : ZMod 5, z i ≤ z j →
      (![4, 2, 0, r.val, 6] : Fin 5 → ℕ) i ≤ (![4, 2, 0, r.val, 6] : Fin 5 → ℕ) j := by
    rcases lt_trichotomy (z 3) (z 1) with h31 | h31 | h31
    · refine ⟨1, by decide, fun i j hij => ?_⟩
      rcases hcases i with rfl | rfl | rfl | rfl | rfl <;> rcases hcases j with rfl | rfl | rfl | rfl | rfl <;> dsimp <;> first | omega | linarith only [hij, h21, h10, h04, h23, h31]
    · refine ⟨2, by decide, fun i j hij => ?_⟩
      rcases hcases i with rfl | rfl | rfl | rfl | rfl <;> rcases hcases j with rfl | rfl | rfl | rfl | rfl <;> dsimp <;> first | omega | linarith only [hij, h21, h10, h04, h23, h31]
    · rcases lt_trichotomy (z 3) (z 0) with h30 | h30 | h30
      · refine ⟨3, by decide, fun i j hij => ?_⟩
        rcases hcases i with rfl | rfl | rfl | rfl | rfl <;> rcases hcases j with rfl | rfl | rfl | rfl | rfl <;> dsimp <;> first | omega | linarith only [hij, h21, h10, h04, h23, h31, h30]
      · refine ⟨4, by decide, fun i j hij => ?_⟩
        rcases hcases i with rfl | rfl | rfl | rfl | rfl <;> rcases hcases j with rfl | rfl | rfl | rfl | rfl <;> dsimp <;> first | omega | linarith only [hij, h21, h10, h04, h23, h31, h30]
      · rcases lt_trichotomy (z 3) (z 4) with h34 | h34 | h34
        · refine ⟨5, by decide, fun i j hij => ?_⟩
          rcases hcases i with rfl | rfl | rfl | rfl | rfl <;> rcases hcases j with rfl | rfl | rfl | rfl | rfl <;> dsimp <;> first | omega | linarith only [hij, h21, h10, h04, h23, h31, h30, h34]
        · refine ⟨6, by decide, fun i j hij => ?_⟩
          rcases hcases i with rfl | rfl | rfl | rfl | rfl <;> rcases hcases j with rfl | rfl | rfl | rfl | rfl <;> dsimp <;> first | omega | linarith only [hij, h21, h10, h04, h23, h31, h30, h34]
        · refine ⟨7, by decide, fun i j hij => ?_⟩
          rcases hcases i with rfl | rfl | rfl | rfl | rfl <;> rcases hcases j with rfl | rfl | rfl | rfl | rfl <;> dsimp <;> first | omega | linarith only [hij, h21, h10, h04, h23, h31, h30, h34]
  rcases hr with ⟨r, hr1, hmono⟩
  intro B b c d hb hbc hcd hdk ⟨h1, h2, h3, h4⟩
  have hb5 : b < 5 := by omega
  have hc5 : c < 5 := by omega
  have hb_eq : (b : ZMod 5) = ⟨b, hb5⟩ := Fin.ext (Nat.mod_eq_of_lt hb5)
  have hc_eq : (c : ZMod 5) = ⟨c, hc5⟩ := Fin.ext (Nat.mod_eq_of_lt hc5)
  have hd_eq : (d : ZMod 5) = ⟨d, hdk⟩ := Fin.ext (Nat.mod_eq_of_lt hdk)
  refine hdec r B ⟨b, hb5⟩ ⟨c, hc5⟩ ⟨d, hdk⟩ hr1 hb hbc hcd ⟨?_, ?_, ?_, ?_⟩
  · rw [← hb_eq]; exact hmono _ _ h1
  · rw [← hb_eq, ← hc_eq]; exact hmono _ _ h2
  · rw [← hd_eq]; exact hmono _ _ h3
  · rw [← hd_eq, ← hc_eq]; exact hmono _ _ h4

private theorem robUni_2340 {z : ZMod 5 → ℝ}
    (h23 : z 2 < z 3) (h34 : z 3 < z 4) (h40 : z 4 < z 0) (h21 : z 2 < z 1) :
    H21.RobUni z := by
  have hdec : ∀ (r : Fin 8) (B b c d : Fin 5),
      1 ≤ r.val → 0 < b.val → b.val < c.val → c.val < d.val →
      let ord : Fin 5 → ℕ := ![6, r.val, 0, 2, 4]
      ¬ (ord (B + b) ≤ ord B ∧ ord (B + b) ≤ ord (B + c) ∧
         ord (B + d) ≤ ord B ∧ ord (B + d) ≤ ord (B + c)) := by
    decide
  have hcases : ∀ k : ZMod 5, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := fun k => by
    fin_cases k <;> dsimp <;> first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr (Or.inl rfl))
      | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      | exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  have hr : ∃ r : Fin 8, 1 ≤ r.val ∧ ∀ i j : ZMod 5, z i ≤ z j →
      (![6, r.val, 0, 2, 4] : Fin 5 → ℕ) i ≤ (![6, r.val, 0, 2, 4] : Fin 5 → ℕ) j := by
    rcases lt_trichotomy (z 1) (z 3) with h13 | h13 | h13
    · refine ⟨1, by decide, fun i j hij => ?_⟩
      rcases hcases i with rfl | rfl | rfl | rfl | rfl <;> rcases hcases j with rfl | rfl | rfl | rfl | rfl <;> dsimp <;> first | omega | linarith only [hij, h23, h34, h40, h21, h13]
    · refine ⟨2, by decide, fun i j hij => ?_⟩
      rcases hcases i with rfl | rfl | rfl | rfl | rfl <;> rcases hcases j with rfl | rfl | rfl | rfl | rfl <;> dsimp <;> first | omega | linarith only [hij, h23, h34, h40, h21, h13]
    · rcases lt_trichotomy (z 1) (z 4) with h14 | h14 | h14
      · refine ⟨3, by decide, fun i j hij => ?_⟩
        rcases hcases i with rfl | rfl | rfl | rfl | rfl <;> rcases hcases j with rfl | rfl | rfl | rfl | rfl <;> dsimp <;> first | omega | linarith only [hij, h23, h34, h40, h21, h13, h14]
      · refine ⟨4, by decide, fun i j hij => ?_⟩
        rcases hcases i with rfl | rfl | rfl | rfl | rfl <;> rcases hcases j with rfl | rfl | rfl | rfl | rfl <;> dsimp <;> first | omega | linarith only [hij, h23, h34, h40, h21, h13, h14]
      · rcases lt_trichotomy (z 1) (z 0) with h10 | h10 | h10
        · refine ⟨5, by decide, fun i j hij => ?_⟩
          rcases hcases i with rfl | rfl | rfl | rfl | rfl <;> rcases hcases j with rfl | rfl | rfl | rfl | rfl <;> dsimp <;> first | omega | linarith only [hij, h23, h34, h40, h21, h13, h14, h10]
        · refine ⟨6, by decide, fun i j hij => ?_⟩
          rcases hcases i with rfl | rfl | rfl | rfl | rfl <;> rcases hcases j with rfl | rfl | rfl | rfl | rfl <;> dsimp <;> first | omega | linarith only [hij, h23, h34, h40, h21, h13, h14, h10]
        · refine ⟨7, by decide, fun i j hij => ?_⟩
          rcases hcases i with rfl | rfl | rfl | rfl | rfl <;> rcases hcases j with rfl | rfl | rfl | rfl | rfl <;> dsimp <;> first | omega | linarith only [hij, h23, h34, h40, h21, h13, h14, h10]
  rcases hr with ⟨r, hr1, hmono⟩
  intro B b c d hb hbc hcd hdk ⟨h1, h2, h3, h4⟩
  have hb5 : b < 5 := by omega
  have hc5 : c < 5 := by omega
  have hb_eq : (b : ZMod 5) = ⟨b, hb5⟩ := Fin.ext (Nat.mod_eq_of_lt hb5)
  have hc_eq : (c : ZMod 5) = ⟨c, hc5⟩ := Fin.ext (Nat.mod_eq_of_lt hc5)
  have hd_eq : (d : ZMod 5) = ⟨d, hdk⟩ := Fin.ext (Nat.mod_eq_of_lt hdk)
  refine hdec r B ⟨b, hb5⟩ ⟨c, hc5⟩ ⟨d, hdk⟩ hr1 hb hbc hcd ⟨?_, ?_, ?_, ?_⟩
  · rw [← hb_eq]; exact hmono _ _ h1
  · rw [← hb_eq, ← hc_eq]; exact hmono _ _ h2
  · rw [← hd_eq]; exact hmono _ _ h3
  · rw [← hd_eq, ← hc_eq]; exact hmono _ _ h4

private theorem wc_contra_of_rob {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F)
    (hb3 : oblX2 x 3 ≤ 1) (hb5 : oblX2 x 5 ≤ 1)
    {cc : ℝ} (hcc : cc ∈ Set.Ioo (cLo x) (omega3 x))
    (hrob : H21.RobUni (fun i => ⟪x (wcRim i), capView x 1 0 cc⟫)) : False := by
  have hC : CbarIn x := hF.1
  have T := M4.type24OfFac F
  have hcell : ∀ᶠ η : ℝ in 𝓝[>] 0,
      CellAt F ({3, 4, 6, 8} : Finset (Fin 9)) ({0, 1, 2, 5, 7} : Finset (Fin 9))
        (capView x 1 η cc) := by
    rcases lt_or_eq_of_le hb3 with hb3_s | hb3_eq
    · have hwin := (wc_window_nonempty F hC hb3_s).2 cc hcc
      exact wcCell_eventually F hC cc hwin.1 hwin.2.1 hwin.2.2.1 hwin.2.2.2.1 hwin.2.2.2.2
    · have hw5 : 1 / omega5 x < cc := lt_of_le_of_lt (le_max_left _ _) hcc.1
      have hcc_pos : 0 < cc := lt_trans (one_div_pos.mpr hC.2.2.1) hw5
      have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
      have hid_w3 : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
          oblX0 x 3 * ⟪F.N t, capView x 1 0 (omega3 x)⟫ =
            (oblX2 x 3 - 1) * F.f t (x 6) - oblX2 x 3 * F.f t (x 2) := by
        intro t ht
        have ht3 : 3 ∈ s0x_S24 t := by
          simp only [mem_insert, mem_singleton] at ht
          rcases ht with rfl | rfl | rfl <;> decide
        have ev := M4.fac_eval F t 3
        rw [F.zero t 3 ht3] at ev
        have e3 := M4.eq3 F
        dsimp [capView]
        simp only [inner_add_right, real_inner_smul_right, F.inner_sub]
        linear_combination -ev + (F.f t (x 1) - F.f t (x 6)) * e3
      have hw3_val : 0 < ⟪F.N 3, capView x 1 0 (omega3 x)⟫ := by
        have := hid_w3 3 (by decide)
        rw [hb3_eq, sub_self, zero_mul, zero_sub, one_mul] at this
        have hneg : 0 < -F.f 3 (x 2) := neg_pos.mpr (F.neg 3 2 (by decide))
        rw [← this] at hneg; exact pos_of_mul_pos_right hneg ha3.le
      have hw8_val : 0 < ⟪F.N 8, capView x 1 0 (omega3 x)⟫ := by
        have := hid_w3 8 (by decide)
        rw [hb3_eq, sub_self, zero_mul, zero_sub, one_mul] at this
        have hneg : 0 < -F.f 8 (x 2) := neg_pos.mpr (F.neg 8 2 (by decide))
        rw [← this] at hneg; exact pos_of_mul_pos_right hneg ha3.le
      have hw6_val : ⟪F.N 6, capView x 1 0 (omega3 x)⟫ = 0 := by
        have := hid_w3 6 (by decide)
        rw [hb3_eq, sub_self, zero_mul, F.zero 6 2 (by decide), mul_zero, sub_zero] at this
        exact (mul_eq_zero.mp this).resolve_left ha3.ne'
      have hcap : ∀ t : Fin 9, ∀ r : ℝ,
          ⟪F.N t, capView x 1 0 r⟫ = ⟪F.N t, x 0 - x 1⟫ + r * ⟪F.N t, x 6 - x 1⟫ := fun t r => by
        dsimp [capView]
        rw [one_smul, zero_smul, add_zero, inner_add_right, real_inner_smul_right]
      have h3_pos : 0 < ⟪F.N 3, x 0 - x 1⟫ + cc * ⟪F.N 3, x 6 - x 1⟫ := by
        rw [hcap 3 (omega3 x)] at hw3_val
        have h3a : 0 < ⟪F.N 3, x 0 - x 1⟫ := by
          rw [F.inner_sub, F.zero 3 0 (by decide), zero_sub]
          exact neg_pos.mpr (F.neg 3 1 (by decide))
        rcases le_or_gt ⟪F.N 3, x 6 - x 1⟫ 0 with hn | hp
        · nlinarith only [hw3_val, hn, hcc.2]
        · nlinarith only [h3a, hp, hcc_pos]
      have h8_pos : 0 < ⟪F.N 8, x 0 - x 1⟫ + cc * ⟪F.N 8, x 6 - x 1⟫ := by
        have h8c : 0 < ⟪F.N 8, x 6 - x 1⟫ := by
          rw [F.inner_sub, F.zero 8 6 (by decide), zero_sub]
          exact neg_pos.mpr (F.neg 8 1 (by decide))
        have h83 := fac8_eq F 3 (by decide)
        have h84 := fac8_eq F 4 (by decide)
        have hkap8 : -F.f 8 (x 1) = ⟪F.N 8, x 6 - x 1⟫ := by
          rw [F.inner_sub, F.zero 8 6 (by decide)]; ring
        rw [hkap8] at h83 h84
        have hcram := wc_cramer_signs_raw F
        have hden : oblX0 x 4 * oblX2 x 3 - oblX0 x 3 * oblX2 x 4 ≠ 0 := by linarith only [hcram.2]
        have hcr : (oblX0 x 4 * oblX2 x 3 - oblX0 x 3 * oblX2 x 4) * (-⟪F.N 8, x 0 - x 1⟫) =
            (oblX2 x 4 * (1 - oblX6 x 3) - oblX2 x 3 * (1 - oblX6 x 4)) * ⟪F.N 8, x 6 - x 1⟫ := by
          linear_combination oblX2 x 4 * h83 - oblX2 x 3 * h84
        have h8_eq : -⟪F.N 8, x 0 - x 1⟫ / ⟪F.N 8, x 6 - x 1⟫ = wcR8 x := by
          dsimp [wcR8]
          rw [div_eq_div_iff h8c.ne' hden]
          linarith only [hcr]
        have hr8 : wcR8 x < cc :=
          lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hcc.1
        rw [← h8_eq, div_lt_iff₀ h8c] at hr8; linarith only [hr8]
      have h6_nonneg : 0 ≤ ⟪F.N 6, x 0 - x 1⟫ + cc * ⟪F.N 6, x 6 - x 1⟫ := by
        rw [hcap 6 (omega3 x)] at hw6_val
        have h63 := fac6_eq F 3 (by decide)
        have h65 := fac6_eq F 5 (by decide)
        have hkap6 : 0 < -F.f 6 (x 1) := neg_pos.mpr (F.neg 6 1 (by decide))
        have hcram := wc_cramer_signs_raw F
        have hden_eq : (oblX0 x 5 * (1 - oblX2 x 3) - oblX0 x 3 * (1 - oblX2 x 5)) * (-F.f 6 (x 1)) =
            -(oblX0 x 3 * oblX6 x 5 - oblX0 x 5 * oblX6 x 3) * ⟪F.N 6, x 6 - x 1⟫ := by
          linear_combination oblX0 x 3 * h65 - oblX0 x 5 * h63
        have h6c_le : ⟪F.N 6, x 6 - x 1⟫ ≤ 0 := by
          have h1 : (oblX0 x 5 * (1 - oblX2 x 3) - oblX0 x 3 * (1 - oblX2 x 5)) * (-F.f 6 (x 1)) ≤ 0 := by
            rw [hb3_eq, sub_self, mul_zero, zero_sub]
            exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg (T.X0_pos (v := 3) (by decide)).le (sub_nonneg.mpr hb5))) hkap6.le
          rw [hden_eq] at h1
          exact nonpos_of_mul_nonpos_right h1 (neg_pos.mpr hcram.1)
        nlinarith only [hw6_val, h6c_le, hcc.2]
      have h6b : 0 < ⟪F.N 6, x 2 - x 1⟫ := by
        rw [F.inner_sub, F.zero 6 2 (by decide), zero_sub]
        exact neg_pos.mpr (F.neg 6 1 (by decide))
      have h6_ev : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < ⟪F.N 6, capView x 1 η cc⟫ := by
        filter_upwards [self_mem_nhdsWithin] with η (hη : 0 < η)
        dsimp [capView]
        rw [one_smul, inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right]
        nlinarith only [h6_nonneg, h6b, hη]
      have e3 : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < ⟪F.N 3, capView x 1 η cc⟫ := by
        have hcont : Continuous (fun η : ℝ => ⟪F.N 3, capView x 1 η cc⟫) := by unfold capView; fun_prop
        exact SF.ev_pos hcont (by dsimp [capView]; rw [one_smul, zero_smul, add_zero, inner_add_right, real_inner_smul_right]; exact h3_pos)
      have e8 : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < ⟪F.N 8, capView x 1 η cc⟫ := by
        have hcont : Continuous (fun η : ℝ => ⟪F.N 8, capView x 1 η cc⟫) := by unfold capView; fun_prop
        exact SF.ev_pos hcont (by dsimp [capView]; rw [one_smul, zero_smul, add_zero, inner_add_right, real_inner_smul_right]; exact h8_pos)
      have e4 : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < ⟪F.N 4, capView x 1 η cc⟫ := by
        have hcont : Continuous (fun η : ℝ => ⟪F.N 4, capView x 1 η cc⟫) := by unfold capView; fun_prop
        refine SF.ev_pos hcont ?_
        dsimp [capView]; rw [one_smul, zero_smul, add_zero, inner_add_right, real_inner_smul_right,
          F.inner_sub, F.inner_sub, F.zero 4 0 (by decide), F.zero 4 6 (by decide)]
        have : 0 < -F.f 4 (x 1) := neg_pos.mpr (F.neg 4 1 (by decide))
        nlinarith only [this, hcc_pos]
      have h2_0 : F.f 2 (x 1) * (cc * omega5 x - 1) < 0 := by
        have hmul : 1 / omega5 x * omega5 x < cc * omega5 x := mul_lt_mul_of_pos_right hw5 hC.2.2.1
        rw [one_div_mul_cancel hC.2.2.1.ne'] at hmul
        exact mul_neg_of_neg_of_pos (F.neg 2 1 (by decide)) (by linarith only [hmul])
      have f2_rel : F.f 2 (x 6) - F.f 2 (x 1) = omega5 x * F.f 2 (x 1) := by
        have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
        have ev := M4.fac_eval F 2 5
        rw [F.zero 2 5 (by decide), F.zero 2 0 (by decide), F.zero 2 2 (by decide)] at ev
        have hw : omega5 x * oblX6 x 5 = oblX0 x 5 + oblX2 x 5 - 1 := by unfold omega5; field_simp
        have : oblX6 x 5 * ((F.f 2 (x 6) - F.f 2 (x 1)) - omega5 x * F.f 2 (x 1)) = 0 := by
          linear_combination -ev - F.f 2 (x 1) * hw
        exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hc5.ne')
      have e2 : ∀ᶠ η : ℝ in 𝓝[>] 0, ⟪F.N 2, capView x 1 η cc⟫ < 0 := by
        have hcont : Continuous (fun η : ℝ => -⟪F.N 2, capView x 1 η cc⟫) := by unfold capView; fun_prop
        refine (SF.ev_pos hcont ?_).mono fun _ h => neg_pos.mp h
        dsimp [capView]; rw [one_smul, zero_smul, add_zero, inner_add_right, real_inner_smul_right,
          F.inner_sub, F.inner_sub, F.zero 2 0 (by decide), f2_rel]; linarith only [h2_0]
      have e7 : ∀ᶠ η : ℝ in 𝓝[>] 0, ⟪F.N 7, capView x 1 η cc⟫ < 0 := by
        have hcont : Continuous (fun η : ℝ => -⟪F.N 7, capView x 1 η cc⟫) := by unfold capView; fun_prop
        refine (SF.ev_pos hcont ?_).mono fun _ h => neg_pos.mp h
        have f7_rel : F.f 7 (x 0) - F.f 7 (x 1) = omega3 x * F.f 7 (x 1) := by
          have ev3 := M4.fac_eval F 7 3
          rw [F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at ev3
          have e3 : oblX2 x 3 + oblX6 x 3 - 1 = omega3 x * oblX0 x 3 := by have := M4.eq3 F; linarith only [this]
          have : oblX0 x 3 * ((F.f 7 (x 0) - F.f 7 (x 1)) - omega3 x * F.f 7 (x 1)) = 0 := by
            linear_combination -ev3 + F.f 7 (x 1) * e3
          exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ha3.ne')
        dsimp [capView]; rw [one_smul, zero_smul, add_zero, inner_add_right, real_inner_smul_right,
          F.inner_sub, F.inner_sub, F.zero 7 6 (by decide), f7_rel]
        have := mul_neg_of_neg_of_pos (F.neg 7 1 (by decide)) (sub_pos.mpr hcc.2)
        linarith only [this]
      filter_upwards [e3, e4, h6_ev, e8, e2, e7, self_mem_nhdsWithin] with η h3 h4 h6 h8 h2 h7 (hη : 0 < η)
      refine ⟨fun t ht => ?_, fun t ht => ?_⟩
      · simp only [mem_insert, mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl <;> assumption
      · simp only [mem_insert, mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl
        · dsimp [capView]; simp only [inner_add_right, real_inner_smul_right, one_smul, F.inner_sub,
            F.zero 0 0 (by decide), F.zero 0 1 (by decide), F.zero 0 2 (by decide)]
          simpa using mul_neg_of_pos_of_neg hcc_pos (F.neg 0 6 (by decide))
        · dsimp [capView]; simp only [inner_add_right, real_inner_smul_right, one_smul, F.inner_sub,
            F.zero 1 0 (by decide), F.zero 1 1 (by decide), F.zero 1 6 (by decide)]
          simpa using mul_neg_of_pos_of_neg hη (F.neg 1 2 (by decide))
        · exact h2
        · dsimp [capView]; simp only [inner_add_right, real_inner_smul_right, one_smul, F.inner_sub,
            F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)]
          simpa using F.neg 5 0 (by decide)
        · exact h7
  have hord : ∀ᶠ η : ℝ in 𝓝[>] 0, ∀ i j : ZMod 5,
      ⟪x (wcRim i), capView x 1 0 cc⟫ < ⟪x (wcRim j), capView x 1 0 cc⟫ →
      ⟪x (wcRim i), capView x 1 η cc⟫ < ⟪x (wcRim j), capView x 1 η cc⟫ := by
    rw [eventually_all]; intro i; rw [eventually_all]; intro j
    by_cases hlt : ⟪x (wcRim i), capView x 1 0 cc⟫ < ⟪x (wcRim j), capView x 1 0 cc⟫
    · have hcont : Continuous (fun η : ℝ =>
          ⟪x (wcRim j), capView x 1 η cc⟫ - ⟪x (wcRim i), capView x 1 η cc⟫) := by
        unfold capView; fun_prop
      exact (SF.ev_pos hcont (sub_pos.mpr hlt)).mono fun _ h _ => sub_pos.mp h
    · exact Filter.Eventually.of_forall fun _ h => absurd h hlt
  obtain ⟨η, hcell_η, hord_η⟩ := (hcell.and hord).exists
  have hrob_η : H21.RobUni (fun i => ⟪x (wcRim i), capView x 1 η cc⟫) := by
    intro B b c d hb hbc hcd hdk ⟨h1, h2, h3, h4⟩
    have hle : ∀ u v : ZMod 5,
        ⟪x (wcRim u), capView x 1 η cc⟫ ≤ ⟪x (wcRim v), capView x 1 η cc⟫ →
        ⟪x (wcRim u), capView x 1 0 cc⟫ ≤ ⟪x (wcRim v), capView x 1 0 cc⟫ := fun u v huv =>
      not_lt.mp fun hlt => not_lt_of_ge huv (hord_η v u hlt)
    exact hrob B b c d hb hbc hcd hdk ⟨hle _ _ h1, hle _ _ h2, hle _ _ h3, hle _ _ h4⟩
  exact hF.2.2.2.1 (lexAny_of_cellAt_robUni (by omega) F wcRim_inj wcRim_cyc hcell_η hrob_η)

/-- **FO4 (`RobUni` exclusion at `r60`):** on a `HoleLeaf`, under `OB1 x`, `oblX2 x 3 ≤ 1`,
`oblX2 x 5 ≤ 1`, and `cLo x < r60 < omega3 x` where `⟪x 0 - x 6, capView x 1 0 r60⟫ = 0`,
both `z_1(r60) = ⟪x 5 - x 6, w0(r60)⟫ ≥ 0` and `z_3(r60) = ⟪x 3 - x 6, w0(r60)⟫ ≥ 0`. -/
theorem wc_r60_z1_z3_nonneg {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F)
    (hOB1 : OB1 x) (hb3 : oblX2 x 3 ≤ 1) (hb5 : oblX2 x 5 ≤ 1)
    {r60 : ℝ} (hr60_lo : cLo x < r60) (hr60_hi : r60 < omega3 x)
    (hr60_eq : ⟪x 0 - x 6, capView x 1 0 r60⟫ = 0) :
    0 ≤ ⟪x 5 - x 6, capView x 1 0 r60⟫ ∧ 0 ≤ ⟪x 3 - x 6, capView x 1 0 r60⟫ := by
  have hC : CbarIn x := hF.1
  have T := M4.type24OfFac F
  have hdet : det24 x ≠ 0 := T.det_ne
  let ea := x 0 - x 1
  let eb := x 2 - x 1
  let ec := x 6 - x 1
  let ga := ⟪ea, ea⟫
  let gc := ⟪ec, ec⟫
  let Gab := ⟪ea, eb⟫
  let Gac := ⟪ea, ec⟫
  let Gbc := ⟪eb, ec⟫
  have hea0 : ea ≠ 0 := by
    intro h0; apply hdet
    simp only [det24, vol3, ea, h0, PiLp.zero_apply]; ring
  have hec0 : ec ≠ 0 := by
    intro h0; apply hdet
    simp only [det24, vol3, ec, h0, PiLp.zero_apply]; ring
  have hga : 0 < ga := real_inner_self_pos.mpr hea0
  have hgc : 0 < gc := real_inner_self_pos.mpr hec0
  have hGac : Gac ≤ 0 := hOB1.2.1
  have hCac : 0 < gc - Gac := by linarith
  have hAac : 0 < ga - Gac := by linarith
  have hr60_pos : 0 < r60 := by
    have : 1 / omega5 x ≤ cLo x := le_max_left _ _
    exact lt_trans (one_div_pos.mpr hC.2.2.1) (lt_of_le_of_lt this hr60_lo)
  have hwe_eq : ⟪ea, capView x 1 0 r60⟫ = ⟪ec, capView x 1 0 r60⟫ := by
    have : ea - ec = x 0 - x 6 := by dsimp only [ea, ec]; abel
    rw [← sub_eq_zero, ← inner_sub_left, this, hr60_eq]
  have hr60_val : r60 = (ga - Gac) / (gc - Gac) := by
    have hcomm : ⟪x 6 - x 1, x 0 - x 1⟫ = ⟪x 0 - x 1, x 6 - x 1⟫ := real_inner_comm _ _
    have h0 : (ga - Gac) - r60 * (gc - Gac) = 0 := by
      have : ⟪ea - ec, capView x 1 0 r60⟫ = 0 := by
        have h : ea - ec = x 0 - x 6 := by dsimp only [ea, ec]; abel
        rw [h, hr60_eq]
      dsimp [capView] at this
      rw [one_smul, zero_smul, add_zero, inner_sub_left, inner_add_right, inner_add_right,
        real_inner_smul_right, real_inner_smul_right] at this
      dsimp only [ga, gc, Gac, ea, ec] at this ⊢
      rw [hcomm] at this
      linarith only [this]
    field_simp [hCac.ne']
    linarith only [h0]
  have hcs : 0 < ga * gc - Gac ^ 2 := by
    by_contra hle; push Not at hle
    have hnorm : ⟪gc • ea - Gac • ec, gc • ea - Gac • ec⟫ ≤ 0 := by
      have hcomm : ⟪ec, ea⟫ = ⟪ea, ec⟫ := real_inner_comm _ _
      have hid : ⟪gc • ea - Gac • ec, gc • ea - Gac • ec⟫ = gc * (ga * gc - Gac ^ 2) := by
        simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
        rw [hcomm]
        dsimp only [ga, gc, Gac]; ring
      rw [hid]; exact mul_nonpos_of_nonneg_of_nonpos hgc.le hle
    have heq : gc • ea = Gac • ec :=
      sub_eq_zero.mp (inner_self_eq_zero.mp (le_antisymm hnorm (real_inner_self_nonneg (x := gc • ea - Gac • ec))))
    have hvol : vol3 (gc • ea) eb ec = 0 := by
      rw [heq]; simp only [vol3, PiLp.smul_apply, smul_eq_mul]; ring
    have hvol2 : vol3 (gc • ea) eb ec = gc * det24 x := by
      simp only [det24, vol3, ea, eb, ec, PiLp.smul_apply, smul_eq_mul]; ring
    rw [hvol] at hvol2
    rcases mul_eq_zero.mp hvol2.symm with h | h
    · linarith
    · exact hdet h
  have hwec_pos : 0 < ⟪ec, capView x 1 0 r60⟫ := by
    have hcomm : ⟪x 6 - x 1, x 0 - x 1⟫ = ⟪x 0 - x 1, x 6 - x 1⟫ := real_inner_comm _ _
    have heq : ⟪ec, capView x 1 0 r60⟫ = (ga * gc - Gac ^ 2) / (gc - Gac) := by
      have hne : ⟪x 6 - x 1, x 6 - x 1⟫ - ⟪x 0 - x 1, x 6 - x 1⟫ ≠ 0 := hCac.ne'
      dsimp [capView]
      rw [one_smul, zero_smul, add_zero, inner_add_right, real_inner_smul_right, hr60_val]
      dsimp only [ga, gc, Gac, ea, ec]
      rw [hcomm]
      field_simp [hne]; ring
    rw [heq]; exact div_pos hcs hCac
  have hweb_le : ⟪eb, capView x 1 0 r60⟫ ≤ 0 := by
    have hcomm : ⟪x 2 - x 1, x 0 - x 1⟫ = ⟪x 0 - x 1, x 2 - x 1⟫ := real_inner_comm _ _
    dsimp [capView]
    rw [one_smul, zero_smul, add_zero, inner_add_right, real_inner_smul_right]
    dsimp only [eb]
    rw [hcomm]
    exact add_nonpos hOB1.1 (mul_nonpos_of_nonneg_of_nonpos hr60_pos.le hOB1.2.2)
  have hz12 : ⟪x 2 - x 6, capView x 1 0 r60⟫ < ⟪x 5 - x 6, capView x 1 0 r60⟫ := by
    have h52 : ⟪x 5 - x 2, capView x 1 0 r60⟫ =
        oblX0 x 5 * ⟪ea, capView x 1 0 r60⟫ + (oblX2 x 5 - 1) * ⟪eb, capView x 1 0 r60⟫ +
        oblX6 x 5 * ⟪ec, capView x 1 0 r60⟫ := by
      have : x 5 - x 2 = (x 5 - x 1) - (x 2 - x 1) := by abel
      rw [this, inner_sub_left, M4.inner_rep F 5]
      dsimp only [ea, eb, ec]; ring
    have ha5 : 0 < oblX0 x 5 := T.X0_pos (v := 5) (by decide)
    have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
    have hpos : 0 < ⟪x 5 - x 2, capView x 1 0 r60⟫ := by
      rw [h52, hwe_eq]
      have h1 : 0 < (oblX0 x 5 + oblX6 x 5) * ⟪ec, capView x 1 0 r60⟫ :=
        mul_pos (by linarith) hwec_pos
      have h2 : 0 ≤ (oblX2 x 5 - 1) * ⟪eb, capView x 1 0 r60⟫ :=
        mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hb5) hweb_le
      linarith
    have : x 5 - x 6 - (x 2 - x 6) = x 5 - x 2 := by abel
    rw [← sub_pos, ← inner_sub_left, this]; exact hpos
  have hz32 : ⟪x 2 - x 6, capView x 1 0 r60⟫ < ⟪x 3 - x 6, capView x 1 0 r60⟫ := by
    have h32 : ⟪x 3 - x 2, capView x 1 0 r60⟫ =
        oblX0 x 3 * ⟪ea, capView x 1 0 r60⟫ + (oblX2 x 3 - 1) * ⟪eb, capView x 1 0 r60⟫ +
        oblX6 x 3 * ⟪ec, capView x 1 0 r60⟫ := by
      have : x 3 - x 2 = (x 3 - x 1) - (x 2 - x 1) := by abel
      rw [this, inner_sub_left, M4.inner_rep F 3]
      dsimp only [ea, eb, ec]; ring
    have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
    have hc3 : 0 < oblX6 x 3 := T.X6_pos (v := 3) (by decide)
    have hpos : 0 < ⟪x 3 - x 2, capView x 1 0 r60⟫ := by
      rw [h32, hwe_eq]
      have h1 : 0 < (oblX0 x 3 + oblX6 x 3) * ⟪ec, capView x 1 0 r60⟫ :=
        mul_pos (by linarith) hwec_pos
      have h2 : 0 ≤ (oblX2 x 3 - 1) * ⟪eb, capView x 1 0 r60⟫ :=
        mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hb3) hweb_le
      linarith
    have : x 3 - x 6 - (x 2 - x 6) = x 3 - x 2 := by abel
    rw [← sub_pos, ← inner_sub_left, this]; exact hpos
  have hz1_ge : 0 ≤ ⟪x 5 - x 6, capView x 1 0 r60⟫ := by
    by_contra hlt; push Not at hlt
    let cc : ℝ → ℝ := fun ε => r60 + ε
    have hcc_cont : Continuous cc := by unfold cc; fun_prop
    have hev_lo : ∀ᶠ ε : ℝ in 𝓝[>] 0, cLo x < cc ε :=
      (SF.ev_pos (continuous_iff_continuousAt.mpr fun _ => hcc_cont.continuousAt.sub continuousAt_const)
        (by simpa [cc] using sub_pos.mpr hr60_lo)).mono fun _ h => sub_pos.mp h
    have hev_hi : ∀ᶠ ε : ℝ in 𝓝[>] 0, cc ε < omega3 x :=
      (SF.ev_pos (continuous_iff_continuousAt.mpr fun _ => continuousAt_const.sub hcc_cont.continuousAt)
        (by simpa [cc] using sub_pos.mpr hr60_hi)).mono fun _ h => sub_pos.mp h
    have hev_21 : ∀ᶠ ε : ℝ in 𝓝[>] 0,
        ⟪x 2 - x 6, capView x 1 0 (cc ε)⟫ < ⟪x 5 - x 6, capView x 1 0 (cc ε)⟫ := by
      have hcont : Continuous (fun ε : ℝ =>
          ⟪x 5 - x 6, capView x 1 0 (cc ε)⟫ - ⟪x 2 - x 6, capView x 1 0 (cc ε)⟫) := by
        unfold capView cc; fun_prop
      exact (SF.ev_pos hcont (by simpa [cc] using sub_pos.mpr hz12)).mono fun _ h => sub_pos.mp h
    have hev_10 : ∀ᶠ ε : ℝ in 𝓝[>] 0,
        ⟪x 5 - x 6, capView x 1 0 (cc ε)⟫ < ⟪x 0 - x 6, capView x 1 0 (cc ε)⟫ := by
      have hcont : Continuous (fun ε : ℝ =>
          ⟪x 0 - x 6, capView x 1 0 (cc ε)⟫ - ⟪x 5 - x 6, capView x 1 0 (cc ε)⟫) := by
        unfold capView cc; fun_prop
      exact (SF.ev_pos hcont (by simpa [cc, hr60_eq] using neg_pos.mpr hlt)).mono fun _ h => sub_pos.mp h
    have hev_23 : ∀ᶠ ε : ℝ in 𝓝[>] 0,
        ⟪x 2 - x 6, capView x 1 0 (cc ε)⟫ < ⟪x 3 - x 6, capView x 1 0 (cc ε)⟫ := by
      have hcont : Continuous (fun ε : ℝ =>
          ⟪x 3 - x 6, capView x 1 0 (cc ε)⟫ - ⟪x 2 - x 6, capView x 1 0 (cc ε)⟫) := by
        unfold capView cc; fun_prop
      exact (SF.ev_pos hcont (by simpa [cc] using sub_pos.mpr hz32)).mono fun _ h => sub_pos.mp h
    have hev_04 : ∀ᶠ ε : ℝ in 𝓝[>] 0, ⟪x 0 - x 6, capView x 1 0 (cc ε)⟫ < 0 := by
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      have hcap : capView x 1 0 (cc ε) = capView x 1 0 r60 + ε • ec := by
        dsimp [capView, cc, ec]; module
      rw [hcap, inner_add_right, hr60_eq, zero_add, real_inner_smul_right]
      have h06_ec : ⟪x 0 - x 6, ec⟫ = -(gc - Gac) := by
        have : x 0 - x 6 = ea - ec := by dsimp only [ea, ec]; abel
        rw [this, inner_sub_left]
        dsimp only [gc, Gac, ea, ec]; ring
      rw [h06_ec]
      nlinarith only [hCac, hε]
    obtain ⟨ε, hlo_ε, hhi_ε, h21_ε, h10_ε, h23_ε, h04_ε⟩ :=
      (hev_lo.and (hev_hi.and (hev_21.and (hev_10.and (hev_23.and hev_04))))).exists
    have hshift : ∀ i j : ZMod 5,
        ⟪x (wcRim i) - x 6, capView x 1 0 (cc ε)⟫ < ⟪x (wcRim j) - x 6, capView x 1 0 (cc ε)⟫ →
        ⟪x (wcRim i), capView x 1 0 (cc ε)⟫ < ⟪x (wcRim j), capView x 1 0 (cc ε)⟫ := by
      intro i j hij; rw [inner_sub_left, inner_sub_left] at hij; linarith only [hij]
    have h4_0 : ⟪x 6 - x 6, capView x 1 0 (cc ε)⟫ = 0 := by rw [sub_self, inner_zero_left]
    exact wc_contra_of_rob hF hb3 hb5 ⟨hlo_ε, hhi_ε⟩
      (robUni_2104 (hshift 2 1 h21_ε) (hshift 1 0 h10_ε)
        (hshift 0 4 (by dsimp [wcRim]; rw [h4_0]; exact h04_ε)) (hshift 2 3 h23_ε))
  have hz3_ge : 0 ≤ ⟪x 3 - x 6, capView x 1 0 r60⟫ := by
    by_contra hlt; push Not at hlt
    let cc : ℝ → ℝ := fun ε => r60 - ε
    have hcc_cont : Continuous cc := by unfold cc; fun_prop
    have hev_lo : ∀ᶠ ε : ℝ in 𝓝[>] 0, cLo x < cc ε :=
      (SF.ev_pos (continuous_iff_continuousAt.mpr fun _ => hcc_cont.continuousAt.sub continuousAt_const)
        (by simpa [cc] using sub_pos.mpr hr60_lo)).mono fun _ h => sub_pos.mp h
    have hev_hi : ∀ᶠ ε : ℝ in 𝓝[>] 0, cc ε < omega3 x :=
      (SF.ev_pos (continuous_iff_continuousAt.mpr fun _ => continuousAt_const.sub hcc_cont.continuousAt)
        (by simpa [cc] using sub_pos.mpr hr60_hi)).mono fun _ h => sub_pos.mp h
    have hev_23 : ∀ᶠ ε : ℝ in 𝓝[>] 0,
        ⟪x 2 - x 6, capView x 1 0 (cc ε)⟫ < ⟪x 3 - x 6, capView x 1 0 (cc ε)⟫ := by
      have hcont : Continuous (fun ε : ℝ =>
          ⟪x 3 - x 6, capView x 1 0 (cc ε)⟫ - ⟪x 2 - x 6, capView x 1 0 (cc ε)⟫) := by
        unfold capView cc; fun_prop
      exact (SF.ev_pos hcont (by simpa [cc] using sub_pos.mpr hz32)).mono fun _ h => sub_pos.mp h
    have hev_34 : ∀ᶠ ε : ℝ in 𝓝[>] 0, ⟪x 3 - x 6, capView x 1 0 (cc ε)⟫ < 0 := by
      have hcont : Continuous (fun ε : ℝ => -⟪x 3 - x 6, capView x 1 0 (cc ε)⟫) := by
        unfold capView cc; fun_prop
      exact (SF.ev_pos hcont (by simpa [cc] using neg_pos.mpr hlt)).mono fun _ h => neg_pos.mp h
    have hev_21 : ∀ᶠ ε : ℝ in 𝓝[>] 0,
        ⟪x 2 - x 6, capView x 1 0 (cc ε)⟫ < ⟪x 5 - x 6, capView x 1 0 (cc ε)⟫ := by
      have hcont : Continuous (fun ε : ℝ =>
          ⟪x 5 - x 6, capView x 1 0 (cc ε)⟫ - ⟪x 2 - x 6, capView x 1 0 (cc ε)⟫) := by
        unfold capView cc; fun_prop
      exact (SF.ev_pos hcont (by simpa [cc] using sub_pos.mpr hz12)).mono fun _ h => sub_pos.mp h
    have hev_40 : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ⟪x 0 - x 6, capView x 1 0 (cc ε)⟫ := by
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      have hcap : capView x 1 0 (cc ε) = capView x 1 0 r60 - ε • ec := by
        dsimp [capView, cc, ec]; module
      rw [hcap, inner_sub_right, hr60_eq, zero_sub, real_inner_smul_right]
      have h06_ec : ⟪x 0 - x 6, ec⟫ = -(gc - Gac) := by
        have : x 0 - x 6 = ea - ec := by dsimp only [ea, ec]; abel
        rw [this, inner_sub_left]
        dsimp only [gc, Gac, ea, ec]; ring
      rw [h06_ec]
      nlinarith only [hCac, hε]
    obtain ⟨ε, hlo_ε, hhi_ε, h23_ε, h34_ε, h21_ε, h40_ε⟩ :=
      (hev_lo.and (hev_hi.and (hev_23.and (hev_34.and (hev_21.and hev_40))))).exists
    have hshift : ∀ i j : ZMod 5,
        ⟪x (wcRim i) - x 6, capView x 1 0 (cc ε)⟫ < ⟪x (wcRim j) - x 6, capView x 1 0 (cc ε)⟫ →
        ⟪x (wcRim i), capView x 1 0 (cc ε)⟫ < ⟪x (wcRim j), capView x 1 0 (cc ε)⟫ := by
      intro i j hij; rw [inner_sub_left, inner_sub_left] at hij; linarith only [hij]
    have h4_0 : ⟪x 6 - x 6, capView x 1 0 (cc ε)⟫ = 0 := by rw [sub_self, inner_zero_left]
    exact wc_contra_of_rob hF hb3 hb5 ⟨hlo_ε, hhi_ε⟩
      (robUni_2340 (hshift 2 3 h23_ε)
        (hshift 3 4 (by dsimp [wcRim]; rw [h4_0]; exact h34_ε))
        (hshift 4 0 (by dsimp [wcRim]; rw [h4_0]; exact h40_ε)) (hshift 2 1 h21_ε))
  exact ⟨hz1_ge, hz3_ge⟩
