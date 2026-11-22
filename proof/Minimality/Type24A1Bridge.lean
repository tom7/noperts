module

public import Minimality.M4cType24
public import Minimality.Type24Quad

/-!
# Type 24, region A1: bridges and easy region facts (group F1)

`sigma_le_one_iff`, `a5_gt_one_iff_N5`, `lam5_nonneg_A1`, `E05P5U_A1`, `t25_facets`, `t25_016`,
`t26_facets`, `t25_tilt_frame`.  Facet indices are those of `s0x_S24`:
`0 = 012, 1 = 016, 2 = 025, 3 = 0345, 4 = 046, 5 = 126, 6 = 235, 7 = 236, 8 = 346`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.A1

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell
  Minimality.LexCell Minimality.Split Minimality.T24.M4 Minimality.T24.A7 Minimality.T24.A8
  Minimality.T24.Q24 Minimality.T24

/-- Lemma M with the `f8` relation: `x3 - x0 = s (x4 - x0) + t (x5 - x0)` forces
`t f8(x5) = (s + t - 1) f8(x0)` (facet `346`, index 8). -/
theorem f8_relation {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {s t : ℝ}
    (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) :
    t * F.f 8 (x 5) = (s + t - 1) * F.f 8 (x 0) := by
  have h3 : F.f 8 (x 3) = 0 := F.zero 8 3 (by decide)
  have h4 : F.f 8 (x 4) = 0 := F.zero 8 4 (by decide)
  have e : F.f 8 (x 3) - F.f 8 (x 0) =
      s * (F.f 8 (x 4) - F.f 8 (x 0)) + t * (F.f 8 (x 5) - F.f 8 (x 0)) := by
    rw [F.hN 8 (x 3) (x 0), hdec, inner_add_right, inner_smul_right, inner_smul_right,
      ← F.hN 8 (x 4) (x 0), ← F.hN 8 (x 5) (x 0)]
  rw [h3, h4] at e
  linarith

theorem sigma_le_one_iff {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    F.f 8 (x 0) ≤ F.f 8 (x 5) ↔
      ∀ s t : ℝ, 0 < s → 0 < t → 1 < s + t →
        x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0) → s ≤ 1 := by
  have f0 : F.f 8 (x 0) < 0 := F.neg 8 0 (by decide)
  have f5 : F.f 8 (x 5) < 0 := F.neg 8 5 (by decide)
  constructor
  · intro h s t hs ht _ hdec
    have e := f8_relation F hdec
    by_contra hlt
    push Not at hlt
    nlinarith
  · intro h
    obtain ⟨s, t, hs, ht, hdec, -⟩ := lemmaM_coords F
    have e := f8_relation F hdec
    have hst : 1 < s + t := by nlinarith
    have hs1 := h s t hs ht hst hdec
    nlinarith

theorem a5_gt_one_iff_N5 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    ⟪F.N 5, x 5 - x 0⟫ < 0 ↔ 1 < oblX0 x 5 := by
  have ev := fac_eval F 5 5
  rw [F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)] at ev
  have f0 : F.f 5 (x 0) < 0 := F.neg 5 0 (by decide)
  rw [← F.hN 5 (x 5) (x 0), ev]
  constructor
  · intro h; by_contra hle; push Not at hle; nlinarith
  · intro h; nlinarith

/-- `Lam5 > 0` already from `sigma ≤ 1` (the `a5 > 1` hypothesis of A1PLAN is not needed, nor `C̄`):
`t (f7(x5) - f7(x0)) = (s - 1) f7(x0) - s f7(x4)` and `⟪N7, x5 - x0⟫ = -f7(x1) Lam5`. -/
theorem lam5_pos_of_sigma {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hsig : F.f 8 (x 0) ≤ F.f 8 (x 5)) : 0 < Lam5 x := by
  have T := type24OfFac F
  obtain ⟨s, t, hs, ht, hdec, -⟩ := lemmaM_coords F
  have e8 := f8_relation F hdec
  have f0 : F.f 8 (x 0) < 0 := F.neg 8 0 (by decide)
  have f5 : F.f 8 (x 5) < 0 := F.neg 8 5 (by decide)
  have hs1 : s ≤ 1 := by nlinarith
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hf7_0 : F.f 7 (x 0) = (1 + omega3 x) * F.f 7 (x 1) := by
    have ev7 := fac_eval F 7 3
    rw [F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at ev7
    have e3 := eq3 F
    have hprod : oblX0 x 3 * (F.f 7 (x 0) - (1 + omega3 x) * F.f 7 (x 1)) = 0 := by
      linear_combination -ev7 + F.f 7 (x 1) * e3
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left ha3.ne')
  have hw7 : F.f 7 (x 5) - F.f 7 (x 0) = (-F.f 7 (x 1)) * Lam5 x := by
    dsimp [Lam5]
    have ev7_5 := fac_eval F 7 5
    rw [F.zero 7 2 (by decide), F.zero 7 6 (by decide), hf7_0] at ev7_5
    rw [ev7_5, hf7_0]; ring
  have h7_0 : F.f 7 (x 0) < 0 := F.neg 7 0 (by decide)
  have h7_4 : F.f 7 (x 4) < 0 := F.neg 7 4 (by decide)
  have h7_1 : F.f 7 (x 1) < 0 := F.neg 7 1 (by decide)
  have e7 : F.f 7 (x 3) - F.f 7 (x 0) =
      s * (F.f 7 (x 4) - F.f 7 (x 0)) + t * (F.f 7 (x 5) - F.f 7 (x 0)) := by
    rw [F.hN 7 (x 3) (x 0), hdec, inner_add_right, inner_smul_right, inner_smul_right,
      ← F.hN 7 (x 4) (x 0), ← F.hN 7 (x 5) (x 0)]
  rw [F.zero 7 3 (by decide)] at e7
  have hpos : 0 < t * (F.f 7 (x 5) - F.f 7 (x 0)) := by nlinarith
  have hpos' : 0 < F.f 7 (x 5) - F.f 7 (x 0) := (mul_pos_iff_of_pos_left ht).mp hpos
  rw [hw7] at hpos'
  by_contra hc
  push Not at hc
  nlinarith

theorem lam5_nonneg_A1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hsig : F.f 8 (x 0) ≤ F.f 8 (x 5)) : 0 ≤ Lam5 x :=
  (lam5_pos_of_sigma F hsig).le

/-- `lexAny_or_split_E05P5U` with `0 ≤ Lam5` derived from `h346` (`lam5_nonneg_A1`). -/
theorem E05P5U_A1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (ha5 : 1 < oblX0 x 5) (ha4 : oblX0 x 4 ≤ 1)
    (h346 : F.f 8 (x 0) ≤ F.f 8 (x 5))
    (hz : ⟪x 4, x 5 - x 0⟫ < ⟪x 5, x 5 - x 0⟫ ∧
          ⟪x 5, x 5 - x 0⟫ < ⟪x 2, x 5 - x 0⟫) :
    LexAny F ∨ SplitAny24 F :=
  lexAny_or_split_E05P5U F hC ha5 ha4 (lam5_nonneg_A1 F h346) h346 hz

/-! ### Facet signs at the T25 view `bT25 = x5 - x2` -/

theorem inner_bT25 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) :
    ⟪F.N t, bT25 x⟫ = F.f t (x 5) - F.f t (x 2) := by
  rw [bT25, F.inner_sub]

theorem t25_facets {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    ⟪F.N 0, bT25 x⟫ < 0 ∧ ⟪F.N 5, bT25 x⟫ < 0 ∧ ⟪F.N 7, bT25 x⟫ < 0 ∧ 0 < ⟪F.N 3, bT25 x⟫ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [inner_bT25, F.zero 0 2 (by decide)]; linarith [F.neg 0 5 (by decide)]
  · rw [inner_bT25, F.zero 5 2 (by decide)]; linarith [F.neg 5 5 (by decide)]
  · rw [inner_bT25, F.zero 7 2 (by decide)]; linarith [F.neg 7 5 (by decide)]
  · rw [inner_bT25, F.zero 3 5 (by decide)]; linarith [F.neg 3 2 (by decide)]

theorem t25_016 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    ⟪F.N 1, bT25 x⟫ < 0 ↔ 1 < oblX2 x 5 := by
  have ev := fac_eval F 1 5
  rw [F.zero 1 0 (by decide), F.zero 1 6 (by decide)] at ev
  have f2 : F.f 1 (x 2) < 0 := F.neg 1 2 (by decide)
  have e0 := F.zero 1 0 (by decide)
  have e1 : F.f 1 (x 1) = 0 := F.zero 1 1 (by decide)
  rw [e1] at ev
  rw [inner_bT25, ev]
  constructor
  · intro h; by_contra hle; push Not at hle; nlinarith
  · intro h; nlinarith

theorem t25_tilt_frame {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    LexPos3 (-⟪F.N 2, bT25 x⟫) (-⟪F.N 2, x 3 - x 5⟫) (-⟪F.N 2, x 0 - x 5⟫) ∧
    LexPos3 (-⟪F.N 6, bT25 x⟫) (-⟪F.N 6, x 3 - x 5⟫) (-⟪F.N 6, x 0 - x 5⟫) := by
  refine ⟨Or.inr ⟨by rw [bT25_N2 F, neg_zero], Or.inl ?_⟩,
    Or.inr ⟨by rw [bT25_N6 F, neg_zero], Or.inr ⟨?_, ?_⟩⟩⟩
  · rw [F.inner_sub, F.zero 2 5 (by decide)]; linarith [F.neg 2 3 (by decide)]
  · rw [F.inner_sub, F.zero 6 3 (by decide), F.zero 6 5 (by decide)]; simp
  · rw [F.inner_sub, F.zero 6 5 (by decide)]; linarith [F.neg 6 0 (by decide)]

/-! ### Facet signs at the T26 view `bT26` -/

theorem det3_rep0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (v : Fin 7) :
    x v - x 0 = (oblX0 x v - 1) • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) +
      oblX6 x v • (x 6 - x 1) := by
  have T := type24OfFac F
  have hv := T.rep v
  calc x v - x 0 = (x v - x 1) - (x 0 - x 1) := by abel
    _ = (oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1)) -
        (x 0 - x 1) := by rw [hv]; abel
    _ = _ := by module

/-- `bT26 = det24 * (c5 (x6 - x1) + (a5 + b5 - 1) (x2 - x1))`. -/
theorem bT26_frame_form {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    bT26 x = det24 x • (oblX6 x 5 • (x 6 - x 1) + (oblX0 x 5 + oblX2 x 5 - 1) • (x 2 - x 1)) := by
  have h50 := det3_rep0 F 5
  have e20 : (-1 : ℝ) • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) = x 2 - x 0 := by
    module
  have e21 : (0 : ℝ) • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) = x 2 - x 1 := by
    module
  have e61 : (0 : ℝ) • (x 0 - x 1) + (0 : ℝ) • (x 2 - x 1) + (1 : ℝ) • (x 6 - x 1) = x 6 - x 1 := by
    module
  have d21 : Split.det3 (x 2 - x 0) (x 5 - x 0) (x 2 - x 1) = oblX6 x 5 * det24 x := by
    have h := M4.det3_frame x (-1) 1 0 (oblX0 x 5 - 1) (oblX2 x 5) (oblX6 x 5) 0 1 0
    rw [e20, ← h50, e21] at h
    rw [Split.det3_eq_minimality, h]; ring
  have d61 : Split.det3 (x 2 - x 0) (x 5 - x 0) (x 6 - x 1) =
      -(oblX0 x 5 + oblX2 x 5 - 1) * det24 x := by
    have h := M4.det3_frame x (-1) 1 0 (oblX0 x 5 - 1) (oblX2 x 5) (oblX6 x 5) 0 0 1
    rw [e20, ← h50, e61] at h
    rw [Split.det3_eq_minimality, h]; ring
  unfold bT26
  rw [d21, d61]
  module

theorem inner_bT26 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) :
    ⟪F.N t, bT26 x⟫ = det24 x * (oblX6 x 5 * (F.f t (x 6) - F.f t (x 1)) +
      (oblX0 x 5 + oblX2 x 5 - 1) * (F.f t (x 2) - F.f t (x 1))) := by
  rw [bT26_frame_form F, inner_smul_right, inner_add_right, inner_smul_right, inner_smul_right,
    F.inner_sub, F.inner_sub]

/-- Facet signs at the T26 view.  `0 < det24 x` is the orientation of the frame: `bT26` is built from
`det3`, so the signs flip with `det24` (mirror image of the configuration). -/
theorem t26_facets {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hdet : 0 < det24 x)
    (ha5 : 1 < oblX0 x 5) :
    0 < ⟪F.N 6, bT26 x⟫ ∧ 0 < ⟪F.N 7, bT26 x⟫ ∧ ⟪F.N 3, bT26 x⟫ < 0 ∧ ⟪F.N 4, bT26 x⟫ < 0 := by
  have T := type24OfFac F
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [inner_bT26]
    apply mul_pos hdet
    have ev := fac_eval F 6 5
    rw [F.zero 6 5 (by decide), F.zero 6 2 (by decide)] at ev
    have f0 := F.neg 6 0 (by decide)
    have hF0 : 0 < oblX0 x 5 * (-F.f 6 (x 0)) := mul_pos (by linarith) (by linarith)
    rw [F.zero 6 2 (by decide)]
    linarith
  · rw [inner_bT26]
    apply mul_pos hdet
    rw [F.zero 7 6 (by decide), F.zero 7 2 (by decide)]
    nlinarith [F.neg 7 1 (by decide)]
  · rw [inner_bT26]
    apply mul_neg_of_pos_of_neg hdet
    have ev := fac_eval F 3 5
    rw [F.zero 3 5 (by decide), F.zero 3 0 (by decide)] at ev
    have f2 := F.neg 3 2 (by decide)
    have hf2 : 0 < (oblX0 x 5 - 1) * (-F.f 3 (x 2)) := mul_pos (by linarith) (by linarith)
    linarith
  · rw [inner_bT26]
    apply mul_neg_of_pos_of_neg hdet
    have ev := fac_eval F 4 5
    rw [F.zero 4 0 (by decide), F.zero 4 6 (by decide)] at ev
    have f5 := F.neg 4 5 (by decide)
    have f2 := F.neg 4 2 (by decide)
    have hf2 : 0 < (oblX0 x 5 - 1) * (-F.f 4 (x 2)) := mul_pos (by linarith) (by linarith)
    rw [F.zero 4 6 (by decide)]
    linarith

end Minimality.T24.A1
