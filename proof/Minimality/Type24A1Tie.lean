import Minimality.Type24Regions
import Minimality.Type24A1Bridge
import Minimality.Type24A1Frame
import Minimality.Type24TieLex
import Minimality.CSLCorner

/-!
# Type 24, region A1 on the tie: `a1_tie_rupert`

Main glue theorem for region `A1` (`1 < oblX0 x 5`, `F.f 8 (x 0) ≤ F.f 8 (x 5)`) on the tie
`⟪x 2 - x 5, x 5 - x 0⟫ = 0`.

- On the corner `W = {E13 = E23 = 0}`, `CSLCorner.csl24` closes the configuration (`IsRupert`),
  with `csl24_h16_of_region` supplying `h1, h6` and `csl24_hq_of_frame` supplying `hq`
  (derived from `x4_frame` when `σ < 1`, and from `hc63_sig1` when `σ = 1`).
- Outside `W`, dispatching on `⟪F.N 1, bT25 x⟫` (`t25_016`), `⟪F.N 8, bT25 x⟫`, and `⟪F.N 8, bT26 x⟫`
  applies the six tie covers (`Type24TieCover`, `Type24TieCover2`, `Type24TieSigma`, `Type24TieLex`)
  to derive `LexAny F`, contradicting `Hole24R`.
- Without `0 < det24 x`, `a1_tie_rupert` reduces `det24 x < 0` to `0 < det24 (fun i => -x i)` by
  point reflection (`facNeg`, `isRupert_image_smul (-1)`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.A1

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell
  Minimality.LexCell Minimality.Split Minimality.T24.M4 Minimality.T24.A7 Minimality.T24.A8
  Minimality.T24.A10 Minimality.T24.Q24 Minimality.T24 Minimality.GenQuad

/-! ### Derived region and frame lemmas -/

/-- `a4 ≤ 1` from `Reg.A1` and `¬ Q45HalfPred F`. -/
theorem a4_le_of_hA1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hA1 : Reg.A1 x F) (hnQ45 : ¬ Q45HalfPred F) : oblX0 x 4 ≤ 1 := by
  have h5 : ⟪F.N 5, x 5 - x 0⟫ < 0 := (a5_gt_one_iff_N5 F).2 hA1.1
  have hle : ∀ s t : ℝ, 0 < s → 0 < t → 1 < s + t →
      x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0) → s ≤ 1 :=
    (sigma_le_one_iff F).1 hA1.2
  have hN4 : 0 ≤ ⟪F.N 5, x 4 - x 0⟫ := a4_le_of_not_half F hle h5 hnQ45
  have ev := fac_eval F 5 4
  rw [F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)] at ev
  have f0 : F.f 5 (x 0) < 0 := F.neg 5 0 (by decide)
  rw [← F.hN 5 (x 4) (x 0), ev] at hN4
  by_contra hlt; push Not at hlt
  nlinarith

/-- `D45 > 0` (`oblX2 x 5 * oblX6 x 4 - oblX2 x 4 * oblX6 x 5 > 0`) from `F` alone. -/
theorem D45_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    0 < oblX2 x 5 * oblX6 x 4 - oblX2 x 4 * oblX6 x 5 := by
  have T := type24OfFac F
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have ev34 := fac_eval F 3 4
  have ev35 := fac_eval F 3 5
  rw [F.zero 3 0 (by decide), F.zero 3 4 (by decide)] at ev34
  rw [F.zero 3 0 (by decide), F.zero 3 5 (by decide)] at ev35
  set α := -F.f 3 (x 1)
  set β := F.f 3 (x 2) - F.f 3 (x 1)
  set γ := F.f 3 (x 6) - F.f 3 (x 1)
  have hα : 0 < α := by linarith [F.neg 3 1 (by decide)]
  have h4 : α * (oblX0 x 4 - 1) + β * oblX2 x 4 + γ * oblX6 x 4 = 0 := by
    dsimp [α, β, γ]; linarith
  have h5 : α * (oblX0 x 5 - 1) + β * oblX2 x 5 + γ * oblX6 x 5 = 0 := by
    dsimp [α, β, γ]; linarith
  have h025_4 : oblX0 x 4 + oblX2 x 4 - omega5 x * oblX6 x 4 < 1 := by
    have hneg : F.f 2 (x 4) < 0 := F.neg 2 4 (by decide)
    have h1 : F.f 2 (x 1) < 0 := F.neg 2 1 (by decide)
    have ev24 := fac_eval F 2 4
    have ev25 := fac_eval F 2 5
    rw [F.zero 2 0 (by decide), F.zero 2 2 (by decide)] at ev24
    rw [F.zero 2 5 (by decide), F.zero 2 0 (by decide), F.zero 2 2 (by decide)] at ev25
    have h6_eq : F.f 2 (x 6) - F.f 2 (x 1) = F.f 2 (x 1) * omega5 x := by
      have := eq5 F
      have h1' : F.f 2 (x 1) * (1 - oblX0 x 5 - oblX2 x 5) +
          oblX6 x 5 * (F.f 2 (x 6) - F.f 2 (x 1)) = 0 := by linear_combination -ev25
      have h2' : oblX6 x 5 * ((F.f 2 (x 6) - F.f 2 (x 1)) - F.f 2 (x 1) * omega5 x) = 0 := by
        linear_combination h1' + F.f 2 (x 1) * this
      exact sub_eq_zero.mp ((mul_eq_zero.mp h2').resolve_left hc5.ne')
    have e24 : (-F.f 2 (x 1)) * (oblX0 x 4 + oblX2 x 4 - omega5 x * oblX6 x 4 - 1) = F.f 2 (x 4) := by
      rw [ev24, h6_eq]; ring
    have hpos1 : 0 < -F.f 2 (x 1) := by linarith
    nlinarith
  have e_comb : (α - β) * (oblX2 x 5 * oblX6 x 4 - oblX2 x 4 * oblX6 x 5) +
      α * oblX6 x 5 * (oblX0 x 4 + oblX2 x 4 - omega5 x * oblX6 x 4 - 1) = 0 := by
    have := eq5 F
    linear_combination oblX6 x 5 * h4 - oblX6 x 4 * h5 + α * oblX6 x 4 * this
  have hαβ : α - β = -F.f 3 (x 2) := by dsimp [α, β]; ring
  have hαβ_pos : 0 < α - β := by rw [hαβ]; linarith [F.neg 3 2 (by decide)]
  have hrhs_pos : 0 < -α * oblX6 x 5 * (oblX0 x 4 + oblX2 x 4 - omega5 x * oblX6 x 4 - 1) := by
    have : α * oblX6 x 5 * (oblX0 x 4 + oblX2 x 4 - omega5 x * oblX6 x 4 - 1) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos hα hc5) (by linarith)
    linarith
  nlinarith

/-- Non-degeneracy of the T25 tilt basis `(bT25 x, x 3 - x 5, x 0 - x 5)`. -/
theorem t25_det_ne_zero {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    Split.det3 (bT25 x) (x 3 - x 5) (x 0 - x 5) ≠ 0 := by
  intro hdet
  have hb : bT25 x = -(x 2 - x 5) := by unfold bT25; abel
  have hdet' : Split.det3 (x 2 - x 5) (x 0 - x 5) (x 3 - x 5) = 0 := by
    rw [hb] at hdet
    have heq : Split.det3 (-(x 2 - x 5)) (x 3 - x 5) (x 0 - x 5) =
        Split.det3 (x 2 - x 5) (x 0 - x 5) (x 3 - x 5) := by
      simp [Split.det3]; ring
    linarith
  have n3_2 : ⟪F.N 3, x 2 - x 5⟫ = F.f 3 (x 2) := by rw [F.inner_sub, F.zero 3 5 (by decide)]; ring
  have n3_0 : ⟪F.N 3, x 0 - x 5⟫ = 0 := by rw [F.inner_sub, F.zero 3 0 (by decide), F.zero 3 5 (by decide)]; ring
  have n3_3 : ⟪F.N 3, x 3 - x 5⟫ = 0 := by rw [F.inner_sub, F.zero 3 3 (by decide), F.zero 3 5 (by decide)]; ring
  have n6_0 : ⟪F.N 6, x 0 - x 5⟫ = F.f 6 (x 0) := by rw [F.inner_sub, F.zero 6 5 (by decide)]; ring
  have n6_2 : ⟪F.N 6, x 2 - x 5⟫ = 0 := by rw [F.inner_sub, F.zero 6 2 (by decide), F.zero 6 5 (by decide)]; ring
  have n6_3 : ⟪F.N 6, x 3 - x 5⟫ = 0 := by rw [F.inner_sub, F.zero 6 3 (by decide), F.zero 6 5 (by decide)]; ring
  have n2_3 : ⟪F.N 2, x 3 - x 5⟫ = F.f 2 (x 3) := by rw [F.inner_sub, F.zero 2 5 (by decide)]; ring
  have n2_2 : ⟪F.N 2, x 2 - x 5⟫ = 0 := by rw [F.inner_sub, F.zero 2 2 (by decide), F.zero 2 5 (by decide)]; ring
  have n2_0 : ⟪F.N 2, x 0 - x 5⟫ = 0 := by rw [F.inner_sub, F.zero 2 0 (by decide), F.zero 2 5 (by decide)]; ring
  have hprod : Split.det3 (F.N 3) (F.N 6) (F.N 2) * Split.det3 (x 2 - x 5) (x 0 - x 5) (x 3 - x 5) =
      ⟪F.N 3, x 2 - x 5⟫ * (⟪F.N 6, x 0 - x 5⟫ * ⟪F.N 2, x 3 - x 5⟫ - ⟪F.N 6, x 3 - x 5⟫ * ⟪F.N 2, x 0 - x 5⟫) -
      ⟪F.N 3, x 0 - x 5⟫ * (⟪F.N 6, x 2 - x 5⟫ * ⟪F.N 2, x 3 - x 5⟫ - ⟪F.N 6, x 3 - x 5⟫ * ⟪F.N 2, x 2 - x 5⟫) +
      ⟪F.N 3, x 3 - x 5⟫ * (⟪F.N 6, x 2 - x 5⟫ * ⟪F.N 2, x 0 - x 5⟫ - ⟪F.N 6, x 0 - x 5⟫ * ⟪F.N 2, x 2 - x 5⟫) := by
    generalize F.N 3 = u; generalize F.N 6 = v; generalize F.N 2 = w
    generalize x 2 - x 5 = a; generalize x 0 - x 5 = b; generalize x 3 - x 5 = c
    unfold Split.det3
    simp [PiLp.inner_apply, Fin.sum_univ_succ]; ring
  rw [n3_2, n3_0, n3_3, n6_0, n6_2, n6_3, n2_3, n2_2, n2_0, hdet'] at hprod
  have hneg : F.f 3 (x 2) * (F.f 6 (x 0) * F.f 2 (x 3)) < 0 :=
    mul_neg_of_neg_of_pos (F.neg 3 2 (by decide))
      (mul_pos_of_neg_of_neg (F.neg 6 0 (by decide)) (F.neg 2 3 (by decide)))
  linarith

/-- `CrossOf (x 0) (x 3) (x 5) (x 4)` from `x4_frame` with `0 < p4` and `1 < q4`. -/
theorem crossOf_0354_of_x4 {x : Fin 7 → ℝ³} {p4 q4 : ℝ}
    (hx4 : x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5)) (hp4 : 0 < p4) (hq4 : 1 < q4) :
    GenQuad.CrossOf (x 0) (x 3) (x 5) (x 4) := by
  have hD : 0 < p4 + q4 := by linarith
  refine ⟨p4 / (p4 + q4), (p4 + q4 - 1) / (p4 + q4),
    div_pos hp4 hD, (div_lt_one hD).2 (by linarith),
    div_pos (by linarith) hD, (div_lt_one hD).2 (by linarith), ?_⟩
  apply smul_right_injective _ hD.ne'
  have e1 : (p4 + q4) * (p4 / (p4 + q4)) = p4 := by field_simp
  have e2 : (p4 + q4) * (q4 / (p4 + q4)) = q4 := by field_simp
  have e3 : (p4 + q4) * ((p4 + q4 - 1) / (p4 + q4)) = p4 + q4 - 1 := by field_simp
  have e4 : (p4 + q4) * (1 / (p4 + q4)) = 1 := by field_simp
  have h1 : 1 - p4 / (p4 + q4) = q4 / (p4 + q4) := by field_simp; ring
  have h2 : 1 - (p4 + q4 - 1) / (p4 + q4) = 1 / (p4 + q4) := by field_simp; ring
  rw [h1, h2]
  simp only [smul_add, smul_smul]
  rw [e1, e2, e3, e4]
  linear_combination (norm := module) -hx4

/-- `CrossOf (x 0) (x 3) (x 4) (x 5)` from `x4_frame` with `0 < p4` and `1 < q4`. -/
theorem crossOf_0345_of_x4 {x : Fin 7 → ℝ³} {p4 q4 : ℝ}
    (hx4 : x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5)) (hp4 : 0 < p4) (hq4 : 1 < q4) :
    GenQuad.CrossOf (x 0) (x 3) (x 4) (x 5) := by
  have hD : 0 < p4 + q4 := by linarith
  refine ⟨p4 / (p4 + q4), 1 / (p4 + q4),
    div_pos hp4 hD, (div_lt_one hD).2 (by linarith),
    div_pos one_pos hD, (div_lt_one hD).2 (by linarith), ?_⟩
  apply smul_right_injective _ hD.ne'
  have e1 : (p4 + q4) * (p4 / (p4 + q4)) = p4 := by field_simp
  have e2 : (p4 + q4) * (q4 / (p4 + q4)) = q4 := by field_simp
  have e3 : (p4 + q4) * (1 / (p4 + q4)) = 1 := by field_simp
  have e4 : (p4 + q4) * ((p4 + q4 - 1) / (p4 + q4)) = p4 + q4 - 1 := by field_simp
  have h1 : 1 - p4 / (p4 + q4) = q4 / (p4 + q4) := by field_simp; ring
  have h2 : 1 - 1 / (p4 + q4) = (p4 + q4 - 1) / (p4 + q4) := by field_simp
  rw [h1, h2]
  simp only [smul_add, smul_smul]
  rw [e1, e2, e3, e4]
  linear_combination (norm := module) -hx4

/-- `csl24`'s `hq` on `W`: derived from `x4_frame` when `F.f 8 (x 0) < F.f 8 (x 5)` (`σ < 1`),
and from `F.f 2 (x 6) < F.f 2 (x 3)` (`1 < c63`) when `F.f 8 (x 0) = F.f 8 (x 5)` (`σ = 1`). -/
theorem csl24_hq_of_frame {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hsig : F.f 8 (x 0) ≤ F.f 8 (x 5))
    (h23 : ⟪x 2 - x 5, x 3 - x 5⟫ = 0) (h03 : ⟪x 0 - x 5, x 3 - x 5⟫ = 0)
    (hc63_sig1 : F.f 8 (x 0) = F.f 8 (x 5) → F.f 2 (x 6) < F.f 2 (x 3)) :
    0 < ⟪x 6 - x 3, x 3 - x 5⟫ ∨ 0 < ⟪x 4 - x 3, x 3 - x 5⟫ := by
  have hne3 : x 3 - x 5 ≠ 0 := by
    intro h
    have : F.f 2 (x 3) = F.f 2 (x 5) := by
      have := F.inner_sub 2 3 5; rw [h, inner_zero_right] at this; linarith
    rw [F.zero 2 5 (by decide)] at this
    exact (F.neg 2 3 (by decide)).ne this
  have hE33 : 0 < ⟪x 3 - x 5, x 3 - x 5⟫ := real_inner_self_pos.2 hne3
  rcases lt_or_eq_of_le hsig with hlt | heq
  · right
    obtain ⟨p4, q4, hx4, -, -, -, hq4_gt⟩ := x4_frame F
    have hq4 : 1 < q4 := hq4_gt hlt
    have : x 4 - x 3 = p4 • (x 0 - x 5) + (q4 - 1) • (x 3 - x 5) := by
      linear_combination (norm := module) hx4
    rw [this, inner_add_left, inner_smul_left, inner_smul_left, h03, mul_zero, zero_add]
    exact mul_pos (sub_pos.2 hq4) hE33
  · left
    obtain ⟨c61, c62, c63, hx6, _, _, hc63_eq⟩ := frame5_exists F 6
    have hc63 : 1 < c63 := by
      rw [hc63_eq, lt_div_iff_of_neg (F.neg 2 3 (by decide))]
      simpa using hc63_sig1 heq
    have : x 6 - x 3 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + (c63 - 1) • (x 3 - x 5) := by
      linear_combination (norm := module) hx6
    rw [this, inner_add_left, inner_add_left, inner_smul_left, inner_smul_left, inner_smul_left,
      h23, h03, mul_zero, mul_zero, add_zero, zero_add]
    exact mul_pos (sub_pos.2 hc63) hE33

/-! ### Minimal sample-fact bundle for `a1_tie_rupert` -/

/-- Minimal sample-fact bundle for `a1_tie_rupert`: only the hypotheses of `csl24` and the six
tie covers that are not derivable from `Hole24R`, `Reg.A1`, `0 < det24 x`, and the tie.
Rim-specific facts are guarded by the rim signs so that `A1TieSample` holds uniformly across all rims. -/
structure A1TieSample (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop where
  /-- Non-boundary `b5 ≠ 1` (`016` at T25): no lex cover for `⟪F.N 1, bT25 x⟫ = 0` yet (`b5 = 1` is SAT in A1). -/
  hb5_ne : ⟪F.N 1, bT25 x⟫ ≠ 0
  /-- `1 ≤ c63` (`F.f 2 (x 6) ≤ F.f 2 (x 3)` since `F.f 2 (x 3) < 0`): needed by `tieCover_01635`,
  `tieCover_01635_2536`, `tieCover_05346W`, `tieCover_016435`, and `rim_pair_lemma` (sample fact; false at general `σ = 1`). -/
  hc63 : F.f 2 (x 6) ≤ F.f 2 (x 3)
  /-- `1 < c63` at `σ = 1` on `W`: needed by `csl24`'s `hq` when `F.f 8 (x 0) = F.f 8 (x 5)` (sample fact). -/
  hq_sig1 : F.f 8 (x 0) = F.f 8 (x 5) → ⟪x 2 - x 5, x 3 - x 5⟫ = 0 → ⟪x 0 - x 5, x 3 - x 5⟫ = 0 →
    F.f 2 (x 6) < F.f 2 (x 3)
  /-- Facet `4` (`046`) at T25 (`0 < ⟪F.N 4, bT25 x⟫`): sample fact (SAT negated in A1 + Cbar + a4 ≤ 1);
  needed on rims `0536`, `05346`, `016435`. -/
  h4 : ⟪F.N 1, bT25 x⟫ < 0 ∨ ⟪F.N 8, bT25 x⟫ < 0 → 0 < ⟪F.N 4, bT25 x⟫
  /-- T26 `FrontDet` for `2356` (sample fact; needed on all 6 covers). -/
  f2356_26 : FrontDet (x 2) (x 3) (x 5) (x 6) (bT26 x)
  /-- Remaining 4 T26 `FrontDet`s when `0 ≤ ⟪F.N 8, bT26 x⟫` (rim `25346`; sample facts). -/
  t26_fronts_25346 : 0 ≤ ⟪F.N 8, bT26 x⟫ →
    FrontDet (x 2) (x 3) (x 5) (x 4) (bT26 x) ∧
    FrontDet (x 2) (x 4) (x 5) (x 6) (bT26 x) ∧
    FrontDet (x 3) (x 6) (x 2) (x 4) (bT26 x) ∧
    FrontDet (x 3) (x 6) (x 5) (x 4) (bT26 x)
  /-- T25 `FrontDet` for rim `0536` (`⟪F.N 1, bT25 x⟫ < 0`, `0 ≤ ⟪F.N 8, bT25 x⟫`; sample fact). -/
  t25_fronts_0536 : ⟪F.N 1, bT25 x⟫ < 0 → 0 ≤ ⟪F.N 8, bT25 x⟫ →
    FrontDet (x 0) (x 3) (x 5) (x 6) (bT25 x)
  /-- T25 `FrontDet`s for rim `05346` (`⟪F.N 1, bT25 x⟫ < 0`, `⟪F.N 8, bT25 x⟫ < 0`; sample facts). -/
  t25_fronts_05346 : ⟪F.N 1, bT25 x⟫ < 0 → ⟪F.N 8, bT25 x⟫ < 0 →
    FrontDet (x 0) (x 3) (x 5) (x 6) (bT25 x) ∧
    FrontDet (x 0) (x 4) (x 5) (x 6) (bT25 x) ∧
    FrontDet (x 0) (x 4) (x 3) (x 6) (bT25 x) ∧
    FrontDet (x 5) (x 4) (x 3) (x 6) (bT25 x)
  /-- T25 `FrontDet`s for rim `01635` (`0 < ⟪F.N 1, bT25 x⟫`, `0 ≤ ⟪F.N 8, bT25 x⟫`; sample facts).
  Either `FrontDet (x 6) (x 5) (x 1) (x 3)` or the flipped front `FrontDet (x 1) (x 3) (x 6) (x 5)`
  (with `c13 ≤ c63 ∧ 0 < c63 * c11 - c13 * c61` when flipped; `GenQuadLex` will later close `det3 = 0`). -/
  t25_fronts_01635 : 0 < ⟪F.N 1, bT25 x⟫ → 0 ≤ ⟪F.N 8, bT25 x⟫ →
    FrontDet (x 0) (x 6) (x 1) (x 3) (bT25 x) ∧
    FrontDet (x 0) (x 6) (x 1) (x 5) (bT25 x) ∧
    FrontDet (x 0) (x 3) (x 1) (x 5) (bT25 x) ∧
    FrontDet (x 0) (x 3) (x 6) (x 5) (bT25 x) ∧
    (FrontDet (x 6) (x 5) (x 1) (x 3) (bT25 x) ∨
      (FrontDet (x 1) (x 3) (x 6) (x 5) (bT25 x) ∧
        ∀ {c11 c12 c13 c61 c62 c63 : ℝ},
          x 1 - x 5 = c11 • (x 2 - x 5) + c12 • (x 0 - x 5) + c13 • (x 3 - x 5) →
          x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5) →
          c13 ≤ c63 ∧ 0 < c63 * c11 - c13 * c61))
  /-- T25 `FrontDet`s and frame inequalities for rim `016435` (`0 < ⟪F.N 1, bT25 x⟫`, `⟪F.N 8, bT25 x⟫ < 0`; sample facts). -/
  t25_016435 : 0 < ⟪F.N 1, bT25 x⟫ → ⟪F.N 8, bT25 x⟫ < 0 →
    (∀ {p4 q4 c11 c12 c13 c61 c62 c63 : ℝ},
      x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5) →
      x 1 - x 5 = c11 • (x 2 - x 5) + c12 • (x 0 - x 5) + c13 • (x 3 - x 5) →
      x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5) →
      c13 < 1 ∧ c13 ≤ c63 ∧ q4 ≤ c63 ∧ 0 < c63 * c11 - c13 * c61) ∧
    FrontDet (x 0) (x 6) (x 1) (x 4) (bT25 x) ∧
    FrontDet (x 0) (x 6) (x 1) (x 3) (bT25 x) ∧
    FrontDet (x 0) (x 6) (x 1) (x 5) (bT25 x) ∧
    FrontDet (x 0) (x 4) (x 1) (x 3) (bT25 x) ∧
    FrontDet (x 0) (x 4) (x 1) (x 5) (bT25 x) ∧
    FrontDet (x 0) (x 3) (x 1) (x 5) (bT25 x) ∧
    FrontDet (x 0) (x 4) (x 6) (x 3) (bT25 x) ∧
    FrontDet (x 0) (x 4) (x 6) (x 5) (bT25 x) ∧
    FrontDet (x 0) (x 3) (x 6) (x 5) (bT25 x) ∧
    FrontDet (x 1) (x 4) (x 6) (x 3) (bT25 x) ∧
    FrontDet (x 1) (x 4) (x 6) (x 5) (bT25 x) ∧
    FrontDet (x 6) (x 5) (x 1) (x 3) (bT25 x) ∧
    FrontDet (x 4) (x 5) (x 1) (x 3) (bT25 x) ∧
    FrontDet (x 4) (x 5) (x 6) (x 3) (bT25 x)

/-! ### Core tie theorem (`0 < det24 x`) -/

private theorem a1_tie_rupert_core {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hnQ45 : ¬ Q45HalfPred F) (hnLex : ¬ LexAny F)
    (hA1 : Reg.A1 x F) (hdet : 0 < det24 x)
    (htie : ⟪x 2 - x 5, x 5 - x 0⟫ = 0) (hS : A1TieSample x F) :
    IsRupert (univ.image x) := by
  have tie : ⟪x 2 - x 5, x 0 - x 5⟫ = 0 := by
    have : x 0 - x 5 = -(x 5 - x 0) := by abel
    rw [this, inner_neg_right, htie, neg_zero]
  by_cases hW : ⟪x 2 - x 5, x 3 - x 5⟫ = 0 ∧ ⟪x 0 - x 5, x 3 - x 5⟫ = 0
  · have ha4 : oblX0 x 4 ≤ 1 := a4_le_of_hA1 F hA1 hnQ45
    have hD : 0 < oblX2 x 5 * oblX6 x 4 - oblX2 x 4 * oblX6 x 5 := D45_pos F
    obtain ⟨h1, h6⟩ := csl24_h16_of_region F tie hW.1 ha4 hA1.1 hD
    have hq := csl24_hq_of_frame F hA1.2 hW.1 hW.2 (fun heq => hS.hq_sig1 heq hW.1 hW.2)
    exact CSLCorner.csl24 F tie hW.1 hW.2 h1 h6 hq
  · exfalso
    apply hnLex
    -- Common frame & facet data
    obtain ⟨μ, hμ, hb26⟩ := bT26_frame F hdet
    obtain ⟨p4, q4, hx4, hp4, _, hq4_le, _⟩ := x4_frame F
    have hq4_nonneg : 0 ≤ q4 := by linarith [hq4_le hA1.2]
    obtain ⟨c61, c62, c63, hx6, hc61_eq, hc62_eq, hc63_eq⟩ := frame5_exists F 6
    have hc61_pos : 0 < c61 := by
      rw [hc61_eq]
      exact div_pos_of_neg_of_neg (F.neg 3 6 (by decide)) (F.neg 3 2 (by decide))
    have hc62_pos : 0 < c62 := by
      rw [hc62_eq]
      exact div_pos_of_neg_of_neg (F.neg 6 6 (by decide)) (F.neg 6 0 (by decide))
    have hc63 : 1 ≤ c63 := by
      rw [hc63_eq, le_div_iff_of_neg (F.neg 2 3 (by decide))]
      simpa using hS.hc63
    have hd1 : x 3 - x 5 = (0 : ℝ) • (x 2 - x 5) + (1 : ℝ) • (x 3 - x 5) := by simp
    have hδ : (0 : ℝ) < 1 := one_pos
    obtain ⟨h0, h5, h7, h3⟩ := t25_facets F
    obtain ⟨t2, t6⟩ := t25_tilt_frame F
    obtain ⟨g6, g7, g3, g4⟩ := t26_facets F hdet hA1.1
    have hdet25 := t25_det_ne_zero F
    -- Dispatch on `⟪F.N 1, bT25 x⟫` (`b5 ≠ 1`) and `⟪F.N 8, bT25 x⟫`
    rcases lt_or_gt_of_ne hS.hb5_ne with h1_lt | h1_gt
    · -- `N1 < 0`: rim `0536` or `05346`
      rcases lt_or_ge ⟪F.N 8, bT25 x⟫ 0 with h8_25 | h8_25
      · -- Rim `05346` (`N1 < 0`, `N8_25 < 0`)
        have hq4_gt : 1 < q4 := q4_gt_one_of_facet8 F hx4 hx6 hp4 hc61_pos hc62_pos hc63 h8_25
        obtain ⟨κ25, hκ25, h8_eq25⟩ := facet8_T25 F hx4 hx6 hp4 hc61_pos
        have h8_alg : p4 * (c63 - 1) - (q4 - 1) * c62 < 0 := by
          have : κ25 * (p4 * (c63 - 1) - (q4 - 1) * c62) < 0 := by rw [← h8_eq25]; exact h8_25
          nlinarith
        obtain ⟨_, hg8_alg⟩ := rim_pair_lemma hp4 hc61_pos hc62_pos hA1.1 hc63 h8_alg
        obtain ⟨κ26, hκ26, h8_eq26⟩ := facet8_T26 F hx4 hx6 hb26 hp4 hc61_pos hμ
        have g8 : 0 < ⟪F.N 8, bT26 x⟫ := by rw [h8_eq26]; exact mul_pos hκ26 hg8_alg
        obtain ⟨f0356, f0456, f0436, f5436⟩ := hS.t25_fronts_05346 h1_lt h8_25
        obtain ⟨f2354, f2456, f3624, f3654⟩ := hS.t26_fronts_25346 g8.le
        exact tieCover_05346W F hd1 hδ hb26 hμ hA1.1 hx4 hp4 hx6 hc61_pos hc62_pos hc63 tie hW
          hdet25 h3 (hS.h4 (Or.inl h1_lt)) h1_lt h8_25 t2 t6
          (crossOf_0354_of_x4 hx4 hp4 hq4_gt) f0356 f0456 f0436 f5436
          g6 g7 g8 g3 g4 f2354 hS.f2356_26 f2456 f3624 f3654
      · -- Rim `0536` (`N1 < 0`, `0 ≤ N8_25`)
        have f0356 := hS.t25_fronts_0536 h1_lt h8_25
        have h4 := hS.h4 (Or.inl h1_lt)
        rcases lt_or_ge ⟪F.N 8, bT26 x⟫ 0 with g8_lt | g8_ge
        · exact tieCover_0536_2536_le F hd1 hδ hb26 hμ hA1.1 tie hW h3 h4 h8_25 h1_lt h7 t2 t6
            f0356 g6 g7 g3 g8_lt hS.f2356_26
        · obtain ⟨f2354, f2456, f3624, f3654⟩ := hS.t26_fronts_25346 g8_ge
          exact tieCover_0536_le F hd1 hδ hb26 hμ hA1.1 hx4 hp4 hq4_nonneg tie hW h3 h4 h8_25
            h1_lt h7 t2 t6 f0356 g6 g7 g8_ge g3 g4 f2354 hS.f2356_26 f2456 f3624 f3654
    · -- `0 < N1`: rim `01635` or `016435`
      rcases lt_or_ge ⟪F.N 8, bT25 x⟫ 0 with h8_25 | h8_25
      · -- Rim `016435` (`0 < N1`, `N8_25 < 0`)
        have hq4_gt : 1 < q4 := q4_gt_one_of_facet8 F hx4 hx6 hp4 hc61_pos hc62_pos hc63 h8_25
        obtain ⟨κ25, hκ25, h8_eq25⟩ := facet8_T25 F hx4 hx6 hp4 hc61_pos
        have h8_alg : p4 * (c63 - 1) - (q4 - 1) * c62 < 0 := by
          have : κ25 * (p4 * (c63 - 1) - (q4 - 1) * c62) < 0 := by rw [← h8_eq25]; exact h8_25
          nlinarith
        obtain ⟨_, hg8_alg⟩ := rim_pair_lemma hp4 hc61_pos hc62_pos hA1.1 hc63 h8_alg
        obtain ⟨κ26, hκ26, h8_eq26⟩ := facet8_T26 F hx4 hx6 hb26 hp4 hc61_pos hμ
        have g8 : 0 < ⟪F.N 8, bT26 x⟫ := by rw [h8_eq26]; exact mul_pos hκ26 hg8_alg
        obtain ⟨c11, c12, c13, hx1, hc11, hc12, hc13⟩ := x1_frame F
        obtain ⟨hfr, f0614, f0613, f0615, f0413, f0415, f0315, f0463, f0465, f0365,
          f1463, f1465, f6513, f4513, f4563⟩ := hS.t25_016435 h1_gt h8_25
        obtain ⟨hc13_1, hc13_63, hq4_63, h16⟩ := hfr hx4 hx1 hx6
        obtain ⟨f2354, f2456, f3624, f3654⟩ := hS.t26_fronts_25346 g8.le
        exact tieCover_016435 F hd1 hδ hb26 hμ hA1.1 hx4 hp4 hq4_gt hx1 hc11 hc13.le hc13_1
          hx6 hc61_pos hc13_63 hq4_63 h16 tie hW hdet25 h1_gt h3 (hS.h4 (Or.inr h8_25))
          h0 h5 h7 h8_25 t2 t6 (crossOf_0345_of_x4 hx4 hp4 hq4_gt)
          f0614 f0613 f0615 f0413 f0415 f0315 f0463 f0465 f0365 f1463 f1465 f6513 f4513 f4563
          g6 g7 g8 g3 g4 f2354 hS.f2356_26 f2456 f3624 f3654
      · -- Rim `01635` (`0 < N1`, `0 ≤ N8_25`)
        obtain ⟨f0613, f0615, f0315, f0365, h6513⟩ := hS.t25_fronts_01635 h1_gt h8_25
        rcases h6513 with f6513 | ⟨f1365, hfr_flip⟩
        · rcases lt_or_ge ⟪F.N 8, bT26 x⟫ 0 with g8_lt | g8_ge
          · exact tieCover_01635_2536_le F hd1 hδ hb26 hμ hA1.1 hx6 hc61_pos hc63 tie hW
              h1_gt h3 h8_25 h0 h5 h7 t2 t6 f0613 f0615 f0315 f0365 f6513
              g6 g7 g3 g8_lt hS.f2356_26
          · obtain ⟨f2354, f2456, f3624, f3654⟩ := hS.t26_fronts_25346 g8_ge
            exact tieCover_01635_le F hd1 hδ hb26 hμ hA1.1 hx4 hp4 hq4_nonneg hx6 hc61_pos hc63 tie hW
              h1_gt h3 h8_25 h0 h5 h7 t2 t6 f0613 f0615 f0315 f0365 f6513
              g6 g7 g8_ge g3 g4 f2354 hS.f2356_26 f2456 f3624 f3654
        · obtain ⟨c11, c12, c13, hx1, _, _, hc13⟩ := x1_frame F
          obtain ⟨hc13_63, h16⟩ := hfr_flip hx1 hx6
          rcases lt_or_ge ⟪F.N 8, bT26 x⟫ 0 with g8_lt | g8_ge
          · exact tieCover_01635_2536_flip_le F hd1 hδ hb26 hμ hA1.1 hx1 hc13.le hx6 hc61_pos hc63
              hc13_63 h16 tie hW h1_gt h3 h8_25 h0 h5 h7 t2 t6 f0613 f0615 f0315 f0365 f1365
              g6 g7 g3 g8_lt hS.f2356_26
          · obtain ⟨f2354, f2456, f3624, f3654⟩ := hS.t26_fronts_25346 g8_ge
            exact tieCover_01635_flip_le F hd1 hδ hb26 hμ hA1.1 hx4 hp4 hq4_nonneg hx1 hc13.le hx6
              hc61_pos hc63 hc13_63 h16 tie hW h1_gt h3 h8_25 h0 h5 h7 t2 t6
              f0613 f0615 f0315 f0365 f1365 g6 g7 g8_ge g3 g4 f2354 hS.f2356_26 f2456 f3624 f3654

/-! ### Point-reflection wlog (`det24 x < 0` → `0 < det24 (-x)`) -/

/-- Point-reflected `S0xFac` for `fun i => -x i`. -/
def facNeg {n m : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) : S0xFac m S (fun i => -x i) where
  f t y := F.f t (-y)
  N t := -F.N t
  hN t y z := by
    rw [F.hN t (-y) (-z), inner_neg_left, ← inner_neg_right]
    congr 1; abel
  zero t i hi := by simp [F.zero t i hi]
  neg t i hi := by simp [F.neg t i hi]

private theorem det24_neg (x : Fin 7 → ℝ³) : det24 (fun i => -x i) = -det24 x := by
  simp only [det24, vol3, PiLp.sub_apply, PiLp.neg_apply]; ring

private theorem oblX0_neg (x : Fin 7 → ℝ³) (v : Fin 7) : oblX0 (fun i => -x i) v = oblX0 x v := by
  simp only [oblX0, det24_neg]
  have hn : vol3 (-x v - -x 1) (-x 2 - -x 1) (-x 6 - -x 1) =
      -vol3 (x v - x 1) (x 2 - x 1) (x 6 - x 1) := by
    simp only [vol3, PiLp.sub_apply, PiLp.neg_apply]; ring
  rw [hn, neg_div_neg_eq]

private theorem q45HalfPred_of_neg {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (h : Q45HalfPred (facNeg F)) : Q45HalfPred F := by
  intro s t hs ht hst hdec
  have hdec' : (-x 3) - (-x 0) = s • ((-x 4) - (-x 0)) + t • ((-x 5) - (-x 0)) := by
    linear_combination (norm := module) -hdec
  have hq := h s t hs ht hst hdec'
  have hd1 : det3 (-x 5 - -x 6) (-x 2 - -x 6) (-x 4 - -x 6) =
      -det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) := by
    simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_succ]; ring
  have hd2 : det3 (-x 0 - -x 1) (-x 2 - -x 1) (-x 6 - -x 1) =
      -det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := by
    simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_succ]; ring
  have hi : ∀ u v : ℝ³, ⟪-F.N 5, -u - -v⟫ = ⟪F.N 5, u - v⟫ := by
    intro u v; rw [show -u - -v = -(u - v) by abel, inner_neg_left, inner_neg_right, neg_neg]
  unfold Q45.Q45HalfHyp at hq ⊢
  dsimp [facNeg] at hq
  rw [hd1, hd2] at hq
  simp only [hi, neg_mul_neg, neg_eq_zero] at hq
  exact hq

theorem lexAny_of_neg {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (h : LexAny (facNeg F)) : LexAny F := by
  rcases h with ⟨k, hk, c, U, Dn, b, d1, d2, h4, hc, hcyc, hU, hD, hR⟩
  refine ⟨k, hk, c, U, Dn, -b, -d1, -d2, h4, hc, hcyc, ?_, ?_, ?_⟩
  · intro t ht
    simpa [facNeg, inner_neg_left, inner_neg_right] using hU t ht
  · intro t ht
    simpa [facNeg, inner_neg_left, inner_neg_right] using hD t ht
  · simpa [inner_neg_left, inner_neg_right] using hR

/-- **Main A1 tie theorem**: `Hole24R x F`, `Reg.A1 x F`, the tie `⟪x 2 - x 5, x 5 - x 0⟫ = 0`, and
`A1TieSample` (on `x` when `0 < det24 x`, or on `fun i => -x i` when `det24 x < 0`) imply `IsRupert (univ.image x)`. -/
theorem a1_tie_rupert {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hR : Hole24R x F) (hA1 : Reg.A1 x F) (htie : ⟪x 2 - x 5, x 5 - x 0⟫ = 0)
    (hS : if 0 < det24 x then A1TieSample x F else A1TieSample (fun i => -x i) (facNeg F)) :
    IsRupert (univ.image x) := by
  have hdet_ne : det24 x ≠ 0 := (type24OfFac F).det_ne
  rcases lt_or_gt_of_ne hdet_ne with hneg | hpos
  · have hpos' : 0 < det24 (fun i => -x i) := by rw [det24_neg]; linarith
    have hS' : A1TieSample (fun i => -x i) (facNeg F) := by
      simpa [not_lt.2 hneg.le] using hS
    have hA1' : Reg.A1 (fun i => -x i) (facNeg F) := by
      refine ⟨?_, ?_⟩
      · rw [oblX0_neg]; exact hA1.1
      · simpa [facNeg] using hA1.2
    have htie' : ⟪(-x 2) - (-x 5), (-x 5) - (-x 0)⟫ = 0 := by
      rw [show (-x 2) - (-x 5) = -(x 2 - x 5) by abel,
          show (-x 5) - (-x 0) = -(x 5 - x 0) by abel,
          inner_neg_left, inner_neg_right, neg_neg]
      exact htie
    have hrup := a1_tie_rupert_core (facNeg F)
      (fun h => hR.2.2.1 (q45HalfPred_of_neg F h))
      (fun h => hR.2.2.2.2.1 (lexAny_of_neg F h))
      hA1' hpos' htie' hS'
    have himg : univ.image x = (univ.image (fun i => -x i)).image ((-1 : ℝ) • ·) := by
      ext v; simp [Finset.mem_image]
    rw [himg]
    exact Noperts.Pipeline.isRupert_image_smul (-1) (by norm_num) _ hrup
  · exact a1_tie_rupert_core F hR.2.2.1 hR.2.2.2.2.1 hA1 hpos htie (by simpa [hpos] using hS)

end Minimality.T24.A1
