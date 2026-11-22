module

public import Minimality.M4hType24
public import Minimality.Type24Quad
public import Minimality.GenQuadCross

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.LexCell Minimality.H21 Minimality.H24.SAT
  Minimality.T24.SAT Minimality.T24.RCell Minimality.Split Minimality.T24.M4
  Minimality.T24.A7 Minimality.T24.A8 Minimality.T24.A15 Minimality.T24.Q24

namespace Minimality.T24.A19

/-- Planar (`a`,`c`) crossing data of the chords `p q`, `r s`, projected along `eb`. -/
noncomputable def crD (x : Fin 7 → ℝ³) (p q r s : Fin 7) : ℝ :=
  (oblX0 x p - oblX0 x q) * (oblX6 x r - oblX6 x s) - (oblX6 x p - oblX6 x q) * (oblX0 x r - oblX0 x s)
noncomputable def crL (x : Fin 7 → ℝ³) (_p q r s : Fin 7) : ℝ :=
  (oblX0 x s - oblX0 x q) * (oblX6 x r - oblX6 x s) - (oblX6 x s - oblX6 x q) * (oblX0 x r - oblX0 x s)
noncomputable def crM (x : Fin 7 → ℝ³) (p q _r s : Fin 7) : ℝ :=
  -((oblX0 x p - oblX0 x q) * (oblX6 x s - oblX6 x q) - (oblX6 x p - oblX6 x q) * (oblX0 x s - oblX0 x q))

theorem cr_planar (x : Fin 7 → ℝ³) {p q r s : Fin 7} (hD : crD x p q r s ≠ 0) :
    crL x p q r s / crD x p q r s * oblX0 x p + (1 - crL x p q r s / crD x p q r s) * oblX0 x q =
      crM x p q r s / crD x p q r s * oblX0 x r + (1 - crM x p q r s / crD x p q r s) * oblX0 x s ∧
    crL x p q r s / crD x p q r s * oblX6 x p + (1 - crL x p q r s / crD x p q r s) * oblX6 x q =
      crM x p q r s / crD x p q r s * oblX6 x r + (1 - crM x p q r s / crD x p q r s) * oblX6 x s := by
  have i1 : crL x p q r s * (oblX0 x p - oblX0 x q) - crM x p q r s * (oblX0 x r - oblX0 x s) =
      crD x p q r s * (oblX0 x s - oblX0 x q) := by unfold crL crM crD; ring
  have i2 : crL x p q r s * (oblX6 x p - oblX6 x q) - crM x p q r s * (oblX6 x r - oblX6 x s) =
      crD x p q r s * (oblX6 x s - oblX6 x q) := by unfold crL crM crD; ring
  generalize crL x p q r s = Nl at *
  generalize crM x p q r s = Nm at *
  generalize crD x p q r s = D at *
  constructor
  · field_simp; linear_combination i1
  · field_simp; linear_combination i2

/-- A front pair from planar crossing parameters in `[0,1]` and a positive height. -/
theorem front_gen {x : Fin 7 → ℝ³} (T : Type24 x) {p q r s : Fin 7} (hD : crD x p q r s ≠ 0)
    (hl0 : 0 ≤ crL x p q r s / crD x p q r s) (hl1 : crL x p q r s / crD x p q r s ≤ 1)
    (hm0 : 0 ≤ crM x p q r s / crD x p q r s) (hm1 : crM x p q r s / crD x p q r s ≤ 1)
    (he : 0 < crL x p q r s / crD x p q r s * oblX2 x p +
      (1 - crL x p q r s / crD x p q r s) * oblX2 x q -
      (crM x p q r s / crD x p q r s * oblX2 x r + (1 - crM x p q r s / crD x p q r s) * oblX2 x s)) :
    GenQuad.FrontOf (x p) (x q) (x r) (x s) (x 2 - x 1) := by
  obtain ⟨ha, hc⟩ := cr_planar x hD
  generalize crL x p q r s / crD x p q r s = lam at *
  generalize crM x p q r s / crD x p q r s = mu at *
  refine ⟨lam, mu, _, hl0, hl1, hm0, hm1, he, ?_⟩
  have hp := T.rep p
  have hq := T.rep q
  have hr := T.rep r
  have hs := T.rep s
  ext i
  have hpi := congrArg (fun v => v i) hp
  have hqi := congrArg (fun v => v i) hq
  have hri := congrArg (fun v => v i) hr
  have hsi := congrArg (fun v => v i) hs
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at hpi hqi hri hsi ⊢
  rw [hpi, hqi, hri, hsi]
  linear_combination (x 0 i - x 1 i) * ha + (x 6 i - x 1 i) * hc

/-- Front pair `p q` over a back pair `r s` lying on a down-facing facet `t`. -/
theorem front_dn {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {p q r s : Fin 7} {t : Fin 9}
    (hD : crD x p q r s ≠ 0)
    (hl0 : 0 ≤ crL x p q r s / crD x p q r s) (hl1 : crL x p q r s / crD x p q r s ≤ 1)
    (hm0 : 0 ≤ crM x p q r s / crD x p q r s) (hm1 : crM x p q r s / crD x p q r s ≤ 1)
    (hB : F.f t (x 2) - F.f t (x 1) < 0) (hr : F.f t (x r) = 0) (hs : F.f t (x s) = 0)
    (hneg : crL x p q r s / crD x p q r s * F.f t (x p) +
      (1 - crL x p q r s / crD x p q r s) * F.f t (x q) < 0) :
    GenQuad.FrontOf (x p) (x q) (x r) (x s) (x 2 - x 1) := by
  have T := type24OfFac F
  refine front_gen T hD hl0 hl1 hm0 hm1 ?_
  obtain ⟨ha, hc⟩ := cr_planar x hD
  have e1 := fac_eval F t p
  have e2 := fac_eval F t q
  have e3 := fac_eval F t r
  have e4 := fac_eval F t s
  generalize crL x p q r s / crD x p q r s = lam at *
  generalize crM x p q r s / crD x p q r s = mu at *
  rw [hr] at e3
  rw [hs] at e4
  rw [hr, hs] at *
  by_contra hcon
  push Not at hcon
  have key : (F.f t (x 2) - F.f t (x 1)) * (lam * oblX2 x p + (1 - lam) * oblX2 x q -
      (mu * oblX2 x r + (1 - mu) * oblX2 x s)) = lam * F.f t (x p) + (1 - lam) * F.f t (x q) := by
    linear_combination (-lam) * e1 - (1 - lam) * e2 + mu * e3 + (1 - mu) * e4
      - (F.f t (x 0) - F.f t (x 1)) * ha - (F.f t (x 6) - F.f t (x 1)) * hc
  nlinarith [mul_nonneg_of_nonpos_of_nonpos hB.le hcon]

/-- Front pair `p q` lying on an up-facing facet `t`, over a pair `r s`. -/
theorem front_up {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {p q r s : Fin 7} {t : Fin 9}
    (hD : crD x p q r s ≠ 0)
    (hl0 : 0 ≤ crL x p q r s / crD x p q r s) (hl1 : crL x p q r s / crD x p q r s ≤ 1)
    (hm0 : 0 ≤ crM x p q r s / crD x p q r s) (hm1 : crM x p q r s / crD x p q r s ≤ 1)
    (hB : 0 < F.f t (x 2) - F.f t (x 1)) (hp : F.f t (x p) = 0) (hq : F.f t (x q) = 0)
    (hneg : crM x p q r s / crD x p q r s * F.f t (x r) +
      (1 - crM x p q r s / crD x p q r s) * F.f t (x s) < 0) :
    GenQuad.FrontOf (x p) (x q) (x r) (x s) (x 2 - x 1) := by
  have T := type24OfFac F
  refine front_gen T hD hl0 hl1 hm0 hm1 ?_
  obtain ⟨ha, hc⟩ := cr_planar x hD
  have e1 := fac_eval F t p
  have e2 := fac_eval F t q
  have e3 := fac_eval F t r
  have e4 := fac_eval F t s
  generalize crL x p q r s / crD x p q r s = lam at *
  generalize crM x p q r s / crD x p q r s = mu at *
  rw [hp] at e1
  rw [hq] at e2
  by_contra hcon
  push Not at hcon
  have key : (F.f t (x 2) - F.f t (x 1)) * (lam * oblX2 x p + (1 - lam) * oblX2 x q -
      (mu * oblX2 x r + (1 - mu) * oblX2 x s)) = -(mu * F.f t (x r) + (1 - mu) * F.f t (x s)) := by
    linear_combination (-lam) * e1 - (1 - lam) * e2 + mu * e3 + (1 - mu) * e4
      - (F.f t (x 0) - F.f t (x 1)) * ha - (F.f t (x 6) - F.f t (x 1)) * hc
  nlinarith [mul_nonneg hB.le (neg_nonneg.2 hcon)]

/-- Silhouette edge `u v` (up facet `U`, down facet `D`): every vertex `w` is on the same side. -/
theorem edge_orient {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {U D : Fin 9} {u v w w1 : Fin 7}
    (hU : 0 < F.f U (x 2) - F.f U (x 1)) (hD : F.f D (x 2) - F.f D (x 1) < 0)
    (huU : F.f U (x u) = 0) (huD : F.f D (x u) = 0) (hvU : F.f U (x v) = 0) (hvD : F.f D (x v) = 0)
    (hw : F.f U (x w) < 0 ∨ F.f D (x w) < 0) (hw1 : F.f U (x w1) < 0 ∨ F.f D (x w1) < 0)
    (hO1 : 0 < (oblX0 x v - oblX0 x u) * (oblX6 x w1 - oblX6 x u) -
      (oblX6 x v - oblX6 x u) * (oblX0 x w1 - oblX0 x u)) :
    0 < (oblX0 x v - oblX0 x u) * (oblX6 x w - oblX6 x u) -
      (oblX6 x v - oblX6 x u) * (oblX0 x w - oblX0 x u) := by
  have lU := F.le U w
  have lD := F.le D w
  have lU1 := F.le U w1
  have lD1 := F.le D w1
  generalize hBU : F.f U (x 2) - F.f U (x 1) = BU at *
  generalize hBD : F.f D (x 2) - F.f D (x 1) = BD at *
  have hφw : (-BD) * F.f U (x w) + BU * F.f D (x w) < 0 := by
    rcases hw with h | h <;> nlinarith [mul_nonneg (neg_nonneg.2 hD.le) (neg_nonneg.2 lU),
      mul_nonneg hU.le (neg_nonneg.2 lD), mul_pos (neg_pos.2 hD) (neg_pos.2 h),
      mul_pos hU (neg_pos.2 h)]
  have hφ1 : (-BD) * F.f U (x w1) + BU * F.f D (x w1) < 0 := by
    rcases hw1 with h | h <;> nlinarith [mul_nonneg (neg_nonneg.2 hD.le) (neg_nonneg.2 lU1),
      mul_nonneg hU.le (neg_nonneg.2 lD1), mul_pos (neg_pos.2 hD) (neg_pos.2 h),
      mul_pos hU (neg_pos.2 h)]
  have hphi : ∀ y : Fin 7, (-BD) * F.f U (x y) + BU * F.f D (x y) =
      ((-BD) * F.f U (x 1) + BU * F.f D (x 1)) +
      ((-BD) * (F.f U (x 0) - F.f U (x 1)) + BU * (F.f D (x 0) - F.f D (x 1))) * oblX0 x y +
      ((-BD) * (F.f U (x 6) - F.f U (x 1)) + BU * (F.f D (x 6) - F.f D (x 1))) * oblX6 x y := by
    intro y
    rw [fac_eval F U y, fac_eval F D y, ← hBU, ← hBD]
    ring
  have hu : (-BD) * F.f U (x u) + BU * F.f D (x u) = 0 := by rw [huU, huD]; ring
  have hv : (-BD) * F.f U (x v) + BU * F.f D (x v) = 0 := by rw [hvU, hvD]; ring
  rw [hphi u] at hu
  rw [hphi v] at hv
  rw [hphi w] at hφw
  rw [hphi w1] at hφ1
  generalize ((-BD) * F.f U (x 1) + BU * F.f D (x 1)) = p0 at *
  generalize ((-BD) * (F.f U (x 0) - F.f U (x 1)) + BU * (F.f D (x 0) - F.f D (x 1))) = pa at *
  generalize ((-BD) * (F.f U (x 6) - F.f U (x 1)) + BU * (F.f D (x 6) - F.f D (x 1))) = pc at *
  have key : (p0 + pa * oblX0 x w + pc * oblX6 x w) *
      ((oblX0 x v - oblX0 x u) * (oblX6 x w1 - oblX6 x u) - (oblX6 x v - oblX6 x u) * (oblX0 x w1 - oblX0 x u))
      = (p0 + pa * oblX0 x w1 + pc * oblX6 x w1) *
      ((oblX0 x v - oblX0 x u) * (oblX6 x w - oblX6 x u) - (oblX6 x v - oblX6 x u) * (oblX0 x w - oblX0 x u)) := by
    linear_combination
      ((oblX0 x v - oblX0 x w) * (oblX6 x w1 - oblX6 x w) - (oblX6 x v - oblX6 x w) * (oblX0 x w1 - oblX0 x w)) * hu +
      ((oblX0 x w - oblX0 x u) * (oblX6 x w1 - oblX6 x u) - (oblX6 x w - oblX6 x u) * (oblX0 x w1 - oblX0 x u)) * hv
  by_contra hcon
  push Not at hcon
  nlinarith [mul_pos_of_neg_of_neg hφw hφ1, mul_nonneg (neg_nonneg.2 hφ1.le) (neg_nonneg.2 hcon)]

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- The 14 front pairs of the 6-rim `1 0 5 3 4 6` at `eb`, from facet data and the two brackets (`nB < 0`). -/
theorem neg6_fronts {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (hnb : F.f 3 (x 2) < F.f 3 (x 1)) (h346 : F.f 8 (x 1) < F.f 8 (x 2))
    (h1356 : 0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3)
    (h1456 : 0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4) :
    GenQuad.FrontOf (x 1) (x 5) (x 0) (x 3) (x 2 - x 1) ∧ GenQuad.FrontOf (x 1) (x 5) (x 0) (x 4) (x 2 - x 1) ∧ GenQuad.FrontOf (x 1) (x 5) (x 0) (x 6) (x 2 - x 1) ∧ GenQuad.FrontOf (x 1) (x 3) (x 0) (x 4) (x 2 - x 1) ∧ GenQuad.FrontOf (x 1) (x 3) (x 0) (x 6) (x 2 - x 1) ∧ GenQuad.FrontOf (x 1) (x 4) (x 0) (x 6) (x 2 - x 1) ∧ GenQuad.FrontOf (x 1) (x 3) (x 5) (x 4) (x 2 - x 1) ∧ GenQuad.FrontOf (x 5) (x 6) (x 1) (x 3) (x 2 - x 1) ∧ GenQuad.FrontOf (x 5) (x 6) (x 1) (x 4) (x 2 - x 1) ∧ GenQuad.FrontOf (x 3) (x 6) (x 1) (x 4) (x 2 - x 1) ∧ GenQuad.FrontOf (x 5) (x 6) (x 0) (x 3) (x 2 - x 1) ∧ GenQuad.FrontOf (x 5) (x 6) (x 0) (x 4) (x 2 - x 1) ∧ GenQuad.FrontOf (x 3) (x 6) (x 0) (x 4) (x 2 - x 1) ∧ GenQuad.FrontOf (x 3) (x 6) (x 5) (x 4) (x 2 - x 1) := by
  have T := type24OfFac F
  have hdet := T.det_ne
  have ha0 : oblX0 x 0 = 1 := by simp only [oblX0, det24]; exact div_self hdet
  have ha1 : oblX0 x 1 = 0 := by
    unfold oblX0; rw [show vol3 (x 1 - x 1) (x 2 - x 1) (x 6 - x 1) = 0 by simp [vol3], zero_div]
  have ha6 : oblX0 x 6 = 0 := by
    unfold oblX0; rw [show vol3 (x 6 - x 1) (x 2 - x 1) (x 6 - x 1) = 0 by simp only [vol3]; ring, zero_div]
  have hc0 : oblX6 x 0 = 0 := by
    unfold oblX6; rw [show vol3 (x 0 - x 1) (x 2 - x 1) (x 0 - x 1) = 0 by simp only [vol3]; ring, zero_div]
  have hc1 : oblX6 x 1 = 0 := by
    unfold oblX6; rw [show vol3 (x 0 - x 1) (x 2 - x 1) (x 1 - x 1) = 0 by simp [vol3], zero_div]
  have hc6 : oblX6 x 6 = 1 := by simp only [oblX6, det24]; exact div_self hdet
  have hb1 : oblX2 x 1 = 0 := by
    unfold oblX2; rw [show vol3 (x 0 - x 1) (x 1 - x 1) (x 6 - x 1) = 0 by simp [vol3], zero_div]
  have hb6 : oblX2 x 6 = 0 := by
    unfold oblX2; rw [show vol3 (x 0 - x 1) (x 6 - x 1) (x 6 - x 1) = 0 by simp only [vol3]; ring, zero_div]
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have ha4 : 0 < oblX0 x 4 := T.X0_pos (v := 4) (by decide)
  have ha5 : 0 < oblX0 x 5 := T.X0_pos (v := 5) (by decide)
  have hc3 : 0 < oblX6 x 3 := T.X6_pos (v := 3) (by decide)
  have hc4 : 0 < oblX6 x 4 := T.X6_pos (v := 4) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hB1 : F.f 1 (x 2) - F.f 1 (x 1) < 0 := by
    rw [F.zero 1 1 (by decide)]; linarith [F.neg 1 2 (by decide)]
  have hB2 : 0 < F.f 2 (x 2) - F.f 2 (x 1) := by
    rw [F.zero 2 2 (by decide)]; linarith [F.neg 2 1 (by decide)]
  have hB3 : F.f 3 (x 2) - F.f 3 (x 1) < 0 := by linarith
  have hB6 : 0 < F.f 6 (x 2) - F.f 6 (x 1) := by
    rw [F.zero 6 2 (by decide)]; linarith [F.neg 6 1 (by decide)]
  have hB8 : 0 < F.f 8 (x 2) - F.f 8 (x 1) := by linarith
  have hB4 : F.f 4 (x 2) - F.f 4 (x 1) < 0 := by
    have e := fac_eval F 4 4
    rw [F.zero 4 4 (by decide), F.zero 4 0 (by decide), F.zero 4 6 (by decide)] at e
    have h1 := F.neg 4 1 (by decide)
    have hω := T.eq4
    have hω4 := hC.2.1
    have key : (F.f 4 (x 2) - F.f 4 (x 1)) * oblX2 x 4 =
        F.f 4 (x 1) * (omega4 x * oblX2 x 4) := by
      linear_combination (-1 : ℝ) * e + F.f 4 (x 1) * hω
    by_contra hge
    push Not at hge
    have h2 : 0 ≤ (F.f 4 (x 2) - F.f 4 (x 1)) * oblX2 x 4 := mul_nonneg hge hb4.le
    have h3 := mul_neg_of_neg_of_pos h1 (mul_pos hω4 hb4)
    linarith
  have b051 : 0 < (((oblX0 x 5) - (oblX0 x 0)) * ((oblX6 x 1) - (oblX6 x 0)) - ((oblX6 x 5) - (oblX6 x 0)) * ((oblX0 x 1) - (oblX0 x 0))) := by (try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]); nlinarith [hc5]
  have O053 := edge_orient F (U := 2) (D := 3) (u := 0) (v := 5) (w := 3) (w1 := 1) hB2 hB3 (F.zero 2 0 (by decide)) (F.zero 3 0 (by decide)) (F.zero 2 5 (by decide)) (F.zero 3 5 (by decide)) (Or.inl (F.neg 2 3 (by decide))) (Or.inl (F.neg 2 1 (by decide))) b051
  try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6] at O053
  have O054 := edge_orient F (U := 2) (D := 3) (u := 0) (v := 5) (w := 4) (w1 := 1) hB2 hB3 (F.zero 2 0 (by decide)) (F.zero 3 0 (by decide)) (F.zero 2 5 (by decide)) (F.zero 3 5 (by decide)) (Or.inl (F.neg 2 4 (by decide))) (Or.inl (F.neg 2 1 (by decide))) b051
  try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6] at O054
  have O056 := edge_orient F (U := 2) (D := 3) (u := 0) (v := 5) (w := 6) (w1 := 1) hB2 hB3 (F.zero 2 0 (by decide)) (F.zero 3 0 (by decide)) (F.zero 2 5 (by decide)) (F.zero 3 5 (by decide)) (Or.inl (F.neg 2 6 (by decide))) (Or.inl (F.neg 2 1 (by decide))) b051
  try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6] at O056
  have b530 : 0 < (((oblX0 x 3) - (oblX0 x 5)) * ((oblX6 x 0) - (oblX6 x 5)) - ((oblX6 x 3) - (oblX6 x 5)) * ((oblX0 x 0) - (oblX0 x 5))) := by (try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]); nlinarith [O053]
  have O531 := edge_orient F (U := 6) (D := 3) (u := 5) (v := 3) (w := 1) (w1 := 0) hB6 hB3 (F.zero 6 5 (by decide)) (F.zero 3 5 (by decide)) (F.zero 6 3 (by decide)) (F.zero 3 3 (by decide)) (Or.inl (F.neg 6 1 (by decide))) (Or.inl (F.neg 6 0 (by decide))) b530
  try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6] at O531
  have O534 := edge_orient F (U := 6) (D := 3) (u := 5) (v := 3) (w := 4) (w1 := 0) hB6 hB3 (F.zero 6 5 (by decide)) (F.zero 3 5 (by decide)) (F.zero 6 3 (by decide)) (F.zero 3 3 (by decide)) (Or.inl (F.neg 6 4 (by decide))) (Or.inl (F.neg 6 0 (by decide))) b530
  try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6] at O534
  have O536 := edge_orient F (U := 6) (D := 3) (u := 5) (v := 3) (w := 6) (w1 := 0) hB6 hB3 (F.zero 6 5 (by decide)) (F.zero 3 5 (by decide)) (F.zero 6 3 (by decide)) (F.zero 3 3 (by decide)) (Or.inl (F.neg 6 6 (by decide))) (Or.inl (F.neg 6 0 (by decide))) b530
  try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6] at O536
  have b345 : 0 < (((oblX0 x 4) - (oblX0 x 3)) * ((oblX6 x 5) - (oblX6 x 3)) - ((oblX6 x 4) - (oblX6 x 3)) * ((oblX0 x 5) - (oblX0 x 3))) := by (try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]); nlinarith [O534]
  have O341 := edge_orient F (U := 8) (D := 3) (u := 3) (v := 4) (w := 1) (w1 := 5) hB8 hB3 (F.zero 8 3 (by decide)) (F.zero 3 3 (by decide)) (F.zero 8 4 (by decide)) (F.zero 3 4 (by decide)) (Or.inl (F.neg 8 1 (by decide))) (Or.inl (F.neg 8 5 (by decide))) b345
  try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6] at O341
  have O340 := edge_orient F (U := 8) (D := 3) (u := 3) (v := 4) (w := 0) (w1 := 5) hB8 hB3 (F.zero 8 3 (by decide)) (F.zero 3 3 (by decide)) (F.zero 8 4 (by decide)) (F.zero 3 4 (by decide)) (Or.inl (F.neg 8 0 (by decide))) (Or.inl (F.neg 8 5 (by decide))) b345
  try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6] at O340
  have O346 := edge_orient F (U := 8) (D := 3) (u := 3) (v := 4) (w := 6) (w1 := 5) hB8 hB3 (F.zero 8 3 (by decide)) (F.zero 3 3 (by decide)) (F.zero 8 4 (by decide)) (F.zero 3 4 (by decide)) (Or.inr (F.neg 3 6 (by decide))) (Or.inl (F.neg 8 5 (by decide))) b345
  try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6] at O346
  have b463 : 0 < (((oblX0 x 6) - (oblX0 x 4)) * ((oblX6 x 3) - (oblX6 x 4)) - ((oblX6 x 6) - (oblX6 x 4)) * ((oblX0 x 3) - (oblX0 x 4))) := by (try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]); nlinarith [O346]
  have O461 := edge_orient F (U := 8) (D := 4) (u := 4) (v := 6) (w := 1) (w1 := 3) hB8 hB4 (F.zero 8 4 (by decide)) (F.zero 4 4 (by decide)) (F.zero 8 6 (by decide)) (F.zero 4 6 (by decide)) (Or.inl (F.neg 8 1 (by decide))) (Or.inr (F.neg 4 3 (by decide))) b463
  try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6] at O461
  have O460 := edge_orient F (U := 8) (D := 4) (u := 4) (v := 6) (w := 0) (w1 := 3) hB8 hB4 (F.zero 8 4 (by decide)) (F.zero 4 4 (by decide)) (F.zero 8 6 (by decide)) (F.zero 4 6 (by decide)) (Or.inl (F.neg 8 0 (by decide))) (Or.inr (F.neg 4 3 (by decide))) b463
  try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6] at O460
  have O465 := edge_orient F (U := 8) (D := 4) (u := 4) (v := 6) (w := 5) (w1 := 3) hB8 hB4 (F.zero 8 4 (by decide)) (F.zero 4 4 (by decide)) (F.zero 8 6 (by decide)) (F.zero 4 6 (by decide)) (Or.inl (F.neg 8 5 (by decide))) (Or.inr (F.neg 4 3 (by decide))) b463
  try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6] at O465
  have O153 : 0 < (((oblX0 x 5) - 0) * ((oblX6 x 3) - 0) - ((oblX6 x 5) - 0) * ((oblX0 x 3) - 0)) := by (try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6] at O531); nlinarith [O531]
  have O134 : 0 < (((oblX0 x 3) - 0) * ((oblX6 x 4) - 0) - ((oblX6 x 3) - 0) * ((oblX0 x 4) - 0)) := by (try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6] at O341); nlinarith [O341]
  have O154 : 0 < (((oblX0 x 5) - 0) * ((oblX6 x 4) - 0) - ((oblX6 x 5) - 0) * ((oblX0 x 4) - 0)) := by
    by_contra hn; push Not at hn
    have h1 := mul_pos hc4 O153; have h2 := mul_pos hc5 O134
    nlinarith [mul_nonneg hc3.le (neg_nonneg.2 hn)]
  have O034 : 0 < (((oblX0 x 3) - 1) * ((oblX6 x 4) - 0) - ((oblX6 x 3) - 0) * ((oblX0 x 4) - 1)) := by (try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6] at O340); nlinarith [O340]
  have O046 : 0 < (((oblX0 x 4) - 1) * (1 - 0) - ((oblX6 x 4) - 0) * (0 - 1)) := by (try simp only [ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6] at O460); nlinarith [O460]
  have O036 : 0 < (((oblX0 x 3) - 1) * (1 - 0) - ((oblX6 x 3) - 0) * (0 - 1)) := by
    by_contra hn; push Not at hn
    have h2 := mul_pos hc3 O046
    nlinarith [mul_nonneg hc4.le (neg_nonneg.2 hn)]
  have f15_03 : GenQuad.FrontOf (x 1) (x 5) (x 0) (x 3) (x 2 - x 1) := by
    have hD : 0 < crD x 1 5 0 3 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL0 : 0 < crL x 1 5 0 3 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL1 : crL x 1 5 0 3 < crD x 1 5 0 3 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM0 : 0 < crM x 1 5 0 3 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM1 : crM x 1 5 0 3 < crD x 1 5 0 3 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have l0 := div_pos hL0 hD
    have l1 := (div_lt_one hD).2 hL1
    have m0 := div_pos hM0 hD
    have m1 := (div_lt_one hD).2 hM1
    have hD' := hD.ne'
    refine front_dn F (t := 3) hD' l0.le l1.le m0.le m1.le ?_ ?_ ?_ ?_
    · exact hB3
    · exact F.zero 3 0 (by decide)
    · exact F.zero 3 3 (by decide)
    · rw [F.zero 3 5 (by decide)]; nlinarith [mul_neg_of_pos_of_neg l0 (F.neg 3 1 (by decide))]
  have f15_04 : GenQuad.FrontOf (x 1) (x 5) (x 0) (x 4) (x 2 - x 1) := by
    have hD : 0 < crD x 1 5 0 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL0 : 0 < crL x 1 5 0 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL1 : crL x 1 5 0 4 < crD x 1 5 0 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM0 : 0 < crM x 1 5 0 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM1 : crM x 1 5 0 4 < crD x 1 5 0 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have l0 := div_pos hL0 hD
    have l1 := (div_lt_one hD).2 hL1
    have m0 := div_pos hM0 hD
    have m1 := (div_lt_one hD).2 hM1
    have hD' := hD.ne'
    refine front_dn F (t := 3) hD' l0.le l1.le m0.le m1.le ?_ ?_ ?_ ?_
    · exact hB3
    · exact F.zero 3 0 (by decide)
    · exact F.zero 3 4 (by decide)
    · rw [F.zero 3 5 (by decide)]; nlinarith [mul_neg_of_pos_of_neg l0 (F.neg 3 1 (by decide))]
  have f15_06 : GenQuad.FrontOf (x 1) (x 5) (x 0) (x 6) (x 2 - x 1) := by
    have hD : 0 < crD x 1 5 0 6 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL0 : 0 < crL x 1 5 0 6 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL1 : crL x 1 5 0 6 < crD x 1 5 0 6 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM0 : 0 < crM x 1 5 0 6 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM1 : crM x 1 5 0 6 < crD x 1 5 0 6 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have l0 := div_pos hL0 hD
    have l1 := (div_lt_one hD).2 hL1
    have m0 := div_pos hM0 hD
    have m1 := (div_lt_one hD).2 hM1
    have hD' := hD.ne'
    refine front_dn F (t := 1) hD' l0.le l1.le m0.le m1.le ?_ ?_ ?_ ?_
    · exact hB1
    · exact F.zero 1 0 (by decide)
    · exact F.zero 1 6 (by decide)
    · rw [F.zero 1 1 (by decide)]; nlinarith [mul_neg_of_pos_of_neg (sub_pos.2 l1) (F.neg 1 5 (by decide))]
  have f13_04 : GenQuad.FrontOf (x 1) (x 3) (x 0) (x 4) (x 2 - x 1) := by
    have hD : 0 < crD x 1 3 0 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL0 : 0 < crL x 1 3 0 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL1 : crL x 1 3 0 4 < crD x 1 3 0 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM0 : 0 < crM x 1 3 0 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM1 : crM x 1 3 0 4 < crD x 1 3 0 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have l0 := div_pos hL0 hD
    have l1 := (div_lt_one hD).2 hL1
    have m0 := div_pos hM0 hD
    have m1 := (div_lt_one hD).2 hM1
    have hD' := hD.ne'
    refine front_dn F (t := 3) hD' l0.le l1.le m0.le m1.le ?_ ?_ ?_ ?_
    · exact hB3
    · exact F.zero 3 0 (by decide)
    · exact F.zero 3 4 (by decide)
    · rw [F.zero 3 3 (by decide)]; nlinarith [mul_neg_of_pos_of_neg l0 (F.neg 3 1 (by decide))]
  have f13_06 : GenQuad.FrontOf (x 1) (x 3) (x 0) (x 6) (x 2 - x 1) := by
    have hD : 0 < crD x 1 3 0 6 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL0 : 0 < crL x 1 3 0 6 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL1 : crL x 1 3 0 6 < crD x 1 3 0 6 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM0 : 0 < crM x 1 3 0 6 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM1 : crM x 1 3 0 6 < crD x 1 3 0 6 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have l0 := div_pos hL0 hD
    have l1 := (div_lt_one hD).2 hL1
    have m0 := div_pos hM0 hD
    have m1 := (div_lt_one hD).2 hM1
    have hD' := hD.ne'
    refine front_dn F (t := 1) hD' l0.le l1.le m0.le m1.le ?_ ?_ ?_ ?_
    · exact hB1
    · exact F.zero 1 0 (by decide)
    · exact F.zero 1 6 (by decide)
    · rw [F.zero 1 1 (by decide)]; nlinarith [mul_neg_of_pos_of_neg (sub_pos.2 l1) (F.neg 1 3 (by decide))]
  have f14_06 : GenQuad.FrontOf (x 1) (x 4) (x 0) (x 6) (x 2 - x 1) := by
    have hD : 0 < crD x 1 4 0 6 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL0 : 0 < crL x 1 4 0 6 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL1 : crL x 1 4 0 6 < crD x 1 4 0 6 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM0 : 0 < crM x 1 4 0 6 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM1 : crM x 1 4 0 6 < crD x 1 4 0 6 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have l0 := div_pos hL0 hD
    have l1 := (div_lt_one hD).2 hL1
    have m0 := div_pos hM0 hD
    have m1 := (div_lt_one hD).2 hM1
    have hD' := hD.ne'
    refine front_dn F (t := 1) hD' l0.le l1.le m0.le m1.le ?_ ?_ ?_ ?_
    · exact hB1
    · exact F.zero 1 0 (by decide)
    · exact F.zero 1 6 (by decide)
    · rw [F.zero 1 1 (by decide)]; nlinarith [mul_neg_of_pos_of_neg (sub_pos.2 l1) (F.neg 1 4 (by decide))]
  have f13_54 : GenQuad.FrontOf (x 1) (x 3) (x 5) (x 4) (x 2 - x 1) := by
    have hD : 0 < crD x 1 3 5 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL0 : 0 < crL x 1 3 5 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL1 : crL x 1 3 5 4 < crD x 1 3 5 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM0 : 0 < crM x 1 3 5 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM1 : crM x 1 3 5 4 < crD x 1 3 5 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have l0 := div_pos hL0 hD
    have l1 := (div_lt_one hD).2 hL1
    have m0 := div_pos hM0 hD
    have m1 := (div_lt_one hD).2 hM1
    have hD' := hD.ne'
    refine front_dn F (t := 3) hD' l0.le l1.le m0.le m1.le ?_ ?_ ?_ ?_
    · exact hB3
    · exact F.zero 3 5 (by decide)
    · exact F.zero 3 4 (by decide)
    · rw [F.zero 3 3 (by decide)]; nlinarith [mul_neg_of_pos_of_neg l0 (F.neg 3 1 (by decide))]
  have f56_13 : GenQuad.FrontOf (x 5) (x 6) (x 1) (x 3) (x 2 - x 1) := by
    have hD : crD x 5 6 1 3 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL0 : crL x 5 6 1 3 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL1 : crD x 5 6 1 3 < crL x 5 6 1 3 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM0 : crM x 5 6 1 3 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM1 : crD x 5 6 1 3 < crM x 5 6 1 3 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have l0 := div_pos_of_neg_of_neg hL0 hD
    have l1 := (div_lt_one_of_neg hD).2 hL1
    have m0 := div_pos_of_neg_of_neg hM0 hD
    have m1 := (div_lt_one_of_neg hD).2 hM1
    have hD' := hD.ne
    refine front_gen T hD' l0.le l1.le m0.le m1.le ?_
    have e : crL x 5 6 1 3 / crD x 5 6 1 3 * oblX2 x 5 + (1 - crL x 5 6 1 3 / crD x 5 6 1 3) * oblX2 x 6 - (crM x 5 6 1 3 / crD x 5 6 1 3 * oblX2 x 1 + (1 - crM x 5 6 1 3 / crD x 5 6 1 3) * oblX2 x 3) = -(oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3) / crD x 5 6 1 3 := by
      have hk : crL x 5 6 1 3 * oblX2 x 5 - (crD x 5 6 1 3 - crM x 5 6 1 3) * oblX2 x 3 = -(oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3) := by
        simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6]; ring
      rw [hb6, hb1]
      generalize crL x 5 6 1 3 = Nl at *
      generalize crM x 5 6 1 3 = Nm at *
      generalize crD x 5 6 1 3 = D at *
      field_simp; linear_combination hk
    rw [e]; exact div_pos_of_neg_of_neg (by linarith) hD
  have f56_14 : GenQuad.FrontOf (x 5) (x 6) (x 1) (x 4) (x 2 - x 1) := by
    have hD : crD x 5 6 1 4 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL0 : crL x 5 6 1 4 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL1 : crD x 5 6 1 4 < crL x 5 6 1 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM0 : crM x 5 6 1 4 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM1 : crD x 5 6 1 4 < crM x 5 6 1 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have l0 := div_pos_of_neg_of_neg hL0 hD
    have l1 := (div_lt_one_of_neg hD).2 hL1
    have m0 := div_pos_of_neg_of_neg hM0 hD
    have m1 := (div_lt_one_of_neg hD).2 hM1
    have hD' := hD.ne
    refine front_gen T hD' l0.le l1.le m0.le m1.le ?_
    have e : crL x 5 6 1 4 / crD x 5 6 1 4 * oblX2 x 5 + (1 - crL x 5 6 1 4 / crD x 5 6 1 4) * oblX2 x 6 - (crM x 5 6 1 4 / crD x 5 6 1 4 * oblX2 x 1 + (1 - crM x 5 6 1 4 / crD x 5 6 1 4) * oblX2 x 4) = -(oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4) / crD x 5 6 1 4 := by
      have hk : crL x 5 6 1 4 * oblX2 x 5 - (crD x 5 6 1 4 - crM x 5 6 1 4) * oblX2 x 4 = -(oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4) := by
        simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6]; ring
      rw [hb6, hb1]
      generalize crL x 5 6 1 4 = Nl at *
      generalize crM x 5 6 1 4 = Nm at *
      generalize crD x 5 6 1 4 = D at *
      field_simp; linear_combination hk
    rw [e]; exact div_pos_of_neg_of_neg (by linarith) hD
  have f36_14 : GenQuad.FrontOf (x 3) (x 6) (x 1) (x 4) (x 2 - x 1) := by
    have hD : crD x 3 6 1 4 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL0 : crL x 3 6 1 4 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL1 : crD x 3 6 1 4 < crL x 3 6 1 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM0 : crM x 3 6 1 4 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM1 : crD x 3 6 1 4 < crM x 3 6 1 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have l0 := div_pos_of_neg_of_neg hL0 hD
    have l1 := (div_lt_one_of_neg hD).2 hL1
    have m0 := div_pos_of_neg_of_neg hM0 hD
    have m1 := (div_lt_one_of_neg hD).2 hM1
    have hD' := hD.ne
    refine front_up F (t := 8) hD' l0.le l1.le m0.le m1.le ?_ ?_ ?_ ?_
    · exact hB8
    · exact F.zero 8 3 (by decide)
    · exact F.zero 8 6 (by decide)
    · rw [F.zero 8 4 (by decide)]; nlinarith [mul_neg_of_pos_of_neg m0 (F.neg 8 1 (by decide))]
  have f56_03 : GenQuad.FrontOf (x 5) (x 6) (x 0) (x 3) (x 2 - x 1) := by
    have hD : crD x 5 6 0 3 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL0 : crL x 5 6 0 3 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL1 : crD x 5 6 0 3 < crL x 5 6 0 3 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM0 : crM x 5 6 0 3 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM1 : crD x 5 6 0 3 < crM x 5 6 0 3 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have l0 := div_pos_of_neg_of_neg hL0 hD
    have l1 := (div_lt_one_of_neg hD).2 hL1
    have m0 := div_pos_of_neg_of_neg hM0 hD
    have m1 := (div_lt_one_of_neg hD).2 hM1
    have hD' := hD.ne
    refine front_dn F (t := 3) hD' l0.le l1.le m0.le m1.le ?_ ?_ ?_ ?_
    · exact hB3
    · exact F.zero 3 0 (by decide)
    · exact F.zero 3 3 (by decide)
    · rw [F.zero 3 5 (by decide)]; nlinarith [mul_neg_of_pos_of_neg (sub_pos.2 l1) (F.neg 3 6 (by decide))]
  have f56_04 : GenQuad.FrontOf (x 5) (x 6) (x 0) (x 4) (x 2 - x 1) := by
    have hD : crD x 5 6 0 4 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL0 : crL x 5 6 0 4 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL1 : crD x 5 6 0 4 < crL x 5 6 0 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM0 : crM x 5 6 0 4 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM1 : crD x 5 6 0 4 < crM x 5 6 0 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have l0 := div_pos_of_neg_of_neg hL0 hD
    have l1 := (div_lt_one_of_neg hD).2 hL1
    have m0 := div_pos_of_neg_of_neg hM0 hD
    have m1 := (div_lt_one_of_neg hD).2 hM1
    have hD' := hD.ne
    refine front_dn F (t := 3) hD' l0.le l1.le m0.le m1.le ?_ ?_ ?_ ?_
    · exact hB3
    · exact F.zero 3 0 (by decide)
    · exact F.zero 3 4 (by decide)
    · rw [F.zero 3 5 (by decide)]; nlinarith [mul_neg_of_pos_of_neg (sub_pos.2 l1) (F.neg 3 6 (by decide))]
  have f36_04 : GenQuad.FrontOf (x 3) (x 6) (x 0) (x 4) (x 2 - x 1) := by
    have hD : crD x 3 6 0 4 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL0 : crL x 3 6 0 4 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL1 : crD x 3 6 0 4 < crL x 3 6 0 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM0 : crM x 3 6 0 4 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM1 : crD x 3 6 0 4 < crM x 3 6 0 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have l0 := div_pos_of_neg_of_neg hL0 hD
    have l1 := (div_lt_one_of_neg hD).2 hL1
    have m0 := div_pos_of_neg_of_neg hM0 hD
    have m1 := (div_lt_one_of_neg hD).2 hM1
    have hD' := hD.ne
    refine front_dn F (t := 3) hD' l0.le l1.le m0.le m1.le ?_ ?_ ?_ ?_
    · exact hB3
    · exact F.zero 3 0 (by decide)
    · exact F.zero 3 4 (by decide)
    · rw [F.zero 3 3 (by decide)]; nlinarith [mul_neg_of_pos_of_neg (sub_pos.2 l1) (F.neg 3 6 (by decide))]
  have f36_54 : GenQuad.FrontOf (x 3) (x 6) (x 5) (x 4) (x 2 - x 1) := by
    have hD : crD x 3 6 5 4 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL0 : crL x 3 6 5 4 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hL1 : crD x 3 6 5 4 < crL x 3 6 5 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM0 : crM x 3 6 5 4 < 0 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have hM1 : crD x 3 6 5 4 < crM x 3 6 5 4 := by simp only [crD, crL, crM, ha0, hc0, ha1, hc1, ha6, hc6, hb1, hb6]; linarith
    have l0 := div_pos_of_neg_of_neg hL0 hD
    have l1 := (div_lt_one_of_neg hD).2 hL1
    have m0 := div_pos_of_neg_of_neg hM0 hD
    have m1 := (div_lt_one_of_neg hD).2 hM1
    have hD' := hD.ne
    refine front_dn F (t := 3) hD' l0.le l1.le m0.le m1.le ?_ ?_ ?_ ?_
    · exact hB3
    · exact F.zero 3 5 (by decide)
    · exact F.zero 3 4 (by decide)
    · rw [F.zero 3 3 (by decide)]; nlinarith [mul_neg_of_pos_of_neg (sub_pos.2 l1) (F.neg 3 6 (by decide))]
  exact ⟨f15_03, f15_04, f15_06, f13_04, f13_06, f14_06, f13_54, f56_13, f56_14, f36_14, f56_03, f56_04, f36_04, f36_54⟩

private def cN6 : ZMod 6 → Fin 7 := ![1, 0, 5, 3, 4, 6]
private theorem cN6_inj : Function.Injective cN6 := by decide
private theorem cN6_cyc : S0xCycUD s0x_S24 cN6 {0, 2, 5, 6, 7, 8} {1, 3, 4} := by decide

/-- The leaf: 6-rim `1 0 5 3 4 6` at `(eb, -ea - ec, ea)`. -/
theorem lexAny_neg6_leaf {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hdet : Split.det3 (x 2 - x 1) (-(x 0 - x 1) - (x 6 - x 1)) (x 0 - x 1) ≠ 0)
    (hN0 : ⟪F.N 0, x 2 - x 1⟫ = 0) (hN0d : 0 < ⟪F.N 0, -(x 0 - x 1) - (x 6 - x 1)⟫)
    (hN5 : ⟪F.N 5, x 2 - x 1⟫ = 0) (hN5d : 0 < ⟪F.N 5, -(x 0 - x 1) - (x 6 - x 1)⟫)
    (hN2 : 0 < ⟪F.N 2, x 2 - x 1⟫) (hN6 : 0 < ⟪F.N 6, x 2 - x 1⟫)
    (hN7 : 0 < ⟪F.N 7, x 2 - x 1⟫) (hN8 : 0 < ⟪F.N 8, x 2 - x 1⟫)
    (hN1 : ⟪F.N 1, x 2 - x 1⟫ < 0) (hN4 : ⟪F.N 4, x 2 - x 1⟫ < 0)
    (hN3 : LexPos3 (-⟪F.N 3, x 2 - x 1⟫) (-⟪F.N 3, -(x 0 - x 1) - (x 6 - x 1)⟫)
      (-⟪F.N 3, x 0 - x 1⟫))
    (hX : GenQuad.CrossOf (x 0) (x 3) (x 5) (x 4))
    (f15_03 : GenQuad.FrontOf (x 1) (x 5) (x 0) (x 3) (x 2 - x 1))
    (f15_04 : GenQuad.FrontOf (x 1) (x 5) (x 0) (x 4) (x 2 - x 1))
    (f15_06 : GenQuad.FrontOf (x 1) (x 5) (x 0) (x 6) (x 2 - x 1))
    (f13_04 : GenQuad.FrontOf (x 1) (x 3) (x 0) (x 4) (x 2 - x 1))
    (f13_06 : GenQuad.FrontOf (x 1) (x 3) (x 0) (x 6) (x 2 - x 1))
    (f14_06 : GenQuad.FrontOf (x 1) (x 4) (x 0) (x 6) (x 2 - x 1))
    (f13_54 : GenQuad.FrontOf (x 1) (x 3) (x 5) (x 4) (x 2 - x 1))
    (f56_13 : GenQuad.FrontOf (x 5) (x 6) (x 1) (x 3) (x 2 - x 1))
    (f56_14 : GenQuad.FrontOf (x 5) (x 6) (x 1) (x 4) (x 2 - x 1))
    (f36_14 : GenQuad.FrontOf (x 3) (x 6) (x 1) (x 4) (x 2 - x 1))
    (f56_03 : GenQuad.FrontOf (x 5) (x 6) (x 0) (x 3) (x 2 - x 1))
    (f56_04 : GenQuad.FrontOf (x 5) (x 6) (x 0) (x 4) (x 2 - x 1))
    (f36_04 : GenQuad.FrontOf (x 3) (x 6) (x 0) (x 4) (x 2 - x 1))
    (f36_54 : GenQuad.FrontOf (x 3) (x 6) (x 5) (x 4) (x 2 - x 1))
    (m0123 : ¬ (max (z x (x 2 - x 1) 0) (z x (x 2 - x 1) 3) ≤ min (z x (x 2 - x 1) 1) (z x (x 2 - x 1) 5)))
    (m0124 : ¬ (max (z x (x 2 - x 1) 0) (z x (x 2 - x 1) 4) ≤ min (z x (x 2 - x 1) 1) (z x (x 2 - x 1) 5)))
    (m0125 : ¬ (max (z x (x 2 - x 1) 0) (z x (x 2 - x 1) 6) ≤ min (z x (x 2 - x 1) 1) (z x (x 2 - x 1) 5)))
    (m0134 : ¬ (max (z x (x 2 - x 1) 0) (z x (x 2 - x 1) 4) ≤ min (z x (x 2 - x 1) 1) (z x (x 2 - x 1) 3)))
    (m0135 : ¬ (max (z x (x 2 - x 1) 0) (z x (x 2 - x 1) 6) ≤ min (z x (x 2 - x 1) 1) (z x (x 2 - x 1) 3)))
    (m0145 : ¬ (max (z x (x 2 - x 1) 0) (z x (x 2 - x 1) 6) ≤ min (z x (x 2 - x 1) 1) (z x (x 2 - x 1) 4)))
    (m0234 : ¬ (max (z x (x 2 - x 1) 5) (z x (x 2 - x 1) 4) ≤ min (z x (x 2 - x 1) 1) (z x (x 2 - x 1) 3)))
    (m0235 : ¬ (max (z x (x 2 - x 1) 1) (z x (x 2 - x 1) 3) ≤ min (z x (x 2 - x 1) 5) (z x (x 2 - x 1) 6)))
    (m0245 : ¬ (max (z x (x 2 - x 1) 1) (z x (x 2 - x 1) 4) ≤ min (z x (x 2 - x 1) 5) (z x (x 2 - x 1) 6)))
    (m0345 : ¬ (max (z x (x 2 - x 1) 1) (z x (x 2 - x 1) 4) ≤ min (z x (x 2 - x 1) 3) (z x (x 2 - x 1) 6)))
    (m1235 : ¬ (max (z x (x 2 - x 1) 0) (z x (x 2 - x 1) 3) ≤ min (z x (x 2 - x 1) 5) (z x (x 2 - x 1) 6)))
    (m1245 : ¬ (max (z x (x 2 - x 1) 0) (z x (x 2 - x 1) 4) ≤ min (z x (x 2 - x 1) 5) (z x (x 2 - x 1) 6)))
    (m1345 : ¬ (max (z x (x 2 - x 1) 0) (z x (x 2 - x 1) 4) ≤ min (z x (x 2 - x 1) 3) (z x (x 2 - x 1) 6)))
    (m2345 : ¬ (max (z x (x 2 - x 1) 5) (z x (x 2 - x 1) 4) ≤ min (z x (x 2 - x 1) 3) (z x (x 2 - x 1) 6))) :
    LexAny F := by
  have hb : x 2 - x 1 ≠ 0 := fun h => by rw [h, inner_zero_right] at hN2; exact lt_irrefl _ hN2
  have hinj := inj_of_fac F
  have h05 : x 0 ≠ x 5 := fun h => absurd (hinj h) (by decide)
  obtain ⟨cB, cA⟩ := GenQuad.lexClause_of_crossOf hX hdet h05
  refine GenQuad.lexAny_of_clauses F (k := 6) (by norm_num) cN6_inj cN6_cyc (x 2 - x 1)
    (-(x 0 - x 1) - (x 6 - x 1)) (x 0 - x 1) ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr ⟨hN0, Or.inl hN0d⟩
    · exact Or.inl hN2
    · exact Or.inr ⟨hN5, Or.inl hN5d⟩
    · exact Or.inl hN6
    · exact Or.inl hN7
    · exact Or.inl hN8
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact Or.inl (by linarith)
    · exact hN3
    · exact Or.inl (by linarith)
  · exact GenQuad.clauses_six (p := fun i => x (cN6 i)) (b := x 2 - x 1)
      (d1 := -(x 0 - x 1) - (x 6 - x 1)) (d2 := x 0 - x 1)
      (lexClause_of_z m0123) (GenQuad.lexClause_of_frontOf hb f15_03)
      (lexClause_of_z m0124) (GenQuad.lexClause_of_frontOf hb f15_04)
      (lexClause_of_z m0125) (GenQuad.lexClause_of_frontOf hb f15_06)
      (lexClause_of_z m0134) (GenQuad.lexClause_of_frontOf hb f13_04)
      (lexClause_of_z m0135) (GenQuad.lexClause_of_frontOf hb f13_06)
      (lexClause_of_z m0145) (GenQuad.lexClause_of_frontOf hb f14_06)
      (lexClause_of_z m0234) (GenQuad.lexClause_of_frontOf hb f13_54)
      (GenQuad.lexClause_of_frontOf hb f56_13) (lexClause_of_z m0235)
      (GenQuad.lexClause_of_frontOf hb f56_14) (lexClause_of_z m0245)
      (GenQuad.lexClause_of_frontOf hb f36_14) (lexClause_of_z m0345)
      cA cB
      (GenQuad.lexClause_of_frontOf hb f56_03) (lexClause_of_z m1235)
      (GenQuad.lexClause_of_frontOf hb f56_04) (lexClause_of_z m1245)
      (GenQuad.lexClause_of_frontOf hb f36_04) (lexClause_of_z m1345)
      (GenQuad.lexClause_of_frontOf hb f36_54) (lexClause_of_z m2345)

/-- Depth facts of the six vertices at `eb` and Lemma M: the bundle used by the 14 not-`M` clauses. -/
theorem neg6_depth {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hab : 0 < ⟪x 0 - x 1, x 2 - x 1⟫) (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0) :
    (¬ (max (z x (x 2 - x 1) 0) (z x (x 2 - x 1) 3) ≤ min (z x (x 2 - x 1) 1) (z x (x 2 - x 1) 5))) ∧
    (¬ (max (z x (x 2 - x 1) 0) (z x (x 2 - x 1) 4) ≤ min (z x (x 2 - x 1) 1) (z x (x 2 - x 1) 5))) ∧
    (¬ (max (z x (x 2 - x 1) 0) (z x (x 2 - x 1) 6) ≤ min (z x (x 2 - x 1) 1) (z x (x 2 - x 1) 5))) ∧
    (¬ (max (z x (x 2 - x 1) 0) (z x (x 2 - x 1) 4) ≤ min (z x (x 2 - x 1) 1) (z x (x 2 - x 1) 3))) ∧
    (¬ (max (z x (x 2 - x 1) 0) (z x (x 2 - x 1) 6) ≤ min (z x (x 2 - x 1) 1) (z x (x 2 - x 1) 3))) ∧
    (¬ (max (z x (x 2 - x 1) 0) (z x (x 2 - x 1) 6) ≤ min (z x (x 2 - x 1) 1) (z x (x 2 - x 1) 4))) ∧
    (¬ (max (z x (x 2 - x 1) 5) (z x (x 2 - x 1) 4) ≤ min (z x (x 2 - x 1) 1) (z x (x 2 - x 1) 3))) ∧
    (¬ (max (z x (x 2 - x 1) 1) (z x (x 2 - x 1) 3) ≤ min (z x (x 2 - x 1) 5) (z x (x 2 - x 1) 6))) ∧
    (¬ (max (z x (x 2 - x 1) 1) (z x (x 2 - x 1) 4) ≤ min (z x (x 2 - x 1) 5) (z x (x 2 - x 1) 6))) ∧
    (¬ (max (z x (x 2 - x 1) 1) (z x (x 2 - x 1) 4) ≤ min (z x (x 2 - x 1) 3) (z x (x 2 - x 1) 6))) ∧
    (¬ (max (z x (x 2 - x 1) 0) (z x (x 2 - x 1) 3) ≤ min (z x (x 2 - x 1) 5) (z x (x 2 - x 1) 6))) ∧
    (¬ (max (z x (x 2 - x 1) 0) (z x (x 2 - x 1) 4) ≤ min (z x (x 2 - x 1) 5) (z x (x 2 - x 1) 6))) ∧
    (¬ (max (z x (x 2 - x 1) 0) (z x (x 2 - x 1) 4) ≤ min (z x (x 2 - x 1) 3) (z x (x 2 - x 1) 6))) ∧
    (¬ (max (z x (x 2 - x 1) 5) (z x (x 2 - x 1) 4) ≤ min (z x (x 2 - x 1) 3) (z x (x 2 - x 1) 6))) := by
  have T := type24OfFac F
  have hB : 0 < ⟪x 2 - x 1, x 2 - x 1⟫ :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide))
  have hrep : ∀ v : Fin 7, x v - x 1 = oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) +
      oblX6 x v • (x 6 - x 1) := by
    intro v
    rw [sub_eq_iff_eq_add']
    refine (T.rep v).trans ?_
    abel
  have hz : ∀ v : Fin 7, z x (x 2 - x 1) v =
      oblX0 x v * ⟪x 0 - x 1, x 2 - x 1⟫ + oblX2 x v * ⟪x 2 - x 1, x 2 - x 1⟫ +
        oblX6 x v * ⟪x 2 - x 1, x 6 - x 1⟫ := by
    intro v
    rw [z, hrep v, inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_left, real_inner_comm (x 2 - x 1) (x 6 - x 1)]
  have hz0 : z x (x 2 - x 1) 0 = ⟪x 0 - x 1, x 2 - x 1⟫ := rfl
  have hz1 : z x (x 2 - x 1) 1 = 0 := by simp [z]
  have hz6 : z x (x 2 - x 1) 6 = ⟪x 2 - x 1, x 6 - x 1⟫ := by
    rw [z, real_inner_comm]
  obtain ⟨s, t, hs, ht, hst, hq⟩ := Minimality.T24.RimFromSigns.lemmaM_quad_decomp F
  have hM : z x (x 2 - x 1) 3 - z x (x 2 - x 1) 0 =
      s * (z x (x 2 - x 1) 4 - z x (x 2 - x 1) 0) + t * (z x (x 2 - x 1) 5 - z x (x 2 - x 1) 0) := by
    have e := congrArg (fun v => ⟪v, x 2 - x 1⟫) hq
    simp only [inner_add_left, inner_sub_left, real_inner_smul_left] at e
    simp only [z, inner_sub_left]
    linarith
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have ha4 : 0 < oblX0 x 4 := T.X0_pos (v := 4) (by decide)
  have hb3 : 0 < oblX2 x 3 := T.X2_pos (v := 3) (by decide)
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  set g := ⟪x 0 - x 1, x 2 - x 1⟫ with hg
  set h := ⟪x 2 - x 1, x 6 - x 1⟫ with hh
  set B := ⟪x 2 - x 1, x 2 - x 1⟫ with hBdef
  have p3 : h = 0 → 0 < z x (x 2 - x 1) 3 := by
    intro h0; rw [hz 3, h0]; nlinarith [mul_pos ha3 hab, mul_pos hb3 hB]
  have p4 : h = 0 → 0 < z x (x 2 - x 1) 4 := by
    intro h0; rw [hz 4, h0]; nlinarith [mul_pos ha4 hab, mul_pos hb4 hB]
  have K : z x (x 2 - x 1) 4 ≤ z x (x 2 - x 1) 3 → z x (x 2 - x 1) 5 ≤ z x (x 2 - x 1) 3 →
      g ≤ z x (x 2 - x 1) 3 := by
    intro k4 k5
    by_contra hlt
    push Not at hlt
    rw [hz0] at hM
    nlinarith [mul_nonneg hs.le (sub_nonneg.2 k4), mul_nonneg ht.le (sub_nonneg.2 k5),
      mul_pos (sub_pos.2 hst) (sub_pos.2 hlt)]
  rw [hz0] at hM
  simp only [max_le_iff, le_min_iff, hz0, hz1, hz6]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨⟨_, _⟩, h1, _⟩; linarith
  · rintro ⟨⟨_, _⟩, h1, _⟩; linarith
  · rintro ⟨⟨_, _⟩, h1, _⟩; linarith
  · rintro ⟨⟨_, _⟩, h1, _⟩; linarith
  · rintro ⟨⟨_, _⟩, h1, _⟩; linarith
  · rintro ⟨⟨_, _⟩, h1, _⟩; linarith
  · rintro ⟨⟨h5, h4⟩, ⟨h3a, h3b⟩⟩
    have := K (by linarith) (by linarith)
    nlinarith [mul_pos (sub_pos.2 hst) hab]
  · rintro ⟨⟨h1, h3⟩, h5, h6⟩
    have h0 : h = 0 := by linarith
    have := p3 h0; linarith
  · rintro ⟨⟨h1, h4⟩, h5, h6⟩
    have h0 : h = 0 := by linarith
    have := p4 h0; linarith
  · rintro ⟨⟨h1, h4⟩, h3, h6⟩
    have h0 : h = 0 := by linarith
    have := p4 h0; linarith
  · rintro ⟨⟨h0, h3⟩, h5, h6⟩; linarith
  · rintro ⟨⟨h0, h4⟩, h5, h6⟩; linarith
  · rintro ⟨⟨h0, h4⟩, h3, h6⟩; linarith
  · rintro ⟨⟨h5, h4⟩, h5', h4'⟩
    have := K h4 h5
    nlinarith [mul_pos (sub_pos.2 hst) hab, mul_nonneg hs.le (sub_nonneg.2 (h4'.trans hbc)),
      mul_nonneg ht.le (sub_nonneg.2 (h5'.trans hbc))]


/-- **E12-Neg6** with the 14 front facts as hypotheses (`FrontOf`); `nB = 0` allowed when `nC > 0`. -/
theorem e12_neg6_fo {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (hnb : F.f 3 (x 2) < F.f 3 (x 1) ∨ (F.f 3 (x 2) = F.f 3 (x 1) ∧ F.f 3 (x 1) < F.f 3 (x 6)))
    (h346 : F.f 8 (x 1) < F.f 8 (x 2))
    (hab : 0 < ⟪x 0 - x 1, x 2 - x 1⟫) (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0)
    (f15_03 : GenQuad.FrontOf (x 1) (x 5) (x 0) (x 3) (x 2 - x 1))
    (f15_04 : GenQuad.FrontOf (x 1) (x 5) (x 0) (x 4) (x 2 - x 1))
    (f15_06 : GenQuad.FrontOf (x 1) (x 5) (x 0) (x 6) (x 2 - x 1))
    (f13_04 : GenQuad.FrontOf (x 1) (x 3) (x 0) (x 4) (x 2 - x 1))
    (f13_06 : GenQuad.FrontOf (x 1) (x 3) (x 0) (x 6) (x 2 - x 1))
    (f14_06 : GenQuad.FrontOf (x 1) (x 4) (x 0) (x 6) (x 2 - x 1))
    (f13_54 : GenQuad.FrontOf (x 1) (x 3) (x 5) (x 4) (x 2 - x 1))
    (f56_13 : GenQuad.FrontOf (x 5) (x 6) (x 1) (x 3) (x 2 - x 1))
    (f56_14 : GenQuad.FrontOf (x 5) (x 6) (x 1) (x 4) (x 2 - x 1))
    (f36_14 : GenQuad.FrontOf (x 3) (x 6) (x 1) (x 4) (x 2 - x 1))
    (f56_03 : GenQuad.FrontOf (x 5) (x 6) (x 0) (x 3) (x 2 - x 1))
    (f56_04 : GenQuad.FrontOf (x 5) (x 6) (x 0) (x 4) (x 2 - x 1))
    (f36_04 : GenQuad.FrontOf (x 3) (x 6) (x 0) (x 4) (x 2 - x 1))
    (f36_54 : GenQuad.FrontOf (x 3) (x 6) (x 5) (x 4) (x 2 - x 1)) :
    LexAny F := by
  have T := type24OfFac F
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hdet : Split.det3 (x 2 - x 1) (-(x 0 - x 1) - (x 6 - x 1)) (x 0 - x 1) ≠ 0 := by
    have e : Split.det3 (x 2 - x 1) (-(x 0 - x 1) - (x 6 - x 1)) (x 0 - x 1) = -det24 x := by
      simp only [Split.det3, det24, vol3, PiLp.sub_apply, PiLp.neg_apply]; ring
    rw [e]; exact neg_ne_zero.2 T.det_ne
  have hN0 : ⟪F.N 0, x 2 - x 1⟫ = 0 := by
    rw [← F.hN, F.zero 0 2 (by decide), F.zero 0 1 (by decide), sub_self]
  have hN1 : ⟪F.N 1, x 2 - x 1⟫ < 0 := by
    rw [← F.hN, F.zero 1 1 (by decide), sub_zero]; exact F.neg 1 2 (by decide)
  have hN2 : 0 < ⟪F.N 2, x 2 - x 1⟫ := by
    rw [← F.hN, F.zero 2 2 (by decide)]; linarith [F.neg 2 1 (by decide)]
  have hN3 : ⟪F.N 3, x 2 - x 1⟫ ≤ 0 := by
    rw [← F.hN]; rcases hnb with h | ⟨h, _⟩ <;> linarith
  have hN5 : ⟪F.N 5, x 2 - x 1⟫ = 0 := by
    rw [← F.hN, F.zero 5 2 (by decide), F.zero 5 1 (by decide), sub_self]
  have hN6 : 0 < ⟪F.N 6, x 2 - x 1⟫ := by
    rw [← F.hN, F.zero 6 2 (by decide)]; linarith [F.neg 6 1 (by decide)]
  have hN7 : 0 < ⟪F.N 7, x 2 - x 1⟫ := by
    rw [← F.hN, F.zero 7 2 (by decide)]; linarith [F.neg 7 1 (by decide)]
  have hN8 : 0 < ⟪F.N 8, x 2 - x 1⟫ := by rw [← F.hN]; linarith
  have hN4 : ⟪F.N 4, x 2 - x 1⟫ < 0 := by
    have e := fac_eval F 4 4
    rw [F.zero 4 4 (by decide), F.zero 4 0 (by decide), F.zero 4 6 (by decide)] at e
    have h1 := F.neg 4 1 (by decide)
    have hω := T.eq4
    have hω4 := hC.2.1
    have key : (F.f 4 (x 2) - F.f 4 (x 1)) * oblX2 x 4 =
        F.f 4 (x 1) * (omega4 x * oblX2 x 4) := by
      linear_combination (-1 : ℝ) * e + F.f 4 (x 1) * hω
    rw [← F.hN]
    by_contra hge
    push Not at hge
    have h2 : 0 ≤ (F.f 4 (x 2) - F.f 4 (x 1)) * oblX2 x 4 := mul_nonneg hge hb4.le
    have h3 := mul_neg_of_neg_of_pos h1 (mul_pos hω4 hb4)
    linarith
  have hN0d : 0 < ⟪F.N 0, -(x 0 - x 1) - (x 6 - x 1)⟫ := by
    rw [inner_sub_right, inner_neg_right, ← F.hN, ← F.hN, F.zero 0 0 (by decide),
      F.zero 0 1 (by decide)]
    linarith [F.neg 0 6 (by decide)]
  have hN5d : 0 < ⟪F.N 5, -(x 0 - x 1) - (x 6 - x 1)⟫ := by
    rw [inner_sub_right, inner_neg_right, ← F.hN, ← F.hN, F.zero 5 6 (by decide),
      F.zero 5 1 (by decide)]
    linarith [F.neg 5 0 (by decide)]
  have hN3' : LexPos3 (-⟪F.N 3, x 2 - x 1⟫) (-⟪F.N 3, -(x 0 - x 1) - (x 6 - x 1)⟫)
      (-⟪F.N 3, x 0 - x 1⟫) := by
    rcases hnb with h | ⟨h, hnc⟩
    · exact Or.inl (by rw [← F.hN]; linarith)
    · refine Or.inr ⟨by rw [← F.hN, h]; ring, Or.inl ?_⟩
      rw [inner_sub_right, inner_neg_right, ← F.hN, ← F.hN, F.zero 3 0 (by decide)]
      linarith [F.neg 3 1 (by decide)]
  have hX : GenQuad.CrossOf (x 0) (x 3) (x 5) (x 4) := by
    obtain ⟨s, t, hs, ht, hst, hq⟩ := Minimality.T24.RimFromSigns.lemmaM_quad_decomp F
    have hst0 : 0 < s + t := by linarith
    refine ⟨1 - 1 / (s + t), t / (s + t), ?_, ?_, ?_, ?_, ?_⟩
    · have : 1 / (s + t) < 1 := (div_lt_one hst0).2 hst
      linarith
    · have : 0 < 1 / (s + t) := by positivity
      linarith
    · positivity
    · rw [div_lt_one hst0]; linarith
    · have hx3 : x 3 = x 0 + s • (x 4 - x 0) + t • (x 5 - x 0) := by
        calc x 3 = x 0 + (x 3 - x 0) := by abel
          _ = _ := by rw [hq]; abel
      ext i
      have hi := congrArg (fun v => v i) hx3
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at hi ⊢
      rw [hi]
      field_simp
      ring
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14⟩ := neg6_depth F hab hbc
  exact lexAny_neg6_leaf F hdet hN0 hN0d hN5 hN5d hN2 hN6 hN7 hN8 hN1 hN4 hN3' hX
    f15_03 f15_04 f15_06 f13_04 f13_06 f14_06 f13_54 f56_13 f56_14 f36_14 f56_03 f56_04 f36_04 f36_54
    d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14


/-- **Lemma E12-Neg6** (A19-REFEREE section 4, S6).  At the frame view `eb = x 2 - x 1` with tilt
`(-ea - ec, ea)`: if the facet `0345` faces down strictly (`nB < 0`), `346` faces up (`nu346b > 0`),
`b1356 > 0`, `b1456 > 0` and `G_ab > 0 >= G_bc`, then `LexAny`. -/
theorem e12_neg6 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (hnb : F.f 3 (x 2) < F.f 3 (x 1)) (h346 : F.f 8 (x 1) < F.f 8 (x 2))
    (h1356 : 0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3)
    (h1456 : 0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4)
    (hab : 0 < ⟪x 0 - x 1, x 2 - x 1⟫) (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0) :
    LexAny F := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14⟩ :=
    neg6_fronts F hC hnb h346 h1356 h1456
  exact e12_neg6_fo F hC (Or.inl hnb) h346 hab hbc f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14

end Minimality.T24.A19
