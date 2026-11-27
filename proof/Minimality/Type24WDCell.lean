module

public import Minimality.Type24FamSlope

/-!
# `w_D` cell (`rD = ![0, 1, 2, 3, 6]`, vertices `4, 5` hidden, Carbon A84 Section 1)

* `FR1` (`rD_cyc`, `wd_seven_facets`, `wd_cellAt_iff`, `hidden_in_rD_of_cell`):
  `S0xCycUD` for `rD = ![0, 1, 2, 3, 6]` and `(U_D, D_D) = ({1, 5, 7}, {0, 2, 3, 4, 6, 8})`,
  automatic 7-of-9 facet reduction at `wD x beta gamma = capView x (-1) (-beta) gamma`
  under `CbarIn x`, `beta > 0`, `gamma > 0`, `omega4 x * beta + gamma < 1`, and
  `HiddenInTriangles` for vertices `4` and `5`.
* `FR2` (`wd_edgePlaneAny`, `WDCertAt`, `holeLeaf_not_wd`, `hole24_not_wd`,
  `wd_edgePlaneAny_twin`, `holeLeaf_not_wd_twin`, `hole24_not_wd_twin`,
  `TwoConeResidue'''`, `hole24_twoConeResidue'''`):
  interior `w_D` leaf, `π_24` twin, hole facts, and extended residue.
* `FR3` (`wd_det3_frame`, `wd_det3_rim`):
  exact `det24 x * ((1 - gamma) * u_b - beta * (u_a + u_c))` determinant formula on `rD`,
  edge `a = 4` (`6 → 0`, `d = x 0 - x 6`).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.M4
open Minimality.T24.HC Minimality.T24.SF Minimality.T24.DeepC

namespace Minimality.T24.TwoCone

/-! ## FR1: Cell `(U_D, D_D)`, 7-facet reduction, and hidden vertices `4, 5` -/

/-- Rim `rD = ![0, 1, 2, 3, 6]` (reverse of `0.6.3.2.1`). -/
def rD : ZMod 5 → Fin 7 := ![0, 1, 2, 3, 6]

theorem rD_inj : Function.Injective rD := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)

/-- Up facets `{1, 5, 7}` (`016, 126, 236 > 0`) of the `w_D` cell. -/
def U_D : Finset (Fin 9) := {1, 5, 7}

/-- Down facets `{0, 2, 3, 4, 6, 8}` (`012, 025, 0345, 046, 235, 346 < 0`) of the `w_D` cell. -/
def D_D : Finset (Fin 9) := {0, 2, 3, 4, 6, 8}

theorem rD_cyc : S0xCycUD s0x_S24 rD U_D D_D := by
  decide

/-- View `w_D(x, β, γ) := capView x (-1) (-β) γ`. -/
noncomputable def wD (x : Fin 7 → ℝ³) (beta gamma : ℝ) : ℝ³ :=
  capView x (-1) (-beta) gamma

/-- **FR1 (7-of-9 facet reduction):** under `CbarIn x`, `β > 0`, `γ > 0`, and
`ω_4(x) * β + γ < 1`, all seven facets `{0, 1, 2, 3, 4, 5, 7}` automatically have their
`(U_D, D_D)` signs at `wD x β γ`. -/
theorem wd_seven_facets {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    {beta gamma : ℝ} (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hroof : omega4 x * beta + gamma < 1) :
    (∀ t ∈ ({1, 5, 7} : Finset (Fin 9)), 0 < ⟪F.N t, wD x beta gamma⟫) ∧
    (∀ t ∈ ({0, 2, 3, 4} : Finset (Fin 9)), ⟪F.N t, wD x beta gamma⟫ < 0) := by
  have T := type24OfFac F
  have h1 : 0 < ⟪F.N 1, wD x beta gamma⟫ := by
    rw [wD, inner_cap, F.zero 1 1 (by decide), F.zero 1 0 (by decide), F.zero 1 6 (by decide)]
    have hf := F.neg 1 2 (by decide)
    nlinarith
  have h5 : 0 < ⟪F.N 5, wD x beta gamma⟫ := by
    rw [wD, inner_cap, F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)]
    have hf := F.neg 5 0 (by decide)
    nlinarith
  have h7 : 0 < ⟪F.N 7, wD x beta gamma⟫ := by
    rw [wD, inner_cap, F.zero 7 2 (by decide), F.zero 7 6 (by decide)]
    have e3 := fac_eval F 7 3
    rw [F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at e3
    have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
    have h3eq := eq3 F
    have hf01 : F.f 7 (x 0) - F.f 7 (x 1) = omega3 x * F.f 7 (x 1) := by
      have hmul : oblX0 x 3 * (F.f 7 (x 0) - F.f 7 (x 1)) =
          oblX0 x 3 * (omega3 x * F.f 7 (x 1)) := by
        linear_combination -e3 + F.f 7 (x 1) * h3eq
      exact mul_left_cancel₀ ha3.ne' hmul
    have hprod : 1 < omega3 x * omega4 x :=
      Minimality.omega_prod_gt_one hC.1 hC.2.1 hC.2.2.1 hC.2.2.2
    have hw4 : 0 < omega4 x := hC.2.1
    have hbw : beta < omega3 x := by
      have h1' : omega4 x * beta < 1 := by linarith
      have h2' : beta < 1 / omega4 x := (lt_div_iff₀ hw4).mpr (by linarith)
      have h3' : 1 / omega4 x < omega3 x := (div_lt_iff₀ hw4).mpr hprod
      linarith
    have hf1 : F.f 7 (x 1) < 0 := F.neg 7 1 (by decide)
    rw [hf01]
    have heval : -1 * (omega3 x * F.f 7 (x 1)) + -beta * (0 - F.f 7 (x 1)) +
        gamma * (0 - F.f 7 (x 1)) = -(omega3 x - beta + gamma) * F.f 7 (x 1) := by ring
    rw [heval]
    exact mul_pos_of_neg_of_neg (by linarith) hf1
  have h0 : ⟪F.N 0, wD x beta gamma⟫ < 0 := by
    rw [wD, inner_cap, F.zero 0 1 (by decide), F.zero 0 0 (by decide), F.zero 0 2 (by decide)]
    have hf := F.neg 0 6 (by decide)
    nlinarith
  have h2 : ⟪F.N 2, wD x beta gamma⟫ < 0 := by
    rw [wD, inner_cap, F.zero 2 0 (by decide), F.zero 2 2 (by decide)]
    have e5 := fac_eval F 2 5
    rw [F.zero 2 5 (by decide), F.zero 2 0 (by decide), F.zero 2 2 (by decide)] at e5
    have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
    have h5eq := eq5 F
    have hf61 : F.f 2 (x 6) - F.f 2 (x 1) = omega5 x * F.f 2 (x 1) := by
      have hmul : oblX6 x 5 * (F.f 2 (x 6) - F.f 2 (x 1)) =
          oblX6 x 5 * (omega5 x * F.f 2 (x 1)) := by
        linear_combination -e5 + F.f 2 (x 1) * h5eq
      exact mul_left_cancel₀ hc5.ne' hmul
    have hf1 : F.f 2 (x 1) < 0 := F.neg 2 1 (by decide)
    have hw5 : 0 < omega5 x := hC.2.2.1
    rw [hf61]
    have heval : -1 * (0 - F.f 2 (x 1)) + -beta * (0 - F.f 2 (x 1)) +
        gamma * (omega5 x * F.f 2 (x 1)) = (1 + beta + omega5 x * gamma) * F.f 2 (x 1) := by ring
    rw [heval]
    have hcoeff : 0 < 1 + beta + omega5 x * gamma := by nlinarith
    exact mul_neg_of_pos_of_neg hcoeff hf1
  have h3 : ⟪F.N 3, wD x beta gamma⟫ < 0 := by
    have e4 := fac_eval F 3 4
    rw [F.zero 3 4 (by decide), F.zero 3 0 (by decide)] at e4
    have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
    have hc4 : 0 < oblX6 x 4 := T.X6_pos (v := 4) (by decide)
    have h4eq := eq4 F
    have hmul : oblX2 x 4 * ⟪F.N 3, wD x beta gamma⟫ =
        oblX2 x 4 * (1 - omega4 x * beta - gamma) * F.f 3 (x 1) +
        (oblX2 x 4 * gamma + oblX6 x 4 * beta) * F.f 3 (x 6) := by
      rw [wD, inner_cap, F.zero 3 0 (by decide)]
      linear_combination beta * e4 - beta * F.f 3 (x 1) * h4eq
    have hf1 : F.f 3 (x 1) < 0 := F.neg 3 1 (by decide)
    have hf6 : F.f 3 (x 6) < 0 := F.neg 3 6 (by decide)
    have ht1 : oblX2 x 4 * (1 - omega4 x * beta - gamma) * F.f 3 (x 1) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos hb4 (by linarith)) hf1
    have ht2 : (oblX2 x 4 * gamma + oblX6 x 4 * beta) * F.f 3 (x 6) < 0 :=
      mul_neg_of_pos_of_neg (by nlinarith) hf6
    have hprod_neg : oblX2 x 4 * ⟪F.N 3, wD x beta gamma⟫ < 0 := by linarith
    exact (mul_neg_iff.mp hprod_neg).elim (fun ⟨_, h⟩ => h) (fun ⟨h, _⟩ => absurd hb4 (not_lt.mpr h.le))
  have h4 : ⟪F.N 4, wD x beta gamma⟫ < 0 := by
    rw [wD, inner_cap, F.zero 4 0 (by decide), F.zero 4 6 (by decide)]
    have e4 := fac_eval F 4 4
    rw [F.zero 4 4 (by decide), F.zero 4 0 (by decide), F.zero 4 6 (by decide)] at e4
    have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
    have h4eq := eq4 F
    have hf21 : F.f 4 (x 2) - F.f 4 (x 1) = omega4 x * F.f 4 (x 1) := by
      have hmul : oblX2 x 4 * (F.f 4 (x 2) - F.f 4 (x 1)) =
          oblX2 x 4 * (omega4 x * F.f 4 (x 1)) := by
        linear_combination -e4 + F.f 4 (x 1) * h4eq
      exact mul_left_cancel₀ hb4.ne' hmul
    have hf1 : F.f 4 (x 1) < 0 := F.neg 4 1 (by decide)
    rw [hf21]
    have heval : -1 * (0 - F.f 4 (x 1)) + -beta * (omega4 x * F.f 4 (x 1)) +
        gamma * (0 - F.f 4 (x 1)) = (1 - omega4 x * beta - gamma) * F.f 4 (x 1) := by ring
    rw [heval]
    exact mul_neg_of_pos_of_neg (by linarith) hf1
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · fin_cases t <;> simp at ht ⊢
    · exact h1
    · exact h5
    · exact h7
  · fin_cases t <;> simp at ht ⊢
    · exact h0
    · exact h2
    · exact h3
    · exact h4

/-- **FR1:** Under `CbarIn x`, `β > 0`, `γ > 0`, `ω_4(x) * β + γ < 1`,
`CellAt F U_D D_D (wD x β γ)` holds iff facets `6` and `8` are strictly negative. -/
theorem wd_cellAt_iff {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    {beta gamma : ℝ} (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hroof : omega4 x * beta + gamma < 1) :
    CellAt F U_D D_D (wD x beta gamma) ↔
      ⟪F.N 6, wD x beta gamma⟫ < 0 ∧ ⟪F.N 8, wD x beta gamma⟫ < 0 := by
  have ⟨hU7, hD7⟩ := wd_seven_facets F hC hbeta hgamma hroof
  constructor
  · intro ⟨_, hdn⟩
    exact ⟨hdn 6 (by decide), hdn 8 (by decide)⟩
  · intro ⟨h6, h8⟩
    refine ⟨fun t ht => hU7 t ?_, fun t ht => ?_⟩
    · fin_cases t <;> simp [U_D] at ht ⊢
    · fin_cases t <;> simp [D_D] at ht
      · exact hD7 0 (by decide)
      · exact hD7 2 (by decide)
      · exact hD7 3 (by decide)
      · exact hD7 4 (by decide)
      · exact h6
      · exact h8

/-- Shared 3-facet hidden-vertex helper: if vertex `v` is coplanar with `(p0, p1)` on `t0`
(off `p2`), `(p1, p2)` on `t1` (off `p0`), and `(p2, p0)` on `t2` (off `p1`), and all three
facets satisfy `⟪F.N t, w⟫ < 0`, then `x v` lies strictly inside `(x p0, x p1, x p2)` or
`(x p0, x p2, x p1)` in `w^⊥`. -/
theorem hidden_of_three_facets {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {w : ℝ³}
    (v p0 p1 p2 : Fin 7) (t0 t1 t2 : Fin 9)
    (hv0 : v ∈ s0x_S24 t0) (hp00 : p0 ∈ s0x_S24 t0) (hp10 : p1 ∈ s0x_S24 t0) (hp20 : p2 ∉ s0x_S24 t0)
    (hv1 : v ∈ s0x_S24 t1) (hp11 : p1 ∈ s0x_S24 t1) (hp21 : p2 ∈ s0x_S24 t1) (hp01 : p0 ∉ s0x_S24 t1)
    (hv2 : v ∈ s0x_S24 t2) (hp22 : p2 ∈ s0x_S24 t2) (hp02 : p0 ∈ s0x_S24 t2) (hp12 : p1 ∉ s0x_S24 t2)
    (ht0 : ⟪F.N t0, w⟫ < 0) (ht1 : ⟪F.N t1, w⟫ < 0) (ht2 : ⟪F.N t2, w⟫ < 0) :
    ∃ p ∈ ({x p0, x p1, x p2} : Finset ℝ³),
      ∃ q ∈ ({x p0, x p1, x p2} : Finset ℝ³),
      ∃ r ∈ ({x p0, x p1, x p2} : Finset ℝ³),
      0 < Split.det3 (q - p) (r - p) w ∧ 0 < Split.det3 (q - p) (x v - p) w ∧
      0 < Split.det3 (r - q) (x v - q) w ∧ 0 < Split.det3 (p - r) (x v - r) w := by
  let e0 := x p0 - x v
  let e1 := x p1 - x v
  let e2 := x p2 - x v
  have hf_lt : ∀ (t : Fin 9) (q : Fin 7), v ∈ s0x_S24 t → q ∉ s0x_S24 t →
      ⟪F.N t, x q - x v⟫ < 0 := by
    intro t q hvt hq
    rw [F.inner_sub t q v, F.zero t v hvt, sub_zero]; exact F.neg t q hq
  have h0t0 : ⟪F.N t0, e0⟫ = 0 := by rw [F.inner_sub t0 p0 v, F.zero t0 p0 hp00, F.zero t0 v hv0, sub_self]
  have h1t0 : ⟪F.N t0, e1⟫ = 0 := by rw [F.inner_sub t0 p1 v, F.zero t0 p1 hp10, F.zero t0 v hv0, sub_self]
  have h1t1 : ⟪F.N t1, e1⟫ = 0 := by rw [F.inner_sub t1 p1 v, F.zero t1 p1 hp11, F.zero t1 v hv1, sub_self]
  have h2t1 : ⟪F.N t1, e2⟫ = 0 := by rw [F.inner_sub t1 p2 v, F.zero t1 p2 hp21, F.zero t1 v hv1, sub_self]
  have h2t2 : ⟪F.N t2, e2⟫ = 0 := by rw [F.inner_sub t2 p2 v, F.zero t2 p2 hp22, F.zero t2 v hv2, sub_self]
  have h0t2 : ⟪F.N t2, e0⟫ = 0 := by rw [F.inner_sub t2 p0 v, F.zero t2 p0 hp02, F.zero t2 v hv2, sub_self]
  have hne : Split.det3 e0 e1 e2 ≠ 0 := by
    have hcr : cross e0 e1 ≠ 0 := by
      intro h0
      have he0_ne : e0 ≠ 0 := by
        intro he0
        have hlt := hf_lt t1 p0 hv1 hp01
        change ⟪F.N t1, e0⟫ < 0 at hlt
        rw [he0, inner_zero_right] at hlt
        exact lt_irrefl 0 hlt
      have he1_span : ∃ c : ℝ, e1 = c • e0 := by
        have hid : ⟪e0, e0⟫ • e1 - ⟪e0, e1⟫ • e0 = 0 := by
          ext i; fin_cases i <;> dsimp
          · have hc1 := congrArg (fun u : ℝ³ => u 1) h0
            have hc2 := congrArg (fun u : ℝ³ => u 2) h0
            simp only [Split.cross_1, Split.cross_2, PiLp.zero_apply] at hc1 hc2
            simp only [Split.inner3]
            linear_combination -e0 1 * hc2 + e0 2 * hc1
          · have hc0 := congrArg (fun u : ℝ³ => u 0) h0
            have hc2 := congrArg (fun u : ℝ³ => u 2) h0
            simp only [Split.cross_0, Split.cross_2, PiLp.zero_apply] at hc0 hc2
            simp only [Split.inner3]
            linear_combination -e0 2 * hc0 + e0 0 * hc2
          · have hc0 := congrArg (fun u : ℝ³ => u 0) h0
            have hc1 := congrArg (fun u : ℝ³ => u 1) h0
            simp only [Split.cross_0, Split.cross_1, PiLp.zero_apply] at hc0 hc1
            simp only [Split.inner3]
            linear_combination -e0 0 * hc1 + e0 1 * hc0
        have hnn : ⟪e0, e0⟫ ≠ 0 := inner_self_ne_zero.mpr he0_ne
        refine ⟨⟪e0, e1⟫ / ⟪e0, e0⟫, ?_⟩
        have h1 : ⟪e0, e0⟫ • e1 = ⟪e0, e1⟫ • e0 := sub_eq_zero.mp hid
        calc e1 = (1 / ⟪e0, e0⟫) • (⟪e0, e0⟫ • e1) := by rw [smul_smul, one_div_mul_cancel hnn, one_smul]
          _ = (1 / ⟪e0, e0⟫) • (⟪e0, e1⟫ • e0) := by rw [h1]
          _ = (⟪e0, e1⟫ / ⟪e0, e0⟫) • e0 := by rw [smul_smul]; ring_nf
      obtain ⟨c, hc⟩ := he1_span
      have hlt2 := hf_lt t2 p1 hv2 hp12
      change ⟪F.N t2, e1⟫ < 0 at hlt2
      rw [hc, real_inner_smul_right, h0t2, mul_zero] at hlt2
      exact lt_irrefl 0 hlt2
    intro h0
    have horth : ∀ r : ℝ³, ⟪r, e0⟫ = 0 → ⟪r, e1⟫ = 0 → ⟪r, cross e0 e1⟫ = 0 → r = 0 := by
      intro r hr0 hr1 hrc
      have hid : ⟪cross e0 e1, cross e0 e1⟫ * ⟪r, r⟫ =
          ⟪r, e0⟫ * Split.det3 e1 (cross e0 e1) r - ⟪r, e1⟫ * Split.det3 e0 (cross e0 e1) r +
          ⟪r, cross e0 e1⟫ * Split.det3 e0 e1 r := by
        have hbin : Split.det3 e0 e1 (cross e0 e1) = ⟪cross e0 e1, cross e0 e1⟫ := by
          simp only [Split.det3, Split.inner3, Split.cross_0, Split.cross_1, Split.cross_2]
        rw [← hbin]
        simp only [Split.det3, Split.inner3]; ring
      rw [hr0, hr1, hrc, zero_mul, zero_mul, zero_mul, sub_zero, add_zero] at hid
      have hcc : ⟪cross e0 e1, cross e0 e1⟫ ≠ 0 := inner_self_ne_zero.mpr hcr
      exact inner_self_eq_zero.mp ((mul_eq_zero.mp hid).resolve_left hcc)
    have hNt0_ne : ⟪F.N t0, cross e0 e1⟫ ≠ 0 := by
      intro h0'
      have hN0 := horth (F.N t0) h0t0 h1t0 h0'
      have hlt := hf_lt t0 p2 hv0 hp20
      change ⟪F.N t0, e2⟫ < 0 at hlt
      rw [hN0, inner_zero_left] at hlt
      exact lt_irrefl 0 hlt
    have hprop0 : ⟪F.N t0, cross e0 e1⟫ • cross e0 e1 - ⟪cross e0 e1, cross e0 e1⟫ • F.N t0 = 0 :=
      horth _
        (by rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left, h0t0, mul_zero,
          show ⟪cross e0 e1, e0⟫ = 0 by simp only [Split.inner3, Split.cross_0, Split.cross_1, Split.cross_2]; ring,
          mul_zero, sub_self])
        (by rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left, h1t0, mul_zero,
          show ⟪cross e0 e1, e1⟫ = 0 by simp only [Split.inner3, Split.cross_0, Split.cross_1, Split.cross_2]; ring,
          mul_zero, sub_self])
        (by rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left]; ring)
    have hdot := congrArg (fun u => ⟪u, e2⟫) hprop0
    rw [inner_zero_left, inner_sub_left, real_inner_smul_left, real_inner_smul_left] at hdot
    have hce2 : ⟪cross e0 e1, e2⟫ = Split.det3 e0 e1 e2 := by
      simp only [Split.inner3, Split.det3, Split.cross_0, Split.cross_1, Split.cross_2]
    rw [hce2, h0, mul_zero, zero_sub, neg_eq_zero] at hdot
    have hcc : ⟪cross e0 e1, cross e0 e1⟫ ≠ 0 := inner_self_ne_zero.mpr hcr
    have hN2 := (mul_eq_zero.mp hdot).resolve_left hcc
    have hlt := hf_lt t0 p2 hv0 hp20
    change ⟪F.N t0, e2⟫ < 0 at hlt
    exact hlt.ne hN2
  have hcross_eq : ∀ (t : Fin 9) (u1 u2 : ℝ³) (hu : ⟪F.N t, u1⟫ = 0) (hv : ⟪F.N t, u2⟫ = 0)
      (q0 : Fin 7) (hq0 : ⟪F.N t, x q0 - x v⟫ < 0)
      (hdq : Split.det3 u1 u2 (x q0 - x v) ≠ 0),
      Split.det3 u1 u2 w * ⟪F.N t, x q0 - x v⟫ = Split.det3 u1 u2 (x q0 - x v) * ⟪F.N t, w⟫ := by
    intro t u1 u2 hu hv q0 hq0 hdq
    have hcr : cross u1 u2 ≠ 0 := by
      intro hc0
      apply hdq
      rw [Split.det3_eq_minimality, det3, hc0, inner_zero_left]
    have horth : ∀ r : ℝ³, ⟪r, u1⟫ = 0 → ⟪r, u2⟫ = 0 → ⟪r, cross u1 u2⟫ = 0 → r = 0 := by
      intro r hru hrv hrc
      have hid : ⟪cross u1 u2, cross u1 u2⟫ * ⟪r, r⟫ =
          ⟪r, u1⟫ * Split.det3 u2 (cross u1 u2) r - ⟪r, u2⟫ * Split.det3 u1 (cross u1 u2) r +
          ⟪r, cross u1 u2⟫ * Split.det3 u1 u2 r := by
        have hbin : Split.det3 u1 u2 (cross u1 u2) = ⟪cross u1 u2, cross u1 u2⟫ := by
          simp only [Split.det3, Split.inner3, Split.cross_0, Split.cross_1, Split.cross_2]
        rw [← hbin]
        simp only [Split.det3, Split.inner3]; ring
      rw [hru, hrv, hrc, zero_mul, zero_mul, zero_mul, sub_zero, add_zero] at hid
      have hcc : ⟪cross u1 u2, cross u1 u2⟫ ≠ 0 := inner_self_ne_zero.mpr hcr
      exact inner_self_eq_zero.mp ((mul_eq_zero.mp hid).resolve_left hcc)
    have hprop : ⟪F.N t, cross u1 u2⟫ • cross u1 u2 - ⟪cross u1 u2, cross u1 u2⟫ • F.N t = 0 :=
      horth _
        (by rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left, hu, mul_zero,
          show ⟪cross u1 u2, u1⟫ = 0 by simp only [Split.inner3, Split.cross_0, Split.cross_1, Split.cross_2]; ring,
          mul_zero, sub_self])
        (by rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left, hv, mul_zero,
          show ⟪cross u1 u2, u2⟫ = 0 by simp only [Split.inner3, Split.cross_0, Split.cross_1, Split.cross_2]; ring,
          mul_zero, sub_self])
        (by rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left]; ring)
    have h1 := congrArg (fun r => ⟪r, x q0 - x v⟫) hprop
    have h2 := congrArg (fun r => ⟪r, w⟫) hprop
    rw [inner_zero_left, inner_sub_left, real_inner_smul_left, real_inner_smul_left] at h1 h2
    have hd1 : ⟪cross u1 u2, x q0 - x v⟫ = Split.det3 u1 u2 (x q0 - x v) := by
      simp only [Split.inner3, Split.det3, Split.cross_0, Split.cross_1, Split.cross_2]
    have hd2 : ⟪cross u1 u2, w⟫ = Split.det3 u1 u2 w := by
      simp only [Split.inner3, Split.det3, Split.cross_0, Split.cross_1, Split.cross_2]
    rw [hd1] at h1; rw [hd2] at h2
    have hcc : ⟪cross u1 u2, cross u1 u2⟫ ≠ 0 := inner_self_ne_zero.mpr hcr
    have h01 : ⟪F.N t, cross u1 u2⟫ * Split.det3 u1 u2 (x q0 - x v) =
        ⟪cross u1 u2, cross u1 u2⟫ * ⟪F.N t, x q0 - x v⟫ := sub_eq_zero.mp h1
    have h02 : ⟪F.N t, cross u1 u2⟫ * Split.det3 u1 u2 w =
        ⟪cross u1 u2, cross u1 u2⟫ * ⟪F.N t, w⟫ := sub_eq_zero.mp h2
    have hmul : ⟪cross u1 u2, cross u1 u2⟫ * (Split.det3 u1 u2 w * ⟪F.N t, x q0 - x v⟫) =
        ⟪cross u1 u2, cross u1 u2⟫ * (Split.det3 u1 u2 (x q0 - x v) * ⟪F.N t, w⟫) := by
      calc ⟪cross u1 u2, cross u1 u2⟫ * (Split.det3 u1 u2 w * ⟪F.N t, x q0 - x v⟫)
          = Split.det3 u1 u2 w * (⟪cross u1 u2, cross u1 u2⟫ * ⟪F.N t, x q0 - x v⟫) := by ring
        _ = Split.det3 u1 u2 w * (⟪F.N t, cross u1 u2⟫ * Split.det3 u1 u2 (x q0 - x v)) := by rw [← h01]
        _ = (⟪F.N t, cross u1 u2⟫ * Split.det3 u1 u2 w) * Split.det3 u1 u2 (x q0 - x v) := by ring
        _ = (⟪cross u1 u2, cross u1 u2⟫ * ⟪F.N t, w⟫) * Split.det3 u1 u2 (x q0 - x v) := by rw [h02]
        _ = ⟪cross u1 u2, cross u1 u2⟫ * (Split.det3 u1 u2 (x q0 - x v) * ⟪F.N t, w⟫) := by ring
    exact mul_left_cancel₀ hcc hmul
  have hd01 : Split.det3 e0 e1 w * ⟪F.N t0, e2⟫ = Split.det3 e0 e1 e2 * ⟪F.N t0, w⟫ :=
    hcross_eq t0 e0 e1 h0t0 h1t0 p2 (hf_lt t0 p2 hv0 hp20) hne
  have hne12 : Split.det3 e1 e2 e0 ≠ 0 := by
    rwa [show Split.det3 e1 e2 e0 = Split.det3 e0 e1 e2 by simp only [Split.det3]; ring]
  have hd12 : Split.det3 e1 e2 w * ⟪F.N t1, e0⟫ = Split.det3 e1 e2 e0 * ⟪F.N t1, w⟫ :=
    hcross_eq t1 e1 e2 h1t1 h2t1 p0 (hf_lt t1 p0 hv1 hp01) hne12
  have hne20 : Split.det3 e2 e0 e1 ≠ 0 := by
    rwa [show Split.det3 e2 e0 e1 = Split.det3 e0 e1 e2 by simp only [Split.det3]; ring]
  have hd20 : Split.det3 e2 e0 w * ⟪F.N t2, e1⟫ = Split.det3 e2 e0 e1 * ⟪F.N t2, w⟫ :=
    hcross_eq t2 e2 e0 h2t2 h0t2 p1 (hf_lt t2 p1 hv2 hp12) hne20
  have heq12 : Split.det3 e1 e2 e0 = Split.det3 e0 e1 e2 := by
    simp only [Split.det3]; ring
  have heq20 : Split.det3 e2 e0 e1 = Split.det3 e0 e1 e2 := by
    simp only [Split.det3]; ring
  have hlt_t0 : ⟪F.N t0, e2⟫ < 0 := hf_lt t0 p2 hv0 hp20
  have hlt_t1 : ⟪F.N t1, e0⟫ < 0 := hf_lt t1 p0 hv1 hp01
  have hlt_t2 : ⟪F.N t2, e1⟫ < 0 := hf_lt t2 p1 hv2 hp12
  have hsum : Split.det3 e0 e1 w + Split.det3 e1 e2 w + Split.det3 e2 e0 w =
      Split.det3 (x p1 - x p0) (x p2 - x p0) w := by
    dsimp only [e0, e1, e2]
    simp only [Split.det3, PiLp.sub_apply]; ring
  have hp0m : x p0 ∈ ({x p0, x p1, x p2} : Finset ℝ³) := by simp
  have hp1m : x p1 ∈ ({x p0, x p1, x p2} : Finset ℝ³) := by simp
  have hp2m : x p2 ∈ ({x p0, x p1, x p2} : Finset ℝ³) := by simp
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have h01 : Split.det3 e0 e1 w < 0 := by nlinarith
    have h12 : Split.det3 e1 e2 w < 0 := by rw [heq12] at hd12; nlinarith
    have h20 : Split.det3 e2 e0 w < 0 := by rw [heq20] at hd20; nlinarith
    refine ⟨x p0, hp0m, x p2, hp2m, x p1, hp1m, ?_, ?_, ?_, ?_⟩
    · have : Split.det3 (x p2 - x p0) (x p1 - x p0) w = -(Split.det3 (x p1 - x p0) (x p2 - x p0) w) := by
        simp only [Split.det3, PiLp.sub_apply]; ring
      linarith
    · have : Split.det3 (x p2 - x p0) (x v - x p0) w = -(Split.det3 e2 e0 w) := by
        dsimp only [e0, e2]; simp only [Split.det3, PiLp.sub_apply]; ring
      linarith
    · have : Split.det3 (x p1 - x p2) (x v - x p2) w = -(Split.det3 e1 e2 w) := by
        dsimp only [e1, e2]; simp only [Split.det3, PiLp.sub_apply]; ring
      linarith
    · have : Split.det3 (x p0 - x p1) (x v - x p1) w = -(Split.det3 e0 e1 w) := by
        dsimp only [e0, e1]; simp only [Split.det3, PiLp.sub_apply]; ring
      linarith
  · have h01 : 0 < Split.det3 e0 e1 w := by nlinarith
    have h12 : 0 < Split.det3 e1 e2 w := by rw [heq12] at hd12; nlinarith
    have h20 : 0 < Split.det3 e2 e0 w := by rw [heq20] at hd20; nlinarith
    refine ⟨x p0, hp0m, x p1, hp1m, x p2, hp2m, by linarith, ?_, ?_, ?_⟩
    · have : Split.det3 (x p1 - x p0) (x v - x p0) w = Split.det3 e0 e1 w := by
        dsimp only [e0, e1]; simp only [Split.det3, PiLp.sub_apply]; ring
      linarith
    · have : Split.det3 (x p2 - x p1) (x v - x p1) w = Split.det3 e1 e2 w := by
        dsimp only [e1, e2]; simp only [Split.det3, PiLp.sub_apply]; ring
      linarith
    · have : Split.det3 (x p0 - x p2) (x v - x p2) w = Split.det3 e2 e0 w := by
        dsimp only [e0, e2]; simp only [Split.det3, PiLp.sub_apply]; ring
      linarith

/-- **FR1:** On any `CellAt F U_D D_D w`, both hidden vertices `4` and `5` satisfy
`Split.HiddenInTriangles x w rD`. -/
theorem hidden_in_rD_of_cell {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {w : ℝ³}
    (hcell : CellAt F U_D D_D w) :
    Split.HiddenInTriangles x w rD := by
  intro m hm
  have hm45 : m = 4 ∨ m = 5 := by
    fin_cases m
    · exact absurd rfl (hm 0)
    · exact absurd rfl (hm 1)
    · exact absurd rfl (hm 2)
    · exact absurd rfl (hm 3)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd rfl (hm 4)
  rcases hm45 with rfl | rfl
  · obtain ⟨p, hp, q, hq, r, hr, h1, h2, h3, h4⟩ :=
      hidden_of_three_facets F 4 0 3 6 3 8 4
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (hcell.2 3 (by decide)) (hcell.2 8 (by decide)) (hcell.2 4 (by decide))
    have hsub : ∀ y ∈ ({x 0, x 3, x 6} : Finset ℝ³), y ∈ univ.image x := fun y hy => by
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl | rfl <;> exact mem_image_of_mem x (mem_univ _)
    exact ⟨p, hsub p hp, q, hsub q hq, r, hsub r hr, h1, h2, h3, h4⟩
  · obtain ⟨p, hp, q, hq, r, hr, h1, h2, h3, h4⟩ :=
      hidden_of_three_facets F 5 0 3 2 3 6 2
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (hcell.2 3 (by decide)) (hcell.2 6 (by decide)) (hcell.2 2 (by decide))
    have hsub : ∀ y ∈ ({x 0, x 3, x 2} : Finset ℝ³), y ∈ univ.image x := fun y hy => by
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl | rfl <;> exact mem_image_of_mem x (mem_univ _)
    exact ⟨p, hsub p hp, q, hsub q hq, r, hsub r hr, h1, h2, h3, h4⟩

/-! ## FR2: `w_D` leaf, `π_24` twin, hole facts, and `TwoConeResidue'''` -/

/-- Shared interior line-separation helper for any valid `(r, U, D)` cell. -/
theorem cell_lineSep_edgePlaneAny {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {w : ℝ³}
    {k : ℕ} [NeZero k] (hk : 3 ≤ k) (r : ZMod k → Fin 7) (hr : Function.Injective r)
    {U D : Finset (Fin 9)} (hcyc : S0xCycUD s0x_S24 r U D) (hcell : CellAt F U D w)
    (hhid : Split.HiddenInTriangles x w r)
    (a : ZMod k)
    (hD0 : ⟪x (r (a + 1)) - x (r a), w⟫ ≠ 0)
    (hc_ne0 : ∀ i : ZMod k, i ≠ a →
      Split.det3 (x (r (i + 1)) - x (r i)) (x (r (a + 1)) - x (r a)) w ≠ 0)
    (sh : ℝ) (hsh : sh = 1 ∨ sh = -1) (α' μ' : ℝ)
    (hBlue0 : ∀ i j : ZMod k, i ≠ a → (j = i ∨ j = i + 1) →
      0 < Split.det3 (x (r (i + 1)) - x (r i)) (x (r (a + 1)) - x (r a)) w →
      (-sh * ⟪Split.Slope.linSpinVec (fun t => x (r t)) a i j, w⟫ /
          Split.det3 (x (r (i + 1)) - x (r i)) (x (r (a + 1)) - x (r a)) w) -
        μ' * ⟪x (r j) - x (r a), w⟫ < α')
    (hOrange0 : ∀ p q : ZMod k, p ≠ a → (q = p ∨ q = p + 1) →
      Split.det3 (x (r (p + 1)) - x (r p)) (x (r (a + 1)) - x (r a)) w < 0 →
      α' < (-sh * ⟪Split.Slope.linSpinVec (fun t => x (r t)) a p q, w⟫ /
          Split.det3 (x (r (p + 1)) - x (r p)) (x (r (a + 1)) - x (r a)) w) -
        μ' * ⟪x (r q) - x (r a), w⟫) :
    Gen.EdgePlaneAny x := by
  refine (edgePlaneAny_iff_exists_at x).mpr ⟨w, ?_⟩
  rcases LexEP.strictRimN_of_openCell hk F hr hcyc hcell with
    hrim | hrim_rev
  · exact Split.Slope.edgePlaneAt_of_lineSep hk x w r hr hrim hhid
      a hD0 hc_ne0 sh hsh α' μ' hBlue0 hOrange0
  · let r_rev : ZMod k → Fin 7 := fun i => r (-i)
    let a' : ZMod k := -a - 1
    have hr_rev_inj : Function.Injective r_rev :=
      fun i j h => neg_inj.mp (hr h)
    have hrim' : Split.StrictRimN x w r_rev := fun m i hm0 hm1 => hrim_rev m i hm0 hm1
    have hhid' : Split.HiddenInTriangles x w r_rev := fun m hm =>
      hhid m (fun i h => hm (-i) (by dsimp [r_rev]; simpa using h))
    have ha1 : r_rev (a' + 1) = r a := by dsimp [r_rev, a']; congr 1; ring
    have ha0 : r_rev a' = r (a + 1) := by dsimp [r_rev, a']; congr 1; ring
    have hD' : ⟪x (r_rev (a' + 1)) - x (r_rev a'), w⟫ ≠ 0 := by
      rw [ha1, ha0]
      intro h; apply hD0
      have hsub : x (r (a + 1)) - x (r a) = -(x (r a) - x (r (a + 1))) := by abel
      rw [hsub, inner_neg_left, h, neg_zero]
    have hc_eq : ∀ i : ZMod k,
        Split.det3 (x (r_rev (i + 1)) - x (r_rev i)) (x (r_rev (a' + 1)) - x (r_rev a')) w =
        Split.det3 (x (r (-i - 1 + 1)) - x (r (-i - 1))) (x (r (a + 1)) - x (r a)) w := by
      intro i
      have hc1 : r_rev (i + 1) = r (-i - 1) := by dsimp [r_rev]; congr 1; ring
      have hc0 : r_rev i = r (-i - 1 + 1) := by dsimp [r_rev]; congr 1; ring
      rw [hc1, hc0, ha1, ha0]
      simp only [Split.det3, PiLp.sub_apply]
      ring
    have hv_eq : ∀ i j : ZMod k,
        Split.Slope.linSpinVec (fun t => x (r_rev t)) a' i j =
        Split.Slope.linSpinVec (fun t => x (r t)) a (-i - 1) (-j) := by
      intro i j
      have hc1 : r_rev (i + 1) = r (-i - 1) := by dsimp [r_rev]; congr 1; ring
      have hc0 : r_rev i = r (-i - 1 + 1) := by dsimp [r_rev]; congr 1; ring
      have hrj : r_rev j = r (-j) := rfl
      dsimp only [Split.Slope.linSpinVec]
      rw [hc1, hc0, ha1, ha0, hrj]
      have hsub : x (r (-j)) - x (r (a + 1)) = (x (r (-j)) - x (r a)) - (x (r (a + 1)) - x (r a)) := by
        abel
      have he1 : x (r (-i - 1)) - x (r (-i - 1 + 1)) = -(x (r (-i - 1 + 1)) - x (r (-i - 1))) := by abel
      have he2 : x (r a) - x (r (a + 1)) = -(x (r (a + 1)) - x (r a)) := by abel
      rw [hsub, he1, he2]
      simp only [inner_sub_right, inner_neg_left, inner_neg_right]
      module
    have hz_eq : ∀ j : ZMod k,
        ⟪x (r_rev j) - x (r_rev a'), w⟫ =
        ⟪x (r (-j)) - x (r a), w⟫ - ⟪x (r (a + 1)) - x (r a), w⟫ := by
      intro j
      have h4 : -a' = a + 1 := by dsimp [a']; ring
      change ⟪x (r (-j)) - x (r (-a')), w⟫ = _
      rw [h4]
      have : x (r (-j)) - x (r (a + 1)) = (x (r (-j)) - x (r a)) - (x (r (a + 1)) - x (r a)) := by abel
      rw [this, inner_sub_left]
    have hi_iff : ∀ i : ZMod k, i ≠ a' → -i - 1 ≠ a := by
      intro i hi h; apply hi; linear_combination -h
    have hj_iff : ∀ i j : ZMod k, j = i ∨ j = i + 1 → -j = -i - 1 ∨ -j = -i - 1 + 1 := by
      intro i j hj
      rcases hj with rfl | rfl
      · right; ring
      · left; ring
    refine Split.Slope.edgePlaneAt_of_lineSep hk x w r_rev hr_rev_inj hrim' hhid'
      a' hD' (fun i hi => by rw [hc_eq]; exact hc_ne0 (-i - 1) (hi_iff i hi))
      sh hsh (α' + μ' * ⟪x (r (a + 1)) - x (r a), w⟫) μ' ?_ ?_
    · intro i j hi hj hpos
      rw [hc_eq] at hpos
      rw [hc_eq, hv_eq, hz_eq]
      have h0 := hBlue0 (-i - 1) (-j) (hi_iff i hi) (hj_iff i j hj) hpos
      linarith
    · intro p q hp hq hneg
      rw [hc_eq] at hneg
      rw [hc_eq, hv_eq, hz_eq]
      have h0 := hOrange0 (-p - 1) (-q) (hi_iff p hp) (hj_iff p q hq) hneg
      linarith

/-- **FR2 (`w_D` leaf):** strict line separation at an interior view `wD x β γ` of `(U_D, D_D)`
on any edge `a` yields `Gen.EdgePlaneAny x` (no limit argument needed). -/
theorem wd_edgePlaneAny {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    {beta gamma : ℝ} (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hroof : omega4 x * beta + gamma < 1)
    (h6 : ⟪F.N 6, wD x beta gamma⟫ < 0) (h8 : ⟪F.N 8, wD x beta gamma⟫ < 0)
    (a : ZMod 5)
    (hD0 : ⟪x (rD (a + 1)) - x (rD a), wD x beta gamma⟫ ≠ 0)
    (hc_ne0 : ∀ i : ZMod 5, i ≠ a →
      Split.det3 (x (rD (i + 1)) - x (rD i)) (x (rD (a + 1)) - x (rD a)) (wD x beta gamma) ≠ 0)
    (sh : ℝ) (hsh : sh = 1 ∨ sh = -1) (α' μ' : ℝ)
    (hBlue0 : ∀ i j : ZMod 5, i ≠ a → (j = i ∨ j = i + 1) →
      0 < Split.det3 (x (rD (i + 1)) - x (rD i)) (x (rD (a + 1)) - x (rD a)) (wD x beta gamma) →
      (-sh * ⟪Split.Slope.linSpinVec (fun t => x (rD t)) a i j, wD x beta gamma⟫ /
          Split.det3 (x (rD (i + 1)) - x (rD i)) (x (rD (a + 1)) - x (rD a)) (wD x beta gamma)) -
        μ' * ⟪x (rD j) - x (rD a), wD x beta gamma⟫ < α')
    (hOrange0 : ∀ p q : ZMod 5, p ≠ a → (q = p ∨ q = p + 1) →
      Split.det3 (x (rD (p + 1)) - x (rD p)) (x (rD (a + 1)) - x (rD a)) (wD x beta gamma) < 0 →
      α' < (-sh * ⟪Split.Slope.linSpinVec (fun t => x (rD t)) a p q, wD x beta gamma⟫ /
          Split.det3 (x (rD (p + 1)) - x (rD p)) (x (rD (a + 1)) - x (rD a)) (wD x beta gamma)) -
        μ' * ⟪x (rD q) - x (rD a), wD x beta gamma⟫) :
    Gen.EdgePlaneAny x := by
  have hcell : CellAt F U_D D_D (wD x beta gamma) :=
    (wd_cellAt_iff F hC hbeta hgamma hroof).mpr ⟨h6, h8⟩
  exact cell_lineSep_edgePlaneAny F (by norm_num) rD rD_inj rD_cyc hcell
    (hidden_in_rD_of_cell F hcell) a hD0 hc_ne0 sh hsh α' μ' hBlue0 hOrange0

/-- `WDCertAt x F β γ`: interior `(U_D, D_D)` cell conditions and strict line separation at
`wD x β γ` on some edge `a : ZMod 5` of `rD = ![0, 1, 2, 3, 6]`. -/
def WDCertAt (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) (beta gamma : ℝ) : Prop :=
  0 < beta ∧ 0 < gamma ∧ omega4 x * beta + gamma < 1 ∧
  ⟪F.N 6, wD x beta gamma⟫ < 0 ∧ ⟪F.N 8, wD x beta gamma⟫ < 0 ∧
  ∃ a : ZMod 5,
    ⟪x (rD (a + 1)) - x (rD a), wD x beta gamma⟫ ≠ 0 ∧
    (∀ i : ZMod 5, i ≠ a →
      Split.det3 (x (rD (i + 1)) - x (rD i)) (x (rD (a + 1)) - x (rD a)) (wD x beta gamma) ≠ 0) ∧
    ∃ sh α' μ' : ℝ, (sh = 1 ∨ sh = -1) ∧
      (∀ i j : ZMod 5, i ≠ a → (j = i ∨ j = i + 1) →
        0 < Split.det3 (x (rD (i + 1)) - x (rD i)) (x (rD (a + 1)) - x (rD a)) (wD x beta gamma) →
        (-sh * ⟪Split.Slope.linSpinVec (fun t => x (rD t)) a i j, wD x beta gamma⟫ /
            Split.det3 (x (rD (i + 1)) - x (rD i)) (x (rD (a + 1)) - x (rD a)) (wD x beta gamma)) -
          μ' * ⟪x (rD j) - x (rD a), wD x beta gamma⟫ < α') ∧
      (∀ p q : ZMod 5, p ≠ a → (q = p ∨ q = p + 1) →
        Split.det3 (x (rD (p + 1)) - x (rD p)) (x (rD (a + 1)) - x (rD a)) (wD x beta gamma) < 0 →
        α' < (-sh * ⟪Split.Slope.linSpinVec (fun t => x (rD t)) a p q, wD x beta gamma⟫ /
            Split.det3 (x (rD (p + 1)) - x (rD p)) (x (rD (a + 1)) - x (rD a)) (wD x beta gamma)) -
          μ' * ⟪x (rD q) - x (rD a), wD x beta gamma⟫)

theorem holeLeaf_not_wd {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F)
    {beta gamma : ℝ} (hc : WDCertAt x F beta gamma) : False := by
  rcases hc with ⟨hb, hg, hr, h6, h8, a, hD0, hc_ne0, sh, α', μ', hsh, hB, hO⟩
  exact Atlas.holeLeaf_not_edgePlaneAny hF
    (wd_edgePlaneAny F hF.1 hb hg hr h6 h8 a hD0 hc_ne0 sh hsh α' μ' hB hO)

theorem hole24_not_wd {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : Hole24 x F)
    {beta gamma : ℝ} (hc : WDCertAt x F beta gamma) : False :=
  holeLeaf_not_wd hF.1 hc

/-- **FR2 (`π_24` twin of `wd_edgePlaneAny`).** -/
theorem wd_edgePlaneAny_twin {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    {beta gamma : ℝ} (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hroof : omega4 (x ∘ Sym.pi24) * beta + gamma < 1)
    (h6 : ⟪(Sym.sym24 F).N 6, wD (x ∘ Sym.pi24) beta gamma⟫ < 0)
    (h8 : ⟪(Sym.sym24 F).N 8, wD (x ∘ Sym.pi24) beta gamma⟫ < 0)
    (a : ZMod 5)
    (hD0 : ⟪(x ∘ Sym.pi24) (rD (a + 1)) - (x ∘ Sym.pi24) (rD a), wD (x ∘ Sym.pi24) beta gamma⟫ ≠ 0)
    (hc_ne0 : ∀ i : ZMod 5, i ≠ a →
      Split.det3 ((x ∘ Sym.pi24) (rD (i + 1)) - (x ∘ Sym.pi24) (rD i))
        ((x ∘ Sym.pi24) (rD (a + 1)) - (x ∘ Sym.pi24) (rD a)) (wD (x ∘ Sym.pi24) beta gamma) ≠ 0)
    (sh : ℝ) (hsh : sh = 1 ∨ sh = -1) (α' μ' : ℝ)
    (hBlue0 : ∀ i j : ZMod 5, i ≠ a → (j = i ∨ j = i + 1) →
      0 < Split.det3 ((x ∘ Sym.pi24) (rD (i + 1)) - (x ∘ Sym.pi24) (rD i))
          ((x ∘ Sym.pi24) (rD (a + 1)) - (x ∘ Sym.pi24) (rD a)) (wD (x ∘ Sym.pi24) beta gamma) →
      (-sh * ⟪Split.Slope.linSpinVec (fun t => (x ∘ Sym.pi24) (rD t)) a i j,
            wD (x ∘ Sym.pi24) beta gamma⟫ /
          Split.det3 ((x ∘ Sym.pi24) (rD (i + 1)) - (x ∘ Sym.pi24) (rD i))
            ((x ∘ Sym.pi24) (rD (a + 1)) - (x ∘ Sym.pi24) (rD a)) (wD (x ∘ Sym.pi24) beta gamma)) -
        μ' * ⟪(x ∘ Sym.pi24) (rD j) - (x ∘ Sym.pi24) (rD a), wD (x ∘ Sym.pi24) beta gamma⟫ < α')
    (hOrange0 : ∀ p q : ZMod 5, p ≠ a → (q = p ∨ q = p + 1) →
      Split.det3 ((x ∘ Sym.pi24) (rD (p + 1)) - (x ∘ Sym.pi24) (rD p))
          ((x ∘ Sym.pi24) (rD (a + 1)) - (x ∘ Sym.pi24) (rD a)) (wD (x ∘ Sym.pi24) beta gamma) < 0 →
      α' < (-sh * ⟪Split.Slope.linSpinVec (fun t => (x ∘ Sym.pi24) (rD t)) a p q,
            wD (x ∘ Sym.pi24) beta gamma⟫ /
          Split.det3 ((x ∘ Sym.pi24) (rD (p + 1)) - (x ∘ Sym.pi24) (rD p))
            ((x ∘ Sym.pi24) (rD (a + 1)) - (x ∘ Sym.pi24) (rD a)) (wD (x ∘ Sym.pi24) beta gamma)) -
        μ' * ⟪(x ∘ Sym.pi24) (rD q) - (x ∘ Sym.pi24) (rD a), wD (x ∘ Sym.pi24) beta gamma⟫) :
    Gen.EdgePlaneAny x :=
  edgePlaneAny_of_comp_pi24 x
    (wd_edgePlaneAny (Sym.sym24 F) ((Sym.cbarIn_comp_pi24 x).2 hC) hbeta hgamma hroof h6 h8
      a hD0 hc_ne0 sh hsh α' μ' hBlue0 hOrange0)

theorem holeLeaf_not_wd_twin {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F)
    {beta gamma : ℝ} (hc : WDCertAt (x ∘ Sym.pi24) (Sym.sym24 F) beta gamma) : False := by
  rcases hc with ⟨hb, hg, hr, h6, h8, a, hD0, hc_ne0, sh, α', μ', hsh, hB, hO⟩
  exact Atlas.holeLeaf_not_edgePlaneAny hF
    (wd_edgePlaneAny_twin F hF.1 hb hg hr h6 h8 a hD0 hc_ne0 sh hsh α' μ' hB hO)

theorem hole24_not_wd_twin {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : Hole24 x F)
    {beta gamma : ℝ} (hc : WDCertAt (x ∘ Sym.pi24) (Sym.sym24 F) beta gamma) : False :=
  holeLeaf_not_wd_twin hF.1 hc

/-- Extended two-cone residue adding `¬ WDCertAt` and its `π_24` twin. -/
def TwoConeResidue''' (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  TwoConeResidue'' x F ∧
  (∀ beta gamma : ℝ, ¬ WDCertAt x F beta gamma) ∧
  (∀ beta gamma : ℝ, ¬ WDCertAt (x ∘ Sym.pi24) (Sym.sym24 F) beta gamma)

theorem hole24_twoConeResidue''' {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : Hole24 x F) :
    TwoConeResidue''' x F :=
  ⟨hole24_twoConeResidue'' hF,
    fun _ _ h => hole24_not_wd hF h,
    fun _ _ h => hole24_not_wd_twin hF h⟩

/-! ## FR3: Rim determinants on `rD = ![0, 1, 2, 3, 6]`, edge `6 → 0` -/

/-- **FR3 (general frame form):** for `E = u_a • (x 0 - x 1) + u_b • (x 2 - x 1) + u_c • (x 6 - x 1)`,
`Split.det3 E (x 0 - x 6) (wD x β γ) = det24 x * ((1 - γ) * u_b - β * (u_a + u_c))`. -/
theorem wd_det3_frame (x : Fin 7 → ℝ³) (ua ub uc beta gamma : ℝ) :
    Split.det3 (ua • (x 0 - x 1) + ub • (x 2 - x 1) + uc • (x 6 - x 1))
      (x 0 - x 6) (wD x beta gamma) =
    det24 x * ((1 - gamma) * ub - beta * (ua + uc)) := by
  have hd : x 0 - x 6 = (1 : ℝ) • (x 0 - x 1) + (0 : ℝ) • (x 2 - x 1) + (-1 : ℝ) • (x 6 - x 1) := by
    module
  have hw : wD x beta gamma =
      (-1 : ℝ) • (x 0 - x 1) + (-beta) • (x 2 - x 1) + gamma • (x 6 - x 1) := by
    unfold wD capView; module
  rw [Split.det3_eq_minimality, hd, hw, M4.det3_frame]
  ring

/-- **FR3 (explicit `rD` rim determinants, edge `a = 4`, `6 → 0`):**
the four non-`a` determinants `Split.det3 (x (rD (i + 1)) - x (rD i)) (x 0 - x 6) (wD x β γ)`
equal `det24 x` times `β`, `1 - γ`, `-(1 - b_3)(1 - γ) - β(a_3 + c_3)`, and
`-b_3(1 - γ) - β(1 - a_3 - c_3)`. -/
theorem wd_det3_rim {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (beta gamma : ℝ) :
    Split.det3 (x (rD (0 + 1)) - x (rD 0)) (x 0 - x 6) (wD x beta gamma) =
      beta * det24 x ∧
    Split.det3 (x (rD (1 + 1)) - x (rD 1)) (x 0 - x 6) (wD x beta gamma) =
      (1 - gamma) * det24 x ∧
    Split.det3 (x (rD (2 + 1)) - x (rD 2)) (x 0 - x 6) (wD x beta gamma) =
      (-(1 - oblX2 x 3) * (1 - gamma) - beta * (oblX0 x 3 + oblX6 x 3)) * det24 x ∧
    Split.det3 (x (rD (3 + 1)) - x (rD 3)) (x 0 - x 6) (wD x beta gamma) =
      (-oblX2 x 3 * (1 - gamma) - beta * (1 - oblX0 x 3 - oblX6 x 3)) * det24 x := by
  have T := type24OfFac F
  have hrep : ∀ v : Fin 7, x v - x 1 =
      oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1) := by
    intro v; rw [T.rep v]; abel
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h0 : x (rD (0 + 1)) - x (rD 0) =
        (-1 : ℝ) • (x 0 - x 1) + (0 : ℝ) • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) := by
      show x 1 - x 0 = _; module
    rw [h0, wd_det3_frame]; ring
  · have h1 : x (rD (1 + 1)) - x (rD 1) =
        (0 : ℝ) • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) := by
      show x 2 - x 1 = _; module
    rw [h1, wd_det3_frame]; ring
  · have h2 : x (rD (2 + 1)) - x (rD 2) =
        oblX0 x 3 • (x 0 - x 1) + (oblX2 x 3 - 1) • (x 2 - x 1) + oblX6 x 3 • (x 6 - x 1) := by
      have h32 : x (rD (2 + 1)) - x (rD 2) = (x 3 - x 1) - (x 2 - x 1) := by
        show x 3 - x 2 = _; abel
      rw [h32, hrep 3]; module
    rw [h2, wd_det3_frame]; ring
  · have h3 : x (rD (3 + 1)) - x (rD 3) =
        (-oblX0 x 3) • (x 0 - x 1) + (-oblX2 x 3) • (x 2 - x 1) + (1 - oblX6 x 3) • (x 6 - x 1) := by
      have h63 : x (rD (3 + 1)) - x (rD 3) = (x 6 - x 1) - (x 3 - x 1) := by
        show x 6 - x 3 = _; abel
      rw [h63, hrep 3]; module
    rw [h3, wd_det3_frame]; ring

/-! ## FS1: `w_D6` cell (`rD6 = ![0, 1, 2, 3, 4, 6]`, vertex `5` hidden) -/

/-- Rim `rD6 = ![0, 1, 2, 3, 4, 6]` (reverse of `0.6.4.3.2.1`). -/
def rD6 : ZMod 6 → Fin 7 := ![0, 1, 2, 3, 4, 6]

theorem rD6_inj : Function.Injective rD6 := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)

/-- Up facets `{1, 5, 7, 8}` (`016, 126, 236, 346 > 0`) of the `w_D6` cell. -/
def U_D6 : Finset (Fin 9) := {1, 5, 7, 8}

/-- Down facets `{0, 2, 3, 4, 6}` (`012, 025, 0345, 046, 235 < 0`) of the `w_D6` cell. -/
def D_D6 : Finset (Fin 9) := {0, 2, 3, 4, 6}

theorem rD6_cyc : S0xCycUD s0x_S24 rD6 U_D6 D_D6 := by
  decide

/-- **FS1:** Under `CbarIn x`, `β > 0`, `γ > 0`, `ω_4(x) * β + γ < 1`,
`CellAt F U_D6 D_D6 (wD x β γ)` holds iff facet `6` is strictly negative and facet `8` is
strictly positive (so 7 of 9 facets hold automatically on the right triangle, and 8 of 9 hold
when `0 < ⟪F.N 8, wD x β γ⟫`, e.g. near `γ = 1 - ω_4 * β` for `0 < β < min(b_4/a_4, 1/ω_4)`). -/
theorem wd6_cellAt_iff {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    {beta gamma : ℝ} (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hroof : omega4 x * beta + gamma < 1) :
    CellAt F U_D6 D_D6 (wD x beta gamma) ↔
      ⟪F.N 6, wD x beta gamma⟫ < 0 ∧ 0 < ⟪F.N 8, wD x beta gamma⟫ := by
  have ⟨hU7, hD7⟩ := wd_seven_facets F hC hbeta hgamma hroof
  constructor
  · intro ⟨hup, hdn⟩
    exact ⟨hdn 6 (by decide), hup 8 (by decide)⟩
  · intro ⟨h6, h8⟩
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · fin_cases t <;> simp [U_D6] at ht
      · exact hU7 1 (by decide)
      · exact hU7 5 (by decide)
      · exact hU7 7 (by decide)
      · exact h8
    · fin_cases t <;> simp [D_D6] at ht
      · exact hD7 0 (by decide)
      · exact hD7 2 (by decide)
      · exact hD7 3 (by decide)
      · exact hD7 4 (by decide)
      · exact h6

/-- **FS1:** On any `CellAt F U_D6 D_D6 w`, vertex `5` lies strictly inside `(x 0, x 3, x 2)`
or `(x 0, x 2, x 3)` via `{3, 6, 2} ⊆ D_D6`. -/
theorem hidden_in_rD6_of_cell {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {w : ℝ³}
    (hcell : CellAt F U_D6 D_D6 w) :
    Split.HiddenInTriangles x w rD6 := by
  intro m hm
  have hm5 : m = 5 := by
    fin_cases m
    · exact absurd rfl (hm 0)
    · exact absurd rfl (hm 1)
    · exact absurd rfl (hm 2)
    · exact absurd rfl (hm 3)
    · exact absurd rfl (hm 4)
    · rfl
    · exact absurd rfl (hm 5)
  subst hm5
  obtain ⟨p, hp, q, hq, r, hr, h1, h2, h3, h4⟩ :=
    hidden_of_three_facets F 5 0 3 2 3 6 2
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (hcell.2 3 (by decide)) (hcell.2 6 (by decide)) (hcell.2 2 (by decide))
  have hsub : ∀ y ∈ ({x 0, x 3, x 2} : Finset ℝ³), y ∈ univ.image x := fun y hy => by
    simp only [mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl | rfl <;> exact mem_image_of_mem x (mem_univ _)
  exact ⟨p, hsub p hp, q, hsub q hq, r, hsub r hr, h1, h2, h3, h4⟩

/-- **FS1 (`w_D6` leaf):** strict line separation at an interior view `wD x β γ` of `(U_D6, D_D6)`
on any edge `a : ZMod 6` yields `Gen.EdgePlaneAny x`. -/
theorem wd6_edgePlaneAny {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    {beta gamma : ℝ} (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hroof : omega4 x * beta + gamma < 1)
    (h6 : ⟪F.N 6, wD x beta gamma⟫ < 0) (h8 : 0 < ⟪F.N 8, wD x beta gamma⟫)
    (a : ZMod 6)
    (hD0 : ⟪x (rD6 (a + 1)) - x (rD6 a), wD x beta gamma⟫ ≠ 0)
    (hc_ne0 : ∀ i : ZMod 6, i ≠ a →
      Split.det3 (x (rD6 (i + 1)) - x (rD6 i)) (x (rD6 (a + 1)) - x (rD6 a)) (wD x beta gamma) ≠ 0)
    (sh : ℝ) (hsh : sh = 1 ∨ sh = -1) (α' μ' : ℝ)
    (hBlue0 : ∀ i j : ZMod 6, i ≠ a → (j = i ∨ j = i + 1) →
      0 < Split.det3 (x (rD6 (i + 1)) - x (rD6 i)) (x (rD6 (a + 1)) - x (rD6 a)) (wD x beta gamma) →
      (-sh * ⟪Split.Slope.linSpinVec (fun t => x (rD6 t)) a i j, wD x beta gamma⟫ /
          Split.det3 (x (rD6 (i + 1)) - x (rD6 i)) (x (rD6 (a + 1)) - x (rD6 a)) (wD x beta gamma)) -
        μ' * ⟪x (rD6 j) - x (rD6 a), wD x beta gamma⟫ < α')
    (hOrange0 : ∀ p q : ZMod 6, p ≠ a → (q = p ∨ q = p + 1) →
      Split.det3 (x (rD6 (p + 1)) - x (rD6 p)) (x (rD6 (a + 1)) - x (rD6 a)) (wD x beta gamma) < 0 →
      α' < (-sh * ⟪Split.Slope.linSpinVec (fun t => x (rD6 t)) a p q, wD x beta gamma⟫ /
          Split.det3 (x (rD6 (p + 1)) - x (rD6 p)) (x (rD6 (a + 1)) - x (rD6 a)) (wD x beta gamma)) -
        μ' * ⟪x (rD6 q) - x (rD6 a), wD x beta gamma⟫) :
    Gen.EdgePlaneAny x := by
  have hcell : CellAt F U_D6 D_D6 (wD x beta gamma) :=
    (wd6_cellAt_iff F hC hbeta hgamma hroof).mpr ⟨h6, h8⟩
  exact cell_lineSep_edgePlaneAny F (by norm_num) rD6 rD6_inj rD6_cyc hcell
    (hidden_in_rD6_of_cell F hcell) a hD0 hc_ne0 sh hsh α' μ' hBlue0 hOrange0

/-- `WD6CertAt x F β γ`: interior `(U_D6, D_D6)` cell conditions and strict line separation at
`wD x β γ` on some edge `a : ZMod 6` of `rD6 = ![0, 1, 2, 3, 4, 6]`. -/
def WD6CertAt (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) (beta gamma : ℝ) : Prop :=
  0 < beta ∧ 0 < gamma ∧ omega4 x * beta + gamma < 1 ∧
  ⟪F.N 6, wD x beta gamma⟫ < 0 ∧ 0 < ⟪F.N 8, wD x beta gamma⟫ ∧
  ∃ a : ZMod 6,
    ⟪x (rD6 (a + 1)) - x (rD6 a), wD x beta gamma⟫ ≠ 0 ∧
    (∀ i : ZMod 6, i ≠ a →
      Split.det3 (x (rD6 (i + 1)) - x (rD6 i)) (x (rD6 (a + 1)) - x (rD6 a)) (wD x beta gamma) ≠ 0) ∧
    ∃ sh α' μ' : ℝ, (sh = 1 ∨ sh = -1) ∧
      (∀ i j : ZMod 6, i ≠ a → (j = i ∨ j = i + 1) →
        0 < Split.det3 (x (rD6 (i + 1)) - x (rD6 i)) (x (rD6 (a + 1)) - x (rD6 a)) (wD x beta gamma) →
        (-sh * ⟪Split.Slope.linSpinVec (fun t => x (rD6 t)) a i j, wD x beta gamma⟫ /
            Split.det3 (x (rD6 (i + 1)) - x (rD6 i)) (x (rD6 (a + 1)) - x (rD6 a)) (wD x beta gamma)) -
          μ' * ⟪x (rD6 j) - x (rD6 a), wD x beta gamma⟫ < α') ∧
      (∀ p q : ZMod 6, p ≠ a → (q = p ∨ q = p + 1) →
        Split.det3 (x (rD6 (p + 1)) - x (rD6 p)) (x (rD6 (a + 1)) - x (rD6 a)) (wD x beta gamma) < 0 →
        α' < (-sh * ⟪Split.Slope.linSpinVec (fun t => x (rD6 t)) a p q, wD x beta gamma⟫ /
            Split.det3 (x (rD6 (p + 1)) - x (rD6 p)) (x (rD6 (a + 1)) - x (rD6 a)) (wD x beta gamma)) -
          μ' * ⟪x (rD6 q) - x (rD6 a), wD x beta gamma⟫)

theorem holeLeaf_not_wd6 {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F)
    {beta gamma : ℝ} (hc : WD6CertAt x F beta gamma) : False := by
  rcases hc with ⟨hb, hg, hr, h6, h8, a, hD0, hc_ne0, sh, α', μ', hsh, hB, hO⟩
  exact Atlas.holeLeaf_not_edgePlaneAny hF
    (wd6_edgePlaneAny F hF.1 hb hg hr h6 h8 a hD0 hc_ne0 sh hsh α' μ' hB hO)

theorem hole24_not_wd6 {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : Hole24 x F)
    {beta gamma : ℝ} (hc : WD6CertAt x F beta gamma) : False :=
  holeLeaf_not_wd6 hF.1 hc

/-- **FS1 (`π_24` twin of `wd6_edgePlaneAny`).** -/
theorem wd6_edgePlaneAny_twin {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    {beta gamma : ℝ} (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hroof : omega4 (x ∘ Sym.pi24) * beta + gamma < 1)
    (h6 : ⟪(Sym.sym24 F).N 6, wD (x ∘ Sym.pi24) beta gamma⟫ < 0)
    (h8 : 0 < ⟪(Sym.sym24 F).N 8, wD (x ∘ Sym.pi24) beta gamma⟫)
    (a : ZMod 6)
    (hD0 : ⟪(x ∘ Sym.pi24) (rD6 (a + 1)) - (x ∘ Sym.pi24) (rD6 a), wD (x ∘ Sym.pi24) beta gamma⟫ ≠ 0)
    (hc_ne0 : ∀ i : ZMod 6, i ≠ a →
      Split.det3 ((x ∘ Sym.pi24) (rD6 (i + 1)) - (x ∘ Sym.pi24) (rD6 i))
        ((x ∘ Sym.pi24) (rD6 (a + 1)) - (x ∘ Sym.pi24) (rD6 a)) (wD (x ∘ Sym.pi24) beta gamma) ≠ 0)
    (sh : ℝ) (hsh : sh = 1 ∨ sh = -1) (α' μ' : ℝ)
    (hBlue0 : ∀ i j : ZMod 6, i ≠ a → (j = i ∨ j = i + 1) →
      0 < Split.det3 ((x ∘ Sym.pi24) (rD6 (i + 1)) - (x ∘ Sym.pi24) (rD6 i))
          ((x ∘ Sym.pi24) (rD6 (a + 1)) - (x ∘ Sym.pi24) (rD6 a)) (wD (x ∘ Sym.pi24) beta gamma) →
      (-sh * ⟪Split.Slope.linSpinVec (fun t => (x ∘ Sym.pi24) (rD6 t)) a i j,
            wD (x ∘ Sym.pi24) beta gamma⟫ /
          Split.det3 ((x ∘ Sym.pi24) (rD6 (i + 1)) - (x ∘ Sym.pi24) (rD6 i))
            ((x ∘ Sym.pi24) (rD6 (a + 1)) - (x ∘ Sym.pi24) (rD6 a)) (wD (x ∘ Sym.pi24) beta gamma)) -
        μ' * ⟪(x ∘ Sym.pi24) (rD6 j) - (x ∘ Sym.pi24) (rD6 a), wD (x ∘ Sym.pi24) beta gamma⟫ < α')
    (hOrange0 : ∀ p q : ZMod 6, p ≠ a → (q = p ∨ q = p + 1) →
      Split.det3 ((x ∘ Sym.pi24) (rD6 (p + 1)) - (x ∘ Sym.pi24) (rD6 p))
          ((x ∘ Sym.pi24) (rD6 (a + 1)) - (x ∘ Sym.pi24) (rD6 a)) (wD (x ∘ Sym.pi24) beta gamma) < 0 →
      α' < (-sh * ⟪Split.Slope.linSpinVec (fun t => (x ∘ Sym.pi24) (rD6 t)) a p q,
            wD (x ∘ Sym.pi24) beta gamma⟫ /
          Split.det3 ((x ∘ Sym.pi24) (rD6 (p + 1)) - (x ∘ Sym.pi24) (rD6 p))
            ((x ∘ Sym.pi24) (rD6 (a + 1)) - (x ∘ Sym.pi24) (rD6 a)) (wD (x ∘ Sym.pi24) beta gamma)) -
        μ' * ⟪(x ∘ Sym.pi24) (rD6 q) - (x ∘ Sym.pi24) (rD6 a), wD (x ∘ Sym.pi24) beta gamma⟫) :
    Gen.EdgePlaneAny x :=
  edgePlaneAny_of_comp_pi24 x
    (wd6_edgePlaneAny (Sym.sym24 F) ((Sym.cbarIn_comp_pi24 x).2 hC) hbeta hgamma hroof h6 h8
      a hD0 hc_ne0 sh hsh α' μ' hBlue0 hOrange0)

theorem holeLeaf_not_wd6_twin {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F)
    {beta gamma : ℝ} (hc : WD6CertAt (x ∘ Sym.pi24) (Sym.sym24 F) beta gamma) : False := by
  rcases hc with ⟨hb, hg, hr, h6, h8, a, hD0, hc_ne0, sh, α', μ', hsh, hB, hO⟩
  exact Atlas.holeLeaf_not_edgePlaneAny hF
    (wd6_edgePlaneAny_twin F hF.1 hb hg hr h6 h8 a hD0 hc_ne0 sh hsh α' μ' hB hO)

theorem hole24_not_wd6_twin {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : Hole24 x F)
    {beta gamma : ℝ} (hc : WD6CertAt (x ∘ Sym.pi24) (Sym.sym24 F) beta gamma) : False :=
  holeLeaf_not_wd6_twin hF.1 hc

/-- Extended two-cone residue adding `¬ WD6CertAt` and its `π_24` twin. -/
def TwoConeResidue_FS1 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  TwoConeResidue''' x F ∧
  (∀ beta gamma : ℝ, ¬ WD6CertAt x F beta gamma) ∧
  (∀ beta gamma : ℝ, ¬ WD6CertAt (x ∘ Sym.pi24) (Sym.sym24 F) beta gamma)

theorem hole24_twoConeResidue_FS1 {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : Hole24 x F) :
    TwoConeResidue_FS1 x F :=
  ⟨hole24_twoConeResidue''' hF,
    fun _ _ h => hole24_not_wd6 hF h,
    fun _ _ h => hole24_not_wd6_twin hF h⟩

end Minimality.T24.TwoCone
