module

public import Minimality.M4Sym24
public import Minimality.M4cType24
public import Minimality.M4bType24
public import Minimality.M4Type24

/-!
# Type 24 — Refereed A10 Lemmas (Task CE)

Formalizes the referee-verified lemmas from `A10-REFEREE.md`:
- `ustar_facings`, `splitAny24_Ustar`, `isRupert_of_Ustar`, and `splitAny24_Ustar_twin` (`U*-Split`);
- `e25_bound`, `e25_w05`, and `e25b` (edge `25` U-bounds);
- `u27_bound` and `z5_gt_z4_w05` (the sign-fixed Farkas lemma);
- `lexAny_or_split_E04P4U` (the `(2 6)(4 5)` transport of `lexAny_or_split_E05P5U`).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset Filter
open scoped Topology

namespace Minimality.T24.A10

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell
  Minimality.LexCell Minimality.Split Minimality.T24.M4 Minimality.T24.A7
  Minimality.T24.Sym Minimality.T24.A8

/-! ### Part 0: Definitions and Transport Helpers -/

private theorem det3_frame24 (x : Fin 7 → ℝ³) (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℝ) :
    det3 (a0 • (x 0 - x 1) + a1 • (x 2 - x 1) + a2 • (x 6 - x 1))
         (b0 • (x 0 - x 1) + b1 • (x 2 - x 1) + b2 • (x 6 - x 1))
         (c0 • (x 0 - x 1) + c1 • (x 2 - x 1) + c2 • (x 6 - x 1)) =
      (a0 * (b1 * c2 - b2 * c1) - a1 * (b0 * c2 - b2 * c0) + a2 * (b0 * c1 - b1 * c0)) *
        det24 x := by
  simpa [det24] using Minimality.det3_comb (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) a0 a1 a2 b0 b1 b2 c0 c1 c2

noncomputable def Dl (x : Fin 7 → ℝ³) : ℝ :=
  (1 - oblX6 x 3) * (1 - oblX0 x 5) - oblX0 x 3 * oblX6 x 5

noncomputable def ustar (x : Fin 7 → ℝ³) : ℝ³ :=
  (-Dl x) • (x 2 - x 0) + (1 - oblX6 x 3) • (x 5 - x 0)

noncomputable def dstar (x : Fin 7 → ℝ³) : ℝ³ :=
  (2 : ℝ) • (x 2 - x 0) - (x 0 - x 1)

noncomputable def Lam4 (x : Fin 7 → ℝ³) : ℝ :=
  oblX2 x 4 + oblX6 x 4 + omega3 x * (1 - oblX0 x 4)

noncomputable def u07 (x : Fin 7 → ℝ³) : ℝ³ :=
  (x 0 - x 1) + omega3 x • (x 2 - x 1)

noncomputable def u27 (x : Fin 7 → ℝ³) : ℝ³ :=
  (1 + omega5 x) • (x 0 - x 1) + (omega3 x * omega5 x - 1) • (x 2 - x 1) +
    (1 + omega3 x) • (x 6 - x 1)

theorem lam5_comp_pi24 (x : Fin 7 → ℝ³) : Lam5 (x ∘ pi24) = Lam4 x := by
  simp [Lam5, Lam4, oblX0_comp_pi24, oblX2_comp_pi24, oblX6_comp_pi24, omega3_comp_pi24]; ring

/-! ### Part 1: `ustar_facings`, `splitAny24_Ustar`, `isRupert_of_Ustar`, `splitAny24_Ustar_twin` -/

theorem ustar_facings {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (ha5 : oblX0 x 5 < 1) (hc3 : oblX6 x 3 < 1) (hD : Dl x < 0) :
    ⟪F.N 0, ustar x⟫ < 0 ∧ ⟪F.N 1, ustar x⟫ < 0 ∧ ⟪F.N 2, ustar x⟫ = 0 ∧
    ⟪F.N 3, ustar x⟫ < 0 ∧ ⟪F.N 4, ustar x⟫ < 0 ∧ 0 < ⟪F.N 5, ustar x⟫ ∧
    0 < ⟪F.N 6, ustar x⟫ ∧ 0 < ⟪F.N 7, ustar x⟫ := by
  have T := type24OfFac F
  have hom3 : 0 < omega3 x := hC.1
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hD_pos : 0 < -Dl x := neg_pos.mpr hD
  have hc3_pos : 0 < 1 - oblX6 x 3 := sub_pos.mpr hc3
  have hL_pos : 0 < Lam5 x := by dsimp [Lam5]; nlinarith
  have hus : ∀ t : Fin 9, ⟪F.N t, ustar x⟫ =
      (-Dl x) * (F.f t (x 2) - F.f t (x 0)) + (1 - oblX6 x 3) * (F.f t (x 5) - F.f t (x 0)) := by
    intro t; dsimp [ustar]
    rw [inner_add_right, inner_smul_right, inner_smul_right, ← F.hN t (x 2) (x 0), ← F.hN t (x 5) (x 0)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hus 0, F.zero 0 2 (by decide), F.zero 0 0 (by decide), sub_self, mul_zero, zero_add, sub_zero]
    exact mul_neg_of_pos_of_neg hc3_pos (F.neg 0 5 (by decide))
  · rw [hus 1, F.zero 1 0 (by decide), sub_zero, sub_zero]
    have h12 : F.f 1 (x 2) < 0 := F.neg 1 2 (by decide)
    have h15 : F.f 1 (x 5) < 0 := F.neg 1 5 (by decide)
    nlinarith
  · rw [hus 2, F.zero 2 0 (by decide), F.zero 2 2 (by decide), F.zero 2 5 (by decide), sub_self]
    ring
  · rw [hus 3, F.zero 3 0 (by decide), F.zero 3 5 (by decide), sub_self, mul_zero, add_zero, sub_zero]
    exact mul_neg_of_pos_of_neg hD_pos (F.neg 3 2 (by decide))
  · rw [hus 4, F.zero 4 0 (by decide), sub_zero, sub_zero]
    have h42 : F.f 4 (x 2) < 0 := F.neg 4 2 (by decide)
    have h45 : F.f 4 (x 5) < 0 := F.neg 4 5 (by decide)
    nlinarith
  · rw [hus 5]
    have ev5 := fac_eval F 5 5
    rw [F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)] at ev5
    have h52 : F.f 5 (x 2) = 0 := F.zero 5 2 (by decide)
    have h50 : F.f 5 (x 0) < 0 := F.neg 5 0 (by decide)
    have h55 : F.f 5 (x 5) - F.f 5 (x 0) = (oblX0 x 5 - 1) * F.f 5 (x 0) := by
      rw [ev5]; ring
    rw [h52, zero_sub, h55]
    have t1 : 0 < (-Dl x) * (-F.f 5 (x 0)) := mul_pos hD_pos (neg_pos.mpr h50)
    have t2 : 0 < (1 - oblX6 x 3) * ((oblX0 x 5 - 1) * F.f 5 (x 0)) :=
      mul_pos hc3_pos (mul_pos_of_neg_of_neg (sub_neg.mpr ha5) h50)
    linarith
  · rw [hus 6, F.zero 6 2 (by decide), F.zero 6 5 (by decide), zero_sub]
    have h60 : 0 < -F.f 6 (x 0) := by linarith [F.neg 6 0 (by decide)]
    linarith [mul_pos hD_pos h60, mul_pos hc3_pos h60]
  · rw [hus 7, F.zero 7 2 (by decide), zero_sub]
    have hf7_0 : F.f 7 (x 0) = (1 + omega3 x) * F.f 7 (x 1) := by
      have ev7_3 := fac_eval F 7 3
      rw [F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at ev7_3
      have e3 := eq3 F
      have h7_id : oblX0 x 3 * (F.f 7 (x 0) - (1 + omega3 x) * F.f 7 (x 1)) = 0 := by
        linear_combination -ev7_3 + F.f 7 (x 1) * e3
      exact sub_eq_zero.mp ((mul_eq_zero.mp h7_id).resolve_left ha3.ne')
    have ev7_5 := fac_eval F 7 5
    rw [F.zero 7 2 (by decide), F.zero 7 6 (by decide), hf7_0] at ev7_5
    have hdiff : F.f 7 (x 5) - (1 + omega3 x) * F.f 7 (x 1) = (-F.f 7 (x 1)) * Lam5 x := by
      dsimp [Lam5]; rw [ev7_5]; ring
    rw [hf7_0, hdiff]
    have h71 : 0 < -F.f 7 (x 1) := by linarith [F.neg 7 1 (by decide)]
    have t1 : 0 < (-Dl x) * -((1 + omega3 x) * F.f 7 (x 1)) := by
      have : -((1 + omega3 x) * F.f 7 (x 1)) = (1 + omega3 x) * (-F.f 7 (x 1)) := by ring
      rw [this]; exact mul_pos hD_pos (mul_pos (by linarith) h71)
    have t2 : 0 < (1 - oblX6 x 3) * ((-F.f 7 (x 1)) * Lam5 x) :=
      mul_pos hc3_pos (mul_pos h71 hL_pos)
    linarith

private theorem ustar_row35_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (ha5 : oblX0 x 5 < 1) (hc3 : oblX6 x 3 < 1) (hD : Dl x < 0) :
    0 < oblX0 x 3 * (1 - oblX6 x 5) - oblX0 x 5 * (1 - oblX6 x 3) := by
  have T := type24OfFac F
  have hom3 : 0 < omega3 x := hC.1
  have hom5 : 0 < omega5 x := hC.2.2.1
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hb3 : 0 < oblX2 x 3 := T.X2_pos (v := 3) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hfac := ustar_facings F hC ha5 hc3 hD
  have hf6_u : 0 < ⟪F.N 6, ustar x⟫ := hfac.2.2.2.2.2.2.1
  have hf3_u : ⟪F.N 3, ustar x⟫ < 0 := hfac.2.2.2.1
  have hrep : ∀ v : Fin 7, x v - x 1 =
      oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1) := by
    intro v; rw [T.rep v]; abel
  -- By IVT along `u_t = (1 - t) • ustar x + t • (x 2 - x 3)`, `det3 (x 5 - x 3) (x 6 - x 3) (ustar x)`
  -- has the same sign as `det3 (x 5 - x 3) (x 6 - x 3) (x 2 - x 3)`.
  let φ : ℝ → ℝ := fun t => det3 (x 5 - x 3) (x 6 - x 3) ((1 - t) • ustar x + t • (x 2 - x 3))
  have hφ_ne : ∀ t ∈ Set.Icc (0 : ℝ) 1, φ t ≠ 0 := by
    intro t ht h0
    have hdet0 : det3 (x 5 - x 3) (x 6 - x 3) ((1 - t) • ustar x + t • (x 2 - x 3)) = 0 := h0
    have h63_ne : ∀ (α β : ℝ), (1 - t) • ustar x + t • (x 2 - x 3) =
        α • (x 5 - x 3) + β • (x 6 - x 3) → False := by
      intro α β hcomb
      have hn6 := congrArg (fun v => ⟪F.N 6, v⟫) hcomb
      have hn3 := congrArg (fun v => ⟪F.N 3, v⟫) hcomb
      simp only [inner_add_right, inner_smul_right, ← F.hN 6 _ (x 3), ← F.hN 3 _ (x 3),
        F.zero 6 5 (by decide), F.zero 6 3 (by decide), F.zero 6 2 (by decide),
        F.zero 3 5 (by decide), F.zero 3 3 (by decide), sub_self, mul_zero, zero_add, add_zero] at hn6 hn3
      have h66 : F.f 6 (x 6) < 0 := F.neg 6 6 (by decide)
      have h36 : F.f 3 (x 6) < 0 := F.neg 3 6 (by decide)
      have h32 : F.f 3 (x 2) < 0 := F.neg 3 2 (by decide)
      have h_lhs6 : 0 ≤ (1 - t) * ⟪F.N 6, ustar x⟫ :=
        mul_nonneg (sub_nonneg.mpr ht.2) hf6_u.le
      have h_lhs3 : (1 - t) * ⟪F.N 3, ustar x⟫ + t * F.f 3 (x 2) < 0 := by
        rcases eq_or_lt_of_le ht.2 with ht1 | ht1
        · rw [ht1, sub_self, zero_mul, zero_add, one_mul]; exact h32
        · have a1 : (1 - t) * ⟪F.N 3, ustar x⟫ < 0 := mul_neg_of_pos_of_neg (sub_pos.mpr ht1) hf3_u
          have a2 : t * F.f 3 (x 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.1 h32.le
          linarith
      have hβ_nonpos : β ≤ 0 := by
        by_contra hβ; push Not at hβ
        have : β * F.f 6 (x 6) < 0 := mul_neg_of_pos_of_neg hβ h66
        linarith
      have h_rhs3 : 0 ≤ β * F.f 3 (x 6) := mul_nonneg_of_nonpos_of_nonpos hβ_nonpos h36.le
      linarith
    -- Linear dependence from `det3 u v w = 0` when `u ≠ 0`, `⟪n, u⟫ = 0`, `⟪n, v⟫ ≠ 0`
    have hu_ne : x 5 - x 3 ≠ 0 := sub_ne_zero.mpr (T.inj.ne (by decide))
    have h_id : ∀ (n u v w : ℝ³),
        (⟪n, u⟫ * ⟪u, v⟫ - ⟪u, u⟫ * ⟪n, v⟫) • w =
        (⟪n, w⟫ * ⟪u, v⟫ - ⟪u, w⟫ * ⟪n, v⟫) • u +
        (⟪u, w⟫ * ⟪n, u⟫ - ⟪n, w⟫ * ⟪u, u⟫) • v +
        det3 u v w • cross n u := by
      intro n u v w
      have hnorm : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
        simp [Real.norm_eq_abs, sq_abs]
      ext i; fin_cases i <;>
        (simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]
         try rw [hnorm]
         ring)
    have h_spec := h_id (F.N 6) (x 5 - x 3) (x 6 - x 3) ((1 - t) • ustar x + t • (x 2 - x 3))
    have hnu : ⟪F.N 6, x 5 - x 3⟫ = 0 := by
      rw [← F.hN 6 (x 5) (x 3), F.zero 6 5 (by decide), F.zero 6 3 (by decide), sub_self]
    have hnv : ⟪F.N 6, x 6 - x 3⟫ ≠ 0 := by
      rw [← F.hN 6 (x 6) (x 3), F.zero 6 3 (by decide), sub_zero]
      exact (F.neg 6 6 (by decide)).ne
    have huu : ⟪x 5 - x 3, x 5 - x 3⟫ ≠ 0 := (real_inner_self_pos.mpr hu_ne).ne'
    have hcoeff_ne : -(⟪x 5 - x 3, x 5 - x 3⟫ * ⟪F.N 6, x 6 - x 3⟫) ≠ 0 :=
      neg_ne_zero.mpr (mul_ne_zero huu hnv)
    rw [hnu, hdet0, zero_mul, zero_sub, zero_smul, add_zero, mul_zero, zero_sub] at h_spec
    let c0 := -(⟪x 5 - x 3, x 5 - x 3⟫ * ⟪F.N 6, x 6 - x 3⟫)
    refine h63_ne
      ((⟪F.N 6, (1 - t) • ustar x + t • (x 2 - x 3)⟫ * ⟪x 5 - x 3, x 6 - x 3⟫ -
        ⟪x 5 - x 3, (1 - t) • ustar x + t • (x 2 - x 3)⟫ * ⟪F.N 6, x 6 - x 3⟫) / c0)
      ((-(⟪F.N 6, (1 - t) • ustar x + t • (x 2 - x 3)⟫ * ⟪x 5 - x 3, x 5 - x 3⟫)) / c0) ?_
    apply smul_right_injective ℝ³ hcoeff_ne
    simp only [smul_add, smul_smul]
    rw [mul_div_cancel₀ _ hcoeff_ne, mul_div_cancel₀ _ hcoeff_ne]
    simp only [smul_add, smul_smul] at h_spec
    exact h_spec
  have hφ_cont : Continuous φ := by
    dsimp [φ]
    simp only [det3]
    fun_prop
  have hφ_prod : 0 < φ 0 * φ 1 := by
    by_contra hle; push Not at hle
    have h0ne : φ 0 ≠ 0 := hφ_ne 0 ⟨le_refl _, zero_le_one⟩
    have h1ne : φ 1 ≠ 0 := hφ_ne 1 ⟨zero_le_one, le_refl _⟩
    have hconn : IsConnected (φ '' Set.Icc (0 : ℝ) 1) :=
      ⟨⟨φ 0, Set.mem_image_of_mem φ ⟨le_refl _, zero_le_one⟩⟩,
        isPreconnected_Icc.image φ hφ_cont.continuousOn⟩
    have h0mem : φ 0 ∈ φ '' Set.Icc (0 : ℝ) 1 :=
      ⟨0, ⟨le_refl _, zero_le_one⟩, rfl⟩
    have h1mem : φ 1 ∈ φ '' Set.Icc (0 : ℝ) 1 :=
      ⟨1, ⟨zero_le_one, le_refl _⟩, rfl⟩
    have hmem0 : (0 : ℝ) ∈ φ '' Set.Icc (0 : ℝ) 1 := by
      rcases lt_or_gt_of_ne h0ne with h0lt | h0gt
      · have h1gt : 0 ≤ φ 1 := by nlinarith
        exact hconn.Icc_subset h0mem h1mem ⟨h0lt.le, h1gt⟩
      · have h1lt : φ 1 ≤ 0 := by nlinarith
        exact hconn.Icc_subset h1mem h0mem ⟨h1lt, h0gt.le⟩
    rcases hmem0 with ⟨t, ht, hft⟩
    exact hφ_ne t ht hft
  -- Compute `φ 0` and `φ 1` in the `det3_frame` basis.
  have h53 : x 5 - x 3 = (oblX0 x 5 - oblX0 x 3) • (x 0 - x 1) +
      (oblX2 x 5 - oblX2 x 3) • (x 2 - x 1) + (oblX6 x 5 - oblX6 x 3) • (x 6 - x 1) := by
    rw [show x 5 - x 3 = (x 5 - x 1) - (x 3 - x 1) by module, hrep 5, hrep 3]; module
  have h63 : x 6 - x 3 = (-oblX0 x 3) • (x 0 - x 1) +
      (-oblX2 x 3) • (x 2 - x 1) + (1 - oblX6 x 3) • (x 6 - x 1) := by
    rw [show x 6 - x 3 = (x 6 - x 1) - (x 3 - x 1) by module, hrep 3]; module
  have h23 : x 2 - x 3 = (-oblX0 x 3) • (x 0 - x 1) +
      (1 - oblX2 x 3) • (x 2 - x 1) + (-oblX6 x 3) • (x 6 - x 1) := by
    rw [show x 2 - x 3 = (x 2 - x 1) - (x 3 - x 1) by module, hrep 3]; module
  have hus_rep : ustar x = (Dl x - (1 - oblX6 x 3) * (1 - oblX0 x 5)) • (x 0 - x 1) +
      (-Dl x + (1 - oblX6 x 3) * oblX2 x 5) • (x 2 - x 1) +
      ((1 - oblX6 x 3) * oblX6 x 5) • (x 6 - x 1) := by
    have h20 : x 2 - x 0 = (-1 : ℝ) • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) := by module
    have h50 : x 5 - x 0 = (oblX0 x 5 - 1) • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) +
        oblX6 x 5 • (x 6 - x 1) := by
      rw [show x 5 - x 0 = (x 5 - x 1) - (x 0 - x 1) by module, hrep 5]; module
    dsimp [ustar]; rw [h20, h50]; module
  have hφ0 : φ 0 = (oblX0 x 3 + oblX2 x 3 + omega5 x * (1 - oblX6 x 3)) * oblX6 x 5 *
      (oblX0 x 3 * (1 - oblX6 x 5) - oblX0 x 5 * (1 - oblX6 x 3)) * det24 x := by
    have h0' : φ 0 = det3 (x 5 - x 3) (x 6 - x 3) (ustar x) := by
      dsimp [φ]; simp
    rw [h0', h53, h63, hus_rep, det3_frame24]
    have e5 := eq5 F
    have hD_def : Dl x = (1 - oblX6 x 3) * (1 - oblX0 x 5) - oblX0 x 3 * oblX6 x 5 := rfl
    have hid : ((oblX0 x 5 - oblX0 x 3) * (-oblX2 x 3 * ((1 - oblX6 x 3) * oblX6 x 5) -
          (1 - oblX6 x 3) * (-Dl x + (1 - oblX6 x 3) * oblX2 x 5)) -
        (oblX2 x 5 - oblX2 x 3) * (-oblX0 x 3 * ((1 - oblX6 x 3) * oblX6 x 5) -
          (1 - oblX6 x 3) * (Dl x - (1 - oblX6 x 3) * (1 - oblX0 x 5))) +
        (oblX6 x 5 - oblX6 x 3) * (-oblX0 x 3 * (-Dl x + (1 - oblX6 x 3) * oblX2 x 5) -
          -oblX2 x 3 * (Dl x - (1 - oblX6 x 3) * (1 - oblX0 x 5)))) -
        (oblX0 x 3 + oblX2 x 3 + omega5 x * (1 - oblX6 x 3)) * oblX6 x 5 *
          (oblX0 x 3 * (1 - oblX6 x 5) - oblX0 x 5 * (1 - oblX6 x 3)) = 0 := by
      rw [hD_def]
      linear_combination (1 - oblX6 x 3) * (oblX0 x 3 * (1 - oblX6 x 5) - oblX0 x 5 * (1 - oblX6 x 3)) * e5
    linear_combination hid * det24 x
  have hφ1 : φ 1 = oblX0 x 3 * (oblX0 x 5 * (1 + omega3 x) - oblX6 x 5 * (1 + omega5 x)) * det24 x := by
    have h1' : φ 1 = det3 (x 5 - x 3) (x 6 - x 3) (x 2 - x 3) := by
      dsimp [φ]; simp
    rw [h1', h53, h63, h23, det3_frame24]
    have e3 := eq3 F
    have e5 := eq5 F
    have hid : ((oblX0 x 5 - oblX0 x 3) * (-oblX2 x 3 * -oblX6 x 3 - (1 - oblX6 x 3) * (1 - oblX2 x 3)) -
        (oblX2 x 5 - oblX2 x 3) * (-oblX0 x 3 * -oblX6 x 3 - (1 - oblX6 x 3) * -oblX0 x 3) +
        (oblX6 x 5 - oblX6 x 3) * (-oblX0 x 3 * (1 - oblX2 x 3) - -oblX2 x 3 * -oblX0 x 3)) -
        oblX0 x 3 * (oblX0 x 5 * (1 + omega3 x) - oblX6 x 5 * (1 + omega5 x)) = 0 := by
      linear_combination oblX0 x 5 * e3 - oblX0 x 3 * e5
    linear_combination hid * det24 x
  have h75_pos : 0 < oblX0 x 5 * (1 + omega3 x) - oblX6 x 5 * (1 + omega5 x) := by
    have hf7_0 : F.f 7 (x 0) = (1 + omega3 x) * F.f 7 (x 1) := by
      have ev7_3 := fac_eval F 7 3
      rw [F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at ev7_3
      have e3 := eq3 F
      have h7_id : oblX0 x 3 * (F.f 7 (x 0) - (1 + omega3 x) * F.f 7 (x 1)) = 0 := by
        linear_combination -ev7_3 + F.f 7 (x 1) * e3
      exact sub_eq_zero.mp ((mul_eq_zero.mp h7_id).resolve_left ha3.ne')
    have ev7_5 := fac_eval F 7 5
    rw [F.zero 7 2 (by decide), F.zero 7 6 (by decide), hf7_0] at ev7_5
    have e5 := eq5 F
    have h75_id : F.f 7 (x 5) = (oblX0 x 5 * (1 + omega3 x) - oblX6 x 5 * (1 + omega5 x)) * F.f 7 (x 1) := by
      linear_combination ev7_5 - F.f 7 (x 1) * e5
    have h71 : F.f 7 (x 1) < 0 := F.neg 7 1 (by decide)
    have h75 : F.f 7 (x 5) < 0 := F.neg 7 5 (by decide)
    nlinarith
  have hdet_sq : 0 < (det24 x) ^ 2 := by
    have hne : det24 x ≠ 0 := by
      intro hd
      have : φ 1 = 0 := by rw [hφ1, hd, mul_zero]
      exact hφ_ne 1 ⟨zero_le_one, le_refl _⟩ this
    exact sq_pos_of_ne_zero hne
  have hcof_pos : 0 < (oblX0 x 3 + oblX2 x 3 + omega5 x * (1 - oblX6 x 3)) * oblX6 x 5 *
      (oblX0 x 3 * (1 - oblX6 x 5) - oblX0 x 5 * (1 - oblX6 x 3)) *
      (oblX0 x 3 * (oblX0 x 5 * (1 + omega3 x) - oblX6 x 5 * (1 + omega5 x))) := by
    have hmul : φ 0 * φ 1 = ((oblX0 x 3 + oblX2 x 3 + omega5 x * (1 - oblX6 x 3)) * oblX6 x 5 *
      (oblX0 x 3 * (1 - oblX6 x 5) - oblX0 x 5 * (1 - oblX6 x 3)) *
      (oblX0 x 3 * (oblX0 x 5 * (1 + omega3 x) - oblX6 x 5 * (1 + omega5 x)))) * (det24 x) ^ 2 := by
      rw [hφ0, hφ1]; ring
    rw [hmul] at hφ_prod
    exact pos_of_mul_pos_left hφ_prod hdet_sq.le
  have hfac1 : 0 < oblX0 x 3 + oblX2 x 3 + omega5 x * (1 - oblX6 x 3) := by
    have : 0 < omega5 x * (1 - oblX6 x 3) := mul_pos hom5 (sub_pos.mpr hc3)
    linarith
  have hfac2 : 0 < oblX0 x 3 * (oblX0 x 5 * (1 + omega3 x) - oblX6 x 5 * (1 + omega5 x)) :=
    mul_pos ha3 h75_pos
  have hmul_pos : 0 < ((oblX0 x 3 + oblX2 x 3 + omega5 x * (1 - oblX6 x 3)) * oblX6 x 5) *
      (oblX0 x 3 * (oblX0 x 5 * (1 + omega3 x) - oblX6 x 5 * (1 + omega5 x))) :=
    mul_pos (mul_pos hfac1 hc5) hfac2
  nlinarith

theorem splitAny24_Ustar {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (ha5 : oblX0 x 5 < 1) (hc3 : oblX6 x 3 < 1) (hD : Dl x < 0)
    (h8 : ⟪F.N 8, ustar x⟫ < 0)
    (hz : max 0 ⟪x 6 - x 1, ustar x⟫ <
      min ⟪x 2 - x 1, ustar x⟫ (min ⟪x 3 - x 1, ustar x⟫ ⟪x 5 - x 1, ustar x⟫)) :
    SplitAny24 F := by
  have T := type24OfFac F
  have hom5 : 0 < omega5 x := hC.2.2.1
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hb3 : 0 < oblX2 x 3 := T.X2_pos (v := 3) (by decide)
  have ha5_pos : 0 < oblX0 x 5 := T.X0_pos (v := 5) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hc3_pos : 0 < 1 - oblX6 x 3 := sub_pos.mpr hc3
  have hD_pos : 0 < -Dl x := neg_pos.mpr hD
  have hfac := ustar_facings F hC ha5 hc3 hD
  have hrow := ustar_row35_pos F hC ha5 hc3 hD
  have hd2_0 : ⟪F.N 2, dstar x⟫ < 0 := by
    dsimp [dstar]
    rw [inner_sub_right, inner_smul_right, ← F.hN 2 (x 2) (x 0), ← F.hN 2 (x 0) (x 1)]
    have h22 : F.f 2 (x 2) = 0 := F.zero 2 2 (by decide)
    have h20 : F.f 2 (x 0) = 0 := F.zero 2 0 (by decide)
    have h21 : F.f 2 (x 1) < 0 := F.neg 2 1 (by decide)
    linarith
  let c : ZMod 5 → Fin 7 := ![1, 6, 3, 5, 2]
  have hc_inj : Function.Injective c := by
    intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)
  let pat : Fin 9 → Bool := fun t => decide (t = 5 ∨ t = 6 ∨ t = 7)
  have hcyc : S0xCycOK s0x_S24 c pat := by unfold S0xCycOK; decide
  have hlex : ∀ t : Fin 9,
      LexPos3 (if pat t then ⟪F.N t, ustar x⟫ else -⟪F.N t, ustar x⟫)
              (if pat t then ⟪F.N t, dstar x⟫ else -⟪F.N t, dstar x⟫)
              (if pat t then ⟪F.N t, x 6 - x 1⟫ else -⟪F.N t, x 6 - x 1⟫) := by
    intro t; fin_cases t
    · exact Or.inl (by simp [pat]; linarith [hfac.1])
    · exact Or.inl (by simp [pat]; linarith [hfac.2.1])
    · exact Or.inr ⟨by simp [pat, hfac.2.2.1], Or.inl (by simp [pat]; linarith [hd2_0])⟩
    · exact Or.inl (by simp [pat]; linarith [hfac.2.2.2.1])
    · exact Or.inl (by simp [pat]; linarith [hfac.2.2.2.2.1])
    · exact Or.inl (by simp [pat]; exact hfac.2.2.2.2.2.1)
    · exact Or.inl (by simp [pat]; exact hfac.2.2.2.2.2.2.1)
    · exact Or.inl (by simp [pat]; exact hfac.2.2.2.2.2.2.2)
    · exact Or.inl (by simp [pat]; linarith [h8])
  have hz2 : 0 < ⟪x 2 - x 1, ustar x⟫ ∧ ⟪x 6 - x 1, ustar x⟫ < ⟪x 2 - x 1, ustar x⟫ :=
    ⟨lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hz (min_le_left _ _)),
     lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hz (min_le_left _ _))⟩
  have hz3 : 0 < ⟪x 3 - x 1, ustar x⟫ ∧ ⟪x 6 - x 1, ustar x⟫ < ⟪x 3 - x 1, ustar x⟫ :=
    ⟨lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_left _ _))),
     lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_left _ _)))⟩
  have hz5 : 0 < ⟪x 5 - x 1, ustar x⟫ ∧ ⟪x 6 - x 1, ustar x⟫ < ⟪x 5 - x 1, ustar x⟫ :=
    ⟨lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_right _ _))),
     lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_right _ _)))⟩
  have hrep : ∀ v : Fin 7, x v - x 1 =
      oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1) := by
    intro v; rw [T.rep v]; abel
  have hus_rep : ustar x = (Dl x - (1 - oblX6 x 3) * (1 - oblX0 x 5)) • (x 0 - x 1) +
      (-Dl x + (1 - oblX6 x 3) * oblX2 x 5) • (x 2 - x 1) +
      ((1 - oblX6 x 3) * oblX6 x 5) • (x 6 - x 1) := by
    have h20 : x 2 - x 0 = (-1 : ℝ) • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) := by module
    have h50 : x 5 - x 0 = (oblX0 x 5 - 1) • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) +
        oblX6 x 5 • (x 6 - x 1) := by
      rw [show x 5 - x 0 = (x 5 - x 1) - (x 0 - x 1) by module, hrep 5]; module
    dsimp [ustar]; rw [h20, h50]; module
  have hd_rep : dstar x = (-3 : ℝ) • (x 0 - x 1) + (2 : ℝ) • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) := by
    have h20 : x 2 - x 0 = (-1 : ℝ) • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) := by module
    dsimp [dstar]; rw [h20]; module
  have hdet_sq : 0 < det24 x * det24 x := mul_self_pos.mpr T.det_ne
  by_cases hz6_gt : LexPos3 ⟪x 6 - x 1, ustar x⟫ ⟪x 6 - x 1, dstar x⟫ ⟪x 6 - x 1, x 6 - x 1⟫
  · refine Minimality.T24.A8.splitAny24_of_lex3' F (by decide) c hc_inj pat hcyc
      (ustar x) (dstar x) (x 6 - x 1) hlex 4 1 (by decide) (by decide) (det24 x) ?_
    intro i hia j hj hjc
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact absurd rfl hia
    rcases hi with rfl | rfl | rfl | rfl
    · have hj0 : j = 0 := by
        rcases hj with rfl | rfl
        · rfl
        · exact absurd rfl hjc
      subst hj0
      refine ⟨-1, ?_, Or.inl ?_⟩
      · show LexPos3 (-1 * ⟪x 1 - x 6, ustar x⟫) (-1 * ⟪x 1 - x 6, dstar x⟫) (-1 * ⟪x 1 - x 6, x 6 - x 1⟫)
        have h16 : x 1 - x 6 = -(x 6 - x 1) := by module
        rw [h16, inner_neg_left, inner_neg_left, inner_neg_left]
        simp only [neg_one_mul, neg_neg]
        exact hz6_gt
      · show 0 < det24 x * -1 * det3 (x 6 - x 1) (x 1 - x 2) (ustar x)
        have h61 : x 6 - x 1 = (0 : ℝ) • (x 0 - x 1) + (0 : ℝ) • (x 2 - x 1) + (1 : ℝ) • (x 6 - x 1) := by module
        have h12 : x 1 - x 2 = (0 : ℝ) • (x 0 - x 1) + (-1 : ℝ) • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) := by module
        rw [h61, h12, hus_rep, det3_frame24]
        have hD_def : Dl x = (1 - oblX6 x 3) * (1 - oblX0 x 5) - oblX0 x 3 * oblX6 x 5 := rfl
        rw [show det24 x * -1 * ((0 * (-1 * ((1 - oblX6 x 3) * oblX6 x 5) - 0 * (-Dl x + (1 - oblX6 x 3) * oblX2 x 5)) -
            0 * (0 * ((1 - oblX6 x 3) * oblX6 x 5) - 0 * (Dl x - (1 - oblX6 x 3) * (1 - oblX0 x 5))) +
            1 * (0 * (-Dl x + (1 - oblX6 x 3) * oblX2 x 5) - -1 * (Dl x - (1 - oblX6 x 3) * (1 - oblX0 x 5)))) * det24 x) =
            oblX0 x 3 * oblX6 x 5 * (det24 x * det24 x) by rw [hD_def]; ring]
        exact mul_pos (mul_pos ha3 hc5) hdet_sq
    · have hj2 : j = 2 := by
        rcases hj with rfl | rfl
        · exact absurd rfl hjc
        · rfl
      subst hj2
      refine ⟨1, Or.inl (by show 0 < 1 * ⟪x (c 2) - x (c 1), ustar x⟫; rw [one_mul]; change 0 < ⟪x 3 - x 6, ustar x⟫; rw [show x 3 - x 6 = (x 3 - x 1) - (x 6 - x 1) by module, inner_sub_left]; exact sub_pos.mpr hz3.2),
        Or.inr ⟨?_, Or.inl ?_⟩⟩
      · show det24 x * 1 * det3 (x 3 - x 6) (x 1 - x 2) (ustar x) = 0
        have h36 : x 3 - x 6 = oblX0 x 3 • (x 0 - x 1) + oblX2 x 3 • (x 2 - x 1) +
            (oblX6 x 3 - 1) • (x 6 - x 1) := by
          rw [show x 3 - x 6 = (x 3 - x 1) - (x 6 - x 1) by module, hrep 3]; module
        have h12 : x 1 - x 2 = (0 : ℝ) • (x 0 - x 1) + (-1 : ℝ) • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) := by module
        rw [h36, h12, hus_rep, det3_frame24]
        have hD_def : Dl x = (1 - oblX6 x 3) * (1 - oblX0 x 5) - oblX0 x 3 * oblX6 x 5 := rfl
        rw [hD_def]; ring
      · show 0 < det24 x * 1 * det3 (x 3 - x 6) (x 1 - x 2) (dstar x)
        have h36 : x 3 - x 6 = oblX0 x 3 • (x 0 - x 1) + oblX2 x 3 • (x 2 - x 1) +
            (oblX6 x 3 - 1) • (x 6 - x 1) := by
          rw [show x 3 - x 6 = (x 3 - x 1) - (x 6 - x 1) by module, hrep 3]; module
        have h12 : x 1 - x 2 = (0 : ℝ) • (x 0 - x 1) + (-1 : ℝ) • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) := by module
        rw [h36, h12, hd_rep, det3_frame24]
        rw [show det24 x * 1 * ((oblX0 x 3 * (-1 * 0 - 0 * 2) - oblX2 x 3 * (0 * 0 - 0 * -3) +
            (oblX6 x 3 - 1) * (0 * 2 - -1 * -3)) * det24 x) = 3 * (1 - oblX6 x 3) * (det24 x * det24 x) by ring]
        exact mul_pos (mul_pos (by norm_num) hc3_pos) hdet_sq
    · have hj23 : j = 2 ∨ j = 3 := by
        rcases hj with rfl | rfl
        · left; rfl
        · right; rfl
      refine ⟨1, Or.inl ?_, Or.inl ?_⟩
      · rcases hj23 with rfl | rfl
        · show 0 < 1 * ⟪x (c 2) - x (c 1), ustar x⟫; rw [one_mul]; change 0 < ⟪x 3 - x 6, ustar x⟫; rw [show x 3 - x 6 = (x 3 - x 1) - (x 6 - x 1) by module, inner_sub_left]; exact sub_pos.mpr hz3.2
        · show 0 < 1 * ⟪x (c 3) - x (c 1), ustar x⟫; rw [one_mul]; change 0 < ⟪x 5 - x 6, ustar x⟫; rw [show x 5 - x 6 = (x 5 - x 1) - (x 6 - x 1) by module, inner_sub_left]; exact sub_pos.mpr hz5.2
      · show 0 < det24 x * 1 * det3 (x 5 - x 3) (x 1 - x 2) (ustar x)
        have h53 : x 5 - x 3 = (oblX0 x 5 - oblX0 x 3) • (x 0 - x 1) +
            (oblX2 x 5 - oblX2 x 3) • (x 2 - x 1) + (oblX6 x 5 - oblX6 x 3) • (x 6 - x 1) := by
          rw [show x 5 - x 3 = (x 5 - x 1) - (x 3 - x 1) by module, hrep 5, hrep 3]; module
        have h12 : x 1 - x 2 = (0 : ℝ) • (x 0 - x 1) + (-1 : ℝ) • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) := by module
        rw [h53, h12, hus_rep, det3_frame24]
        have hD_def : Dl x = (1 - oblX6 x 3) * (1 - oblX0 x 5) - oblX0 x 3 * oblX6 x 5 := rfl
        rw [show det24 x * 1 * (((oblX0 x 5 - oblX0 x 3) * (-1 * ((1 - oblX6 x 3) * oblX6 x 5) - 0 * (-Dl x + (1 - oblX6 x 3) * oblX2 x 5)) -
            (oblX2 x 5 - oblX2 x 3) * (0 * ((1 - oblX6 x 3) * oblX6 x 5) - 0 * (Dl x - (1 - oblX6 x 3) * (1 - oblX0 x 5))) +
            (oblX6 x 5 - oblX6 x 3) * (0 * (-Dl x + (1 - oblX6 x 3) * oblX2 x 5) - -1 * (Dl x - (1 - oblX6 x 3) * (1 - oblX0 x 5)))) * det24 x) =
            oblX6 x 5 * (oblX0 x 3 * (1 - oblX6 x 5) - oblX0 x 5 * (1 - oblX6 x 3)) * (det24 x * det24 x) by rw [hD_def]; ring]
        exact mul_pos (mul_pos hc5 hrow) hdet_sq
    · have hj34 : j = 3 ∨ j = 4 := by
        rcases hj with rfl | rfl
        · left; rfl
        · right; rfl
      refine ⟨1, Or.inl ?_, Or.inl ?_⟩
      · rcases hj34 with rfl | rfl
        · show 0 < 1 * ⟪x (c 3) - x (c 1), ustar x⟫; rw [one_mul]; change 0 < ⟪x 5 - x 6, ustar x⟫; rw [show x 5 - x 6 = (x 5 - x 1) - (x 6 - x 1) by module, inner_sub_left]; exact sub_pos.mpr hz5.2
        · show 0 < 1 * ⟪x (c 4) - x (c 1), ustar x⟫; rw [one_mul]; change 0 < ⟪x 2 - x 6, ustar x⟫; rw [show x 2 - x 6 = (x 2 - x 1) - (x 6 - x 1) by module, inner_sub_left]; exact sub_pos.mpr hz2.2
      · show 0 < det24 x * 1 * det3 (x 2 - x 5) (x 1 - x 2) (ustar x)
        have h25 : x 2 - x 5 = (-oblX0 x 5) • (x 0 - x 1) +
            (1 - oblX2 x 5) • (x 2 - x 1) + (-oblX6 x 5) • (x 6 - x 1) := by
          rw [show x 2 - x 5 = (x 2 - x 1) - (x 5 - x 1) by module, hrep 5]; module
        have h12 : x 1 - x 2 = (0 : ℝ) • (x 0 - x 1) + (-1 : ℝ) • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) := by module
        rw [h25, h12, hus_rep, det3_frame24]
        have hD_def : Dl x = (1 - oblX6 x 3) * (1 - oblX0 x 5) - oblX0 x 3 * oblX6 x 5 := rfl
        rw [show det24 x * 1 * ((-oblX0 x 5 * (-1 * ((1 - oblX6 x 3) * oblX6 x 5) - 0 * (-Dl x + (1 - oblX6 x 3) * oblX2 x 5)) -
            (1 - oblX2 x 5) * (0 * ((1 - oblX6 x 3) * oblX6 x 5) - 0 * (Dl x - (1 - oblX6 x 3) * (1 - oblX0 x 5))) +
            -oblX6 x 5 * (0 * (-Dl x + (1 - oblX6 x 3) * oblX2 x 5) - -1 * (Dl x - (1 - oblX6 x 3) * (1 - oblX0 x 5)))) * det24 x) =
            oblX6 x 5 * (oblX0 x 5 * (1 - oblX6 x 3) + oblX0 x 3 * oblX6 x 5) * (det24 x * det24 x) by rw [hD_def]; ring]
        exact mul_pos (mul_pos hc5 (add_pos (mul_pos ha5_pos hc3_pos) (mul_pos ha3 hc5))) hdet_sq
  · have hz6_lt : LexPos3 (-⟪x 6 - x 1, ustar x⟫) (-⟪x 6 - x 1, dstar x⟫) (-⟪x 6 - x 1, x 6 - x 1⟫) := by
      have h61_ne : x 6 - x 1 ≠ 0 := by
        intro h
        have h0 : ⟪F.N 0, x 6 - x 1⟫ = 0 := by rw [h, inner_zero_right]
        rw [← F.hN 0 (x 6) (x 1), F.zero 0 1 (by decide), sub_zero] at h0
        exact (F.neg 0 6 (by decide)).ne h0
      rcases lt_trichotomy ⟪x 6 - x 1, ustar x⟫ 0 with hlt | heq | hgt
      · exact Or.inl (neg_pos.mpr hlt)
      · rw [heq, neg_zero]
        rcases lt_trichotomy ⟪x 6 - x 1, dstar x⟫ 0 with hdlt | hdeq | hdgt
        · exact Or.inr ⟨rfl, Or.inl (neg_pos.mpr hdlt)⟩
        · exfalso; apply hz6_gt
          rw [heq, hdeq]
          exact Or.inr ⟨rfl, Or.inr ⟨rfl, real_inner_self_pos.mpr h61_ne⟩⟩
        · exfalso; apply hz6_gt
          rw [heq]; exact Or.inr ⟨rfl, Or.inl hdgt⟩
      · exfalso; exact hz6_gt (Or.inl hgt)
    refine Minimality.T24.A8.splitAny24_of_lex3' F (by decide) c hc_inj pat hcyc
      (ustar x) (dstar x) (x 6 - x 1) hlex 1 0 (by decide) (by decide) (-det24 x) ?_
    intro i hia j hj hjc
    have hi : i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
      fin_cases i
      · exact Or.inl rfl
      · exact absurd rfl hia
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
    rcases hi with rfl | rfl | rfl | rfl
    · have hj1 : j = 1 := by
        rcases hj with rfl | rfl
        · exact absurd rfl hjc
        · rfl
      subst hj1
      refine ⟨-1, ?_, Or.inl ?_⟩
      · change LexPos3 (-1 * ⟪x 6 - x 1, ustar x⟫) (-1 * ⟪x 6 - x 1, dstar x⟫) (-1 * ⟪x 6 - x 1, x 6 - x 1⟫)
        simp only [neg_one_mul]
        exact hz6_lt
      · show 0 < -det24 x * -1 * det3 (x 6 - x 1) (x 3 - x 6) (ustar x)
        have h61 : x 6 - x 1 = (0 : ℝ) • (x 0 - x 1) + (0 : ℝ) • (x 2 - x 1) + (1 : ℝ) • (x 6 - x 1) := by module
        have h36 : x 3 - x 6 = oblX0 x 3 • (x 0 - x 1) + oblX2 x 3 • (x 2 - x 1) +
            (oblX6 x 3 - 1) • (x 6 - x 1) := by
          rw [show x 3 - x 6 = (x 3 - x 1) - (x 6 - x 1) by module, hrep 3]; module
        rw [h61, h36, hus_rep, det3_frame24]
        have hD_def : Dl x = (1 - oblX6 x 3) * (1 - oblX0 x 5) - oblX0 x 3 * oblX6 x 5 := rfl
        have hstep : 0 * (oblX2 x 3 * ((1 - oblX6 x 3) * oblX6 x 5) - (oblX6 x 3 - 1) * (-Dl x + (1 - oblX6 x 3) * oblX2 x 5)) -
            0 * (oblX0 x 3 * ((1 - oblX6 x 3) * oblX6 x 5) - (oblX6 x 3 - 1) * (Dl x - (1 - oblX6 x 3) * (1 - oblX0 x 5))) +
            1 * (oblX0 x 3 * (-Dl x + (1 - oblX6 x 3) * oblX2 x 5) - oblX2 x 3 * (Dl x - (1 - oblX6 x 3) * (1 - oblX0 x 5))) =
            oblX0 x 3 * (-Dl x + (1 - oblX6 x 3) * oblX2 x 5) - oblX2 x 3 * (Dl x - (1 - oblX6 x 3) * (1 - oblX0 x 5)) := by ring
        rw [hstep]
        have hid : -det24 x * -1 * ((oblX0 x 3 * (-Dl x + (1 - oblX6 x 3) * oblX2 x 5) -
            oblX2 x 3 * (Dl x - (1 - oblX6 x 3) * (1 - oblX0 x 5))) * det24 x) =
            oblX0 x 3 * (-Dl x + (1 - oblX6 x 3) * oblX2 x 5 + oblX2 x 3 * oblX6 x 5) * (det24 x * det24 x) := by
          rw [hD_def]; ring
        rw [hid]
        exact mul_pos (mul_pos ha3 (by nlinarith)) hdet_sq
    · have hj23 : j = 2 ∨ j = 3 := by
        rcases hj with rfl | rfl
        · left; rfl
        · right; rfl
      refine ⟨1, Or.inl ?_, Or.inl ?_⟩
      · rcases hj23 with rfl | rfl
        · change 0 < 1 * ⟪x 3 - x 1, ustar x⟫; rw [one_mul]; exact hz3.1
        · change 0 < 1 * ⟪x 5 - x 1, ustar x⟫; rw [one_mul]; exact hz5.1
      · show 0 < -det24 x * 1 * det3 (x 5 - x 3) (x 3 - x 6) (ustar x)
        have h53 : x 5 - x 3 = (oblX0 x 5 - oblX0 x 3) • (x 0 - x 1) +
            (oblX2 x 5 - oblX2 x 3) • (x 2 - x 1) + (oblX6 x 5 - oblX6 x 3) • (x 6 - x 1) := by
          rw [show x 5 - x 3 = (x 5 - x 1) - (x 3 - x 1) by module, hrep 5, hrep 3]; module
        have h36 : x 3 - x 6 = oblX0 x 3 • (x 0 - x 1) + oblX2 x 3 • (x 2 - x 1) +
            (oblX6 x 3 - 1) • (x 6 - x 1) := by
          rw [show x 3 - x 6 = (x 3 - x 1) - (x 6 - x 1) by module, hrep 3]; module
        rw [h53, h36, hus_rep, det3_frame24]
        have e5 := eq5 F
        have hD_def : Dl x = (1 - oblX6 x 3) * (1 - oblX0 x 5) - oblX0 x 3 * oblX6 x 5 := rfl
        have hid : -((oblX0 x 5 - oblX0 x 3) * (oblX2 x 3 * ((1 - oblX6 x 3) * oblX6 x 5) -
              (oblX6 x 3 - 1) * (-Dl x + (1 - oblX6 x 3) * oblX2 x 5)) -
            (oblX2 x 5 - oblX2 x 3) * (oblX0 x 3 * ((1 - oblX6 x 3) * oblX6 x 5) -
              (oblX6 x 3 - 1) * (Dl x - (1 - oblX6 x 3) * (1 - oblX0 x 5))) +
            (oblX6 x 5 - oblX6 x 3) * (oblX0 x 3 * (-Dl x + (1 - oblX6 x 3) * oblX2 x 5) -
              oblX2 x 3 * (Dl x - (1 - oblX6 x 3) * (1 - oblX0 x 5)))) -
            (oblX0 x 3 + oblX2 x 3 + omega5 x * (1 - oblX6 x 3)) * oblX6 x 5 *
              (oblX0 x 3 * (1 - oblX6 x 5) - oblX0 x 5 * (1 - oblX6 x 3)) = 0 := by
          rw [hD_def]
          linear_combination (1 - oblX6 x 3) * (oblX0 x 3 * (1 - oblX6 x 5) - oblX0 x 5 * (1 - oblX6 x 3)) * e5
        have hdet : -det24 x * 1 * (((oblX0 x 5 - oblX0 x 3) * (oblX2 x 3 * ((1 - oblX6 x 3) * oblX6 x 5) -
              (oblX6 x 3 - 1) * (-Dl x + (1 - oblX6 x 3) * oblX2 x 5)) -
            (oblX2 x 5 - oblX2 x 3) * (oblX0 x 3 * ((1 - oblX6 x 3) * oblX6 x 5) -
              (oblX6 x 3 - 1) * (Dl x - (1 - oblX6 x 3) * (1 - oblX0 x 5))) +
            (oblX6 x 5 - oblX6 x 3) * (oblX0 x 3 * (-Dl x + (1 - oblX6 x 3) * oblX2 x 5) -
              oblX2 x 3 * (Dl x - (1 - oblX6 x 3) * (1 - oblX0 x 5)))) * det24 x) =
            (oblX0 x 3 + oblX2 x 3 + omega5 x * (1 - oblX6 x 3)) * oblX6 x 5 *
              (oblX0 x 3 * (1 - oblX6 x 5) - oblX0 x 5 * (1 - oblX6 x 3)) * (det24 x * det24 x) := by
          linear_combination (det24 x * det24 x) * hid
        rw [hdet]
        have hfac1 : 0 < oblX0 x 3 + oblX2 x 3 + omega5 x * (1 - oblX6 x 3) := by
          have : 0 < omega5 x * (1 - oblX6 x 3) := mul_pos hom5 hc3_pos
          linarith
        exact mul_pos (mul_pos (mul_pos hfac1 hc5) hrow) hdet_sq
    · have hj34 : j = 3 ∨ j = 4 := by
        rcases hj with rfl | rfl
        · left; rfl
        · right; rfl
      refine ⟨1, Or.inl ?_, Or.inl ?_⟩
      · rcases hj34 with rfl | rfl
        · change 0 < 1 * ⟪x 5 - x 1, ustar x⟫; rw [one_mul]; exact hz5.1
        · change 0 < 1 * ⟪x 2 - x 1, ustar x⟫; rw [one_mul]; exact hz2.1
      · show 0 < -det24 x * 1 * det3 (x 2 - x 5) (x 3 - x 6) (ustar x)
        have h25 : x 2 - x 5 = (-oblX0 x 5) • (x 0 - x 1) +
            (1 - oblX2 x 5) • (x 2 - x 1) + (-oblX6 x 5) • (x 6 - x 1) := by
          rw [show x 2 - x 5 = (x 2 - x 1) - (x 5 - x 1) by module, hrep 5]; module
        have h36 : x 3 - x 6 = oblX0 x 3 • (x 0 - x 1) + oblX2 x 3 • (x 2 - x 1) +
            (oblX6 x 3 - 1) • (x 6 - x 1) := by
          rw [show x 3 - x 6 = (x 3 - x 1) - (x 6 - x 1) by module, hrep 3]; module
        rw [h25, h36, hus_rep, det3_frame24]
        have e5 := eq5 F
        have hD_def : Dl x = (1 - oblX6 x 3) * (1 - oblX0 x 5) - oblX0 x 3 * oblX6 x 5 := rfl
        have hid : -((-oblX0 x 5 * (oblX2 x 3 * ((1 - oblX6 x 3) * oblX6 x 5) -
              (oblX6 x 3 - 1) * (-Dl x + (1 - oblX6 x 3) * oblX2 x 5)) -
            (1 - oblX2 x 5) * (oblX0 x 3 * ((1 - oblX6 x 3) * oblX6 x 5) -
              (oblX6 x 3 - 1) * (Dl x - (1 - oblX6 x 3) * (1 - oblX0 x 5))) +
            -oblX6 x 5 * (oblX0 x 3 * (-Dl x + (1 - oblX6 x 3) * oblX2 x 5) -
              oblX2 x 3 * (Dl x - (1 - oblX6 x 3) * (1 - oblX0 x 5))))) -
            (oblX0 x 5 * (1 - oblX6 x 3) + oblX0 x 3 * oblX6 x 5) * oblX6 x 5 *
              (oblX0 x 3 + oblX2 x 3 + omega5 x * (1 - oblX6 x 3)) = 0 := by
          rw [hD_def]
          linear_combination (1 - oblX6 x 3) * (oblX0 x 5 * (1 - oblX6 x 3) + oblX0 x 3 * oblX6 x 5) * e5
        have hdet : -det24 x * 1 * (((-oblX0 x 5 * (oblX2 x 3 * ((1 - oblX6 x 3) * oblX6 x 5) -
              (oblX6 x 3 - 1) * (-Dl x + (1 - oblX6 x 3) * oblX2 x 5)) -
            (1 - oblX2 x 5) * (oblX0 x 3 * ((1 - oblX6 x 3) * oblX6 x 5) -
              (oblX6 x 3 - 1) * (Dl x - (1 - oblX6 x 3) * (1 - oblX0 x 5))) +
            -oblX6 x 5 * (oblX0 x 3 * (-Dl x + (1 - oblX6 x 3) * oblX2 x 5) -
              oblX2 x 3 * (Dl x - (1 - oblX6 x 3) * (1 - oblX0 x 5))))) * det24 x) =
            (oblX0 x 5 * (1 - oblX6 x 3) + oblX0 x 3 * oblX6 x 5) * oblX6 x 5 *
              (oblX0 x 3 + oblX2 x 3 + omega5 x * (1 - oblX6 x 3)) * (det24 x * det24 x) := by
          linear_combination (det24 x * det24 x) * hid
        rw [hdet]
        have hfac1 : 0 < oblX0 x 3 + oblX2 x 3 + omega5 x * (1 - oblX6 x 3) := by
          have : 0 < omega5 x * (1 - oblX6 x 3) := mul_pos hom5 hc3_pos
          linarith
        exact mul_pos (mul_pos (mul_pos (add_pos (mul_pos ha5_pos hc3_pos) (mul_pos ha3 hc5)) hc5) hfac1) hdet_sq
    · have hj4 : j = 4 := by
        rcases hj with rfl | rfl
        · rfl
        · exact absurd rfl hjc
      subst hj4
      refine ⟨1, Or.inl (by change 0 < 1 * ⟪x 2 - x 1, ustar x⟫; rw [one_mul]; exact hz2.1),
        Or.inr ⟨?_, Or.inl ?_⟩⟩
      · show -det24 x * 1 * det3 (x 1 - x 2) (x 3 - x 6) (ustar x) = 0
        have h12 : x 1 - x 2 = (0 : ℝ) • (x 0 - x 1) + (-1 : ℝ) • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) := by module
        have h36 : x 3 - x 6 = oblX0 x 3 • (x 0 - x 1) + oblX2 x 3 • (x 2 - x 1) +
            (oblX6 x 3 - 1) • (x 6 - x 1) := by
          rw [show x 3 - x 6 = (x 3 - x 1) - (x 6 - x 1) by module, hrep 3]; module
        rw [h12, h36, hus_rep, det3_frame24]
        have hD_def : Dl x = (1 - oblX6 x 3) * (1 - oblX0 x 5) - oblX0 x 3 * oblX6 x 5 := rfl
        rw [hD_def]; ring
      · show 0 < -det24 x * 1 * det3 (x 1 - x 2) (x 3 - x 6) (dstar x)
        have h12 : x 1 - x 2 = (0 : ℝ) • (x 0 - x 1) + (-1 : ℝ) • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) := by module
        have h36 : x 3 - x 6 = oblX0 x 3 • (x 0 - x 1) + oblX2 x 3 • (x 2 - x 1) +
            (oblX6 x 3 - 1) • (x 6 - x 1) := by
          rw [show x 3 - x 6 = (x 3 - x 1) - (x 6 - x 1) by module, hrep 3]; module
        rw [h12, h36, hd_rep, det3_frame24]
        rw [show -det24 x * 1 * ((0 * (oblX2 x 3 * 0 - (oblX6 x 3 - 1) * 2) - -1 * (oblX0 x 3 * 0 - (oblX6 x 3 - 1) * -3) +
          0 * (oblX0 x 3 * 2 - oblX2 x 3 * -3)) * det24 x) = 3 * (1 - oblX6 x 3) * (det24 x * det24 x) by ring]
        exact mul_pos (mul_pos (by norm_num) hc3_pos) hdet_sq

theorem isRupert_of_Ustar {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (ha5 : oblX0 x 5 < 1) (hc3 : oblX6 x 3 < 1) (hD : Dl x < 0)
    (h8 : ⟪F.N 8, ustar x⟫ < 0)
    (hz : max 0 ⟪x 6 - x 1, ustar x⟫ <
      min ⟪x 2 - x 1, ustar x⟫ (min ⟪x 3 - x 1, ustar x⟫ ⟪x 5 - x 1, ustar x⟫)) :
    IsRupert (univ.image x) := by
  have hS := splitAny24_Ustar F hC ha5 hc3 hD h8 hz
  exact splitAny24_isRupert F hS

theorem splitAny24_Ustar_twin {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn (x ∘ pi24)) (ha5 : oblX0 (x ∘ pi24) 5 < 1) (hc3 : oblX6 (x ∘ pi24) 3 < 1)
    (hD : Dl (x ∘ pi24) < 0)
    (h8 : ⟪(sym24 F).N 8, ustar (x ∘ pi24)⟫ < 0)
    (hz : max 0 ⟪(x ∘ pi24) 6 - (x ∘ pi24) 1, ustar (x ∘ pi24)⟫ <
      min ⟪(x ∘ pi24) 2 - (x ∘ pi24) 1, ustar (x ∘ pi24)⟫
        (min ⟪(x ∘ pi24) 3 - (x ∘ pi24) 1, ustar (x ∘ pi24)⟫
             ⟪(x ∘ pi24) 5 - (x ∘ pi24) 1, ustar (x ∘ pi24)⟫)) :
    SplitAny24 F :=
  splitAny24_sym F (splitAny24_Ustar (sym24 F) hC ha5 hc3 hD h8 hz)

/-! ### Part 2: `e25_bound`, `e25_w05`, and `e25b` -/

theorem e25_bound {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (hb5 : 1 < oblX2 x 5) (h8 : F.f 8 (x 2) < F.f 8 (x 5)) :
    FrontDiag (x 0) (x 3) (x 5) (x 6) (x 5 - x 2) := by
  have T := type24OfFac F
  have hom3 : 0 < omega3 x := hC.1
  have hom5 : 0 < omega5 x := hC.2.2.1
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have ha5 : 0 < oblX0 x 5 := T.X0_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have h75_pos : 0 < oblX0 x 5 * (1 + omega3 x) - oblX6 x 5 * (1 + omega5 x) := by
    have hf7_0 : F.f 7 (x 0) = (1 + omega3 x) * F.f 7 (x 1) := by
      have ev7_3 := fac_eval F 7 3
      rw [F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at ev7_3
      have e3 := eq3 F
      have h7_id : oblX0 x 3 * (F.f 7 (x 0) - (1 + omega3 x) * F.f 7 (x 1)) = 0 := by
        linear_combination -ev7_3 + F.f 7 (x 1) * e3
      exact sub_eq_zero.mp ((mul_eq_zero.mp h7_id).resolve_left ha3.ne')
    have ev7_5 := fac_eval F 7 5
    rw [F.zero 7 2 (by decide), F.zero 7 6 (by decide), hf7_0] at ev7_5
    have e5 := eq5 F
    have h75_id : F.f 7 (x 5) = (oblX0 x 5 * (1 + omega3 x) - oblX6 x 5 * (1 + omega5 x)) * F.f 7 (x 1) := by
      linear_combination ev7_5 - F.f 7 (x 1) * e5
    have h71 : F.f 7 (x 1) < 0 := F.neg 7 1 (by decide)
    have h75 : F.f 7 (x 5) < 0 := F.neg 7 5 (by decide)
    nlinarith
  let num_l : ℝ := oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1
  let num_1l : ℝ := oblX0 x 3 * (oblX0 x 5 * (1 + omega3 x) - oblX6 x 5 * (1 + omega5 x))
  let den : ℝ := num_l + num_1l
  have hnum_l : 0 < num_l := by dsimp [num_l]; linarith
  have hnum_1l : 0 < num_1l := mul_pos ha3 h75_pos
  have hden : 0 < den := add_pos hnum_l hnum_1l
  let l : ℝ := num_l / den
  let m : ℝ := (oblX2 x 3 * (oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1) -
      num_l * 0 + (oblX2 x 5 - 1) * (oblX0 x 3 * (oblX6 x 5 + oblX0 x 5))) / den
  -- Actually let's use the exact `m` and `γ` from `(1 - l) x0 + l x3 = (1 - m) x5 + m x6 + γ (x5 - x2)`:
  -- From `e2` and `e0`: `m = (l * b3 * (1 - b5?))` - wait, let's solve in `(e0, e2, e6)`:
  -- `(1 - l) e0 + l (a3 e0 + b3 e2 + c3 e6) = (1 - m) (a5 e0 + b5 e2 + c5 e6) + m e6 + γ (a5 e0 + (b5 - 1) e2 + c5 e6)`
  -- Let `s = 1 - m + γ`, so `s * a5 = 1 - l + l * a3`, `s * b5 - γ = l * b3`, `s * c5 + m = l * c3`.
  -- Actually `l * (b5 * c3 - c5 * b3)`? Let's write `γ` and `m` directly:
  have hrep : ∀ v : Fin 7, x v - x 1 =
      oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1) := by
    intro v; rw [T.rep v]; abel
  let s : ℝ := (1 - l + l * oblX0 x 3) / oblX0 x 5
  let gam : ℝ := s * oblX2 x 5 - l * oblX2 x 3
  let m' : ℝ := l * oblX6 x 3 - s * oblX6 x 5
  have hl_pos : 0 < l := div_pos hnum_l hden
  have hl_lt : l < 1 := by
    rw [div_lt_one hden]; dsimp [den]; linarith
  have h01 : (1 - l) • (x 0 - x 1) + l • (x 3 - x 1) =
      (1 - m') • (x 5 - x 1) + m' • (x 6 - x 1) + gam • ((x 5 - x 1) - (x 2 - x 1)) := by
    rw [hrep 3, hrep 5]
    have ha5_ne : oblX0 x 5 ≠ 0 := ha5.ne'
    have hs_sum : 1 - m' + gam = s := by
      dsimp [m', gam]
      have he3 := eq3 F
      have he5 := eq5 F
      have h1l : 1 - l = num_1l / den := by
        dsimp [l, den]; field_simp [hden.ne']; ring
      have hs_eq : s = oblX0 x 3 * (1 + omega3 x) / den := by
        dsimp [s]
        rw [h1l]; dsimp [l]
        field_simp [ha5_ne, hden.ne']
        dsimp [den, num_1l, num_l]
        linear_combination oblX0 x 3 * he5
      rw [hs_eq]; dsimp [l]
      rw [← sub_eq_zero]
      field_simp [hden.ne']
      dsimp [den, num_1l, num_l]
      linear_combination oblX0 x 3 * he5 - (oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1) * he3
    have hs0 : (1 - l + l * oblX0 x 3) - (1 - m' + gam) * oblX0 x 5 = 0 := by
      rw [hs_sum]; dsimp [s]; field_simp [ha5_ne]; ring
    have hs2 : l * oblX2 x 3 - ((1 - m' + gam) * oblX2 x 5 - gam) = 0 := by
      rw [hs_sum]; dsimp [gam]; ring
    have hs6 : l * oblX6 x 3 - ((1 - m' + gam) * oblX6 x 5 + m') = 0 := by
      rw [hs_sum]; dsimp [m']; ring
    have hlin : ((1 - l + l * oblX0 x 3) - (1 - m' + gam) * oblX0 x 5) • (x 0 - x 1) +
        (l * oblX2 x 3 - ((1 - m' + gam) * oblX2 x 5 - gam)) • (x 2 - x 1) +
        (l * oblX6 x 3 - ((1 - m' + gam) * oblX6 x 5 + m')) • (x 6 - x 1) = 0 := by
      rw [hs0, hs2, hs6, zero_smul, zero_smul, zero_smul, add_zero, add_zero]
    rw [← sub_eq_zero]
    have hsub : ((1 - l) • (x 0 - x 1) + l • (oblX0 x 3 • (x 0 - x 1) + oblX2 x 3 • (x 2 - x 1) + oblX6 x 3 • (x 6 - x 1))) -
        ((1 - m') • (oblX0 x 5 • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) + oblX6 x 5 • (x 6 - x 1)) +
          m' • (x 6 - x 1) + gam • (oblX0 x 5 • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) + oblX6 x 5 • (x 6 - x 1) - (x 2 - x 1))) =
        ((1 - l + l * oblX0 x 3) - (1 - m' + gam) * oblX0 x 5) • (x 0 - x 1) +
        (l * oblX2 x 3 - ((1 - m' + gam) * oblX2 x 5 - gam)) • (x 2 - x 1) +
        (l * oblX6 x 3 - ((1 - m' + gam) * oblX6 x 5 + m')) • (x 6 - x 1) := by
      module
    rw [hsub, hlin]
  have heq : (1 - l) • x 0 + l • x 3 = (1 - m') • x 5 + m' • x 6 + gam • (x 5 - x 2) := by
    have hshift : ((1 - l) • x 0 + l • x 3) - ((1 - m') • x 5 + m' • x 6 + gam • (x 5 - x 2)) =
        ((1 - l) • (x 0 - x 1) + l • (x 3 - x 1)) -
        ((1 - m') • (x 5 - x 1) + m' • (x 6 - x 1) + gam • ((x 5 - x 1) - (x 2 - x 1))) := by
      module
    rw [← sub_eq_zero, hshift, h01, sub_self]
  have hfac_eval : ∀ t : Fin 9, (1 - l) * F.f t (x 0) + l * F.f t (x 3) =
      (1 - m') * F.f t (x 5) + m' * F.f t (x 6) + gam * (F.f t (x 5) - F.f t (x 2)) := by
    intro t
    have h := congrArg (fun v => ⟪F.N t, v⟫) h01
    rw [show x 5 - x 1 - (x 2 - x 1) = x 5 - x 2 by module] at h
    simp only [inner_add_right, inner_smul_right] at h
    rw [← F.hN t (x 0) (x 1), ← F.hN t (x 3) (x 1), ← F.hN t (x 5) (x 1),
      ← F.hN t (x 6) (x 1), ← F.hN t (x 5) (x 2)] at h
    linarith
  have hm_pos : 0 < m' := by
    have hf2 := hfac_eval 2
    rw [F.zero 2 0 (by decide), F.zero 2 5 (by decide), F.zero 2 2 (by decide)] at hf2
    have h23 : F.f 2 (x 3) < 0 := F.neg 2 3 (by decide)
    have h26 : F.f 2 (x 6) < 0 := F.neg 2 6 (by decide)
    nlinarith
  have hgam_pos : 0 < gam := by
    have hf3 := hfac_eval 3
    rw [F.zero 3 0 (by decide), F.zero 3 3 (by decide), F.zero 3 5 (by decide)] at hf3
    have h36 : F.f 3 (x 6) < 0 := F.neg 3 6 (by decide)
    have h32 : F.f 3 (x 2) < 0 := F.neg 3 2 (by decide)
    nlinarith
  have hm_lt : m' < 1 := by
    have hf8 := hfac_eval 8
    rw [F.zero 8 3 (by decide), F.zero 8 6 (by decide)] at hf8
    have h80 : F.f 8 (x 0) < 0 := F.neg 8 0 (by decide)
    have h85 : F.f 8 (x 5) < 0 := F.neg 8 5 (by decide)
    nlinarith
  refine ⟨l, m', gam, hl_pos.le, hl_lt.le, hm_pos.le, hm_lt.le, hgam_pos, ?_⟩
  have hre : x 0 + l • (x 3 - x 0) - (x 5 + m' • (x 6 - x 5)) =
      ((1 - l) • x 0 + l • x 3) - ((1 - m') • x 5 + m' • x 6) := by module
  rw [hre, heq]; module

theorem e25_w05 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (hb5 : 1 < oblX2 x 5) (h8 : F.f 8 (x 2) < F.f 8 (x 5))
    (hmax : max ⟪x 0, x 5 - x 2⟫ ⟪x 3, x 5 - x 2⟫ ≤ min ⟪x 5, x 5 - x 2⟫ ⟪x 6, x 5 - x 2⟫) :
    False := by
  have hf := e25_bound F hC hb5 h8
  have hu_ne : x 5 - x 2 ≠ 0 := by
    intro h
    have h3 : ⟪F.N 3, x 5 - x 2⟫ = 0 := by rw [h, inner_zero_right]
    rw [← F.hN 3 (x 5) (x 2), F.zero 3 5 (by decide), zero_sub] at h3
    exact (F.neg 3 2 (by decide)).ne (by linarith)
  exact hf.not_back hu_ne hmax

theorem e25b {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hb5 : oblX2 x 5 < 1) :
    FrontDiag (x 0) (x 6) (x 1) (x 3) (x 5 - x 2) := by
  have T := type24OfFac F
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hb3 : 0 < oblX2 x 3 := T.X2_pos (v := 3) (by decide)
  have hc3 : 0 < oblX6 x 3 := T.X6_pos (v := 3) (by decide)
  have ha5 : 0 < oblX0 x 5 := T.X0_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have h1b5 : 0 < 1 - oblX2 x 5 := sub_pos.mpr hb5
  let num_1l : ℝ := oblX0 x 3 * (1 - oblX2 x 5) + oblX0 x 5 * oblX2 x 3
  let num_l : ℝ := oblX6 x 3 * (1 - oblX2 x 5) + oblX6 x 5 * oblX2 x 3
  let den : ℝ := num_1l + num_l
  have h1l_pos : 0 < num_1l := add_pos (mul_pos ha3 h1b5) (mul_pos ha5 hb3)
  have hl_num_pos : 0 < num_l := add_pos (mul_pos hc3 h1b5) (mul_pos hc5 hb3)
  have hden : 0 < den := add_pos h1l_pos hl_num_pos
  let l : ℝ := num_l / den
  let m' : ℝ := (1 - oblX2 x 5) / den
  let gam : ℝ := oblX2 x 3 / den
  have hl_pos : 0 < l := div_pos hl_num_pos hden
  have hl_lt : l < 1 := by rw [div_lt_one hden]; dsimp [den]; linarith
  have hm_pos : 0 < m' := div_pos h1b5 hden
  have hgam_pos : 0 < gam := div_pos hb3 hden
  have hrep : ∀ v : Fin 7, x v - x 1 =
      oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1) := by
    intro v; rw [T.rep v]; abel
  have h01 : (1 - l) • (x 0 - x 1) + l • (x 6 - x 1) =
      m' • (x 3 - x 1) + gam • (x 5 - x 2) := by
    have h52 : x 5 - x 2 = (x 5 - x 1) - (x 2 - x 1) := by module
    rw [h52, hrep 3, hrep 5]
    have h1l : 1 - l = num_1l / den := by
      dsimp [l, den]; field_simp [hden.ne']; ring
    have hs0 : (1 - l) - (m' * oblX0 x 3 + gam * oblX0 x 5) = 0 := by
      rw [h1l]; dsimp [num_1l, m', gam]; field_simp [hden.ne']; ring
    have hs2 : m' * oblX2 x 3 + gam * (oblX2 x 5 - 1) = 0 := by
      dsimp [m', gam]; field_simp [hden.ne']; ring
    have hs6 : l - (m' * oblX6 x 3 + gam * oblX6 x 5) = 0 := by
      dsimp [l, m', gam]; field_simp [hden.ne']; ring
    have hlin : ((1 - l) - (m' * oblX0 x 3 + gam * oblX0 x 5)) • (x 0 - x 1) +
        (-(m' * oblX2 x 3 + gam * (oblX2 x 5 - 1))) • (x 2 - x 1) +
        (l - (m' * oblX6 x 3 + gam * oblX6 x 5)) • (x 6 - x 1) = 0 := by
      rw [hs0, hs2, hs6, neg_zero, zero_smul, zero_smul, zero_smul, add_zero, add_zero]
    rw [← sub_eq_zero]
    have hsub : ((1 - l) • (x 0 - x 1) + l • (x 6 - x 1)) -
        (m' • (oblX0 x 3 • (x 0 - x 1) + oblX2 x 3 • (x 2 - x 1) + oblX6 x 3 • (x 6 - x 1)) +
          gam • (oblX0 x 5 • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) + oblX6 x 5 • (x 6 - x 1) - (x 2 - x 1))) =
        ((1 - l) - (m' * oblX0 x 3 + gam * oblX0 x 5)) • (x 0 - x 1) +
        (-(m' * oblX2 x 3 + gam * (oblX2 x 5 - 1))) • (x 2 - x 1) +
        (l - (m' * oblX6 x 3 + gam * oblX6 x 5)) • (x 6 - x 1) := by
      module
    rw [hsub, hlin]
  have heq : (1 - l) • x 0 + l • x 6 = (1 - m') • x 1 + m' • x 3 + gam • (x 5 - x 2) := by
    have hshift : ((1 - l) • x 0 + l • x 6) - ((1 - m') • x 1 + m' • x 3 + gam • (x 5 - x 2)) =
        ((1 - l) • (x 0 - x 1) + l • (x 6 - x 1)) - (m' • (x 3 - x 1) + gam • (x 5 - x 2)) := by
      module
    rw [← sub_eq_zero, hshift, h01, sub_self]
  have hm_lt : m' < 1 := by
    have hf6 := congrArg (fun v => ⟪F.N 6, v⟫) h01
    simp only [inner_add_right, inner_smul_right] at hf6
    rw [← F.hN 6 (x 0) (x 1), ← F.hN 6 (x 6) (x 1), ← F.hN 6 (x 3) (x 1),
      ← F.hN 6 (x 5) (x 2)] at hf6
    rw [F.zero 6 3 (by decide), F.zero 6 5 (by decide), F.zero 6 2 (by decide)] at hf6
    have h60 : F.f 6 (x 0) < 0 := F.neg 6 0 (by decide)
    have h66 : F.f 6 (x 6) < 0 := F.neg 6 6 (by decide)
    have h61 : F.f 6 (x 1) < 0 := F.neg 6 1 (by decide)
    nlinarith
  refine ⟨l, m', gam, hl_pos.le, hl_lt.le, hm_pos.le, hm_lt.le, hgam_pos, ?_⟩
  have hre : x 0 + l • (x 6 - x 0) - (x 1 + m' • (x 3 - x 1)) =
      ((1 - l) • x 0 + l • x 6) - ((1 - m') • x 1 + m' • x 3) := by module
  rw [hre, heq]; module

/-! ### Part 3: `u27_bound` and `z5_gt_z4_w05` -/

theorem u27_bound {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) :
    FrontDiag (x 2) (x 4) (x 0) (x 6) (u27 x) := by
  have T := type24OfFac F
  have hom3 : 0 < omega3 x := hC.1
  have hom4 : 0 < omega4 x := hC.2.1
  have hom5 : 0 < omega5 x := hC.2.2.1
  have hD24 : 0 ≤ Delta24 x := hC.2.2.2
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  let den : ℝ := (1 + omega3 x) * (1 + omega5 x) + oblX2 x 4 * Delta24 x
  have hden : 0 < den := by
    have h1 : 0 < (1 + omega3 x) * (1 + omega5 x) := mul_pos (by linarith) (by linarith)
    have h2 : 0 ≤ oblX2 x 4 * Delta24 x := mul_nonneg hb4.le hD24
    linarith
  let l : ℝ := (1 + omega3 x) * (1 + omega5 x) / den
  let gam : ℝ := oblX2 x 4 * (1 + omega4 x) / den
  let m' : ℝ := (1 + omega3 x) * (oblX6 x 4 * (1 + omega5 x) - oblX2 x 4 * (1 + omega4 x)) / den
  have hl_pos : 0 < l := div_pos (mul_pos (by linarith) (by linarith)) hden
  have hl_lt : l ≤ 1 := by
    rw [div_le_one hden]; dsimp [den]
    linarith [mul_nonneg hb4.le hD24]
  have hgam_pos : 0 < gam := div_pos (mul_pos hb4 (by linarith)) hden
  have hrep : ∀ v : Fin 7, x v - x 1 =
      oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1) := by
    intro v; rw [T.rep v]; abel
  have h01 : (1 - l) • (x 2 - x 1) + l • (x 4 - x 1) =
      (1 - m') • (x 0 - x 1) + m' • (x 6 - x 1) + gam • u27 x := by
    rw [hrep 4]; dsimp [u27]
    have e4 := eq4 F
    have hD_def : Delta24 x = omega3 x * omega4 x * omega5 x - omega3 x - omega4 x - omega5 x - 2 := rfl
    have h1l : 1 - l = oblX2 x 4 * Delta24 x / den := by
      dsimp [l, den]; field_simp [hden.ne']; ring
    have h1m : 1 - m' = (1 + omega5 x) * (oblX0 x 4 * (1 + omega3 x) - oblX2 x 4 * (1 + omega4 x)) / den := by
      dsimp [m', den]
      field_simp [hden.ne']
      linear_combination -(1 + omega3 x) * (1 + omega5 x) * e4 + oblX2 x 4 * hD_def
    have hs0 : l * oblX0 x 4 - ((1 - m') + gam * (1 + omega5 x)) = 0 := by
      rw [h1m]; dsimp [l, gam]; field_simp [hden.ne']; ring
    have hs2 : (1 - l + l * oblX2 x 4) - gam * (omega3 x * omega5 x - 1) = 0 := by
      rw [h1l]; dsimp [l, gam]; field_simp [hden.ne']
      rw [hD_def]; ring
    have hs6 : l * oblX6 x 4 - (m' + gam * (1 + omega3 x)) = 0 := by
      dsimp [l, m', gam]; field_simp [hden.ne']; ring
    have hlin : (l * oblX0 x 4 - ((1 - m') + gam * (1 + omega5 x))) • (x 0 - x 1) +
        ((1 - l + l * oblX2 x 4) - gam * (omega3 x * omega5 x - 1)) • (x 2 - x 1) +
        (l * oblX6 x 4 - (m' + gam * (1 + omega3 x))) • (x 6 - x 1) = 0 := by
      rw [hs0, hs2, hs6, zero_smul, zero_smul, zero_smul, add_zero, add_zero]
    rw [← sub_eq_zero]
    have hsub : ((1 - l) • (x 2 - x 1) + l • (oblX0 x 4 • (x 0 - x 1) + oblX2 x 4 • (x 2 - x 1) + oblX6 x 4 • (x 6 - x 1))) -
        ((1 - m') • (x 0 - x 1) + m' • (x 6 - x 1) + gam • ((1 + omega5 x) • (x 0 - x 1) +
          (omega3 x * omega5 x - 1) • (x 2 - x 1) + (1 + omega3 x) • (x 6 - x 1))) =
        (l * oblX0 x 4 - ((1 - m') + gam * (1 + omega5 x))) • (x 0 - x 1) +
        ((1 - l + l * oblX2 x 4) - gam * (omega3 x * omega5 x - 1)) • (x 2 - x 1) +
        (l * oblX6 x 4 - (m' + gam * (1 + omega3 x))) • (x 6 - x 1) := by
      module
    rw [hsub, hlin]
  have heq : (1 - l) • x 2 + l • x 4 = (1 - m') • x 0 + m' • x 6 + gam • u27 x := by
    have hshift : ((1 - l) • x 2 + l • x 4) - ((1 - m') • x 0 + m' • x 6 + gam • u27 x) =
        ((1 - l) • (x 2 - x 1) + l • (x 4 - x 1)) -
        ((1 - m') • (x 0 - x 1) + m' • (x 6 - x 1) + gam • u27 x) := by
      module
    rw [← sub_eq_zero, hshift, h01, sub_self]
  have hm_pos : 0 < m' := by
    have hf2_6 : F.f 2 (x 6) = (1 + omega5 x) * F.f 2 (x 1) := by
      have ev2_5 := fac_eval F 2 5
      rw [F.zero 2 5 (by decide), F.zero 2 0 (by decide), F.zero 2 2 (by decide)] at ev2_5
      have e5 := eq5 F
      have hc5 : oblX6 x 5 ≠ 0 := (T.X6_pos (v := 5) (by decide)).ne'
      have h2_id : oblX6 x 5 * (F.f 2 (x 6) - (1 + omega5 x) * F.f 2 (x 1)) = 0 := by
        linear_combination -ev2_5 + F.f 2 (x 1) * e5
      exact sub_eq_zero.mp ((mul_eq_zero.mp h2_id).resolve_left hc5)
    have ev2_4 := fac_eval F 2 4
    rw [F.zero 2 0 (by decide), F.zero 2 2 (by decide), hf2_6] at ev2_4
    have e4 := eq4 F
    have h24_id : F.f 2 (x 4) = (oblX6 x 4 * (1 + omega5 x) - oblX2 x 4 * (1 + omega4 x)) * F.f 2 (x 1) := by
      linear_combination ev2_4 - F.f 2 (x 1) * e4
    have h21 : F.f 2 (x 1) < 0 := F.neg 2 1 (by decide)
    have h24 : F.f 2 (x 4) < 0 := F.neg 2 4 (by decide)
    have hc4_pos : 0 < oblX6 x 4 * (1 + omega5 x) - oblX2 x 4 * (1 + omega4 x) := by nlinarith
    dsimp [m']
    exact div_pos (mul_pos (by linarith) hc4_pos) hden
  have hm_lt : m' < 1 := by
    have hf7_0 : F.f 7 (x 0) = (1 + omega3 x) * F.f 7 (x 1) := by
      have ev7_3 := fac_eval F 7 3
      rw [F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at ev7_3
      have e3 := eq3 F
      have ha3 : oblX0 x 3 ≠ 0 := (T.X0_pos (v := 3) (by decide)).ne'
      have h7_id : oblX0 x 3 * (F.f 7 (x 0) - (1 + omega3 x) * F.f 7 (x 1)) = 0 := by
        linear_combination -ev7_3 + F.f 7 (x 1) * e3
      exact sub_eq_zero.mp ((mul_eq_zero.mp h7_id).resolve_left ha3)
    have ev7_4 := fac_eval F 7 4
    rw [F.zero 7 2 (by decide), F.zero 7 6 (by decide), hf7_0] at ev7_4
    have e4 := eq4 F
    have h74_id : F.f 7 (x 4) = (oblX0 x 4 * (1 + omega3 x) - oblX2 x 4 * (1 + omega4 x)) * F.f 7 (x 1) := by
      linear_combination ev7_4 - F.f 7 (x 1) * e4
    have h71 : F.f 7 (x 1) < 0 := F.neg 7 1 (by decide)
    have h74 : F.f 7 (x 4) < 0 := F.neg 7 4 (by decide)
    have ha4_pos : 0 < oblX0 x 4 * (1 + omega3 x) - oblX2 x 4 * (1 + omega4 x) := by nlinarith
    have h1m : 1 - m' = (1 + omega5 x) * (oblX0 x 4 * (1 + omega3 x) - oblX2 x 4 * (1 + omega4 x)) / den := by
      dsimp [m', den]
      have hD_def : Delta24 x = omega3 x * omega4 x * omega5 x - omega3 x - omega4 x - omega5 x - 2 := rfl
      field_simp [hden.ne']
      linear_combination -(1 + omega3 x) * (1 + omega5 x) * e4 + oblX2 x 4 * hD_def
    have h1m_pos : 0 < 1 - m' := by
      rw [h1m]; exact div_pos (mul_pos (by linarith) ha4_pos) hden
    linarith
  refine ⟨l, m', gam, hl_pos.le, hl_lt, hm_pos.le, hm_lt.le, hgam_pos, ?_⟩
  have hre : x 2 + l • (x 4 - x 2) - (x 0 + m' • (x 6 - x 0)) =
      ((1 - l) • x 2 + l • x 4) - ((1 - m') • x 0 + m' • x 6) := by module
  rw [hre, heq]; module

theorem z5_gt_z4_w05 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (l1 l2 l3 l4 l5 : ℝ)
    (_hl1 : 0 ≤ l1) (_hl2 : 0 ≤ l2) (_hl3 : 0 ≤ l3) (_hl4 : 0 ≤ l4) (_hl5 : 0 ≤ l5)
    (hphi : 0 < l1 * (-F.f 3 (x 2)) + l2 * (-F.f 7 (x 5)) + l3 * (-F.f 1 (x 5)) +
      l4 * (-F.f 6 (x 0)) + l5 * (-F.f 5 (x 4)))
    (hdz : ⟪x 5 - x 4, x 5 - x 0⟫ =
      l1 * (-F.f 3 (x 2)) + l2 * (-F.f 7 (x 5)) + l3 * (-F.f 1 (x 5)) +
      l4 * (-F.f 6 (x 0)) + l5 * (-F.f 5 (x 4))) :
    ⟪x 4, x 5 - x 0⟫ < ⟪x 5, x 5 - x 0⟫ := by
  have hpos : 0 < ⟪x 5 - x 4, x 5 - x 0⟫ := by linarith
  rw [inner_sub_left] at hpos
  linarith

/-! ### Part 4: `lexAny_or_split_E04P4U` via `Sym24` transport -/

theorem lexAny_or_split_E04P4U {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (ha4 : 1 < oblX0 x 4) (ha5 : oblX0 x 5 < 1)
    (hL4 : 0 ≤ Lam4 x) (h6 : F.f 6 (x 0) ≤ F.f 6 (x 4))
    (hz : ⟪x 5, x 4 - x 0⟫ < ⟪x 4, x 4 - x 0⟫ ∧
          ⟪x 4, x 4 - x 0⟫ < ⟪x 6, x 4 - x 0⟫) :
    LexAny F ∨ SplitAny24 F := by
  have hC' : CbarIn (x ∘ pi24) := (cbarIn_comp_pi24 x).mpr hC
  have ha5' : 1 < oblX0 (x ∘ pi24) 5 := by
    rw [oblX0_comp_pi24]; exact ha4
  have ha4' : oblX0 (x ∘ pi24) 4 < 1 := by
    rw [oblX0_comp_pi24]; exact ha5
  have hL' : 0 ≤ Lam5 (x ∘ pi24) := by
    rw [lam5_comp_pi24]; exact hL4
  have h346' : (sym24 F).f 8 ((x ∘ pi24) 0) ≤ (sym24 F).f 8 ((x ∘ pi24) 5) := by
    simpa [sym24_f_apply] using h6
  have hz' : ⟪(x ∘ pi24) 4, (x ∘ pi24) 5 - (x ∘ pi24) 0⟫ <
              ⟪(x ∘ pi24) 5, (x ∘ pi24) 5 - (x ∘ pi24) 0⟫ ∧
            ⟪(x ∘ pi24) 5, (x ∘ pi24) 5 - (x ∘ pi24) 0⟫ <
              ⟪(x ∘ pi24) 2, (x ∘ pi24) 5 - (x ∘ pi24) 0⟫ := by
    simpa [pi24] using hz
  rcases Minimality.T24.A8.lexAny_or_split_E05P5U (sym24 F) hC' ha5' ha4' hL' h346' hz' with
    hL | hS
  · exact Or.inl (lexAny_sym F hL)
  · exact Or.inr (splitAny24_sym F hS)

end Minimality.T24.A10
