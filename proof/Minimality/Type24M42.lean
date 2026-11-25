module

public import Minimality.Type24HiddenCone
public import Minimality.RimCellClosed
public import Minimality.RDispatch24
public import Minimality.Type24SAT.Geo.Top
public import Minimality.Type24Z0

@[expose] public section

/-!
# EO: the meridian view `M_42 = N_4 × N_2` of the type-24 hidden-cap cover

Formalization of `EOSpec.lean` in module form (Hydrogen Task EO):
- `viewM42`, `FacetCellF`
- Cells `M1, M2, M3`, cycles `cycM1..cycM3`, injectivity `injM1..injM3`
- `(i)` `m42_n4`, `m42_n2`, `m42_signs`, `m42_not_both`
- `(ii)` `m42_cellLe_M1..M3`, `tilt_pp`, `tilt_mp`, `tilt_pm`, `m42_cellAt_M1..M3`
- `(iii)` `Crit`, `isRupert_m42_M1..M3`, `isRupert_m42`
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.EO

open Minimality Minimality.H21 Minimality.T24.SAT Minimality.RimCell Minimality.T24.HC

variable {x : Fin 7 → ℝ³}

/-! ## The view and the facet-cell hypothesis -/

/-- `M_42 = N_4 x N_2 = (ω4 ω5 - 1, ω5 + 1, ω4 + 1)` in corner coordinates. -/
noncomputable def viewM42 (x : Fin 7 → ℝ³) : ℝ³ :=
  capView x (omega4 x * omega5 x - 1) (omega5 x + 1) (omega4 x + 1)

/-- `FacetCell24` in terms of the facet data `F` (some facet `t` faces a view `u` while every facet across an
edge of `t` faces away from it); `Minimality.T24.Z0.nb` is the neighbour table of `FacetCell24`. -/
def FacetCellF (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ t : Fin 9, ∃ u : ℝ³, 0 < ⟪F.N t, u⟫ ∧ ∀ s ∈ Minimality.T24.Z0.nb t, ⟪F.N s, u⟫ < 0

/-! ## Cells and cycles -/

/-- `M1`: up `025, 0345, 046, 235, 346`, down `012, 016, 126, 236`; rim `0 2 3 6`. -/
def UM1 : Finset (Fin 9) := {2, 3, 4, 6, 8}
def DnM1 : Finset (Fin 9) := {0, 1, 5, 7}
def cM1 : ZMod 4 → Fin 7 := ![0, 2, 3, 6]
/-- `M2`: up `025, 0345, 235`, down `012, 016, 046, 126, 236, 346`; rim `0 2 3 4`. -/
def UM2 : Finset (Fin 9) := {2, 3, 6}
def DnM2 : Finset (Fin 9) := {0, 1, 4, 5, 7, 8}
def cM2 : ZMod 4 → Fin 7 := ![0, 2, 3, 4]
/-- `M3`: up `0345, 046, 346`, down `012, 016, 025, 126, 235, 236`; rim `0 5 3 6`. -/
def UM3 : Finset (Fin 9) := {3, 4, 8}
def DnM3 : Finset (Fin 9) := {0, 1, 2, 5, 6, 7}
def cM3 : ZMod 4 → Fin 7 := ![0, 5, 3, 6]

theorem cycM1 : S0xCycUD s0x_S24 cM1 UM1 DnM1 := by decide
theorem cycM2 : S0xCycUD s0x_S24 cM2 UM2 DnM2 := by decide
theorem cycM3 : S0xCycUD s0x_S24 cM3 UM3 DnM3 := by decide

theorem injM1 : Function.Injective cM1 := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)
theorem injM2 : Function.Injective cM2 := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)
theorem injM3 : Function.Injective cM3 := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)

/-! ## (i) The region lemmas (exact sign statements at the single view `M_42`) -/

private lemma fac_eval (F : S0xFac 9 s0x_S24 x) (t : Fin 9) (v : Fin 7) :
    F.f t (x v) = F.f t (x 1) + oblX0 x v * (F.f t (x 0) - F.f t (x 1)) +
      oblX2 x v * (F.f t (x 2) - F.f t (x 1)) + oblX6 x v * (F.f t (x 6) - F.f t (x 1)) := by
  have hv : x v - x 1 = oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1) := by
    have := (Minimality.T24.M4.type24OfFac F).rep v
    rw [sub_eq_iff_eq_add]; rw [this]; abel
  have hi := congrArg (fun w => ⟪F.N t, w⟫) hv
  simp only [inner_add_right, real_inner_smul_right, F.inner_sub] at hi
  linarith

private lemma n4_edge_b (F : S0xFac 9 s0x_S24 x) :
    F.f 4 (x 2) - F.f 4 (x 1) = omega4 x * F.f 4 (x 1) := by
  have T := Minimality.T24.M4.type24OfFac F
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hf4 := fac_eval F 4 4
  rw [F.zero 4 4 (by decide), F.zero 4 0 (by decide), F.zero 4 6 (by decide)] at hf4
  have e4 : oblX0 x 4 + oblX6 x 4 - 1 = omega4 x * oblX2 x 4 := by
    dsimp [omega4]; field_simp [hb4.ne']
  apply mul_left_cancel₀ hb4.ne'; linear_combination -hf4 + F.f 4 (x 1) * e4

private lemma n2_edge_c (F : S0xFac 9 s0x_S24 x) :
    F.f 2 (x 6) - F.f 2 (x 1) = omega5 x * F.f 2 (x 1) := by
  have T := Minimality.T24.M4.type24OfFac F
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hf5 := fac_eval F 2 5
  rw [F.zero 2 5 (by decide), F.zero 2 0 (by decide), F.zero 2 2 (by decide)] at hf5
  have e5 : oblX0 x 5 + oblX2 x 5 - 1 = omega5 x * oblX6 x 5 := by
    dsimp [omega5]; field_simp [hc5.ne']
  apply mul_left_cancel₀ hc5.ne'; linear_combination -hf5 + F.f 2 (x 1) * e5

private lemma n7_edge_a (F : S0xFac 9 s0x_S24 x) :
    F.f 7 (x 0) - F.f 7 (x 1) = omega3 x * F.f 7 (x 1) := by
  have T := Minimality.T24.M4.type24OfFac F
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hf3 := fac_eval F 7 3
  rw [F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at hf3
  have e3 : oblX2 x 3 + oblX6 x 3 - 1 = omega3 x * oblX0 x 3 := by
    dsimp [omega3]; field_simp [ha3.ne']
  apply mul_left_cancel₀ ha3.ne'; linear_combination -hf3 + F.f 7 (x 1) * e3

/-- `046` is edge-on at `M_42`. -/
theorem m42_n4 (F : S0xFac 9 s0x_S24 x) (_hC : CbarIn x) : ⟪F.N 4, viewM42 x⟫ = 0 := by
  simp only [viewM42, capView, inner_add_right, real_inner_smul_right, F.inner_sub,
    F.zero 4 0 (by decide), F.zero 4 6 (by decide), n4_edge_b F]
  ring

/-- `025` is edge-on at `M_42`. -/
theorem m42_n2 (F : S0xFac 9 s0x_S24 x) (_hC : CbarIn x) : ⟪F.N 2, viewM42 x⟫ = 0 := by
  simp only [viewM42, capView, inner_add_right, real_inner_smul_right, F.inner_sub,
    F.zero 2 0 (by decide), F.zero 2 2 (by decide), n2_edge_c F]
  ring

/-- **EO(i), signs.** For `Δ24 > 0`: facets `012, 016, 126, 236` (`0, 1, 5, 7`) strictly back, `0345` (`3`)
strictly front at `M_42`. -/
theorem m42_signs (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hD : 0 < Delta24 x) :
    ⟪F.N 0, viewM42 x⟫ < 0 ∧ ⟪F.N 1, viewM42 x⟫ < 0 ∧ ⟪F.N 5, viewM42 x⟫ < 0 ∧
      ⟪F.N 7, viewM42 x⟫ < 0 ∧ 0 < ⟪F.N 3, viewM42 x⟫ := by
  have hom3 : 0 < omega3 x := hC.1
  have hom4 : 0 < omega4 x := hC.2.1
  have hom5 : 0 < omega5 x := hC.2.2.1
  have hD_eq : Delta24 x = omega3 x * omega4 x * omega5 x - omega3 x - omega4 x - omega5 x - 2 := rfl
  have hom45 : 1 < omega4 x * omega5 x := by nlinarith
  have hca : 0 < omega4 x * omega5 x - 1 := sub_pos.mpr hom45
  have hcb : 0 < omega5 x + 1 := by linarith
  have hcc : 0 < omega4 x + 1 := by linarith
  obtain ⟨h0, h1, h5⟩ := back24_of_cone F _ _ _ hca hcb hcc
  have h7 : ⟪F.N 7, viewM42 x⟫ < 0 := by
    have heq : ⟪F.N 7, viewM42 x⟫ = Delta24 x * F.f 7 (x 1) := by
      simp only [viewM42, capView, inner_add_right, real_inner_smul_right, F.inner_sub,
        F.zero 7 2 (by decide), F.zero 7 6 (by decide), n7_edge_a F, hD_eq]
      ring
    rw [heq]
    exact mul_neg_of_pos_of_neg hD (F.neg 7 1 (by decide))
  have h3 : 0 < ⟪F.N 3, viewM42 x⟫ := by
    have T := Minimality.T24.M4.type24OfFac F
    have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
    have hf34 := fac_eval F 3 4
    rw [F.zero 3 4 (by decide), F.zero 3 0 (by decide)] at hf34
    have e4 : oblX0 x 4 + oblX6 x 4 - 1 = omega4 x * oblX2 x 4 := by
      dsimp [omega4]; field_simp [hb4.ne']
    have hsum34 : oblX2 x 4 * F.f 3 (x 2) + oblX6 x 4 * F.f 3 (x 6) =
        (omega4 x + 1) * oblX2 x 4 * F.f 3 (x 1) := by
      linear_combination -hf34 + F.f 3 (x 1) * e4
    have hf24 := fac_eval F 2 4
    rw [F.zero 2 0 (by decide), F.zero 2 2 (by decide), n2_edge_c F] at hf24
    have h24_neg : F.f 2 (x 4) < 0 := F.neg 2 4 (by decide)
    have h24_val : F.f 2 (x 4) = ((omega5 x + 1) * oblX6 x 4 - (omega4 x + 1) * oblX2 x 4) * F.f 2 (x 1) := by
      linear_combination hf24 - F.f 2 (x 1) * e4
    have h21_neg : F.f 2 (x 1) < 0 := F.neg 2 1 (by decide)
    have hcoeff_neg : (omega4 x + 1) * oblX2 x 4 - (omega5 x + 1) * oblX6 x 4 < 0 := by
      rw [h24_val] at h24_neg
      have hpos : 0 < (omega5 x + 1) * oblX6 x 4 - (omega4 x + 1) * oblX2 x 4 := by nlinarith
      linarith
    have hM3_exp : ⟪F.N 3, viewM42 x⟫ =
        (omega4 x + 1) * (omega5 x + 1) * (-F.f 3 (x 1)) +
          (omega5 x + 1) * F.f 3 (x 2) + (omega4 x + 1) * F.f 3 (x 6) := by
      simp only [viewM42, capView, inner_add_right, real_inner_smul_right, F.inner_sub,
        F.zero 3 0 (by decide)]
      ring
    have hprod : oblX2 x 4 * ⟪F.N 3, viewM42 x⟫ =
        ((omega4 x + 1) * oblX2 x 4 - (omega5 x + 1) * oblX6 x 4) * F.f 3 (x 6) := by
      rw [hM3_exp]
      linear_combination (omega5 x + 1) * hsum34
    have h36_neg : F.f 3 (x 6) < 0 := F.neg 3 6 (by decide)
    have hprod_pos : 0 < oblX2 x 4 * ⟪F.N 3, viewM42 x⟫ := by
      rw [hprod]; exact mul_pos_of_neg_of_neg hcoeff_neg h36_neg
    exact pos_of_mul_pos_right hprod_pos hb4.le
  exact ⟨h0, h1, h5, h7, h3⟩

/-- Tilt `v = x 0 - x 1`: `046` and `025` both strictly front. -/
theorem tilt_pp (F : S0xFac 9 s0x_S24 x) : 0 < ⟪F.N 4, x 0 - x 1⟫ ∧ 0 < ⟪F.N 2, x 0 - x 1⟫ := by
  rw [F.inner_sub, F.inner_sub, F.zero 4 0 (by decide), F.zero 2 0 (by decide)]
  have h4 := F.neg 4 1 (by decide)
  have h2 := F.neg 2 1 (by decide)
  constructor <;> linarith

/-- **EO(i), impossibility lemma.** Outside the facet cells, `235` and `346` are not both strictly back at `M_42`
(exact form: `0 ≤ N_6 . M ∨ 0 ≤ N_8 . M`; the strict form "`0 < N_6 . M ∨ 0 < N_8 . M`" is FALSE in special
position: on the mirror stratum there is a point with `N_6 . M = N_8 . M = 0`, and `N_6 . M = 0 ≥ N_8 . M` is
constructible, see GATE.md).  `¬ FacetCellF F` is necessary: without it the weak form fails on many points. -/
theorem m42_not_both (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hD : 0 < Delta24 x)
    (hfc : ¬ FacetCellF F) : 0 ≤ ⟪F.N 6, viewM42 x⟫ ∨ 0 ≤ ⟪F.N 8, viewM42 x⟫ := by
  by_contra hnot
  push Not at hnot
  obtain ⟨h6, h8⟩ := hnot
  obtain ⟨_, _, _, _, h3⟩ := m42_signs F hC hD
  have e4 := m42_n4 F hC
  have e2 := m42_n2 F hC
  obtain ⟨t4, t2⟩ := tilt_pp F
  let v : ℝ³ := -(x 0 - x 1)
  have hv4 : ⟪F.N 4, v⟫ < 0 := by dsimp [v]; rw [inner_neg_right]; linarith
  have hv2 : ⟪F.N 2, v⟫ < 0 := by dsimp [v]; rw [inner_neg_right]; linarith
  let M := viewM42 x
  let d : ℝ := 1 + |⟪F.N 3, v⟫| + |⟪F.N 6, v⟫| + |⟪F.N 8, v⟫|
  have hd_pos : 0 < d := by
    have : 0 ≤ |⟪F.N 3, v⟫| := abs_nonneg _
    have : 0 ≤ |⟪F.N 6, v⟫| := abs_nonneg _
    have : 0 ≤ |⟪F.N 8, v⟫| := abs_nonneg _
    linarith
  let m : ℝ := min ⟪F.N 3, M⟫ (min (-⟪F.N 6, M⟫) (-⟪F.N 8, M⟫))
  have hm_pos : 0 < m := lt_min h3 (lt_min (neg_pos.mpr h6) (neg_pos.mpr h8))
  let ε : ℝ := m / (2 * d)
  have hε_pos : 0 < ε := div_pos hm_pos (by linarith)
  have hε3 : ε * |⟪F.N 3, v⟫| < ⟪F.N 3, M⟫ := by
    have h1 : ε * |⟪F.N 3, v⟫| ≤ ε * d := mul_le_mul_of_nonneg_left (by
      have := abs_nonneg ⟪F.N 6, v⟫; have := abs_nonneg ⟪F.N 8, v⟫; dsimp [d]; linarith) hε_pos.le
    have h2 : ε * d = m / 2 := by dsimp [ε]; field_simp [hd_pos.ne']
    have h3m : m ≤ ⟪F.N 3, M⟫ := min_le_left _ _
    linarith
  have hε6 : ε * |⟪F.N 6, v⟫| < -⟪F.N 6, M⟫ := by
    have h1 : ε * |⟪F.N 6, v⟫| ≤ ε * d := mul_le_mul_of_nonneg_left (by
      have := abs_nonneg ⟪F.N 3, v⟫; have := abs_nonneg ⟪F.N 8, v⟫; dsimp [d]; linarith) hε_pos.le
    have h2 : ε * d = m / 2 := by dsimp [ε]; field_simp [hd_pos.ne']
    have h6m : m ≤ -⟪F.N 6, M⟫ := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hε8 : ε * |⟪F.N 8, v⟫| < -⟪F.N 8, M⟫ := by
    have h1 : ε * |⟪F.N 8, v⟫| ≤ ε * d := mul_le_mul_of_nonneg_left (by
      have := abs_nonneg ⟪F.N 3, v⟫; have := abs_nonneg ⟪F.N 6, v⟫; dsimp [d]; linarith) hε_pos.le
    have h2 : ε * d = m / 2 := by dsimp [ε]; field_simp [hd_pos.ne']
    have h8m : m ≤ -⟪F.N 8, M⟫ := le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  apply hfc
  refine ⟨3, M + ε • v, ?_, ?_⟩
  · rw [inner_add_right, real_inner_smul_right]
    have := neg_le_abs ⟪F.N 3, v⟫
    nlinarith [abs_nonneg ⟪F.N 3, v⟫, neg_abs_le ⟪F.N 3, v⟫]
  · intro s hs
    have hs' : s = 4 ∨ s = 8 ∨ s = 6 ∨ s = 2 := by
      fin_cases s <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr (Or.inl rfl)) |
        exact Or.inr (Or.inr (Or.inr rfl)) | exact absurd hs (by decide)
    rw [inner_add_right, real_inner_smul_right]
    rcases hs' with rfl | rfl | rfl | rfl
    · rw [show ⟪F.N 4, M⟫ = 0 from e4, zero_add]; exact mul_neg_of_pos_of_neg hε_pos hv4
    · have := le_abs_self ⟪F.N 8, v⟫; nlinarith [abs_nonneg ⟪F.N 8, v⟫]
    · have := le_abs_self ⟪F.N 6, v⟫; nlinarith [abs_nonneg ⟪F.N 6, v⟫]
    · rw [show ⟪F.N 2, M⟫ = 0 from e2, zero_add]; exact mul_neg_of_pos_of_neg hε_pos hv2

/-! ## (ii) Closed-cell points and cell points -/

theorem m42_cellLe_M1 (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hD : 0 < Delta24 x)
    (h6 : 0 ≤ ⟪F.N 6, viewM42 x⟫) (h8 : 0 ≤ ⟪F.N 8, viewM42 x⟫) : CellLe F UM1 DnM1 (viewM42 x) := by
  obtain ⟨s0, s1, s5, s7, s3⟩ := m42_signs F hC hD
  have e4 := m42_n4 F hC
  have e2 := m42_n2 F hC
  constructor
  · intro t ht
    simp only [UM1, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl <;> linarith
  · intro t ht
    simp only [DnM1, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl <;> linarith

theorem m42_cellLe_M2 (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hD : 0 < Delta24 x)
    (h6 : 0 ≤ ⟪F.N 6, viewM42 x⟫) (h8 : ⟪F.N 8, viewM42 x⟫ ≤ 0) : CellLe F UM2 DnM2 (viewM42 x) := by
  obtain ⟨s0, s1, s5, s7, s3⟩ := m42_signs F hC hD
  have e4 := m42_n4 F hC
  have e2 := m42_n2 F hC
  constructor
  · intro t ht
    simp only [UM2, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl <;> linarith
  · intro t ht
    simp only [DnM2, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> linarith

theorem m42_cellLe_M3 (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hD : 0 < Delta24 x)
    (h6 : ⟪F.N 6, viewM42 x⟫ ≤ 0) (h8 : 0 ≤ ⟪F.N 8, viewM42 x⟫) : CellLe F UM3 DnM3 (viewM42 x) := by
  obtain ⟨s0, s1, s5, s7, s3⟩ := m42_signs F hC hD
  have e4 := m42_n4 F hC
  have e2 := m42_n2 F hC
  constructor
  · intro t ht
    simp only [UM3, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl <;> linarith
  · intro t ht
    simp only [DnM3, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> linarith

/-- Tilt `v = x 2 - x 4`: `046` back, `025`, `235` front, `346` back (so the lex tilt also decides `235`, `346`
when they are edge-on at `M_42`). -/
theorem tilt_mp (F : S0xFac 9 s0x_S24 x) :
    ⟪F.N 4, x 2 - x 4⟫ < 0 ∧ 0 < ⟪F.N 2, x 2 - x 4⟫ ∧ 0 < ⟪F.N 6, x 2 - x 4⟫ ∧ ⟪F.N 8, x 2 - x 4⟫ < 0 := by
  rw [F.inner_sub, F.inner_sub, F.inner_sub, F.inner_sub, F.zero 4 4 (by decide), F.zero 2 2 (by decide),
    F.zero 6 2 (by decide), F.zero 8 4 (by decide)]
  have h4 := F.neg 4 2 (by decide)
  have h2 := F.neg 2 4 (by decide)
  have h6 := F.neg 6 4 (by decide)
  have h8 := F.neg 8 2 (by decide)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- Tilt `v = x 4 - x 2`: the opposite of `tilt_mp`. -/
theorem tilt_pm (F : S0xFac 9 s0x_S24 x) :
    0 < ⟪F.N 4, x 4 - x 2⟫ ∧ ⟪F.N 2, x 4 - x 2⟫ < 0 ∧ ⟪F.N 6, x 4 - x 2⟫ < 0 ∧ 0 < ⟪F.N 8, x 4 - x 2⟫ := by
  rw [F.inner_sub, F.inner_sub, F.inner_sub, F.inner_sub, F.zero 4 4 (by decide), F.zero 2 2 (by decide),
    F.zero 6 2 (by decide), F.zero 8 4 (by decide)]
  have h4 := F.neg 4 2 (by decide)
  have h2 := F.neg 2 4 (by decide)
  have h6 := F.neg 6 4 (by decide)
  have h8 := F.neg 8 2 (by decide)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem m42_cellAt_M1 (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hD : 0 < Delta24 x)
    (h6 : 0 < ⟪F.N 6, viewM42 x⟫) (h8 : 0 < ⟪F.N 8, viewM42 x⟫) : ∃ a, CellAt F UM1 DnM1 a := by
  obtain ⟨s0, s1, s5, s7, s3⟩ := m42_signs F hC hD
  have e4 := m42_n4 F hC
  have e2 := m42_n2 F hC
  obtain ⟨t4, t2⟩ := tilt_pp F
  refine exists_cellAt_of_lex (u₀ := viewM42 x) (v := x 0 - x 1) (fun t ht => ?_) (fun t ht => ?_)
  · simp only [UM1, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact Or.inr ⟨e2, t2⟩
    · exact Or.inl s3
    · exact Or.inr ⟨e4, t4⟩
    · exact Or.inl h6
    · exact Or.inl h8
  · simp only [DnM1, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)

/-- `M2` is nonempty already for `0 ≤ N_6 . M`, `N_8 . M ≤ 0` (the tilt `x 2 - x 4` decides `235`, `346` when
they are edge-on). -/
theorem m42_cellAt_M2 (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hD : 0 < Delta24 x)
    (h6 : 0 ≤ ⟪F.N 6, viewM42 x⟫) (h8 : ⟪F.N 8, viewM42 x⟫ ≤ 0) : ∃ a, CellAt F UM2 DnM2 a := by
  obtain ⟨s0, s1, s5, s7, s3⟩ := m42_signs F hC hD
  have e4 := m42_n4 F hC
  have e2 := m42_n2 F hC
  obtain ⟨t4, t2, t6, t8⟩ := tilt_mp F
  refine exists_cellAt_of_lex (u₀ := viewM42 x) (v := x 2 - x 4) (fun t ht => ?_) (fun t ht => ?_)
  · simp only [UM2, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact Or.inr ⟨e2, t2⟩
    · exact Or.inl s3
    · rcases h6.lt_or_eq with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h.symm, t6⟩
  · simp only [DnM2, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, by linarith⟩
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · rcases h8.lt_or_eq with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by linarith, by linarith⟩

/-- `M3` is nonempty already for `N_6 . M ≤ 0`, `0 ≤ N_8 . M` (tilt `x 4 - x 2`). -/
theorem m42_cellAt_M3 (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hD : 0 < Delta24 x)
    (h6 : ⟪F.N 6, viewM42 x⟫ ≤ 0) (h8 : 0 ≤ ⟪F.N 8, viewM42 x⟫) : ∃ a, CellAt F UM3 DnM3 a := by
  obtain ⟨s0, s1, s5, s7, s3⟩ := m42_signs F hC hD
  have e4 := m42_n4 F hC
  have e2 := m42_n2 F hC
  obtain ⟨t4, t2, t6, t8⟩ := tilt_pm F
  refine exists_cellAt_of_lex (u₀ := viewM42 x) (v := x 4 - x 2) (fun t ht => ?_) (fun t ht => ?_)
  · simp only [UM3, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact Or.inl s3
    · exact Or.inr ⟨e4, t4⟩
    · rcases h8.lt_or_eq with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h.symm, t8⟩
  · simp only [DnM3, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, by linarith⟩
    · exact Or.inl (by linarith)
    · rcases h6.lt_or_eq with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by linarith, by linarith⟩
    · exact Or.inl (by linarith)

/-! ## (iii) The leaves (proved from (i), (ii) and `isRupert_of_closedCell_q4`) -/

/-- Some diagonal form of the 4-rim `c` is negative and some is positive at `u`. -/
def Crit (x : Fin 7 → ℝ³) (c : ZMod 4 → Fin 7) (u : ℝ³) : Prop :=
  (∃ p ∈ diagPairs, ⟪x (c p.1) - x (c p.2), u⟫ < 0) ∧ (∃ p ∈ diagPairs, 0 < ⟪x (c p.1) - x (c p.2), u⟫)

/-- **EO(iii), sub-region M1** (`N_6 . M > 0`, `N_8 . M > 0`, rim `0 2 3 6`). -/
theorem isRupert_m42_M1 (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hD : 0 < Delta24 x)
    (h6 : 0 < ⟪F.N 6, viewM42 x⟫) (h8 : 0 < ⟪F.N 8, viewM42 x⟫) (hc : Crit x cM1 (viewM42 x)) :
    IsRupert (univ.image x) := by
  obtain ⟨a, ha⟩ := m42_cellAt_M1 F hC hD h6 h8
  have hL := m42_cellLe_M1 F hC hD h6.le h8.le
  exact isRupert_of_closedCell_q4 F (Minimality.H24.SAT.inj_of_fac F) injM1 cycM1 ha hL hL hc.1 hc.2

/-- **EO(iii), sub-region M2** (`N_6 . M ≥ 0 ≥ N_8 . M`, rim `0 2 3 4`; ties allowed). -/
theorem isRupert_m42_M2 (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hD : 0 < Delta24 x)
    (h6 : 0 ≤ ⟪F.N 6, viewM42 x⟫) (h8 : ⟪F.N 8, viewM42 x⟫ ≤ 0) (hc : Crit x cM2 (viewM42 x)) :
    IsRupert (univ.image x) := by
  obtain ⟨a, ha⟩ := m42_cellAt_M2 F hC hD h6 h8
  have hL := m42_cellLe_M2 F hC hD h6 h8
  exact isRupert_of_closedCell_q4 F (Minimality.H24.SAT.inj_of_fac F) injM2 cycM2 ha hL hL hc.1 hc.2

/-- **EO(iii), sub-region M3** (`N_8 . M ≥ 0 ≥ N_6 . M`, rim `0 5 3 6`; ties allowed). -/
theorem isRupert_m42_M3 (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hD : 0 < Delta24 x)
    (h6 : ⟪F.N 6, viewM42 x⟫ ≤ 0) (h8 : 0 ≤ ⟪F.N 8, viewM42 x⟫) (hc : Crit x cM3 (viewM42 x)) :
    IsRupert (univ.image x) := by
  obtain ⟨a, ha⟩ := m42_cellAt_M3 F hC hD h6 h8
  have hL := m42_cellLe_M3 F hC hD h6 h8
  exact isRupert_of_closedCell_q4 F (Minimality.H24.SAT.inj_of_fac F) injM3 cycM3 ha hL hL hc.1 hc.2

/-- **EO, combined leaf.**  Outside the facet cells, for `Δ24 > 0`, with NO tie hypothesis: `M_42` is in one of
the cases, taken in this order: `M3` (`N_6 . M ≤ 0 ≤ N_8 . M`), else `M2` (`N_8 . M ≤ 0 ≤ N_6 . M`), else `M1`
(both `> 0`); coverage is `m42_not_both`.  `NOT D_A and NOT D_B` at `M_42` on that case's rim gives Rupert. -/
theorem isRupert_m42 (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hD : 0 < Delta24 x) (hfc : ¬ FacetCellF F)
    (hM3 : ⟪F.N 6, viewM42 x⟫ ≤ 0 → 0 ≤ ⟪F.N 8, viewM42 x⟫ → Crit x cM3 (viewM42 x))
    (hM2 : 0 ≤ ⟪F.N 6, viewM42 x⟫ → ⟪F.N 8, viewM42 x⟫ ≤ 0 →
      ¬ (⟪F.N 6, viewM42 x⟫ ≤ 0 ∧ 0 ≤ ⟪F.N 8, viewM42 x⟫) → Crit x cM2 (viewM42 x))
    (hM1 : 0 < ⟪F.N 6, viewM42 x⟫ → 0 < ⟪F.N 8, viewM42 x⟫ → Crit x cM1 (viewM42 x)) :
    IsRupert (univ.image x) := by
  have hnb := m42_not_both F hC hD hfc
  by_cases h3 : ⟪F.N 6, viewM42 x⟫ ≤ 0 ∧ 0 ≤ ⟪F.N 8, viewM42 x⟫
  · exact isRupert_m42_M3 F hC hD h3.1 h3.2 (hM3 h3.1 h3.2)
  · by_cases h2 : 0 ≤ ⟪F.N 6, viewM42 x⟫ ∧ ⟪F.N 8, viewM42 x⟫ ≤ 0
    · exact isRupert_m42_M2 F hC hD h2.1 h2.2 (hM2 h2.1 h2.2 h3)
    · have h6 : 0 < ⟪F.N 6, viewM42 x⟫ := by
        by_contra h
        push Not at h
        rcases hnb with hn | hn
        · have h8 : ⟪F.N 8, viewM42 x⟫ < 0 := by
            by_contra h'; push Not at h'; exact h3 ⟨h, h'⟩
          exact h2 ⟨hn, h8.le⟩
        · exact h3 ⟨h, hn⟩
      have h8 : 0 < ⟪F.N 8, viewM42 x⟫ := by
        by_contra h
        push Not at h
        exact h2 ⟨h6.le, h⟩
      exact isRupert_m42_M1 F hC hD h6 h8 (hM1 h6 h8)

/-- Remark: `FacetCellF (mkFac24 fs h)` is equivalent to `FacetCell24 fs`. -/
theorem facetCellF_iff_facetCell24 (fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ)
    (h : ∀ t i, (i ∈ s0x_S24 t → fs t (x i) = 0) ∧ (i ∉ s0x_S24 t → fs t (x i) < 0)) :
    FacetCellF (Minimality.T24.mkFac24 fs h) ↔ Minimality.T24.Z0.FacetCell24 fs := by
  have hN : ∀ s u, ⟪(Minimality.T24.mkFac24 fs h).N s, u⟫ = (fs s).linear u := by
    intro s u
    have h1 := (Minimality.T24.mkFac24 fs h).hN s u 0
    have h2 : (fs s).linear u = fs s u - fs s 0 := by simpa using (fs s).linear_apply_vsub u 0
    rw [sub_zero] at h1
    rw [h2]; exact h1.symm
  simp only [FacetCellF, Minimality.T24.Z0.FacetCell24, hN]

end Minimality.T24.EO
