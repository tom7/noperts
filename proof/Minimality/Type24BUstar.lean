module

public import Minimality.M4dType24
public import Minimality.GenQuad
public import Minimality.Type24SAT.K24.CornerOB1

/-!
# Type 24, region B: R1 (algebra) and R2 (`ustar_collapse`)
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

/-! ### R1: pure algebra -/

theorem e0416_hrow_real {a4 a5 b4 b5 nC : ℝ} (h5 : 1 < a5 + b5) (ha4 : a4 ≤ 1)
    (hnC : nC < 0) (hnCdef : nC = b5 * (1 - a4) - b4 * (1 - a5))
    (ha5 : 0 < a5) (hb4 : 0 < b4) (hb5 : 0 < b5) :
    (1 - a4) * (1 - b5) < a5 * b4 := by
  by_cases hb : 1 ≤ b5
  · nlinarith [mul_nonneg (sub_nonneg.2 ha4) (sub_nonneg.2 hb), mul_pos ha5 hb4]
  · push Not at hb
    have h1 : 0 < 1 - b5 := by linarith
    have h2 : b5 * (1 - a4) < b4 * (1 - a5) := by linarith
    have h3 : (1 - a5) * (1 - b5) < a5 * b5 := by nlinarith
    have h4 : b5 * ((1 - a4) * (1 - b5)) < b5 * (a5 * b4) := by
      nlinarith [mul_lt_mul_of_pos_right h2 h1, mul_lt_mul_of_pos_left h3 hb4]
    exact lt_of_mul_lt_mul_left h4 hb5.le

theorem e0416_hrow {x : Fin 7 → ℝ³} (h5 : 1 < oblX0 x 5 + oblX2 x 5) (ha4 : oblX0 x 4 ≤ 1)
    (hnC : nC x < 0) (ha5 : 0 < oblX0 x 5) (hb4 : 0 < oblX2 x 4) (hb5 : 0 < oblX2 x 5) :
    (1 - oblX0 x 4) * (1 - oblX2 x 5) < oblX0 x 5 * oblX2 x 4 :=
  e0416_hrow_real h5 ha4 hnC rfl ha5 hb4 hb5

/-- Dl4 (the `x 4` analogue of `Dl`). -/
noncomputable def Dl4 (x : Fin 7 → ℝ³) : ℝ :=
  (1 - oblX6 x 4) * (1 - oblX0 x 5) - oblX0 x 4 * oblX6 x 5

/-- Lemma-M substitution: `a3 = (1 - s - t) + s a4 + t a5`, same for `c3`. -/
theorem dl_sigma_real {a3 c3 a4 c4 a5 c5 s t : ℝ}
    (ha : a3 = (1 - s - t) + s * a4 + t * a5) (hc : c3 = s * c4 + t * c5) :
    (1 - c3) * (1 - a5) - a3 * c5 =
      (1 - s) * (1 - a5 - c5) + s * ((1 - c4) * (1 - a5) - a4 * c5) := by
  subst ha hc; ring

theorem dl_sigma {x : Fin 7 → ℝ³} {s t : ℝ}
    (ha : oblX0 x 3 = (1 - s - t) + s * oblX0 x 4 + t * oblX0 x 5)
    (hc : oblX6 x 3 = s * oblX6 x 4 + t * oblX6 x 5) :
    Dl x = (1 - s) * (1 - oblX0 x 5 - oblX6 x 5) + s * Dl4 x :=
  dl_sigma_real ha hc


/-! ### R2: `ustar_collapse` -/

theorem clause_of_gt {p q r s b d1 d2 : ℝ³}
    (h : ⟪r, b⟫ < ⟪p, b⟫ ∨ ⟪r, b⟫ < ⟪q, b⟫ ∨ ⟪s, b⟫ < ⟪p, b⟫ ∨ ⟪s, b⟫ < ⟪q, b⟫) :
    Minimality.GenQuad.LexClause p q r s b d1 d2 := by
  apply Minimality.GenQuad.lexClause_of_notM
  rintro ⟨h1, h2, h3, h4⟩
  rcases h with h | h | h | h <;> linarith

/-- `z0(u*) <= 0` under the two OB1 face-angle conditions at vertex 1. -/
theorem ustar_z0_nonpos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hD : Dl x < 0)
    (hc3 : oblX6 x 3 < 1)
    (hab : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0) (hac : ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0) :
    ⟪x 0 - x 1, ustar x⟫ ≤ 0 := by
  have T := type24OfFac F
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc3_pos : 0 < 1 - oblX6 x 3 := sub_pos.mpr hc3
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
  have hA0 : Dl x - (1 - oblX6 x 3) * (1 - oblX0 x 5) = -(oblX0 x 3 * oblX6 x 5) := by
    dsimp [Dl]; ring
  have hA0n : Dl x - (1 - oblX6 x 3) * (1 - oblX0 x 5) ≤ 0 := by
    rw [hA0]; nlinarith [mul_pos ha3 hc5]
  have hA2 : 0 ≤ -Dl x + (1 - oblX6 x 3) * oblX2 x 5 := by
    nlinarith [mul_pos hc3_pos hb5]
  have hA6 : 0 ≤ (1 - oblX6 x 3) * oblX6 x 5 := (mul_pos hc3_pos hc5).le
  rw [hus_rep]
  exact Minimality.GenQuad.obtuse_frame hab hac hA0n hA2 hA6

/-- Shared `U*` hypothesis bundle for `ustar_collapse`, `ustar_sharp`, and `ustar_closed_W26*`. -/
structure UStarArgs (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop where
  hC : CbarIn x
  ha5 : oblX0 x 5 ≤ 1
  hc3 : oblX6 x 3 < 1
  hD : Dl x < 0
  h8 : ⟪F.N 8, ustar x⟫ < 0
  hab : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0
  hac : ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0

/-- Shared `ustar` 5-rim `![1, 6, 3, 5, 2]` clause scaffolding for `ustar_collapse` and `ustar_sharp`. -/
theorem ustar_lexAny_of_clauses {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hU : UStarArgs x F)
    (hA0123 : Minimality.GenQuad.LexClause (x 6) (x 5) (x 1) (x 3) (ustar x) (dstar x) (x 6 - x 1))
    (hB0123 : Minimality.GenQuad.LexClause (x 1) (x 3) (x 6) (x 5) (ustar x) (dstar x) (x 6 - x 1))
    (hA0124 : Minimality.GenQuad.LexClause (x 6) (x 2) (x 1) (x 3) (ustar x) (dstar x) (x 6 - x 1))
    (hB0124 : Minimality.GenQuad.LexClause (x 1) (x 3) (x 6) (x 2) (ustar x) (dstar x) (x 6 - x 1))
    (hA0134 : Minimality.GenQuad.LexClause (x 6) (x 2) (x 1) (x 5) (ustar x) (dstar x) (x 6 - x 1))
    (hB0134 : Minimality.GenQuad.LexClause (x 1) (x 5) (x 6) (x 2) (ustar x) (dstar x) (x 6 - x 1))
    (hA0234 : Minimality.GenQuad.LexClause (x 3) (x 2) (x 1) (x 5) (ustar x) (dstar x) (x 6 - x 1))
    (hB0234 : Minimality.GenQuad.LexClause (x 1) (x 5) (x 3) (x 2) (ustar x) (dstar x) (x 6 - x 1))
    (hA1234 : Minimality.GenQuad.LexClause (x 3) (x 2) (x 6) (x 5) (ustar x) (dstar x) (x 6 - x 1))
    (hB1234 : Minimality.GenQuad.LexClause (x 6) (x 5) (x 3) (x 2) (ustar x) (dstar x) (x 6 - x 1)) :
    Minimality.Gen.LexAny F := by
  have hfac := ustar_facings F hU.hC hU.ha5 hU.hc3 hU.hD
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
  have hcyc : S0xCycUD s0x_S24 c ({5, 6, 7} : Finset (Fin 9)) ({0, 1, 2, 3, 4, 8} : Finset (Fin 9)) := by
    unfold S0xCycUD; decide
  have hUset : ∀ t ∈ ({5, 6, 7} : Finset (Fin 9)),
      LexPos3 ⟪F.N t, ustar x⟫ ⟪F.N t, dstar x⟫ ⟪F.N t, x 6 - x 1⟫ := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact Or.inl hfac.2.2.2.2.2.1
    · exact Or.inl hfac.2.2.2.2.2.2.1
    · exact Or.inl hfac.2.2.2.2.2.2.2
  have hD' : ∀ t ∈ ({0, 1, 2, 3, 4, 8} : Finset (Fin 9)),
      LexPos3 (-⟪F.N t, ustar x⟫) (-⟪F.N t, dstar x⟫) (-⟪F.N t, x 6 - x 1⟫) := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (by linarith [hfac.1])
    · exact Or.inl (by linarith [hfac.2.1])
    · exact Or.inr ⟨by simp [hfac.2.2.1], Or.inl (by linarith [hd2_0])⟩
    · exact Or.inl (by linarith [hfac.2.2.2.1])
    · exact Or.inl (by linarith [hfac.2.2.2.2.1])
    · exact Or.inl (by linarith [hU.h8])
  refine Minimality.GenQuad.lexAny_of_clauses F (k := 5) (by norm_num) hc_inj hcyc
    (ustar x) (dstar x) (x 6 - x 1) hUset hD' ?_
  refine Minimality.GenQuad.clauses_five (p := fun i => x (c i))
    hA0123 hB0123 hA0124 hB0124 hA0134 hB0134 hA0234 hB0234 hA1234 hB1234

theorem ustar_collapse {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hU : UStarArgs x F)
    (hz : max 0 ⟪x 6 - x 1, ustar x⟫ < min ⟪x 3 - x 1, ustar x⟫ ⟪x 5 - x 1, ustar x⟫) :
    Minimality.Gen.LexAny F ∨ SplitAny24 F := by
  have T := type24OfFac F
  have ha5p : 0 < oblX0 x 5 := T.X0_pos (v := 5) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  by_cases h2 : max 0 ⟪x 6 - x 1, ustar x⟫ < ⟪x 2 - x 1, ustar x⟫
  · exact Or.inr (splitAny24_Ustar F hU.hC hU.ha5 hU.hc3 hU.hD hU.h8 (lt_min h2 hz))
  left
  push Not at h2
  have hz0 := ustar_z0_nonpos F hU.hD hU.hc3 hU.hab hU.hac
  have hz3 : max 0 ⟪x 6 - x 1, ustar x⟫ < ⟪x 3 - x 1, ustar x⟫ := lt_of_lt_of_le hz (min_le_left _ _)
  have hz5 : max 0 ⟪x 6 - x 1, ustar x⟫ < ⟪x 5 - x 1, ustar x⟫ := lt_of_lt_of_le hz (min_le_right _ _)
  have hrep : ∀ v : Fin 7, x v - x 1 =
      oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1) := by
    intro v; rw [T.rep v]; abel
  have hz5e : ⟪x 5 - x 1, ustar x⟫ = oblX0 x 5 * ⟪x 0 - x 1, ustar x⟫ +
      oblX2 x 5 * ⟪x 2 - x 1, ustar x⟫ + oblX6 x 5 * ⟪x 6 - x 1, ustar x⟫ := by
    rw [hrep 5, inner_add_left, inner_add_left, inner_smul_left, inner_smul_left, inner_smul_left]
    simp
  have hz6 : 0 < ⟪x 6 - x 1, ustar x⟫ := by
    by_contra hn
    push Not at hn
    have hm : max 0 ⟪x 6 - x 1, ustar x⟫ = 0 := max_eq_left hn
    rw [hm] at h2 hz5
    nlinarith [mul_nonpos_of_nonneg_of_nonpos ha5p.le hz0,
      mul_nonpos_of_nonneg_of_nonpos hb5.le h2, mul_nonpos_of_nonneg_of_nonpos hc5.le hn]
  have hm : max 0 ⟪x 6 - x 1, ustar x⟫ = ⟪x 6 - x 1, ustar x⟫ := max_eq_right hz6.le
  rw [hm] at h2 hz3 hz5
  have w6 : ⟪x 6, ustar x⟫ = ⟪x 1, ustar x⟫ + ⟪x 6 - x 1, ustar x⟫ := by rw [inner_sub_left]; ring
  have w3 : ⟪x 3, ustar x⟫ = ⟪x 1, ustar x⟫ + ⟪x 3 - x 1, ustar x⟫ := by rw [inner_sub_left]; ring
  have w5 : ⟪x 5, ustar x⟫ = ⟪x 1, ustar x⟫ + ⟪x 5 - x 1, ustar x⟫ := by rw [inner_sub_left]; ring
  have w2 : ⟪x 2, ustar x⟫ = ⟪x 1, ustar x⟫ + ⟪x 2 - x 1, ustar x⟫ := by rw [inner_sub_left]; ring
  refine ustar_lexAny_of_clauses F hU ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    exact clause_of_gt (by first | (left; linarith) | (right; left; linarith) | (right; right; right; linarith))

/-! ### nu346b form of `h8` -/

/-- `nu346b = a4 (1 - c3) - a3 (1 - c4)`. -/
noncomputable def nu346b (x : Fin 7 → ℝ³) : ℝ :=
  oblX0 x 4 * (1 - oblX6 x 3) - oblX0 x 3 * (1 - oblX6 x 4)

theorem nu346_ustar {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (hc3 : oblX6 x 3 < 1)
    (hΔ : 0 < oblX0 x 4 * oblX2 x 3 - oblX0 x 3 * oblX2 x 4) :
    ∃ k : ℝ, 0 < k ∧ ⟪F.N 8, ustar x⟫ = k * nu346b x := by
  have T := type24OfFac F
  have hom5 : 0 < omega5 x := hC.2.2.1
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hb3 : 0 < oblX2 x 3 := T.X2_pos (v := 3) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hc3_pos : 0 < 1 - oblX6 x 3 := sub_pos.mpr hc3
  have e5 := T.eq5
  have hg : 0 < -F.f 8 (x 1) := by linarith [F.neg 8 1 (by decide)]
  have z3 := fac_eval F 8 3
  have z4 := fac_eval F 8 4
  have z6 : F.f 8 (x 6) = 0 := F.zero 8 6 (by decide)
  have f3 : F.f 8 (x 3) = 0 := F.zero 8 3 (by decide)
  have f4 : F.f 8 (x 4) = 0 := F.zero 8 4 (by decide)
  have z5 := fac_eval F 8 5
  rw [z6] at z3 z4 z5
  rw [f3] at z3
  rw [f4] at z4
  have hus : ⟪F.N 8, ustar x⟫ =
      (-Dl x) * (F.f 8 (x 2) - F.f 8 (x 0)) + (1 - oblX6 x 3) * (F.f 8 (x 5) - F.f 8 (x 0)) := by
    dsimp [ustar]
    rw [inner_add_right, inner_smul_right, inner_smul_right, ← F.hN 8 (x 2) (x 0),
      ← F.hN 8 (x 5) (x 0)]
  have hM : 0 < (oblX0 x 3 + oblX2 x 3) * oblX6 x 5 + (oblX0 x 5 + oblX2 x 5 - 1) * (1 - oblX6 x 3) := by
    have : oblX0 x 5 + oblX2 x 5 - 1 = omega5 x * oblX6 x 5 := by linarith
    rw [this]; nlinarith [mul_pos hom5 hc5, mul_pos (mul_pos hom5 hc5) hc3_pos, mul_pos ha3 hc5, mul_pos hb3 hc5]
  refine ⟨(-F.f 8 (x 1)) * ((oblX0 x 3 + oblX2 x 3) * oblX6 x 5 +
      (oblX0 x 5 + oblX2 x 5 - 1) * (1 - oblX6 x 3)) /
      (oblX0 x 4 * oblX2 x 3 - oblX0 x 3 * oblX2 x 4), by positivity, ?_⟩
  have hE3 : oblX0 x 3 * (F.f 8 (x 0) - F.f 8 (x 1)) + oblX2 x 3 * (F.f 8 (x 2) - F.f 8 (x 1)) =
      (-F.f 8 (x 1)) * (1 - oblX6 x 3) := by linarith
  have hE4 : oblX0 x 4 * (F.f 8 (x 0) - F.f 8 (x 1)) + oblX2 x 4 * (F.f 8 (x 2) - F.f 8 (x 1)) =
      (-F.f 8 (x 1)) * (1 - oblX6 x 4) := by linarith
  rw [hus, z5, div_mul_eq_mul_div, eq_div_iff hΔ.ne']
  simp only [Dl, nu346b]
  linear_combination
    (-((-(oblX0 x 3 * oblX6 x 5)) * oblX2 x 4 -
      (-((1 - oblX6 x 3) * (1 - oblX0 x 5) - oblX0 x 3 * oblX6 x 5) + (1 - oblX6 x 3) * oblX2 x 5) *
        oblX0 x 4)) * hE3 +
    (-((-((1 - oblX6 x 3) * (1 - oblX0 x 5) - oblX0 x 3 * oblX6 x 5) + (1 - oblX6 x 3) * oblX2 x 5) *
        oblX0 x 3 - (-(oblX0 x 3 * oblX6 x 5)) * oblX2 x 3)) * hE4

end Minimality.T24.A10
