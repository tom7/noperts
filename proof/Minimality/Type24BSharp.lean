module

public import Minimality.Type24BCertW26

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

theorem ustar_sharp {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (ha5 : oblX0 x 5 < 1) (hc3 : oblX6 x 3 < 1) (hD : Dl x < 0)
    (h8 : ⟪F.N 8, ustar x⟫ < 0)
    (hab : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0) (hac : ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0)
    (h63 : ⟪x 6 - x 1, ustar x⟫ < ⟪x 3 - x 1, ustar x⟫) (h30 : ⟪x 3 - x 1, ustar x⟫ ≤ 0)
    (hz5 : 0 < ⟪x 5 - x 1, ustar x⟫) :
    Minimality.Gen.LexAny F := by
  have T := type24OfFac F
  have ha5p : 0 < oblX0 x 5 := T.X0_pos (v := 5) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hz0 := ustar_z0_nonpos F hD hc3 hab hac
  have hrep : ∀ v : Fin 7, x v - x 1 =
      oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1) := by
    intro v; rw [T.rep v]; abel
  have hz5e : ⟪x 5 - x 1, ustar x⟫ = oblX0 x 5 * ⟪x 0 - x 1, ustar x⟫ +
      oblX2 x 5 * ⟪x 2 - x 1, ustar x⟫ + oblX6 x 5 * ⟪x 6 - x 1, ustar x⟫ := by
    rw [hrep 5, inner_add_left, inner_add_left, inner_smul_left, inner_smul_left, inner_smul_left]
    simp
  have hz5' := hz5
  have hz6 : ⟪x 6 - x 1, ustar x⟫ < 0 := by linarith
  have hz2 : 0 < ⟪x 2 - x 1, ustar x⟫ := by
    by_contra hn
    push Not at hn
    nlinarith [mul_nonpos_of_nonneg_of_nonpos ha5p.le hz0,
      mul_nonpos_of_nonneg_of_nonpos hb5.le hn, mul_neg_of_pos_of_neg hc5 hz6]
  have hfac := ustar_facings F hC ha5 hc3 hD
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
  have hU : ∀ t ∈ ({5, 6, 7} : Finset (Fin 9)),
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
    · exact Or.inl (by linarith [h8])
  have w6 : ⟪x 6, ustar x⟫ = ⟪x 1, ustar x⟫ + ⟪x 6 - x 1, ustar x⟫ := by
    rw [inner_sub_left]; ring
  have w3 : ⟪x 3, ustar x⟫ = ⟪x 1, ustar x⟫ + ⟪x 3 - x 1, ustar x⟫ := by
    rw [inner_sub_left]; ring
  have w5 : ⟪x 5, ustar x⟫ = ⟪x 1, ustar x⟫ + ⟪x 5 - x 1, ustar x⟫ := by
    rw [inner_sub_left]; ring
  have w2 : ⟪x 2, ustar x⟫ = ⟪x 1, ustar x⟫ + ⟪x 2 - x 1, ustar x⟫ := by
    rw [inner_sub_left]; ring
  have cl : ∀ (i j k l : Fin 7),
      (⟪x i, ustar x⟫ < ⟪x k, ustar x⟫ ∨ ⟪x i, ustar x⟫ < ⟪x l, ustar x⟫ ∨
        ⟪x j, ustar x⟫ < ⟪x k, ustar x⟫ ∨ ⟪x j, ustar x⟫ < ⟪x l, ustar x⟫) →
      Minimality.GenQuad.LexClause (x k) (x l) (x i) (x j) (ustar x) (dstar x) (x 6 - x 1) :=
    fun i j k l h => clause_of_gt h
  refine Minimality.GenQuad.lexAny_of_clauses F (k := 5) (by norm_num) hc_inj hcyc
    (ustar x) (dstar x) (x 6 - x 1) hU hD' ?_
  refine Minimality.GenQuad.clauses_five (p := fun i => x (c i)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
  · simp only [c, Matrix.cons_val]
    first
      | exact cl _ _ _ _ (by first | (left; linarith) | (right; left; linarith) )


/-- `ustar_closed_W26` without any `z3` hypothesis. -/
theorem ustar_closed_W26_full {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (ha5 : oblX0 x 5 < 1) (hc3 : oblX6 x 3 < 1) (hD : Dl x < 0)
    (h8 : ⟪F.N 8, ustar x⟫ < 0)
    (hab : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0) (hac : ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0)
    (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0) (hn : nB x < nC x)
    (hz5 : max 0 ⟪x 6 - x 1, ustar x⟫ < ⟪x 5 - x 1, ustar x⟫) :
    Minimality.Gen.LexAny F ∨ SplitAny24 F := by
  by_cases hU : Minimality.Gen.LexAny F
  · exact Or.inl hU
  by_cases h3 : 0 < ⟪x 3 - x 1, ustar x⟫
  · exact ustar_closed_W26 F hC ha5 hc3 hD h8 hab hac hbc hn h3 hz5
  have h63 : ⟪x 6 - x 1, ustar x⟫ < ⟪x 3 - x 1, ustar x⟫ := by
    by_contra h
    exact cert_w26_geom F hC ha5 hc3 hbc hn hU (not_lt.mp h)
  exact absurd (ustar_sharp F hC ha5 hc3 hD h8 hab hac h63 (not_lt.mp h3)
    (lt_of_le_of_lt (le_max_left _ _) hz5)) hU

end Minimality.T24.A10
