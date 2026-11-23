module

public import Minimality.Type29Pair2Lex2
public import Minimality.Type29Pair2W1.C0_0
public import Minimality.Type29Pair2W1.C0_1
public import Minimality.Type29Pair2W1.C0_2
public import Minimality.Type29Pair2W1.C0_3
public import Minimality.Type29Pair2W1.C0_4
public import Minimality.Type29Pair2W1.C0_5
public import Minimality.Type29Pair2W1.C0_6
public import Minimality.Type29Pair2W1.C1_0
public import Minimality.Type29Pair2W1.C1_1
public import Minimality.Type29Pair2W1.C1_2
public import Minimality.Type29Pair2W1.C1_3
public import Minimality.Type29Pair2W1.C1_4
public import Minimality.Type29Pair2W1.C1_5
public import Minimality.Type29Pair2W1.C1_6
public import Minimality.Type29Pair2W1.C2_0
public import Minimality.Type29Pair2W1.C2_1
public import Minimality.Type29Pair2W1.C2_2
public import Minimality.Type29Pair2W1.C2_3
public import Minimality.Type29Pair2W1.C2_4
public import Minimality.Type29Pair2W1.C2_5
public import Minimality.Type29Pair2W1.C2_6

@[expose] public section

/-!
# Type 29: tie-tolerant `pair2` closure (`lexAny_pair2_lex`, `lexAny29_pair2_lex`)
-/

set_option autoImplicit false

open scoped RealInnerProductSpace
open Minimality Minimality.H21 Minimality.SVCC Minimality.PSVC

namespace Minimality.PL29

theorem pair2_check1W : check1W s0x_S29 pair2_P pair2_swA [] pair2_D pair2_EA pair2_EB pair2_RA pair2_T1 pair2_B2 = true := by
  refine check1W_of_masks _ _ _ _ _ _ _ _ _ _ pair2_rMs1 pair2_m21
    (by decide +kernel) rfl pair2_hr1 pair2_hm21 ?_
  refine SVC.weakOrders_split3 (by omega) pair2_T1 _ (fun a => ?_) (fun a => ?_) (fun a => ?_)
  · fin_cases a
    exacts [pair2_w1_h0_0, pair2_w1_h0_1, pair2_w1_h0_2, pair2_w1_h0_3, pair2_w1_h0_4, pair2_w1_h0_5, pair2_w1_h0_6]
  · fin_cases a
    exacts [pair2_w1_h1_0, pair2_w1_h1_1, pair2_w1_h1_2, pair2_w1_h1_3, pair2_w1_h1_4, pair2_w1_h1_5, pair2_w1_h1_6]
  · fin_cases a
    exacts [pair2_w1_h2_0, pair2_w1_h2_1, pair2_w1_h2_2, pair2_w1_h2_3, pair2_w1_h2_4, pair2_w1_h2_5, pair2_w1_h2_6]

/-- **Pair `x 1 - x 2` + `x 5 - x 6` (lines F012xF124, F1456xF356)**, tie-tolerant `PSVC.pair_closure_lex`. -/
theorem lexAny_pair2_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (hA035 : ⟪F.N 3, x 1 - x 2⟫ < 0)
    (hA346 : ⟪F.N 7, x 1 - x 2⟫ < 0)
    (hA356 : ⟪F.N 8, x 1 - x 2⟫ < 0)
    (hB012 : 0 < ⟪F.N 0, x 5 - x 6⟫)
    (hB023 : 0 < ⟪F.N 2, x 5 - x 6⟫)
    (hB124 : ⟪F.N 4, x 5 - x 6⟫ < 0)
    (hB234 : ⟪F.N 6, x 5 - x 6⟫ < 0)
    (hS0 : 0 < PlaneSide x 2 4 5 0 1)
    (hS1 : 0 < PlaneSide x 2 5 6 0 1)
    (hS2 : 0 < PlaneSide x 2 3 6 1 5)
    (hS3 : 0 < PlaneSide x 2 3 5 1 6)
    (hw : ⟪x 1 - x 2, x 5 - x 6⟫ ≠ 0)
    (hT1 : ∀ i j : Fin 7, i ≠ j → ⟪x (pair2_P i), x 1 - x 2⟫ = ⟪x (pair2_P j), x 1 - x 2⟫ →
      (i, j) ∈ pair2_T1 ∨ (j, i) ∈ pair2_T1)
    (hT2 : ∀ i j : Fin 7, i ≠ j → ⟪x (pair2_P i), x 5 - x 6⟫ = ⟪x (pair2_P j), x 5 - x 6⟫ →
      (i, j) ∈ pair2_T2 ∨ (j, i) ∈ pair2_T2) :
    Gen.LexAny F := by
  have hs1 : ∀ t ∈ ({0, 1, 3, 4, 5, 7, 8} : Finset (Fin 9)), SignType.sign ⟪F.N t, x 1 - x 2⟫ = pair2_swA t := by
    intro t ht
    fin_cases t <;> simp at ht
    · exact sign_eq_zero_iff.mpr (edge_zero F 0 (by decide) (by decide))
    · exact sign_pos (edge_pos F 1 (by decide) (by decide))
    · exact sign_neg hA035
    · exact sign_eq_zero_iff.mpr (edge_zero F 4 (by decide) (by decide))
    · exact sign_pos (edge_pos F 5 (by decide) (by decide))
    · exact sign_neg hA346
    · exact sign_neg hA356
  have hS1' : ∀ ρ ∈ pair2_RA, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → t ∈ ({0, 1, 3, 4, 5, 7, 8} : Finset (Fin 9)) := by decide
  have hE1 : ∀ d ∈ pair2_EA, DecOK x pair2_P (x 1 - x 2) d := by
    intro d hd
    simp only [pair2_EA, List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    exact decOK_edge x pair2_P 1 2
  have hf1 : ∀ ij ∈ ([] : List (Fin 7 × Fin 7)), ⟪x (pair2_P ij.2), x 1 - x 2⟫ < ⟪x (pair2_P ij.1), x 1 - x 2⟫ := (by simp)
  have hw1 : x 1 - x 2 ≠ 0 := sub_ne_zero.mpr ((inj29 F).ne (by decide))
  have hR1 := hR_two_lex F pair2_swA pair2_RA (x 1 - x 2) hw1 0 4 1 4 0 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (edge_zero F 0 (by decide) (by decide))
  have hs2 : ∀ t ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)), SignType.sign ⟪F.N t, x 5 - x 6⟫ = pair2_swB t := by
    intro t ht
    fin_cases t <;> simp at ht
    · exact sign_pos hB012
    · exact sign_pos (edge_pos F 1 (by decide) (by decide))
    · exact sign_pos hB023
    · exact sign_pos (edge_pos F 3 (by decide) (by decide))
    · exact sign_neg hB124
    · exact sign_eq_zero_iff.mpr (edge_zero F 5 (by decide) (by decide))
    · exact sign_neg hB234
    · exact sign_neg (edge_neg F 7 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 8 (by decide) (by decide))
  have hS2' : ∀ ρ ∈ pair2_RB, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → t ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hE2 : ∀ d ∈ pair2_EB, DecOK x pair2_P (x 5 - x 6) d := by
    intro d hd
    simp only [pair2_EB, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact decOK_edge x pair2_P 5 6
    · exact decOK_tri F pair2_P pair2_swB 5 7 4 1 6 4 0 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (x 5 - x 6) (edge_zero F 5 (by decide) (by decide))
        (hs2 7 (by decide)) (hs2 4 (by decide))
  have hf2 : ∀ ij ∈ ([] : List (Fin 7 × Fin 7)), ⟪x (pair2_P ij.2), x 5 - x 6⟫ < ⟪x (pair2_P ij.1), x 5 - x 6⟫ := (by simp)
  have hw2 : x 5 - x 6 ≠ 0 := sub_ne_zero.mpr ((inj29 F).ne (by decide))
  have hR2 := hR_two_lex F pair2_swB pair2_RB (x 5 - x 6) hw2 5 8 5 3 1 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (edge_zero F 5 (by decide) (by decide))
  have hP : Function.Injective (fun i => x (pair2_P i)) := (inj29 F).comp (by decide)
  have hD : ∀ s ∈ pair2_D, ∃ mu : Fin 7 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (pair2_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = s i := by
    intro s hs
    simp only [pair2_D, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact pair2_dep0 F hS0
    · exact pair2_dep1 F hS1
    · exact pair2_dep2 F hS2 hS3
  exact pair_closure_lex F pair2_P (x 1 - x 2) (x 5 - x 6) pair2_swA pair2_swB pair2_RA pair2_RB
    [] [] pair2_EA pair2_EB pair2_T1 pair2_T2
    ⟨hw1, fun ρ hρ t ht => hs1 t (hS1' ρ hρ t ht), hR1, hf1, hE1, hP, hT1⟩
    ⟨hw2, fun ρ hρ t ht => hs2 t (hS2' ρ hρ t ht), hR2, hf2, hE2, hP, hT2⟩
    hw pair2_D hD pair2_B2 pair2_check1W pair2_check2W

/-- **NF29 form of `lexAny_pair2_lex`**. -/
theorem lexAny29_pair2_lex {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : N.V < 0)
    (h2 : ⟪(s0x_fac29 N.facets).N 3, x 1 - x 2⟫ < 0)
    (h3 : ⟪(s0x_fac29 N.facets).N 7, x 1 - x 2⟫ < 0)
    (h4 : ⟪(s0x_fac29 N.facets).N 8, x 1 - x 2⟫ < 0)
    (h5 : 0 < ⟪(s0x_fac29 N.facets).N 0, x 5 - x 6⟫)
    (h6 : 0 < ⟪(s0x_fac29 N.facets).N 2, x 5 - x 6⟫)
    (h7 : ⟪(s0x_fac29 N.facets).N 4, x 5 - x 6⟫ < 0)
    (h8 : ⟪(s0x_fac29 N.facets).N 6, x 5 - x 6⟫ < 0)
    (h9 : 0 < PlaneSide x 2 5 6 0 1)
    (h10 : 0 < PlaneSide x 2 3 6 1 5)
    (h11 : 0 < PlaneSide x 2 3 5 1 6)
    (hw : ⟪x 1 - x 2, x 5 - x 6⟫ ≠ 0)
    (hfA14 : ⟪x (pair2_P 1), x 1 - x 2⟫ ≠ ⟪x (pair2_P 4), x 1 - x 2⟫)
    (hfA46 : ⟪x (pair2_P 4), x 1 - x 2⟫ ≠ ⟪x (pair2_P 6), x 1 - x 2⟫)
    (hfA56 : ⟪x (pair2_P 5), x 1 - x 2⟫ ≠ ⟪x (pair2_P 6), x 1 - x 2⟫)
    (hfB12 : ⟪x (pair2_P 1), x 5 - x 6⟫ ≠ ⟪x (pair2_P 2), x 5 - x 6⟫)
    (hfB15 : ⟪x (pair2_P 1), x 5 - x 6⟫ ≠ ⟪x (pair2_P 5), x 5 - x 6⟫)
    (hfB23 : ⟪x (pair2_P 2), x 5 - x 6⟫ ≠ ⟪x (pair2_P 3), x 5 - x 6⟫)
    (hfB35 : ⟪x (pair2_P 3), x 5 - x 6⟫ ≠ ⟪x (pair2_P 5), x 5 - x 6⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by
  refine lexAny_pair2_lex _ h2 h3 h4 h5 h6 h7 h8 (ps24501_pos N h1) h9 h10 h11 hw ?_ ?_
  · intro i j hij heq
    fin_cases i <;> fin_cases j <;> (first | exact absurd rfl hij | decide | exact absurd heq hfA14 | exact absurd heq hfA14.symm | exact absurd heq hfA46 | exact absurd heq hfA46.symm | exact absurd heq hfA56 | exact absurd heq hfA56.symm)
  · intro i j hij heq
    fin_cases i <;> fin_cases j <;> (first | exact absurd rfl hij | decide | exact absurd heq hfB12 | exact absurd heq hfB12.symm | exact absurd heq hfB15 | exact absurd heq hfB15.symm | exact absurd heq hfB23 | exact absurd heq hfB23.symm | exact absurd heq hfB35 | exact absurd heq hfB35.symm)

end Minimality.PL29
