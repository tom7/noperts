module

public import Minimality.Type29Pair5Lex2
public import Minimality.Type29Pair5W1.C0_0
public import Minimality.Type29Pair5W1.C0_1
public import Minimality.Type29Pair5W1.C0_2
public import Minimality.Type29Pair5W1.C0_3
public import Minimality.Type29Pair5W1.C0_4
public import Minimality.Type29Pair5W1.C0_5
public import Minimality.Type29Pair5W1.C0_6
public import Minimality.Type29Pair5W1.C1_0
public import Minimality.Type29Pair5W1.C1_1
public import Minimality.Type29Pair5W1.C1_2
public import Minimality.Type29Pair5W1.C1_3
public import Minimality.Type29Pair5W1.C1_4
public import Minimality.Type29Pair5W1.C1_5
public import Minimality.Type29Pair5W1.C1_6
public import Minimality.Type29Pair5W1.C2_0
public import Minimality.Type29Pair5W1.C2_1
public import Minimality.Type29Pair5W1.C2_2
public import Minimality.Type29Pair5W1.C2_3
public import Minimality.Type29Pair5W1.C2_4
public import Minimality.Type29Pair5W1.C2_5
public import Minimality.Type29Pair5W1.C2_6

@[expose] public section

/-!
# Type 29: tie-tolerant `pair5` closure (`lexAny_pair5_lex`, `lexAny29_pair5_lex`)
-/

set_option autoImplicit false

open scoped RealInnerProductSpace
open Minimality Minimality.H21 Minimality.SVCC Minimality.PSVC

namespace Minimality.PL29

theorem pair5_check1W : check1W s0x_S29 pair5_P pair5_swA [] pair5_D pair5_EA pair5_EB pair5_RA pair5_T1 pair5_B2 = true := by
  refine check1W_of_masks _ _ _ _ _ _ _ _ _ _ pair5_rMs1 pair5_m21
    (by decide +kernel) rfl pair5_hr1 pair5_hm21 ?_
  refine SVC.weakOrders_split3 (by omega) pair5_T1 _ (fun a => ?_) (fun a => ?_) (fun a => ?_)
  · fin_cases a
    exacts [pair5_w1_h0_0, pair5_w1_h0_1, pair5_w1_h0_2, pair5_w1_h0_3, pair5_w1_h0_4, pair5_w1_h0_5, pair5_w1_h0_6]
  · fin_cases a
    exacts [pair5_w1_h1_0, pair5_w1_h1_1, pair5_w1_h1_2, pair5_w1_h1_3, pair5_w1_h1_4, pair5_w1_h1_5, pair5_w1_h1_6]
  · fin_cases a
    exacts [pair5_w1_h2_0, pair5_w1_h2_1, pair5_w1_h2_2, pair5_w1_h2_3, pair5_w1_h2_4, pair5_w1_h2_5, pair5_w1_h2_6]

/-- **Pair `w1` + `x 1 - x 4` (lines F035xF346, F124xF1456)**, tie-tolerant `PSVC.pair_closure_lex`. -/
theorem lexAny_pair5_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (w1 : ℝ³) (hw1X : ⟪F.N 3, w1⟫ = 0) (hw1Y : ⟪F.N 7, w1⟫ = 0)
    (hA012 : 0 < ⟪F.N 0, w1⟫)
    (hA015 : ⟪F.N 1, w1⟫ < 0)
    (hA023 : 0 < ⟪F.N 2, w1⟫)
    (hA124 : 0 < ⟪F.N 4, w1⟫)
    (hA1456 : ⟪F.N 5, w1⟫ < 0)
    (hA234 : 0 < ⟪F.N 6, w1⟫)
    (hA356 : ⟪F.N 8, w1⟫ < 0)
    (hB023 : 0 < ⟪F.N 2, x 1 - x 4⟫)
    (hB356 : 0 < ⟪F.N 8, x 1 - x 4⟫)
    (hS0 : 0 < PlaneSide x 1 3 4 0 5)
    (hS1 : PlaneSide x 2 3 6 1 4 < 0)
    (hw : ⟪w1, x 1 - x 4⟫ ≠ 0)
    (hT1 : ∀ i j : Fin 7, i ≠ j → ⟪x (pair5_P i), w1⟫ = ⟪x (pair5_P j), w1⟫ →
      (i, j) ∈ pair5_T1 ∨ (j, i) ∈ pair5_T1)
    (hT2 : ∀ i j : Fin 7, i ≠ j → ⟪x (pair5_P i), x 1 - x 4⟫ = ⟪x (pair5_P j), x 1 - x 4⟫ →
      (i, j) ∈ pair5_T2 ∨ (j, i) ∈ pair5_T2) :
    Gen.LexAny F := by
  have hs1 : ∀ t ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)), SignType.sign ⟪F.N t, w1⟫ = pair5_swA t := by
    intro t ht
    fin_cases t <;> simp at ht
    · exact sign_pos hA012
    · exact sign_neg hA015
    · exact sign_pos hA023
    · exact sign_eq_zero_iff.mpr hw1X
    · exact sign_pos hA124
    · exact sign_neg hA1456
    · exact sign_pos hA234
    · exact sign_eq_zero_iff.mpr hw1Y
    · exact sign_neg hA356
  have hS1' : ∀ ρ ∈ pair5_RA, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → t ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hE1 : ∀ d ∈ pair5_EA, DecOK x pair5_P w1 d := by
    intro d hd
    simp only [pair5_EA, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact decOK_tri F pair5_P pair5_swA 3 8 1 0 3 5 1 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) w1 hw1X
        (hs1 8 (by decide)) (hs1 1 (by decide))
    · exact decOK_tri F pair5_P pair5_swA 7 5 8 3 4 6 0 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) w1 hw1Y
        (hs1 5 (by decide)) (hs1 8 (by decide))
  have hf1 : ∀ ij ∈ ([] : List (Fin 7 × Fin 7)), ⟪x (pair5_P ij.2), w1⟫ < ⟪x (pair5_P ij.1), w1⟫ := (by simp)
  have hw1 : w1 ≠ 0 := fun h0 => by rw [h0, inner_zero_right] at hA012; exact lt_irrefl 0 hA012
  have hR1 := hR_two_lex F pair5_swA pair5_RA w1 hw1 3 7 3 4 0 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hw1X
  have hs2 : ∀ t ∈ ({1, 2, 4, 5, 6, 7, 8} : Finset (Fin 9)), SignType.sign ⟪F.N t, x 1 - x 4⟫ = pair5_swB t := by
    intro t ht
    fin_cases t <;> simp at ht
    · exact sign_pos (edge_pos F 1 (by decide) (by decide))
    · exact sign_pos hB023
    · exact sign_eq_zero_iff.mpr (edge_zero F 4 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 5 (by decide) (by decide))
    · exact sign_neg (edge_neg F 6 (by decide) (by decide))
    · exact sign_neg (edge_neg F 7 (by decide) (by decide))
    · exact sign_pos hB356
  have hS2' : ∀ ρ ∈ pair5_RB, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → t ∈ ({1, 2, 4, 5, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hE2 : ∀ d ∈ pair5_EB, DecOK x pair5_P (x 1 - x 4) d := by
    intro d hd
    simp only [pair5_EB, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact decOK_edge x pair5_P 1 4
    · exact decOK_tri F pair5_P pair5_swB 5 1 8 6 1 5 0 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (x 1 - x 4) (edge_zero F 5 (by decide) (by decide))
        (hs2 1 (by decide)) (hs2 8 (by decide))
  have hf2 : ∀ ij ∈ ([] : List (Fin 7 × Fin 7)), ⟪x (pair5_P ij.2), x 1 - x 4⟫ < ⟪x (pair5_P ij.1), x 1 - x 4⟫ := (by simp)
  have hw2 : x 1 - x 4 ≠ 0 := sub_ne_zero.mpr ((inj29 F).ne (by decide))
  have hR2 := hR_two_lex F pair5_swB pair5_RB (x 1 - x 4) hw2 4 5 1 5 2 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (edge_zero F 4 (by decide) (by decide))
  have hP : Function.Injective (fun i => x (pair5_P i)) := (inj29 F).comp (by decide)
  have hD : ∀ s ∈ pair5_D, ∃ mu : Fin 7 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (pair5_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = s i := by
    intro s hs
    simp only [pair5_D, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact pair5_dep0 F hS0
    · exact pair5_dep1 F hS1
  exact pair_closure_lex F pair5_P w1 (x 1 - x 4) pair5_swA pair5_swB pair5_RA pair5_RB
    [] [] pair5_EA pair5_EB pair5_T1 pair5_T2
    ⟨hw1, fun ρ hρ t ht => hs1 t (hS1' ρ hρ t ht), hR1, hf1, hE1, hP, hT1⟩
    ⟨hw2, fun ρ hρ t ht => hs2 t (hS2' ρ hρ t ht), hR2, hf2, hE2, hP, hT2⟩
    hw pair5_D hD pair5_B2 pair5_check1W pair5_check2W

/-- **NF29 form of `lexAny_pair5_lex`**. -/
theorem lexAny29_pair5_lex {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : 0 < N.b0)
    (h2 : 0 < ⟪(s0x_fac29 N.facets).N 0, lv29 N 3 7⟫)
    (h3 : ⟪(s0x_fac29 N.facets).N 1, lv29 N 3 7⟫ < 0)
    (h4 : 0 < ⟪(s0x_fac29 N.facets).N 2, lv29 N 3 7⟫)
    (h5 : 0 < ⟪(s0x_fac29 N.facets).N 4, lv29 N 3 7⟫)
    (h6 : ⟪(s0x_fac29 N.facets).N 5, lv29 N 3 7⟫ < 0)
    (h7 : 0 < ⟪(s0x_fac29 N.facets).N 6, lv29 N 3 7⟫)
    (h8 : ⟪(s0x_fac29 N.facets).N 8, lv29 N 3 7⟫ < 0)
    (h9 : 0 < ⟪(s0x_fac29 N.facets).N 2, x 1 - x 4⟫)
    (h10 : 0 < ⟪(s0x_fac29 N.facets).N 8, x 1 - x 4⟫)
    (h11 : PlaneSide x 2 3 6 1 4 < 0)
    (hw : ⟪lv29 N 3 7, x 1 - x 4⟫ ≠ 0)
    (hfA14 : ⟪x (pair5_P 1), lv29 N 3 7⟫ ≠ ⟪x (pair5_P 4), lv29 N 3 7⟫)
    (hfA56 : ⟪x (pair5_P 5), lv29 N 3 7⟫ ≠ ⟪x (pair5_P 6), lv29 N 3 7⟫)
    (hfB23 : ⟪x (pair5_P 2), x 1 - x 4⟫ ≠ ⟪x (pair5_P 3), x 1 - x 4⟫)
    (hfB24 : ⟪x (pair5_P 2), x 1 - x 4⟫ ≠ ⟪x (pair5_P 4), x 1 - x 4⟫)
    (hfB36 : ⟪x (pair5_P 3), x 1 - x 4⟫ ≠ ⟪x (pair5_P 6), x 1 - x 4⟫)
    (hfB46 : ⟪x (pair5_P 4), x 1 - x 4⟫ ≠ ⟪x (pair5_P 6), x 1 - x 4⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by
  refine lexAny_pair5_lex _ (lv29 N 3 7) (by rw [real_inner_comm]; exact Minimality.inner_cross_left _ _)
    (by rw [real_inner_comm]; exact Minimality.inner_cross_right _ _) h2 h3 h4 h5 h6 h7 h8 h9 h10 (ps13405_pos N h1) h11 hw ?_ ?_
  · intro i j hij heq
    fin_cases i <;> fin_cases j <;> (first | exact absurd rfl hij | decide | exact absurd heq hfA14 | exact absurd heq hfA14.symm | exact absurd heq hfA56 | exact absurd heq hfA56.symm)
  · intro i j hij heq
    fin_cases i <;> fin_cases j <;> (first | exact absurd rfl hij | decide | exact absurd heq hfB23 | exact absurd heq hfB23.symm | exact absurd heq hfB24 | exact absurd heq hfB24.symm | exact absurd heq hfB36 | exact absurd heq hfB36.symm | exact absurd heq hfB46 | exact absurd heq hfB46.symm)

end Minimality.PL29
