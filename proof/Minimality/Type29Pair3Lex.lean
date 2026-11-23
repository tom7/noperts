module

public import Minimality.Type29Pair

@[expose] public section

/-!
# Type 29: tie-tolerant `_lex` closures for `pair1`, `pair3`, `pair4`, `pair6`
-/

set_option autoImplicit false

open scoped RealInnerProductSpace
open Minimality Minimality.H21 Minimality.SVCC Minimality.PSVC

namespace Minimality.PL29

def pair3_T1 : List (Fin 6 × Fin 6) := allPairs 6
def pair3_T2 : List (Fin 6 × Fin 6) :=
  [(0,3), (0,4), (0,5), (1,2), (1,4), (1,5), (2,4), (3,4), (3,5)]

theorem pair3_check2W :
    check2W s0x_S29 pair3_P pair3_swB [] pair3_D pair3_EB pair3_RB pair3_T2 pair3_B2 = true := by
  decide +kernel

def pair3_rMs1 : List Nat := []
def pair3_m21 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

theorem pair3_check1W :
    check1W s0x_S29 pair3_P pair3_swA [] pair3_D pair3_EA pair3_EB pair3_RA pair3_T1 pair3_B2 = true := by
  refine check1W_of_masks _ _ _ _ _ _ _ _ _ _ pair3_rMs1 pair3_m21
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) ?_
  rw [SVC.weakOrders, SVC.allWeakOrdersF_eq]
  decide +kernel

theorem lexAny_pair3_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (w1 : ℝ³) (hw1X : ⟪F.N 1, w1⟫ = 0) (hw1Y : ⟪F.N 8, w1⟫ = 0)
    (hA012 : 0 < ⟪F.N 0, w1⟫)
    (hA035 : 0 < ⟪F.N 3, w1⟫)
    (hA1456 : ⟪F.N 5, w1⟫ < 0)
    (hA346 : ⟪F.N 7, w1⟫ < 0)
    (hB012 : 0 < ⟪F.N 0, x 4 - x 6⟫)
    (hB015 : ⟪F.N 1, x 4 - x 6⟫ < 0)
    (hB023 : 0 < ⟪F.N 2, x 4 - x 6⟫)
    (hB035 : ⟪F.N 3, x 4 - x 6⟫ < 0)
    (hS0 : PlaneSide x 1 3 4 0 5 < 0)
    (hw : ⟪w1, x 4 - x 6⟫ ≠ 0)
    (hT2 : ∀ i j, i ≠ j → ⟪x (pair3_P i), x 4 - x 6⟫ = ⟪x (pair3_P j), x 4 - x 6⟫ →
      (i, j) ∈ pair3_T2 ∨ (j, i) ∈ pair3_T2) :
    Gen.LexAny F := by
  have hs1 : ∀ t ∈ ({0, 1, 3, 5, 7, 8} : Finset (Fin 9)), SignType.sign ⟪F.N t, w1⟫ = pair3_swA t := by
    intro t ht; fin_cases t <;> simp at ht
    · exact sign_pos hA012
    · exact sign_eq_zero_iff.mpr hw1X
    · exact sign_pos hA035
    · exact sign_neg hA1456
    · exact sign_neg hA346
    · exact sign_eq_zero_iff.mpr hw1Y
  have hT1_set : ∀ ρ ∈ pair3_RA, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → t ∈ ({0, 1, 3, 5, 7, 8} : Finset (Fin 9)) := by decide
  have hE1 : ∀ d ∈ pair3_EA, DecOK x pair3_P (w1) d := by
    intro d hd; simp only [pair3_EA, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact decOK_tri F pair3_P pair3_swA 1 3 0 1 4 0 2 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (w1) hw1X
        (hs1 3 (by decide)) (hs1 0 (by decide))
    · exact decOK_tri F pair3_P pair3_swA 8 5 7 2 4 5 0 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (w1) hw1Y
        (hs1 5 (by decide)) (hs1 7 (by decide))
  have hs2 : ∀ t ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)), SignType.sign ⟪F.N t, x 4 - x 6⟫ = pair3_swB t := by
    intro t ht; fin_cases t <;> simp at ht
    · exact sign_pos hB012
    · exact sign_neg hB015
    · exact sign_pos hB023
    · exact sign_neg hB035
    · exact sign_pos (edge_pos F 4 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 5 (by decide) (by decide))
    · exact sign_pos (edge_pos F 6 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 7 (by decide) (by decide))
    · exact sign_neg (edge_neg F 8 (by decide) (by decide))
  have hT2_set : ∀ ρ ∈ pair3_RB, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → t ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hE2 : ∀ d ∈ pair3_EB, DecOK x pair3_P (x 4 - x 6) d := by
    intro d hd; simp only [pair3_EB, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact decOK_edge x pair3_P 3 5
    · exact decOK_tri F pair3_P pair3_swB 5 1 8 5 1 4 0 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (x 4 - x 6) (edge_zero F 5 (by decide) (by decide))
        (hs2 1 (by decide)) (hs2 8 (by decide))
  have hP : Function.Injective (fun i => x (pair3_P i)) := (inj29 F).comp (by decide)
  have hw1_ne : w1 ≠ 0 := fun h0 => by rw [h0, inner_zero_right] at hA012; exact lt_irrefl 0 hA012
  have hw2_ne : x 4 - x 6 ≠ 0 := sub_ne_zero.mpr ((inj29 F).ne (by decide))
  have V1 : ViewDataLex F pair3_P w1 pair3_swA pair3_RA [] pair3_EA pair3_T1 :=
    ⟨hw1_ne, fun ρ hρ t ht => hs1 t (hT1_set ρ hρ t ht),
     hR_two_lex F pair3_swA pair3_RA w1 hw1_ne 1 8 5 3 0 (by decide) (by decide) (by decide) (by decide)
       (by decide) (by decide) (by decide) (by decide) (by decide) hw1X,
     by simp, hE1, hP, hT_allPairs⟩
  have V2 : ViewDataLex F pair3_P (x 4 - x 6) pair3_swB pair3_RB [] pair3_EB pair3_T2 :=
    ⟨hw2_ne, fun ρ hρ t ht => hs2 t (hT2_set ρ hρ t ht),
     hR_two_lex F pair3_swB pair3_RB (x 4 - x 6) hw2_ne 5 7 4 3 1 (by decide) (by decide) (by decide) (by decide)
       (by decide) (by decide) (by decide) (by decide) (by decide) (edge_zero F 5 (by decide) (by decide)),
     by simp, hE2, hP, hT2⟩
  have hD : ∀ s ∈ pair3_D, ∃ mu : Fin 6 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (pair3_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = s i := by
    intro s hs; simp only [pair3_D, List.mem_cons, List.not_mem_nil, or_false] at hs; subst hs
    exact pair3_dep0 F hS0
  exact pair_closure_lex F pair3_P w1 (x 4 - x 6) pair3_swA pair3_swB pair3_RA pair3_RB [] []
    pair3_EA pair3_EB pair3_T1 pair3_T2 V1 V2 hw pair3_D hD pair3_B2 pair3_check1W pair3_check2W

theorem lexAny29_pair3_lex {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : N.b0 < 0)
    (h2 : 0 < ⟪(s0x_fac29 N.facets).N 0, lv29 N 1 8⟫)
    (h3 : 0 < ⟪(s0x_fac29 N.facets).N 3, lv29 N 1 8⟫)
    (h4 : ⟪(s0x_fac29 N.facets).N 5, lv29 N 1 8⟫ < 0)
    (h5 : ⟪(s0x_fac29 N.facets).N 7, lv29 N 1 8⟫ < 0)
    (h6 : 0 < ⟪(s0x_fac29 N.facets).N 0, x 4 - x 6⟫)
    (h7 : ⟪(s0x_fac29 N.facets).N 1, x 4 - x 6⟫ < 0)
    (h8 : 0 < ⟪(s0x_fac29 N.facets).N 2, x 4 - x 6⟫)
    (h9 : ⟪(s0x_fac29 N.facets).N 3, x 4 - x 6⟫ < 0)
    (hw : ⟪lv29 N 1 8, x 4 - x 6⟫ ≠ 0)
    (hf01 : ⟪x (pair3_P 0), x 4 - x 6⟫ ≠ ⟪x (pair3_P 1), x 4 - x 6⟫)
    (hf02 : ⟪x (pair3_P 0), x 4 - x 6⟫ ≠ ⟪x (pair3_P 2), x 4 - x 6⟫)
    (hf13 : ⟪x (pair3_P 1), x 4 - x 6⟫ ≠ ⟪x (pair3_P 3), x 4 - x 6⟫)
    (hf23 : ⟪x (pair3_P 2), x 4 - x 6⟫ ≠ ⟪x (pair3_P 3), x 4 - x 6⟫)
    (hf25 : ⟪x (pair3_P 2), x 4 - x 6⟫ ≠ ⟪x (pair3_P 5), x 4 - x 6⟫)
    (hf45 : ⟪x (pair3_P 4), x 4 - x 6⟫ ≠ ⟪x (pair3_P 5), x 4 - x 6⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by
  refine lexAny_pair3_lex _ (lv29 N 1 8) (by rw [real_inner_comm]; exact Minimality.inner_cross_left _ _)
    (by rw [real_inner_comm]; exact Minimality.inner_cross_right _ _) h2 h3 h4 h5 h6 h7 h8 h9 (ps13405_neg N h1) hw ?_
  intro i j hij heq
  fin_cases i <;> fin_cases j <;> (first | exact absurd rfl hij | decide | exact absurd heq hf01 | exact absurd heq hf01.symm | exact absurd heq hf02 | exact absurd heq hf02.symm | exact absurd heq hf13 | exact absurd heq hf13.symm | exact absurd heq hf23 | exact absurd heq hf23.symm | exact absurd heq hf25 | exact absurd heq hf25.symm | exact absurd heq hf45 | exact absurd heq hf45.symm)

end Minimality.PL29
