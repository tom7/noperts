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

def pair1_T1 : List (Fin 6 × Fin 6) := allPairs 6
def pair1_T2 : List (Fin 6 × Fin 6) :=
  [(0,2), (0,3), (0,5), (1,3), (1,4), (1,5), (2,3), (3,4), (4,5)]

theorem pair1_check2W :
    check2W s0x_S29 pair1_P pair1_swB [] pair1_D pair1_EB pair1_RB pair1_T2 pair1_B2 = true := by
  decide +kernel

def pair1_rMs1 : List Nat := []
def pair1_m21 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

theorem pair1_check1W :
    check1W s0x_S29 pair1_P pair1_swA [] pair1_D pair1_EA pair1_EB pair1_RA pair1_T1 pair1_B2 = true := by
  refine check1W_of_masks _ _ _ _ _ _ _ _ _ _ pair1_rMs1 pair1_m21
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) ?_
  rw [SVC.weakOrders, SVC.allWeakOrdersF_eq]
  decide +kernel

theorem lexAny_pair1_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (w1 : ℝ³) (hw1X : ⟪F.N 4, w1⟫ = 0) (hw1Y : ⟪F.N 7, w1⟫ = 0)
    (hA012 : ⟪F.N 0, w1⟫ < 0)
    (hA1456 : 0 < ⟪F.N 5, w1⟫)
    (hA234 : ⟪F.N 6, w1⟫ < 0)
    (hA356 : 0 < ⟪F.N 8, w1⟫)
    (hB012 : 0 < ⟪F.N 0, x 5 - x 6⟫)
    (hB023 : 0 < ⟪F.N 2, x 5 - x 6⟫)
    (hB124 : ⟪F.N 4, x 5 - x 6⟫ < 0)
    (hB234 : ⟪F.N 6, x 5 - x 6⟫ < 0)
    (hS0 : 0 < PlaneSide x 2 3 5 1 4)
    (hw : ⟪w1, x 5 - x 6⟫ ≠ 0)
    (hT2 : ∀ i j, i ≠ j → ⟪x (pair1_P i), x 5 - x 6⟫ = ⟪x (pair1_P j), x 5 - x 6⟫ →
      (i, j) ∈ pair1_T2 ∨ (j, i) ∈ pair1_T2) :
    Gen.LexAny F := by
  have hs1 : ∀ t ∈ ({0, 4, 5, 6, 7, 8} : Finset (Fin 9)), SignType.sign ⟪F.N t, w1⟫ = pair1_swA t := by
    intro t ht; fin_cases t <;> simp at ht
    · exact sign_neg hA012
    · exact sign_eq_zero_iff.mpr hw1X
    · exact sign_pos hA1456
    · exact sign_neg hA234
    · exact sign_eq_zero_iff.mpr hw1Y
    · exact sign_pos hA356
  have hT1_set : ∀ ρ ∈ pair1_RA, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → t ∈ ({0, 4, 5, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hE1 : ∀ d ∈ pair1_EA, DecOK x pair1_P (w1) d := by
    intro d hd; simp only [pair1_EA, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact decOK_tri F pair1_P pair1_swA 4 6 0 0 3 1 0 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (w1) hw1X
        (hs1 6 (by decide)) (hs1 0 (by decide))
    · exact decOK_tri F pair1_P pair1_swA 7 5 8 2 3 5 0 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (w1) hw1Y
        (hs1 5 (by decide)) (hs1 8 (by decide))
  have hs2 : ∀ t ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)), SignType.sign ⟪F.N t, x 5 - x 6⟫ = pair1_swB t := by
    intro t ht; fin_cases t <;> simp at ht
    · exact sign_pos hB012
    · exact sign_pos (edge_pos F 1 (by decide) (by decide))
    · exact sign_pos hB023
    · exact sign_pos (edge_pos F 3 (by decide) (by decide))
    · exact sign_neg hB124
    · exact sign_eq_zero_iff.mpr (edge_zero F 5 (by decide) (by decide))
    · exact sign_neg hB234
    · exact sign_neg (edge_neg F 7 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 8 (by decide) (by decide))
  have hT2_set : ∀ ρ ∈ pair1_RB, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → t ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hE2 : ∀ d ∈ pair1_EB, DecOK x pair1_P (x 5 - x 6) d := by
    intro d hd; simp only [pair1_EB, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact decOK_edge x pair1_P 4 5
    · exact decOK_tri F pair1_P pair1_swB 5 7 4 0 5 3 0 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (x 5 - x 6) (edge_zero F 5 (by decide) (by decide))
        (hs2 7 (by decide)) (hs2 4 (by decide))
  have hP : Function.Injective (fun i => x (pair1_P i)) := (inj29 F).comp (by decide)
  have hw1_ne : w1 ≠ 0 := fun h0 => by rw [h0, inner_zero_right] at hA012; exact lt_irrefl 0 hA012
  have hw2_ne : x 5 - x 6 ≠ 0 := sub_ne_zero.mpr ((inj29 F).ne (by decide))
  have V1 : ViewDataLex F pair1_P w1 pair1_swA pair1_RA [] pair1_EA pair1_T1 :=
    ⟨hw1_ne, fun ρ hρ t ht => hs1 t (hT1_set ρ hρ t ht),
     hR_two_lex F pair1_swA pair1_RA w1 hw1_ne 4 7 4 3 1 (by decide) (by decide) (by decide) (by decide)
       (by decide) (by decide) (by decide) (by decide) (by decide) hw1X,
     by simp, hE1, hP, hT_allPairs⟩
  have V2 : ViewDataLex F pair1_P (x 5 - x 6) pair1_swB pair1_RB [] pair1_EB pair1_T2 :=
    ⟨hw2_ne, fun ρ hρ t ht => hs2 t (hT2_set ρ hρ t ht),
     hR_two_lex F pair1_swB pair1_RB (x 5 - x 6) hw2_ne 5 8 5 3 1 (by decide) (by decide) (by decide) (by decide)
       (by decide) (by decide) (by decide) (by decide) (by decide) (edge_zero F 5 (by decide) (by decide)),
     by simp, hE2, hP, hT2⟩
  have hD : ∀ s ∈ pair1_D, ∃ mu : Fin 6 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (pair1_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = s i := by
    intro s hs; simp only [pair1_D, List.mem_cons, List.not_mem_nil, or_false] at hs; subst hs
    exact pair1_dep0 F hS0
  exact pair_closure_lex F pair1_P w1 (x 5 - x 6) pair1_swA pair1_swB pair1_RA pair1_RB [] []
    pair1_EA pair1_EB pair1_T1 pair1_T2 V1 V2 hw pair1_D hD pair1_B2 pair1_check1W pair1_check2W

theorem lexAny29_pair1_lex {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : N.a2 < 0)
    (h2 : ⟪(s0x_fac29 N.facets).N 0, lv29 N 4 7⟫ < 0)
    (h3 : 0 < ⟪(s0x_fac29 N.facets).N 5, lv29 N 4 7⟫)
    (h4 : ⟪(s0x_fac29 N.facets).N 6, lv29 N 4 7⟫ < 0)
    (h5 : 0 < ⟪(s0x_fac29 N.facets).N 8, lv29 N 4 7⟫)
    (h6 : 0 < ⟪(s0x_fac29 N.facets).N 0, x 5 - x 6⟫)
    (h7 : 0 < ⟪(s0x_fac29 N.facets).N 2, x 5 - x 6⟫)
    (h8 : ⟪(s0x_fac29 N.facets).N 4, x 5 - x 6⟫ < 0)
    (h9 : ⟪(s0x_fac29 N.facets).N 6, x 5 - x 6⟫ < 0)
    (hw : ⟪lv29 N 4 7, x 5 - x 6⟫ ≠ 0)
    (hf01 : ⟪x (pair1_P 0), x 5 - x 6⟫ ≠ ⟪x (pair1_P 1), x 5 - x 6⟫)
    (hf04 : ⟪x (pair1_P 0), x 5 - x 6⟫ ≠ ⟪x (pair1_P 4), x 5 - x 6⟫)
    (hf12 : ⟪x (pair1_P 1), x 5 - x 6⟫ ≠ ⟪x (pair1_P 2), x 5 - x 6⟫)
    (hf24 : ⟪x (pair1_P 2), x 5 - x 6⟫ ≠ ⟪x (pair1_P 4), x 5 - x 6⟫)
    (hf25 : ⟪x (pair1_P 2), x 5 - x 6⟫ ≠ ⟪x (pair1_P 5), x 5 - x 6⟫)
    (hf35 : ⟪x (pair1_P 3), x 5 - x 6⟫ ≠ ⟪x (pair1_P 5), x 5 - x 6⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by
  refine lexAny_pair1_lex _ (lv29 N 4 7) (by rw [real_inner_comm]; exact Minimality.inner_cross_left _ _)
    (by rw [real_inner_comm]; exact Minimality.inner_cross_right _ _) h2 h3 h4 h5 h6 h7 h8 h9 (ps23514_pos N h1) hw ?_
  intro i j hij heq
  fin_cases i <;> fin_cases j <;> (first | exact absurd rfl hij | decide | exact absurd heq hf01 | exact absurd heq hf01.symm | exact absurd heq hf04 | exact absurd heq hf04.symm | exact absurd heq hf12 | exact absurd heq hf12.symm | exact absurd heq hf24 | exact absurd heq hf24.symm | exact absurd heq hf25 | exact absurd heq hf25.symm | exact absurd heq hf35 | exact absurd heq hf35.symm)

end Minimality.PL29
