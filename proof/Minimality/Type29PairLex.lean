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

def pair4_T : List (Fin 5 × Fin 5) := allPairs 5

theorem pair4_check2W :
    check2W s0x_S29 pair4_P pair4_swA [] pair4_D pair4_EA pair4_RA pair4_T pair4_B2 = true := by
  decide +kernel

theorem pair4_check1W :
    check1W s0x_S29 pair4_P pair4_swA [] pair4_D pair4_EA pair4_EA pair4_RA pair4_T pair4_B2 = true := by
  decide +kernel

theorem lexAny_pair4_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (hA015 : 0 < ⟪F.N 1, x 3 - x 6⟫)
    (hA124 : 0 < ⟪F.N 4, x 3 - x 6⟫) :
    Gen.LexAny F := by
  have hs1 : ∀ t ∈ ({1, 4, 5, 7, 8} : Finset (Fin 9)), SignType.sign ⟪F.N t, x 3 - x 6⟫ = pair4_swA t := by
    intro t ht; fin_cases t <;> simp at ht
    · exact sign_pos hA015
    · exact sign_pos hA124
    · exact sign_neg (edge_neg F 5 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 7 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 8 (by decide) (by decide))
  have hT1_set : ∀ ρ ∈ pair4_RA, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → t ∈ ({1, 4, 5, 7, 8} : Finset (Fin 9)) := by decide
  have hE1 : ∀ d ∈ pair4_EA, DecOK x pair4_P (x 3 - x 6) d := by simp [pair4_EA]
  have hP : Function.Injective (fun i => x (pair4_P i)) := (inj29 F).comp (by decide)
  have hw_ne : x 3 - x 6 ≠ 0 := sub_ne_zero.mpr ((inj29 F).ne (by decide))
  have V1 : ViewDataLex F pair4_P (x 3 - x 6) pair4_swA pair4_RA [] pair4_EA pair4_T :=
    ⟨hw_ne, fun ρ hρ t ht => hs1 t (hT1_set ρ hρ t ht),
     hR_two_lex F pair4_swA pair4_RA (x 3 - x 6) hw_ne 7 8 3 5 4 (by decide) (by decide) (by decide) (by decide)
       (by decide) (by decide) (by decide) (by decide) (by decide) (edge_zero F 7 (by decide) (by decide)),
     by simp, hE1, hP, hT_allPairs⟩
  have hD : ∀ s ∈ pair4_D, ∃ mu : Fin 5 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (pair4_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = s i := by
    intro s hs; simp only [pair4_D, List.mem_cons, List.not_mem_nil, or_false] at hs; subst hs
    exact pair4_dep0 F
  exact pair_closure_lex F pair4_P (x 3 - x 6) (x 3 - x 6) pair4_swA pair4_swA pair4_RA pair4_RA [] []
    pair4_EA pair4_EA pair4_T pair4_T V1 V1 (inner_self_ne_zero.mpr hw_ne) pair4_D hD pair4_B2 pair4_check1W pair4_check2W

def pair6_T1 : List (Fin 5 × Fin 5) := allPairs 5
def pair6_T2 : List (Fin 5 × Fin 5) :=
  [(0,1), (0,2), (0,3), (0,4), (1,3), (1,4), (2,3), (2,4), (3,4)]

theorem pair6_check2W :
    check2W s0x_S29 pair6_P pair6_swA [] pair6_D pair6_EA pair6_RA pair6_T2 pair6_B2 = true := by
  decide +kernel

theorem pair6_check1W :
    check1W s0x_S29 pair6_P pair6_swA [] pair6_D pair6_EA pair6_EA pair6_RA pair6_T1 pair6_B2 = true := by
  decide +kernel

theorem lexAny_pair6_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (w1 : ℝ³) (hw1X : ⟪F.N 1, w1⟫ = 0) (hw1Y : ⟪F.N 2, w1⟫ = 0)
    (hA012 : 0 < ⟪F.N 0, w1⟫)
    (hA035 : ⟪F.N 3, w1⟫ < 0)
    (hA124 : ⟪F.N 4, w1⟫ < 0)
    (hA1456 : ⟪F.N 5, w1⟫ < 0)
    (hA234 : ⟪F.N 6, w1⟫ < 0)
    (hT2 : ∀ i j, i ≠ j → ⟪x (pair6_P i), w1⟫ = ⟪x (pair6_P j), w1⟫ →
      (i, j) ∈ pair6_T2 ∨ (j, i) ∈ pair6_T2) :
    Gen.LexAny F := by
  have hs1 : ∀ t ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 9)), SignType.sign ⟪F.N t, w1⟫ = pair6_swA t := by
    intro t ht; fin_cases t <;> simp at ht
    · exact sign_pos hA012
    · exact sign_eq_zero_iff.mpr hw1X
    · exact sign_eq_zero_iff.mpr hw1Y
    · exact sign_neg hA035
    · exact sign_neg hA124
    · exact sign_neg hA1456
    · exact sign_neg hA234
  have hT1_set : ∀ ρ ∈ pair6_RA, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → t ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 9)) := by decide
  have hE1 : ∀ d ∈ pair6_EA, DecOK x pair6_P (w1) d := by
    intro d hd; simp only [pair6_EA, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact decOK_tri F pair6_P pair6_swA 1 5 3 0 1 4 2 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (w1) hw1X
        (hs1 5 (by decide)) (hs1 3 (by decide))
    · exact decOK_tri F pair6_P pair6_swA 2 6 3 0 2 3 1 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (w1) hw1Y
        (hs1 6 (by decide)) (hs1 3 (by decide))
  have hP : Function.Injective (fun i => x (pair6_P i)) := (inj29 F).comp (by decide)
  have hw_ne : w1 ≠ 0 := fun h0 => by rw [h0, inner_zero_right] at hA012; exact lt_irrefl 0 hA012
  have V1 : ViewDataLex F pair6_P w1 pair6_swA pair6_RA [] pair6_EA pair6_T1 :=
    ⟨hw_ne, fun ρ hρ t ht => hs1 t (hT1_set ρ hρ t ht),
     hR_two_lex F pair6_swA pair6_RA w1 hw_ne 1 2 0 2 1 (by decide) (by decide) (by decide) (by decide)
       (by decide) (by decide) (by decide) (by decide) (by decide) hw1X,
     by simp, hE1, hP, hT_allPairs⟩
  have V2 : ViewDataLex F pair6_P w1 pair6_swA pair6_RA [] pair6_EA pair6_T2 :=
    ⟨hw_ne, fun ρ hρ t ht => hs1 t (hT1_set ρ hρ t ht),
     hR_two_lex F pair6_swA pair6_RA w1 hw_ne 1 2 0 2 1 (by decide) (by decide) (by decide) (by decide)
       (by decide) (by decide) (by decide) (by decide) (by decide) hw1X,
     by simp, hE1, hP, hT2⟩
  have hD : ∀ s ∈ pair6_D, ∃ mu : Fin 5 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (pair6_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = s i := by simp [pair6_D]
  exact pair_closure_lex F pair6_P w1 w1 pair6_swA pair6_swA pair6_RA pair6_RA [] []
    pair6_EA pair6_EA pair6_T1 pair6_T2 V1 V2 (inner_self_ne_zero.mpr hw_ne) pair6_D hD pair6_B2 pair6_check1W pair6_check2W

theorem lexAny29_pair4_lex {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : 0 < ⟪(s0x_fac29 N.facets).N 1, x 3 - x 6⟫)
    (h2 : 0 < ⟪(s0x_fac29 N.facets).N 4, x 3 - x 6⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) :=
  lexAny_pair4_lex _ h1 h2

theorem lexAny29_pair6_lex {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : 0 < ⟪(s0x_fac29 N.facets).N 0, lv29 N 1 2⟫)
    (h2 : ⟪(s0x_fac29 N.facets).N 3, lv29 N 1 2⟫ < 0)
    (h3 : ⟪(s0x_fac29 N.facets).N 4, lv29 N 1 2⟫ < 0)
    (h4 : ⟪(s0x_fac29 N.facets).N 5, lv29 N 1 2⟫ < 0)
    (h5 : ⟪(s0x_fac29 N.facets).N 6, lv29 N 1 2⟫ < 0)
    (hf12 : ⟪x (pair6_P 1), lv29 N 1 2⟫ ≠ ⟪x (pair6_P 2), lv29 N 1 2⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by
  refine lexAny_pair6_lex _ (lv29 N 1 2) (by rw [real_inner_comm]; exact Minimality.inner_cross_left _ _)
    (by rw [real_inner_comm]; exact Minimality.inner_cross_right _ _) h1 h2 h3 h4 h5 ?_
  intro i j hij heq
  fin_cases i <;> fin_cases j <;> (first | exact absurd rfl hij | decide | exact absurd heq hf12 | exact absurd heq hf12.symm)

end Minimality.PL29
