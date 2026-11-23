module

public import Minimality.Type29Single
public import Minimality.SVCLex

@[expose] public section

/-!
# Type-29 Single-View Closures, Tie-Tolerant (`SVCLex.svc_local_lex`)

Tie-tolerant (`_lex`) versions of all 18 single-view cells from `Type29Single.lean`
(`e01`, `e24`, and the 16 `SINGLE29` cells), using `Minimality.SVC.svc_local_lex`.
-/

set_option autoImplicit false

open scoped RealInnerProductSpace
open Minimality Minimality.H21 Minimality.SVC Minimality.SVCC

namespace Minimality.PL29

/-- Injectivity of vertices in `NF29`, derived from `N.facets` (`s0x_S29`) via `inj29`. -/
theorem inj29_of_NF29 {x : Fin 7 → ℝ³} (N : NF29 x) : Function.Injective x :=
  inj29 (s0x_fac29 N.facets)

private theorem hR_two_lex {m n p : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (sw : Fin m → SignType) (R : List (SVC.Rim m p))
    (w : ℝ³) (hw : w ≠ 0)
    (t1 t2 : Fin m) (o v1 v2 : Fin n) (ho1 : o ∈ S t1)
    (ho2 : o ∈ S t2) (hv1a : v1 ∉ S t1) (hv1b : v1 ∈ S t2) (hv2a : v2 ∈ S t1)
    (hv2b : v2 ∉ S t2) (hz : ∀ t, sw t = 0 → t = t1 ∨ t = t2)
    (hsd : R.all (fun ρ => decide (ρ.sd t1 ≠ 0 ∧ ρ.sd t2 ≠ 0)) = true)
    (ht1 : sw t1 = 0) (hnw : ⟪F.N t1, w⟫ = 0) :
    ∀ ρ ∈ R, ∃ d1 d2 : ℝ³,
      (∀ t, sw t = 0 → SignType.sign ⟪F.N t, d1⟫ = ρ.sd t) ∧ Split.det3 w d1 d2 ≠ 0 := by
  intro ρ hρ
  obtain ⟨d1, hd1⟩ := hR_two F sw R t1 t2 o v1 v2 ho1 ho2 hv1a hv1b hv2a hv2b hz hsd ρ hρ
  have hsd1 : ρ.sd t1 ≠ 0 := by
    simp only [List.all_eq_true, decide_eq_true_eq] at hsd
    exact (hsd ρ hρ).1
  have hnd : ⟪F.N t1, d1⟫ ≠ 0 := by
    intro h0
    have hs := hd1 t1 ht1
    rw [h0, sign_zero] at hs
    exact hsd1 hs.symm
  obtain ⟨d2, hdet⟩ := exists_det3_ne_zero_of_orth hw hnw hnd
  exact ⟨d1, d2, hd1, hdet⟩


def e01_T : List (Fin 5 × Fin 5) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4)]

theorem e01_checkW : checkW s0x_S29 PA A_sw [(0, 1)] A_D A_R e01_T = true := by
  decide +kernel

theorem lexAny_e01_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (h234 : ⟪F.N 6, x 0 - x 1⟫ < 0) (h356 : ⟪F.N 8, x 0 - x 1⟫ < 0) (hS : Sep123_05 x)
    (hT_e01 : ∀ i j, i ≠ j → ⟪x (PA i), x 0 - x 1⟫ = ⟪x (PA j), x 0 - x 1⟫ → (i, j) ∈ e01_T ∨ (j, i) ∈ e01_T) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ A_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      t ∈ ({0, 1, 2, 3, 4, 5, 6, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ A_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      SignType.sign ⟪F.N t, x 0 - x 1⟫ = A_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_eq_zero_iff.mpr (edge_zero F 0 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 1 (by decide) (by decide))
    · exact sign_pos (edge_pos F 2 (by decide) (by decide))
    · exact sign_pos (edge_pos F 3 (by decide) (by decide))
    · exact sign_neg (edge_neg F 4 (by decide) (by decide))
    · exact sign_neg (edge_neg F 5 (by decide) (by decide))
    · exact sign_neg h234
    · exact sign_neg h356
  refine svc_local_lex F PA (x 0 - x 1) A_sw A_R (by decide) hsw
    (hR_two_lex F A_sw A_R (x 0 - x 1) (sub_ne_zero.mpr ((inj29 F).ne (by decide))) 0 1 0 5 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (edge_zero F 0 (by decide) (by decide)))
    [(0, 1)] ?_ A_D ?_ ((inj29 F).comp (by decide)) e01_T hT_e01 e01_checkW
  · intro ij hij
    simp only [List.mem_singleton] at hij
    subst hij
    exact forced_edge ((inj29 F).ne (by decide))
  · intro s hs
    simp only [A_D, List.mem_singleton] at hs
    subst hs
    exact depA F hS


theorem lexAny29_K1a_e01_lex {x : Fin 7 → ℝ³} (N : NF29 x) (ha2 : N.a2 < 0)
    (h234 : ⟪(s0x_fac29 N.facets).N 6, x 0 - x 1⟫ < 0)
    (h356 : ⟪(s0x_fac29 N.facets).N 8, x 0 - x 1⟫ < 0)
    (hforb_3_4 : ⟪x (PA 3), x 0 - x 1⟫ ≠ ⟪x (PA 4), x 0 - x 1⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by

  refine lexAny_e01_lex _ h234 h356 (sep123_05_of_nf N ha2) ?_

  intro i j hij heq

  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide | exact absurd heq hforb_3_4 | exact absurd heq hforb_3_4.symm

def e24_T : List (Fin 5 × Fin 5) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 4), (2, 3), (2, 4), (3, 4)]

theorem e24_checkW : checkW s0x_S29 PB B_sw [(2, 4)] B_D B_R e24_T = true := by
  decide +kernel

theorem lexAny_e24_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (h015 : ⟪F.N 1, x 2 - x 4⟫ < 0) (h035 : ⟪F.N 3, x 2 - x 4⟫ < 0) (hS : Sep013_24 x)
    (hT_e24 : ∀ i j, i ≠ j → ⟪x (PB i), x 2 - x 4⟫ = ⟪x (PB j), x 2 - x 4⟫ → (i, j) ∈ e24_T ∨ (j, i) ∈ e24_T) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ B_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      t ∈ ({0, 1, 2, 3, 4, 5, 6, 7} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ B_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      SignType.sign ⟪F.N t, x 2 - x 4⟫ = B_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_pos (edge_pos F 0 (by decide) (by decide))
    · exact sign_neg h015
    · exact sign_pos (edge_pos F 2 (by decide) (by decide))
    · exact sign_neg h035
    · exact sign_eq_zero_iff.mpr (edge_zero F 4 (by decide) (by decide))
    · exact sign_neg (edge_neg F 5 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 6 (by decide) (by decide))
    · exact sign_neg (edge_neg F 7 (by decide) (by decide))
  refine svc_local_lex F PB (x 2 - x 4) B_sw B_R (by decide) hsw
    (hR_two_lex F B_sw B_R (x 2 - x 4) (sub_ne_zero.mpr ((inj29 F).ne (by decide))) 4 6 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (edge_zero F 4 (by decide) (by decide)))
    [(2, 4)] ?_ B_D ?_ ((inj29 F).comp (by decide)) e24_T hT_e24 e24_checkW
  · intro ij hij
    simp only [List.mem_singleton] at hij
    subst hij
    exact forced_edge ((inj29 F).ne (by decide))
  · intro s hs
    simp only [B_D, List.mem_singleton] at hs
    subst hs
    exact depB F hS


theorem lexAny29_K1a_e24_lex {x : Fin 7 → ℝ³} (N : NF29 x) (hb0 : 0 < N.b0)
    (h015 : ⟪(s0x_fac29 N.facets).N 1, x 2 - x 4⟫ < 0)
    (h035 : ⟪(s0x_fac29 N.facets).N 3, x 2 - x 4⟫ < 0)
    (hforb_1_3 : ⟪x (PB 1), x 2 - x 4⟫ ≠ ⟪x (PB 3), x 2 - x 4⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by

  refine lexAny_e24_lex _ h015 h035 (sep013_24_of_nf N hb0) ?_

  intro i j hij heq

  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide | exact absurd heq hforb_1_3 | exact absurd heq hforb_1_3.symm

def e05b_T : List (Fin 5 × Fin 5) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 4)]

theorem e05b_checkW : checkW s0x_S29 e05b_P e05b_sw [] e05b_D e05b_R e05b_T = true := by
  decide +kernel

theorem lexAny_e05b_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (h124 : ⟪F.N 4, x 0 - x 5⟫ < 0)
    (h234 : ⟪F.N 6, x 0 - x 5⟫ < 0)
    (hS0 : 0 < PlaneSide x 2 3 5 0 1)
    (hT_e05b : ∀ i j, i ≠ j → ⟪x (e05b_P i), x 0 - x 5⟫ = ⟪x (e05b_P j), x 0 - x 5⟫ → (i, j) ∈ e05b_T ∨ (j, i) ∈ e05b_T) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ e05b_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      t ∈ ({0, 1, 2, 3, 4, 5, 6, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ e05b_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      SignType.sign ⟪F.N t, x 0 - x 5⟫ = e05b_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_pos (edge_pos F 0 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 1 (by decide) (by decide))
    · exact sign_pos (edge_pos F 2 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 3 (by decide) (by decide))
    · exact sign_neg h124
    · exact sign_neg (edge_neg F 5 (by decide) (by decide))
    · exact sign_neg h234
    · exact sign_neg (edge_neg F 8 (by decide) (by decide))
  refine svc_local_lex F e05b_P (x 0 - x 5) e05b_sw e05b_R (by decide) hsw
    (hR_two_lex F e05b_sw e05b_R (x 0 - x 5) (sub_ne_zero.mpr ((inj29 F).ne (by decide))) 1 3 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (edge_zero F 1 (by decide) (by decide)))
    [] (by simp) e05b_D ?_ ((inj29 F).comp (by decide)) e05b_T hT_e05b e05b_checkW
  intro s hs
  simp only [e05b_D, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst hs
  exact e05b_dep0 F hS0



theorem lexAny29_K1b_e05_lex {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : 0 < N.a2)
    (h2 : ⟪(s0x_fac29 N.facets).N 4, x 0 - x 5⟫ < 0)
    (h3 : ⟪(s0x_fac29 N.facets).N 6, x 0 - x 5⟫ < 0)
    (hforb_1_4 : ⟪x (e05b_P 1), x 0 - x 5⟫ ≠ ⟪x (e05b_P 4), x 0 - x 5⟫) (hforb_2_3 : ⟪x (e05b_P 2), x 0 - x 5⟫ ≠ ⟪x (e05b_P 3), x 0 - x 5⟫) (hforb_3_4 : ⟪x (e05b_P 3), x 0 - x 5⟫ ≠ ⟪x (e05b_P 4), x 0 - x 5⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by

  refine lexAny_e05b_lex _ h2 h3 (ps23501_pos N h1) ?_

  intro i j hij heq

  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide | exact absurd heq hforb_1_4 | exact absurd heq hforb_1_4.symm | exact absurd heq hforb_2_3 | exact absurd heq hforb_2_3.symm | exact absurd heq hforb_3_4 | exact absurd heq hforb_3_4.symm

def e12b_T : List (Fin 5 × Fin 5) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 3), (1, 4), (2, 3), (2, 4)]

theorem e12b_checkW : checkW s0x_S29 e12b_P e12b_sw [] e12b_D e12b_R e12b_T = true := by
  decide +kernel

theorem lexAny_e12b_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (h035 : 0 < ⟪F.N 3, x 1 - x 2⟫)
    (h346 : 0 < ⟪F.N 7, x 1 - x 2⟫)
    (hS0 : 0 < PlaneSide x 1 3 4 0 2)
    (hT_e12b : ∀ i j, i ≠ j → ⟪x (e12b_P i), x 1 - x 2⟫ = ⟪x (e12b_P j), x 1 - x 2⟫ → (i, j) ∈ e12b_T ∨ (j, i) ∈ e12b_T) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ e12b_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      t ∈ ({0, 1, 2, 3, 4, 5, 6, 7} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ e12b_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      SignType.sign ⟪F.N t, x 1 - x 2⟫ = e12b_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_eq_zero_iff.mpr (edge_zero F 0 (by decide) (by decide))
    · exact sign_pos (edge_pos F 1 (by decide) (by decide))
    · exact sign_neg (edge_neg F 2 (by decide) (by decide))
    · exact sign_pos h035
    · exact sign_eq_zero_iff.mpr (edge_zero F 4 (by decide) (by decide))
    · exact sign_pos (edge_pos F 5 (by decide) (by decide))
    · exact sign_neg (edge_neg F 6 (by decide) (by decide))
    · exact sign_pos h346
  refine svc_local_lex F e12b_P (x 1 - x 2) e12b_sw e12b_R (by decide) hsw
    (hR_two_lex F e12b_sw e12b_R (x 1 - x 2) (sub_ne_zero.mpr ((inj29 F).ne (by decide))) 0 4 1 4 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (edge_zero F 0 (by decide) (by decide)))
    [] (by simp) e12b_D ?_ ((inj29 F).comp (by decide)) e12b_T hT_e12b e12b_checkW
  intro s hs
  simp only [e12b_D, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst hs
  exact e12b_dep0 F hS0



theorem lexAny29_K1b_e12_lex {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : N.b0 < 0)
    (h2 : 0 < ⟪(s0x_fac29 N.facets).N 3, x 1 - x 2⟫)
    (h3 : 0 < ⟪(s0x_fac29 N.facets).N 7, x 1 - x 2⟫)
    (hforb_1_2 : ⟪x (e12b_P 1), x 1 - x 2⟫ ≠ ⟪x (e12b_P 2), x 1 - x 2⟫) (hforb_3_4 : ⟪x (e12b_P 3), x 1 - x 2⟫ ≠ ⟪x (e12b_P 4), x 1 - x 2⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by

  refine lexAny_e12b_lex _ h2 h3 (ps13402_pos N h1) ?_

  intro i j hij heq

  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide | exact absurd heq hforb_1_2 | exact absurd heq hforb_1_2.symm | exact absurd heq hforb_3_4 | exact absurd heq hforb_3_4.symm

def e02a_T : List (Fin 5 × Fin 5) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 3), (1, 4), (2, 4)]

theorem e02a_checkW : checkW s0x_S29 e02a_P e02a_sw [] e02a_D e02a_R e02a_T = true := by
  decide +kernel

theorem lexAny_e02a_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (h1456 : 0 < ⟪F.N 5, x 0 - x 2⟫)
    (h346 : 0 < ⟪F.N 7, x 0 - x 2⟫)
    (hS0 : PlaneSide x 1 3 4 0 2 < 0)
    (hT_e02a : ∀ i j, i ≠ j → ⟪x (e02a_P i), x 0 - x 2⟫ = ⟪x (e02a_P j), x 0 - x 2⟫ → (i, j) ∈ e02a_T ∨ (j, i) ∈ e02a_T) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ e02a_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      t ∈ ({0, 1, 2, 3, 4, 5, 6, 7} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ e02a_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      SignType.sign ⟪F.N t, x 0 - x 2⟫ = e02a_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_eq_zero_iff.mpr (edge_zero F 0 (by decide) (by decide))
    · exact sign_pos (edge_pos F 1 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 2 (by decide) (by decide))
    · exact sign_pos (edge_pos F 3 (by decide) (by decide))
    · exact sign_neg (edge_neg F 4 (by decide) (by decide))
    · exact sign_pos h1456
    · exact sign_neg (edge_neg F 6 (by decide) (by decide))
    · exact sign_pos h346
  refine svc_local_lex F e02a_P (x 0 - x 2) e02a_sw e02a_R (by decide) hsw
    (hR_two_lex F e02a_sw e02a_R (x 0 - x 2) (sub_ne_zero.mpr ((inj29 F).ne (by decide))) 0 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (edge_zero F 0 (by decide) (by decide)))
    [] (by simp) e02a_D ?_ ((inj29 F).comp (by decide)) e02a_T hT_e02a e02a_checkW
  intro s hs
  simp only [e02a_D, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst hs
  exact e02a_dep0 F hS0



theorem lexAny29_K1a_e02_lex {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : 0 < N.b0)
    (h2 : 0 < ⟪(s0x_fac29 N.facets).N 5, x 0 - x 2⟫)
    (h3 : 0 < ⟪(s0x_fac29 N.facets).N 7, x 0 - x 2⟫)
    (hforb_1_2 : ⟪x (e02a_P 1), x 0 - x 2⟫ ≠ ⟪x (e02a_P 2), x 0 - x 2⟫) (hforb_2_3 : ⟪x (e02a_P 2), x 0 - x 2⟫ ≠ ⟪x (e02a_P 3), x 0 - x 2⟫) (hforb_3_4 : ⟪x (e02a_P 3), x 0 - x 2⟫ ≠ ⟪x (e02a_P 4), x 0 - x 2⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by

  refine lexAny_e02a_lex _ h2 h3 (ps13402_neg N h1) ?_

  intro i j hij heq

  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide | exact absurd heq hforb_1_2 | exact absurd heq hforb_1_2.symm | exact absurd heq hforb_2_3 | exact absurd heq hforb_2_3.symm | exact absurd heq hforb_3_4 | exact absurd heq hforb_3_4.symm

def e15a_T : List (Fin 6 × Fin 6) := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 5), (2, 4), (2, 5), (3, 4), (4, 5)]

theorem e15a_checkW : checkW s0x_S29 e15a_P e15a_sw [] e15a_D e15a_R e15a_T = true := by
  decide +kernel

theorem lexAny_e15a_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (h023 : ⟪F.N 2, x 1 - x 5⟫ < 0)
    (h234 : ⟪F.N 6, x 1 - x 5⟫ < 0)
    (h346 : ⟪F.N 7, x 1 - x 5⟫ < 0)
    (hS0 : 0 < PlaneSide x 2 4 5 0 1)
    (hS1 : 0 < PlaneSide x 2 5 6 0 1)
    (hT_e15a : ∀ i j, i ≠ j → ⟪x (e15a_P i), x 1 - x 5⟫ = ⟪x (e15a_P j), x 1 - x 5⟫ → (i, j) ∈ e15a_T ∨ (j, i) ∈ e15a_T) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ e15a_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      t ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ e15a_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      SignType.sign ⟪F.N t, x 1 - x 5⟫ = e15a_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_pos (edge_pos F 0 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 1 (by decide) (by decide))
    · exact sign_neg h023
    · exact sign_neg (edge_neg F 3 (by decide) (by decide))
    · exact sign_pos (edge_pos F 4 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 5 (by decide) (by decide))
    · exact sign_neg h234
    · exact sign_neg h346
    · exact sign_neg (edge_neg F 8 (by decide) (by decide))
  refine svc_local_lex F e15a_P (x 1 - x 5) e15a_sw e15a_R (by decide) hsw
    (hR_two_lex F e15a_sw e15a_R (x 1 - x 5) (sub_ne_zero.mpr ((inj29 F).ne (by decide))) 1 5 1 4 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (edge_zero F 1 (by decide) (by decide)))
    [] (by simp) e15a_D ?_ ((inj29 F).comp (by decide)) e15a_T hT_e15a e15a_checkW
  intro s hs
  simp only [e15a_D, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact e15a_dep0 F hS0
  · exact e15a_dep1 F hS1
  · exact e15a_dep2 F
  · exact e15a_dep3 F
  · exact e15a_dep4 F



theorem lexAny29_K1a_e15_lex {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : N.V < 0)
    (h2 : ⟪(s0x_fac29 N.facets).N 2, x 1 - x 5⟫ < 0)
    (h3 : ⟪(s0x_fac29 N.facets).N 6, x 1 - x 5⟫ < 0)
    (h4 : ⟪(s0x_fac29 N.facets).N 7, x 1 - x 5⟫ < 0)
    (h5 : 0 < PlaneSide x 2 5 6 0 1)
    (hforb_1_4 : ⟪x (e15a_P 1), x 1 - x 5⟫ ≠ ⟪x (e15a_P 4), x 1 - x 5⟫) (hforb_2_3 : ⟪x (e15a_P 2), x 1 - x 5⟫ ≠ ⟪x (e15a_P 3), x 1 - x 5⟫) (hforb_3_5 : ⟪x (e15a_P 3), x 1 - x 5⟫ ≠ ⟪x (e15a_P 5), x 1 - x 5⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by

  refine lexAny_e15a_lex _ h2 h3 h4 (ps24501_pos N h1) h5 ?_

  intro i j hij heq

  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide | exact absurd heq hforb_1_4 | exact absurd heq hforb_1_4.symm | exact absurd heq hforb_2_3 | exact absurd heq hforb_2_3.symm | exact absurd heq hforb_3_5 | exact absurd heq hforb_3_5.symm

def e15a2_T : List (Fin 6 × Fin 6) := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 5), (2, 3), (2, 4), (3, 4), (3, 5)]

theorem e15a2_checkW : checkW s0x_S29 e15a2_P e15a2_sw [] e15a2_D e15a2_R e15a2_T = true := by
  decide +kernel

theorem lexAny_e15a2_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (h023 : 0 < ⟪F.N 2, x 1 - x 5⟫)
    (h346 : 0 < ⟪F.N 7, x 1 - x 5⟫)
    (hS0 : 0 < PlaneSide x 1 3 4 0 5)
    (hT_e15a2 : ∀ i j, i ≠ j → ⟪x (e15a2_P i), x 1 - x 5⟫ = ⟪x (e15a2_P j), x 1 - x 5⟫ → (i, j) ∈ e15a2_T ∨ (j, i) ∈ e15a2_T) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ e15a2_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      t ∈ ({0, 1, 2, 3, 4, 5, 7, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ e15a2_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      SignType.sign ⟪F.N t, x 1 - x 5⟫ = e15a2_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_pos (edge_pos F 0 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 1 (by decide) (by decide))
    · exact sign_pos h023
    · exact sign_neg (edge_neg F 3 (by decide) (by decide))
    · exact sign_pos (edge_pos F 4 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 5 (by decide) (by decide))
    · exact sign_pos h346
    · exact sign_neg (edge_neg F 8 (by decide) (by decide))
  refine svc_local_lex F e15a2_P (x 1 - x 5) e15a2_sw e15a2_R (by decide) hsw
    (hR_two_lex F e15a2_sw e15a2_R (x 1 - x 5) (sub_ne_zero.mpr ((inj29 F).ne (by decide))) 1 5 1 4 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (edge_zero F 1 (by decide) (by decide)))
    [] (by simp) e15a2_D ?_ ((inj29 F).comp (by decide)) e15a2_T hT_e15a2 e15a2_checkW
  intro s hs
  simp only [e15a2_D, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact e15a2_dep0 F hS0
  · exact e15a2_dep1 F
  · exact e15a2_dep2 F
  · exact e15a2_dep3 F
  · exact e15a2_dep4 F



theorem lexAny29_K1a_e15_2_lex {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : 0 < N.b0)
    (h2 : 0 < ⟪(s0x_fac29 N.facets).N 2, x 1 - x 5⟫)
    (h3 : 0 < ⟪(s0x_fac29 N.facets).N 7, x 1 - x 5⟫)
    (hforb_1_4 : ⟪x (e15a2_P 1), x 1 - x 5⟫ ≠ ⟪x (e15a2_P 4), x 1 - x 5⟫) (hforb_2_5 : ⟪x (e15a2_P 2), x 1 - x 5⟫ ≠ ⟪x (e15a2_P 5), x 1 - x 5⟫) (hforb_4_5 : ⟪x (e15a2_P 4), x 1 - x 5⟫ ≠ ⟪x (e15a2_P 5), x 1 - x 5⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by

  refine lexAny_e15a2_lex _ h2 h3 (ps13405_pos N h1) ?_

  intro i j hij heq

  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide | exact absurd heq hforb_1_4 | exact absurd heq hforb_1_4.symm | exact absurd heq hforb_2_5 | exact absurd heq hforb_2_5.symm | exact absurd heq hforb_4_5 | exact absurd heq hforb_4_5.symm

def e02b_T : List (Fin 5 × Fin 5) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 3), (1, 4), (2, 4)]

theorem e02b_checkW : checkW s0x_S29 e02b_P e02b_sw [] e02b_D e02b_R e02b_T = true := by
  decide +kernel

theorem lexAny_e02b_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (h1456 : ⟪F.N 5, x 0 - x 2⟫ < 0)
    (h356 : ⟪F.N 8, x 0 - x 2⟫ < 0)
    (hS0 : 0 < PlaneSide x 2 3 5 0 1)
    (hT_e02b : ∀ i j, i ≠ j → ⟪x (e02b_P i), x 0 - x 2⟫ = ⟪x (e02b_P j), x 0 - x 2⟫ → (i, j) ∈ e02b_T ∨ (j, i) ∈ e02b_T) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ e02b_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      t ∈ ({0, 1, 2, 3, 4, 5, 6, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ e02b_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      SignType.sign ⟪F.N t, x 0 - x 2⟫ = e02b_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_eq_zero_iff.mpr (edge_zero F 0 (by decide) (by decide))
    · exact sign_pos (edge_pos F 1 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 2 (by decide) (by decide))
    · exact sign_pos (edge_pos F 3 (by decide) (by decide))
    · exact sign_neg (edge_neg F 4 (by decide) (by decide))
    · exact sign_neg h1456
    · exact sign_neg (edge_neg F 6 (by decide) (by decide))
    · exact sign_neg h356
  refine svc_local_lex F e02b_P (x 0 - x 2) e02b_sw e02b_R (by decide) hsw
    (hR_two_lex F e02b_sw e02b_R (x 0 - x 2) (sub_ne_zero.mpr ((inj29 F).ne (by decide))) 0 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (edge_zero F 0 (by decide) (by decide)))
    [] (by simp) e02b_D ?_ ((inj29 F).comp (by decide)) e02b_T hT_e02b e02b_checkW
  intro s hs
  simp only [e02b_D, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst hs
  exact e02b_dep0 F hS0



theorem lexAny29_K1b_e02_lex {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : 0 < N.a2)
    (h2 : ⟪(s0x_fac29 N.facets).N 5, x 0 - x 2⟫ < 0)
    (h3 : ⟪(s0x_fac29 N.facets).N 8, x 0 - x 2⟫ < 0)
    (hforb_1_2 : ⟪x (e02b_P 1), x 0 - x 2⟫ ≠ ⟪x (e02b_P 2), x 0 - x 2⟫) (hforb_2_3 : ⟪x (e02b_P 2), x 0 - x 2⟫ ≠ ⟪x (e02b_P 3), x 0 - x 2⟫) (hforb_3_4 : ⟪x (e02b_P 3), x 0 - x 2⟫ ≠ ⟪x (e02b_P 4), x 0 - x 2⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by

  refine lexAny_e02b_lex _ h2 h3 (ps23501_pos N h1) ?_

  intro i j hij heq

  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide | exact absurd heq hforb_1_2 | exact absurd heq hforb_1_2.symm | exact absurd heq hforb_2_3 | exact absurd heq hforb_2_3.symm | exact absurd heq hforb_3_4 | exact absurd heq hforb_3_4.symm

def e14b_T : List (Fin 6 × Fin 6) := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 5), (3, 4), (3, 5)]

theorem e14b_checkW : checkW s0x_S29 e14b_P e14b_sw [] e14b_D e14b_R e14b_T = true := by
  decide +kernel

theorem lexAny_e14b_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (h023 : ⟪F.N 2, x 1 - x 4⟫ < 0)
    (h035 : ⟪F.N 3, x 1 - x 4⟫ < 0)
    (h356 : ⟪F.N 8, x 1 - x 4⟫ < 0)
    (hS0 : PlaneSide x 2 4 5 0 1 < 0)
    (hS1 : PlaneSide x 2 4 6 0 1 < 0)
    (hT_e14b : ∀ i j, i ≠ j → ⟪x (e14b_P i), x 1 - x 4⟫ = ⟪x (e14b_P j), x 1 - x 4⟫ → (i, j) ∈ e14b_T ∨ (j, i) ∈ e14b_T) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ e14b_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      t ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ e14b_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      SignType.sign ⟪F.N t, x 1 - x 4⟫ = e14b_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_pos (edge_pos F 0 (by decide) (by decide))
    · exact sign_pos (edge_pos F 1 (by decide) (by decide))
    · exact sign_neg h023
    · exact sign_neg h035
    · exact sign_eq_zero_iff.mpr (edge_zero F 4 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 5 (by decide) (by decide))
    · exact sign_neg (edge_neg F 6 (by decide) (by decide))
    · exact sign_neg (edge_neg F 7 (by decide) (by decide))
    · exact sign_neg h356
  refine svc_local_lex F e14b_P (x 1 - x 4) e14b_sw e14b_R (by decide) hsw
    (hR_two_lex F e14b_sw e14b_R (x 1 - x 4) (sub_ne_zero.mpr ((inj29 F).ne (by decide))) 4 5 1 5 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (edge_zero F 4 (by decide) (by decide)))
    [] (by simp) e14b_D ?_ ((inj29 F).comp (by decide)) e14b_T hT_e14b e14b_checkW
  intro s hs
  simp only [e14b_D, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact e14b_dep0 F hS0
  · exact e14b_dep1 F hS1
  · exact e14b_dep2 F
  · exact e14b_dep3 F
  · exact e14b_dep4 F



theorem lexAny29_K1b_e14_lex {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : 0 < N.V)
    (h2 : ⟪(s0x_fac29 N.facets).N 2, x 1 - x 4⟫ < 0)
    (h3 : ⟪(s0x_fac29 N.facets).N 3, x 1 - x 4⟫ < 0)
    (h4 : ⟪(s0x_fac29 N.facets).N 8, x 1 - x 4⟫ < 0)
    (h5 : PlaneSide x 2 4 6 0 1 < 0)
    (hforb_2_3 : ⟪x (e14b_P 2), x 1 - x 4⟫ ≠ ⟪x (e14b_P 3), x 1 - x 4⟫) (hforb_2_4 : ⟪x (e14b_P 2), x 1 - x 4⟫ ≠ ⟪x (e14b_P 4), x 1 - x 4⟫) (hforb_4_5 : ⟪x (e14b_P 4), x 1 - x 4⟫ ≠ ⟪x (e14b_P 5), x 1 - x 4⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by

  refine lexAny_e14b_lex _ h2 h3 h4 (ps24501_neg N h1) h5 ?_

  intro i j hij heq

  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide | exact absurd heq hforb_2_3 | exact absurd heq hforb_2_3.symm | exact absurd heq hforb_2_4 | exact absurd heq hforb_2_4.symm | exact absurd heq hforb_4_5 | exact absurd heq hforb_4_5.symm

def e14b2_T : List (Fin 6 × Fin 6) := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 4), (1, 5), (2, 3), (2, 4), (3, 4), (3, 5)]

theorem e14b2_checkW : checkW s0x_S29 e14b2_P e14b2_sw [] e14b2_D e14b2_R e14b2_T = true := by
  decide +kernel

theorem lexAny_e14b2_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (h023 : 0 < ⟪F.N 2, x 1 - x 4⟫)
    (h356 : 0 < ⟪F.N 8, x 1 - x 4⟫)
    (hS0 : PlaneSide x 2 3 5 1 4 < 0)
    (hT_e14b2 : ∀ i j, i ≠ j → ⟪x (e14b2_P i), x 1 - x 4⟫ = ⟪x (e14b2_P j), x 1 - x 4⟫ → (i, j) ∈ e14b2_T ∨ (j, i) ∈ e14b2_T) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ e14b2_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      t ∈ ({0, 1, 2, 4, 5, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ e14b2_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      SignType.sign ⟪F.N t, x 1 - x 4⟫ = e14b2_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_pos (edge_pos F 0 (by decide) (by decide))
    · exact sign_pos (edge_pos F 1 (by decide) (by decide))
    · exact sign_pos h023
    · exact sign_eq_zero_iff.mpr (edge_zero F 4 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 5 (by decide) (by decide))
    · exact sign_neg (edge_neg F 6 (by decide) (by decide))
    · exact sign_neg (edge_neg F 7 (by decide) (by decide))
    · exact sign_pos h356
  refine svc_local_lex F e14b2_P (x 1 - x 4) e14b2_sw e14b2_R (by decide) hsw
    (hR_two_lex F e14b2_sw e14b2_R (x 1 - x 4) (sub_ne_zero.mpr ((inj29 F).ne (by decide))) 4 5 1 5 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (edge_zero F 4 (by decide) (by decide)))
    [] (by simp) e14b2_D ?_ ((inj29 F).comp (by decide)) e14b2_T hT_e14b2 e14b2_checkW
  intro s hs
  simp only [e14b2_D, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact e14b2_dep0 F hS0
  · exact e14b2_dep1 F
  · exact e14b2_dep2 F
  · exact e14b2_dep3 F
  · exact e14b2_dep4 F



theorem lexAny29_K1b_e14_2_lex {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : 0 < N.a2)
    (h2 : 0 < ⟪(s0x_fac29 N.facets).N 2, x 1 - x 4⟫)
    (h3 : 0 < ⟪(s0x_fac29 N.facets).N 8, x 1 - x 4⟫)
    (hforb_1_3 : ⟪x (e14b2_P 1), x 1 - x 4⟫ ≠ ⟪x (e14b2_P 3), x 1 - x 4⟫) (hforb_2_5 : ⟪x (e14b2_P 2), x 1 - x 4⟫ ≠ ⟪x (e14b2_P 5), x 1 - x 4⟫) (hforb_4_5 : ⟪x (e14b2_P 4), x 1 - x 4⟫ ≠ ⟪x (e14b2_P 5), x 1 - x 4⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by

  refine lexAny_e14b2_lex _ h2 h3 (ps23514_neg N h1) ?_

  intro i j hij heq

  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide | exact absurd heq hforb_1_3 | exact absurd heq hforb_1_3.symm | exact absurd heq hforb_2_5 | exact absurd heq hforb_2_5.symm | exact absurd heq hforb_4_5 | exact absurd heq hforb_4_5.symm

def e15a3_T : List (Fin 6 × Fin 6) := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 5), (2, 4), (2, 5), (3, 4), (4, 5)]

theorem e15a3_checkW : checkW s0x_S29 e15a3_P e15a3_sw [] e15a3_D e15a3_R e15a3_T = true := by
  decide +kernel

theorem lexAny_e15a3_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (h023 : 0 < ⟪F.N 2, x 1 - x 5⟫)
    (h234 : 0 < ⟪F.N 6, x 1 - x 5⟫)
    (h346 : ⟪F.N 7, x 1 - x 5⟫ < 0)
    (hS0 : 0 < PlaneSide x 1 3 4 0 5)
    (hT_e15a3 : ∀ i j, i ≠ j → ⟪x (e15a3_P i), x 1 - x 5⟫ = ⟪x (e15a3_P j), x 1 - x 5⟫ → (i, j) ∈ e15a3_T ∨ (j, i) ∈ e15a3_T) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ e15a3_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      t ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ e15a3_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      SignType.sign ⟪F.N t, x 1 - x 5⟫ = e15a3_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_pos (edge_pos F 0 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 1 (by decide) (by decide))
    · exact sign_pos h023
    · exact sign_neg (edge_neg F 3 (by decide) (by decide))
    · exact sign_pos (edge_pos F 4 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 5 (by decide) (by decide))
    · exact sign_pos h234
    · exact sign_neg h346
    · exact sign_neg (edge_neg F 8 (by decide) (by decide))
  refine svc_local_lex F e15a3_P (x 1 - x 5) e15a3_sw e15a3_R (by decide) hsw
    (hR_two_lex F e15a3_sw e15a3_R (x 1 - x 5) (sub_ne_zero.mpr ((inj29 F).ne (by decide))) 1 5 1 4 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (edge_zero F 1 (by decide) (by decide)))
    [] (by simp) e15a3_D ?_ ((inj29 F).comp (by decide)) e15a3_T hT_e15a3 e15a3_checkW
  intro s hs
  simp only [e15a3_D, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact e15a3_dep0 F hS0
  · exact e15a3_dep1 F
  · exact e15a3_dep2 F
  · exact e15a3_dep3 F
  · exact e15a3_dep4 F



theorem lexAny29_K1a_e15_3_lex {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : 0 < N.b0)
    (h2 : 0 < ⟪(s0x_fac29 N.facets).N 2, x 1 - x 5⟫)
    (h3 : 0 < ⟪(s0x_fac29 N.facets).N 6, x 1 - x 5⟫)
    (h4 : ⟪(s0x_fac29 N.facets).N 7, x 1 - x 5⟫ < 0)
    (hforb_1_4 : ⟪x (e15a3_P 1), x 1 - x 5⟫ ≠ ⟪x (e15a3_P 4), x 1 - x 5⟫) (hforb_2_3 : ⟪x (e15a3_P 2), x 1 - x 5⟫ ≠ ⟪x (e15a3_P 3), x 1 - x 5⟫) (hforb_3_5 : ⟪x (e15a3_P 3), x 1 - x 5⟫ ≠ ⟪x (e15a3_P 5), x 1 - x 5⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by

  refine lexAny_e15a3_lex _ h2 h3 h4 (ps13405_pos N h1) ?_

  intro i j hij heq

  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide | exact absurd heq hforb_1_4 | exact absurd heq hforb_1_4.symm | exact absurd heq hforb_2_3 | exact absurd heq hforb_2_3.symm | exact absurd heq hforb_3_5 | exact absurd heq hforb_3_5.symm

def e14b3_T : List (Fin 6 × Fin 6) := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 4), (1, 5), (2, 3), (2, 5), (3, 4), (3, 5)]

theorem e14b3_checkW : checkW s0x_S29 e14b3_P e14b3_sw [] e14b3_D e14b3_R e14b3_T = true := by
  decide +kernel

theorem lexAny_e14b3_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (h023 : 0 < ⟪F.N 2, x 1 - x 4⟫)
    (h035 : 0 < ⟪F.N 3, x 1 - x 4⟫)
    (h356 : ⟪F.N 8, x 1 - x 4⟫ < 0)
    (hS0 : PlaneSide x 2 3 5 1 4 < 0)
    (hT_e14b3 : ∀ i j, i ≠ j → ⟪x (e14b3_P i), x 1 - x 4⟫ = ⟪x (e14b3_P j), x 1 - x 4⟫ → (i, j) ∈ e14b3_T ∨ (j, i) ∈ e14b3_T) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ e14b3_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      t ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ e14b3_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      SignType.sign ⟪F.N t, x 1 - x 4⟫ = e14b3_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_pos (edge_pos F 0 (by decide) (by decide))
    · exact sign_pos (edge_pos F 1 (by decide) (by decide))
    · exact sign_pos h023
    · exact sign_pos h035
    · exact sign_eq_zero_iff.mpr (edge_zero F 4 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 5 (by decide) (by decide))
    · exact sign_neg (edge_neg F 6 (by decide) (by decide))
    · exact sign_neg (edge_neg F 7 (by decide) (by decide))
    · exact sign_neg h356
  refine svc_local_lex F e14b3_P (x 1 - x 4) e14b3_sw e14b3_R (by decide) hsw
    (hR_two_lex F e14b3_sw e14b3_R (x 1 - x 4) (sub_ne_zero.mpr ((inj29 F).ne (by decide))) 4 5 1 5 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (edge_zero F 4 (by decide) (by decide)))
    [] (by simp) e14b3_D ?_ ((inj29 F).comp (by decide)) e14b3_T hT_e14b3 e14b3_checkW
  intro s hs
  simp only [e14b3_D, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact e14b3_dep0 F hS0
  · exact e14b3_dep1 F
  · exact e14b3_dep2 F
  · exact e14b3_dep3 F
  · exact e14b3_dep4 F



theorem lexAny29_K1b_e14_3_lex {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : 0 < N.a2)
    (h2 : 0 < ⟪(s0x_fac29 N.facets).N 2, x 1 - x 4⟫)
    (h3 : 0 < ⟪(s0x_fac29 N.facets).N 3, x 1 - x 4⟫)
    (h4 : ⟪(s0x_fac29 N.facets).N 8, x 1 - x 4⟫ < 0)
    (hforb_1_3 : ⟪x (e14b3_P 1), x 1 - x 4⟫ ≠ ⟪x (e14b3_P 3), x 1 - x 4⟫) (hforb_2_4 : ⟪x (e14b3_P 2), x 1 - x 4⟫ ≠ ⟪x (e14b3_P 4), x 1 - x 4⟫) (hforb_4_5 : ⟪x (e14b3_P 4), x 1 - x 4⟫ ≠ ⟪x (e14b3_P 5), x 1 - x 4⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by

  refine lexAny_e14b3_lex _ h2 h3 h4 (ps23514_neg N h1) ?_

  intro i j hij heq

  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide | exact absurd heq hforb_1_3 | exact absurd heq hforb_1_3.symm | exact absurd heq hforb_2_4 | exact absurd heq hforb_2_4.symm | exact absurd heq hforb_4_5 | exact absurd heq hforb_4_5.symm

def e24a2_T : List (Fin 5 × Fin 5) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 4), (2, 3), (3, 4)]

theorem e24a2_checkW : checkW s0x_S29 e24a2_P e24a2_sw [] e24a2_D e24a2_R e24a2_T = true := by
  decide +kernel

theorem lexAny_e24a2_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (h015 : 0 < ⟪F.N 1, x 2 - x 4⟫)
    (h035 : 0 < ⟪F.N 3, x 2 - x 4⟫)
    (h356 : ⟪F.N 8, x 2 - x 4⟫ < 0)
    (hS0 : 0 < PlaneSide x 2 3 5 1 4)
    (hT_e24a2 : ∀ i j, i ≠ j → ⟪x (e24a2_P i), x 2 - x 4⟫ = ⟪x (e24a2_P j), x 2 - x 4⟫ → (i, j) ∈ e24a2_T ∨ (j, i) ∈ e24a2_T) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ e24a2_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      t ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ e24a2_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      SignType.sign ⟪F.N t, x 2 - x 4⟫ = e24a2_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_pos (edge_pos F 0 (by decide) (by decide))
    · exact sign_pos h015
    · exact sign_pos (edge_pos F 2 (by decide) (by decide))
    · exact sign_pos h035
    · exact sign_eq_zero_iff.mpr (edge_zero F 4 (by decide) (by decide))
    · exact sign_neg (edge_neg F 5 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 6 (by decide) (by decide))
    · exact sign_neg (edge_neg F 7 (by decide) (by decide))
    · exact sign_neg h356
  refine svc_local_lex F e24a2_P (x 2 - x 4) e24a2_sw e24a2_R (by decide) hsw
    (hR_two_lex F e24a2_sw e24a2_R (x 2 - x 4) (sub_ne_zero.mpr ((inj29 F).ne (by decide))) 4 6 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (edge_zero F 4 (by decide) (by decide)))
    [] (by simp) e24a2_D ?_ ((inj29 F).comp (by decide)) e24a2_T hT_e24a2 e24a2_checkW
  intro s hs
  simp only [e24a2_D, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst hs
  exact e24a2_dep0 F hS0



theorem lexAny29_K1a_e24_2_lex {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : N.a2 < 0)
    (h2 : 0 < ⟪(s0x_fac29 N.facets).N 1, x 2 - x 4⟫)
    (h3 : 0 < ⟪(s0x_fac29 N.facets).N 3, x 2 - x 4⟫)
    (h4 : ⟪(s0x_fac29 N.facets).N 8, x 2 - x 4⟫ < 0)
    (hforb_1_3 : ⟪x (e24a2_P 1), x 2 - x 4⟫ ≠ ⟪x (e24a2_P 3), x 2 - x 4⟫) (hforb_2_4 : ⟪x (e24a2_P 2), x 2 - x 4⟫ ≠ ⟪x (e24a2_P 4), x 2 - x 4⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by

  refine lexAny_e24a2_lex _ h2 h3 h4 (ps23514_pos N h1) ?_

  intro i j hij heq

  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide | exact absurd heq hforb_1_3 | exact absurd heq hforb_1_3.symm | exact absurd heq hforb_2_4 | exact absurd heq hforb_2_4.symm

def e05b2_T : List (Fin 5 × Fin 5) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (3, 4)]

theorem e05b2_checkW : checkW s0x_S29 e05b2_P e05b2_sw [] e05b2_D e05b2_R e05b2_T = true := by
  decide +kernel

theorem lexAny_e05b2_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (h124 : 0 < ⟪F.N 4, x 0 - x 5⟫)
    (h234 : 0 < ⟪F.N 6, x 0 - x 5⟫)
    (h346 : ⟪F.N 7, x 0 - x 5⟫ < 0)
    (hS0 : PlaneSide x 1 3 4 0 5 < 0)
    (hT_e05b2 : ∀ i j, i ≠ j → ⟪x (e05b2_P i), x 0 - x 5⟫ = ⟪x (e05b2_P j), x 0 - x 5⟫ → (i, j) ∈ e05b2_T ∨ (j, i) ∈ e05b2_T) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ e05b2_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      t ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ e05b2_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      SignType.sign ⟪F.N t, x 0 - x 5⟫ = e05b2_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_pos (edge_pos F 0 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 1 (by decide) (by decide))
    · exact sign_pos (edge_pos F 2 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 3 (by decide) (by decide))
    · exact sign_pos h124
    · exact sign_neg (edge_neg F 5 (by decide) (by decide))
    · exact sign_pos h234
    · exact sign_neg h346
    · exact sign_neg (edge_neg F 8 (by decide) (by decide))
  refine svc_local_lex F e05b2_P (x 0 - x 5) e05b2_sw e05b2_R (by decide) hsw
    (hR_two_lex F e05b2_sw e05b2_R (x 0 - x 5) (sub_ne_zero.mpr ((inj29 F).ne (by decide))) 1 3 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (edge_zero F 1 (by decide) (by decide)))
    [] (by simp) e05b2_D ?_ ((inj29 F).comp (by decide)) e05b2_T hT_e05b2 e05b2_checkW
  intro s hs
  simp only [e05b2_D, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst hs
  exact e05b2_dep0 F hS0



theorem lexAny29_K1b_e05_2_lex {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : N.b0 < 0)
    (h2 : 0 < ⟪(s0x_fac29 N.facets).N 4, x 0 - x 5⟫)
    (h3 : 0 < ⟪(s0x_fac29 N.facets).N 6, x 0 - x 5⟫)
    (h4 : ⟪(s0x_fac29 N.facets).N 7, x 0 - x 5⟫ < 0)
    (hforb_1_4 : ⟪x (e05b2_P 1), x 0 - x 5⟫ ≠ ⟪x (e05b2_P 4), x 0 - x 5⟫) (hforb_2_3 : ⟪x (e05b2_P 2), x 0 - x 5⟫ ≠ ⟪x (e05b2_P 3), x 0 - x 5⟫) (hforb_2_4 : ⟪x (e05b2_P 2), x 0 - x 5⟫ ≠ ⟪x (e05b2_P 4), x 0 - x 5⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by

  refine lexAny_e05b2_lex _ h2 h3 h4 (ps13405_neg N h1) ?_

  intro i j hij heq

  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide | exact absurd heq hforb_1_4 | exact absurd heq hforb_1_4.symm | exact absurd heq hforb_2_3 | exact absurd heq hforb_2_3.symm | exact absurd heq hforb_2_4 | exact absurd heq hforb_2_4.symm

def e03a_T : List (Fin 5 × Fin 5) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4)]

theorem e03a_checkW : checkW s0x_S29 e03a_P e03a_sw [] e03a_D e03a_R e03a_T = true := by
  decide +kernel

theorem lexAny_e03a_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (h124 : ⟪F.N 4, x 0 - x 3⟫ < 0)
    (h1456 : ⟪F.N 5, x 0 - x 3⟫ < 0)
    (hS0 : PlaneSide x 2 3 5 0 1 < 0)
    (hT_e03a : ∀ i j, i ≠ j → ⟪x (e03a_P i), x 0 - x 3⟫ = ⟪x (e03a_P j), x 0 - x 3⟫ → (i, j) ∈ e03a_T ∨ (j, i) ∈ e03a_T) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ e03a_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      t ∈ ({0, 1, 2, 3, 4, 5, 6, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ e03a_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      SignType.sign ⟪F.N t, x 0 - x 3⟫ = e03a_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_pos (edge_pos F 0 (by decide) (by decide))
    · exact sign_pos (edge_pos F 1 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 2 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 3 (by decide) (by decide))
    · exact sign_neg h124
    · exact sign_neg h1456
    · exact sign_neg (edge_neg F 6 (by decide) (by decide))
    · exact sign_neg (edge_neg F 8 (by decide) (by decide))
  refine svc_local_lex F e03a_P (x 0 - x 3) e03a_sw e03a_R (by decide) hsw
    (hR_two_lex F e03a_sw e03a_R (x 0 - x 3) (sub_ne_zero.mpr ((inj29 F).ne (by decide))) 2 3 0 5 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (edge_zero F 2 (by decide) (by decide)))
    [] (by simp) e03a_D ?_ ((inj29 F).comp (by decide)) e03a_T hT_e03a e03a_checkW
  intro s hs
  simp only [e03a_D, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst hs
  exact e03a_dep0 F hS0



theorem lexAny29_K1a_e03_lex {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : N.a2 < 0)
    (h2 : ⟪(s0x_fac29 N.facets).N 4, x 0 - x 3⟫ < 0)
    (h3 : ⟪(s0x_fac29 N.facets).N 5, x 0 - x 3⟫ < 0)
    (hforb_2_3 : ⟪x (e03a_P 2), x 0 - x 3⟫ ≠ ⟪x (e03a_P 3), x 0 - x 3⟫) (hforb_2_4 : ⟪x (e03a_P 2), x 0 - x 3⟫ ≠ ⟪x (e03a_P 4), x 0 - x 3⟫) (hforb_3_4 : ⟪x (e03a_P 3), x 0 - x 3⟫ ≠ ⟪x (e03a_P 4), x 0 - x 3⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by

  refine lexAny_e03a_lex _ h2 h3 (ps23501_neg N h1) ?_

  intro i j hij heq

  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide | exact absurd heq hforb_2_3 | exact absurd heq hforb_2_3.symm | exact absurd heq hforb_2_4 | exact absurd heq hforb_2_4.symm | exact absurd heq hforb_3_4 | exact absurd heq hforb_3_4.symm

def e23b_T : List (Fin 5 × Fin 5) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 4), (3, 4)]

theorem e23b_checkW : checkW s0x_S29 e23b_P e23b_sw [] e23b_D e23b_R e23b_T = true := by
  decide +kernel

theorem lexAny_e23b_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (h015 : ⟪F.N 1, x 2 - x 3⟫ < 0)
    (h1456 : ⟪F.N 5, x 2 - x 3⟫ < 0)
    (hS0 : 0 < PlaneSide x 1 3 4 0 2)
    (hT_e23b : ∀ i j, i ≠ j → ⟪x (e23b_P i), x 2 - x 3⟫ = ⟪x (e23b_P j), x 2 - x 3⟫ → (i, j) ∈ e23b_T ∨ (j, i) ∈ e23b_T) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ e23b_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      t ∈ ({0, 1, 2, 3, 4, 5, 6, 7} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ e23b_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      SignType.sign ⟪F.N t, x 2 - x 3⟫ = e23b_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_pos (edge_pos F 0 (by decide) (by decide))
    · exact sign_neg h015
    · exact sign_eq_zero_iff.mpr (edge_zero F 2 (by decide) (by decide))
    · exact sign_neg (edge_neg F 3 (by decide) (by decide))
    · exact sign_pos (edge_pos F 4 (by decide) (by decide))
    · exact sign_neg h1456
    · exact sign_eq_zero_iff.mpr (edge_zero F 6 (by decide) (by decide))
    · exact sign_neg (edge_neg F 7 (by decide) (by decide))
  refine svc_local_lex F e23b_P (x 2 - x 3) e23b_sw e23b_R (by decide) hsw
    (hR_two_lex F e23b_sw e23b_R (x 2 - x 3) (sub_ne_zero.mpr ((inj29 F).ne (by decide))) 2 6 2 4 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (edge_zero F 2 (by decide) (by decide)))
    [] (by simp) e23b_D ?_ ((inj29 F).comp (by decide)) e23b_T hT_e23b e23b_checkW
  intro s hs
  simp only [e23b_D, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst hs
  exact e23b_dep0 F hS0



theorem lexAny29_K1b_e23_lex {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : N.b0 < 0)
    (h2 : ⟪(s0x_fac29 N.facets).N 1, x 2 - x 3⟫ < 0)
    (h3 : ⟪(s0x_fac29 N.facets).N 5, x 2 - x 3⟫ < 0)
    (hforb_1_4 : ⟪x (e23b_P 1), x 2 - x 3⟫ ≠ ⟪x (e23b_P 4), x 2 - x 3⟫) (hforb_2_3 : ⟪x (e23b_P 2), x 2 - x 3⟫ ≠ ⟪x (e23b_P 3), x 2 - x 3⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by

  refine lexAny_e23b_lex _ h2 h3 (ps13402_pos N h1) ?_

  intro i j hij heq

  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide | exact absurd heq hforb_1_4 | exact absurd heq hforb_1_4.symm | exact absurd heq hforb_2_3 | exact absurd heq hforb_2_3.symm

def l1456x234_T : List (Fin 5 × Fin 5) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4)]

theorem l1456x234_checkW : checkW s0x_S29 l1456x234_P l1456x234_sw [] l1456x234_D l1456x234_R l1456x234_T = true := by
  decide +kernel

theorem lexAny_l1456x234_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (w : ℝ³) (h1456 : ⟪F.N 5, w⟫ = 0) (h234 : ⟪F.N 6, w⟫ = 0)
    (h015 : ⟪F.N 1, w⟫ < 0)
    (h035 : ⟪F.N 3, w⟫ < 0)
    (h124 : ⟪F.N 4, w⟫ < 0)
    (h346 : 0 < ⟪F.N 7, w⟫)
    (h356 : 0 < ⟪F.N 8, w⟫)
    (hT_l1456x234 : ∀ i j, i ≠ j → ⟪x (l1456x234_P i), w⟫ = ⟪x (l1456x234_P j), w⟫ → (i, j) ∈ l1456x234_T ∨ (j, i) ∈ l1456x234_T) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ l1456x234_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      t ∈ ({1, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ l1456x234_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      SignType.sign ⟪F.N t, w⟫ = l1456x234_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_neg h015
    · exact sign_neg h035
    · exact sign_neg h124
    · exact sign_eq_zero_iff.mpr h1456
    · exact sign_eq_zero_iff.mpr h234
    · exact sign_pos h346
    · exact sign_pos h356
  refine svc_local_lex F l1456x234_P w l1456x234_sw l1456x234_R (by decide) hsw
    (hR_two_lex F l1456x234_sw l1456x234_R (w) (fun h0 => by rw [h0, inner_zero_right] at h015; exact lt_irrefl 0 h015) 5 6 4 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h1456)
    [] (by simp) l1456x234_D ?_ ((inj29 F).comp (by decide)) l1456x234_T hT_l1456x234 l1456x234_checkW
  intro s hs
  simp only [l1456x234_D, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact l1456x234_dep0 F
  · exact l1456x234_dep1 F
  · exact l1456x234_dep2 F



theorem lexAny29_l1456x234_lex {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : ⟪(s0x_fac29 N.facets).N 1, lv29 N 5 6⟫ < 0)
    (h2 : ⟪(s0x_fac29 N.facets).N 3, lv29 N 5 6⟫ < 0)
    (h3 : ⟪(s0x_fac29 N.facets).N 4, lv29 N 5 6⟫ < 0)
    (h4 : 0 < ⟪(s0x_fac29 N.facets).N 7, lv29 N 5 6⟫)
    (h5 : 0 < ⟪(s0x_fac29 N.facets).N 8, lv29 N 5 6⟫)
    (hforb_2_3 : ⟪x (l1456x234_P 2), lv29 N 5 6⟫ ≠ ⟪x (l1456x234_P 3), lv29 N 5 6⟫) (hforb_2_4 : ⟪x (l1456x234_P 2), lv29 N 5 6⟫ ≠ ⟪x (l1456x234_P 4), lv29 N 5 6⟫) (hforb_3_4 : ⟪x (l1456x234_P 3), lv29 N 5 6⟫ ≠ ⟪x (l1456x234_P 4), lv29 N 5 6⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by

  refine lexAny_l1456x234_lex _ _ (by rw [real_inner_comm]; exact Minimality.inner_cross_left _ _) (by rw [real_inner_comm]; exact Minimality.inner_cross_right _ _) h1 h2 h3 h4 h5 ?_

  intro i j hij heq

  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide | exact absurd heq hforb_2_3 | exact absurd heq hforb_2_3.symm | exact absurd heq hforb_2_4 | exact absurd heq hforb_2_4.symm | exact absurd heq hforb_3_4 | exact absurd heq hforb_3_4.symm

def l035x1456_T : List (Fin 5 × Fin 5) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4)]

theorem l035x1456_checkW : checkW s0x_S29 l035x1456_P l035x1456_sw [] l035x1456_D l035x1456_R l035x1456_T = true := by
  decide +kernel

theorem lexAny_l035x1456_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (w : ℝ³) (h035 : ⟪F.N 3, w⟫ = 0) (h1456 : ⟪F.N 5, w⟫ = 0)
    (h015 : ⟪F.N 1, w⟫ < 0)
    (h124 : ⟪F.N 4, w⟫ < 0)
    (h234 : ⟪F.N 6, w⟫ < 0)
    (h346 : 0 < ⟪F.N 7, w⟫)
    (h356 : 0 < ⟪F.N 8, w⟫)
    (hT_l035x1456 : ∀ i j, i ≠ j → ⟪x (l035x1456_P i), w⟫ = ⟪x (l035x1456_P j), w⟫ → (i, j) ∈ l035x1456_T ∨ (j, i) ∈ l035x1456_T) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ l035x1456_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      t ∈ ({1, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ l035x1456_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      SignType.sign ⟪F.N t, w⟫ = l035x1456_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_neg h015
    · exact sign_eq_zero_iff.mpr h035
    · exact sign_neg h124
    · exact sign_eq_zero_iff.mpr h1456
    · exact sign_neg h234
    · exact sign_pos h346
    · exact sign_pos h356
  refine svc_local_lex F l035x1456_P w l035x1456_sw l035x1456_R (by decide) hsw
    (hR_two_lex F l035x1456_sw l035x1456_R (w) (fun h0 => by rw [h0, inner_zero_right] at h015; exact lt_irrefl 0 h015) 3 5 5 1 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h035)
    [] (by simp) l035x1456_D ?_ ((inj29 F).comp (by decide)) l035x1456_T hT_l035x1456 l035x1456_checkW
  intro s hs
  simp only [l035x1456_D, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact l035x1456_dep0 F
  · exact l035x1456_dep1 F
  · exact l035x1456_dep2 F



theorem lexAny29_l035x1456_lex {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : ⟪(s0x_fac29 N.facets).N 1, lv29 N 3 5⟫ < 0)
    (h2 : ⟪(s0x_fac29 N.facets).N 4, lv29 N 3 5⟫ < 0)
    (h3 : ⟪(s0x_fac29 N.facets).N 6, lv29 N 3 5⟫ < 0)
    (h4 : 0 < ⟪(s0x_fac29 N.facets).N 7, lv29 N 3 5⟫)
    (h5 : 0 < ⟪(s0x_fac29 N.facets).N 8, lv29 N 3 5⟫)
    (hforb_2_3 : ⟪x (l035x1456_P 2), lv29 N 3 5⟫ ≠ ⟪x (l035x1456_P 3), lv29 N 3 5⟫) (hforb_2_4 : ⟪x (l035x1456_P 2), lv29 N 3 5⟫ ≠ ⟪x (l035x1456_P 4), lv29 N 3 5⟫) (hforb_3_4 : ⟪x (l035x1456_P 3), lv29 N 3 5⟫ ≠ ⟪x (l035x1456_P 4), lv29 N 3 5⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by

  refine lexAny_l035x1456_lex _ _ (by rw [real_inner_comm]; exact Minimality.inner_cross_left _ _) (by rw [real_inner_comm]; exact Minimality.inner_cross_right _ _) h1 h2 h3 h4 h5 ?_

  intro i j hij heq

  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide | exact absurd heq hforb_2_3 | exact absurd heq hforb_2_3.symm | exact absurd heq hforb_2_4 | exact absurd heq hforb_2_4.symm | exact absurd heq hforb_3_4 | exact absurd heq hforb_3_4.symm

end Minimality.PL29
