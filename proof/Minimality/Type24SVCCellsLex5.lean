module

public import Minimality.SVCLex
public import Minimality.Type24SVCCells

@[expose] public section

/-!
# Tie-tolerant SVC cells, `p = 5` (type 24)

Weak-order (`SVC.checkW` / `SVC.svc_local_lex`) versions of the four `p = 5` SVC cells in
`SVCCellHyp`:
- `c08`: `cell_025_235_ppzmppzpp_lex` (all ties tolerated)
- `c19`: `cell_046_346_mmmpzmmmz_lex` (all ties tolerated)
- `c20`: `cell_235_236_pppmmpzzm_lex` (all ties tolerated except `(3, 4)`, i.e. `x 5` vs `x 6`)
- `c22`: `cell_236_346_mmppmmpzz_lex` (all ties tolerated except `(1, 3)`, i.e. `x 2` vs `x 4`)
-/

set_option autoImplicit false

open scoped RealInnerProductSpace
open Minimality Minimality.H21 Minimality.SVCC Minimality.SVCC.Cells Minimality.T24.SAT

namespace Minimality.SVCC.CellsLex

def allPairs (p : ℕ) : List (Fin p × Fin p) :=
  (List.finRange p).flatMap fun a =>
    (List.finRange p).filterMap fun b => if a < b then some (a, b) else none

theorem mem_allPairs {p : ℕ} {i j : Fin p} (hij : i ≠ j) :
    (i, j) ∈ allPairs p ∨ (j, i) ∈ allPairs p := by
  rcases lt_or_gt_of_ne hij with h | h
  · left
    simp only [allPairs, List.mem_flatMap, List.mem_finRange, List.mem_filterMap, true_and]
    exact ⟨i, j, by simp [h]⟩
  · right
    simp only [allPairs, List.mem_flatMap, List.mem_finRange, List.mem_filterMap, true_and]
    exact ⟨j, i, by simp [h]⟩

theorem hR_lex_of_hR {m n p : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (w : ℝ³) (sw : Fin m → SignType) (R : List (SVC.Rim m p))
    (tpos tz : Fin m) (hw : ⟪F.N tpos, w⟫ ≠ 0) (hz : ⟪F.N tz, w⟫ = 0)
    (hsd : ∀ ρ ∈ R, ρ.sd tz ≠ 0)
    (hR : ∀ ρ ∈ R, ∃ d1 : ℝ³, ∀ t, sw t = 0 → SignType.sign ⟪F.N t, d1⟫ = ρ.sd t)
    (hswz : sw tz = 0) :
    ∀ ρ ∈ R, ∃ d1 d2 : ℝ³,
      (∀ t, sw t = 0 → SignType.sign ⟪F.N t, d1⟫ = ρ.sd t) ∧ Split.det3 w d1 d2 ≠ 0 := by
  intro ρ hρ
  obtain ⟨d1, hd1⟩ := hR ρ hρ
  have hNd : ⟪F.N tz, d1⟫ ≠ 0 := by
    intro h0
    have := hd1 tz hswz
    rw [h0, sign_zero] at this
    exact hsd ρ hρ this.symm
  obtain ⟨d2, hdet⟩ := SVC.exists_det3_ne_zero hw hz hNd
  exact ⟨d1, d2, hd1, hdet⟩

/-! ### c08: F025xF235 sig ++0-++0++ -/

theorem c08_checkW :
    SVC.checkW s0x_S24 c08_P c08_sw [(1, 4)] c08_D c08_R (allPairs 5) = true := by
  decide +kernel

theorem cell_025_235_ppzmppzpp_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (h4 : 0 < ⟪F.N 4, (x 2 - x 5)⟫)
    (h8 : 0 < ⟪F.N 8, (x 2 - x 5)⟫) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ c08_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → t ∈ ({0, 2, 3, 4, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ c08_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → SignType.sign ⟪F.N t, (x 2 - x 5)⟫ = c08_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_pos (edge_pos F 0 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 2 (by decide) (by decide))
    · exact sign_neg (edge_neg F 3 (by decide) (by decide))
    · exact sign_pos h4
    · exact sign_eq_zero_iff.mpr (edge_zero F 6 (by decide) (by decide))
    · exact sign_pos (edge_pos F 7 (by decide) (by decide))
    · exact sign_pos h8
  have hR1 := hR_two F c08_sw c08_R 2 6 2 3 0 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hR := hR_lex_of_hR F (x 2 - x 5) c08_sw c08_R 4 2 h4.ne'
    (edge_zero F 2 (by decide) (by decide)) (by decide) hR1 rfl
  have hPinj : Function.Injective (fun i => x (c08_P i)) :=
    (EdgeViewLink.inj_of_fac24 F).comp (by decide : Function.Injective c08_P)
  refine SVC.svc_local_lex F c08_P (x 2 - x 5) c08_sw c08_R (by decide) hsw hR [(1, 4)] ?_
    c08_D (c08_dep F) hPinj (allPairs 5) (fun i j hij _ => mem_allPairs hij) c08_checkW
  intro ij hij
  simp only [List.mem_singleton] at hij
  subst hij
  exact forced_edge ((EdgeViewLink.inj_of_fac24 F).ne (by decide))

/-! ### c19: F046xF346 sig ---+0---0 -/

theorem c19_checkW :
    SVC.checkW s0x_S24 c19_P c19_sw [(2, 4)] c19_D c19_R (allPairs 5) = true := by
  decide +kernel

theorem cell_046_346_mmmpzmmmz_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (h2 : ⟪F.N 2, (x 4 - x 6)⟫ < 0)
    (h6 : ⟪F.N 6, (x 4 - x 6)⟫ < 0) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ c19_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → t ∈ ({1, 2, 3, 4, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ c19_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → SignType.sign ⟪F.N t, (x 4 - x 6)⟫ = c19_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_neg (edge_neg F 1 (by decide) (by decide))
    · exact sign_neg h2
    · exact sign_pos (edge_pos F 3 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 4 (by decide) (by decide))
    · exact sign_neg h6
    · exact sign_neg (edge_neg F 7 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 8 (by decide) (by decide))
  have hR1 := hR_two F c19_sw c19_R 4 8 4 3 0 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hR := hR_lex_of_hR F (x 4 - x 6) c19_sw c19_R 2 4 h2.ne
    (edge_zero F 4 (by decide) (by decide)) (by decide) hR1 rfl
  have hPinj : Function.Injective (fun i => x (c19_P i)) :=
    (EdgeViewLink.inj_of_fac24 F).comp (by decide : Function.Injective c19_P)
  refine SVC.svc_local_lex F c19_P (x 4 - x 6) c19_sw c19_R (by decide) hsw hR [(2, 4)] ?_
    c19_D (c19_dep F) hPinj (allPairs 5) (fun i j hij _ => mem_allPairs hij) c19_checkW
  intro ij hij
  simp only [List.mem_singleton] at hij
  subst hij
  exact forced_edge ((EdgeViewLink.inj_of_fac24 F).ne (by decide))

/-! ### c20: F235xF236 sig +++--+00- -/

def c20_T : List (Fin 5 × Fin 5) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4)]

theorem c20_checkW :
    SVC.checkW s0x_S24 c20_P c20_sw [(1, 2)] c20_D c20_R c20_T = true := by
  decide +kernel

theorem cell_235_236_pppmmpzzm_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (h1 : 0 < ⟪F.N 1, (x 2 - x 3)⟫)
    (h4 : ⟪F.N 4, (x 2 - x 3)⟫ < 0)
    (h56 : ⟪x 5, (x 2 - x 3)⟫ ≠ ⟪x 6, (x 2 - x 3)⟫) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ c20_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → t ∈ ({1, 2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ c20_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → SignType.sign ⟪F.N t, (x 2 - x 3)⟫ = c20_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_pos h1
    · exact sign_pos (edge_pos F 2 (by decide) (by decide))
    · exact sign_neg (edge_neg F 3 (by decide) (by decide))
    · exact sign_neg h4
    · exact sign_pos (edge_pos F 5 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 6 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 7 (by decide) (by decide))
    · exact sign_neg (edge_neg F 8 (by decide) (by decide))
  have hR1 := hR_two F c20_sw c20_R 6 7 2 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hR := hR_lex_of_hR F (x 2 - x 3) c20_sw c20_R 1 6 h1.ne'
    (edge_zero F 6 (by decide) (by decide)) (by decide) hR1 rfl
  have hPinj : Function.Injective (fun i => x (c20_P i)) :=
    (EdgeViewLink.inj_of_fac24 F).comp (by decide : Function.Injective c20_P)
  refine SVC.svc_local_lex F c20_P (x 2 - x 3) c20_sw c20_R (by decide) hsw hR [(1, 2)] ?_
    c20_D (c20_dep F) hPinj c20_T (fun i j hij heq => ?_) c20_checkW
  · intro ij hij
    simp only [List.mem_singleton] at hij
    subst hij
    exact forced_edge ((EdgeViewLink.inj_of_fac24 F).ne (by decide))
  · by_contra hnot
    have hbad := (by decide : ∀ i j : Fin 5, i ≠ j → ¬ ((i, j) ∈ c20_T ∨ (j, i) ∈ c20_T) →
      (i, j) = (3, 4) ∨ (i, j) = (4, 3)) i j hij hnot
    rcases hbad with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h56 heq
    · exact h56 heq.symm

/-! ### c22: F236xF346 sig --++--+00 -/

def c22_T : List (Fin 5 × Fin 5) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 4), (2, 3), (2, 4), (3, 4)]

theorem c22_checkW :
    SVC.checkW s0x_S24 c22_P c22_sw [(2, 4)] c22_D c22_R c22_T = true := by
  decide +kernel

theorem cell_236_346_mmppmmpzz_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (h0 : ⟪F.N 0, (x 3 - x 6)⟫ < 0)
    (h2 : 0 < ⟪F.N 2, (x 3 - x 6)⟫)
    (h24 : ⟪x 2, (x 3 - x 6)⟫ ≠ ⟪x 4, (x 3 - x 6)⟫) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ c22_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → t ∈ ({0, 2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ c22_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → SignType.sign ⟪F.N t, (x 3 - x 6)⟫ = c22_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_neg h0
    · exact sign_pos h2
    · exact sign_pos (edge_pos F 3 (by decide) (by decide))
    · exact sign_neg (edge_neg F 4 (by decide) (by decide))
    · exact sign_neg (edge_neg F 5 (by decide) (by decide))
    · exact sign_pos (edge_pos F 6 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 7 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 8 (by decide) (by decide))
  have hR1 := hR_two F c22_sw c22_R 7 8 3 4 2 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hR := hR_lex_of_hR F (x 3 - x 6) c22_sw c22_R 2 7 h2.ne'
    (edge_zero F 7 (by decide) (by decide)) (by decide) hR1 rfl
  have hPinj : Function.Injective (fun i => x (c22_P i)) :=
    (EdgeViewLink.inj_of_fac24 F).comp (by decide : Function.Injective c22_P)
  refine SVC.svc_local_lex F c22_P (x 3 - x 6) c22_sw c22_R (by decide) hsw hR [(2, 4)] ?_
    c22_D (c22_dep F) hPinj c22_T (fun i j hij heq => ?_) c22_checkW
  · intro ij hij
    simp only [List.mem_singleton] at hij
    subst hij
    exact forced_edge ((EdgeViewLink.inj_of_fac24 F).ne (by decide))
  · by_contra hnot
    have hbad := (by decide : ∀ i j : Fin 5, i ≠ j → ¬ ((i, j) ∈ c22_T ∨ (j, i) ∈ c22_T) →
      (i, j) = (1, 3) ∨ (i, j) = (3, 1)) i j hij hnot
    rcases hbad with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h24 heq
    · exact h24 heq.symm

end Minimality.SVCC.CellsLex
