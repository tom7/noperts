module

public import Minimality.Type24Quad

@[expose] public section

/-!
# Type 24: A2 leaves at the line `w02 = F012 x F025` (QUAD24 section 2, Task CJ)

Exact `U` leaves at `bW02 x = x 0 - x 2` on A2 (`211/211` shapes):
1. `lexAny_w02_ppp`: tilt `+++`, 5-rim `![1, 2, 5, 3, 6]`, front table `15 15 13 56 56`.
2. `lexAny_w02_pmm`: tilt `+--`, 5-rim `![0, 1, 6, 3, 5]`, front table `06 06 03 03 65`.
3. `lexAny_w02_pmp`: tilt `+-+`, 6-rim `![0, 1, 6, 3, 5, 2]`, front table `06 06 06 03 03 05 03 03 05 05 65 13 15 15 65`.
4. `lexAny_w02_ppm`: tilt `++-`, 6-rim `![0, 2, 1, 6, 3, 5]`, front table `01 01 01 06 06 03 06 06 03 03 13 15 15 65 65`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.Q24

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell
  Minimality.LexCell Minimality.Split Minimality.T24.A15
open Minimality.GenQuad (FrontDet)

/-- Crossing view of `F012` and `F025`: `n012 × n025` is a positive multiple of `x 0 - x 2`. -/
noncomputable def bW02 (x : Fin 7 → ℝ³) : ℝ³ := x 0 - x 2

theorem bW02_N0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : ⟪F.N 0, bW02 x⟫ = 0 := by
  rw [bW02, F.inner_sub, F.zero 0 0 (by decide), F.zero 0 2 (by decide), sub_zero]

theorem bW02_N2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : ⟪F.N 2, bW02 x⟫ = 0 := by
  rw [bW02, F.inner_sub, F.zero 2 0 (by decide), F.zero 2 2 (by decide), sub_zero]

/-! ### 1. `w02+++` on 5-rim `![1, 2, 5, 3, 6]` -/

private def cW02_ppp : ZMod 5 → Fin 7 := ![1, 2, 5, 3, 6]
private theorem cW02_ppp_inj : Function.Injective cW02_ppp := by decide
private theorem cW02_ppp_cyc : S0xCycUD s0x_S24 cW02_ppp {0, 1, 2, 3, 4, 8} {5, 6, 7} := by decide

theorem lexAny_w02_ppp {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (h1 : 0 < ⟪F.N 1, bW02 x⟫) (h3 : 0 < ⟪F.N 3, bW02 x⟫)
    (h4 : 0 < ⟪F.N 4, bW02 x⟫) (h8 : 0 < ⟪F.N 8, bW02 x⟫)
    (h5 : ⟪F.N 5, bW02 x⟫ < 0) (h6 : ⟪F.N 6, bW02 x⟫ < 0) (h7 : ⟪F.N 7, bW02 x⟫ < 0)
    (f1523 : FrontDet (x 1) (x 5) (x 2) (x 3) (bW02 x))
    (f1526 : FrontDet (x 1) (x 5) (x 2) (x 6) (bW02 x))
    (f1326 : FrontDet (x 1) (x 3) (x 2) (x 6) (bW02 x))
    (f5613 : FrontDet (x 5) (x 6) (x 1) (x 3) (bW02 x))
    (f5623 : FrontDet (x 5) (x 6) (x 2) (x 3) (bW02 x))
    (m1523 : ¬ (max (z x (bW02 x) 2) (z x (bW02 x) 3) ≤ min (z x (bW02 x) 1) (z x (bW02 x) 5)))
    (m1526 : ¬ (max (z x (bW02 x) 2) (z x (bW02 x) 6) ≤ min (z x (bW02 x) 1) (z x (bW02 x) 5)))
    (m1326 : ¬ (max (z x (bW02 x) 2) (z x (bW02 x) 6) ≤ min (z x (bW02 x) 1) (z x (bW02 x) 3)))
    (m5613 : ¬ (max (z x (bW02 x) 1) (z x (bW02 x) 3) ≤ min (z x (bW02 x) 5) (z x (bW02 x) 6)))
    (m5623 : ¬ (max (z x (bW02 x) 2) (z x (bW02 x) 3) ≤ min (z x (bW02 x) 5) (z x (bW02 x) 6))) :
    LexAny F := by
  have hb : bW02 x ≠ 0 := fun h => by rw [h, inner_zero_right] at h1; exact lt_irrefl _ h1
  let d1 : ℝ³ := x 0 - x 3
  refine GenQuad.lexAny_of_clauses F (k := 5) (by norm_num) cW02_ppp_inj cW02_ppp_cyc (bW02 x) d1 0 ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · refine Or.inr ⟨bW02_N0 F, Or.inl ?_⟩
      simp only [d1, F.inner_sub, F.zero 0 0 (by decide)]
      have := F.neg 0 3 (by decide); linarith
    · exact Or.inl h1
    · refine Or.inr ⟨bW02_N2 F, Or.inl ?_⟩
      simp only [d1, F.inner_sub, F.zero 2 0 (by decide)]
      have := F.neg 2 3 (by decide); linarith
    · exact Or.inl h3
    · exact Or.inl h4
    · exact Or.inl h8
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
  · exact GenQuad.clauses_five (p := fun i => x (cW02_ppp i)) (b := bW02 x) (d1 := d1) (d2 := 0)
      (lexClause_of_z m1523) (lexClause_of_det hb f1523)
      (lexClause_of_z m1526) (lexClause_of_det hb f1526)
      (lexClause_of_z m1326) (lexClause_of_det hb f1326)
      (lexClause_of_det hb f5613) (lexClause_of_z m5613)
      (lexClause_of_det hb f5623) (lexClause_of_z m5623)

/-! ### 2. `w02+--` on 5-rim `![0, 1, 6, 3, 5]` -/

private def cW02_pmm : ZMod 5 → Fin 7 := ![0, 1, 6, 3, 5]
private theorem cW02_pmm_inj : Function.Injective cW02_pmm := by decide
private theorem cW02_pmm_cyc : S0xCycUD s0x_S24 cW02_pmm {1, 3, 4, 8} {0, 2, 5, 6, 7} := by decide

theorem lexAny_w02_pmm {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (h1 : 0 < ⟪F.N 1, bW02 x⟫) (h3 : 0 < ⟪F.N 3, bW02 x⟫)
    (h4 : 0 < ⟪F.N 4, bW02 x⟫) (h8 : 0 < ⟪F.N 8, bW02 x⟫)
    (h5 : ⟪F.N 5, bW02 x⟫ < 0) (h6 : ⟪F.N 6, bW02 x⟫ < 0) (h7 : ⟪F.N 7, bW02 x⟫ < 0)
    (f0613 : FrontDet (x 0) (x 6) (x 1) (x 3) (bW02 x))
    (f0615 : FrontDet (x 0) (x 6) (x 1) (x 5) (bW02 x))
    (f0315 : FrontDet (x 0) (x 3) (x 1) (x 5) (bW02 x))
    (f0365 : FrontDet (x 0) (x 3) (x 6) (x 5) (bW02 x))
    (f6513 : FrontDet (x 6) (x 5) (x 1) (x 3) (bW02 x))
    (m0613 : ¬ (max (z x (bW02 x) 1) (z x (bW02 x) 3) ≤ min (z x (bW02 x) 0) (z x (bW02 x) 6)))
    (m0615 : ¬ (max (z x (bW02 x) 1) (z x (bW02 x) 5) ≤ min (z x (bW02 x) 0) (z x (bW02 x) 6)))
    (m0315 : ¬ (max (z x (bW02 x) 1) (z x (bW02 x) 5) ≤ min (z x (bW02 x) 0) (z x (bW02 x) 3)))
    (m0365 : ¬ (max (z x (bW02 x) 6) (z x (bW02 x) 5) ≤ min (z x (bW02 x) 0) (z x (bW02 x) 3)))
    (m6513 : ¬ (max (z x (bW02 x) 1) (z x (bW02 x) 3) ≤ min (z x (bW02 x) 6) (z x (bW02 x) 5))) :
    LexAny F := by
  have hb : bW02 x ≠ 0 := fun h => by rw [h, inner_zero_right] at h1; exact lt_irrefl _ h1
  let d1 : ℝ³ := x 3 - x 0
  refine GenQuad.lexAny_of_clauses F (k := 5) (by norm_num) cW02_pmm_inj cW02_pmm_cyc (bW02 x) d1 0 ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact Or.inl h1
    · exact Or.inl h3
    · exact Or.inl h4
    · exact Or.inl h8
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · refine Or.inr ⟨by rw [bW02_N0 F, neg_zero], Or.inl ?_⟩
      simp only [d1, F.inner_sub, F.zero 0 0 (by decide)]
      have := F.neg 0 3 (by decide); linarith
    · refine Or.inr ⟨by rw [bW02_N2 F, neg_zero], Or.inl ?_⟩
      simp only [d1, F.inner_sub, F.zero 2 0 (by decide)]
      have := F.neg 2 3 (by decide); linarith
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
  · exact GenQuad.clauses_five (p := fun i => x (cW02_pmm i)) (b := bW02 x) (d1 := d1) (d2 := 0)
      (lexClause_of_z m0613) (lexClause_of_det hb f0613)
      (lexClause_of_z m0615) (lexClause_of_det hb f0615)
      (lexClause_of_z m0315) (lexClause_of_det hb f0315)
      (lexClause_of_z m0365) (lexClause_of_det hb f0365)
      (lexClause_of_det hb f6513) (lexClause_of_z m6513)

/-! ### 3a. `w02+-+` on 6-rim `![0, 1, 6, 3, 5, 2]` -/

private def cW02_pmp : ZMod 6 → Fin 7 := ![0, 1, 6, 3, 5, 2]
private theorem cW02_pmp_inj : Function.Injective cW02_pmp := by decide
private theorem cW02_pmp_cyc : S0xCycUD s0x_S24 cW02_pmp {1, 2, 3, 4, 8} {0, 5, 6, 7} := by decide

theorem lexAny_w02_pmp {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (h1 : 0 < ⟪F.N 1, bW02 x⟫) (h3 : 0 < ⟪F.N 3, bW02 x⟫)
    (h4 : 0 < ⟪F.N 4, bW02 x⟫) (h8 : 0 < ⟪F.N 8, bW02 x⟫)
    (h5 : ⟪F.N 5, bW02 x⟫ < 0) (h6 : ⟪F.N 6, bW02 x⟫ < 0) (h7 : ⟪F.N 7, bW02 x⟫ < 0)
    (f0613 : FrontDet (x 0) (x 6) (x 1) (x 3) (bW02 x))
    (f0615 : FrontDet (x 0) (x 6) (x 1) (x 5) (bW02 x))
    (f0612 : FrontDet (x 0) (x 6) (x 1) (x 2) (bW02 x))
    (f0315 : FrontDet (x 0) (x 3) (x 1) (x 5) (bW02 x))
    (f0312 : FrontDet (x 0) (x 3) (x 1) (x 2) (bW02 x))
    (f0512 : FrontDet (x 0) (x 5) (x 1) (x 2) (bW02 x))
    (f0365 : FrontDet (x 0) (x 3) (x 6) (x 5) (bW02 x))
    (f0362 : FrontDet (x 0) (x 3) (x 6) (x 2) (bW02 x))
    (f0562 : FrontDet (x 0) (x 5) (x 6) (x 2) (bW02 x))
    (f0532 : FrontDet (x 0) (x 5) (x 3) (x 2) (bW02 x))
    (f6513 : FrontDet (x 6) (x 5) (x 1) (x 3) (bW02 x))
    (f1362 : FrontDet (x 1) (x 3) (x 6) (x 2) (bW02 x))
    (f1562 : FrontDet (x 1) (x 5) (x 6) (x 2) (bW02 x))
    (f1532 : FrontDet (x 1) (x 5) (x 3) (x 2) (bW02 x))
    (f6532 : FrontDet (x 6) (x 5) (x 3) (x 2) (bW02 x))
    (m0613 : ¬ (max (z x (bW02 x) 1) (z x (bW02 x) 3) ≤ min (z x (bW02 x) 0) (z x (bW02 x) 6)))
    (m0615 : ¬ (max (z x (bW02 x) 1) (z x (bW02 x) 5) ≤ min (z x (bW02 x) 0) (z x (bW02 x) 6)))
    (m0612 : ¬ (max (z x (bW02 x) 1) (z x (bW02 x) 2) ≤ min (z x (bW02 x) 0) (z x (bW02 x) 6)))
    (m0315 : ¬ (max (z x (bW02 x) 1) (z x (bW02 x) 5) ≤ min (z x (bW02 x) 0) (z x (bW02 x) 3)))
    (m0312 : ¬ (max (z x (bW02 x) 1) (z x (bW02 x) 2) ≤ min (z x (bW02 x) 0) (z x (bW02 x) 3)))
    (m0512 : ¬ (max (z x (bW02 x) 1) (z x (bW02 x) 2) ≤ min (z x (bW02 x) 0) (z x (bW02 x) 5)))
    (m0365 : ¬ (max (z x (bW02 x) 6) (z x (bW02 x) 5) ≤ min (z x (bW02 x) 0) (z x (bW02 x) 3)))
    (m0362 : ¬ (max (z x (bW02 x) 6) (z x (bW02 x) 2) ≤ min (z x (bW02 x) 0) (z x (bW02 x) 3)))
    (m0562 : ¬ (max (z x (bW02 x) 6) (z x (bW02 x) 2) ≤ min (z x (bW02 x) 0) (z x (bW02 x) 5)))
    (m0532 : ¬ (max (z x (bW02 x) 3) (z x (bW02 x) 2) ≤ min (z x (bW02 x) 0) (z x (bW02 x) 5)))
    (m6513 : ¬ (max (z x (bW02 x) 1) (z x (bW02 x) 3) ≤ min (z x (bW02 x) 6) (z x (bW02 x) 5)))
    (m1362 : ¬ (max (z x (bW02 x) 6) (z x (bW02 x) 2) ≤ min (z x (bW02 x) 1) (z x (bW02 x) 3)))
    (m1562 : ¬ (max (z x (bW02 x) 6) (z x (bW02 x) 2) ≤ min (z x (bW02 x) 1) (z x (bW02 x) 5)))
    (m1532 : ¬ (max (z x (bW02 x) 3) (z x (bW02 x) 2) ≤ min (z x (bW02 x) 1) (z x (bW02 x) 5)))
    (m6532 : ¬ (max (z x (bW02 x) 3) (z x (bW02 x) 2) ≤ min (z x (bW02 x) 6) (z x (bW02 x) 5))) :
    LexAny F := by
  have hb : bW02 x ≠ 0 := fun h => by rw [h, inner_zero_right] at h1; exact lt_irrefl _ h1
  let d1 : ℝ³ := x 5 - x 1
  refine GenQuad.lexAny_of_clauses F (k := 6) (by norm_num) cW02_pmp_inj cW02_pmp_cyc (bW02 x) d1 0 ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl h1
    · refine Or.inr ⟨bW02_N2 F, Or.inl ?_⟩
      simp only [d1, F.inner_sub, F.zero 2 5 (by decide)]
      have := F.neg 2 1 (by decide); linarith
    · exact Or.inl h3
    · exact Or.inl h4
    · exact Or.inl h8
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · refine Or.inr ⟨by rw [bW02_N0 F, neg_zero], Or.inl ?_⟩
      simp only [d1, F.inner_sub, F.zero 0 1 (by decide)]
      have := F.neg 0 5 (by decide); linarith
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
  · exact GenQuad.clauses_six (p := fun i => x (cW02_pmp i)) (b := bW02 x) (d1 := d1) (d2 := 0)
      (lexClause_of_z m0613) (lexClause_of_det hb f0613)
      (lexClause_of_z m0615) (lexClause_of_det hb f0615)
      (lexClause_of_z m0612) (lexClause_of_det hb f0612)
      (lexClause_of_z m0315) (lexClause_of_det hb f0315)
      (lexClause_of_z m0312) (lexClause_of_det hb f0312)
      (lexClause_of_z m0512) (lexClause_of_det hb f0512)
      (lexClause_of_z m0365) (lexClause_of_det hb f0365)
      (lexClause_of_z m0362) (lexClause_of_det hb f0362)
      (lexClause_of_z m0562) (lexClause_of_det hb f0562)
      (lexClause_of_z m0532) (lexClause_of_det hb f0532)
      (lexClause_of_det hb f6513) (lexClause_of_z m6513)
      (lexClause_of_z m1362) (lexClause_of_det hb f1362)
      (lexClause_of_z m1562) (lexClause_of_det hb f1562)
      (lexClause_of_z m1532) (lexClause_of_det hb f1532)
      (lexClause_of_z m6532) (lexClause_of_det hb f6532)

/-! ### 3b. `w02++-` on 6-rim `![0, 2, 1, 6, 3, 5]` -/

private def cW02_ppm : ZMod 6 → Fin 7 := ![0, 2, 1, 6, 3, 5]
private theorem cW02_ppm_inj : Function.Injective cW02_ppm := by decide
private theorem cW02_ppm_cyc : S0xCycUD s0x_S24 cW02_ppm {0, 1, 3, 4, 8} {2, 5, 6, 7} := by decide

theorem lexAny_w02_ppm {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (h1 : 0 < ⟪F.N 1, bW02 x⟫) (h3 : 0 < ⟪F.N 3, bW02 x⟫)
    (h4 : 0 < ⟪F.N 4, bW02 x⟫) (h8 : 0 < ⟪F.N 8, bW02 x⟫)
    (h5 : ⟪F.N 5, bW02 x⟫ < 0) (h6 : ⟪F.N 6, bW02 x⟫ < 0) (h7 : ⟪F.N 7, bW02 x⟫ < 0)
    (f0126 : FrontDet (x 0) (x 1) (x 2) (x 6) (bW02 x))
    (f0123 : FrontDet (x 0) (x 1) (x 2) (x 3) (bW02 x))
    (f0125 : FrontDet (x 0) (x 1) (x 2) (x 5) (bW02 x))
    (f0623 : FrontDet (x 0) (x 6) (x 2) (x 3) (bW02 x))
    (f0625 : FrontDet (x 0) (x 6) (x 2) (x 5) (bW02 x))
    (f0325 : FrontDet (x 0) (x 3) (x 2) (x 5) (bW02 x))
    (f0613 : FrontDet (x 0) (x 6) (x 1) (x 3) (bW02 x))
    (f0615 : FrontDet (x 0) (x 6) (x 1) (x 5) (bW02 x))
    (f0315 : FrontDet (x 0) (x 3) (x 1) (x 5) (bW02 x))
    (f0365 : FrontDet (x 0) (x 3) (x 6) (x 5) (bW02 x))
    (f1326 : FrontDet (x 1) (x 3) (x 2) (x 6) (bW02 x))
    (f1526 : FrontDet (x 1) (x 5) (x 2) (x 6) (bW02 x))
    (f1523 : FrontDet (x 1) (x 5) (x 2) (x 3) (bW02 x))
    (f6523 : FrontDet (x 6) (x 5) (x 2) (x 3) (bW02 x))
    (f6513 : FrontDet (x 6) (x 5) (x 1) (x 3) (bW02 x))
    (m0126 : ¬ (max (z x (bW02 x) 2) (z x (bW02 x) 6) ≤ min (z x (bW02 x) 0) (z x (bW02 x) 1)))
    (m0123 : ¬ (max (z x (bW02 x) 2) (z x (bW02 x) 3) ≤ min (z x (bW02 x) 0) (z x (bW02 x) 1)))
    (m0125 : ¬ (max (z x (bW02 x) 2) (z x (bW02 x) 5) ≤ min (z x (bW02 x) 0) (z x (bW02 x) 1)))
    (m0623 : ¬ (max (z x (bW02 x) 2) (z x (bW02 x) 3) ≤ min (z x (bW02 x) 0) (z x (bW02 x) 6)))
    (m0625 : ¬ (max (z x (bW02 x) 2) (z x (bW02 x) 5) ≤ min (z x (bW02 x) 0) (z x (bW02 x) 6)))
    (m0325 : ¬ (max (z x (bW02 x) 2) (z x (bW02 x) 5) ≤ min (z x (bW02 x) 0) (z x (bW02 x) 3)))
    (m0613 : ¬ (max (z x (bW02 x) 1) (z x (bW02 x) 3) ≤ min (z x (bW02 x) 0) (z x (bW02 x) 6)))
    (m0615 : ¬ (max (z x (bW02 x) 1) (z x (bW02 x) 5) ≤ min (z x (bW02 x) 0) (z x (bW02 x) 6)))
    (m0315 : ¬ (max (z x (bW02 x) 1) (z x (bW02 x) 5) ≤ min (z x (bW02 x) 0) (z x (bW02 x) 3)))
    (m0365 : ¬ (max (z x (bW02 x) 6) (z x (bW02 x) 5) ≤ min (z x (bW02 x) 0) (z x (bW02 x) 3)))
    (m1326 : ¬ (max (z x (bW02 x) 2) (z x (bW02 x) 6) ≤ min (z x (bW02 x) 1) (z x (bW02 x) 3)))
    (m1526 : ¬ (max (z x (bW02 x) 2) (z x (bW02 x) 6) ≤ min (z x (bW02 x) 1) (z x (bW02 x) 5)))
    (m1523 : ¬ (max (z x (bW02 x) 2) (z x (bW02 x) 3) ≤ min (z x (bW02 x) 1) (z x (bW02 x) 5)))
    (m6523 : ¬ (max (z x (bW02 x) 2) (z x (bW02 x) 3) ≤ min (z x (bW02 x) 6) (z x (bW02 x) 5)))
    (m6513 : ¬ (max (z x (bW02 x) 1) (z x (bW02 x) 3) ≤ min (z x (bW02 x) 6) (z x (bW02 x) 5))) :
    LexAny F := by
  have hb : bW02 x ≠ 0 := fun h => by rw [h, inner_zero_right] at h1; exact lt_irrefl _ h1
  let d1 : ℝ³ := x 1 - x 5
  refine GenQuad.lexAny_of_clauses F (k := 6) (by norm_num) cW02_ppm_inj cW02_ppm_cyc (bW02 x) d1 0 ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · refine Or.inr ⟨bW02_N0 F, Or.inl ?_⟩
      simp only [d1, F.inner_sub, F.zero 0 1 (by decide)]
      have := F.neg 0 5 (by decide); linarith
    · exact Or.inl h1
    · exact Or.inl h3
    · exact Or.inl h4
    · exact Or.inl h8
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · refine Or.inr ⟨by rw [bW02_N2 F, neg_zero], Or.inl ?_⟩
      simp only [d1, F.inner_sub, F.zero 2 5 (by decide)]
      have := F.neg 2 1 (by decide); linarith
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
  · exact GenQuad.clauses_six (p := fun i => x (cW02_ppm i)) (b := bW02 x) (d1 := d1) (d2 := 0)
      (lexClause_of_z m0126) (lexClause_of_det hb f0126)
      (lexClause_of_z m0123) (lexClause_of_det hb f0123)
      (lexClause_of_z m0125) (lexClause_of_det hb f0125)
      (lexClause_of_z m0623) (lexClause_of_det hb f0623)
      (lexClause_of_z m0625) (lexClause_of_det hb f0625)
      (lexClause_of_z m0325) (lexClause_of_det hb f0325)
      (lexClause_of_z m0613) (lexClause_of_det hb f0613)
      (lexClause_of_z m0615) (lexClause_of_det hb f0615)
      (lexClause_of_z m0315) (lexClause_of_det hb f0315)
      (lexClause_of_z m0365) (lexClause_of_det hb f0365)
      (lexClause_of_det hb f1326) (lexClause_of_z m1326)
      (lexClause_of_det hb f1526) (lexClause_of_z m1526)
      (lexClause_of_det hb f1523) (lexClause_of_z m1523)
      (lexClause_of_det hb f6523) (lexClause_of_z m6523)
      (lexClause_of_det hb f6513) (lexClause_of_z m6513)

end Minimality.T24.Q24
