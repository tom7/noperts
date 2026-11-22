module

public import Minimality.M4fType24
public import Minimality.Type29Exact
public import Minimality.GenQuad
public import Minimality.GenQuadCross

@[expose] public section

/-!
# Type 24: exact-region tie leaves (QUAD24 section 4)

`lexAny_T26` (line F025xF126+--, rim 2 5 3 4 6, five fronts + five clauses; all A1 shapes), `lexAny_T25_0536`,
`lexAny_T25_01635`, `lexAny_T25_05346` (line F025xF235+--, b = x5 - x2, the three A1 rims; the last uses
`GenQuad.lexClause_of_crossOf` for the coplanar 0345). Together they cover the A1 tie (z3, 77/77 shapes).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.Q24

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell
  Minimality.LexCell Minimality.Split Minimality.T24.A15 Minimality.NF29

/-! ### Clause helpers -/

/-- Not-`M` clause from depths: `z`-form of `GenQuad.lexClause_of_notM`
(back diagonal `p q` is not weakly below the front diagonal `r s`). -/
theorem lexClause_of_z {x : Fin 7 → ℝ³} {b d1 d2 : ℝ³} {p q r s : Fin 7}
    (h : ¬ (max (z x b p) (z x b q) ≤ min (z x b r) (z x b s))) :
    GenQuad.LexClause (x p) (x q) (x r) (x s) b d1 d2 := by
  apply GenQuad.lexClause_of_notM
  rintro ⟨h1, h2, h3, h4⟩
  apply h
  simp only [z, inner_sub_left]
  exact max_le_iff.2 ⟨le_min (by linarith) (by linarith), le_min (by linarith) (by linarith)⟩

/-- Front clause from `det3` signs. -/
theorem lexClause_of_det {b d1 d2 p q r s : ℝ³} (hb : b ≠ 0) (h : FrontDet p q r s b) :
    GenQuad.LexClause p q r s b d1 d2 :=
  GenQuad.lexClause_of_frontOf hb h.frontOf

/-! ### T26: line F025 x F126, tilt +-- -/

/-- `n025 × n126` as a combination of edge vectors (scaled by `det3`s):
`D21 (x6 - x1) - D61 (x2 - x1)` with `Dij = Split.det3 (x2 - x0) (x5 - x0) (x_i - x_1)`. -/
noncomputable def bT26 (x : Fin 7 → ℝ³) : ℝ³ :=
  Split.det3 (x 2 - x 0) (x 5 - x 0) (x 2 - x 1) • (x 6 - x 1) -
    Split.det3 (x 2 - x 0) (x 5 - x 0) (x 6 - x 1) • (x 2 - x 1)

theorem bT26_N5 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : ⟪F.N 5, bT26 x⟫ = 0 := by
  have h1 : ⟪F.N 5, x 6 - x 1⟫ = 0 := by
    rw [F.inner_sub, F.zero 5 6 (by decide), F.zero 5 1 (by decide)]; ring
  have h2 : ⟪F.N 5, x 2 - x 1⟫ = 0 := by
    rw [F.inner_sub, F.zero 5 2 (by decide), F.zero 5 1 (by decide)]; ring
  simp only [bT26, inner_sub_right, inner_smul_right, h1, h2]; ring

theorem bT26_N2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : ⟪F.N 2, bT26 x⟫ = 0 := by
  have h1 : ⟪F.N 2, x 2 - x 0⟫ = 0 := by
    rw [F.inner_sub, F.zero 2 2 (by decide), F.zero 2 0 (by decide)]; ring
  have h2 : ⟪F.N 2, x 5 - x 0⟫ = 0 := by
    rw [F.inner_sub, F.zero 2 5 (by decide), F.zero 2 0 (by decide)]; ring
  have hc := GenQuad.cramer3 (x 2 - x 0) (x 5 - x 0) (x 2 - x 1) (x 6 - x 1)
  have hb : bT26 x = Split.det3 (x 6 - x 1) (x 5 - x 0) (x 2 - x 1) • (x 2 - x 0) +
      Split.det3 (x 2 - x 0) (x 6 - x 1) (x 2 - x 1) • (x 5 - x 0) := by
    unfold bT26; rw [hc]; abel
  rw [hb]; simp only [inner_add_right, inner_smul_right, h1, h2]; ring

private def c26 : ZMod 5 → Fin 7 := ![2, 5, 3, 4, 6]
private theorem c26_inj : Function.Injective c26 := by decide
private theorem c26_cyc : S0xCycUD s0x_S24 c26 {6, 7, 8} {2, 3, 4, 5} := by decide

/-- **T26** (A1, line `F025 x F126`, tilt `+--`, rim `(2 5 3 4 6)`, front table `23 23 24 36 36`).
Facet signs at `b = bT26 x`; five fronts (`FrontDet`); five not-`M` clauses (`z i = ⟪x i - x 1, b⟫`). -/
theorem lexAny_T26 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (h6 : 0 < ⟪F.N 6, bT26 x⟫) (h7 : 0 < ⟪F.N 7, bT26 x⟫) (h8 : 0 < ⟪F.N 8, bT26 x⟫)
    (h3 : ⟪F.N 3, bT26 x⟫ < 0) (h4 : ⟪F.N 4, bT26 x⟫ < 0)
    (f2354 : FrontDet (x 2) (x 3) (x 5) (x 4) (bT26 x))
    (f2356 : FrontDet (x 2) (x 3) (x 5) (x 6) (bT26 x))
    (f2456 : FrontDet (x 2) (x 4) (x 5) (x 6) (bT26 x))
    (f3624 : FrontDet (x 3) (x 6) (x 2) (x 4) (bT26 x))
    (f3654 : FrontDet (x 3) (x 6) (x 5) (x 4) (bT26 x))
    (m2354 : ¬ (max (z x (bT26 x) 5) (z x (bT26 x) 4) ≤ min (z x (bT26 x) 2) (z x (bT26 x) 3)))
    (m2356 : ¬ (max (z x (bT26 x) 5) (z x (bT26 x) 6) ≤ min (z x (bT26 x) 2) (z x (bT26 x) 3)))
    (m2456 : ¬ (max (z x (bT26 x) 5) (z x (bT26 x) 6) ≤ min (z x (bT26 x) 2) (z x (bT26 x) 4)))
    (m3624 : ¬ (max (z x (bT26 x) 2) (z x (bT26 x) 4) ≤ min (z x (bT26 x) 3) (z x (bT26 x) 6)))
    (m3654 : ¬ (max (z x (bT26 x) 5) (z x (bT26 x) 4) ≤ min (z x (bT26 x) 3) (z x (bT26 x) 6))) :
    LexAny F := by
  have hb : bT26 x ≠ 0 := fun h => by rw [h, inner_zero_right] at h6; exact lt_irrefl _ h6
  let d1 : ℝ³ := x 3 - x 2
  refine GenQuad.lexAny_of_clauses F (k := 5) (by norm_num) c26_inj c26_cyc (bT26 x) d1 0 ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact Or.inl h6
    · exact Or.inl h7
    · exact Or.inl h8
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · refine Or.inr ⟨by rw [bT26_N2 F, neg_zero], Or.inl ?_⟩
      simp only [d1, F.inner_sub, F.zero 2 2 (by decide)]
      have := F.neg 2 3 (by decide); linarith
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · refine Or.inr ⟨by rw [bT26_N5 F, neg_zero], Or.inl ?_⟩
      simp only [d1, F.inner_sub, F.zero 5 2 (by decide)]
      have := F.neg 5 3 (by decide); linarith
  · exact GenQuad.clauses_five (p := fun i => x (c26 i)) (b := bT26 x) (d1 := d1) (d2 := 0)
      (lexClause_of_z m2354) (lexClause_of_det hb f2354)
      (lexClause_of_z m2356) (lexClause_of_det hb f2356)
      (lexClause_of_z m2456) (lexClause_of_det hb f2456)
      (lexClause_of_det hb f3624) (lexClause_of_z m3624)
      (lexClause_of_det hb f3654) (lexClause_of_z m3654)

/-! ### T25: line F025 x F235, tilt +-- (b along edge 25) -/

/-- The view of T25: `n025 × n235` is a positive multiple of `x 5 - x 2`. -/
noncomputable def bT25 (x : Fin 7 → ℝ³) : ℝ³ := x 5 - x 2

theorem bT25_N2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : ⟪F.N 2, bT25 x⟫ = 0 := by
  rw [bT25, F.inner_sub, F.zero 2 5 (by decide), F.zero 2 2 (by decide)]; ring

theorem bT25_N6 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : ⟪F.N 6, bT25 x⟫ = 0 := by
  rw [bT25, F.inner_sub, F.zero 6 5 (by decide), F.zero 6 2 (by decide)]; ring

/-- The two tie facets `025`, `235` face down at the tilt `d1 = x 1 - x 2`. -/
theorem bT25_tilt {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    LexPos3 (-⟪F.N 2, bT25 x⟫) (-⟪F.N 2, x 1 - x 2⟫) (-⟪F.N 2, (0 : ℝ³)⟫) ∧
    LexPos3 (-⟪F.N 6, bT25 x⟫) (-⟪F.N 6, x 1 - x 2⟫) (-⟪F.N 6, (0 : ℝ³)⟫) := by
  refine ⟨Or.inr ⟨by rw [bT25_N2 F, neg_zero], Or.inl ?_⟩, Or.inr ⟨by rw [bT25_N6 F, neg_zero], Or.inl ?_⟩⟩
  · rw [F.inner_sub, F.zero 2 2 (by decide)]; have := F.neg 2 1 (by decide); linarith
  · rw [F.inner_sub, F.zero 6 2 (by decide)]; have := F.neg 6 1 (by decide); linarith

private def c25a : ZMod 4 → Fin 7 := ![0, 5, 3, 6]
private theorem c25a_inj : Function.Injective c25a := by decide
private theorem c25a_cyc : S0xCycUD s0x_S24 c25a {3, 4, 8} {1, 2, 6, 7} := by decide

/-- **T25, 4-rim `(0 5 3 6)`** (front `03`, one clause). -/
theorem lexAny_T25_0536 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (h3 : 0 < ⟪F.N 3, bT25 x⟫) (h4 : 0 < ⟪F.N 4, bT25 x⟫) (h8 : 0 < ⟪F.N 8, bT25 x⟫)
    (h1 : ⟪F.N 1, bT25 x⟫ < 0) (h7 : ⟪F.N 7, bT25 x⟫ < 0)
    (f0356 : FrontDet (x 0) (x 3) (x 5) (x 6) (bT25 x))
    (m0356 : ¬ (max (z x (bT25 x) 5) (z x (bT25 x) 6) ≤ min (z x (bT25 x) 0) (z x (bT25 x) 3))) :
    LexAny F := by
  have hb : bT25 x ≠ 0 := fun h => by rw [h, inner_zero_right] at h3; exact lt_irrefl _ h3
  refine GenQuad.lexAny_of_clauses F (k := 4) (by norm_num) c25a_inj c25a_cyc (bT25 x) (x 1 - x 2) 0 ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact Or.inl h3
    · exact Or.inl h4
    · exact Or.inl h8
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact Or.inl (by linarith)
    · exact (bT25_tilt F).1
    · exact (bT25_tilt F).2
    · exact Or.inl (by linarith)
  · exact GenQuad.clauses_four (p := fun i => x (c25a i)) (b := bT25 x) (d1 := x 1 - x 2) (d2 := 0)
      (lexClause_of_z m0356) (lexClause_of_det hb f0356)

private def c25b : ZMod 5 → Fin 7 := ![0, 1, 6, 3, 5]
private theorem c25b_inj : Function.Injective c25b := by decide
private theorem c25b_cyc : S0xCycUD s0x_S24 c25b {1, 3, 8} {0, 2, 5, 6, 7} := by decide

/-- **T25, 5-rim `(0 1 6 3 5)`** (front table `06 06 03 03 65`). -/
theorem lexAny_T25_01635 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (h1 : 0 < ⟪F.N 1, bT25 x⟫) (h3 : 0 < ⟪F.N 3, bT25 x⟫) (h8 : 0 < ⟪F.N 8, bT25 x⟫)
    (h0 : ⟪F.N 0, bT25 x⟫ < 0) (h5 : ⟪F.N 5, bT25 x⟫ < 0) (h7 : ⟪F.N 7, bT25 x⟫ < 0)
    (f0613 : FrontDet (x 0) (x 6) (x 1) (x 3) (bT25 x))
    (f0615 : FrontDet (x 0) (x 6) (x 1) (x 5) (bT25 x))
    (f0315 : FrontDet (x 0) (x 3) (x 1) (x 5) (bT25 x))
    (f0365 : FrontDet (x 0) (x 3) (x 6) (x 5) (bT25 x))
    (f6513 : FrontDet (x 6) (x 5) (x 1) (x 3) (bT25 x))
    (m0613 : ¬ (max (z x (bT25 x) 1) (z x (bT25 x) 3) ≤ min (z x (bT25 x) 0) (z x (bT25 x) 6)))
    (m0615 : ¬ (max (z x (bT25 x) 1) (z x (bT25 x) 5) ≤ min (z x (bT25 x) 0) (z x (bT25 x) 6)))
    (m0315 : ¬ (max (z x (bT25 x) 1) (z x (bT25 x) 5) ≤ min (z x (bT25 x) 0) (z x (bT25 x) 3)))
    (m0365 : ¬ (max (z x (bT25 x) 6) (z x (bT25 x) 5) ≤ min (z x (bT25 x) 0) (z x (bT25 x) 3)))
    (m6513 : ¬ (max (z x (bT25 x) 1) (z x (bT25 x) 3) ≤ min (z x (bT25 x) 6) (z x (bT25 x) 5))) :
    LexAny F := by
  have hb : bT25 x ≠ 0 := fun h => by rw [h, inner_zero_right] at h1; exact lt_irrefl _ h1
  refine GenQuad.lexAny_of_clauses F (k := 5) (by norm_num) c25b_inj c25b_cyc (bT25 x) (x 1 - x 2) 0 ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact Or.inl h1
    · exact Or.inl h3
    · exact Or.inl h8
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (by linarith)
    · exact (bT25_tilt F).1
    · exact Or.inl (by linarith)
    · exact (bT25_tilt F).2
    · exact Or.inl (by linarith)
  · exact GenQuad.clauses_five (p := fun i => x (c25b i)) (b := bT25 x) (d1 := x 1 - x 2) (d2 := 0)
      (lexClause_of_z m0613) (lexClause_of_det hb f0613)
      (lexClause_of_z m0615) (lexClause_of_det hb f0615)
      (lexClause_of_z m0315) (lexClause_of_det hb f0315)
      (lexClause_of_z m0365) (lexClause_of_det hb f0365)
      (lexClause_of_det hb f6513) (lexClause_of_z m6513)

private def c25c : ZMod 5 → Fin 7 := ![0, 5, 3, 4, 6]
private theorem c25c_inj : Function.Injective c25c := by decide
private theorem c25c_cyc : S0xCycUD s0x_S24 c25c {3, 4} {1, 2, 6, 8} := by decide

/-- **T25, 5-rim `(0 5 3 4 6)`** (front table `D0 03 04 04 54`): the subset `{0,5,3,4}` contains the coplanar
facet `0345` whose diagonals `03`, `54` cross (`GenQuad.lexClause_of_crossOf`; needs the depth map
`(b, d1, d2) = (x5 - x2, x1 - x2, x3 - x2)` to be a basis, the shape fact `hdet`). -/
theorem lexAny_T25_05346 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hdet : Split.det3 (bT25 x) (x 1 - x 2) (x 3 - x 2) ≠ 0)
    (h3 : 0 < ⟪F.N 3, bT25 x⟫) (h4 : 0 < ⟪F.N 4, bT25 x⟫)
    (h1 : ⟪F.N 1, bT25 x⟫ < 0) (h8 : ⟪F.N 8, bT25 x⟫ < 0)
    (hX : GenQuad.CrossOf (x 0) (x 3) (x 5) (x 4))
    (f0356 : FrontDet (x 0) (x 3) (x 5) (x 6) (bT25 x))
    (f0456 : FrontDet (x 0) (x 4) (x 5) (x 6) (bT25 x))
    (f0436 : FrontDet (x 0) (x 4) (x 3) (x 6) (bT25 x))
    (f5436 : FrontDet (x 5) (x 4) (x 3) (x 6) (bT25 x))
    (m0356 : ¬ (max (z x (bT25 x) 5) (z x (bT25 x) 6) ≤ min (z x (bT25 x) 0) (z x (bT25 x) 3)))
    (m0456 : ¬ (max (z x (bT25 x) 5) (z x (bT25 x) 6) ≤ min (z x (bT25 x) 0) (z x (bT25 x) 4)))
    (m0436 : ¬ (max (z x (bT25 x) 3) (z x (bT25 x) 6) ≤ min (z x (bT25 x) 0) (z x (bT25 x) 4)))
    (m5436 : ¬ (max (z x (bT25 x) 3) (z x (bT25 x) 6) ≤ min (z x (bT25 x) 5) (z x (bT25 x) 4))) :
    LexAny F := by
  have hb : bT25 x ≠ 0 := fun h => by rw [h, inner_zero_right] at h3; exact lt_irrefl _ h3
  have hinj := inj_of_fac F
  have h05 : x 0 ≠ x 5 := fun h => absurd (hinj h) (by decide)
  obtain ⟨cB, cA⟩ := GenQuad.lexClause_of_crossOf hX hdet h05
  refine GenQuad.lexAny_of_clauses F (k := 5) (by norm_num) c25c_inj c25c_cyc (bT25 x) (x 1 - x 2)
    (x 3 - x 2) ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact Or.inl h3
    · exact Or.inl h4
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact Or.inl (by linarith)
    · refine Or.inr ⟨by rw [bT25_N2 F, neg_zero], Or.inl ?_⟩
      rw [F.inner_sub, F.zero 2 2 (by decide)]; have := F.neg 2 1 (by decide); linarith
    · refine Or.inr ⟨by rw [bT25_N6 F, neg_zero], Or.inl ?_⟩
      rw [F.inner_sub, F.zero 6 2 (by decide)]; have := F.neg 6 1 (by decide); linarith
    · exact Or.inl (by linarith)
  · exact GenQuad.clauses_five (p := fun i => x (c25c i)) (b := bT25 x) (d1 := x 1 - x 2) (d2 := x 3 - x 2)
      cA cB
      (lexClause_of_z m0356) (lexClause_of_det hb f0356)
      (lexClause_of_z m0456) (lexClause_of_det hb f0456)
      (lexClause_of_z m0436) (lexClause_of_det hb f0436)
      (lexClause_of_z m5436) (lexClause_of_det hb f5436)

end Minimality.T24.Q24
