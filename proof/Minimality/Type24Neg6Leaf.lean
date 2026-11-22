module

public import Minimality.M4jType24

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.LexCell Minimality.H21 Minimality.H24.SAT
  Minimality.T24.SAT Minimality.T24.RCell Minimality.Split Minimality.T24.M4
  Minimality.T24.A7 Minimality.T24.A8 Minimality.T24.A15 Minimality.T24.Q24

namespace Minimality.T24.A19

private def cN6' : ZMod 6 → Fin 7 := ![1, 0, 5, 3, 4, 6]
private theorem cN6'_inj : Function.Injective cN6' := by decide
private theorem cN6'_cyc : S0xCycUD s0x_S24 cN6' {0, 2, 5, 6, 7, 8} {1, 3, 4} := by decide

/-- The leaf: 6-rim `1 0 5 3 4 6` at `(eb, -ea - ec, ea)`. -/
theorem lexAny_neg6_leaf' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hdet : Split.det3 (x 2 - x 1) (-(x 0 - x 1) - (x 6 - x 1)) (x 0 - x 1) ≠ 0)
    (hN0 : ⟪F.N 0, x 2 - x 1⟫ = 0) (hN0d : 0 < ⟪F.N 0, -(x 0 - x 1) - (x 6 - x 1)⟫)
    (hN5 : ⟪F.N 5, x 2 - x 1⟫ = 0) (hN5d : 0 < ⟪F.N 5, -(x 0 - x 1) - (x 6 - x 1)⟫)
    (hN2 : 0 < ⟪F.N 2, x 2 - x 1⟫) (hN6 : 0 < ⟪F.N 6, x 2 - x 1⟫)
    (hN7 : 0 < ⟪F.N 7, x 2 - x 1⟫) (hN8 : LexPos3 ⟪F.N 8, x 2 - x 1⟫ ⟪F.N 8, -(x 0 - x 1) - (x 6 - x 1)⟫ ⟪F.N 8, x 0 - x 1⟫)
    (hN1 : ⟪F.N 1, x 2 - x 1⟫ < 0) (hN4 : ⟪F.N 4, x 2 - x 1⟫ < 0)
    (hN3 : LexPos3 (-⟪F.N 3, x 2 - x 1⟫) (-⟪F.N 3, -(x 0 - x 1) - (x 6 - x 1)⟫)
      (-⟪F.N 3, x 0 - x 1⟫))
    (hX : GenQuad.CrossOf (x 0) (x 3) (x 5) (x 4))
    (f15_03 : GenQuad.LexClause (x 1) (x 5) (x 0) (x 3) (x 2 - x 1) (-(x 0 - x 1) - (x 6 - x 1)) (x 0 - x 1))
    (f15_04 : GenQuad.LexClause (x 1) (x 5) (x 0) (x 4) (x 2 - x 1) (-(x 0 - x 1) - (x 6 - x 1)) (x 0 - x 1))
    (f15_06 : GenQuad.LexClause (x 1) (x 5) (x 0) (x 6) (x 2 - x 1) (-(x 0 - x 1) - (x 6 - x 1)) (x 0 - x 1))
    (f13_04 : GenQuad.LexClause (x 1) (x 3) (x 0) (x 4) (x 2 - x 1) (-(x 0 - x 1) - (x 6 - x 1)) (x 0 - x 1))
    (f13_06 : GenQuad.LexClause (x 1) (x 3) (x 0) (x 6) (x 2 - x 1) (-(x 0 - x 1) - (x 6 - x 1)) (x 0 - x 1))
    (f14_06 : GenQuad.LexClause (x 1) (x 4) (x 0) (x 6) (x 2 - x 1) (-(x 0 - x 1) - (x 6 - x 1)) (x 0 - x 1))
    (f13_54 : GenQuad.LexClause (x 1) (x 3) (x 5) (x 4) (x 2 - x 1) (-(x 0 - x 1) - (x 6 - x 1)) (x 0 - x 1))
    (f56_13 : GenQuad.LexClause (x 5) (x 6) (x 1) (x 3) (x 2 - x 1) (-(x 0 - x 1) - (x 6 - x 1)) (x 0 - x 1))
    (f56_14 : GenQuad.LexClause (x 5) (x 6) (x 1) (x 4) (x 2 - x 1) (-(x 0 - x 1) - (x 6 - x 1)) (x 0 - x 1))
    (f36_14 : GenQuad.LexClause (x 3) (x 6) (x 1) (x 4) (x 2 - x 1) (-(x 0 - x 1) - (x 6 - x 1)) (x 0 - x 1))
    (f56_03 : GenQuad.LexClause (x 5) (x 6) (x 0) (x 3) (x 2 - x 1) (-(x 0 - x 1) - (x 6 - x 1)) (x 0 - x 1))
    (f56_04 : GenQuad.LexClause (x 5) (x 6) (x 0) (x 4) (x 2 - x 1) (-(x 0 - x 1) - (x 6 - x 1)) (x 0 - x 1))
    (f36_04 : GenQuad.LexClause (x 3) (x 6) (x 0) (x 4) (x 2 - x 1) (-(x 0 - x 1) - (x 6 - x 1)) (x 0 - x 1))
    (f36_54 : GenQuad.LexClause (x 3) (x 6) (x 5) (x 4) (x 2 - x 1) (-(x 0 - x 1) - (x 6 - x 1)) (x 0 - x 1))
    (m0123 : ¬ (max (z x (x 2 - x 1) 0) (z x (x 2 - x 1) 3) ≤ min (z x (x 2 - x 1) 1) (z x (x 2 - x 1) 5)))
    (m0124 : ¬ (max (z x (x 2 - x 1) 0) (z x (x 2 - x 1) 4) ≤ min (z x (x 2 - x 1) 1) (z x (x 2 - x 1) 5)))
    (m0125 : ¬ (max (z x (x 2 - x 1) 0) (z x (x 2 - x 1) 6) ≤ min (z x (x 2 - x 1) 1) (z x (x 2 - x 1) 5)))
    (m0134 : ¬ (max (z x (x 2 - x 1) 0) (z x (x 2 - x 1) 4) ≤ min (z x (x 2 - x 1) 1) (z x (x 2 - x 1) 3)))
    (m0135 : ¬ (max (z x (x 2 - x 1) 0) (z x (x 2 - x 1) 6) ≤ min (z x (x 2 - x 1) 1) (z x (x 2 - x 1) 3)))
    (m0145 : ¬ (max (z x (x 2 - x 1) 0) (z x (x 2 - x 1) 6) ≤ min (z x (x 2 - x 1) 1) (z x (x 2 - x 1) 4)))
    (m0234 : ¬ (max (z x (x 2 - x 1) 5) (z x (x 2 - x 1) 4) ≤ min (z x (x 2 - x 1) 1) (z x (x 2 - x 1) 3)))
    (m0235 : ¬ (max (z x (x 2 - x 1) 1) (z x (x 2 - x 1) 3) ≤ min (z x (x 2 - x 1) 5) (z x (x 2 - x 1) 6)))
    (m0245 : ¬ (max (z x (x 2 - x 1) 1) (z x (x 2 - x 1) 4) ≤ min (z x (x 2 - x 1) 5) (z x (x 2 - x 1) 6)))
    (m0345 : ¬ (max (z x (x 2 - x 1) 1) (z x (x 2 - x 1) 4) ≤ min (z x (x 2 - x 1) 3) (z x (x 2 - x 1) 6)))
    (m1235 : ¬ (max (z x (x 2 - x 1) 0) (z x (x 2 - x 1) 3) ≤ min (z x (x 2 - x 1) 5) (z x (x 2 - x 1) 6)))
    (m1245 : ¬ (max (z x (x 2 - x 1) 0) (z x (x 2 - x 1) 4) ≤ min (z x (x 2 - x 1) 5) (z x (x 2 - x 1) 6)))
    (m1345 : ¬ (max (z x (x 2 - x 1) 0) (z x (x 2 - x 1) 4) ≤ min (z x (x 2 - x 1) 3) (z x (x 2 - x 1) 6)))
    (m2345 : ¬ (max (z x (x 2 - x 1) 5) (z x (x 2 - x 1) 4) ≤ min (z x (x 2 - x 1) 3) (z x (x 2 - x 1) 6))) :
    LexAny F := by
  have hb : x 2 - x 1 ≠ 0 := fun h => by rw [h, inner_zero_right] at hN2; exact lt_irrefl _ hN2
  have hinj := inj_of_fac F
  have h05 : x 0 ≠ x 5 := fun h => absurd (hinj h) (by decide)
  obtain ⟨cB, cA⟩ := GenQuad.lexClause_of_crossOf hX hdet h05
  refine GenQuad.lexAny_of_clauses F (k := 6) (by norm_num) cN6'_inj cN6'_cyc (x 2 - x 1)
    (-(x 0 - x 1) - (x 6 - x 1)) (x 0 - x 1) ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr ⟨hN0, Or.inl hN0d⟩
    · exact Or.inl hN2
    · exact Or.inr ⟨hN5, Or.inl hN5d⟩
    · exact Or.inl hN6
    · exact Or.inl hN7
    · exact hN8
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact Or.inl (by linarith)
    · exact hN3
    · exact Or.inl (by linarith)
  · exact GenQuad.clauses_six (p := fun i => x (cN6' i)) (b := x 2 - x 1)
      (d1 := -(x 0 - x 1) - (x 6 - x 1)) (d2 := x 0 - x 1)
      (lexClause_of_z m0123) f15_03
      (lexClause_of_z m0124) f15_04
      (lexClause_of_z m0125) f15_06
      (lexClause_of_z m0134) f13_04
      (lexClause_of_z m0135) f13_06
      (lexClause_of_z m0145) f14_06
      (lexClause_of_z m0234) f13_54
      f56_13 (lexClause_of_z m0235)
      f56_14 (lexClause_of_z m0245)
      f36_14 (lexClause_of_z m0345)
      cA cB
      f56_03 (lexClause_of_z m1235)
      f56_04 (lexClause_of_z m1245)
      f36_04 (lexClause_of_z m1345)
      f36_54 (lexClause_of_z m2345)

/-- **E12-Neg6** with the 14 front facts as hypotheses (`FrontOf`); `nB = 0` allowed when `nC > 0`. -/
theorem e12_neg6_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (hnb : F.f 3 (x 2) < F.f 3 (x 1) ∨ (F.f 3 (x 2) = F.f 3 (x 1) ∧ F.f 3 (x 1) < F.f 3 (x 6)))
    (h346 : LexPos3 ⟪F.N 8, x 2 - x 1⟫ ⟪F.N 8, -(x 0 - x 1) - (x 6 - x 1)⟫ ⟪F.N 8, x 0 - x 1⟫)
    (hab : 0 < ⟪x 0 - x 1, x 2 - x 1⟫) (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0)
    (f15_03 : GenQuad.LexClause (x 1) (x 5) (x 0) (x 3) (x 2 - x 1) (-(x 0 - x 1) - (x 6 - x 1)) (x 0 - x 1))
    (f15_04 : GenQuad.LexClause (x 1) (x 5) (x 0) (x 4) (x 2 - x 1) (-(x 0 - x 1) - (x 6 - x 1)) (x 0 - x 1))
    (f15_06 : GenQuad.LexClause (x 1) (x 5) (x 0) (x 6) (x 2 - x 1) (-(x 0 - x 1) - (x 6 - x 1)) (x 0 - x 1))
    (f13_04 : GenQuad.LexClause (x 1) (x 3) (x 0) (x 4) (x 2 - x 1) (-(x 0 - x 1) - (x 6 - x 1)) (x 0 - x 1))
    (f13_06 : GenQuad.LexClause (x 1) (x 3) (x 0) (x 6) (x 2 - x 1) (-(x 0 - x 1) - (x 6 - x 1)) (x 0 - x 1))
    (f14_06 : GenQuad.LexClause (x 1) (x 4) (x 0) (x 6) (x 2 - x 1) (-(x 0 - x 1) - (x 6 - x 1)) (x 0 - x 1))
    (f13_54 : GenQuad.LexClause (x 1) (x 3) (x 5) (x 4) (x 2 - x 1) (-(x 0 - x 1) - (x 6 - x 1)) (x 0 - x 1))
    (f56_13 : GenQuad.LexClause (x 5) (x 6) (x 1) (x 3) (x 2 - x 1) (-(x 0 - x 1) - (x 6 - x 1)) (x 0 - x 1))
    (f56_14 : GenQuad.LexClause (x 5) (x 6) (x 1) (x 4) (x 2 - x 1) (-(x 0 - x 1) - (x 6 - x 1)) (x 0 - x 1))
    (f36_14 : GenQuad.LexClause (x 3) (x 6) (x 1) (x 4) (x 2 - x 1) (-(x 0 - x 1) - (x 6 - x 1)) (x 0 - x 1))
    (f56_03 : GenQuad.LexClause (x 5) (x 6) (x 0) (x 3) (x 2 - x 1) (-(x 0 - x 1) - (x 6 - x 1)) (x 0 - x 1))
    (f56_04 : GenQuad.LexClause (x 5) (x 6) (x 0) (x 4) (x 2 - x 1) (-(x 0 - x 1) - (x 6 - x 1)) (x 0 - x 1))
    (f36_04 : GenQuad.LexClause (x 3) (x 6) (x 0) (x 4) (x 2 - x 1) (-(x 0 - x 1) - (x 6 - x 1)) (x 0 - x 1))
    (f36_54 : GenQuad.LexClause (x 3) (x 6) (x 5) (x 4) (x 2 - x 1) (-(x 0 - x 1) - (x 6 - x 1)) (x 0 - x 1)) :
    LexAny F := by
  have T := type24OfFac F
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hdet : Split.det3 (x 2 - x 1) (-(x 0 - x 1) - (x 6 - x 1)) (x 0 - x 1) ≠ 0 := by
    have e : Split.det3 (x 2 - x 1) (-(x 0 - x 1) - (x 6 - x 1)) (x 0 - x 1) = -det24 x := by
      simp only [Split.det3, det24, vol3, PiLp.sub_apply, PiLp.neg_apply]; ring
    rw [e]; exact neg_ne_zero.2 T.det_ne
  have hN0 : ⟪F.N 0, x 2 - x 1⟫ = 0 := by
    rw [← F.hN, F.zero 0 2 (by decide), F.zero 0 1 (by decide), sub_self]
  have hN1 : ⟪F.N 1, x 2 - x 1⟫ < 0 := by
    rw [← F.hN, F.zero 1 1 (by decide), sub_zero]; exact F.neg 1 2 (by decide)
  have hN2 : 0 < ⟪F.N 2, x 2 - x 1⟫ := by
    rw [← F.hN, F.zero 2 2 (by decide)]; linarith [F.neg 2 1 (by decide)]
  have hN3 : ⟪F.N 3, x 2 - x 1⟫ ≤ 0 := by
    rw [← F.hN]; rcases hnb with h | ⟨h, _⟩ <;> linarith
  have hN5 : ⟪F.N 5, x 2 - x 1⟫ = 0 := by
    rw [← F.hN, F.zero 5 2 (by decide), F.zero 5 1 (by decide), sub_self]
  have hN6 : 0 < ⟪F.N 6, x 2 - x 1⟫ := by
    rw [← F.hN, F.zero 6 2 (by decide)]; linarith [F.neg 6 1 (by decide)]
  have hN7 : 0 < ⟪F.N 7, x 2 - x 1⟫ := by
    rw [← F.hN, F.zero 7 2 (by decide)]; linarith [F.neg 7 1 (by decide)]
  have hN8 := h346
  have hN4 : ⟪F.N 4, x 2 - x 1⟫ < 0 := by
    have e := fac_eval F 4 4
    rw [F.zero 4 4 (by decide), F.zero 4 0 (by decide), F.zero 4 6 (by decide)] at e
    have h1 := F.neg 4 1 (by decide)
    have hω := T.eq4
    have hω4 := hC.2.1
    have key : (F.f 4 (x 2) - F.f 4 (x 1)) * oblX2 x 4 =
        F.f 4 (x 1) * (omega4 x * oblX2 x 4) := by
      linear_combination (-1 : ℝ) * e + F.f 4 (x 1) * hω
    rw [← F.hN]
    by_contra hge
    push Not at hge
    have h2 : 0 ≤ (F.f 4 (x 2) - F.f 4 (x 1)) * oblX2 x 4 := mul_nonneg hge hb4.le
    have h3 := mul_neg_of_neg_of_pos h1 (mul_pos hω4 hb4)
    linarith
  have hN0d : 0 < ⟪F.N 0, -(x 0 - x 1) - (x 6 - x 1)⟫ := by
    rw [inner_sub_right, inner_neg_right, ← F.hN, ← F.hN, F.zero 0 0 (by decide),
      F.zero 0 1 (by decide)]
    linarith [F.neg 0 6 (by decide)]
  have hN5d : 0 < ⟪F.N 5, -(x 0 - x 1) - (x 6 - x 1)⟫ := by
    rw [inner_sub_right, inner_neg_right, ← F.hN, ← F.hN, F.zero 5 6 (by decide),
      F.zero 5 1 (by decide)]
    linarith [F.neg 5 0 (by decide)]
  have hN3' : LexPos3 (-⟪F.N 3, x 2 - x 1⟫) (-⟪F.N 3, -(x 0 - x 1) - (x 6 - x 1)⟫)
      (-⟪F.N 3, x 0 - x 1⟫) := by
    rcases hnb with h | ⟨h, hnc⟩
    · exact Or.inl (by rw [← F.hN]; linarith)
    · refine Or.inr ⟨by rw [← F.hN, h]; ring, Or.inl ?_⟩
      rw [inner_sub_right, inner_neg_right, ← F.hN, ← F.hN, F.zero 3 0 (by decide)]
      linarith [F.neg 3 1 (by decide)]
  have hX : GenQuad.CrossOf (x 0) (x 3) (x 5) (x 4) := by
    obtain ⟨s, t, hs, ht, hst, hq⟩ := Minimality.T24.RimFromSigns.lemmaM_quad_decomp F
    have hst0 : 0 < s + t := by linarith
    refine ⟨1 - 1 / (s + t), t / (s + t), ?_, ?_, ?_, ?_, ?_⟩
    · have : 1 / (s + t) < 1 := (div_lt_one hst0).2 hst
      linarith
    · have : 0 < 1 / (s + t) := by positivity
      linarith
    · positivity
    · rw [div_lt_one hst0]; linarith
    · have hx3 : x 3 = x 0 + s • (x 4 - x 0) + t • (x 5 - x 0) := by
        calc x 3 = x 0 + (x 3 - x 0) := by abel
          _ = _ := by rw [hq]; abel
      ext i
      have hi := congrArg (fun v => v i) hx3
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at hi ⊢
      rw [hi]
      field_simp
      ring
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14⟩ := neg6_depth F hab hbc
  exact lexAny_neg6_leaf' F hdet hN0 hN0d hN5 hN5d hN2 hN6 hN7 hN8 hN1 hN4 hN3' hX
    f15_03 f15_04 f15_06 f13_04 f13_06 f14_06 f13_54 f56_13 f56_14 f36_14 f56_03 f56_04 f36_04 f36_54
    d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14


end Minimality.T24.A19
