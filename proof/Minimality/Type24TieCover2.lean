module

public import Minimality.Type24TieCover

@[expose] public section

/-!
# Type 24: A1 tie cover, rim 016435 (Task CK, TIECERT.md)

Completes the A1 tie cover outside the corner `W = {E13 = E23 = 0}` for rim `016435` (1 file + 4 pool shapes):
1. Missing 2D Farkas lines in the vertex-5 frame: `line13_56` (covers `13>56` and `14>56`), `line14_36` (`14>36`),
   and `line06_14` (`06>14`); `45>13` and `45>36` reuse `line45_36` + `wp_k4`.
2. `lexAny_T25_016435_tilt`: T25 leaf on 6-rim `![0, 1, 6, 4, 3, 5]` at arbitrary tilt `(d1, d2)`.
3. `tieCover_016435`: on the tie outside `W`, `LexAny F`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.Q24

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell
  Minimality.LexCell Minimality.Split Minimality.T24.A15
open Minimality.GenQuad (FrontDet)

/-! ### 1. Missing 2D Farkas lines (vertex-5 frame) -/

/-- Line `13>56` / `14>56`: `(c63 - c13)(z1 - z5) + c13(z1 - z6) = -(c63*c11 - c13*c61) E11` at T25. -/
theorem line13_56 {x : Fin 7 → ℝ³} {b25 : ℝ³} {c11 c12 c13 c61 c62 c63 : ℝ}
    (hb25 : b25 = x 5 - x 2)
    (hx1 : x 1 - x 5 = c11 • (x 2 - x 5) + c12 • (x 0 - x 5) + c13 • (x 3 - x 5))
    (hx6 : x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5))
    (tie : ⟪x 2 - x 5, x 0 - x 5⟫ = 0) :
    (c63 - c13) * ⟪x 1 - x 5, b25⟫ + c13 * ⟪x 1 - x 6, b25⟫ =
      -(c63 * c11 - c13 * c61) * ⟪x 2 - x 5, x 2 - x 5⟫ := by
  have h25 : x 5 - x 2 = -(x 2 - x 5) := by abel
  have h16 : x 1 - x 6 = (x 1 - x 5) - (x 6 - x 5) := by abel
  subst hb25
  rw [h25, h16, hx1, hx6]
  generalize x 2 - x 5 = e1 at *
  generalize x 0 - x 5 = e2 at *
  generalize x 3 - x 5 = e3 at *
  simp only [inner_add_left, inner_sub_left, inner_smul_left, inner_neg_right,
    real_inner_comm e1 e2, real_inner_comm e1 e3] at *
  simp only [conj_trivial]
  linear_combination (-(c63 - c13) * c12 - c13 * (c12 - c62)) * tie

/-- Line `14>36`: `(q4 - 1)(z1 - z3) + (1 - c13)(z4 - z3) = -(q4 - 1) c11 E11` at T25. -/
theorem line14_36 {x : Fin 7 → ℝ³} {b25 : ℝ³} {c11 c12 c13 p4 q4 : ℝ}
    (hb25 : b25 = x 5 - x 2)
    (hx1 : x 1 - x 5 = c11 • (x 2 - x 5) + c12 • (x 0 - x 5) + c13 • (x 3 - x 5))
    (hx4 : x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5))
    (tie : ⟪x 2 - x 5, x 0 - x 5⟫ = 0) :
    (q4 - 1) * ⟪x 1 - x 3, b25⟫ + (1 - c13) * ⟪x 4 - x 3, b25⟫ =
      -(q4 - 1) * c11 * ⟪x 2 - x 5, x 2 - x 5⟫ := by
  have h25 : x 5 - x 2 = -(x 2 - x 5) := by abel
  have h13 : x 1 - x 3 = (x 1 - x 5) - (x 3 - x 5) := by abel
  have h43 : x 4 - x 3 = (x 4 - x 5) - (x 3 - x 5) := by abel
  subst hb25
  rw [h25, h13, h43, hx1, hx4]
  generalize x 2 - x 5 = e1 at *
  generalize x 0 - x 5 = e2 at *
  generalize x 3 - x 5 = e3 at *
  simp only [inner_add_left, inner_sub_left, inner_smul_left, inner_neg_right,
    real_inner_comm e1 e2, real_inner_comm e1 e3] at *
  simp only [conj_trivial]
  linear_combination (-(q4 - 1) * c12 - (1 - c13) * p4) * tie

/-- Line `06>14`: `(c63 - q4)(z0 - z4) + q4(z6 - z4) = -q4 c61 E11` at T25. -/
theorem line06_14 {x : Fin 7 → ℝ³} {b25 : ℝ³} {p4 q4 c61 c62 c63 : ℝ}
    (hb25 : b25 = x 5 - x 2)
    (hx4 : x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5))
    (hx6 : x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5))
    (tie : ⟪x 2 - x 5, x 0 - x 5⟫ = 0) :
    (c63 - q4) * ⟪x 0 - x 4, b25⟫ + q4 * ⟪x 6 - x 4, b25⟫ =
      -q4 * c61 * ⟪x 2 - x 5, x 2 - x 5⟫ := by
  have h25 : x 5 - x 2 = -(x 2 - x 5) := by abel
  have h04 : x 0 - x 4 = (x 0 - x 5) - (x 4 - x 5) := by abel
  have h64 : x 6 - x 4 = (x 6 - x 5) - (x 4 - x 5) := by abel
  subst hb25
  rw [h25, h04, h64, hx4, hx6]
  generalize x 2 - x 5 = e1 at *
  generalize x 0 - x 5 = e2 at *
  generalize x 3 - x 5 = e3 at *
  simp only [inner_add_left, inner_sub_left, inner_smul_left, inner_neg_right,
    real_inner_comm e1 e2, real_inner_comm e1 e3] at *
  simp only [conj_trivial]
  linear_combination ((c63 - q4) * (p4 - 1) - q4 * (c62 - p4)) * tie

/-! ### 2. T25 tilted leaf on 6-rim `![0, 1, 6, 4, 3, 5]` -/

private def c25d' : ZMod 6 → Fin 7 := ![0, 1, 6, 4, 3, 5]
private theorem c25d'_inj : Function.Injective c25d' := by decide
private theorem c25d'_cyc : S0xCycUD s0x_S24 c25d' {1, 3, 4} {0, 2, 5, 6, 7, 8} := by decide

/-- `lexAny_T25_016435_tilt`: T25 leaf on 6-rim `(0 1 6 4 3 5)` at arbitrary tilt `(d1, d2)`,
with the coplanar `0435` subset discharged by `GenQuad.lexClause_of_crossOf`. -/
theorem lexAny_T25_016435_tilt {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (d1 d2 : ℝ³)
    (hdet : Split.det3 (bT25 x) d1 d2 ≠ 0)
    (h1 : 0 < ⟪F.N 1, bT25 x⟫) (h3 : 0 < ⟪F.N 3, bT25 x⟫) (h4 : 0 < ⟪F.N 4, bT25 x⟫)
    (h0 : ⟪F.N 0, bT25 x⟫ < 0) (h5 : ⟪F.N 5, bT25 x⟫ < 0)
    (h7 : ⟪F.N 7, bT25 x⟫ < 0) (h8 : ⟪F.N 8, bT25 x⟫ < 0)
    (t2 : LexPos3 (-⟪F.N 2, bT25 x⟫) (-⟪F.N 2, d1⟫) (-⟪F.N 2, d2⟫))
    (t6 : LexPos3 (-⟪F.N 6, bT25 x⟫) (-⟪F.N 6, d1⟫) (-⟪F.N 6, d2⟫))
    (hX : GenQuad.CrossOf (x 0) (x 3) (x 4) (x 5))
    (f0614 : FrontDet (x 0) (x 6) (x 1) (x 4) (bT25 x))
    (f0613 : FrontDet (x 0) (x 6) (x 1) (x 3) (bT25 x))
    (f0615 : FrontDet (x 0) (x 6) (x 1) (x 5) (bT25 x))
    (f0413 : FrontDet (x 0) (x 4) (x 1) (x 3) (bT25 x))
    (f0415 : FrontDet (x 0) (x 4) (x 1) (x 5) (bT25 x))
    (f0315 : FrontDet (x 0) (x 3) (x 1) (x 5) (bT25 x))
    (f0463 : FrontDet (x 0) (x 4) (x 6) (x 3) (bT25 x))
    (f0465 : FrontDet (x 0) (x 4) (x 6) (x 5) (bT25 x))
    (f0365 : FrontDet (x 0) (x 3) (x 6) (x 5) (bT25 x))
    (f1463 : FrontDet (x 1) (x 4) (x 6) (x 3) (bT25 x))
    (f1465 : FrontDet (x 1) (x 4) (x 6) (x 5) (bT25 x))
    (f6513 : FrontDet (x 6) (x 5) (x 1) (x 3) (bT25 x))
    (f4513 : FrontDet (x 4) (x 5) (x 1) (x 3) (bT25 x))
    (f4563 : FrontDet (x 4) (x 5) (x 6) (x 3) (bT25 x))
    (m0614 : GenQuad.LexClause (x 1) (x 4) (x 0) (x 6) (bT25 x) d1 d2)
    (m0613 : GenQuad.LexClause (x 1) (x 3) (x 0) (x 6) (bT25 x) d1 d2)
    (m0615 : GenQuad.LexClause (x 1) (x 5) (x 0) (x 6) (bT25 x) d1 d2)
    (m0413 : GenQuad.LexClause (x 1) (x 3) (x 0) (x 4) (bT25 x) d1 d2)
    (m0415 : GenQuad.LexClause (x 1) (x 5) (x 0) (x 4) (bT25 x) d1 d2)
    (m0315 : GenQuad.LexClause (x 1) (x 5) (x 0) (x 3) (bT25 x) d1 d2)
    (m0463 : GenQuad.LexClause (x 6) (x 3) (x 0) (x 4) (bT25 x) d1 d2)
    (m0465 : GenQuad.LexClause (x 6) (x 5) (x 0) (x 4) (bT25 x) d1 d2)
    (m0365 : GenQuad.LexClause (x 6) (x 5) (x 0) (x 3) (bT25 x) d1 d2)
    (m1463 : GenQuad.LexClause (x 6) (x 3) (x 1) (x 4) (bT25 x) d1 d2)
    (m1465 : GenQuad.LexClause (x 6) (x 5) (x 1) (x 4) (bT25 x) d1 d2)
    (m6513 : GenQuad.LexClause (x 1) (x 3) (x 6) (x 5) (bT25 x) d1 d2)
    (m4513 : GenQuad.LexClause (x 1) (x 3) (x 4) (x 5) (bT25 x) d1 d2)
    (m4563 : GenQuad.LexClause (x 6) (x 3) (x 4) (x 5) (bT25 x) d1 d2) :
    LexAny F := by
  have hb : bT25 x ≠ 0 := fun h => by rw [h, inner_zero_right] at h1; exact lt_irrefl _ h1
  have hinj := inj_of_fac F
  have h04 : x 0 ≠ x 4 := fun h => absurd (hinj h) (by decide)
  obtain ⟨cB, cA⟩ := GenQuad.lexClause_of_crossOf hX hdet h04
  refine GenQuad.lexAny_of_clauses F (k := 6) (by norm_num) c25d'_inj c25d'_cyc (bT25 x) d1 d2 ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact Or.inl h1
    · exact Or.inl h3
    · exact Or.inl h4
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (by linarith)
    · exact t2
    · exact Or.inl (by linarith)
    · exact t6
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
  · exact GenQuad.clauses_six (p := fun i => x (c25d' i)) (b := bT25 x) (d1 := d1) (d2 := d2)
      m0614 (lexClause_of_det hb f0614)
      m0613 (lexClause_of_det hb f0613)
      m0615 (lexClause_of_det hb f0615)
      m0413 (lexClause_of_det hb f0413)
      m0415 (lexClause_of_det hb f0415)
      m0315 (lexClause_of_det hb f0315)
      m0463 (lexClause_of_det hb f0463)
      m0465 (lexClause_of_det hb f0465)
      m0365 (lexClause_of_det hb f0365)
      cA cB
      m1463 (lexClause_of_det hb f1463)
      m1465 (lexClause_of_det hb f1465)
      (lexClause_of_det hb f6513) m6513
      (lexClause_of_det hb f4513) m4513
      (lexClause_of_det hb f4563) m4563

/-! ### 3. Tie cover, rim 016435 -/

/-- **Tie cover, rim 016435** (TIECERT 3.4). On the tie, outside `W = {E13 = E23 = 0}`:
T25 (rim `016435`, tilt `(d1, d2)`) or T26 gives `LexAny`. -/
theorem tieCover_016435 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {d1 d2 : ℝ³}
    {μ a δ γ p4 q4 c11 c12 c13 c61 c62 c63 : ℝ}
    (hd1 : d1 = γ • (x 2 - x 5) + δ • (x 3 - x 5)) (hδ : 0 < δ)
    (hb26 : bT26 x = μ • ((a - 1) • (x 2 - x 5) - a • (x 0 - x 5))) (hμ : 0 < μ) (ha : 1 < a)
    (hx4 : x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5)) (hp4 : 0 < p4) (hq4 : 1 < q4)
    (hx1 : x 1 - x 5 = c11 • (x 2 - x 5) + c12 • (x 0 - x 5) + c13 • (x 3 - x 5))
    (hc11 : 0 < c11) (hc13 : 0 ≤ c13) (hc13_1 : c13 < 1)
    (hx6 : x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5))
    (hc61 : 0 < c61) (hc13_63 : c13 ≤ c63) (hq4_63 : q4 ≤ c63)
    (h16 : 0 < c63 * c11 - c13 * c61)
    (tie : ⟪x 2 - x 5, x 0 - x 5⟫ = 0)
    (hW : ¬ (⟪x 2 - x 5, x 3 - x 5⟫ = 0 ∧ ⟪x 0 - x 5, x 3 - x 5⟫ = 0))
    -- T25 leaf hypotheses
    (hdet : Split.det3 (bT25 x) d1 d2 ≠ 0)
    (h1 : 0 < ⟪F.N 1, bT25 x⟫) (h3 : 0 < ⟪F.N 3, bT25 x⟫) (h4 : 0 < ⟪F.N 4, bT25 x⟫)
    (h0 : ⟪F.N 0, bT25 x⟫ < 0) (h5 : ⟪F.N 5, bT25 x⟫ < 0)
    (h7 : ⟪F.N 7, bT25 x⟫ < 0) (h8 : ⟪F.N 8, bT25 x⟫ < 0)
    (t2 : LexPos3 (-⟪F.N 2, bT25 x⟫) (-⟪F.N 2, d1⟫) (-⟪F.N 2, d2⟫))
    (t6 : LexPos3 (-⟪F.N 6, bT25 x⟫) (-⟪F.N 6, d1⟫) (-⟪F.N 6, d2⟫))
    (hX : GenQuad.CrossOf (x 0) (x 3) (x 4) (x 5))
    (f0614 : FrontDet (x 0) (x 6) (x 1) (x 4) (bT25 x))
    (f0613 : FrontDet (x 0) (x 6) (x 1) (x 3) (bT25 x))
    (f0615 : FrontDet (x 0) (x 6) (x 1) (x 5) (bT25 x))
    (f0413 : FrontDet (x 0) (x 4) (x 1) (x 3) (bT25 x))
    (f0415 : FrontDet (x 0) (x 4) (x 1) (x 5) (bT25 x))
    (f0315 : FrontDet (x 0) (x 3) (x 1) (x 5) (bT25 x))
    (f0463 : FrontDet (x 0) (x 4) (x 6) (x 3) (bT25 x))
    (f0465 : FrontDet (x 0) (x 4) (x 6) (x 5) (bT25 x))
    (f0365 : FrontDet (x 0) (x 3) (x 6) (x 5) (bT25 x))
    (f1463 : FrontDet (x 1) (x 4) (x 6) (x 3) (bT25 x))
    (f1465 : FrontDet (x 1) (x 4) (x 6) (x 5) (bT25 x))
    (f6513 : FrontDet (x 6) (x 5) (x 1) (x 3) (bT25 x))
    (f4513 : FrontDet (x 4) (x 5) (x 1) (x 3) (bT25 x))
    (f4563 : FrontDet (x 4) (x 5) (x 6) (x 3) (bT25 x))
    -- T26 leaf hypotheses
    (g6 : 0 < ⟪F.N 6, bT26 x⟫) (g7 : 0 < ⟪F.N 7, bT26 x⟫) (g8 : 0 < ⟪F.N 8, bT26 x⟫)
    (g3 : ⟪F.N 3, bT26 x⟫ < 0) (g4 : ⟪F.N 4, bT26 x⟫ < 0)
    (f2354 : FrontDet (x 2) (x 3) (x 5) (x 4) (bT26 x))
    (f2356 : FrontDet (x 2) (x 3) (x 5) (x 6) (bT26 x))
    (f2456 : FrontDet (x 2) (x 4) (x 5) (x 6) (bT26 x))
    (f3624 : FrontDet (x 3) (x 6) (x 2) (x 4) (bT26 x))
    (f3654 : FrontDet (x 3) (x 6) (x 5) (x 4) (bT26 x)) :
    LexAny F := by
  have hb25 : bT25 x = x 5 - x 2 := rfl
  have hinj := inj_of_fac F
  have hne2 : x 2 - x 5 ≠ 0 := sub_ne_zero.2 (fun h => absurd (hinj h) (by decide))
  have E11 : 0 < ⟪x 2 - x 5, x 2 - x 5⟫ := real_inner_self_pos.mpr hne2
  have E33 : 0 < ⟪x 3 - x 5, x 3 - x 5⟫ :=
    real_inner_self_pos.mpr (sub_ne_zero.2 (fun h => absurd (hinj h) (by decide)))
  have hq0 : 0 < q4 := by linarith
  have kill := kill26 F hb26 hμ ha hx4 hp4 hq0.le tie g6 g7 g8 g3 g4 f2354 f2356 f2456 f3624 f3654
  have iS : ∀ u v : Fin 7, ⟪x u - x v, bT25 x⟫ = ⟪x u, bT25 x⟫ - ⟪x v, bT25 x⟫ :=
    fun u v => inner_sub_left _ _ _
  have viaT : 0 ≤ ⟪x 3 - x 5, bT25 x⟫ → 0 ≤ ⟪x 0 - x 5, d1⟫ → LexAny F := by
    intro hA hB
    rcases T_dich hb25 hd1 hb26 tie hμ hδ ha hA hB with h | h
    · exact kill h
    · exact absurd h hW
  have viaT4 : 0 ≤ ⟪x 4 - x 5, bT25 x⟫ → 0 ≤ ⟪x 0 - x 5, d1⟫ → LexAny F := by
    intro hA4 hB
    have e := z45_q4 hb25 hx4 tie
    refine viaT ?_ hB
    by_contra hneg; push Not at hneg
    nlinarith [mul_pos hq0 (neg_pos.2 hneg)]
  have viaW'03 : ⟪x 0 - x 3, bT25 x⟫ = 0 → ⟪x 3, d1⟫ ≤ ⟪x 0, d1⟫ → LexAny F := by
    intro hz h30d
    have E13 : ⟪x 2 - x 5, x 3 - x 5⟫ = 0 := by rw [← z03_E13 hb25 tie]; exact hz
    exact kill (wp_k3 hd1 hb26 tie E13 hδ hμ ha E33 h30d)
  have viaW'53 : ⟪x 5 - x 3, bT25 x⟫ = 0 → ⟪x 3, d1⟫ ≤ ⟪x 5, d1⟫ → False := by
    intro hz h35d
    have E13 : ⟪x 2 - x 5, x 3 - x 5⟫ = 0 := by rw [← z53_E13 hb25]; exact hz
    exact wp_k4 hd1 E13 hδ E33 h35d
  have k0614 : GenQuad.LexClause (x 1) (x 4) (x 0) (x 6) (bT25 x) d1 d2 := by
    by_contra hn
    obtain ⟨-, -, ⟨u3, -⟩, ⟨u4, -⟩⟩ := notClause hn
    have l := line06_14 hb25 hx4 hx6 tie
    have e1 := iS 0 4; have e2 := iS 6 4
    rw [e1, e2] at l
    nlinarith only [l, mul_nonneg (sub_nonneg.2 hq4_63) (sub_nonneg.2 u3),
      mul_nonneg hq0.le (sub_nonneg.2 u4), mul_pos (mul_pos hq0 hc61) E11]
  have k0613 : GenQuad.LexClause (x 1) (x 3) (x 0) (x 6) (bT25 x) d1 d2 := by
    by_contra hn
    obtain ⟨-, -, ⟨u3, -⟩, ⟨u4, -⟩⟩ := notClause hn
    have l := line06_13 hb25 hx6 tie
    have e1 := iS 0 3; have e2 := iS 6 3
    have hc63_1 : 1 ≤ c63 := by linarith only [hq4, hq4_63]
    rw [e1, e2] at l
    nlinarith only [l, mul_nonneg (sub_nonneg.2 hc63_1) (sub_nonneg.2 u3),
      sub_nonneg.2 u4, mul_pos hc61 E11]
  by_cases k0615 : GenQuad.LexClause (x 1) (x 5) (x 0) (x 6) (bT25 x) d1 d2
  swap
  · obtain ⟨-, -, ⟨u1, u1'⟩, ⟨u2, -⟩⟩ := notClause k0615
    exact kill (T6_strict hb25 hd1 hb26 hx6 tie hμ hδ ha hc61 (by linarith) E11
      (by rw [iS 6 5]; linarith) (levelB hb25 tie u1 u1'))
  by_cases k0413 : GenQuad.LexClause (x 1) (x 3) (x 0) (x 4) (bT25 x) d1 d2
  swap
  · obtain ⟨-, -, ⟨u3, u3'⟩, ⟨u4, -⟩⟩ := notClause k0413
    have l := line04_36 hb25 hx4 tie
    have e1 := iS 0 3; have e2 := iS 4 3
    have hz : ⟪x 0 - x 3, bT25 x⟫ = 0 := by
      by_contra hne
      have hpos := mul_pos (sub_pos.2 hq4) (lt_of_le_of_ne (by rw [e1]; linarith) (Ne.symm hne))
      rw [e2] at l; linarith only [l, hpos, u4]
    exact viaW'03 hz (u3' (by rw [e1] at hz; linarith))
  by_cases k0415 : GenQuad.LexClause (x 1) (x 5) (x 0) (x 4) (bT25 x) d1 d2
  swap
  · obtain ⟨-, -, ⟨u1, u1'⟩, ⟨u2, -⟩⟩ := notClause k0415
    exact viaT4 (by rw [iS 4 5]; linarith) (levelB hb25 tie u1 u1')
  by_cases k0315 : GenQuad.LexClause (x 1) (x 5) (x 0) (x 3) (bT25 x) d1 d2
  swap
  · obtain ⟨-, -, ⟨u1, u1'⟩, ⟨u2, -⟩⟩ := notClause k0315
    exact viaT (by rw [iS 3 5]; linarith) (levelB hb25 tie u1 u1')
  by_cases k0463 : GenQuad.LexClause (x 6) (x 3) (x 0) (x 4) (bT25 x) d1 d2
  swap
  · obtain ⟨-, -, ⟨u3, u3'⟩, ⟨u4, -⟩⟩ := notClause k0463
    have l := line04_36 hb25 hx4 tie
    have e1 := iS 0 3; have e2 := iS 4 3
    have hz : ⟪x 0 - x 3, bT25 x⟫ = 0 := by
      by_contra hne
      have hpos := mul_pos (sub_pos.2 hq4) (lt_of_le_of_ne (by rw [e1]; linarith) (Ne.symm hne))
      rw [e2] at l; linarith only [l, hpos, u4]
    exact viaW'03 hz (u3' (by rw [e1] at hz; linarith))
  by_cases k0465 : GenQuad.LexClause (x 6) (x 5) (x 0) (x 4) (bT25 x) d1 d2
  swap
  · obtain ⟨-, -, ⟨u1, u1'⟩, ⟨u2, -⟩⟩ := notClause k0465
    exact viaT4 (by rw [iS 4 5]; linarith) (levelB hb25 tie u1 u1')
  by_cases k0365 : GenQuad.LexClause (x 6) (x 5) (x 0) (x 3) (bT25 x) d1 d2
  swap
  · obtain ⟨-, -, ⟨u1, u1'⟩, ⟨u2, -⟩⟩ := notClause k0365
    exact viaT (by rw [iS 3 5]; linarith) (levelB hb25 tie u1 u1')
  have k1463 : GenQuad.LexClause (x 6) (x 3) (x 1) (x 4) (bT25 x) d1 d2 := by
    by_contra hn
    obtain ⟨-, -, ⟨u3, -⟩, ⟨u4, -⟩⟩ := notClause hn
    have l := line14_36 hb25 hx1 hx4 tie
    have e1 := iS 1 3; have e2 := iS 4 3
    rw [e1, e2] at l
    nlinarith only [l, mul_nonneg (sub_pos.2 hq4).le (sub_nonneg.2 u3),
      mul_nonneg (sub_pos.2 hc13_1).le (sub_nonneg.2 u4),
      mul_pos (mul_pos (sub_pos.2 hq4) hc11) E11]
  have k1465 : GenQuad.LexClause (x 6) (x 5) (x 1) (x 4) (bT25 x) d1 d2 := by
    by_contra hn
    obtain ⟨⟨u1, -⟩, -, ⟨u3, -⟩, -⟩ := notClause hn
    have l := line13_56 hb25 hx1 hx6 tie
    have e1 := iS 1 5; have e2 := iS 1 6
    rw [e1, e2] at l
    nlinarith only [l, mul_nonneg (sub_nonneg.2 hc13_63) (sub_nonneg.2 u3),
      mul_nonneg hc13 (sub_nonneg.2 u1), mul_pos h16 E11]
  have k6513 : GenQuad.LexClause (x 1) (x 3) (x 6) (x 5) (bT25 x) d1 d2 := by
    by_contra hn
    obtain ⟨-, -, ⟨u3, -⟩, ⟨u4, -⟩⟩ := notClause hn
    have l := line56_13 hb25 hx6 tie
    have e1 := iS 5 3; have e2 := iS 6 3
    have hc63_1 : 1 ≤ c63 := by linarith only [hq4, hq4_63]
    rw [e1, e2] at l
    nlinarith only [l, mul_nonneg (sub_nonneg.2 hc63_1) (sub_nonneg.2 u4),
      sub_nonneg.2 u3, mul_pos hc61 E11]
  have k4513 : GenQuad.LexClause (x 1) (x 3) (x 4) (x 5) (bT25 x) d1 d2 := by
    by_contra hn
    obtain ⟨-, -, ⟨u3, -⟩, ⟨u4, u4'⟩⟩ := notClause hn
    have l := line45_36 hb25 hx4 tie
    have e1 := iS 5 3; have e2 := iS 4 3
    have hz : ⟪x 5 - x 3, bT25 x⟫ = 0 := by
      by_contra hne
      have hpos := mul_pos (sub_pos.2 hq4) (lt_of_le_of_ne (by rw [e1]; linarith) (Ne.symm hne))
      rw [e2] at l; linarith only [l, hpos, u3]
    exact viaW'53 hz (u4' (by rw [e1] at hz; linarith))
  have k4563 : GenQuad.LexClause (x 6) (x 3) (x 4) (x 5) (bT25 x) d1 d2 := by
    by_contra hn
    obtain ⟨-, -, ⟨u3, -⟩, ⟨u4, u4'⟩⟩ := notClause hn
    have l := line45_36 hb25 hx4 tie
    have e1 := iS 5 3; have e2 := iS 4 3
    have hz : ⟪x 5 - x 3, bT25 x⟫ = 0 := by
      by_contra hne
      have hpos := mul_pos (sub_pos.2 hq4) (lt_of_le_of_ne (by rw [e1]; linarith) (Ne.symm hne))
      rw [e2] at l; linarith only [l, hpos, u3]
    exact viaW'53 hz (u4' (by rw [e1] at hz; linarith))
  exact lexAny_T25_016435_tilt F d1 d2 hdet h1 h3 h4 h0 h5 h7 h8 t2 t6 hX
    f0614 f0613 f0615 f0413 f0415 f0315 f0463 f0465 f0365 f1463 f1465 f6513 f4513 f4563
    k0614 k0613 k0615 k0413 k0415 k0315 k0463 k0465 k0365 k1463 k1465 k6513 k4513 k4563

/-! ### 4. Rim `01635` with flipped `(6, 5; 1, 3)` front (`H_adv_s7206_r246`, Task CO) -/

private def c25b_flip : ZMod 5 → Fin 7 := ![0, 1, 6, 3, 5]
private theorem c25b_flip_inj : Function.Injective c25b_flip := by decide
private theorem c25b_flip_cyc : S0xCycUD s0x_S24 c25b_flip {1, 3, 8} {0, 2, 5, 6, 7} := by decide

/-- `lexAny_T25_01635_tilt` with the opposite `(6, 5; 1, 3)` front (`FrontDet (x 1) (x 3) (x 6) (x 5)`). -/
theorem lexAny_T25_01635_tilt_flip {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (d1 d2 : ℝ³)
    (h1 : 0 < ⟪F.N 1, bT25 x⟫) (h3 : 0 < ⟪F.N 3, bT25 x⟫) (h8 : 0 < ⟪F.N 8, bT25 x⟫)
    (h0 : ⟪F.N 0, bT25 x⟫ < 0) (h5 : ⟪F.N 5, bT25 x⟫ < 0) (h7 : ⟪F.N 7, bT25 x⟫ < 0)
    (t2 : LexPos3 (-⟪F.N 2, bT25 x⟫) (-⟪F.N 2, d1⟫) (-⟪F.N 2, d2⟫))
    (t6 : LexPos3 (-⟪F.N 6, bT25 x⟫) (-⟪F.N 6, d1⟫) (-⟪F.N 6, d2⟫))
    (f0613 : FrontDet (x 0) (x 6) (x 1) (x 3) (bT25 x))
    (f0615 : FrontDet (x 0) (x 6) (x 1) (x 5) (bT25 x))
    (f0315 : FrontDet (x 0) (x 3) (x 1) (x 5) (bT25 x))
    (f0365 : FrontDet (x 0) (x 3) (x 6) (x 5) (bT25 x))
    (f1365 : FrontDet (x 1) (x 3) (x 6) (x 5) (bT25 x))
    (m0613 : GenQuad.LexClause (x 1) (x 3) (x 0) (x 6) (bT25 x) d1 d2)
    (m0615 : GenQuad.LexClause (x 1) (x 5) (x 0) (x 6) (bT25 x) d1 d2)
    (m0315 : GenQuad.LexClause (x 1) (x 5) (x 0) (x 3) (bT25 x) d1 d2)
    (m0365 : GenQuad.LexClause (x 6) (x 5) (x 0) (x 3) (bT25 x) d1 d2)
    (m1365 : GenQuad.LexClause (x 6) (x 5) (x 1) (x 3) (bT25 x) d1 d2) :
    LexAny F := by
  have hb : bT25 x ≠ 0 := fun h => by rw [h, inner_zero_right] at h1; exact lt_irrefl _ h1
  refine GenQuad.lexAny_of_clauses F (k := 5) (by norm_num) c25b_flip_inj c25b_flip_cyc (bT25 x) d1 d2 ?_ ?_ ?_
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
    · exact t2
    · exact Or.inl (by linarith)
    · exact t6
    · exact Or.inl (by linarith)
  · exact GenQuad.clauses_five (p := fun i => x (c25b_flip i)) (b := bT25 x) (d1 := d1) (d2 := d2)
      m0613 (lexClause_of_det hb f0613)
      m0615 (lexClause_of_det hb f0615)
      m0315 (lexClause_of_det hb f0315)
      m0365 (lexClause_of_det hb f0365)
      m1365 (lexClause_of_det hb f1365)

/-- **Tie cover, rim 01635 (flipped `(6, 5; 1, 3)` front)**: closes `m1365` by `line13_56`. -/
theorem tieCover_01635_flip {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {d1 d2 : ℝ³}
    {μ a δ γ p4 q4 c11 c12 c13 c61 c62 c63 : ℝ}
    (hd1 : d1 = γ • (x 2 - x 5) + δ • (x 3 - x 5)) (hδ : 0 < δ)
    (hb26 : bT26 x = μ • ((a - 1) • (x 2 - x 5) - a • (x 0 - x 5))) (hμ : 0 < μ) (ha : 1 < a)
    (hx4 : x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5)) (hp4 : 0 < p4) (hq4 : 0 ≤ q4)
    (hx1 : x 1 - x 5 = c11 • (x 2 - x 5) + c12 • (x 0 - x 5) + c13 • (x 3 - x 5))
    (hc13 : 0 ≤ c13)
    (hx6 : x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5))
    (hc61 : 0 < c61) (hc63 : 1 ≤ c63) (hc13_63 : c13 ≤ c63) (h16 : 0 < c63 * c11 - c13 * c61)
    (tie : ⟪x 2 - x 5, x 0 - x 5⟫ = 0)
    (hW : ¬ (⟪x 2 - x 5, x 3 - x 5⟫ = 0 ∧ ⟪x 0 - x 5, x 3 - x 5⟫ = 0))
    -- T25 leaf hypotheses
    (h1 : 0 < ⟪F.N 1, bT25 x⟫) (h3 : 0 < ⟪F.N 3, bT25 x⟫) (h8 : 0 < ⟪F.N 8, bT25 x⟫)
    (h0 : ⟪F.N 0, bT25 x⟫ < 0) (h5 : ⟪F.N 5, bT25 x⟫ < 0) (h7 : ⟪F.N 7, bT25 x⟫ < 0)
    (t2 : LexPos3 (-⟪F.N 2, bT25 x⟫) (-⟪F.N 2, d1⟫) (-⟪F.N 2, d2⟫))
    (t6 : LexPos3 (-⟪F.N 6, bT25 x⟫) (-⟪F.N 6, d1⟫) (-⟪F.N 6, d2⟫))
    (f0613 : FrontDet (x 0) (x 6) (x 1) (x 3) (bT25 x))
    (f0615 : FrontDet (x 0) (x 6) (x 1) (x 5) (bT25 x))
    (f0315 : FrontDet (x 0) (x 3) (x 1) (x 5) (bT25 x))
    (f0365 : FrontDet (x 0) (x 3) (x 6) (x 5) (bT25 x))
    (f1365 : FrontDet (x 1) (x 3) (x 6) (x 5) (bT25 x))
    -- T26 leaf hypotheses
    (g6 : 0 < ⟪F.N 6, bT26 x⟫) (g7 : 0 < ⟪F.N 7, bT26 x⟫) (g8 : 0 < ⟪F.N 8, bT26 x⟫)
    (g3 : ⟪F.N 3, bT26 x⟫ < 0) (g4 : ⟪F.N 4, bT26 x⟫ < 0)
    (f2354 : FrontDet (x 2) (x 3) (x 5) (x 4) (bT26 x))
    (f2356 : FrontDet (x 2) (x 3) (x 5) (x 6) (bT26 x))
    (f2456 : FrontDet (x 2) (x 4) (x 5) (x 6) (bT26 x))
    (f3624 : FrontDet (x 3) (x 6) (x 2) (x 4) (bT26 x))
    (f3654 : FrontDet (x 3) (x 6) (x 5) (x 4) (bT26 x)) :
    LexAny F := by
  have hb25 : bT25 x = x 5 - x 2 := rfl
  have hinj := inj_of_fac F
  have hne2 : x 2 - x 5 ≠ 0 := sub_ne_zero.2 (fun h => absurd (hinj h) (by decide))
  have E11 : 0 < ⟪x 2 - x 5, x 2 - x 5⟫ := real_inner_self_pos.mpr hne2
  have kill := kill26 F hb26 hμ ha hx4 hp4 hq4 tie g6 g7 g8 g3 g4 f2354 f2356 f2456 f3624 f3654
  have iS : ∀ u v : Fin 7, ⟪x u - x v, bT25 x⟫ = ⟪x u, bT25 x⟫ - ⟪x v, bT25 x⟫ :=
    fun u v => inner_sub_left _ _ _
  by_cases k1 : GenQuad.LexClause (x 1) (x 3) (x 0) (x 6) (bT25 x) d1 d2
  swap
  · exfalso
    obtain ⟨-, -, ⟨u3, -⟩, ⟨u4, -⟩⟩ := notClause k1
    have l := line06_13 hb25 hx6 tie
    have e1 := iS 0 3; have e2 := iS 6 3
    nlinarith [mul_nonneg (sub_nonneg.2 hc63) (sub_nonneg.2 u3), mul_pos hc61 E11]
  by_cases k2 : GenQuad.LexClause (x 1) (x 3) (x 6) (x 5) (bT25 x) d1 d2
  swap
  · exfalso
    obtain ⟨-, -, ⟨u3, -⟩, ⟨u4, -⟩⟩ := notClause k2
    have l := line56_13 hb25 hx6 tie
    have e1 := iS 5 3; have e2 := iS 6 3
    nlinarith [mul_nonneg (sub_nonneg.2 hc63) (sub_nonneg.2 u4), mul_pos hc61 E11]
  by_cases k3 : GenQuad.LexClause (x 1) (x 5) (x 0) (x 3) (bT25 x) d1 d2
  swap
  · obtain ⟨-, -, ⟨u1, u1'⟩, ⟨u2, -⟩⟩ := notClause k3
    have hB := levelB hb25 tie u1 u1'
    have hA : 0 ≤ ⟪x 3 - x 5, bT25 x⟫ := by rw [iS 3 5]; linarith
    rcases T_dich hb25 hd1 hb26 tie hμ hδ ha hA hB with h | h
    · exact kill h
    · exact absurd h hW
  by_cases k4 : GenQuad.LexClause (x 6) (x 5) (x 0) (x 3) (bT25 x) d1 d2
  swap
  · obtain ⟨-, -, ⟨u1, u1'⟩, ⟨u2, -⟩⟩ := notClause k4
    have hB := levelB hb25 tie u1 u1'
    have hA : 0 ≤ ⟪x 3 - x 5, bT25 x⟫ := by rw [iS 3 5]; linarith
    rcases T_dich hb25 hd1 hb26 tie hμ hδ ha hA hB with h | h
    · exact kill h
    · exact absurd h hW
  by_cases k5 : GenQuad.LexClause (x 1) (x 5) (x 0) (x 6) (bT25 x) d1 d2
  swap
  · obtain ⟨-, -, ⟨u1, u1'⟩, ⟨u2, -⟩⟩ := notClause k5
    have hB := levelB hb25 tie u1 u1'
    have hA : 0 ≤ ⟪x 6 - x 5, bT25 x⟫ := by rw [iS 6 5]; linarith
    exact kill (T6_strict hb25 hd1 hb26 hx6 tie hμ hδ ha hc61 (by linarith) E11 hA hB)
  by_cases k6 : GenQuad.LexClause (x 6) (x 5) (x 1) (x 3) (bT25 x) d1 d2
  swap
  · exfalso
    obtain ⟨⟨u1, -⟩, -, ⟨u3, -⟩, -⟩ := notClause k6
    have l := line13_56 hb25 hx1 hx6 tie
    have e1 := iS 1 5; have e2 := iS 1 6; rw [e1, e2] at l
    nlinarith only [l, mul_nonneg (sub_nonneg.2 hc13_63) (sub_nonneg.2 u3),
      mul_nonneg hc13 (sub_nonneg.2 u1), mul_pos h16 E11]
  exact lexAny_T25_01635_tilt_flip F d1 d2 h1 h3 h8 h0 h5 h7 t2 t6 f0613 f0615 f0315 f0365 f1365
    k1 k5 k3 k4 k6

end Minimality.T24.Q24
