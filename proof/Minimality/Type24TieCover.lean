module

public import Minimality.Type24Quad
public import Minimality.CSLCorner

@[expose] public section

/-!
# Type 24: the A1 tie cover (TIECERT.md, WCORNER.md)

On the tie z2(w05) = z5(w05) (vertex-5 frame e1 = x2 - x5, e2 = x0 - x5, e3 = x3 - x5, tie <e1, e2> = 0), the exact
unimodal regions of T25 (F025xF235+--, b = x5 - x2) and T26 (F025xF126+--) are pairwise incompatible outside the
corner W = {<e1, e3> = 0, <e2, e3> = 0}:
identities `identityI`, `identityT24`, `identityT36`, `identityT6`, 2D lines `line06_13`, `line56_13`, `line04_36`,
`line45_36`; `T_dich` (Lemma T), `T6_strict`, `kill26`; tilted T25 leaves `lexAny_T25_0536_tilt`,
`lexAny_T25_01635_tilt`, `lexAny_T25_05346_tilt`; covers `tieCover_0536`, `tieCover_01635`, `tieCover_05346W`
(W' discharged by `wp_k3`, `wp_k4`). W itself: `CSLCorner.csl24`. Open: rim 016435, sigma = 1 (q4 = 1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.Q24

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell
  Minimality.LexCell Minimality.Split Minimality.T24.A15 Minimality.NF29
open Minimality.GenQuad (FrontDet)

/-! ### Vertex-5 frame: edges e1 = x2 - x5, e2 = x0 - x5, e3 = x3 - x5; E_ij = <e_i, e_j>. -/

/-- Identity I (TIECERT 3.1). `b25 = x5 - x2` (so `<x3-x5,b25> = -E13`), tilt `d1 = γ e1 + δ e3`
(`<x0-x5,d1> = δ E23` on the tie), `b26 = μ((a-1) e1 - a e2)` (`<x3-x5,b26> = μ((a-1)E13 - a E23)`). -/
theorem identityI {x : Fin 7 → ℝ³} {b25 d1 b26 : ℝ³} {μ a δ γ : ℝ}
    (hb25 : b25 = x 5 - x 2) (hd1 : d1 = γ • (x 2 - x 5) + δ • (x 3 - x 5))
    (hb26 : b26 = μ • ((a - 1) • (x 2 - x 5) - a • (x 0 - x 5)))
    (tie : ⟪x 2 - x 5, x 0 - x 5⟫ = 0) :
    μ * δ * (a - 1) * ⟪x 3 - x 5, b25⟫ + μ * a * ⟪x 0 - x 5, d1⟫ + δ * ⟪x 3 - x 5, b26⟫ = 0 := by
  have h25 : x 5 - x 2 = -(x 2 - x 5) := by abel
  subst hb25 hd1 hb26
  rw [h25]
  generalize x 2 - x 5 = e1 at *
  generalize x 0 - x 5 = e2 at *
  generalize x 3 - x 5 = e3 at *
  simp only [inner_add_right, inner_sub_right, inner_smul_right, inner_neg_right,
    real_inner_comm e1 e2, real_inner_comm e1 e3, real_inner_comm e2 e3] at *
  linear_combination (μ * a * γ) * tie

/-- Lemma T-24 (pair with the T26 clause `24>56`): `x4 - x5 = p4 e2 + q4 e3`. -/
theorem identityT24 {x : Fin 7 → ℝ³} {b25 d1 b26 : ℝ³} {μ a δ γ p4 q4 : ℝ}
    (hb25 : b25 = x 5 - x 2) (hd1 : d1 = γ • (x 2 - x 5) + δ • (x 3 - x 5))
    (hb26 : b26 = μ • ((a - 1) • (x 2 - x 5) - a • (x 0 - x 5)))
    (hx4 : x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5))
    (tie : ⟪x 2 - x 5, x 0 - x 5⟫ = 0) :
    δ * ⟪x 4 - x 5, b26⟫ + q4 * (μ * δ * (a - 1) * ⟪x 3 - x 5, b25⟫ + μ * a * ⟪x 0 - x 5, d1⟫)
      = -(δ * p4 * μ * a) * ⟪x 0 - x 5, x 0 - x 5⟫ := by
  have h25 : x 5 - x 2 = -(x 2 - x 5) := by abel
  subst hb25 hd1 hb26
  rw [hx4, h25]
  generalize x 2 - x 5 = e1 at *
  generalize x 0 - x 5 = e2 at *
  generalize x 3 - x 5 = e3 at *
  simp only [inner_add_right, inner_sub_right, inner_smul_right, inner_neg_right, inner_add_left,
    inner_smul_left, real_inner_comm e1 e2, real_inner_comm e1 e3, real_inner_comm e2 e3] at *
  simp only [conj_trivial]
  linear_combination (μ * a * γ * q4 + δ * μ * p4 * (a - 1)) * tie

/-- Lemma T-36 (pair with the T26 clause `36>24`): `z3 - z2` at T26. -/
theorem identityT36 {x : Fin 7 → ℝ³} {b25 d1 b26 : ℝ³} {μ a δ γ : ℝ}
    (hb25 : b25 = x 5 - x 2) (hd1 : d1 = γ • (x 2 - x 5) + δ • (x 3 - x 5))
    (hb26 : b26 = μ • ((a - 1) • (x 2 - x 5) - a • (x 0 - x 5)))
    (tie : ⟪x 2 - x 5, x 0 - x 5⟫ = 0) :
    δ * ⟪x 3 - x 2, b26⟫ + μ * δ * (a - 1) * ⟪x 3 - x 5, b25⟫ + μ * a * ⟪x 0 - x 5, d1⟫
      = -(δ * μ * (a - 1)) * ⟪x 2 - x 5, x 2 - x 5⟫ := by
  have h25 : x 5 - x 2 = -(x 2 - x 5) := by abel
  have h32 : x 3 - x 2 = (x 3 - x 5) - (x 2 - x 5) := by abel
  subst hb25 hd1 hb26
  rw [h25, h32]
  generalize x 2 - x 5 = e1 at *
  generalize x 0 - x 5 = e2 at *
  generalize x 3 - x 5 = e3 at *
  simp only [inner_add_right, inner_sub_right, inner_smul_right, inner_neg_right, inner_sub_left,
    real_inner_comm e1 e2, real_inner_comm e1 e3, real_inner_comm e2 e3] at *
  linear_combination (μ * a * γ + δ * μ * a) * tie

/-- Lemma T6 (T25 clause `06>15`): `x6 - x5 = c61 e1 + c62 e2 + c63 e3`; strict, no sub-tie. -/
theorem identityT6 {x : Fin 7 → ℝ³} {b25 d1 b26 : ℝ³} {μ a δ γ c61 c62 c63 : ℝ}
    (hb25 : b25 = x 5 - x 2) (hd1 : d1 = γ • (x 2 - x 5) + δ • (x 3 - x 5))
    (hb26 : b26 = μ • ((a - 1) • (x 2 - x 5) - a • (x 0 - x 5)))
    (hx6 : x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5))
    (tie : ⟪x 2 - x 5, x 0 - x 5⟫ = 0) :
    μ * δ * (a - 1) * ⟪x 6 - x 5, b25⟫ + c63 * (μ * a * ⟪x 0 - x 5, d1⟫ + δ * ⟪x 3 - x 5, b26⟫)
      = -(μ * δ * (a - 1) * c61) * ⟪x 2 - x 5, x 2 - x 5⟫ := by
  have h25 : x 5 - x 2 = -(x 2 - x 5) := by abel
  subst hb25 hd1 hb26
  rw [hx6, h25]
  generalize x 2 - x 5 = e1 at *
  generalize x 0 - x 5 = e2 at *
  generalize x 3 - x 5 = e3 at *
  simp only [inner_add_right, inner_sub_right, inner_smul_right, inner_neg_right, inner_add_left,
    inner_smul_left, real_inner_comm e1 e2, real_inner_comm e1 e3, real_inner_comm e2 e3] at *
  simp only [conj_trivial]
  linear_combination (c63 * μ * a * γ + μ * δ * (a - 1) * c62 * (-1)) * tie

/-! ### T25-only 2D lines (b25 = x5 - x2; level 0, tie) -/

/-- Line `06>13` (rim 01635): `(c63 - 1) (z0 - z3) + (z6 - z3) = -c61 E11` at T25. -/
theorem line06_13 {x : Fin 7 → ℝ³} {b25 : ℝ³} {c61 c62 c63 : ℝ}
    (hb25 : b25 = x 5 - x 2)
    (hx6 : x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5))
    (tie : ⟪x 2 - x 5, x 0 - x 5⟫ = 0) :
    (c63 - 1) * ⟪x 0 - x 3, b25⟫ + ⟪x 6 - x 3, b25⟫ = -c61 * ⟪x 2 - x 5, x 2 - x 5⟫ := by
  have h25 : x 5 - x 2 = -(x 2 - x 5) := by abel
  have h03 : x 0 - x 3 = (x 0 - x 5) - (x 3 - x 5) := by abel
  have h63 : x 6 - x 3 = (x 6 - x 5) - (x 3 - x 5) := by abel
  subst hb25
  rw [h25, h03, h63, hx6]
  generalize x 2 - x 5 = e1 at *
  generalize x 0 - x 5 = e2 at *
  generalize x 3 - x 5 = e3 at *
  simp only [inner_add_left, inner_sub_left, inner_smul_left, inner_neg_right,
    real_inner_comm e1 e2, real_inner_comm e1 e3] at *
  simp only [conj_trivial]
  linear_combination (-c62 + 1 - c63) * tie

/-- Line `56>13`: the same with `z5` in place of `z0`. -/
theorem line56_13 {x : Fin 7 → ℝ³} {b25 : ℝ³} {c61 c62 c63 : ℝ}
    (hb25 : b25 = x 5 - x 2)
    (hx6 : x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5))
    (tie : ⟪x 2 - x 5, x 0 - x 5⟫ = 0) :
    (c63 - 1) * ⟪x 5 - x 3, b25⟫ + ⟪x 6 - x 3, b25⟫ = -c61 * ⟪x 2 - x 5, x 2 - x 5⟫ := by
  have h25 : x 5 - x 2 = -(x 2 - x 5) := by abel
  have h53 : x 5 - x 3 = -(x 3 - x 5) := by abel
  have h63 : x 6 - x 3 = (x 6 - x 5) - (x 3 - x 5) := by abel
  subst hb25
  rw [h25, h53, h63, hx6]
  generalize x 2 - x 5 = e1 at *
  generalize x 0 - x 5 = e2 at *
  generalize x 3 - x 5 = e3 at *
  simp only [inner_add_left, inner_sub_left, inner_smul_left, inner_neg_right, inner_neg_left,
    real_inner_comm e1 e2, real_inner_comm e1 e3] at *
  simp only [conj_trivial]
  linear_combination (c62 : ℝ) * (-1) * tie

/-- Line `04>36` (W' identity, rims 05346 / 016435): `(q4 - 1)(z0 - z3) + (z4 - z3) = 0` at T25. -/
theorem line04_36 {x : Fin 7 → ℝ³} {b25 : ℝ³} {p4 q4 : ℝ}
    (hb25 : b25 = x 5 - x 2)
    (hx4 : x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5))
    (tie : ⟪x 2 - x 5, x 0 - x 5⟫ = 0) :
    (q4 - 1) * ⟪x 0 - x 3, b25⟫ + ⟪x 4 - x 3, b25⟫ = 0 := by
  have h25 : x 5 - x 2 = -(x 2 - x 5) := by abel
  have h03 : x 0 - x 3 = (x 0 - x 5) - (x 3 - x 5) := by abel
  have h43 : x 4 - x 3 = (x 4 - x 5) - (x 3 - x 5) := by abel
  subst hb25
  rw [h25, h03, h43, hx4]
  generalize x 2 - x 5 = e1 at *
  generalize x 0 - x 5 = e2 at *
  generalize x 3 - x 5 = e3 at *
  simp only [inner_add_left, inner_sub_left, inner_smul_left, inner_neg_right,
    real_inner_comm e1 e2, real_inner_comm e1 e3] at *
  simp only [conj_trivial]
  linear_combination (-p4 + 1 - q4) * tie

/-! ### Rim 0536: the tie cover with the two leaves -/

private def c25a' : ZMod 4 → Fin 7 := ![0, 5, 3, 6]
private theorem c25a'_inj : Function.Injective c25a' := by decide
private theorem c25a'_cyc : S0xCycUD s0x_S24 c25a' {3, 4, 8} {1, 2, 6, 7} := by decide

/-- `lexAny_T25_0536` with the full lexicographic clause (instead of the level-0 `¬M`) and an arbitrary tilt
`(d1, d2)` for which the two tie facets `025` (facet 2) and `235` (facet 6) face down lexicographically. -/
theorem lexAny_T25_0536_tilt {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (d1 d2 : ℝ³)
    (h3 : 0 < ⟪F.N 3, bT25 x⟫) (h4 : 0 < ⟪F.N 4, bT25 x⟫) (h8 : 0 < ⟪F.N 8, bT25 x⟫)
    (h1 : ⟪F.N 1, bT25 x⟫ < 0) (h7 : ⟪F.N 7, bT25 x⟫ < 0)
    (t2 : LexPos3 (-⟪F.N 2, bT25 x⟫) (-⟪F.N 2, d1⟫) (-⟪F.N 2, d2⟫))
    (t6 : LexPos3 (-⟪F.N 6, bT25 x⟫) (-⟪F.N 6, d1⟫) (-⟪F.N 6, d2⟫))
    (f0356 : FrontDet (x 0) (x 3) (x 5) (x 6) (bT25 x))
    (m0356 : GenQuad.LexClause (x 5) (x 6) (x 0) (x 3) (bT25 x) d1 d2) :
    LexAny F := by
  have hb : bT25 x ≠ 0 := fun h => by rw [h, inner_zero_right] at h3; exact lt_irrefl _ h3
  refine GenQuad.lexAny_of_clauses F (k := 4) (by norm_num) c25a'_inj c25a'_cyc (bT25 x) d1 d2 ?_ ?_ ?_
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
    · exact t2
    · exact t6
    · exact Or.inl (by linarith)
  · exact GenQuad.clauses_four (p := fun i => x (c25a' i)) (b := bT25 x) (d1 := d1) (d2 := d2)
      m0356 (lexClause_of_det hb f0356)

theorem notLexPos3 {A B C : ℝ} (h : ¬ LexPos3 A B C) : A ≤ 0 ∧ (A = 0 → B ≤ 0) := by
  unfold LexPos3 at h
  push Not at h
  exact ⟨h.1, fun hA => by have := h.2 hA; exact this.1⟩

theorem zdiff (x : Fin 7 → ℝ³) (u : ℝ³) (v w : Fin 7) : z x u v - z x u w = ⟪x v - x w, u⟫ := by
  simp only [z]; rw [← inner_sub_left]; congr 1; abel

/-- **Tie cover, rim 0536** (QUAD24 4, TIECERT 3.1/3.4). On the tie `E12 = ⟪x2-x5, x0-x5⟫ = 0`, outside the
sub-tie `W` (`E13 = E23 = 0`), either T25 (clause `03>56`, tilt `(d1, d2)`) or T26 gives `LexAny`.
Frame hypotheses: `d1 = γ e1 + δ e3` (`δ > 0`), `bT26 = μ((a-1) e1 - a e2)` (`μ > 0`, `a > 1`),
`x4 - x5 = p4 e2 + q4 e3` (`p4 > 0`, `q4 ≥ 0`). All leaf hypotheses are passed through. -/
theorem tieCover_0536 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {d1 d2 : ℝ³} {μ a δ γ p4 q4 : ℝ}
    (hd1 : d1 = γ • (x 2 - x 5) + δ • (x 3 - x 5)) (hδ : 0 < δ)
    (hb26 : bT26 x = μ • ((a - 1) • (x 2 - x 5) - a • (x 0 - x 5))) (hμ : 0 < μ) (ha : 1 < a)
    (hx4 : x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5)) (hp4 : 0 < p4) (hq4 : 0 ≤ q4)
    (tie : ⟪x 2 - x 5, x 0 - x 5⟫ = 0)
    (hW : ¬ (⟪x 2 - x 5, x 3 - x 5⟫ = 0 ∧ ⟪x 0 - x 5, x 3 - x 5⟫ = 0))
    -- T25 leaf hypotheses
    (h3 : 0 < ⟪F.N 3, bT25 x⟫) (h4 : 0 < ⟪F.N 4, bT25 x⟫) (h8 : 0 < ⟪F.N 8, bT25 x⟫)
    (h1 : ⟪F.N 1, bT25 x⟫ < 0) (h7 : ⟪F.N 7, bT25 x⟫ < 0)
    (t2 : LexPos3 (-⟪F.N 2, bT25 x⟫) (-⟪F.N 2, d1⟫) (-⟪F.N 2, d2⟫))
    (t6 : LexPos3 (-⟪F.N 6, bT25 x⟫) (-⟪F.N 6, d1⟫) (-⟪F.N 6, d2⟫))
    (f0356 : FrontDet (x 0) (x 3) (x 5) (x 6) (bT25 x))
    -- T26 leaf hypotheses
    (g6 : 0 < ⟪F.N 6, bT26 x⟫) (g7 : 0 < ⟪F.N 7, bT26 x⟫) (g8 : 0 < ⟪F.N 8, bT26 x⟫)
    (g3 : ⟪F.N 3, bT26 x⟫ < 0) (g4 : ⟪F.N 4, bT26 x⟫ < 0)
    (f2354 : FrontDet (x 2) (x 3) (x 5) (x 4) (bT26 x))
    (f2356 : FrontDet (x 2) (x 3) (x 5) (x 6) (bT26 x))
    (f2456 : FrontDet (x 2) (x 4) (x 5) (x 6) (bT26 x))
    (f3624 : FrontDet (x 3) (x 6) (x 2) (x 4) (bT26 x))
    (f3654 : FrontDet (x 3) (x 6) (x 5) (x 4) (bT26 x)) :
    LexAny F := by
  by_cases hc : GenQuad.LexClause (x 5) (x 6) (x 0) (x 3) (bT25 x) d1 d2
  · exact lexAny_T25_0536_tilt F d1 d2 h3 h4 h8 h1 h7 t2 t6 f0356 hc
  · simp only [GenQuad.LexClause, GenQuad.LexClause, LexLt3, not_or] at hc
    obtain ⟨hc1, hc2, -, -⟩ := hc
    have n1 := notLexPos3 hc1
    have n2 := notLexPos3 hc2
    have hb25 : bT25 x = x 5 - x 2 := rfl
    have hinj := inj_of_fac F
    have hne2 : x 2 - x 5 ≠ 0 := sub_ne_zero.2 (fun h => absurd (hinj h) (by decide))
    have hne0 : x 0 - x 5 ≠ 0 := sub_ne_zero.2 (fun h => absurd (hinj h) (by decide))
    have E11 : 0 < ⟪x 2 - x 5, x 2 - x 5⟫ := real_inner_self_pos.mpr hne2
    have E22 : 0 < ⟪x 0 - x 5, x 0 - x 5⟫ := real_inner_self_pos.mpr hne0
    have hA : 0 ≤ ⟪x 3 - x 5, bT25 x⟫ := by
      have := n2.1; rw [inner_sub_left]; linarith
    have hz0 : ⟪x 5, bT25 x⟫ - ⟪x 0, bT25 x⟫ = 0 := by
      rw [← inner_sub_left, hb25]
      have : x 5 - x 0 = -(x 0 - x 5) := by abel
      have h25 : x 5 - x 2 = -(x 2 - x 5) := by abel
      rw [this, h25, inner_neg_left, inner_neg_right, real_inner_comm, tie]; simp
    have hB : 0 ≤ ⟪x 0 - x 5, d1⟫ := by
      have := n1.2 hz0
      rw [← inner_sub_left] at this
      have h2 : x 5 - x 0 = -(x 0 - x 5) := by abel
      rw [h2, inner_neg_left] at this; linarith
    have idI := identityI hb25 hd1 hb26 tie
    have hK1 : 0 < μ * δ * (a - 1) := mul_pos (mul_pos hμ hδ) (by linarith)
    have hK2 : 0 < μ * a := mul_pos hμ (by linarith)
    have caseI : 0 ≤ ⟪x 3 - x 5, bT26 x⟫ → False := by
      intro hC
      have hA0' : ⟪x 3 - x 5, bT25 x⟫ = 0 := by
        by_contra hne
        have h := mul_pos hK1 (lt_of_le_of_ne hA (Ne.symm hne))
        have := mul_nonneg hK2.le hB; have := mul_nonneg hδ.le hC
        linarith
      have hB0 : ⟪x 0 - x 5, d1⟫ = 0 := by
        by_contra hne
        have h := mul_pos hK2 (lt_of_le_of_ne hB (Ne.symm hne))
        have := mul_nonneg hK1.le hA; have := mul_nonneg hδ.le hC
        linarith
      have hA0 : ⟪x 3 - x 5, x 5 - x 2⟫ = 0 := hA0'
      apply hW
      have h25 : x 5 - x 2 = -(x 2 - x 5) := by abel
      rw [h25] at hA0
      rw [hd1] at hB0
      have c13 := real_inner_comm (x 2 - x 5) (x 3 - x 5)
      have c23 := real_inner_comm (x 0 - x 5) (x 3 - x 5)
      have c12 := real_inner_comm (x 2 - x 5) (x 0 - x 5)
      simp only [inner_neg_right, inner_add_right, inner_smul_right] at hA0 hB0
      refine ⟨by linarith, ?_⟩
      have c12' : ⟪x 0 - x 5, x 2 - x 5⟫ = 0 := by rw [c12]; exact tie
      rw [c12'] at hB0
      have : δ * ⟪x 0 - x 5, x 3 - x 5⟫ = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hδ.ne'
      · exact h
    have zd : ∀ v w : Fin 7, z x (bT26 x) v - z x (bT26 x) w = ⟪x v - x w, bT26 x⟫ := zdiff x (bT26 x)
    refine lexAny_T26 F g6 g7 g8 g3 g4 f2354 f2356 f2456 f3624 f3654 ?_ ?_ ?_ ?_ ?_
    · intro hM
      rw [max_le_iff, le_min_iff, le_min_iff] at hM
      exact caseI (by have := zd 3 5; linarith [hM.1.2])
    · intro hM
      rw [max_le_iff, le_min_iff, le_min_iff] at hM
      exact caseI (by have := zd 3 5; linarith [hM.1.2])
    · intro hM
      rw [max_le_iff, le_min_iff, le_min_iff] at hM
      have hD : 0 ≤ ⟪x 4 - x 5, bT26 x⟫ := by have := zd 4 5; linarith [hM.1.2]
      have := identityT24 hb25 hd1 hb26 hx4 tie
      have := mul_nonneg hδ.le hD
      have := mul_nonneg hq4 (add_nonneg (mul_nonneg hK1.le hA) (mul_nonneg hK2.le hB))
      have := mul_pos (mul_pos (mul_pos (mul_pos hδ hp4) hμ) (by linarith : (0:ℝ) < a)) E22
      nlinarith
    · intro hM
      rw [max_le_iff, le_min_iff, le_min_iff] at hM
      have hD : 0 ≤ ⟪x 3 - x 2, bT26 x⟫ := by have := zd 3 2; linarith [hM.1.1]
      have := identityT36 hb25 hd1 hb26 tie
      have := mul_nonneg hδ.le hD
      have := mul_nonneg hK1.le hA
      have := mul_nonneg hK2.le hB
      have := mul_pos (mul_pos (mul_pos hδ hμ) (by linarith : (0:ℝ) < a - 1)) E11
      nlinarith
    · intro hM
      rw [max_le_iff, le_min_iff, le_min_iff] at hM
      exact caseI (by have := zd 3 5; linarith [hM.1.2])


/-! ## Part 2 (TieCert2): level-0/1 extraction, T26 kill, tilted leaves 01635 / 05346, tie covers -/

theorem nlt3 {a b c a' b' c' : ℝ} (h : ¬ LexLt3 (a, b, c) (a', b', c')) :
    a' ≤ a ∧ (a' = a → b' ≤ b) := by
  have := notLexPos3 (show ¬ LexPos3 (a' - a) (b' - b) (c' - c) from h)
  exact ⟨by linarith [this.1], fun e => by have := this.2 (by linarith); linarith⟩

/-- Failure of a lexicographic clause: the four lexicographic non-inequalities, first two levels. -/
theorem notClause {p q r s b d1 d2 : ℝ³} (h : ¬ GenQuad.LexClause p q r s b d1 d2) :
    (⟪p, b⟫ ≤ ⟪r, b⟫ ∧ (⟪p, b⟫ = ⟪r, b⟫ → ⟪p, d1⟫ ≤ ⟪r, d1⟫)) ∧
    (⟪p, b⟫ ≤ ⟪s, b⟫ ∧ (⟪p, b⟫ = ⟪s, b⟫ → ⟪p, d1⟫ ≤ ⟪s, d1⟫)) ∧
    (⟪q, b⟫ ≤ ⟪r, b⟫ ∧ (⟪q, b⟫ = ⟪r, b⟫ → ⟪q, d1⟫ ≤ ⟪r, d1⟫)) ∧
    (⟪q, b⟫ ≤ ⟪s, b⟫ ∧ (⟪q, b⟫ = ⟪s, b⟫ → ⟪q, d1⟫ ≤ ⟪s, d1⟫)) := by
  simp only [GenQuad.LexClause, not_or] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨nlt3 h1, nlt3 h2, nlt3 h3, nlt3 h4⟩

/-- `z0 = z5` at T25 on the tie, so `z0 >= z5` lexicographically gives `<x0-x5,d1> >= 0`. -/
theorem levelB {x : Fin 7 → ℝ³} {b25 d1 : ℝ³} (hb25 : b25 = x 5 - x 2)
    (tie : ⟪x 2 - x 5, x 0 - x 5⟫ = 0)
    (h0 : ⟪x 5, b25⟫ ≤ ⟪x 0, b25⟫) (h1 : ⟪x 5, b25⟫ = ⟪x 0, b25⟫ → ⟪x 5, d1⟫ ≤ ⟪x 0, d1⟫) :
    0 ≤ ⟪x 0 - x 5, d1⟫ := by
  have hz0 : ⟪x 5, b25⟫ - ⟪x 0, b25⟫ = 0 := by
    rw [← inner_sub_left, hb25]
    have : x 5 - x 0 = -(x 0 - x 5) := by abel
    have h25 : x 5 - x 2 = -(x 2 - x 5) := by abel
    rw [this, h25, inner_neg_left, inner_neg_right, real_inner_comm, tie]; simp
  have := h1 (by linarith)
  rw [inner_sub_left]; linarith

theorem t26_vals {x : Fin 7 → ℝ³} {b26 : ℝ³} {μ a : ℝ}
    (hb26 : b26 = μ • ((a - 1) • (x 2 - x 5) - a • (x 0 - x 5)))
    (tie : ⟪x 2 - x 5, x 0 - x 5⟫ = 0) :
    ⟪x 0 - x 5, b26⟫ = -(μ * a) * ⟪x 0 - x 5, x 0 - x 5⟫ ∧
    ⟪x 2 - x 5, b26⟫ = μ * (a - 1) * ⟪x 2 - x 5, x 2 - x 5⟫ := by
  have c12 : ⟪x 0 - x 5, x 2 - x 5⟫ = 0 := by rw [real_inner_comm]; exact tie
  subst hb26
  simp only [inner_smul_right, inner_sub_right, tie, c12]
  constructor <;> ring

/-- If `z3 < z5` at T26 then the other four T26 depth comparisons that the clauses need also fail. -/
theorem t26_dead {x : Fin 7 → ℝ³} {b26 : ℝ³} {μ a p4 q4 : ℝ}
    (hb26 : b26 = μ • ((a - 1) • (x 2 - x 5) - a • (x 0 - x 5))) (hμ : 0 < μ) (ha : 1 < a)
    (hx4 : x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5)) (hp4 : 0 < p4) (hq4 : 0 ≤ q4)
    (tie : ⟪x 2 - x 5, x 0 - x 5⟫ = 0)
    (E11 : 0 < ⟪x 2 - x 5, x 2 - x 5⟫) (E22 : 0 < ⟪x 0 - x 5, x 0 - x 5⟫)
    (hC : ⟪x 3 - x 5, b26⟫ < 0) :
    ⟪x 4 - x 5, b26⟫ < 0 ∧ ⟪x 3 - x 2, b26⟫ < 0 := by
  obtain ⟨v0, v2⟩ := t26_vals hb26 tie
  have h4 : ⟪x 4 - x 5, b26⟫ = p4 * ⟪x 0 - x 5, b26⟫ + q4 * ⟪x 3 - x 5, b26⟫ := by
    rw [hx4, inner_add_left, inner_smul_left, inner_smul_left]; simp
  have h32 : ⟪x 3 - x 2, b26⟫ = ⟪x 3 - x 5, b26⟫ - ⟪x 2 - x 5, b26⟫ := by
    rw [← inner_sub_left]; congr 1; abel
  have ha0 : (0:ℝ) < a := by linarith
  have t1 : 0 < p4 * (μ * a * ⟪x 0 - x 5, x 0 - x 5⟫) := mul_pos hp4 (mul_pos (mul_pos hμ ha0) E22)
  have t2 : 0 < μ * (a - 1) * ⟪x 2 - x 5, x 2 - x 5⟫ :=
    mul_pos (mul_pos hμ (by linarith)) E11
  constructor
  · rw [h4, v0]; nlinarith [mul_nonneg hq4 (neg_nonneg.2 hC.le)]
  · rw [h32, v2]; linarith

/-- Lemma T, dichotomy: `z3 >= z5` at T25 and `<x0-x5,d1> >= 0` force `z3 < z5` at T26 or the sub-tie W. -/
theorem T_dich {x : Fin 7 → ℝ³} {b25 d1 b26 : ℝ³} {μ a δ γ : ℝ}
    (hb25 : b25 = x 5 - x 2) (hd1 : d1 = γ • (x 2 - x 5) + δ • (x 3 - x 5))
    (hb26 : b26 = μ • ((a - 1) • (x 2 - x 5) - a • (x 0 - x 5)))
    (tie : ⟪x 2 - x 5, x 0 - x 5⟫ = 0) (hμ : 0 < μ) (hδ : 0 < δ) (ha : 1 < a)
    (hA : 0 ≤ ⟪x 3 - x 5, b25⟫) (hB : 0 ≤ ⟪x 0 - x 5, d1⟫) :
    ⟪x 3 - x 5, b26⟫ < 0 ∨ (⟪x 2 - x 5, x 3 - x 5⟫ = 0 ∧ ⟪x 0 - x 5, x 3 - x 5⟫ = 0) := by
  rcases lt_or_ge ⟪x 3 - x 5, b26⟫ 0 with h | hC
  · exact Or.inl h
  right
  have idI := identityI hb25 hd1 hb26 tie
  have hK1 : 0 < μ * δ * (a - 1) := mul_pos (mul_pos hμ hδ) (by linarith)
  have hK2 : 0 < μ * a := mul_pos hμ (by linarith)
  have hA0' : ⟪x 3 - x 5, b25⟫ = 0 := by
    by_contra hne
    have h := mul_pos hK1 (lt_of_le_of_ne hA (Ne.symm hne))
    have := mul_nonneg hK2.le hB; have := mul_nonneg hδ.le hC
    linarith
  have hB0 : ⟪x 0 - x 5, d1⟫ = 0 := by
    by_contra hne
    have h := mul_pos hK2 (lt_of_le_of_ne hB (Ne.symm hne))
    have := mul_nonneg hK1.le hA; have := mul_nonneg hδ.le hC
    linarith
  have h25 : x 5 - x 2 = -(x 2 - x 5) := by abel
  rw [hb25, h25] at hA0'
  rw [hd1] at hB0
  have c13 := real_inner_comm (x 2 - x 5) (x 3 - x 5)
  have c12 : ⟪x 0 - x 5, x 2 - x 5⟫ = 0 := by rw [real_inner_comm]; exact tie
  simp only [inner_neg_right, inner_add_right, inner_smul_right] at hA0' hB0
  refine ⟨by linarith, ?_⟩
  rw [c12] at hB0
  have : δ * ⟪x 0 - x 5, x 3 - x 5⟫ = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h hδ.ne'
  · exact h

/-- Lemma T6 (strict): `z6 >= z5` at T25 and `<x0-x5,d1> >= 0` force `z3 < z5` at T26. -/
theorem T6_strict {x : Fin 7 → ℝ³} {b25 d1 b26 : ℝ³} {μ a δ γ c61 c62 c63 : ℝ}
    (hb25 : b25 = x 5 - x 2) (hd1 : d1 = γ • (x 2 - x 5) + δ • (x 3 - x 5))
    (hb26 : b26 = μ • ((a - 1) • (x 2 - x 5) - a • (x 0 - x 5)))
    (hx6 : x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5))
    (tie : ⟪x 2 - x 5, x 0 - x 5⟫ = 0) (hμ : 0 < μ) (hδ : 0 < δ) (ha : 1 < a)
    (hc61 : 0 < c61) (hc63 : 0 < c63) (E11 : 0 < ⟪x 2 - x 5, x 2 - x 5⟫)
    (hA : 0 ≤ ⟪x 6 - x 5, b25⟫) (hB : 0 ≤ ⟪x 0 - x 5, d1⟫) :
    ⟪x 3 - x 5, b26⟫ < 0 := by
  by_contra hC
  push Not at hC
  have id6 := identityT6 hb25 hd1 hb26 hx6 tie
  have hK1 : 0 < μ * δ * (a - 1) := mul_pos (mul_pos hμ hδ) (by linarith)
  have hK2 : 0 < μ * a := mul_pos hμ (by linarith)
  have e1 := mul_nonneg hK1.le hA
  have e2 := mul_nonneg hc63.le (add_nonneg (mul_nonneg hK2.le hB) (mul_nonneg hδ.le hC))
  have e3 := mul_pos (mul_pos hK1 hc61) E11
  nlinarith

/-- Line `45>36` (rim 05346): `(q4 - 1)(z5 - z3) + (z4 - z3) = 0` at T25. -/
theorem line45_36 {x : Fin 7 → ℝ³} {b25 : ℝ³} {p4 q4 : ℝ}
    (hb25 : b25 = x 5 - x 2)
    (hx4 : x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5))
    (tie : ⟪x 2 - x 5, x 0 - x 5⟫ = 0) :
    (q4 - 1) * ⟪x 5 - x 3, b25⟫ + ⟪x 4 - x 3, b25⟫ = 0 := by
  have h25 : x 5 - x 2 = -(x 2 - x 5) := by abel
  have h53 : x 5 - x 3 = -(x 3 - x 5) := by abel
  have h43 : x 4 - x 3 = (x 4 - x 5) - (x 3 - x 5) := by abel
  subst hb25
  rw [h25, h53, h43, hx4]
  generalize x 2 - x 5 = e1 at *
  generalize x 0 - x 5 = e2 at *
  generalize x 3 - x 5 = e3 at *
  simp only [inner_add_left, inner_sub_left, inner_smul_left, inner_neg_right, inner_neg_left,
    real_inner_comm e1 e2, real_inner_comm e1 e3] at *
  simp only [conj_trivial]
  linear_combination (-p4) * tie

/-- `z0 - z3 = E13` at T25 on the tie. -/
theorem z03_E13 {x : Fin 7 → ℝ³} {b25 : ℝ³} (hb25 : b25 = x 5 - x 2)
    (tie : ⟪x 2 - x 5, x 0 - x 5⟫ = 0) :
    ⟪x 0 - x 3, b25⟫ = ⟪x 2 - x 5, x 3 - x 5⟫ := by
  have h25 : x 5 - x 2 = -(x 2 - x 5) := by abel
  have h03 : x 0 - x 3 = (x 0 - x 5) - (x 3 - x 5) := by abel
  subst hb25
  rw [h25, h03]
  generalize x 2 - x 5 = e1 at *
  generalize x 0 - x 5 = e2 at *
  generalize x 3 - x 5 = e3 at *
  simp only [inner_sub_left, inner_neg_right, real_inner_comm e1 e2, real_inner_comm e1 e3] at *
  linear_combination (-1) * tie

/-- `z5 - z3 = E13` at T25. -/
theorem z53_E13 {x : Fin 7 → ℝ³} {b25 : ℝ³} (hb25 : b25 = x 5 - x 2) :
    ⟪x 5 - x 3, b25⟫ = ⟪x 2 - x 5, x 3 - x 5⟫ := by
  have h25 : x 5 - x 2 = -(x 2 - x 5) := by abel
  have h53 : x 5 - x 3 = -(x 3 - x 5) := by abel
  subst hb25
  rw [h25, h53, inner_neg_left, inner_neg_right, real_inner_comm]; simp

/-- `z4 - z5 = q4 (z3 - z5)` at T25 on the tie. -/
theorem z45_q4 {x : Fin 7 → ℝ³} {b25 : ℝ³} {p4 q4 : ℝ} (hb25 : b25 = x 5 - x 2)
    (hx4 : x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5))
    (tie : ⟪x 2 - x 5, x 0 - x 5⟫ = 0) :
    ⟪x 4 - x 5, b25⟫ = q4 * ⟪x 3 - x 5, b25⟫ := by
  have h25 : x 5 - x 2 = -(x 2 - x 5) := by abel
  have c12 : ⟪x 0 - x 5, x 2 - x 5⟫ = 0 := by rw [real_inner_comm]; exact tie
  subst hb25
  rw [hx4, h25, inner_add_left, inner_smul_left, inner_smul_left]
  simp only [inner_neg_right, c12]; simp

/-! ### Tilted leaves -/

private def c25b' : ZMod 5 → Fin 7 := ![0, 1, 6, 3, 5]
private theorem c25b'_inj : Function.Injective c25b' := by decide
private theorem c25b'_cyc : S0xCycUD s0x_S24 c25b' {1, 3, 8} {0, 2, 5, 6, 7} := by decide

/-- `lexAny_T25_01635` with arbitrary tilt `(d1, d2)` (facets 2, 6 as `LexPos3` hypotheses) and the five
full lexicographic clauses. -/
theorem lexAny_T25_01635_tilt {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (d1 d2 : ℝ³)
    (h1 : 0 < ⟪F.N 1, bT25 x⟫) (h3 : 0 < ⟪F.N 3, bT25 x⟫) (h8 : 0 < ⟪F.N 8, bT25 x⟫)
    (h0 : ⟪F.N 0, bT25 x⟫ < 0) (h5 : ⟪F.N 5, bT25 x⟫ < 0) (h7 : ⟪F.N 7, bT25 x⟫ < 0)
    (t2 : LexPos3 (-⟪F.N 2, bT25 x⟫) (-⟪F.N 2, d1⟫) (-⟪F.N 2, d2⟫))
    (t6 : LexPos3 (-⟪F.N 6, bT25 x⟫) (-⟪F.N 6, d1⟫) (-⟪F.N 6, d2⟫))
    (f0613 : FrontDet (x 0) (x 6) (x 1) (x 3) (bT25 x))
    (f0615 : FrontDet (x 0) (x 6) (x 1) (x 5) (bT25 x))
    (f0315 : FrontDet (x 0) (x 3) (x 1) (x 5) (bT25 x))
    (f0365 : FrontDet (x 0) (x 3) (x 6) (x 5) (bT25 x))
    (f6513 : FrontDet (x 6) (x 5) (x 1) (x 3) (bT25 x))
    (m0613 : GenQuad.LexClause (x 1) (x 3) (x 0) (x 6) (bT25 x) d1 d2)
    (m0615 : GenQuad.LexClause (x 1) (x 5) (x 0) (x 6) (bT25 x) d1 d2)
    (m0315 : GenQuad.LexClause (x 1) (x 5) (x 0) (x 3) (bT25 x) d1 d2)
    (m0365 : GenQuad.LexClause (x 6) (x 5) (x 0) (x 3) (bT25 x) d1 d2)
    (m6513 : GenQuad.LexClause (x 1) (x 3) (x 6) (x 5) (bT25 x) d1 d2) :
    LexAny F := by
  have hb : bT25 x ≠ 0 := fun h => by rw [h, inner_zero_right] at h1; exact lt_irrefl _ h1
  refine GenQuad.lexAny_of_clauses F (k := 5) (by norm_num) c25b'_inj c25b'_cyc (bT25 x) d1 d2 ?_ ?_ ?_
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
  · exact GenQuad.clauses_five (p := fun i => x (c25b' i)) (b := bT25 x) (d1 := d1) (d2 := d2)
      m0613 (lexClause_of_det hb f0613)
      m0615 (lexClause_of_det hb f0615)
      m0315 (lexClause_of_det hb f0315)
      m0365 (lexClause_of_det hb f0365)
      (lexClause_of_det hb f6513) m6513

private def c25c' : ZMod 5 → Fin 7 := ![0, 5, 3, 4, 6]
private theorem c25c'_inj : Function.Injective c25c' := by decide
private theorem c25c'_cyc : S0xCycUD s0x_S24 c25c' {3, 4} {1, 2, 6, 8} := by decide

/-- `lexAny_T25_05346_tilt` with `LexPos3` on `-⟪F.N 1, bT25 x⟫` (covering `⟪F.N 1, bT25 x⟫ = 0`). -/
theorem lexAny_T25_05346_tilt_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (d1 d2 : ℝ³)
    (hdet : Split.det3 (bT25 x) d1 d2 ≠ 0)
    (h3 : 0 < ⟪F.N 3, bT25 x⟫) (h4 : 0 < ⟪F.N 4, bT25 x⟫)
    (t1 : LexPos3 (-⟪F.N 1, bT25 x⟫) (-⟪F.N 1, d1⟫) (-⟪F.N 1, d2⟫))
    (h8 : ⟪F.N 8, bT25 x⟫ < 0)
    (t2 : LexPos3 (-⟪F.N 2, bT25 x⟫) (-⟪F.N 2, d1⟫) (-⟪F.N 2, d2⟫))
    (t6 : LexPos3 (-⟪F.N 6, bT25 x⟫) (-⟪F.N 6, d1⟫) (-⟪F.N 6, d2⟫))
    (hX : GenQuad.CrossOf (x 0) (x 3) (x 5) (x 4))
    (f0356 : FrontDet (x 0) (x 3) (x 5) (x 6) (bT25 x))
    (f0456 : FrontDet (x 0) (x 4) (x 5) (x 6) (bT25 x))
    (f0436 : FrontDet (x 0) (x 4) (x 3) (x 6) (bT25 x))
    (f5436 : FrontDet (x 5) (x 4) (x 3) (x 6) (bT25 x))
    (m0356 : GenQuad.LexClause (x 5) (x 6) (x 0) (x 3) (bT25 x) d1 d2)
    (m0456 : GenQuad.LexClause (x 5) (x 6) (x 0) (x 4) (bT25 x) d1 d2)
    (m0436 : GenQuad.LexClause (x 3) (x 6) (x 0) (x 4) (bT25 x) d1 d2)
    (m5436 : GenQuad.LexClause (x 3) (x 6) (x 5) (x 4) (bT25 x) d1 d2) :
    LexAny F := by
  have hb : bT25 x ≠ 0 := fun h => by rw [h, inner_zero_right] at h3; exact lt_irrefl _ h3
  have hinj := inj_of_fac F
  have h05 : x 0 ≠ x 5 := fun h => absurd (hinj h) (by decide)
  obtain ⟨cB, cA⟩ := GenQuad.lexClause_of_crossOf hX hdet h05
  refine GenQuad.lexAny_of_clauses F (k := 5) (by norm_num) c25c'_inj c25c'_cyc (bT25 x) d1 d2 ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact Or.inl h3
    · exact Or.inl h4
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact t1
    · exact t2
    · exact t6
    · exact Or.inl (by linarith)
  · exact GenQuad.clauses_five (p := fun i => x (c25c' i)) (b := bT25 x) (d1 := d1) (d2 := d2)
      cA cB m0356 (lexClause_of_det hb f0356) m0456 (lexClause_of_det hb f0456)
      m0436 (lexClause_of_det hb f0436) m5436 (lexClause_of_det hb f5436)

/-- `lexAny_T25_05346` with arbitrary tilt `(d1, d2)` (`hdet`: `(bT25, d1, d2)` a basis) and full clauses. -/
theorem lexAny_T25_05346_tilt {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (d1 d2 : ℝ³)
    (hdet : Split.det3 (bT25 x) d1 d2 ≠ 0)
    (h3 : 0 < ⟪F.N 3, bT25 x⟫) (h4 : 0 < ⟪F.N 4, bT25 x⟫)
    (h1 : ⟪F.N 1, bT25 x⟫ < 0) (h8 : ⟪F.N 8, bT25 x⟫ < 0)
    (t2 : LexPos3 (-⟪F.N 2, bT25 x⟫) (-⟪F.N 2, d1⟫) (-⟪F.N 2, d2⟫))
    (t6 : LexPos3 (-⟪F.N 6, bT25 x⟫) (-⟪F.N 6, d1⟫) (-⟪F.N 6, d2⟫))
    (hX : GenQuad.CrossOf (x 0) (x 3) (x 5) (x 4))
    (f0356 : FrontDet (x 0) (x 3) (x 5) (x 6) (bT25 x))
    (f0456 : FrontDet (x 0) (x 4) (x 5) (x 6) (bT25 x))
    (f0436 : FrontDet (x 0) (x 4) (x 3) (x 6) (bT25 x))
    (f5436 : FrontDet (x 5) (x 4) (x 3) (x 6) (bT25 x))
    (m0356 : GenQuad.LexClause (x 5) (x 6) (x 0) (x 3) (bT25 x) d1 d2)
    (m0456 : GenQuad.LexClause (x 5) (x 6) (x 0) (x 4) (bT25 x) d1 d2)
    (m0436 : GenQuad.LexClause (x 3) (x 6) (x 0) (x 4) (bT25 x) d1 d2)
    (m5436 : GenQuad.LexClause (x 3) (x 6) (x 5) (x 4) (bT25 x) d1 d2) :
    LexAny F :=
  lexAny_T25_05346_tilt_lex F d1 d2 hdet h3 h4 (Or.inl (by linarith)) h8 t2 t6 hX
    f0356 f0456 f0436 f5436 m0356 m0456 m0436 m5436


/-! ### T26 kill and the tie covers -/

/-- If `z3 < z5` at T26 (and the frame facts hold) then the T26 leaf applies: all five clauses hold. -/
theorem kill26 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {μ a p4 q4 : ℝ}
    (hb26 : bT26 x = μ • ((a - 1) • (x 2 - x 5) - a • (x 0 - x 5))) (hμ : 0 < μ) (ha : 1 < a)
    (hx4 : x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5)) (hp4 : 0 < p4) (hq4 : 0 ≤ q4)
    (tie : ⟪x 2 - x 5, x 0 - x 5⟫ = 0)
    (g6 : 0 < ⟪F.N 6, bT26 x⟫) (g7 : 0 < ⟪F.N 7, bT26 x⟫) (g8 : 0 < ⟪F.N 8, bT26 x⟫)
    (g3 : ⟪F.N 3, bT26 x⟫ < 0) (g4 : ⟪F.N 4, bT26 x⟫ < 0)
    (f2354 : FrontDet (x 2) (x 3) (x 5) (x 4) (bT26 x))
    (f2356 : FrontDet (x 2) (x 3) (x 5) (x 6) (bT26 x))
    (f2456 : FrontDet (x 2) (x 4) (x 5) (x 6) (bT26 x))
    (f3624 : FrontDet (x 3) (x 6) (x 2) (x 4) (bT26 x))
    (f3654 : FrontDet (x 3) (x 6) (x 5) (x 4) (bT26 x))
    (hC : ⟪x 3 - x 5, bT26 x⟫ < 0) : LexAny F := by
  have hinj := inj_of_fac F
  have hne2 : x 2 - x 5 ≠ 0 := sub_ne_zero.2 (fun h => absurd (hinj h) (by decide))
  have hne0 : x 0 - x 5 ≠ 0 := sub_ne_zero.2 (fun h => absurd (hinj h) (by decide))
  have E11 : 0 < ⟪x 2 - x 5, x 2 - x 5⟫ := real_inner_self_pos.mpr hne2
  have E22 : 0 < ⟪x 0 - x 5, x 0 - x 5⟫ := real_inner_self_pos.mpr hne0
  obtain ⟨h4, h32⟩ := t26_dead hb26 hμ ha hx4 hp4 hq4 tie E11 E22 hC
  have zd : ∀ v w : Fin 7, z x (bT26 x) v - z x (bT26 x) w = ⟪x v - x w, bT26 x⟫ := zdiff x (bT26 x)
  have := zd 3 5; have := zd 4 5; have := zd 3 2
  refine lexAny_T26 F g6 g7 g8 g3 g4 f2354 f2356 f2456 f3624 f3654 ?_ ?_ ?_ ?_ ?_ <;>
  · intro hM
    simp only [max_le_iff, le_min_iff] at hM
    obtain ⟨⟨_, _⟩, _, _⟩ := hM
    linarith

/-- **Tie cover, rim 01635** (TIECERT 3.4). On the tie, outside `W = {E13 = E23 = 0}`: T25 (rim 01635, tilt
`(d1, d2)`) or T26 gives `LexAny`. Frame: `x6 - x5 = c61 e1 + c62 e2 + c63 e3`, `c61 > 0`, `c63 ≥ 1`. -/
theorem tieCover_01635 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {d1 d2 : ℝ³}
    {μ a δ γ p4 q4 c61 c62 c63 : ℝ}
    (hd1 : d1 = γ • (x 2 - x 5) + δ • (x 3 - x 5)) (hδ : 0 < δ)
    (hb26 : bT26 x = μ • ((a - 1) • (x 2 - x 5) - a • (x 0 - x 5))) (hμ : 0 < μ) (ha : 1 < a)
    (hx4 : x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5)) (hp4 : 0 < p4) (hq4 : 0 ≤ q4)
    (hx6 : x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5))
    (hc61 : 0 < c61) (hc63 : 1 ≤ c63)
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
    (f6513 : FrontDet (x 6) (x 5) (x 1) (x 3) (bT25 x))
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
  have iS : ∀ u v w : Fin 7, ⟪x u - x v, bT25 x⟫ = ⟪x u, bT25 x⟫ - ⟪x v, bT25 x⟫ :=
    fun u v w => inner_sub_left _ _ _
  by_cases k1 : GenQuad.LexClause (x 1) (x 3) (x 0) (x 6) (bT25 x) d1 d2
  swap
  · exfalso
    obtain ⟨-, -, ⟨u3, -⟩, ⟨u4, -⟩⟩ := notClause k1
    have l := line06_13 hb25 hx6 tie
    have e1 := iS 0 3 0; have e2 := iS 6 3 0
    nlinarith [mul_nonneg (sub_nonneg.2 hc63) (sub_nonneg.2 u3), mul_pos hc61 E11]
  by_cases k2 : GenQuad.LexClause (x 1) (x 3) (x 6) (x 5) (bT25 x) d1 d2
  swap
  · exfalso
    obtain ⟨-, -, ⟨u3, -⟩, ⟨u4, -⟩⟩ := notClause k2
    have l := line56_13 hb25 hx6 tie
    have e1 := iS 5 3 0; have e2 := iS 6 3 0
    nlinarith [mul_nonneg (sub_nonneg.2 hc63) (sub_nonneg.2 u4), mul_pos hc61 E11]
  by_cases k3 : GenQuad.LexClause (x 1) (x 5) (x 0) (x 3) (bT25 x) d1 d2
  swap
  · obtain ⟨-, -, ⟨u1, u1'⟩, ⟨u2, -⟩⟩ := notClause k3
    have hB := levelB hb25 tie u1 u1'
    have hA : 0 ≤ ⟪x 3 - x 5, bT25 x⟫ := by rw [iS 3 5 0]; linarith
    rcases T_dich hb25 hd1 hb26 tie hμ hδ ha hA hB with h | h
    · exact kill h
    · exact absurd h hW
  by_cases k4 : GenQuad.LexClause (x 6) (x 5) (x 0) (x 3) (bT25 x) d1 d2
  swap
  · obtain ⟨-, -, ⟨u1, u1'⟩, ⟨u2, -⟩⟩ := notClause k4
    have hB := levelB hb25 tie u1 u1'
    have hA : 0 ≤ ⟪x 3 - x 5, bT25 x⟫ := by rw [iS 3 5 0]; linarith
    rcases T_dich hb25 hd1 hb26 tie hμ hδ ha hA hB with h | h
    · exact kill h
    · exact absurd h hW
  by_cases k5 : GenQuad.LexClause (x 1) (x 5) (x 0) (x 6) (bT25 x) d1 d2
  swap
  · obtain ⟨-, -, ⟨u1, u1'⟩, ⟨u2, -⟩⟩ := notClause k5
    have hB := levelB hb25 tie u1 u1'
    have hA : 0 ≤ ⟪x 6 - x 5, bT25 x⟫ := by rw [iS 6 5 0]; linarith
    exact kill (T6_strict hb25 hd1 hb26 hx6 tie hμ hδ ha hc61 (by linarith) E11 hA hB)
  exact lexAny_T25_01635_tilt F d1 d2 h1 h3 h8 h0 h5 h7 t2 t6 f0613 f0615 f0315 f0365 f6513
    k1 k5 k3 k4 k2

/-- **Tie cover, rim 05346** (TIECERT 3.4). On the tie: T25 (rim 05346, tilt `(d1, d2)`) or T26 gives
`LexAny`, given the W' step `hW'`: on `E13 = 0` (the T25 tilt settles it, TIECERT W') `LexAny F`.
`q4 > 1` (`σ < 1`; the boundary `q4 = 1` is not covered). -/
theorem tieCover_05346 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {d1 d2 : ℝ³}
    {μ a δ γ p4 q4 : ℝ}
    (hd1 : d1 = γ • (x 2 - x 5) + δ • (x 3 - x 5)) (hδ : 0 < δ)
    (hb26 : bT26 x = μ • ((a - 1) • (x 2 - x 5) - a • (x 0 - x 5))) (hμ : 0 < μ) (ha : 1 < a)
    (hx4 : x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5)) (hp4 : 0 < p4) (hq4 : 1 < q4)
    (tie : ⟪x 2 - x 5, x 0 - x 5⟫ = 0)
    (hW' : ⟪x 2 - x 5, x 3 - x 5⟫ = 0 → LexAny F)
    -- T25 leaf hypotheses
    (hdet : Split.det3 (bT25 x) d1 d2 ≠ 0)
    (h3 : 0 < ⟪F.N 3, bT25 x⟫) (h4 : 0 < ⟪F.N 4, bT25 x⟫)
    (h1 : ⟪F.N 1, bT25 x⟫ < 0) (h8 : ⟪F.N 8, bT25 x⟫ < 0)
    (t2 : LexPos3 (-⟪F.N 2, bT25 x⟫) (-⟪F.N 2, d1⟫) (-⟪F.N 2, d2⟫))
    (t6 : LexPos3 (-⟪F.N 6, bT25 x⟫) (-⟪F.N 6, d1⟫) (-⟪F.N 6, d2⟫))
    (hX : GenQuad.CrossOf (x 0) (x 3) (x 5) (x 4))
    (f0356 : FrontDet (x 0) (x 3) (x 5) (x 6) (bT25 x))
    (f0456 : FrontDet (x 0) (x 4) (x 5) (x 6) (bT25 x))
    (f0436 : FrontDet (x 0) (x 4) (x 3) (x 6) (bT25 x))
    (f5436 : FrontDet (x 5) (x 4) (x 3) (x 6) (bT25 x))
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
  have kill := kill26 F hb26 hμ ha hx4 hp4 (by linarith) tie g6 g7 g8 g3 g4 f2354 f2356 f2456 f3624 f3654
  have iS : ∀ u v : Fin 7, ⟪x u - x v, bT25 x⟫ = ⟪x u, bT25 x⟫ - ⟪x v, bT25 x⟫ :=
    fun u v => inner_sub_left _ _ _
  have hq0 : 0 < q4 := by linarith
  have viaT : 0 ≤ ⟪x 3 - x 5, bT25 x⟫ → 0 ≤ ⟪x 0 - x 5, d1⟫ → LexAny F := by
    intro hA hB
    rcases T_dich hb25 hd1 hb26 tie hμ hδ ha hA hB with h | h
    · exact kill h
    · exact hW' h.1
  by_cases k1 : GenQuad.LexClause (x 5) (x 6) (x 0) (x 3) (bT25 x) d1 d2
  swap
  · obtain ⟨⟨u1, u1'⟩, ⟨u2, -⟩, -, -⟩ := notClause k1
    exact viaT (by rw [iS 3 5]; linarith) (levelB hb25 tie u1 u1')
  by_cases k2 : GenQuad.LexClause (x 5) (x 6) (x 0) (x 4) (bT25 x) d1 d2
  swap
  · obtain ⟨⟨u1, u1'⟩, ⟨u2, -⟩, -, -⟩ := notClause k2
    have hA4 : 0 ≤ ⟪x 4 - x 5, bT25 x⟫ := by rw [iS 4 5]; linarith
    have e := z45_q4 hb25 hx4 tie
    refine viaT ?_ (levelB hb25 tie u1 u1')
    by_contra hneg
    push Not at hneg
    nlinarith [mul_pos hq0 (neg_pos.2 hneg)]
  by_cases k3 : GenQuad.LexClause (x 3) (x 6) (x 0) (x 4) (bT25 x) d1 d2
  swap
  · obtain ⟨⟨u1, -⟩, ⟨u2, -⟩, -, -⟩ := notClause k3
    apply hW'
    have l := line04_36 hb25 hx4 tie
    have e1 := iS 0 3; have e2 := iS 4 3
    have h03 := z03_E13 hb25 tie
    have hz : ⟪x 0 - x 3, bT25 x⟫ = 0 := by
      by_contra hne
      have := mul_pos (sub_pos.2 hq4) (lt_of_le_of_ne (by rw [e1]; linarith) (Ne.symm hne))
      nlinarith
    rw [← h03]; exact hz
  by_cases k4 : GenQuad.LexClause (x 3) (x 6) (x 5) (x 4) (bT25 x) d1 d2
  swap
  · obtain ⟨⟨u1, -⟩, ⟨u2, -⟩, -, -⟩ := notClause k4
    apply hW'
    have l := line45_36 hb25 hx4 tie
    have e1 := iS 5 3; have e2 := iS 4 3
    have h53 := z53_E13 hb25
    have hz : ⟪x 5 - x 3, bT25 x⟫ = 0 := by
      by_contra hne
      have := mul_pos (sub_pos.2 hq4) (lt_of_le_of_ne (by rw [e1]; linarith) (Ne.symm hne))
      nlinarith
    rw [← h53]; exact hz
  exact lexAny_T25_05346_tilt F d1 d2 hdet h3 h4 h1 h8 t2 t6 hX f0356 f0456 f0436 f5436 k1 k2 k3 k4


/-! ## The W' step (rim 05346) -/


open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell
  Minimality.LexCell Minimality.Split Minimality.T24.A15 Minimality.NF29

/-- W' sub-tie, T25 clause `04>36` (rim 05346): with `E12 = E13 = 0` and `z3 <= z0` at the T25 tilt
level, `E23 >= E33 > 0`, so `z3 < z5` at T26. -/
theorem wp_k3 {x : Fin 7 → ℝ³} {d1 b26 : ℝ³} {μ a δ γ : ℝ}
    (hd1 : d1 = γ • (x 2 - x 5) + δ • (x 3 - x 5))
    (hb26 : b26 = μ • ((a - 1) • (x 2 - x 5) - a • (x 0 - x 5)))
    (tie : ⟪x 2 - x 5, x 0 - x 5⟫ = 0) (E13 : ⟪x 2 - x 5, x 3 - x 5⟫ = 0)
    (hδ : 0 < δ) (hμ : 0 < μ) (ha : 1 < a) (E33 : 0 < ⟪x 3 - x 5, x 3 - x 5⟫)
    (h : ⟪x 3, d1⟫ ≤ ⟪x 0, d1⟫) : ⟪x 3 - x 5, b26⟫ < 0 := by
  have h' : 0 ≤ ⟪(x 0 - x 5) - (x 3 - x 5), d1⟫ := by
    rw [show (x 0 - x 5) - (x 3 - x 5) = x 0 - x 3 by abel, inner_sub_left]; linarith
  subst hd1 hb26
  generalize x 2 - x 5 = e1 at *
  generalize x 0 - x 5 = e2 at *
  generalize x 3 - x 5 = e3 at *
  simp only [inner_add_right, inner_sub_right, inner_sub_left, inner_smul_right,
    real_inner_comm e1 e2, real_inner_comm e1 e3, real_inner_comm e2 e3] at *
  have h23 : ⟪e2, e3⟫ ≥ ⟪e3, e3⟫ := by
    have : 0 ≤ δ * (⟪e2, e3⟫ - ⟪e3, e3⟫) := by
      nlinarith [mul_eq_zero_of_right γ tie, mul_eq_zero_of_right γ E13, h']
    by_contra hc; push Not at hc; nlinarith [mul_pos hδ (sub_pos.2 hc)]
  have : 0 < μ * a * ⟪e2, e3⟫ := mul_pos (mul_pos hμ (by linarith)) (by linarith)
  rw [E13]; nlinarith

/-- W' sub-tie, T25 clause `45>36`: `E13 = 0` and `z3 <= z5` at the tilt level contradict `δ E33 > 0`. -/
theorem wp_k4 {x : Fin 7 → ℝ³} {d1 : ℝ³} {δ γ : ℝ}
    (hd1 : d1 = γ • (x 2 - x 5) + δ • (x 3 - x 5)) (E13 : ⟪x 2 - x 5, x 3 - x 5⟫ = 0)
    (hδ : 0 < δ) (E33 : 0 < ⟪x 3 - x 5, x 3 - x 5⟫)
    (h : ⟪x 3, d1⟫ ≤ ⟪x 5, d1⟫) : False := by
  have h' : ⟪x 3 - x 5, d1⟫ ≤ 0 := by rw [inner_sub_left]; linarith
  subst hd1
  generalize x 2 - x 5 = e1 at *
  generalize x 3 - x 5 = e3 at *
  simp only [inner_add_right, inner_smul_right, real_inner_comm e1 e3] at *
  rw [E13] at h'
  nlinarith [mul_pos hδ E33]

/-- SIGMA1 §1: on `rim 05346 / 016435` (`⟪F.N 8, bT25 x⟫ < 0`), `c63 ≥ 1` with `p4, c61, c62 > 0` implies `1 < q4`. -/
theorem q4_gt_one_of_facet8 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    {p4 q4 c61 c62 c63 : ℝ}
    (hx4 : x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5))
    (hx6 : x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5))
    (hp4 : 0 < p4) (hc61 : 0 < c61) (hc62 : 0 < c62) (hc63 : 1 ≤ c63)
    (h8 : ⟪F.N 8, bT25 x⟫ < 0) : 1 < q4 := by
  have z4 : ⟪F.N 8, x 4 - x 3⟫ = 0 := by
    rw [F.inner_sub, F.zero 8 4 (by decide), F.zero 8 3 (by decide)]; ring
  have z6 : ⟪F.N 8, x 6 - x 3⟫ = 0 := by
    rw [F.inner_sub, F.zero 8 6 (by decide), F.zero 8 3 (by decide)]; ring
  have n5 : ⟪F.N 8, x 5 - x 3⟫ < 0 := by
    rw [F.inner_sub, F.zero 8 3 (by decide)]; have := F.neg 8 5 (by decide); linarith
  have e53 : x 5 - x 3 = -(x 3 - x 5) := by abel
  have e43 : x 4 - x 3 = (x 4 - x 5) - (x 3 - x 5) := by abel
  have e63 : x 6 - x 3 = (x 6 - x 5) - (x 3 - x 5) := by abel
  have hb : bT25 x = -(x 2 - x 5) := by simp only [bT25]; abel
  rw [e53, inner_neg_right] at n5
  rw [e43, hx4] at z4
  rw [e63, hx6] at z6
  rw [hb, inner_neg_right] at h8
  generalize x 2 - x 5 = e1 at *
  generalize x 0 - x 5 = e2 at *
  generalize x 3 - x 5 = e3 at *
  simp only [inner_add_right, inner_sub_right, inner_smul_right] at z4 z6
  generalize ⟪F.N 8, e1⟫ = A at *
  generalize ⟪F.N 8, e2⟫ = B at *
  generalize ⟪F.N 8, e3⟫ = C at *
  have h1 : p4 * (c61 * A + c62 * B + (c63 - 1) * C) - c62 * (p4 * B + (q4 - 1) * C) = 0 := by
    linear_combination p4 * z6 - c62 * z4
  have h2 : c62 * (q4 - 1) * C = p4 * c61 * A + p4 * (c63 - 1) * C := by linarith
  have hpos : 0 < c62 * (q4 - 1) * C := by
    nlinarith [mul_pos hp4 hc61, mul_nonneg hp4.le (mul_nonneg (sub_nonneg.2 hc63) (by linarith : 0 ≤ C))]
  by_contra hle
  rw [not_lt] at hle
  have hle' : q4 - 1 ≤ 0 := by linarith
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (mul_pos hc62 (by linarith : 0 < C)).le hle']

/-- `tieCover_05346W` with `LexPos3` on `-⟪F.N 1, bT25 x⟫` (covering `⟪F.N 1, bT25 x⟫ = 0`). -/
theorem tieCover_05346W_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {d1 d2 : ℝ³}
    {μ a δ γ p4 q4 c61 c62 c63 : ℝ}
    (hd1 : d1 = γ • (x 2 - x 5) + δ • (x 3 - x 5)) (hδ : 0 < δ)
    (hb26 : bT26 x = μ • ((a - 1) • (x 2 - x 5) - a • (x 0 - x 5))) (hμ : 0 < μ) (ha : 1 < a)
    (hx4 : x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5)) (hp4 : 0 < p4)
    (hx6 : x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5))
    (hc61 : 0 < c61) (hc62 : 0 < c62) (hc63 : 1 ≤ c63)
    (tie : ⟪x 2 - x 5, x 0 - x 5⟫ = 0)
    (hW : ¬ (⟪x 2 - x 5, x 3 - x 5⟫ = 0 ∧ ⟪x 0 - x 5, x 3 - x 5⟫ = 0))
    -- T25 leaf hypotheses
    (hdet : Split.det3 (bT25 x) d1 d2 ≠ 0)
    (h3 : 0 < ⟪F.N 3, bT25 x⟫) (h4 : 0 < ⟪F.N 4, bT25 x⟫)
    (t1 : LexPos3 (-⟪F.N 1, bT25 x⟫) (-⟪F.N 1, d1⟫) (-⟪F.N 1, d2⟫)) (h8 : ⟪F.N 8, bT25 x⟫ < 0)
    (t2 : LexPos3 (-⟪F.N 2, bT25 x⟫) (-⟪F.N 2, d1⟫) (-⟪F.N 2, d2⟫))
    (t6 : LexPos3 (-⟪F.N 6, bT25 x⟫) (-⟪F.N 6, d1⟫) (-⟪F.N 6, d2⟫))
    (hX : GenQuad.CrossOf (x 0) (x 3) (x 5) (x 4))
    (f0356 : FrontDet (x 0) (x 3) (x 5) (x 6) (bT25 x))
    (f0456 : FrontDet (x 0) (x 4) (x 5) (x 6) (bT25 x))
    (f0436 : FrontDet (x 0) (x 4) (x 3) (x 6) (bT25 x))
    (f5436 : FrontDet (x 5) (x 4) (x 3) (x 6) (bT25 x))
    -- T26 leaf hypotheses
    (g6 : 0 < ⟪F.N 6, bT26 x⟫) (g7 : 0 < ⟪F.N 7, bT26 x⟫) (g8 : 0 < ⟪F.N 8, bT26 x⟫)
    (g3 : ⟪F.N 3, bT26 x⟫ < 0) (g4 : ⟪F.N 4, bT26 x⟫ < 0)
    (f2354 : FrontDet (x 2) (x 3) (x 5) (x 4) (bT26 x))
    (f2356 : FrontDet (x 2) (x 3) (x 5) (x 6) (bT26 x))
    (f2456 : FrontDet (x 2) (x 4) (x 5) (x 6) (bT26 x))
    (f3624 : FrontDet (x 3) (x 6) (x 2) (x 4) (bT26 x))
    (f3654 : FrontDet (x 3) (x 6) (x 5) (x 4) (bT26 x)) :
    LexAny F := by
  have hq4 : 1 < q4 := q4_gt_one_of_facet8 F hx4 hx6 hp4 hc61 hc62 hc63 h8
  have hb25 : bT25 x = x 5 - x 2 := rfl
  have kill := kill26 F hb26 hμ ha hx4 hp4 (by linarith) tie g6 g7 g8 g3 g4 f2354 f2356 f2456 f3624 f3654
  have iS : ∀ u v : Fin 7, ⟪x u - x v, bT25 x⟫ = ⟪x u, bT25 x⟫ - ⟪x v, bT25 x⟫ :=
    fun u v => inner_sub_left _ _ _
  have hq0 : 0 < q4 := by linarith
  have viaT : 0 ≤ ⟪x 3 - x 5, bT25 x⟫ → 0 ≤ ⟪x 0 - x 5, d1⟫ → LexAny F := by
    intro hA hB
    rcases T_dich hb25 hd1 hb26 tie hμ hδ ha hA hB with h | h
    · exact kill h
    · exact absurd h hW
  by_cases k1 : GenQuad.LexClause (x 5) (x 6) (x 0) (x 3) (bT25 x) d1 d2
  swap
  · obtain ⟨⟨u1, u1'⟩, ⟨u2, -⟩, -, -⟩ := notClause k1
    exact viaT (by rw [iS 3 5]; linarith) (levelB hb25 tie u1 u1')
  by_cases k2 : GenQuad.LexClause (x 5) (x 6) (x 0) (x 4) (bT25 x) d1 d2
  swap
  · obtain ⟨⟨u1, u1'⟩, ⟨u2, -⟩, -, -⟩ := notClause k2
    have hA4 : 0 ≤ ⟪x 4 - x 5, bT25 x⟫ := by rw [iS 4 5]; linarith
    have e := z45_q4 hb25 hx4 tie
    refine viaT ?_ (levelB hb25 tie u1 u1')
    by_contra hneg
    push Not at hneg
    nlinarith [mul_pos hq0 (neg_pos.2 hneg)]
  have E33 : 0 < ⟪x 3 - x 5, x 3 - x 5⟫ :=
    real_inner_self_pos.mpr (sub_ne_zero.2 (fun h => absurd (inj_of_fac F h) (by decide)))
  by_cases k3 : GenQuad.LexClause (x 3) (x 6) (x 0) (x 4) (bT25 x) d1 d2
  swap
  · obtain ⟨⟨u1, u1'⟩, ⟨u2, -⟩, -, -⟩ := notClause k3
    have l := line04_36 hb25 hx4 tie
    have e1 := iS 0 3; have e2 := iS 4 3
    have h03 := z03_E13 hb25 tie
    have hz : ⟪x 0 - x 3, bT25 x⟫ = 0 := by
      by_contra hne
      have := mul_pos (sub_pos.2 hq4) (lt_of_le_of_ne (by rw [e1]; linarith) (Ne.symm hne))
      nlinarith
    have E13 : ⟪x 2 - x 5, x 3 - x 5⟫ = 0 := by rw [← h03]; exact hz
    exact kill (wp_k3 hd1 hb26 tie E13 hδ hμ ha E33 (u1' (by rw [e1] at hz; linarith)))
  by_cases k4 : GenQuad.LexClause (x 3) (x 6) (x 5) (x 4) (bT25 x) d1 d2
  swap
  · exfalso
    obtain ⟨⟨u1, u1'⟩, ⟨u2, -⟩, -, -⟩ := notClause k4
    have l := line45_36 hb25 hx4 tie
    have e1 := iS 5 3; have e2 := iS 4 3
    have h53 := z53_E13 hb25
    have hz : ⟪x 5 - x 3, bT25 x⟫ = 0 := by
      by_contra hne
      have := mul_pos (sub_pos.2 hq4) (lt_of_le_of_ne (by rw [e1]; linarith) (Ne.symm hne))
      nlinarith
    have E13 : ⟪x 2 - x 5, x 3 - x 5⟫ = 0 := by rw [← h53]; exact hz
    exact wp_k4 hd1 E13 hδ E33 (u1' (by rw [e1] at hz; linarith))
  exact lexAny_T25_05346_tilt_lex F d1 d2 hdet h3 h4 t1 h8 t2 t6 hX f0356 f0456 f0436 f5436 k1 k2 k3 k4

theorem tieCover_05346W {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {d1 d2 : ℝ³}
    {μ a δ γ p4 q4 c61 c62 c63 : ℝ}
    (hd1 : d1 = γ • (x 2 - x 5) + δ • (x 3 - x 5)) (hδ : 0 < δ)
    (hb26 : bT26 x = μ • ((a - 1) • (x 2 - x 5) - a • (x 0 - x 5))) (hμ : 0 < μ) (ha : 1 < a)
    (hx4 : x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5)) (hp4 : 0 < p4)
    (hx6 : x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5))
    (hc61 : 0 < c61) (hc62 : 0 < c62) (hc63 : 1 ≤ c63)
    (tie : ⟪x 2 - x 5, x 0 - x 5⟫ = 0)
    (hW : ¬ (⟪x 2 - x 5, x 3 - x 5⟫ = 0 ∧ ⟪x 0 - x 5, x 3 - x 5⟫ = 0))
    -- T25 leaf hypotheses
    (hdet : Split.det3 (bT25 x) d1 d2 ≠ 0)
    (h3 : 0 < ⟪F.N 3, bT25 x⟫) (h4 : 0 < ⟪F.N 4, bT25 x⟫)
    (h1 : ⟪F.N 1, bT25 x⟫ < 0) (h8 : ⟪F.N 8, bT25 x⟫ < 0)
    (t2 : LexPos3 (-⟪F.N 2, bT25 x⟫) (-⟪F.N 2, d1⟫) (-⟪F.N 2, d2⟫))
    (t6 : LexPos3 (-⟪F.N 6, bT25 x⟫) (-⟪F.N 6, d1⟫) (-⟪F.N 6, d2⟫))
    (hX : GenQuad.CrossOf (x 0) (x 3) (x 5) (x 4))
    (f0356 : FrontDet (x 0) (x 3) (x 5) (x 6) (bT25 x))
    (f0456 : FrontDet (x 0) (x 4) (x 5) (x 6) (bT25 x))
    (f0436 : FrontDet (x 0) (x 4) (x 3) (x 6) (bT25 x))
    (f5436 : FrontDet (x 5) (x 4) (x 3) (x 6) (bT25 x))
    -- T26 leaf hypotheses
    (g6 : 0 < ⟪F.N 6, bT26 x⟫) (g7 : 0 < ⟪F.N 7, bT26 x⟫) (g8 : 0 < ⟪F.N 8, bT26 x⟫)
    (g3 : ⟪F.N 3, bT26 x⟫ < 0) (g4 : ⟪F.N 4, bT26 x⟫ < 0)
    (f2354 : FrontDet (x 2) (x 3) (x 5) (x 4) (bT26 x))
    (f2356 : FrontDet (x 2) (x 3) (x 5) (x 6) (bT26 x))
    (f2456 : FrontDet (x 2) (x 4) (x 5) (x 6) (bT26 x))
    (f3624 : FrontDet (x 3) (x 6) (x 2) (x 4) (bT26 x))
    (f3654 : FrontDet (x 3) (x 6) (x 5) (x 4) (bT26 x)) :
    LexAny F :=
  tieCover_05346W_lex F hd1 hδ hb26 hμ ha hx4 hp4 hx6 hc61 hc62 hc63 tie hW hdet h3 h4
    (Or.inl (by linarith)) h8 t2 t6 hX f0356 f0456 f0436 f5436 g6 g7 g8 g3 g4 f2354 f2356 f2456 f3624 f3654


end Minimality.T24.Q24
