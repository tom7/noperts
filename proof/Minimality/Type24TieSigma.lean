module

public import Minimality.Type24TieCover
public import Minimality.CSLCorner
public import Minimality.RDispatch24

@[expose] public section

/-!
# Type 24: the sigma = 1 boundary of the A1 tie cover (SIGMA1.md)

T26 rim `2536` (facet 346 back at T26): `lexAny_T26_2536`; tie covers `tieCover_0536_2536`,
`tieCover_01635_2536` (no `q4`, `p4` hypotheses); the two 346 facing formulas `facet8_T25`, `facet8_T26`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.Q24

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell
  Minimality.LexCell Minimality.Split Minimality.T24.A15 Minimality.NF29
open Minimality.GenQuad (FrontDet)
open Minimality.T24.Q45 (Q45HalfHyp)

private def c26' : ZMod 4 → Fin 7 := ![2, 5, 3, 6]
private theorem c26'_inj : Function.Injective c26' := by decide
private theorem c26'_cyc : S0xCycUD s0x_S24 c26' {6, 7} {2, 3, 5, 8} := by decide

/-- **T26, 4-rim `(2 5 3 6)`** (346 back; front `23`, one clause `23>56`). -/
theorem lexAny_T26_2536 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (h6 : 0 < ⟪F.N 6, bT26 x⟫) (h7 : 0 < ⟪F.N 7, bT26 x⟫)
    (h3 : ⟪F.N 3, bT26 x⟫ < 0) (h8 : ⟪F.N 8, bT26 x⟫ < 0)
    (f2356 : FrontDet (x 2) (x 3) (x 5) (x 6) (bT26 x))
    (m2356 : ¬ (max (z x (bT26 x) 5) (z x (bT26 x) 6) ≤ min (z x (bT26 x) 2) (z x (bT26 x) 3))) :
    LexAny F := by
  have hb : bT26 x ≠ 0 := fun h => by rw [h, inner_zero_right] at h6; exact lt_irrefl _ h6
  let d1 : ℝ³ := x 3 - x 2
  refine GenQuad.lexAny_of_clauses F (k := 4) (by norm_num) c26'_inj c26'_cyc (bT26 x) d1 0 ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact Or.inl h6
    · exact Or.inl h7
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · refine Or.inr ⟨by rw [bT26_N2 F, neg_zero], Or.inl ?_⟩
      simp only [d1, F.inner_sub, F.zero 2 2 (by decide)]
      have := F.neg 2 3 (by decide); linarith
    · exact Or.inl (by linarith)
    · refine Or.inr ⟨by rw [bT26_N5 F, neg_zero], Or.inl ?_⟩
      simp only [d1, F.inner_sub, F.zero 5 2 (by decide)]
      have := F.neg 5 3 (by decide); linarith
    · exact Or.inl (by linarith)
  · exact GenQuad.clauses_four (p := fun i => x (c26' i)) (b := bT26 x) (d1 := d1) (d2 := 0)
      (lexClause_of_z m2356) (lexClause_of_det hb f2356)

/-- If `z3 < z5` at T26, the rim-`2536` leaf applies (`z3 >= z5` is part of the clause `23>56`). -/
theorem kill26_2536 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (g6 : 0 < ⟪F.N 6, bT26 x⟫) (g7 : 0 < ⟪F.N 7, bT26 x⟫)
    (g3 : ⟪F.N 3, bT26 x⟫ < 0) (g8 : ⟪F.N 8, bT26 x⟫ < 0)
    (f2356 : FrontDet (x 2) (x 3) (x 5) (x 6) (bT26 x))
    (hC : ⟪x 3 - x 5, bT26 x⟫ < 0) : LexAny F := by
  have zd := zdiff x (bT26 x) 3 5
  refine lexAny_T26_2536 F g6 g7 g3 g8 f2356 ?_
  intro hM
  rw [max_le_iff, le_min_iff, le_min_iff] at hM
  linarith [hM.1.2]

/-- **Tie cover, rims `0536` (T25) / `2536` (T26)** (SIGMA1 1, 4). As `tieCover_0536`, but T26 has the rim
`2536`; no `x4` frame, `p4`, `q4` hypotheses are needed. -/
theorem tieCover_0536_2536 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {d1 d2 : ℝ³} {μ a δ γ : ℝ}
    (hd1 : d1 = γ • (x 2 - x 5) + δ • (x 3 - x 5)) (hδ : 0 < δ)
    (hb26 : bT26 x = μ • ((a - 1) • (x 2 - x 5) - a • (x 0 - x 5))) (hμ : 0 < μ) (ha : 1 < a)
    (tie : ⟪x 2 - x 5, x 0 - x 5⟫ = 0)
    (hW : ¬ (⟪x 2 - x 5, x 3 - x 5⟫ = 0 ∧ ⟪x 0 - x 5, x 3 - x 5⟫ = 0))
    -- T25 leaf hypotheses
    (h3 : 0 < ⟪F.N 3, bT25 x⟫) (h4 : 0 < ⟪F.N 4, bT25 x⟫) (h8 : 0 < ⟪F.N 8, bT25 x⟫)
    (h1 : ⟪F.N 1, bT25 x⟫ < 0) (h7 : ⟪F.N 7, bT25 x⟫ < 0)
    (t2 : LexPos3 (-⟪F.N 2, bT25 x⟫) (-⟪F.N 2, d1⟫) (-⟪F.N 2, d2⟫))
    (t6 : LexPos3 (-⟪F.N 6, bT25 x⟫) (-⟪F.N 6, d1⟫) (-⟪F.N 6, d2⟫))
    (f0356 : FrontDet (x 0) (x 3) (x 5) (x 6) (bT25 x))
    -- T26 leaf hypotheses (rim 2536)
    (g6 : 0 < ⟪F.N 6, bT26 x⟫) (g7 : 0 < ⟪F.N 7, bT26 x⟫)
    (g3 : ⟪F.N 3, bT26 x⟫ < 0) (g8 : ⟪F.N 8, bT26 x⟫ < 0)
    (f2356 : FrontDet (x 2) (x 3) (x 5) (x 6) (bT26 x)) :
    LexAny F := by
  by_cases hc : GenQuad.LexClause (x 5) (x 6) (x 0) (x 3) (bT25 x) d1 d2
  · exact lexAny_T25_0536_tilt F d1 d2 h3 h4 h8 h1 h7 t2 t6 f0356 hc
  · obtain ⟨⟨u1, u1'⟩, ⟨u2, -⟩, -, -⟩ := notClause hc
    have hb25 : bT25 x = x 5 - x 2 := rfl
    have hA : 0 ≤ ⟪x 3 - x 5, bT25 x⟫ := by rw [inner_sub_left]; linarith
    rcases T_dich hb25 hd1 hb26 tie hμ hδ ha hA (levelB hb25 tie u1 u1') with h | h
    · exact kill26_2536 F g6 g7 g3 g8 f2356 h
    · exact absurd h hW

/-- **Tie cover, rims `01635` (T25) / `2536` (T26)**. As `tieCover_01635` with T26 rim `2536`; no `p4`, `q4`. -/
theorem tieCover_01635_2536 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {d1 d2 : ℝ³}
    {μ a δ γ c61 c62 c63 : ℝ}
    (hd1 : d1 = γ • (x 2 - x 5) + δ • (x 3 - x 5)) (hδ : 0 < δ)
    (hb26 : bT26 x = μ • ((a - 1) • (x 2 - x 5) - a • (x 0 - x 5))) (hμ : 0 < μ) (ha : 1 < a)
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
    -- T26 leaf hypotheses (rim 2536)
    (g6 : 0 < ⟪F.N 6, bT26 x⟫) (g7 : 0 < ⟪F.N 7, bT26 x⟫)
    (g3 : ⟪F.N 3, bT26 x⟫ < 0) (g8 : ⟪F.N 8, bT26 x⟫ < 0)
    (f2356 : FrontDet (x 2) (x 3) (x 5) (x 6) (bT26 x)) :
    LexAny F := by
  have hb25 : bT25 x = x 5 - x 2 := rfl
  have hinj := inj_of_fac F
  have hne2 : x 2 - x 5 ≠ 0 := sub_ne_zero.2 (fun h => absurd (hinj h) (by decide))
  have E11 : 0 < ⟪x 2 - x 5, x 2 - x 5⟫ := real_inner_self_pos.mpr hne2
  have kill := kill26_2536 F g6 g7 g3 g8 f2356
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
  exact lexAny_T25_01635_tilt F d1 d2 h1 h3 h8 h0 h5 h7 t2 t6 f0613 f0615 f0315 f0365 f6513
    k1 k5 k3 k4 k2

/-! ### The two 346-facing formulas -/

/-- Common core: the facet-346 covector `N 8` in the vertex-5 frame. `A = ⟪N8, e1⟫`, `B = ⟪N8, e2⟫`,
`C = ⟪N8, e3⟫ > 0` (x5 is behind 346) with `p4 B + (q4-1) C = 0`, `c61 A + c62 B + (c63-1) C = 0`. -/
theorem facet8_frame {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {p4 q4 c61 c62 c63 : ℝ}
    (hx4 : x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5))
    (hx6 : x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5)) :
    0 < ⟪F.N 8, x 3 - x 5⟫ ∧
    p4 * ⟪F.N 8, x 0 - x 5⟫ + (q4 - 1) * ⟪F.N 8, x 3 - x 5⟫ = 0 ∧
    c61 * ⟪F.N 8, x 2 - x 5⟫ + c62 * ⟪F.N 8, x 0 - x 5⟫ + (c63 - 1) * ⟪F.N 8, x 3 - x 5⟫ = 0 := by
  have z4 : ⟪F.N 8, x 4 - x 3⟫ = 0 := by
    rw [F.inner_sub, F.zero 8 4 (by decide), F.zero 8 3 (by decide)]; ring
  have z6 : ⟪F.N 8, x 6 - x 3⟫ = 0 := by
    rw [F.inner_sub, F.zero 8 6 (by decide), F.zero 8 3 (by decide)]; ring
  have n5 : ⟪F.N 8, x 5 - x 3⟫ < 0 := by
    rw [F.inner_sub, F.zero 8 3 (by decide)]; have := F.neg 8 5 (by decide); linarith
  have e53 : x 5 - x 3 = -(x 3 - x 5) := by abel
  have e43 : x 4 - x 3 = (x 4 - x 5) - (x 3 - x 5) := by abel
  have e63 : x 6 - x 3 = (x 6 - x 5) - (x 3 - x 5) := by abel
  rw [e53, inner_neg_right] at n5
  rw [e43, hx4] at z4
  rw [e63, hx6] at z6
  generalize x 2 - x 5 = e1 at *
  generalize x 0 - x 5 = e2 at *
  generalize x 3 - x 5 = e3 at *
  simp only [inner_add_right, inner_sub_right, inner_smul_right] at z4 z6
  refine ⟨by linarith, by linarith, by linarith⟩

/-- **346 facing at T25** (SIGMA1 1, `h8form`): `⟪N 8, bT25⟫ = κ (p4 (c63 - 1) - (q4 - 1) c62)`, `κ > 0`. -/
theorem facet8_T25 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {p4 q4 c61 c62 c63 : ℝ}
    (hx4 : x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5))
    (hx6 : x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5))
    (hp4 : 0 < p4) (hc61 : 0 < c61) :
    ∃ κ : ℝ, 0 < κ ∧ ⟪F.N 8, bT25 x⟫ = κ * (p4 * (c63 - 1) - (q4 - 1) * c62) := by
  obtain ⟨hC, eq1, eq2⟩ := facet8_frame F hx4 hx6
  have hb : bT25 x = -(x 2 - x 5) := by simp only [bT25]; abel
  rw [hb, inner_neg_right]
  generalize ⟪F.N 8, x 2 - x 5⟫ = A at *
  generalize ⟪F.N 8, x 0 - x 5⟫ = B at *
  generalize ⟪F.N 8, x 3 - x 5⟫ = C at *
  refine ⟨C / (p4 * c61), div_pos hC (mul_pos hp4 hc61), ?_⟩
  have hpc : p4 * c61 ≠ 0 := (mul_pos hp4 hc61).ne'
  rw [div_mul_eq_mul_div, eq_div_iff hpc]
  linear_combination (-p4) * eq2 + c62 * eq1

/-- **346 facing at T26** (SIGMA1 1): `⟪N 8, bT26⟫ = κ h26`, `κ > 0`,
`h26 = (q4 - 1)(a c61 + (a - 1) c62) - (a - 1) p4 (c63 - 1)` (`c61` is the `c6^1` of SIGMA1). -/
theorem facet8_T26 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {p4 q4 c61 c62 c63 μ a : ℝ}
    (hx4 : x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5))
    (hx6 : x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5))
    (hb26 : bT26 x = μ • ((a - 1) • (x 2 - x 5) - a • (x 0 - x 5)))
    (hp4 : 0 < p4) (hc61 : 0 < c61) (hμ : 0 < μ) :
    ∃ κ : ℝ, 0 < κ ∧ ⟪F.N 8, bT26 x⟫ =
      κ * ((q4 - 1) * (a * c61 + (a - 1) * c62) - (a - 1) * p4 * (c63 - 1)) := by
  obtain ⟨hC, eq1, eq2⟩ := facet8_frame F hx4 hx6
  rw [hb26, inner_smul_right, inner_sub_right, inner_smul_right, inner_smul_right]
  generalize ⟪F.N 8, x 2 - x 5⟫ = A at *
  generalize ⟪F.N 8, x 0 - x 5⟫ = B at *
  generalize ⟪F.N 8, x 3 - x 5⟫ = C at *
  refine ⟨μ * C / (p4 * c61), div_pos (mul_pos hμ hC) (mul_pos hp4 hc61), ?_⟩
  have hpc : p4 * c61 ≠ 0 := (mul_pos hp4 hc61).ne'
  rw [div_mul_eq_mul_div, eq_div_iff hpc]
  linear_combination (μ * (a - 1) * p4) * eq2 + (-μ * (a * c61 + (a - 1) * c62)) * eq1

/-- Sign form of `facet8_T25`. -/
theorem facet8_T25_pos_iff {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {p4 q4 c61 c62 c63 : ℝ}
    (hx4 : x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5))
    (hx6 : x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5))
    (hp4 : 0 < p4) (hc61 : 0 < c61) :
    0 < ⟪F.N 8, bT25 x⟫ ↔ (q4 - 1) * c62 < p4 * (c63 - 1) := by
  obtain ⟨κ, hκ, h⟩ := facet8_T25 F hx4 hx6 hp4 hc61
  rw [h]; constructor
  · intro h'; have := (pos_iff_pos_of_mul_pos h' |>.1 hκ); linarith
  · intro h'; exact mul_pos hκ (by linarith)

/-- Sign form of `facet8_T26`. -/
theorem facet8_T26_pos_iff {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {p4 q4 c61 c62 c63 μ a : ℝ}
    (hx4 : x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5))
    (hx6 : x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5))
    (hb26 : bT26 x = μ • ((a - 1) • (x 2 - x 5) - a • (x 0 - x 5)))
    (hp4 : 0 < p4) (hc61 : 0 < c61) (hμ : 0 < μ) :
    0 < ⟪F.N 8, bT26 x⟫ ↔
      (a - 1) * p4 * (c63 - 1) < (q4 - 1) * (a * c61 + (a - 1) * c62) := by
  obtain ⟨κ, hκ, h⟩ := facet8_T26 F hx4 hx6 hb26 hp4 hc61 hμ
  rw [h]; constructor
  · intro h'; have := (pos_iff_pos_of_mul_pos h' |>.1 hκ); linarith
  · intro h'; exact mul_pos hκ (by linarith)


/-- **A1 and not `Q45HalfPred` imply `a4 ≤ 1`** (SIGMA1 2, step 1), in `N 5` form (facet 5 = `126`;
`a_y` decreases along `N 5`): if every positive Lemma-M decomposition `x3 - x0 = s (x4-x0) + t (x5-x0)` has
`s ≤ 1` (A1) and `a5 > 1` (`⟪N5, x5 - x0⟫ < 0`), and `Q45HalfPred` fails, then `a4 ≤ 1`
(`0 ≤ ⟪N5, x4 - x0⟫`). The `kJ` case split of `Q45HalfHyp` is not needed. -/
theorem a4_le_of_not_half {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hA1 : ∀ s t : ℝ, 0 < s → 0 < t → 1 < s + t →
      x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0) → s ≤ 1)
    (h5 : ⟪F.N 5, x 5 - x 0⟫ < 0) (hn : ¬ Q45HalfPred F) :
    0 ≤ ⟪F.N 5, x 4 - x 0⟫ := by
  unfold Q45HalfPred at hn
  push Not at hn
  obtain ⟨s, t, hs, ht, hst, hdec, hfail⟩ := hn
  have hs1 := hA1 s t hs ht hst hdec
  by_contra hneg
  push Not at hneg
  apply hfail
  unfold Q45HalfHyp
  refine ⟨fun _ => ⟨fun _ => h5, fun h => absurd hs1 (not_le.2 h)⟩, fun _ => ⟨fun _ => hneg, fun h => ?_⟩,
    fun _ => ⟨hneg, h5⟩⟩
  have e : x 3 - x 5 = s • (x 4 - x 0) + (t - 1) • (x 5 - x 0) := by
    have : x 3 - x 5 = (x 3 - x 0) - (x 5 - x 0) := by abel
    rw [this, hdec]; module
  rw [e, inner_add_right, inner_smul_right, inner_smul_right]
  nlinarith [mul_neg_of_pos_of_neg hs hneg, mul_neg_of_pos_of_neg (sub_pos.2 h) h5]

/-! ### The c^1 identities of SIGMA1 section 2 (vertex-1 frame `y = (a, b, c)`) -/

/-- Vertex-1 frame `y = (a, b, c)` (`y1 = 0`, `y0 = e_a`, `y2 = e_b`, `y6 = e_c`). -/
noncomputable def yv (a b c : ℝ) : ℝ³ := !₂[a, b, c]

/-- `c^1`-coordinate (vertex-5 frame, face-0345 functional normalised at `x2`) of the point `v`,
from the vertices `y4, y5` (`x3` lies in the plane `0 4 5`, so `e3` may be replaced by `y4 - y5`). -/
noncomputable def c1coord (v y4 y5 : ℝ³) : ℝ :=
  Split.det3 (v - y5) (yv 1 0 0 - y5) (y4 - y5) / Split.det3 (yv 0 1 0 - y5) (yv 1 0 0 - y5) (y4 - y5)

theorem c1_den (a4 b4 c4 a5 b5 c5 : ℝ) :
    Split.det3 (yv 0 1 0 - yv a5 b5 c5) (yv 1 0 0 - yv a5 b5 c5) (yv a4 b4 c4 - yv a5 b5 c5) =
      (c4 * (a5 - 1) + c5 * (1 - a4)) + (b5 * c4 - b4 * c5) := by
  simp [Split.det3, yv]; ring

theorem c1_num1 (a4 b4 c4 a5 b5 c5 : ℝ) :
    Split.det3 (yv 0 0 0 - yv a5 b5 c5) (yv 1 0 0 - yv a5 b5 c5) (yv a4 b4 c4 - yv a5 b5 c5) =
      b5 * c4 - b4 * c5 := by
  simp [Split.det3, yv]; ring

theorem c1_num6 (a4 b4 c4 a5 b5 c5 : ℝ) :
    Split.det3 (yv 0 0 1 - yv a5 b5 c5) (yv 1 0 0 - yv a5 b5 c5) (yv a4 b4 c4 - yv a5 b5 c5) =
      (b5 * c4 - b4 * c5) - ((a5 - 1) * (b4 + c4) + (1 - a4) * (b5 + c5)) +
        (c4 * (a5 - 1) + c5 * (1 - a4)) := by
  simp [Split.det3, yv]; ring

/-- `1 - c1^1 = nbp / (nbp + D45)`, `nbp = c4 (a5 - 1) + c5 (1 - a4)`, `D45 = b5 c4 - b4 c5`. -/
theorem one_sub_c1_vertex1 (a4 b4 c4 a5 b5 c5 : ℝ)
    (hden : (c4 * (a5 - 1) + c5 * (1 - a4)) + (b5 * c4 - b4 * c5) ≠ 0) :
    1 - c1coord (yv 0 0 0) (yv a4 b4 c4) (yv a5 b5 c5) =
      (c4 * (a5 - 1) + c5 * (1 - a4)) / ((c4 * (a5 - 1) + c5 * (1 - a4)) + (b5 * c4 - b4 * c5)) := by
  unfold c1coord
  rw [c1_den, c1_num1]
  field_simp
  ring

/-- `1 - c6^1 = m / (nbp + D45)`, `m = (a5 - 1)(b4 + c4) + (1 - a4)(b5 + c5)`. -/
theorem one_sub_c1_vertex6 (a4 b4 c4 a5 b5 c5 : ℝ)
    (hden : (c4 * (a5 - 1) + c5 * (1 - a4)) + (b5 * c4 - b4 * c5) ≠ 0) :
    1 - c1coord (yv 0 0 1) (yv a4 b4 c4) (yv a5 b5 c5) =
      ((a5 - 1) * (b4 + c4) + (1 - a4) * (b5 + c5)) /
        ((c4 * (a5 - 1) + c5 * (1 - a4)) + (b5 * c4 - b4 * c5)) := by
  unfold c1coord
  rw [c1_den, c1_num6]
  field_simp
  ring

/-- With `a4 ≤ 1 < a5`, `b4, c4, b5, c5 > 0` (convexity) and `D45 > 0`: `c1^1 < 1` and `c6^1 < 1`
(these are `csl24`'s `h1`, `h6` up to the inner-product link, not done here). -/
theorem c1_lt_one (a4 b4 c4 a5 b5 c5 : ℝ) (ha4 : a4 ≤ 1) (ha5 : 1 < a5)
    (hb4 : 0 < b4) (hc4 : 0 < c4) (hb5 : 0 < b5) (hc5 : 0 < c5) (hD : 0 < b5 * c4 - b4 * c5) :
    c1coord (yv 0 0 0) (yv a4 b4 c4) (yv a5 b5 c5) < 1 ∧
    c1coord (yv 0 0 1) (yv a4 b4 c4) (yv a5 b5 c5) < 1 := by
  have hn : 0 < c4 * (a5 - 1) + c5 * (1 - a4) := by
    nlinarith [mul_pos hc4 (sub_pos.2 ha5), mul_nonneg hc5.le (sub_nonneg.2 ha4)]
  have hm : 0 < (a5 - 1) * (b4 + c4) + (1 - a4) * (b5 + c5) := by
    nlinarith [mul_pos (sub_pos.2 ha5) (add_pos hb4 hc4), mul_nonneg (sub_nonneg.2 ha4) (add_pos hb5 hc5).le]
  have hden : 0 < (c4 * (a5 - 1) + c5 * (1 - a4)) + (b5 * c4 - b4 * c5) := by linarith
  constructor
  · have := one_sub_c1_vertex1 a4 b4 c4 a5 b5 c5 hden.ne'
    have h2 : 0 < 1 - c1coord (yv 0 0 0) (yv a4 b4 c4) (yv a5 b5 c5) := by rw [this]; positivity
    linarith
  · have := one_sub_c1_vertex6 a4 b4 c4 a5 b5 c5 hden.ne'
    have h2 : 0 < 1 - c1coord (yv 0 0 1) (yv a4 b4 c4) (yv a5 b5 c5) := by rw [this]; positivity
    linarith

end Minimality.T24.Q24
