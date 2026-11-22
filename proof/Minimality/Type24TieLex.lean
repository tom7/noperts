module

public import Minimality.Type24TieSigma
public import Minimality.Type24TieCover2

@[expose] public section

/-!
# Type 24: lex boundaries of the A1 tie cover (`h8form = 0`, `h26 = 0`) (Task CL, SIGMA1.md §4)

When facet `8` (`346`) is edge-on at `T25` (`⟪F.N 8, bT25 x⟫ = 0`) or at `T26` (`⟪F.N 8, bT26 x⟫ = 0`),
its sign is decided at the tilt level (`lexPos3_N8_T25` and `lexPos3_N8_T26`). This module provides the `≤`
variants of the T25 / T26 leaves and tie covers so a glue lemma can dispatch on `<`, `=`, `>`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.Q24

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell
  Minimality.LexCell Minimality.Split Minimality.T24.A15
open Minimality.GenQuad (FrontDet)

/-! ### 1. Tilt-level sign lemmas for facet `8` (`346`) -/

/-- At `T25` (`bT25 x = x 5 - x 2`) with `d1 = γ • (x 2 - x 5) + δ • (x 3 - x 5)` (`0 < δ`):
if `0 ≤ ⟪F.N 8, bT25 x⟫`, then `LexPos3 ⟪F.N 8, bT25 x⟫ ⟪F.N 8, d1⟫ ⟪F.N 8, d2⟫`.
On the boundary `⟪F.N 8, bT25 x⟫ = 0`, the `γ` term vanishes because `bT25 x = x 5 - x 2`,
so `⟪F.N 8, x 2 - x 5⟫ = 0`, leaving `⟪F.N 8, d1⟫ = δ * ⟪F.N 8, x 3 - x 5⟫ > 0`. -/
theorem lexPos3_N8_T25 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {d1 d2 : ℝ³} {γ δ : ℝ}
    (hd1 : d1 = γ • (x 2 - x 5) + δ • (x 3 - x 5)) (hδ : 0 < δ)
    (h8 : 0 ≤ ⟪F.N 8, bT25 x⟫) :
    LexPos3 ⟪F.N 8, bT25 x⟫ ⟪F.N 8, d1⟫ ⟪F.N 8, d2⟫ := by
  rcases lt_or_eq_of_le h8 with hlt | heq
  · exact Or.inl hlt
  · refine Or.inr ⟨heq.symm, Or.inl ?_⟩
    -- On the boundary `⟪F.N 8, bT25 x⟫ = 0`, `⟪F.N 8, x 2 - x 5⟫ = 0` since `bT25 x = x 5 - x 2`.
    have h25 : ⟪F.N 8, x 2 - x 5⟫ = 0 := by
      have hb : x 2 - x 5 = -bT25 x := by simp only [bT25]; abel
      rw [hb, inner_neg_right, ← heq, neg_zero]
    have h35 : 0 < ⟪F.N 8, x 3 - x 5⟫ := by
      rw [F.inner_sub, F.zero 8 3 (by decide)]
      have := F.neg 8 5 (by decide); linarith
    rw [hd1, inner_add_right, inner_smul_right, inner_smul_right, h25, mul_zero, zero_add]
    exact mul_pos hδ h35

/-- At `T26` with tilt `d1 = x 3 - x 2`: if `0 ≤ ⟪F.N 8, bT26 x⟫`, then
`LexPos3 ⟪F.N 8, bT26 x⟫ ⟪F.N 8, x 3 - x 2⟫ ⟪F.N 8, (0 : ℝ³)⟫` (since `⟪F.N 8, x 3 - x 2⟫ = -F.f 8 (x 2) > 0`). -/
theorem lexPos3_N8_T26 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (h8 : 0 ≤ ⟪F.N 8, bT26 x⟫) :
    LexPos3 ⟪F.N 8, bT26 x⟫ ⟪F.N 8, x 3 - x 2⟫ ⟪F.N 8, (0 : ℝ³)⟫ := by
  rcases lt_or_eq_of_le h8 with hlt | heq
  · exact Or.inl hlt
  · refine Or.inr ⟨heq.symm, Or.inl ?_⟩
    rw [F.inner_sub, F.zero 8 3 (by decide)]
    have := F.neg 8 2 (by decide); linarith

/-! ### 2. `≤`-variants of the T25 and T26 leaves -/

private def c25a_le : ZMod 4 → Fin 7 := ![0, 5, 3, 6]
private theorem c25a_le_inj : Function.Injective c25a_le := by decide
private theorem c25a_le_cyc : S0xCycUD s0x_S24 c25a_le {3, 4, 8} {1, 2, 6, 7} := by decide

/-- `lexAny_T25_0536_tilt` with `0 ≤ ⟪F.N 8, bT25 x⟫` (covering `h8form = 0`). -/
theorem lexAny_T25_0536_tilt_le {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (d1 d2 : ℝ³)
    {γ δ : ℝ} (hd1 : d1 = γ • (x 2 - x 5) + δ • (x 3 - x 5)) (hδ : 0 < δ)
    (h3 : 0 < ⟪F.N 3, bT25 x⟫) (h4 : 0 < ⟪F.N 4, bT25 x⟫) (h8 : 0 ≤ ⟪F.N 8, bT25 x⟫)
    (h1 : ⟪F.N 1, bT25 x⟫ < 0) (h7 : ⟪F.N 7, bT25 x⟫ < 0)
    (t2 : LexPos3 (-⟪F.N 2, bT25 x⟫) (-⟪F.N 2, d1⟫) (-⟪F.N 2, d2⟫))
    (t6 : LexPos3 (-⟪F.N 6, bT25 x⟫) (-⟪F.N 6, d1⟫) (-⟪F.N 6, d2⟫))
    (f0356 : FrontDet (x 0) (x 3) (x 5) (x 6) (bT25 x))
    (m0356 : GenQuad.LexClause (x 5) (x 6) (x 0) (x 3) (bT25 x) d1 d2) :
    LexAny F := by
  have hb : bT25 x ≠ 0 := fun h => by rw [h, inner_zero_right] at h3; exact lt_irrefl _ h3
  refine GenQuad.lexAny_of_clauses F (k := 4) (by norm_num) c25a_le_inj c25a_le_cyc (bT25 x) d1 d2 ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact Or.inl h3
    · exact Or.inl h4
    · exact lexPos3_N8_T25 F hd1 hδ h8
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact Or.inl (by linarith)
    · exact t2
    · exact t6
    · exact Or.inl (by linarith)
  · exact GenQuad.clauses_four (p := fun i => x (c25a_le i)) (b := bT25 x) (d1 := d1) (d2 := d2)
      m0356 (lexClause_of_det hb f0356)

private def c25b_le : ZMod 5 → Fin 7 := ![0, 1, 6, 3, 5]
private theorem c25b_le_inj : Function.Injective c25b_le := by decide
private theorem c25b_le_cyc : S0xCycUD s0x_S24 c25b_le {1, 3, 8} {0, 2, 5, 6, 7} := by decide

/-- `lexAny_T25_01635_tilt` with `0 ≤ ⟪F.N 8, bT25 x⟫` (covering `h8form = 0`). -/
theorem lexAny_T25_01635_tilt_le {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (d1 d2 : ℝ³)
    {γ δ : ℝ} (hd1 : d1 = γ • (x 2 - x 5) + δ • (x 3 - x 5)) (hδ : 0 < δ)
    (h1 : 0 < ⟪F.N 1, bT25 x⟫) (h3 : 0 < ⟪F.N 3, bT25 x⟫) (h8 : 0 ≤ ⟪F.N 8, bT25 x⟫)
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
  refine GenQuad.lexAny_of_clauses F (k := 5) (by norm_num) c25b_le_inj c25b_le_cyc (bT25 x) d1 d2 ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact Or.inl h1
    · exact Or.inl h3
    · exact lexPos3_N8_T25 F hd1 hδ h8
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (by linarith)
    · exact t2
    · exact Or.inl (by linarith)
    · exact t6
    · exact Or.inl (by linarith)
  · exact GenQuad.clauses_five (p := fun i => x (c25b_le i)) (b := bT25 x) (d1 := d1) (d2 := d2)
      m0613 (lexClause_of_det hb f0613)
      m0615 (lexClause_of_det hb f0615)
      m0315 (lexClause_of_det hb f0315)
      m0365 (lexClause_of_det hb f0365)
      (lexClause_of_det hb f6513) m6513

private def c26_le : ZMod 5 → Fin 7 := ![2, 5, 3, 4, 6]
private theorem c26_le_inj : Function.Injective c26_le := by decide
private theorem c26_le_cyc : S0xCycUD s0x_S24 c26_le {6, 7, 8} {2, 3, 4, 5} := by decide

/-- `lexAny_T26` with `0 ≤ ⟪F.N 8, bT26 x⟫` (covering `h26 = 0`). -/
theorem lexAny_T26_le {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (h6 : 0 < ⟪F.N 6, bT26 x⟫) (h7 : 0 < ⟪F.N 7, bT26 x⟫) (h8 : 0 ≤ ⟪F.N 8, bT26 x⟫)
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
  refine GenQuad.lexAny_of_clauses F (k := 5) (by norm_num) c26_le_inj c26_le_cyc (bT26 x) d1 0 ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact Or.inl h6
    · exact Or.inl h7
    · exact lexPos3_N8_T26 F h8
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
  · exact GenQuad.clauses_five (p := fun i => x (c26_le i)) (b := bT26 x) (d1 := d1) (d2 := 0)
      (lexClause_of_z m2354) (lexClause_of_det hb f2354)
      (lexClause_of_z m2356) (lexClause_of_det hb f2356)
      (lexClause_of_z m2456) (lexClause_of_det hb f2456)
      (lexClause_of_det hb f3624) (lexClause_of_z m3624)
      (lexClause_of_det hb f3654) (lexClause_of_z m3654)

/-- `kill26` with `0 ≤ ⟪F.N 8, bT26 x⟫` (covering `h26 = 0`). -/
theorem kill26_le {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {μ a p4 q4 : ℝ}
    (hb26 : bT26 x = μ • ((a - 1) • (x 2 - x 5) - a • (x 0 - x 5)))
    (hμ : 0 < μ) (ha : 1 < a)
    (hx4 : x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5)) (hp4 : 0 < p4) (hq4 : 0 ≤ q4)
    (tie : ⟪x 2 - x 5, x 0 - x 5⟫ = 0)
    (g6 : 0 < ⟪F.N 6, bT26 x⟫) (g7 : 0 < ⟪F.N 7, bT26 x⟫) (g8 : 0 ≤ ⟪F.N 8, bT26 x⟫)
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
  refine lexAny_T26_le F g6 g7 g8 g3 g4 f2354 f2356 f2456 f3624 f3654 ?_ ?_ ?_ ?_ ?_ <;>
  · intro hM
    simp only [max_le_iff, le_min_iff] at hM
    obtain ⟨⟨_, _⟩, _, _⟩ := hM
    linarith

/-! ### 3. `≤`-variants of the tie covers -/

/-- `tieCover_0536` with `0 ≤ ⟪F.N 8, bT25 x⟫` and `0 ≤ ⟪F.N 8, bT26 x⟫`. -/
theorem tieCover_0536_le {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {d1 d2 : ℝ³} {μ a δ γ p4 q4 : ℝ}
    (hd1 : d1 = γ • (x 2 - x 5) + δ • (x 3 - x 5)) (hδ : 0 < δ)
    (hb26 : bT26 x = μ • ((a - 1) • (x 2 - x 5) - a • (x 0 - x 5))) (hμ : 0 < μ) (ha : 1 < a)
    (hx4 : x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5)) (hp4 : 0 < p4) (hq4 : 0 ≤ q4)
    (tie : ⟪x 2 - x 5, x 0 - x 5⟫ = 0)
    (hW : ¬ (⟪x 2 - x 5, x 3 - x 5⟫ = 0 ∧ ⟪x 0 - x 5, x 3 - x 5⟫ = 0))
    (h3 : 0 < ⟪F.N 3, bT25 x⟫) (h4 : 0 < ⟪F.N 4, bT25 x⟫) (h8 : 0 ≤ ⟪F.N 8, bT25 x⟫)
    (h1 : ⟪F.N 1, bT25 x⟫ < 0) (h7 : ⟪F.N 7, bT25 x⟫ < 0)
    (t2 : LexPos3 (-⟪F.N 2, bT25 x⟫) (-⟪F.N 2, d1⟫) (-⟪F.N 2, d2⟫))
    (t6 : LexPos3 (-⟪F.N 6, bT25 x⟫) (-⟪F.N 6, d1⟫) (-⟪F.N 6, d2⟫))
    (f0356 : FrontDet (x 0) (x 3) (x 5) (x 6) (bT25 x))
    (g6 : 0 < ⟪F.N 6, bT26 x⟫) (g7 : 0 < ⟪F.N 7, bT26 x⟫) (g8 : 0 ≤ ⟪F.N 8, bT26 x⟫)
    (g3 : ⟪F.N 3, bT26 x⟫ < 0) (g4 : ⟪F.N 4, bT26 x⟫ < 0)
    (f2354 : FrontDet (x 2) (x 3) (x 5) (x 4) (bT26 x))
    (f2356 : FrontDet (x 2) (x 3) (x 5) (x 6) (bT26 x))
    (f2456 : FrontDet (x 2) (x 4) (x 5) (x 6) (bT26 x))
    (f3624 : FrontDet (x 3) (x 6) (x 2) (x 4) (bT26 x))
    (f3654 : FrontDet (x 3) (x 6) (x 5) (x 4) (bT26 x)) :
    LexAny F := by
  by_cases hc : GenQuad.LexClause (x 5) (x 6) (x 0) (x 3) (bT25 x) d1 d2
  · exact lexAny_T25_0536_tilt_le F d1 d2 hd1 hδ h3 h4 h8 h1 h7 t2 t6 f0356 hc
  · obtain ⟨⟨u1, u1'⟩, ⟨u2, -⟩, -, -⟩ := notClause hc
    have hb25 : bT25 x = x 5 - x 2 := rfl
    have hA : 0 ≤ ⟪x 3 - x 5, bT25 x⟫ := by rw [inner_sub_left]; linarith
    rcases T_dich hb25 hd1 hb26 tie hμ hδ ha hA (levelB hb25 tie u1 u1') with h | h
    · exact kill26_le F hb26 hμ ha hx4 hp4 hq4 tie g6 g7 g8 g3 g4 f2354 f2356 f2456 f3624 f3654 h
    · exact absurd h hW

/-- `tieCover_01635` with `0 ≤ ⟪F.N 8, bT25 x⟫` and `0 ≤ ⟪F.N 8, bT26 x⟫`. -/
theorem tieCover_01635_le {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {d1 d2 : ℝ³}
    {μ a δ γ p4 q4 c61 c62 c63 : ℝ}
    (hd1 : d1 = γ • (x 2 - x 5) + δ • (x 3 - x 5)) (hδ : 0 < δ)
    (hb26 : bT26 x = μ • ((a - 1) • (x 2 - x 5) - a • (x 0 - x 5))) (hμ : 0 < μ) (ha : 1 < a)
    (hx4 : x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5)) (hp4 : 0 < p4) (hq4 : 0 ≤ q4)
    (hx6 : x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5))
    (hc61 : 0 < c61) (hc63 : 1 ≤ c63)
    (tie : ⟪x 2 - x 5, x 0 - x 5⟫ = 0)
    (hW : ¬ (⟪x 2 - x 5, x 3 - x 5⟫ = 0 ∧ ⟪x 0 - x 5, x 3 - x 5⟫ = 0))
    (h1 : 0 < ⟪F.N 1, bT25 x⟫) (h3 : 0 < ⟪F.N 3, bT25 x⟫) (h8 : 0 ≤ ⟪F.N 8, bT25 x⟫)
    (h0 : ⟪F.N 0, bT25 x⟫ < 0) (h5 : ⟪F.N 5, bT25 x⟫ < 0) (h7 : ⟪F.N 7, bT25 x⟫ < 0)
    (t2 : LexPos3 (-⟪F.N 2, bT25 x⟫) (-⟪F.N 2, d1⟫) (-⟪F.N 2, d2⟫))
    (t6 : LexPos3 (-⟪F.N 6, bT25 x⟫) (-⟪F.N 6, d1⟫) (-⟪F.N 6, d2⟫))
    (f0613 : FrontDet (x 0) (x 6) (x 1) (x 3) (bT25 x))
    (f0615 : FrontDet (x 0) (x 6) (x 1) (x 5) (bT25 x))
    (f0315 : FrontDet (x 0) (x 3) (x 1) (x 5) (bT25 x))
    (f0365 : FrontDet (x 0) (x 3) (x 6) (x 5) (bT25 x))
    (f6513 : FrontDet (x 6) (x 5) (x 1) (x 3) (bT25 x))
    (g6 : 0 < ⟪F.N 6, bT26 x⟫) (g7 : 0 < ⟪F.N 7, bT26 x⟫) (g8 : 0 ≤ ⟪F.N 8, bT26 x⟫)
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
  have kill := kill26_le F hb26 hμ ha hx4 hp4 hq4 tie g6 g7 g8 g3 g4 f2354 f2356 f2456 f3624 f3654
  have iS : ∀ u v : Fin 7, ⟪x u - x v, bT25 x⟫ = ⟪x u, bT25 x⟫ - ⟪x v, bT25 x⟫ :=
    fun u v => inner_sub_left _ _ _
  have k1 : GenQuad.LexClause (x 1) (x 3) (x 0) (x 6) (bT25 x) d1 d2 := by
    by_contra hn
    obtain ⟨-, -, ⟨u3, -⟩, ⟨u4, -⟩⟩ := notClause hn
    have l := line06_13 hb25 hx6 tie
    have e1 := iS 0 3; have e2 := iS 6 3; rw [e1, e2] at l
    nlinarith only [l, mul_nonneg (sub_nonneg.2 hc63) (sub_nonneg.2 u3), sub_nonneg.2 u4, mul_pos hc61 E11]
  have k2 : GenQuad.LexClause (x 1) (x 3) (x 6) (x 5) (bT25 x) d1 d2 := by
    by_contra hn
    obtain ⟨-, -, ⟨u3, -⟩, ⟨u4, -⟩⟩ := notClause hn
    have l := line56_13 hb25 hx6 tie
    have e1 := iS 5 3; have e2 := iS 6 3; rw [e1, e2] at l
    nlinarith only [l, mul_nonneg (sub_nonneg.2 hc63) (sub_nonneg.2 u4), sub_nonneg.2 u3, mul_pos hc61 E11]
  by_cases k3 : GenQuad.LexClause (x 1) (x 5) (x 0) (x 3) (bT25 x) d1 d2
  swap
  · obtain ⟨-, -, ⟨u1, u1'⟩, ⟨u2, -⟩⟩ := notClause k3
    rcases T_dich hb25 hd1 hb26 tie hμ hδ ha (by rw [iS 3 5]; linarith) (levelB hb25 tie u1 u1') with h | h
    · exact kill h
    · exact absurd h hW
  by_cases k4 : GenQuad.LexClause (x 6) (x 5) (x 0) (x 3) (bT25 x) d1 d2
  swap
  · obtain ⟨-, -, ⟨u1, u1'⟩, ⟨u2, -⟩⟩ := notClause k4
    rcases T_dich hb25 hd1 hb26 tie hμ hδ ha (by rw [iS 3 5]; linarith) (levelB hb25 tie u1 u1') with h | h
    · exact kill h
    · exact absurd h hW
  by_cases k5 : GenQuad.LexClause (x 1) (x 5) (x 0) (x 6) (bT25 x) d1 d2
  swap
  · obtain ⟨-, -, ⟨u1, u1'⟩, ⟨u2, -⟩⟩ := notClause k5
    exact kill (T6_strict hb25 hd1 hb26 hx6 tie hμ hδ ha hc61 (by linarith) E11
      (by rw [iS 6 5]; linarith) (levelB hb25 tie u1 u1'))
  exact lexAny_T25_01635_tilt_le F d1 d2 hd1 hδ h1 h3 h8 h0 h5 h7 t2 t6 f0613 f0615 f0315 f0365 f6513
    k1 k5 k3 k4 k2

/-- `tieCover_0536_2536` with `0 ≤ ⟪F.N 8, bT25 x⟫`. -/
theorem tieCover_0536_2536_le {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {d1 d2 : ℝ³} {μ a δ γ : ℝ}
    (hd1 : d1 = γ • (x 2 - x 5) + δ • (x 3 - x 5)) (hδ : 0 < δ)
    (hb26 : bT26 x = μ • ((a - 1) • (x 2 - x 5) - a • (x 0 - x 5))) (hμ : 0 < μ) (ha : 1 < a)
    (tie : ⟪x 2 - x 5, x 0 - x 5⟫ = 0)
    (hW : ¬ (⟪x 2 - x 5, x 3 - x 5⟫ = 0 ∧ ⟪x 0 - x 5, x 3 - x 5⟫ = 0))
    (h3 : 0 < ⟪F.N 3, bT25 x⟫) (h4 : 0 < ⟪F.N 4, bT25 x⟫) (h8 : 0 ≤ ⟪F.N 8, bT25 x⟫)
    (h1 : ⟪F.N 1, bT25 x⟫ < 0) (h7 : ⟪F.N 7, bT25 x⟫ < 0)
    (t2 : LexPos3 (-⟪F.N 2, bT25 x⟫) (-⟪F.N 2, d1⟫) (-⟪F.N 2, d2⟫))
    (t6 : LexPos3 (-⟪F.N 6, bT25 x⟫) (-⟪F.N 6, d1⟫) (-⟪F.N 6, d2⟫))
    (f0356 : FrontDet (x 0) (x 3) (x 5) (x 6) (bT25 x))
    (g6 : 0 < ⟪F.N 6, bT26 x⟫) (g7 : 0 < ⟪F.N 7, bT26 x⟫)
    (g3 : ⟪F.N 3, bT26 x⟫ < 0) (g8 : ⟪F.N 8, bT26 x⟫ < 0)
    (f2356 : FrontDet (x 2) (x 3) (x 5) (x 6) (bT26 x)) :
    LexAny F := by
  by_cases hc : GenQuad.LexClause (x 5) (x 6) (x 0) (x 3) (bT25 x) d1 d2
  · exact lexAny_T25_0536_tilt_le F d1 d2 hd1 hδ h3 h4 h8 h1 h7 t2 t6 f0356 hc
  · obtain ⟨⟨u1, u1'⟩, ⟨u2, -⟩, -, -⟩ := notClause hc
    have hb25 : bT25 x = x 5 - x 2 := rfl
    have hA : 0 ≤ ⟪x 3 - x 5, bT25 x⟫ := by rw [inner_sub_left]; linarith
    rcases T_dich hb25 hd1 hb26 tie hμ hδ ha hA (levelB hb25 tie u1 u1') with h | h
    · exact kill26_2536 F g6 g7 g3 g8 f2356 h
    · exact absurd h hW

/-- `tieCover_01635_2536` with `0 ≤ ⟪F.N 8, bT25 x⟫`. -/
theorem tieCover_01635_2536_le {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {d1 d2 : ℝ³}
    {μ a δ γ c61 c62 c63 : ℝ}
    (hd1 : d1 = γ • (x 2 - x 5) + δ • (x 3 - x 5)) (hδ : 0 < δ)
    (hb26 : bT26 x = μ • ((a - 1) • (x 2 - x 5) - a • (x 0 - x 5))) (hμ : 0 < μ) (ha : 1 < a)
    (hx6 : x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5))
    (hc61 : 0 < c61) (hc63 : 1 ≤ c63)
    (tie : ⟪x 2 - x 5, x 0 - x 5⟫ = 0)
    (hW : ¬ (⟪x 2 - x 5, x 3 - x 5⟫ = 0 ∧ ⟪x 0 - x 5, x 3 - x 5⟫ = 0))
    (h1 : 0 < ⟪F.N 1, bT25 x⟫) (h3 : 0 < ⟪F.N 3, bT25 x⟫) (h8 : 0 ≤ ⟪F.N 8, bT25 x⟫)
    (h0 : ⟪F.N 0, bT25 x⟫ < 0) (h5 : ⟪F.N 5, bT25 x⟫ < 0) (h7 : ⟪F.N 7, bT25 x⟫ < 0)
    (t2 : LexPos3 (-⟪F.N 2, bT25 x⟫) (-⟪F.N 2, d1⟫) (-⟪F.N 2, d2⟫))
    (t6 : LexPos3 (-⟪F.N 6, bT25 x⟫) (-⟪F.N 6, d1⟫) (-⟪F.N 6, d2⟫))
    (f0613 : FrontDet (x 0) (x 6) (x 1) (x 3) (bT25 x))
    (f0615 : FrontDet (x 0) (x 6) (x 1) (x 5) (bT25 x))
    (f0315 : FrontDet (x 0) (x 3) (x 1) (x 5) (bT25 x))
    (f0365 : FrontDet (x 0) (x 3) (x 6) (x 5) (bT25 x))
    (f6513 : FrontDet (x 6) (x 5) (x 1) (x 3) (bT25 x))
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
  have k1 : GenQuad.LexClause (x 1) (x 3) (x 0) (x 6) (bT25 x) d1 d2 := by
    by_contra hn
    obtain ⟨-, -, ⟨u3, -⟩, ⟨u4, -⟩⟩ := notClause hn
    have l := line06_13 hb25 hx6 tie
    have e1 := iS 0 3; have e2 := iS 6 3; rw [e1, e2] at l
    nlinarith only [l, mul_nonneg (sub_nonneg.2 hc63) (sub_nonneg.2 u3), sub_nonneg.2 u4, mul_pos hc61 E11]
  have k2 : GenQuad.LexClause (x 1) (x 3) (x 6) (x 5) (bT25 x) d1 d2 := by
    by_contra hn
    obtain ⟨-, -, ⟨u3, -⟩, ⟨u4, -⟩⟩ := notClause hn
    have l := line56_13 hb25 hx6 tie
    have e1 := iS 5 3; have e2 := iS 6 3; rw [e1, e2] at l
    nlinarith only [l, mul_nonneg (sub_nonneg.2 hc63) (sub_nonneg.2 u4), sub_nonneg.2 u3, mul_pos hc61 E11]
  by_cases k3 : GenQuad.LexClause (x 1) (x 5) (x 0) (x 3) (bT25 x) d1 d2
  swap
  · obtain ⟨-, -, ⟨u1, u1'⟩, ⟨u2, -⟩⟩ := notClause k3
    rcases T_dich hb25 hd1 hb26 tie hμ hδ ha (by rw [iS 3 5]; linarith) (levelB hb25 tie u1 u1') with h | h
    · exact kill h
    · exact absurd h hW
  by_cases k4 : GenQuad.LexClause (x 6) (x 5) (x 0) (x 3) (bT25 x) d1 d2
  swap
  · obtain ⟨-, -, ⟨u1, u1'⟩, ⟨u2, -⟩⟩ := notClause k4
    rcases T_dich hb25 hd1 hb26 tie hμ hδ ha (by rw [iS 3 5]; linarith) (levelB hb25 tie u1 u1') with h | h
    · exact kill h
    · exact absurd h hW
  by_cases k5 : GenQuad.LexClause (x 1) (x 5) (x 0) (x 6) (bT25 x) d1 d2
  swap
  · obtain ⟨-, -, ⟨u1, u1'⟩, ⟨u2, -⟩⟩ := notClause k5
    exact kill (T6_strict hb25 hd1 hb26 hx6 tie hμ hδ ha hc61 (by linarith) E11
      (by rw [iS 6 5]; linarith) (levelB hb25 tie u1 u1'))
  exact lexAny_T25_01635_tilt_le F d1 d2 hd1 hδ h1 h3 h8 h0 h5 h7 t2 t6 f0613 f0615 f0315 f0365 f6513
    k1 k5 k3 k4 k2

/-- `tieCover_05346W` with `0 ≤ ⟪F.N 8, bT26 x⟫` (covering `h26 = 0`) and `1 ≤ c63`. -/
theorem tieCover_05346W_le {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {d1 d2 : ℝ³}
    {μ a δ γ p4 q4 c61 c62 c63 : ℝ}
    (hd1 : d1 = γ • (x 2 - x 5) + δ • (x 3 - x 5)) (hδ : 0 < δ)
    (hb26 : bT26 x = μ • ((a - 1) • (x 2 - x 5) - a • (x 0 - x 5))) (hμ : 0 < μ) (ha : 1 < a)
    (hx4 : x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5)) (hp4 : 0 < p4)
    (hx6 : x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5))
    (hc61 : 0 < c61) (hc62 : 0 < c62) (hc63 : 1 ≤ c63)
    (tie : ⟪x 2 - x 5, x 0 - x 5⟫ = 0)
    (hW : ¬ (⟪x 2 - x 5, x 3 - x 5⟫ = 0 ∧ ⟪x 0 - x 5, x 3 - x 5⟫ = 0))
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
    (g6 : 0 < ⟪F.N 6, bT26 x⟫) (g7 : 0 < ⟪F.N 7, bT26 x⟫) (g8 : 0 ≤ ⟪F.N 8, bT26 x⟫)
    (g3 : ⟪F.N 3, bT26 x⟫ < 0) (g4 : ⟪F.N 4, bT26 x⟫ < 0)
    (f2354 : FrontDet (x 2) (x 3) (x 5) (x 4) (bT26 x))
    (f2356 : FrontDet (x 2) (x 3) (x 5) (x 6) (bT26 x))
    (f2456 : FrontDet (x 2) (x 4) (x 5) (x 6) (bT26 x))
    (f3624 : FrontDet (x 3) (x 6) (x 2) (x 4) (bT26 x))
    (f3654 : FrontDet (x 3) (x 6) (x 5) (x 4) (bT26 x)) :
    LexAny F := by
  rcases lt_or_eq_of_le g8 with g8lt | g8eq
  · exact tieCover_05346W F hd1 hδ hb26 hμ ha hx4 hp4 hx6 hc61 hc62 hc63 tie hW
      hdet h3 h4 h1 h8 t2 t6 hX f0356 f0456 f0436 f5436 g6 g7 g8lt g3 g4 f2354 f2356 f2456 f3624 f3654
  · have hq4 : 1 < q4 := q4_gt_one_of_facet8 F hx4 hx6 hp4 hc61 hc62 hc63 h8
    have hb25 : bT25 x = x 5 - x 2 := rfl
    have kill := kill26_le F hb26 hμ ha hx4 hp4 (by linarith) tie g6 g7 g8 g3 g4 f2354 f2356 f2456 f3624 f3654
    have iS : ∀ u v : Fin 7, ⟪x u - x v, bT25 x⟫ = ⟪x u, bT25 x⟫ - ⟪x v, bT25 x⟫ :=
      fun u v => inner_sub_left _ _ _
    have hq0 : 0 < q4 := by linarith
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
    have E33 : 0 < ⟪x 3 - x 5, x 3 - x 5⟫ :=
      real_inner_self_pos.mpr (sub_ne_zero.2 (fun h => absurd (inj_of_fac F h) (by decide)))
    by_cases k1 : GenQuad.LexClause (x 5) (x 6) (x 0) (x 3) (bT25 x) d1 d2
    swap
    · obtain ⟨⟨u1, u1'⟩, ⟨u2, -⟩, -, -⟩ := notClause k1
      exact viaT (by rw [iS 3 5]; linarith) (levelB hb25 tie u1 u1')
    by_cases k2 : GenQuad.LexClause (x 5) (x 6) (x 0) (x 4) (bT25 x) d1 d2
    swap
    · obtain ⟨⟨u1, u1'⟩, ⟨u2, -⟩, -, -⟩ := notClause k2
      exact viaT4 (by rw [iS 4 5]; linarith) (levelB hb25 tie u1 u1')
    by_cases k3 : GenQuad.LexClause (x 3) (x 6) (x 0) (x 4) (bT25 x) d1 d2
    swap
    · obtain ⟨⟨u1, u1'⟩, ⟨u2, -⟩, -, -⟩ := notClause k3
      have l := line04_36 hb25 hx4 tie
      have e1 := iS 0 3; have e2 := iS 4 3
      have h03 := z03_E13 hb25 tie
      have hz : ⟪x 0 - x 3, bT25 x⟫ = 0 := by
        by_contra hne
        have hpos := mul_pos (sub_pos.2 hq4) (lt_of_le_of_ne (by rw [e1]; linarith) (Ne.symm hne))
        rw [e2] at l; linarith only [l, hpos, u2]
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
        have hpos := mul_pos (sub_pos.2 hq4) (lt_of_le_of_ne (by rw [e1]; linarith) (Ne.symm hne))
        rw [e2] at l; linarith only [l, hpos, u2]
      have E13 : ⟪x 2 - x 5, x 3 - x 5⟫ = 0 := by rw [← h53]; exact hz
      exact wp_k4 hd1 E13 hδ E33 (u1' (by rw [e1] at hz; linarith))
    exact lexAny_T25_05346_tilt F d1 d2 hdet h3 h4 h1 h8 t2 t6 hX f0356 f0456 f0436 f5436 k1 k2 k3 k4

/-- `tieCover_016435` with `0 ≤ ⟪F.N 8, bT26 x⟫` (covering `h26 = 0`). -/
theorem tieCover_016435_le {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {d1 d2 : ℝ³}
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
    (g6 : 0 < ⟪F.N 6, bT26 x⟫) (g7 : 0 < ⟪F.N 7, bT26 x⟫) (g8 : 0 ≤ ⟪F.N 8, bT26 x⟫)
    (g3 : ⟪F.N 3, bT26 x⟫ < 0) (g4 : ⟪F.N 4, bT26 x⟫ < 0)
    (f2354 : FrontDet (x 2) (x 3) (x 5) (x 4) (bT26 x))
    (f2356 : FrontDet (x 2) (x 3) (x 5) (x 6) (bT26 x))
    (f2456 : FrontDet (x 2) (x 4) (x 5) (x 6) (bT26 x))
    (f3624 : FrontDet (x 3) (x 6) (x 2) (x 4) (bT26 x))
    (f3654 : FrontDet (x 3) (x 6) (x 5) (x 4) (bT26 x)) :
    LexAny F := by
  rcases lt_or_eq_of_le g8 with g8lt | g8eq
  · exact tieCover_016435 F hd1 hδ hb26 hμ ha hx4 hp4 hq4 hx1 hc11 hc13 hc13_1 hx6 hc61 hc13_63 hq4_63
      h16 tie hW hdet h1 h3 h4 h0 h5 h7 h8 t2 t6 hX f0614 f0613 f0615 f0413 f0415 f0315 f0463 f0465
      f0365 f1463 f1465 f6513 f4513 f4563 g6 g7 g8lt g3 g4 f2354 f2356 f2456 f3624 f3654
  · -- On `⟪F.N 8, bT26 x⟫ = 0`, `kill26_le` handles `z3 < z5` at `T26` identically to `kill26`.
    have hb25 : bT25 x = x 5 - x 2 := rfl
    have hinj := inj_of_fac F
    have hne2 : x 2 - x 5 ≠ 0 := sub_ne_zero.2 (fun h => absurd (hinj h) (by decide))
    have E11 : 0 < ⟪x 2 - x 5, x 2 - x 5⟫ := real_inner_self_pos.mpr hne2
    have E33 : 0 < ⟪x 3 - x 5, x 3 - x 5⟫ :=
      real_inner_self_pos.mpr (sub_ne_zero.2 (fun h => absurd (hinj h) (by decide)))
    have hq0 : 0 < q4 := by linarith
    have kill := kill26_le F hb26 hμ ha hx4 hp4 hq0.le tie g6 g7 g8 g3 g4 f2354 f2356 f2456 f3624 f3654
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
      have e1 := iS 0 4; have e2 := iS 6 4; rw [e1, e2] at l
      nlinarith only [l, mul_nonneg (sub_nonneg.2 hq4_63) (sub_nonneg.2 u3),
        mul_nonneg hq0.le (sub_nonneg.2 u4), mul_pos (mul_pos hq0 hc61) E11]
    have k0613 : GenQuad.LexClause (x 1) (x 3) (x 0) (x 6) (bT25 x) d1 d2 := by
      by_contra hn
      obtain ⟨-, -, ⟨u3, -⟩, ⟨u4, -⟩⟩ := notClause hn
      have l := line06_13 hb25 hx6 tie
      have e1 := iS 0 3; have e2 := iS 6 3
      have hc63_1 : 1 ≤ c63 := by linarith only [hq4, hq4_63]
      rw [e1, e2] at l
      nlinarith only [l, mul_nonneg (sub_nonneg.2 hc63_1) (sub_nonneg.2 u3), sub_nonneg.2 u4, mul_pos hc61 E11]
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
      have e1 := iS 1 3; have e2 := iS 4 3; rw [e1, e2] at l
      nlinarith only [l, mul_nonneg (sub_pos.2 hq4).le (sub_nonneg.2 u3),
        mul_nonneg (sub_pos.2 hc13_1).le (sub_nonneg.2 u4),
        mul_pos (mul_pos (sub_pos.2 hq4) hc11) E11]
    have k1465 : GenQuad.LexClause (x 6) (x 5) (x 1) (x 4) (bT25 x) d1 d2 := by
      by_contra hn
      obtain ⟨⟨u1, -⟩, -, ⟨u3, -⟩, -⟩ := notClause hn
      have l := line13_56 hb25 hx1 hx6 tie
      have e1 := iS 1 5; have e2 := iS 1 6; rw [e1, e2] at l
      nlinarith only [l, mul_nonneg (sub_nonneg.2 hc13_63) (sub_nonneg.2 u3),
        mul_nonneg hc13 (sub_nonneg.2 u1), mul_pos h16 E11]
    have k6513 : GenQuad.LexClause (x 1) (x 3) (x 6) (x 5) (bT25 x) d1 d2 := by
      by_contra hn
      obtain ⟨-, -, ⟨u3, -⟩, ⟨u4, -⟩⟩ := notClause hn
      have l := line56_13 hb25 hx6 tie
      have e1 := iS 5 3; have e2 := iS 6 3
      have hc63_1 : 1 ≤ c63 := by linarith only [hq4, hq4_63]
      rw [e1, e2] at l
      nlinarith only [l, mul_nonneg (sub_nonneg.2 hc63_1) (sub_nonneg.2 u4), sub_nonneg.2 u3, mul_pos hc61 E11]
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

end Minimality.T24.Q24
