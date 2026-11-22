module

public import Minimality.Type29Hole
public import Minimality.Type29T1Close
public import Minimality.Type29DClose
public import Minimality.Type29SubPencil

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.Gen Minimality.H21 Minimality.H29K1 Minimality.H29S Minimality.NF29

namespace Minimality.H29

/-!
# Type 29: Reduction of `Hole29` to `Hole29R1`

Excludes the `t = 1` K1a cell closed by `NF29.t1_closed` (`T1Hyp`) from `Hole29`, yielding
`Hole29R1 x N := Hole29 x N ∧ ¬ T1Hyp x N`.
-/

/-- Hypothesis bundle for `NF29.t1_closed` (excluding `OB6`'s `hg35, hg45` and `¬ LexAny29`,
which are already supplied by `Hole29`). -/
def T1Hyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  N.t = 1 ∧ 0 < N.dG4 ∧ 0 < 1 - N.b0 - N.h0 ∧ 0 < N.DG4 - N.D023 ∧
    (N.s < 1 ∨ N.D234 < 1) ∧
    0 < N.f012.f (x 3 + N.u2346 x) - N.f012.f (x 3) ∧
    N.f015.f (x 3 + N.u2346 x) - N.f015.f (x 3) < 0 ∧
    N.f035.f (x 3 + N.u2346 x) - N.f035.f (x 3) < 0 ∧
    0 < N.f124.f (x 3 + N.u2346 x) - N.f124.f (x 3) ∧
    N.f1456.f (x 3 + N.u2346 x) - N.f1456.f (x 3) < 0 ∧
    0 < N.f234.f (x 3 + N.u2346 x) - N.f234.f (x 3) ∧
    N.f356.f (x 3 + N.u2346 x) - N.f356.f (x 3) < 0 ∧
    ∃ lam mu eta : ℝ, 0 < lam ∧ lam < 1 ∧ 0 < mu ∧ mu < 1 ∧ 0 < eta ∧
      lam • x 1 + (1 - lam) • x 3 = mu • x 0 + (1 - mu) • x 4 + eta • N.u2346 x

/-- The `t = 1` pair-D (`W14 x F124xF346`) closing hypothesis bundle on `NF29 x` (excluding `g34 ≤ 0`
and `¬ LexAny29`, which `Hole29` already carries). The three shape inequalities `0 < N.b2 + N.h2`,
`N.b2 + N.h2 < 1`, and `0 < -N.a2 + N.b2 * N.s - N.b2 - N.h2 + 1` are sample facts (true on
`93 / 93` `t = 1` shapes, not implied by `NF29`). -/
def TDHyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  N.t = 1 ∧ 0 < N.dG4 ∧ 0 < 1 - N.b0 - N.h0 ∧
    0 < N.b2 + N.h2 ∧ N.b2 + N.h2 < 1 ∧ 0 < -N.a2 + N.b2 * N.s - N.b2 - N.h2 + 1 ∧
    GenQuad.FrontDet (x 2) (x 5) (x 1) (x 3) (x 1 - x 4) ∧
    GenQuad.FrontDet (x 2) (x 5) (x 1) (x 6) (x 1 - x 4) ∧
    GenQuad.FrontDet (x 3) (x 5) (x 1) (x 6) (x 1 - x 4) ∧
    GenQuad.FrontDet (x 3) (x 5) (x 2) (x 6) (x 1 - x 4) ∧
    ¬ (⟪x 1 - x 6, x 1 - x 4⟫ ≤ ⟪x 2 - x 6, x 1 - x 4⟫ ∧
       ⟪x 1 - x 6, x 1 - x 4⟫ ≤ ⟪x 5 - x 6, x 1 - x 4⟫ ∧
       ⟪x 3 - x 6, x 1 - x 4⟫ ≤ ⟪x 2 - x 6, x 1 - x 4⟫ ∧
       ⟪x 3 - x 6, x 1 - x 4⟫ ≤ ⟪x 5 - x 6, x 1 - x 4⟫) ∧
    ¬ (⟪x 1 - x 6, x 1 - x 4⟫ ≤ ⟪x 2 - x 6, x 1 - x 4⟫ ∧
       ⟪x 1 - x 6, x 1 - x 4⟫ ≤ ⟪x 5 - x 6, x 1 - x 4⟫ ∧
       (0 : ℝ) ≤ ⟪x 2 - x 6, x 1 - x 4⟫ ∧ (0 : ℝ) ≤ ⟪x 5 - x 6, x 1 - x 4⟫) ∧
    ¬ (⟪x 1 - x 6, x 1 - x 4⟫ ≤ ⟪x 3 - x 6, x 1 - x 4⟫ ∧
       ⟪x 1 - x 6, x 1 - x 4⟫ ≤ ⟪x 5 - x 6, x 1 - x 4⟫ ∧
       (0 : ℝ) ≤ ⟪x 3 - x 6, x 1 - x 4⟫ ∧ (0 : ℝ) ≤ ⟪x 5 - x 6, x 1 - x 4⟫) ∧
    GenQuad.FrontDet (x 1) (x 3) (x 2) (x 6) (x 1 - x 4) ∧
    0 < N.f012.f (x 3 + N.u124_346 x) - N.f012.f (x 3) ∧
    N.f015.f (x 3 + N.u124_346 x) - N.f015.f (x 3) < 0 ∧
    0 < N.f023.f (x 3 + N.u124_346 x) - N.f023.f (x 3) ∧
    0 < N.f035.f (x 3 + N.u124_346 x) - N.f035.f (x 3)

/-- Shrunken Type-29 open hole proposition, excluding `T1Hyp` and `TDHyp`. -/
def Hole29R1 (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  Hole29 x N ∧ ¬ (T1Hyp x N ∨ TDHyp x N)

/-- Every point of `Hole29R1` lies in `Hole29`. -/
theorem hole29_of_hole29R1 {x : Fin 7 → ℝ³} {N : NF29 x} (h : Hole29R1 x N) : Hole29 x N :=
  h.1

/-- **Reduction of `Hole29` to `Hole29R1`**: `NF29.t1_closed` and `NF29.t1_D_closed` rule out
`T1Hyp ∨ TDHyp` inside `Hole29`. -/
theorem hole29_reduce {x : Fin 7 → ℝ³} {N : NF29 x} (h : Hole29 x N) : Hole29R1 x N := by
  refine ⟨h, fun hTD => ?_⟩
  rcases hTD with hT | hD
  · rcases hT with ⟨ht, hdG4, hA, hU5, hsD, h012, h015, h035, h124, h1456, h234, h356,
      lam, mu, eta, hlam0, hlam1, hmu0, hmu1, heta, hfront⟩
    exact t1_closed N ht hdG4 hA hU5 hsD h.2.2.1.2.1 h.2.2.1.2.2
      h012 h015 h035 h124 h1456 h234 h356 lam mu eta hlam0 hlam1 hmu0 hmu1 heta hfront
      h.2.2.2.2.2.1
  · rcases hD with ⟨ht, hdG4, hA, hb2h2, hb2h2_lt, hpos,
      hF1235, hF1265, hF1365, hF2365, hM1235, hM1265, hM1365, hF1236, h012, h015, h023, h035⟩
    exact t1_D_closed N ht hdG4 hA hb2h2 hb2h2_lt hpos h.2.2.1.1
      hF1235 hF1265 hF1365 hF2365 hM1235 hM1265 hM1365 hF1236 h012 h015 h023 h035
      h.2.2.2.2.2.1

/-- Main Type-29 reduction leaving `Hole29R1`. -/
theorem type29_rupert_or_hole' {x : Fin 7 → ℝ³} (N : NF29 x)
    (hK1 : K1_29 N) (hZ : ¬ Z29 x) (hOB : OB6 x) :
    IsRupert (univ.image x) ∨ Hole29R1 x N :=
  (type29_rupert_or_hole N hK1 hZ hOB).elim Or.inl (fun h => Or.inr (hole29_reduce h))

private theorem row_of_dir_le' {x : Fin 7 → ℝ³} {N : NF29 x} {i j : Fin 7}
    {q4i q5i Yi q4j q5j Yj v4 v5 : ℝ} {u : ℝ³}
    (hu : v4 • (x 4 - x 6) + v5 • (x 5 - x 6) = S_sp N.s N.t • u)
    (hi : S_sp N.s N.t • (x i - x 6) =
      q4i • (x 4 - x 6) + q5i • (x 5 - x 6) + (S_sp N.s N.t * Yi) • (x 3 - x 6))
    (hj : S_sp N.s N.t • (x j - x 6) =
      q4j • (x 4 - x 6) + q5j • (x 5 - x 6) + (S_sp N.s N.t * Yj) • (x 3 - x 6))
    (hle : ⟪x j, u⟫ ≤ ⟪x i, u⟫) :
    0 ≤ Row_sp (q4i - q4j) (q5i - q5j) (Yi - Yj) v4 v5
      ⟪x 4 - x 6, x 4 - x 6⟫ ⟪x 5 - x 6, x 5 - x 6⟫ ⟪x 4 - x 6, x 5 - x 6⟫
      ⟪x 3 - x 6, x 4 - x 6⟫ ⟪x 3 - x 6, x 5 - x 6⟫ (S_sp N.s N.t) := by
  rw [nf29_row_eq_inner N v4 v5 hi hj, hu, real_inner_smul_right]
  have hdiff : 0 ≤ ⟪x i - x j, u⟫ := by
    rw [inner_sub_left]
    exact sub_nonneg.mpr hle
  have hS : 0 ≤ S_sp N.s N.t := (sub_pos.mpr N.hst).le
  exact mul_nonneg hS (mul_nonneg hS hdiff)

/-- Residual of the `G*` × `F-B` sub-pencil assembly: under `K1a`, `G*`, the `u23Q` `FrontDet`
diagonals, the `bLine` facet signs, the `F-B` branch diagonal + clauses, and `¬ LexAny29`,
either `C_Q2`, `C_Q5+`, or `¬ (0 ≤ m21)` holds (`C_Q1`, `C_Q3`, `C_Q4` are closed; `C_Q5+` stays in
the residual because `B2_diff` has a negative `W21` term so the `W21` multiplier in
`cert_FB_CQ5_pos_eta5_pos` is not unconditionally `≥ 0` as `t → 1`, and its RHS vanishes at
`g45 = 0` under weak `OB6`). -/
theorem gstar_FB_residual {x : Fin 7 → ℝ³} (N : NF29 x)
    (hk : N.a2 < 0) (hh2 : 1 < N.h2) (hh0 : N.h0 < 1) (ht1 : N.t < 1)
    (hU4 : 0 < U4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t)
    (hU5 : 0 < U5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t)
    (hG4 : 0 < G4_sp N.b0 N.h0 N.b2 N.h2) (hb0h0 : 0 < 1 - N.b0 - N.h0)
    (hF0123Q : GenQuad.FrontDet (x 2) (x 6) (x 0) (x 4) (N.u23Q x))
    (hF0124Q : GenQuad.FrontDet (x 2) (x 5) (x 0) (x 4) (N.u23Q x))
    (hF0134Q : GenQuad.FrontDet (x 2) (x 5) (x 0) (x 6) (N.u23Q x))
    (hF0234Q : GenQuad.FrontDet (x 0) (x 6) (x 4) (x 5) (N.u23Q x))
    (hF1234Q : GenQuad.FrontDet (x 2) (x 6) (x 4) (x 5) (N.u23Q x))
    (h035 : 0 < N.v035) (h234 : N.v234 < 0) (h346 : N.v346 < 0) (h356 : 0 < N.v356)
    (hF0123F : GenQuad.FrontDet (x 1) (x 3) (x 2) (x 6) (N.bLine x))
    (hA0124F : GenQuad.LexClause (x 2) (x 5) (x 1) (x 3) (N.bLine x) (x 1 - x 4) (x 3 - x 1))
    (hB0124F : GenQuad.LexClause (x 1) (x 3) (x 2) (x 5) (N.bLine x) (x 1 - x 4) (x 3 - x 1))
    (hA0134F : GenQuad.LexClause (x 2) (x 5) (x 1) (x 6) (N.bLine x) (x 1 - x 4) (x 3 - x 1))
    (hB0134F : GenQuad.LexClause (x 1) (x 6) (x 2) (x 5) (N.bLine x) (x 1 - x 4) (x 3 - x 1))
    (hA0234F : GenQuad.LexClause (x 3) (x 5) (x 1) (x 6) (N.bLine x) (x 1 - x 4) (x 3 - x 1))
    (hB0234F : GenQuad.LexClause (x 1) (x 6) (x 3) (x 5) (N.bLine x) (x 1 - x 4) (x 3 - x 1))
    (hA1234F : GenQuad.LexClause (x 3) (x 5) (x 2) (x 6) (N.bLine x) (x 1 - x 4) (x 3 - x 1))
    (hB1234F : GenQuad.LexClause (x 2) (x 6) (x 3) (x 5) (N.bLine x) (x 1 - x 4) (x 3 - x 1))
    (hnf : ¬ Minimality.H29.LexAny29 (s0x_fac29 N.facets)) :
    (⟪x 4, N.u23Q x⟫ ≤ ⟪x 0, N.u23Q x⟫ ∧ ⟪x 4, N.u23Q x⟫ ≤ ⟪x 6, N.u23Q x⟫ ∧
      ⟪x 5, N.u23Q x⟫ ≤ ⟪x 0, N.u23Q x⟫ ∧ ⟪x 5, N.u23Q x⟫ ≤ ⟪x 6, N.u23Q x⟫) ∨
    (⟪x 0, N.u23Q x⟫ ≤ ⟪x 2, N.u23Q x⟫ ∧ ⟪x 0, N.u23Q x⟫ ≤ ⟪x 5, N.u23Q x⟫ ∧
      ⟪x 6, N.u23Q x⟫ ≤ ⟪x 2, N.u23Q x⟫ ∧ ⟪x 6, N.u23Q x⟫ ≤ ⟪x 5, N.u23Q x⟫) ∨
    ¬ (0 ≤ m21_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t) := by
  have hdG4 : 0 < N.dG4 := by dsimp [NF29.dG4]; exact hG4
  have hS : 0 < S_sp N.s N.t := sub_pos.mpr N.hst
  have hG55 : 0 < ⟪x 5 - x 6, x 5 - x 6⟫ :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr (fun h => absurd (N.inj h) (by decide)))
  have hqc := nf29_q_coords N
  dsimp only at hqc
  have h0c : S_sp N.s N.t • (x 0 - x 6) =
      D035_sp N.a0 N.b0 N.h0 N.s N.t • (x 4 - x 6) +
      P0_sp N.a0 N.b0 N.h0 N.s N.t • (x 5 - x 6) + (S_sp N.s N.t * N.h0) • (x 3 - x 6) := hqc.1
  have h2c : S_sp N.s N.t • (x 2 - x 6) =
      P2_sp N.a2 N.b2 N.h2 N.s N.t • (x 4 - x 6) +
      D234_sp N.a2 N.b2 N.h2 N.s N.t • (x 5 - x 6) + (S_sp N.s N.t * N.h2) • (x 3 - x 6) := hqc.2.2
  have h4c : S_sp N.s N.t • (x 4 - x 6) =
      S_sp N.s N.t • (x 4 - x 6) + (0 : ℝ) • (x 5 - x 6) + (S_sp N.s N.t * 0) • (x 3 - x 6) := by module
  have h5c : S_sp N.s N.t • (x 5 - x 6) =
      (0 : ℝ) • (x 4 - x 6) + S_sp N.s N.t • (x 5 - x 6) + (S_sp N.s N.t * 0) • (x 3 - x 6) := by module
  have h6c : S_sp N.s N.t • (x 6 - x 6) =
      (0 : ℝ) • (x 4 - x 6) + (0 : ℝ) • (x 5 - x 6) + (S_sp N.s N.t * 0) • (x 3 - x 6) := by module
  obtain ⟨r21, r23⟩ := w14_of_not_lexAny29 N hk ht1 hdG4 hb0h0 hnf
  have r12 := fb_of_not_lexAny29 N (by linarith) h035 h234 h346 h356
    hF0123F hA0124F hB0124F hA0134F hB0134F hA0234F hB0234F hA1234F hB1234F hnf
  rcases u23Q_cones_of_not_lexAny29 N hk hh2 hh0 hdG4 hU4 hU5
      hF0123Q hF0124Q hF0134Q hF0234Q hF1234Q hnf with
    hM3 | hM4 | hM5 | hM2 | hM1
  · by_cases hm21 : 0 ≤ m21_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t
    · have q20 := row_of_dir_le' (nf29_vQ_eq_u23Q N) h2c h0c hM3.1
      have q24 := row_of_dir_le' (nf29_vQ_eq_u23Q N) h2c h4c hM3.2.2.1
      simp only [sub_zero] at q24
      have hP4 : 0 < P4C_sp N.b0 N.h0 N.b2 N.h2 := by dsimp [P4C_sp]; linarith [N.hF4]
      have hP5 : 0 < P5C_sp N.a0 N.h0 N.a2 N.h2 := by dsimp [P5C_sp]; linarith [N.hF5]
      exact False.elim (cert_FB_CQ34_false N.ha0 hk N.hb2 N.hs ht1 hh2 hh0 hP4 hP5 N.hDD
        hG4 hU4 hm21 hS hG55 q20 q24 r21 r23 r12)
    · exact Or.inr (Or.inr hm21)
  · by_cases hm21 : 0 ≤ m21_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t
    · have q20 := row_of_dir_le' (nf29_vQ_eq_u23Q N) h2c h0c hM4.1
      have q24 := row_of_dir_le' (nf29_vQ_eq_u23Q N) h2c h4c hM4.2.2.1
      simp only [sub_zero] at q24
      have hP4 : 0 < P4C_sp N.b0 N.h0 N.b2 N.h2 := by dsimp [P4C_sp]; linarith [N.hF4]
      have hP5 : 0 < P5C_sp N.a0 N.h0 N.a2 N.h2 := by dsimp [P5C_sp]; linarith [N.hF5]
      exact False.elim (cert_FB_CQ34_false N.ha0 hk N.hb2 N.hs ht1 hh2 hh0 hP4 hP5 N.hDD
        hG4 hU4 hm21 hS hG55 q20 q24 r21 r23 r12)
    · exact Or.inr (Or.inr hm21)
  · exact Or.inr (Or.inl hM5)
  · exact Or.inl hM2
  · have r24 := row_of_dir_le' (nf29_vQ_eq_u23Q N) h2c h4c hM1.1
    have q4n := row_of_dir_le' (nf29_vQ_eq_u23Q N) h6c h4c hM1.2.1
    have q5n := row_of_dir_le' (nf29_vQ_eq_u23Q N) h6c h5c hM1.2.2.2
    simp only [sub_zero, zero_sub] at r24 q4n q5n
    have hP4 : 0 < P4C_sp N.b0 N.h0 N.b2 N.h2 := by dsimp [P4C_sp]; linarith [N.hF4]
    have hqA4 : 0 < qA4_sp N.a2 N.b2 N.s N.t := by
      dsimp [qA4_sp]
      nlinarith [mul_pos (neg_pos.mpr hk) (sub_pos.mpr ht1), mul_pos (neg_pos.mpr N.hb2) N.hs]
    exact False.elim (cert_FB_CQ1_false hh2 hh0 N.ht ht1 hU4 hU5 hG4 hb0h0 hqA4 N.hDD hP4
      hS hG55 r24 q4n q5n r21 r23 r12)

/-- Hypothesis bundle for the `G*` × `F-B` sub-pencil closure (`C_Q1`, `C_Q3`, `C_Q4`), excluding
`C_Q2`, `C_Q5+`, and `¬ (0 ≤ m21)` (where `0 ≤ m21` is a SAMPLE fact, false outside quadrant II
e.g. `neg21_0`). -/
def GFBHyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  N.a2 < 0 ∧ 1 < N.h2 ∧ N.h0 < 1 ∧ N.t < 1 ∧
    0 < U4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t ∧
    0 < U5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t ∧
    0 < G4_sp N.b0 N.h0 N.b2 N.h2 ∧ 0 < 1 - N.b0 - N.h0 ∧
    0 ≤ m21_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t ∧
    GenQuad.FrontDet (x 2) (x 6) (x 0) (x 4) (N.u23Q x) ∧
    GenQuad.FrontDet (x 2) (x 5) (x 0) (x 4) (N.u23Q x) ∧
    GenQuad.FrontDet (x 2) (x 5) (x 0) (x 6) (N.u23Q x) ∧
    GenQuad.FrontDet (x 0) (x 6) (x 4) (x 5) (N.u23Q x) ∧
    GenQuad.FrontDet (x 2) (x 6) (x 4) (x 5) (N.u23Q x) ∧
    0 < N.v035 ∧ N.v234 < 0 ∧ N.v346 < 0 ∧ 0 < N.v356 ∧
    GenQuad.FrontDet (x 1) (x 3) (x 2) (x 6) (N.bLine x) ∧
    GenQuad.LexClause (x 2) (x 5) (x 1) (x 3) (N.bLine x) (x 1 - x 4) (x 3 - x 1) ∧
    GenQuad.LexClause (x 1) (x 3) (x 2) (x 5) (N.bLine x) (x 1 - x 4) (x 3 - x 1) ∧
    GenQuad.LexClause (x 2) (x 5) (x 1) (x 6) (N.bLine x) (x 1 - x 4) (x 3 - x 1) ∧
    GenQuad.LexClause (x 1) (x 6) (x 2) (x 5) (N.bLine x) (x 1 - x 4) (x 3 - x 1) ∧
    GenQuad.LexClause (x 3) (x 5) (x 1) (x 6) (N.bLine x) (x 1 - x 4) (x 3 - x 1) ∧
    GenQuad.LexClause (x 1) (x 6) (x 3) (x 5) (N.bLine x) (x 1 - x 4) (x 3 - x 1) ∧
    GenQuad.LexClause (x 3) (x 5) (x 2) (x 6) (N.bLine x) (x 1 - x 4) (x 3 - x 1) ∧
    GenQuad.LexClause (x 2) (x 6) (x 3) (x 5) (N.bLine x) (x 1 - x 4) (x 3 - x 1) ∧
    ¬ (⟪x 4, N.u23Q x⟫ ≤ ⟪x 0, N.u23Q x⟫ ∧ ⟪x 4, N.u23Q x⟫ ≤ ⟪x 6, N.u23Q x⟫ ∧
       ⟪x 5, N.u23Q x⟫ ≤ ⟪x 0, N.u23Q x⟫ ∧ ⟪x 5, N.u23Q x⟫ ≤ ⟪x 6, N.u23Q x⟫) ∧
    ¬ (⟪x 0, N.u23Q x⟫ ≤ ⟪x 2, N.u23Q x⟫ ∧ ⟪x 0, N.u23Q x⟫ ≤ ⟪x 5, N.u23Q x⟫ ∧
       ⟪x 6, N.u23Q x⟫ ≤ ⟪x 2, N.u23Q x⟫ ∧ ⟪x 6, N.u23Q x⟫ ≤ ⟪x 5, N.u23Q x⟫)

/-- Shrunken Type-29 open hole proposition, excluding `GFBHyp` from `Hole29R1`. -/
def Hole29R2 (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  Hole29R1 x N ∧ ¬ GFBHyp x N

/-- Every point of `Hole29R2` lies in `Hole29`. -/
theorem hole29_of_hole29R2 {x : Fin 7 → ℝ³} {N : NF29 x} (h : Hole29R2 x N) : Hole29 x N :=
  hole29_of_hole29R1 h.1

/-- **Reduction of `Hole29R1` to `Hole29R2`**: `gstar_FB_residual` rules out `GFBHyp` inside
`Hole29R1`. -/
theorem hole29R1_reduce {x : Fin 7 → ℝ³} {N : NF29 x} (h : Hole29R1 x N) : Hole29R2 x N := by
  refine ⟨h, fun hG => ?_⟩
  rcases hG with ⟨hk, hh2, hh0, ht1, hU4, hU5, hG4, hb0h0, hm21,
    hF0123Q, hF0124Q, hF0134Q, hF0234Q, hF1234Q,
    h035, h234, h346, h356, hF0123F, hA0124F, hB0124F, hA0134F, hB0134F,
    hA0234F, hB0234F, hA1234F, hB1234F, hnotQ2, hnotQ5⟩
  rcases gstar_FB_residual N hk hh2 hh0 ht1 hU4 hU5 hG4 hb0h0
      hF0123Q hF0124Q hF0134Q hF0234Q hF1234Q h035 h234 h346 h356
      hF0123F hA0124F hB0124F hA0134F hB0134F hA0234F hB0234F hA1234F hB1234F
      h.1.2.2.2.2.2.1 with hQ2 | hQ5 | hnotm21
  · exact hnotQ2 hQ2
  · exact hnotQ5 hQ5
  · exact hnotm21 hm21

/-- Main Type-29 reduction leaving `Hole29R2`. -/
theorem type29_rupert_or_hole'' {x : Fin 7 → ℝ³} (N : NF29 x)
    (hK1 : K1_29 N) (hZ : ¬ Z29 x) (hOB : OB6 x) :
    IsRupert (univ.image x) ∨ Hole29R2 x N :=
  (type29_rupert_or_hole' N hK1 hZ hOB).elim Or.inl (fun h => Or.inr (hole29R1_reduce h))

end Minimality.H29
