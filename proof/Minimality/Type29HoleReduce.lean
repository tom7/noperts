module

public import Minimality.Type29Hole
public import Minimality.Type29T1Close
public import Minimality.Type29T1Res
public import Minimality.Type29Exact
public import Minimality.Type29T1Pair
public import Minimality.Type29Quad
public import Minimality.Type29SubPencil
public import Minimality.Type29Single
public import Minimality.Type29Pair2
public import Minimality.Type29Pair5
public import Minimality.Type29Tri2
public import Minimality.Type29Tri3
public import Minimality.Type29Tri10
public import Minimality.Type29Tri8
public import Minimality.Type29Tri7
public import Minimality.Type29Tri6
public import Minimality.Type29Tri5
public import Minimality.Type29Tri1
public import Minimality.Type29Tri9
public import Minimality.Type29Tri4

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.Gen Minimality.H21 Minimality.H29K1 Minimality.H29S Minimality.NF29

namespace Minimality.H29

/-!
# Type 29: Reduction of `Hole29` to `Hole29R1`

Excludes the `t = 1` K1a cell closed by `NF29.t1_closed'` (`T1Hyp`) from `Hole29`, yielding
`Hole29R1 x N := Hole29 x N ∧ ¬ T1Hyp x N`. (A former pair-D exclusion `TDHyp` was empty: its
conjunct `0 < f035` at the `F124xF346` view contradicts the shape facts; removed with `t1_D_closed`.)
-/

/-- Hypothesis bundle for `NF29.t1_closed'` (excluding `OB6`'s `hg34, hg35, hg45`, `¬ Z29`, the K1
sign pattern and `¬ LexAny29`, which are already supplied by `Hole29`). The former sample fact
`s < 1 ∨ D234 < 1` (false on part of the cell) is gone: its escape is closed by the `F023 x F356`
leaf `NF29.lexAny29_F023F356` (K1b is empty there, `NF29.t1r_K1b_false`). -/
def T1Hyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  N.t = 1 ∧ 0 < N.dG4 ∧ 0 < 1 - N.b0 - N.h0 ∧ 0 < N.DG4 - N.D023 ∧
    0 < N.f012.f (x 3 + N.u2346 x) - N.f012.f (x 3) ∧
    N.f015.f (x 3 + N.u2346 x) - N.f015.f (x 3) < 0 ∧
    N.f035.f (x 3 + N.u2346 x) - N.f035.f (x 3) < 0 ∧
    0 < N.f124.f (x 3 + N.u2346 x) - N.f124.f (x 3) ∧
    N.f1456.f (x 3 + N.u2346 x) - N.f1456.f (x 3) < 0 ∧
    0 < N.f234.f (x 3 + N.u2346 x) - N.f234.f (x 3) ∧
    N.f356.f (x 3 + N.u2346 x) - N.f356.f (x 3) < 0 ∧
    ∃ lam mu eta : ℝ, 0 < lam ∧ lam < 1 ∧ 0 < mu ∧ mu < 1 ∧ 0 < eta ∧
      lam • x 1 + (1 - lam) • x 3 = mu • x 0 + (1 - mu) • x 4 + eta • N.u2346 x

/-- Shrunken Type-29 open hole proposition, excluding `T1Hyp`. -/
def Hole29R1 (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  Hole29 x N ∧ ¬ T1Hyp x N

/-- Every point of `Hole29R1` lies in `Hole29`. -/
theorem hole29_of_hole29R1 {x : Fin 7 → ℝ³} {N : NF29 x} (h : Hole29R1 x N) : Hole29 x N :=
  h.1

/-- **Reduction of `Hole29` to `Hole29R1`**: `NF29.t1_closed'` rules out `T1Hyp` inside `Hole29`. -/
theorem hole29_reduce {x : Fin 7 → ℝ³} {N : NF29 x} (h : Hole29 x N) : Hole29R1 x N := by
  refine ⟨h, fun hT => ?_⟩
  rcases hT with ⟨ht, hdG4, hA, hU5, h012, h015, h035, h124, h1456, h234, h356,
    lam, mu, eta, hlam0, hlam1, hmu0, hmu1, heta, hfront⟩
  exact t1_closed' N ht (h.1.imp (fun k => ⟨k.1, k.2.1⟩) (fun k => ⟨k.1, k.2.1⟩)) hdG4 hA hU5
    h.2.2.1.1 h.2.1 h.2.2.1.2.1 h.2.2.1.2.2
    h012 h015 h035 h124 h1456 h234 h356 lam mu eta hlam0 hlam1 hmu0 hmu1 heta hfront
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

/-- K1a single-view closure hypotheses at `x 0 - x 1` (`PL29.lexAny29_K1a_e01`): facings and distinct depths. -/
def E01Hyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  N.a2 < 0 ∧ ⟪(s0x_fac29 N.facets).N 6, x 0 - x 1⟫ < 0 ∧ ⟪(s0x_fac29 N.facets).N 8, x 0 - x 1⟫ < 0 ∧
    ∀ i ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 0 - x 1⟫ ≠ ⟪x j, x 0 - x 1⟫

/-- K1a single-view closure hypotheses at `x 2 - x 4` (`PL29.lexAny29_K1a_e24`): facings and distinct depths. -/
def E24Hyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  0 < N.b0 ∧ ⟪(s0x_fac29 N.facets).N 1, x 2 - x 4⟫ < 0 ∧ ⟪(s0x_fac29 N.facets).N 3, x 2 - x 4⟫ < 0 ∧
    ∀ i ∈ ({0, 1, 2, 3, 4} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 2 - x 4⟫ ≠ ⟪x j, x 2 - x 4⟫

/-- Shrunken Type-29 open hole proposition, excluding the two K1a single-view cells (PAIRLEAN29). -/
def Hole29R3 (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  Hole29R2 x N ∧ ¬ E01Hyp x N ∧ ¬ E24Hyp x N

/-- Every point of `Hole29R3` lies in `Hole29`. -/
theorem hole29_of_hole29R3 {x : Fin 7 → ℝ³} {N : NF29 x} (h : Hole29R3 x N) : Hole29 x N :=
  hole29_of_hole29R2 h.1

/-- **Reduction of `Hole29R2` to `Hole29R3`**: `PL29.lexAny29_K1a_e01` / `_e24` against `¬ LexAny29`. -/
theorem hole29R2_reduce {x : Fin 7 → ℝ³} {N : NF29 x} (h : Hole29R2 x N) : Hole29R3 x N := by
  have hnl := (hole29_of_hole29R2 h).2.2.2.2.2.1
  refine ⟨h, ?_, ?_⟩
  · rintro ⟨ha2, a, b, c⟩
    exact hnl (PL29.lexAny29_K1a_e01 N ha2 a b c)
  · rintro ⟨hb0, a, b, c⟩
    exact hnl (PL29.lexAny29_K1a_e24 N hb0 a b c)

/-- Main Type-29 reduction leaving `Hole29R3`. -/
theorem type29_rupert_or_hole''' {x : Fin 7 → ℝ³} (N : NF29 x)
    (hK1 : K1_29 N) (hZ : ¬ Z29 x) (hOB : OB6 x) :
    IsRupert (univ.image x) ∨ Hole29R3 x N :=
  (type29_rupert_or_hole'' N hK1 hZ hOB).elim Or.inl (fun h => Or.inr (hole29R2_reduce h))

/-! ### SINGLE29: sixteen more single-view cells (`Type29Single.lean`, SINGLE29 part) -/

/-- Single-view cell `e05b` (SINGLE29; `PL29.lexAny_e05b`, view `x 0 - x 5`, K1b). -/
def E05bHyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  0 < N.a2 ∧
    ⟪(s0x_fac29 N.facets).N 4, x 0 - x 5⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 6, x 0 - x 5⟫ < 0 ∧
    ∀ i ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 0 - x 5⟫ ≠ ⟪x j, x 0 - x 5⟫

/-- Single-view cell `e12b` (SINGLE29; `PL29.lexAny_e12b`, view `x 1 - x 2`, K1b). -/
def E12bHyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  N.b0 < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 3, x 1 - x 2⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 7, x 1 - x 2⟫ ∧
    ∀ i ∈ ({0, 1, 2, 3, 4} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 1 - x 2⟫ ≠ ⟪x j, x 1 - x 2⟫

/-- Single-view cell `e02a` (SINGLE29; `PL29.lexAny_e02a`, view `x 0 - x 2`, K1a). -/
def E02aHyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  0 < N.b0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 5, x 0 - x 2⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 7, x 0 - x 2⟫ ∧
    ∀ i ∈ ({0, 1, 2, 3, 4} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 0 - x 2⟫ ≠ ⟪x j, x 0 - x 2⟫

/-- Single-view cell `e15a` (SINGLE29; `PL29.lexAny_e15a`, view `x 1 - x 5`, K1a). -/
def E15aHyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  N.V < 0 ∧
    ⟪(s0x_fac29 N.facets).N 2, x 1 - x 5⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 6, x 1 - x 5⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 7, x 1 - x 5⟫ < 0 ∧
    0 < PL29.PlaneSide x 2 5 6 0 1 ∧
    ∀ i ∈ ({0, 1, 2, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 1 - x 5⟫ ≠ ⟪x j, x 1 - x 5⟫

/-- Single-view cell `e15a2` (SINGLE29; `PL29.lexAny_e15a2`, view `x 1 - x 5`, K1a). -/
def E15a2Hyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  0 < N.b0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 2, x 1 - x 5⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 7, x 1 - x 5⟫ ∧
    ∀ i ∈ ({0, 1, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 1 - x 5⟫ ≠ ⟪x j, x 1 - x 5⟫

/-- Single-view cell `e02b` (SINGLE29; `PL29.lexAny_e02b`, view `x 0 - x 2`, K1b). -/
def E02bHyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  0 < N.a2 ∧
    ⟪(s0x_fac29 N.facets).N 5, x 0 - x 2⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 8, x 0 - x 2⟫ < 0 ∧
    ∀ i ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 0 - x 2⟫ ≠ ⟪x j, x 0 - x 2⟫

/-- Single-view cell `e14b` (SINGLE29; `PL29.lexAny_e14b`, view `x 1 - x 4`, K1b). -/
def E14bHyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  0 < N.V ∧
    ⟪(s0x_fac29 N.facets).N 2, x 1 - x 4⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 3, x 1 - x 4⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 8, x 1 - x 4⟫ < 0 ∧
    PL29.PlaneSide x 2 4 6 0 1 < 0 ∧
    ∀ i ∈ ({0, 1, 2, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 1 - x 4⟫ ≠ ⟪x j, x 1 - x 4⟫

/-- Single-view cell `e14b2` (SINGLE29; `PL29.lexAny_e14b2`, view `x 1 - x 4`, K1b). -/
def E14b2Hyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  0 < N.a2 ∧
    0 < ⟪(s0x_fac29 N.facets).N 2, x 1 - x 4⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 8, x 1 - x 4⟫ ∧
    ∀ i ∈ ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 1 - x 4⟫ ≠ ⟪x j, x 1 - x 4⟫

/-- Single-view cell `e15a3` (SINGLE29; `PL29.lexAny_e15a3`, view `x 1 - x 5`, K1a). -/
def E15a3Hyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  0 < N.b0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 2, x 1 - x 5⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 6, x 1 - x 5⟫ ∧
    ⟪(s0x_fac29 N.facets).N 7, x 1 - x 5⟫ < 0 ∧
    ∀ i ∈ ({0, 1, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 1 - x 5⟫ ≠ ⟪x j, x 1 - x 5⟫

/-- Single-view cell `e14b3` (SINGLE29; `PL29.lexAny_e14b3`, view `x 1 - x 4`, K1b). -/
def E14b3Hyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  0 < N.a2 ∧
    0 < ⟪(s0x_fac29 N.facets).N 2, x 1 - x 4⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 3, x 1 - x 4⟫ ∧
    ⟪(s0x_fac29 N.facets).N 8, x 1 - x 4⟫ < 0 ∧
    ∀ i ∈ ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 1 - x 4⟫ ≠ ⟪x j, x 1 - x 4⟫

/-- Single-view cell `e24a2` (SINGLE29; `PL29.lexAny_e24a2`, view `x 2 - x 4`, K1a). -/
def E24a2Hyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  N.a2 < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 1, x 2 - x 4⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 3, x 2 - x 4⟫ ∧
    ⟪(s0x_fac29 N.facets).N 8, x 2 - x 4⟫ < 0 ∧
    ∀ i ∈ ({1, 2, 3, 4, 5} : Finset (Fin 7)), ∀ j ∈ ({1, 2, 3, 4, 5} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 2 - x 4⟫ ≠ ⟪x j, x 2 - x 4⟫

/-- Single-view cell `e05b2` (SINGLE29; `PL29.lexAny_e05b2`, view `x 0 - x 5`, K1b). -/
def E05b2Hyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  N.b0 < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 4, x 0 - x 5⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 6, x 0 - x 5⟫ ∧
    ⟪(s0x_fac29 N.facets).N 7, x 0 - x 5⟫ < 0 ∧
    ∀ i ∈ ({0, 1, 3, 4, 5} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 3, 4, 5} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 0 - x 5⟫ ≠ ⟪x j, x 0 - x 5⟫

/-- Single-view cell `e03a` (SINGLE29; `PL29.lexAny_e03a`, view `x 0 - x 3`, K1a). -/
def E03aHyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  N.a2 < 0 ∧
    ⟪(s0x_fac29 N.facets).N 4, x 0 - x 3⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 5, x 0 - x 3⟫ < 0 ∧
    ∀ i ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 0 - x 3⟫ ≠ ⟪x j, x 0 - x 3⟫

/-- Single-view cell `e23b` (SINGLE29; `PL29.lexAny_e23b`, view `x 2 - x 3`, K1b). -/
def E23bHyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  N.b0 < 0 ∧
    ⟪(s0x_fac29 N.facets).N 1, x 2 - x 3⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 5, x 2 - x 3⟫ < 0 ∧
    ∀ i ∈ ({0, 1, 2, 3, 4} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 2 - x 3⟫ ≠ ⟪x j, x 2 - x 3⟫

/-- Single-view cell `l1456x234` (SINGLE29; `PL29.lexAny_l1456x234`, view `cross N1456 N234`, no class fact). -/
def L1456x234Hyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  ⟪(s0x_fac29 N.facets).N 1, PL29.lv29 N 5 6⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 3, PL29.lv29 N 5 6⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 4, PL29.lv29 N 5 6⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 7, PL29.lv29 N 5 6⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 8, PL29.lv29 N 5 6⟫ ∧
    ∀ i ∈ ({1, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({1, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, PL29.lv29 N 5 6⟫ ≠ ⟪x j, PL29.lv29 N 5 6⟫

/-- Single-view cell `l035x1456` (SINGLE29; `PL29.lexAny_l035x1456`, view `cross N035 N1456`, no class fact). -/
def L035x1456Hyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  ⟪(s0x_fac29 N.facets).N 1, PL29.lv29 N 3 5⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 4, PL29.lv29 N 3 5⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 6, PL29.lv29 N 3 5⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 7, PL29.lv29 N 3 5⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 8, PL29.lv29 N 3 5⟫ ∧
    ∀ i ∈ ({1, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({1, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, PL29.lv29 N 3 5⟫ ≠ ⟪x j, PL29.lv29 N 3 5⟫


/-- Union of the SINGLE29 single-view cells. -/
def Single29Hyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  E05bHyp x N ∨
    E12bHyp x N ∨
    E02aHyp x N ∨
    E15aHyp x N ∨
    E15a2Hyp x N ∨
    E02bHyp x N ∨
    E14bHyp x N ∨
    E14b2Hyp x N ∨
    E15a3Hyp x N ∨
    E14b3Hyp x N ∨
    E24a2Hyp x N ∨
    E05b2Hyp x N ∨
    E03aHyp x N ∨
    E23bHyp x N ∨
    L1456x234Hyp x N ∨
    L035x1456Hyp x N

/-- Shrunken Type-29 open hole proposition, excluding the SINGLE29 single-view cells. -/
def Hole29R4 (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  Hole29R3 x N ∧ ¬ Single29Hyp x N

/-- Every point of `Hole29R4` lies in `Hole29`. -/
theorem hole29_of_hole29R4 {x : Fin 7 → ℝ³} {N : NF29 x} (h : Hole29R4 x N) : Hole29 x N :=
  hole29_of_hole29R3 h.1

/-- **Reduction of `Hole29R3` to `Hole29R4`**: the SINGLE29 cells (`PL29.lexAny29_*`) against
`¬ LexAny29`. -/
theorem hole29R3_reduce {x : Fin 7 → ℝ³} {N : NF29 x} (h : Hole29R3 x N) : Hole29R4 x N := by
  have hnl := (hole29_of_hole29R3 h).2.2.2.2.2.1
  refine ⟨h, ?_⟩
  rintro (⟨h1, h2, h3, h4⟩
    | ⟨h1, h2, h3, h4⟩
    | ⟨h1, h2, h3, h4⟩
    | ⟨h1, h2, h3, h4, h5, h6⟩
    | ⟨h1, h2, h3, h4⟩
    | ⟨h1, h2, h3, h4⟩
    | ⟨h1, h2, h3, h4, h5, h6⟩
    | ⟨h1, h2, h3, h4⟩
    | ⟨h1, h2, h3, h4, h5⟩
    | ⟨h1, h2, h3, h4, h5⟩
    | ⟨h1, h2, h3, h4, h5⟩
    | ⟨h1, h2, h3, h4, h5⟩
    | ⟨h1, h2, h3, h4⟩
    | ⟨h1, h2, h3, h4⟩
    | ⟨h1, h2, h3, h4, h5, h6⟩
    | ⟨h1, h2, h3, h4, h5, h6⟩)
  · exact hnl (PL29.lexAny29_K1b_e05 N h1 h2 h3 h4)
  · exact hnl (PL29.lexAny29_K1b_e12 N h1 h2 h3 h4)
  · exact hnl (PL29.lexAny29_K1a_e02 N h1 h2 h3 h4)
  · exact hnl (PL29.lexAny29_K1a_e15 N h1 h2 h3 h4 h5 h6)
  · exact hnl (PL29.lexAny29_K1a_e15_2 N h1 h2 h3 h4)
  · exact hnl (PL29.lexAny29_K1b_e02 N h1 h2 h3 h4)
  · exact hnl (PL29.lexAny29_K1b_e14 N h1 h2 h3 h4 h5 h6)
  · exact hnl (PL29.lexAny29_K1b_e14_2 N h1 h2 h3 h4)
  · exact hnl (PL29.lexAny29_K1a_e15_3 N h1 h2 h3 h4 h5)
  · exact hnl (PL29.lexAny29_K1b_e14_3 N h1 h2 h3 h4 h5)
  · exact hnl (PL29.lexAny29_K1a_e24_2 N h1 h2 h3 h4 h5)
  · exact hnl (PL29.lexAny29_K1b_e05_2 N h1 h2 h3 h4 h5)
  · exact hnl (PL29.lexAny29_K1a_e03 N h1 h2 h3 h4)
  · exact hnl (PL29.lexAny29_K1b_e23 N h1 h2 h3 h4)
  · exact hnl (PL29.lexAny29_l1456x234 N h1 h2 h3 h4 h5 h6)
  · exact hnl (PL29.lexAny29_l035x1456 N h1 h2 h3 h4 h5 h6)

/-- Main Type-29 reduction leaving `Hole29R4`. -/
theorem type29_rupert_or_hole'''' {x : Fin 7 → ℝ³} (N : NF29 x)
    (hK1 : K1_29 N) (hZ : ¬ Z29 x) (hOB : OB6 x) :
    IsRupert (univ.image x) ∨ Hole29R4 x N :=
  (type29_rupert_or_hole''' N hK1 hZ hOB).elim Or.inl (fun h => Or.inr (hole29R3_reduce h))

/-! ### PAIR29: two-view (pair) closures (`Type29Pair*.lean`) -/

/-- Pair `w1` + `x 5 - x 6` (lines F124xF346, F1456xF356) (PAIR29; `PL29.lexAny_pair1`). -/
def Pair1Hyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  N.a2 < 0 ∧
    ⟪(s0x_fac29 N.facets).N 0, PL29.lv29 N 4 7⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 5, PL29.lv29 N 4 7⟫ ∧
    ⟪(s0x_fac29 N.facets).N 6, PL29.lv29 N 4 7⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 8, PL29.lv29 N 4 7⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 0, x 5 - x 6⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 2, x 5 - x 6⟫ ∧
    ⟪(s0x_fac29 N.facets).N 4, x 5 - x 6⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 6, x 5 - x 6⟫ < 0 ∧
    (∀ i ∈ ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, PL29.lv29 N 4 7⟫ ≠ ⟪x j, PL29.lv29 N 4 7⟫) ∧
    ∀ i ∈ ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 5 - x 6⟫ ≠ ⟪x j, x 5 - x 6⟫

/-- Pair `x 1 - x 2` + `x 5 - x 6` (lines F012xF124, F1456xF356) (PAIR29; `PL29.lexAny_pair2`). -/
def Pair2Hyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  N.V < 0 ∧
    ⟪(s0x_fac29 N.facets).N 3, x 1 - x 2⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 7, x 1 - x 2⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 8, x 1 - x 2⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 0, x 5 - x 6⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 2, x 5 - x 6⟫ ∧
    ⟪(s0x_fac29 N.facets).N 4, x 5 - x 6⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 6, x 5 - x 6⟫ < 0 ∧
    0 < PL29.PlaneSide x 2 5 6 0 1 ∧
    0 < PL29.PlaneSide x 2 3 6 1 5 ∧
    0 < PL29.PlaneSide x 2 3 5 1 6 ∧
    (∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 1 - x 2⟫ ≠ ⟪x j, x 1 - x 2⟫) ∧
    ∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 5 - x 6⟫ ≠ ⟪x j, x 5 - x 6⟫

/-- Pair `w1` + `x 4 - x 6` (lines F015xF356, F1456xF346) (PAIR29; `PL29.lexAny_pair3`). -/
def Pair3Hyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  N.b0 < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 0, PL29.lv29 N 1 8⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 3, PL29.lv29 N 1 8⟫ ∧
    ⟪(s0x_fac29 N.facets).N 5, PL29.lv29 N 1 8⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 7, PL29.lv29 N 1 8⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 0, x 4 - x 6⟫ ∧
    ⟪(s0x_fac29 N.facets).N 1, x 4 - x 6⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 2, x 4 - x 6⟫ ∧
    ⟪(s0x_fac29 N.facets).N 3, x 4 - x 6⟫ < 0 ∧
    (∀ i ∈ ({0, 1, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, PL29.lv29 N 1 8⟫ ≠ ⟪x j, PL29.lv29 N 1 8⟫) ∧
    ∀ i ∈ ({0, 1, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 4 - x 6⟫ ≠ ⟪x j, x 4 - x 6⟫

/-- Single view `x 3 - x 6` (line F346xF356) (PAIR29; `PL29.lexAny_pair4`, no class fact). -/
def Pair4Hyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  0 < ⟪(s0x_fac29 N.facets).N 1, x 3 - x 6⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 4, x 3 - x 6⟫ ∧
    ∀ i ∈ ({0, 1, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 3 - x 6⟫ ≠ ⟪x j, x 3 - x 6⟫

/-- Pair `w1` + `x 1 - x 4` (lines F035xF346, F124xF1456) (PAIR29; `PL29.lexAny_pair5`). -/
def Pair5Hyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  0 < N.b0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 0, PL29.lv29 N 3 7⟫ ∧
    ⟪(s0x_fac29 N.facets).N 1, PL29.lv29 N 3 7⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 2, PL29.lv29 N 3 7⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 4, PL29.lv29 N 3 7⟫ ∧
    ⟪(s0x_fac29 N.facets).N 5, PL29.lv29 N 3 7⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 6, PL29.lv29 N 3 7⟫ ∧
    ⟪(s0x_fac29 N.facets).N 8, PL29.lv29 N 3 7⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 2, x 1 - x 4⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 8, x 1 - x 4⟫ ∧
    PL29.PlaneSide x 2 3 6 1 4 < 0 ∧
    (∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, PL29.lv29 N 3 7⟫ ≠ ⟪x j, PL29.lv29 N 3 7⟫) ∧
    ∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 1 - x 4⟫ ≠ ⟪x j, x 1 - x 4⟫

/-- Single view `w1` with SELF (line F015xF023) (PAIR29; `PL29.lexAny_pair6`, no class fact). -/
def Pair6Hyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  0 < ⟪(s0x_fac29 N.facets).N 0, PL29.lv29 N 1 2⟫ ∧
    ⟪(s0x_fac29 N.facets).N 3, PL29.lv29 N 1 2⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 4, PL29.lv29 N 1 2⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 5, PL29.lv29 N 1 2⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 6, PL29.lv29 N 1 2⟫ < 0 ∧
    ∀ i ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)),
      i ≠ j → ⟪x i, PL29.lv29 N 1 2⟫ ≠ ⟪x j, PL29.lv29 N 1 2⟫

/-- Union of the PAIR29 pair-closure instances. -/
def Pair29Hyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  Pair1Hyp x N ∨
    Pair2Hyp x N ∨
    Pair3Hyp x N ∨
    Pair4Hyp x N ∨
    Pair5Hyp x N ∨
    Pair6Hyp x N

/-- Shrunken Type-29 open hole proposition, excluding the PAIR29 pair-closure instances. -/
def Hole29R5 (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  Hole29R4 x N ∧ ¬ Pair29Hyp x N

/-- Every point of `Hole29R5` lies in `Hole29`. -/
theorem hole29_of_hole29R5 {x : Fin 7 → ℝ³} {N : NF29 x} (h : Hole29R5 x N) : Hole29 x N :=
  hole29_of_hole29R4 h.1

/-- **Reduction of `Hole29R4` to `Hole29R5`**: the PAIR29 instances (`PL29.lexAny29_pair*`) against
`¬ LexAny29`. -/
theorem hole29R4_reduce {x : Fin 7 → ℝ³} {N : NF29 x} (h : Hole29R4 x N) : Hole29R5 x N := by
  have hnl := (hole29_of_hole29R4 h).2.2.2.2.2.1
  refine ⟨h, ?_⟩
  rintro (⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    | ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
    | ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    | ⟨h1, h2, h3⟩
    | ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
    | ⟨h1, h2, h3, h4, h5, h6⟩)
  · exact hnl (PL29.lexAny29_pair1 N h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11)
  · exact hnl (PL29.lexAny29_pair2 N h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13)
  · exact hnl (PL29.lexAny29_pair3 N h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11)
  · exact hnl (PL29.lexAny29_pair4 N h1 h2 h3)
  · exact hnl (PL29.lexAny29_pair5 N h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13)
  · exact hnl (PL29.lexAny29_pair6 N h1 h2 h3 h4 h5 h6)

/-- Main Type-29 reduction leaving `Hole29R5`. -/
theorem type29_rupert_or_hole''''' {x : Fin 7 → ℝ³} (N : NF29 x)
    (hK1 : K1_29 N) (hZ : ¬ Z29 x) (hOB : OB6 x) :
    IsRupert (univ.image x) ∨ Hole29R5 x N :=
  (type29_rupert_or_hole'''' N hK1 hZ hOB).elim Or.inl (fun h => Or.inr (hole29R4_reduce h))

/-! ### TRI29L: triple closures (`Type29Tri*.lean`) -/

/-- Triple `x 5 - x 6`, `x 0 - x 1`, `x 1 - x 2` (lines F1456xF356, F012xF015, F012xF124) (TRI29L; `PL29.lexAny_tri2`, no class fact). -/
def Triple29_2Hyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  0 < ⟪(s0x_fac29 N.facets).N 0, x 5 - x 6⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 2, x 5 - x 6⟫ ∧
    ⟪(s0x_fac29 N.facets).N 4, x 5 - x 6⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 6, x 5 - x 6⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 6, x 0 - x 1⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 7, x 0 - x 1⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 8, x 0 - x 1⟫ ∧
    ⟪(s0x_fac29 N.facets).N 3, x 1 - x 2⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 7, x 1 - x 2⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 8, x 1 - x 2⟫ < 0 ∧
    PL29.PlaneSide x 1 3 6 0 4 < 0 ∧
    0 < PL29.PlaneSide x 1 3 4 0 6 ∧
    PL29.PlaneSide x 2 4 6 0 3 < 0 ∧
    0 < PL29.PlaneSide x 2 3 6 1 4 ∧
    0 < PL29.PlaneSide x 1 3 6 0 5 ∧
    PL29.PlaneSide x 2 5 6 0 3 < 0 ∧
    (∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 5 - x 6⟫ ≠ ⟪x j, x 5 - x 6⟫) ∧
    (∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 0 - x 1⟫ ≠ ⟪x j, x 0 - x 1⟫) ∧
    ∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 1 - x 2⟫ ≠ ⟪x j, x 1 - x 2⟫

/-- Triple `w1`, `x 0 - x 1`, `x 5 - x 6` (lines F124xF346, F012xF015, F1456xF356) (TRI29L; `PL29.lexAny_tri3`, no class fact). -/
def Triple29_3Hyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  ⟪(s0x_fac29 N.facets).N 0, PL29.lv29 N 4 7⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 1, PL29.lv29 N 4 7⟫ ∧
    ⟪(s0x_fac29 N.facets).N 3, PL29.lv29 N 4 7⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 5, PL29.lv29 N 4 7⟫ ∧
    ⟪(s0x_fac29 N.facets).N 6, PL29.lv29 N 4 7⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 8, PL29.lv29 N 4 7⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 6, x 0 - x 1⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 7, x 0 - x 1⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 8, x 0 - x 1⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 0, x 5 - x 6⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 2, x 5 - x 6⟫ ∧
    ⟪(s0x_fac29 N.facets).N 4, x 5 - x 6⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 6, x 5 - x 6⟫ < 0 ∧
    0 < PL29.PlaneSide x 2 3 6 1 5 ∧
    0 < PL29.PlaneSide x 2 3 5 1 6 ∧
    PL29.PlaneSide x 2 5 6 0 4 < 0 ∧
    0 < PL29.PlaneSide x 2 4 6 0 5 ∧
    PL29.PlaneSide x 2 4 5 0 6 < 0 ∧
    (∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, PL29.lv29 N 4 7⟫ ≠ ⟪x j, PL29.lv29 N 4 7⟫) ∧
    (∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 0 - x 1⟫ ≠ ⟪x j, x 0 - x 1⟫) ∧
    ∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 5 - x 6⟫ ≠ ⟪x j, x 5 - x 6⟫

/-- Triple `w1`, `x 0 - x 1`, `w3` (lines F1456xF234, F012xF015, F035xF234) (TRI29L; `PL29.lexAny_tri10`, no class fact). -/
def Triple29_10Hyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  ⟪(s0x_fac29 N.facets).N 0, PL29.lv29 N 5 6⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 1, PL29.lv29 N 5 6⟫ ∧
    ⟪(s0x_fac29 N.facets).N 2, PL29.lv29 N 5 6⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 3, PL29.lv29 N 5 6⟫ ∧
    ⟪(s0x_fac29 N.facets).N 4, PL29.lv29 N 5 6⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 7, PL29.lv29 N 5 6⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 8, PL29.lv29 N 5 6⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 6, x 0 - x 1⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 7, x 0 - x 1⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 8, x 0 - x 1⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 0, PL29.lv29 N 3 6⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 1, PL29.lv29 N 3 6⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 2, PL29.lv29 N 3 6⟫ ∧
    ⟪(s0x_fac29 N.facets).N 4, PL29.lv29 N 3 6⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 5, PL29.lv29 N 3 6⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 7, PL29.lv29 N 3 6⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 8, PL29.lv29 N 3 6⟫ < 0 ∧
    PL29.PlaneSide x 1 3 6 0 4 < 0 ∧
    PL29.PlaneSide x 1 3 4 0 6 < 0 ∧
    (∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, PL29.lv29 N 5 6⟫ ≠ ⟪x j, PL29.lv29 N 5 6⟫) ∧
    (∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 0 - x 1⟫ ≠ ⟪x j, x 0 - x 1⟫) ∧
    ∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, PL29.lv29 N 3 6⟫ ≠ ⟪x j, PL29.lv29 N 3 6⟫

/-- Triple `w1`, `w2`, `x 1 - x 2` (lines F023xF124, F012xF035, F012xF124) (TRI29L; `PL29.lexAny_tri8`, no class fact). -/
def Triple29_8Hyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  0 < ⟪(s0x_fac29 N.facets).N 0, PL29.lv29 N 2 4⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 1, PL29.lv29 N 2 4⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 3, PL29.lv29 N 2 4⟫ ∧
    ⟪(s0x_fac29 N.facets).N 5, PL29.lv29 N 2 4⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 6, PL29.lv29 N 2 4⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 7, PL29.lv29 N 2 4⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 8, PL29.lv29 N 2 4⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 1, PL29.lv29 N 0 3⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 2, PL29.lv29 N 0 3⟫ ∧
    ⟪(s0x_fac29 N.facets).N 4, PL29.lv29 N 0 3⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 5, PL29.lv29 N 0 3⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 6, PL29.lv29 N 0 3⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 7, PL29.lv29 N 0 3⟫ ∧
    ⟪(s0x_fac29 N.facets).N 8, PL29.lv29 N 0 3⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 3, x 1 - x 2⟫ ∧
    ⟪(s0x_fac29 N.facets).N 7, x 1 - x 2⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 8, x 1 - x 2⟫ ∧
    PL29.PlaneSide x 1 3 6 0 5 < 0 ∧
    0 < PL29.PlaneSide x 2 3 6 1 5 ∧
    PL29.PlaneSide x 2 3 5 1 6 < 0 ∧
    (∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, PL29.lv29 N 2 4⟫ ≠ ⟪x j, PL29.lv29 N 2 4⟫) ∧
    (∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, PL29.lv29 N 0 3⟫ ≠ ⟪x j, PL29.lv29 N 0 3⟫) ∧
    ∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 1 - x 2⟫ ≠ ⟪x j, x 1 - x 2⟫

/-- Triple `w1`, `x 0 - x 1`, `w3` (lines F012xF346, F012xF015, F1456xF234) (TRI29L; `PL29.lexAny_tri7`, no class fact). -/
def Triple29_7Hyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  0 < ⟪(s0x_fac29 N.facets).N 1, PL29.lv29 N 0 7⟫ ∧
    ⟪(s0x_fac29 N.facets).N 2, PL29.lv29 N 0 7⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 3, PL29.lv29 N 0 7⟫ ∧
    ⟪(s0x_fac29 N.facets).N 4, PL29.lv29 N 0 7⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 5, PL29.lv29 N 0 7⟫ ∧
    ⟪(s0x_fac29 N.facets).N 6, PL29.lv29 N 0 7⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 8, PL29.lv29 N 0 7⟫ ∧
    ⟪(s0x_fac29 N.facets).N 6, x 0 - x 1⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 7, x 0 - x 1⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 8, x 0 - x 1⟫ ∧
    ⟪(s0x_fac29 N.facets).N 0, PL29.lv29 N 5 6⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 1, PL29.lv29 N 5 6⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 2, PL29.lv29 N 5 6⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 3, PL29.lv29 N 5 6⟫ ∧
    ⟪(s0x_fac29 N.facets).N 4, PL29.lv29 N 5 6⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 7, PL29.lv29 N 5 6⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 8, PL29.lv29 N 5 6⟫ ∧
    PL29.PlaneSide x 1 3 6 0 4 < 0 ∧
    0 < PL29.PlaneSide x 1 3 4 0 6 ∧
    0 < PL29.PlaneSide x 1 3 6 0 5 ∧
    PL29.PlaneSide x 2 5 6 0 3 < 0 ∧
    (∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, PL29.lv29 N 0 7⟫ ≠ ⟪x j, PL29.lv29 N 0 7⟫) ∧
    (∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 0 - x 1⟫ ≠ ⟪x j, x 0 - x 1⟫) ∧
    ∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, PL29.lv29 N 5 6⟫ ≠ ⟪x j, PL29.lv29 N 5 6⟫

/-- Triple `w1`, `x 0 - x 1`, `x 5 - x 6` (lines F124xF346, F012xF015, F1456xF356) (TRI29L; `PL29.lexAny_tri6`, no class fact). -/
def Triple29_6Hyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  ⟪(s0x_fac29 N.facets).N 0, PL29.lv29 N 4 7⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 1, PL29.lv29 N 4 7⟫ ∧
    ⟪(s0x_fac29 N.facets).N 3, PL29.lv29 N 4 7⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 5, PL29.lv29 N 4 7⟫ ∧
    ⟪(s0x_fac29 N.facets).N 6, PL29.lv29 N 4 7⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 8, PL29.lv29 N 4 7⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 6, x 0 - x 1⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 7, x 0 - x 1⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 8, x 0 - x 1⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 0, x 5 - x 6⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 2, x 5 - x 6⟫ ∧
    ⟪(s0x_fac29 N.facets).N 4, x 5 - x 6⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 6, x 5 - x 6⟫ < 0 ∧
    PL29.PlaneSide x 2 4 6 0 3 < 0 ∧
    0 < PL29.PlaneSide x 2 3 6 1 4 ∧
    PL29.PlaneSide x 2 5 6 0 4 < 0 ∧
    0 < PL29.PlaneSide x 2 4 6 0 5 ∧
    PL29.PlaneSide x 2 4 5 0 6 < 0 ∧
    (∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, PL29.lv29 N 4 7⟫ ≠ ⟪x j, PL29.lv29 N 4 7⟫) ∧
    (∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 0 - x 1⟫ ≠ ⟪x j, x 0 - x 1⟫) ∧
    ∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 5 - x 6⟫ ≠ ⟪x j, x 5 - x 6⟫

/-- Triple `w1`, `w2`, `w3` (lines F012xF1456, F012xF346, F035xF234) (TRI29L; `PL29.lexAny_tri5`, no class fact). -/
def Triple29_5Hyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  0 < ⟪(s0x_fac29 N.facets).N 1, PL29.lv29 N 0 5⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 2, PL29.lv29 N 0 5⟫ ∧
    ⟪(s0x_fac29 N.facets).N 4, PL29.lv29 N 0 5⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 6, PL29.lv29 N 0 5⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 7, PL29.lv29 N 0 5⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 8, PL29.lv29 N 0 5⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 1, PL29.lv29 N 0 7⟫ ∧
    ⟪(s0x_fac29 N.facets).N 2, PL29.lv29 N 0 7⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 3, PL29.lv29 N 0 7⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 4, PL29.lv29 N 0 7⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 5, PL29.lv29 N 0 7⟫ ∧
    ⟪(s0x_fac29 N.facets).N 6, PL29.lv29 N 0 7⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 8, PL29.lv29 N 0 7⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 0, PL29.lv29 N 3 6⟫ ∧
    ⟪(s0x_fac29 N.facets).N 1, PL29.lv29 N 3 6⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 2, PL29.lv29 N 3 6⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 4, PL29.lv29 N 3 6⟫ ∧
    ⟪(s0x_fac29 N.facets).N 5, PL29.lv29 N 3 6⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 7, PL29.lv29 N 3 6⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 8, PL29.lv29 N 3 6⟫ < 0 ∧
    0 < PL29.PlaneSide x 2 3 6 1 4 ∧
    (∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, PL29.lv29 N 0 5⟫ ≠ ⟪x j, PL29.lv29 N 0 5⟫) ∧
    (∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, PL29.lv29 N 0 7⟫ ≠ ⟪x j, PL29.lv29 N 0 7⟫) ∧
    ∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, PL29.lv29 N 3 6⟫ ≠ ⟪x j, PL29.lv29 N 3 6⟫

/-- Triple `w1`, `x 0 - x 1`, `w3` (lines F015xF023, F012xF015, F012xF234) (TRI29L; `PL29.lexAny_tri1`, no class fact). -/
def Triple29_1Hyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  0 < ⟪(s0x_fac29 N.facets).N 0, PL29.lv29 N 1 2⟫ ∧
    ⟪(s0x_fac29 N.facets).N 3, PL29.lv29 N 1 2⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 4, PL29.lv29 N 1 2⟫ ∧
    ⟪(s0x_fac29 N.facets).N 5, PL29.lv29 N 1 2⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 6, PL29.lv29 N 1 2⟫ ∧
    ⟪(s0x_fac29 N.facets).N 7, PL29.lv29 N 1 2⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 8, PL29.lv29 N 1 2⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 6, x 0 - x 1⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 7, x 0 - x 1⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 8, x 0 - x 1⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 1, PL29.lv29 N 0 6⟫ ∧
    ⟪(s0x_fac29 N.facets).N 2, PL29.lv29 N 0 6⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 3, PL29.lv29 N 0 6⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 4, PL29.lv29 N 0 6⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 5, PL29.lv29 N 0 6⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 7, PL29.lv29 N 0 6⟫ ∧
    ⟪(s0x_fac29 N.facets).N 8, PL29.lv29 N 0 6⟫ < 0 ∧
    PL29.PlaneSide x 1 3 6 0 4 < 0 ∧
    0 < PL29.PlaneSide x 1 3 4 0 6 ∧
    0 < PL29.PlaneSide x 2 3 6 1 4 ∧
    (∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, PL29.lv29 N 1 2⟫ ≠ ⟪x j, PL29.lv29 N 1 2⟫) ∧
    (∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 0 - x 1⟫ ≠ ⟪x j, x 0 - x 1⟫) ∧
    ∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, PL29.lv29 N 0 6⟫ ≠ ⟪x j, PL29.lv29 N 0 6⟫

/-- Triple `w1`, `x 1 - x 2`, `x 3 - x 5` (lines F012xF1456, F012xF124, F035xF356) (TRI29L; `PL29.lexAny_tri9`, no class fact). -/
def Triple29_9Hyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  0 < ⟪(s0x_fac29 N.facets).N 1, PL29.lv29 N 0 5⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 2, PL29.lv29 N 0 5⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 3, PL29.lv29 N 0 5⟫ ∧
    ⟪(s0x_fac29 N.facets).N 4, PL29.lv29 N 0 5⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 6, PL29.lv29 N 0 5⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 7, PL29.lv29 N 0 5⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 8, PL29.lv29 N 0 5⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 3, x 1 - x 2⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 7, x 1 - x 2⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 8, x 1 - x 2⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 0, x 3 - x 5⟫ ∧
    0 < ⟪(s0x_fac29 N.facets).N 4, x 3 - x 5⟫ ∧
    (∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, PL29.lv29 N 0 5⟫ ≠ ⟪x j, PL29.lv29 N 0 5⟫) ∧
    (∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 1 - x 2⟫ ≠ ⟪x j, x 1 - x 2⟫) ∧
    ∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 3 - x 5⟫ ≠ ⟪x j, x 3 - x 5⟫

/-- Triple `w1`, `x 0 - x 1`, `x 3 - x 4` (lines F015xF023, F012xF015, F234xF346) (TRI29L; `PL29.lexAny_tri4`, no class fact). -/
def Triple29_4Hyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  0 < ⟪(s0x_fac29 N.facets).N 0, PL29.lv29 N 1 2⟫ ∧
    ⟪(s0x_fac29 N.facets).N 3, PL29.lv29 N 1 2⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 4, PL29.lv29 N 1 2⟫ ∧
    ⟪(s0x_fac29 N.facets).N 5, PL29.lv29 N 1 2⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 6, PL29.lv29 N 1 2⟫ ∧
    ⟪(s0x_fac29 N.facets).N 7, PL29.lv29 N 1 2⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 8, PL29.lv29 N 1 2⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 6, x 0 - x 1⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 7, x 0 - x 1⟫ < 0 ∧
    0 < ⟪(s0x_fac29 N.facets).N 8, x 0 - x 1⟫ ∧
    ⟪(s0x_fac29 N.facets).N 0, x 3 - x 4⟫ < 0 ∧
    ⟪(s0x_fac29 N.facets).N 1, x 3 - x 4⟫ < 0 ∧
    0 < PL29.PlaneSide x 1 3 6 0 5 ∧
    (∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, PL29.lv29 N 1 2⟫ ≠ ⟪x j, PL29.lv29 N 1 2⟫) ∧
    (∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 0 - x 1⟫ ≠ ⟪x j, x 0 - x 1⟫) ∧
    ∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 3 - x 4⟫ ≠ ⟪x j, x 3 - x 4⟫

/-- Union of the TRI29L triple-closure instances. -/
def Tri29Hyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  Triple29_2Hyp x N ∨
    Triple29_3Hyp x N ∨
    Triple29_10Hyp x N ∨
    Triple29_8Hyp x N ∨
    Triple29_7Hyp x N ∨
    Triple29_6Hyp x N ∨
    Triple29_5Hyp x N ∨
    Triple29_1Hyp x N ∨
    Triple29_9Hyp x N ∨
    Triple29_4Hyp x N

/-- Shrunken Type-29 open hole proposition, excluding the TRI29L triple-closure instances. -/
def Hole29R6 (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  Hole29R5 x N ∧ ¬ Tri29Hyp x N

/-- Every point of `Hole29R6` lies in `Hole29`. -/
theorem hole29_of_hole29R6 {x : Fin 7 → ℝ³} {N : NF29 x} (h : Hole29R6 x N) : Hole29 x N :=
  hole29_of_hole29R5 h.1

/-- **Reduction of `Hole29R5` to `Hole29R6`**: the TRI29L instances (`PL29.lexAny29_tri*`) against
`¬ LexAny29`. -/
theorem hole29R5_reduce {x : Fin 7 → ℝ³} {N : NF29 x} (h : Hole29R5 x N) : Hole29R6 x N := by
  have hnl := (hole29_of_hole29R5 h).2.2.2.2.2.1
  refine ⟨h, ?_⟩
  rintro (⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩
    | ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩
    | ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22⟩
    | ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
    | ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24⟩
    | ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩
    | ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24⟩
    | ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
    | ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
    | ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩)
  · exact hnl (PL29.lexAny29_tri2 N h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19)
  · exact hnl (PL29.lexAny29_tri3 N h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21)
  · exact hnl (PL29.lexAny29_tri10 N h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22)
  · exact hnl (PL29.lexAny29_tri8 N h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23)
  · exact hnl (PL29.lexAny29_tri7 N h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24)
  · exact hnl (PL29.lexAny29_tri6 N h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21)
  · exact hnl (PL29.lexAny29_tri5 N h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24)
  · exact hnl (PL29.lexAny29_tri1 N h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23)
  · exact hnl (PL29.lexAny29_tri9 N h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15)
  · exact hnl (PL29.lexAny29_tri4 N h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16)

/-- Main Type-29 reduction leaving `Hole29R6`. -/
theorem type29_rupert_or_hole'''''' {x : Fin 7 → ℝ³} (N : NF29 x)
    (hK1 : K1_29 N) (hZ : ¬ Z29 x) (hOB : OB6 x) :
    IsRupert (univ.image x) ∨ Hole29R6 x N :=
  (type29_rupert_or_hole''''' N hK1 hZ hOB).elim Or.inl (fun h => Or.inr (hole29R5_reduce h))

end Minimality.H29
