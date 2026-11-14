module

public import Minimality.Type24SAT.K24.ParEdge

@[expose] public section

/-!
# Type 24, `25 ∥ 46` (facet `H`): the view along the parallel edges

Facets `A … I` = indices `0 … 8` of `s0x_S24`.  Hypothesis `hl : x 6 - x 4 = l • (x 5 - x 2)`
(the edges `46` and `25` are parallel; `l < 0` follows from facet `H`).  At the view `d = x 2 - x 5`
(depths `w i = ⟪x i, d⟫`) one of the Q4 leaves `P0234`, `P0536` has mixed diagonal signs, unless
`w 0 = w 4 = w 5` (the "double wall": `D` perpendicular to the parallel edges).
* `par2546_real`: the pure real case analysis (identity
  `be (w3 - w4) + al (w3 - w5) = (1 - al - be)(be X + al Y)`, `X = w0 - w4`, `Y = w0 - w5`).
* `par2546_quad`: `D` is a quadrilateral `0 4 3 5`: `x 3 - x 0 = al (x 5 - x 0) + be (x 4 - x 0)`,
  `al, be > 0`, `al + be > 1`.
* `isRupert_par2546`: the theorem.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.Par
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.RimCell

/-- The case analysis at the view `d`, on the real depths. -/
theorem par2546_real (w0 w2 w3 w4 w5 w6 al be : ℝ) (h25 : w5 < w2) (h64 : w4 < w6)
    (hal : 0 < al) (hbe : 0 < be) (hab : 1 < al + be)
    (hq : w3 = w0 + al * (w5 - w0) + be * (w4 - w0))
    (hw : ¬(w0 = w5 ∧ w0 = w4)) :
    ((w0 - w2 < 0 ∨ w0 - w4 < 0 ∨ w3 - w2 < 0 ∨ w3 - w4 < 0) ∧
      (0 < w0 - w2 ∨ 0 < w0 - w4 ∨ 0 < w3 - w2 ∨ 0 < w3 - w4)) ∨
    ((w0 - w5 < 0 ∨ w0 - w6 < 0 ∨ w3 - w5 < 0 ∨ w3 - w6 < 0) ∧
      (0 < w0 - w5 ∨ 0 < w0 - w6 ∨ 0 < w3 - w5 ∨ 0 < w3 - w6)) := by
  have iden : be * (w3 - w4) + al * (w3 - w5) =
      (1 - al - be) * (be * (w0 - w4) + al * (w0 - w5)) := by rw [hq]; ring
  have hneg : 1 - al - be < 0 := by linarith
  by_cases hn1 : (w0 - w2 < 0 ∨ w0 - w4 < 0 ∨ w3 - w2 < 0 ∨ w3 - w4 < 0)
  · by_cases hp1 : (0 < w0 - w2 ∨ 0 < w0 - w4 ∨ 0 < w3 - w2 ∨ 0 < w3 - w4)
    · exact Or.inl ⟨hn1, hp1⟩
    · right
      simp only [not_or, not_lt] at hp1
      obtain ⟨p1, p2, p3, p4⟩ := hp1
      refine ⟨Or.inr (Or.inl (by linarith)), ?_⟩
      by_contra hc
      simp only [not_or, not_lt] at hc
      obtain ⟨c1, c2, c3, c4⟩ := hc
      apply hw
      have hL : be * (w3 - w4) + al * (w3 - w5) ≤ 0 := by
        nlinarith [mul_nonneg hbe.le (sub_nonneg.2 p4), mul_nonneg hal.le (sub_nonneg.2 c3)]
      have hS : be * (w0 - w4) + al * (w0 - w5) ≤ 0 := by
        nlinarith [mul_nonneg hbe.le (sub_nonneg.2 p2), mul_nonneg hal.le (sub_nonneg.2 c1)]
      have hR : 0 ≤ (1 - al - be) * (be * (w0 - w4) + al * (w0 - w5)) :=
        mul_nonneg_of_nonpos_of_nonpos hneg.le hS
      have h0 : (1 - al - be) * (be * (w0 - w4) + al * (w0 - w5)) = 0 := by linarith
      have hS0 : be * (w0 - w4) + al * (w0 - w5) = 0 :=
        (mul_eq_zero.1 h0).resolve_left hneg.ne
      have hX : be * (w0 - w4) = 0 := by
        nlinarith [mul_nonneg hbe.le (sub_nonneg.2 p2), mul_nonneg hal.le (sub_nonneg.2 c1)]
      have hY : al * (w0 - w5) = 0 := by linarith
      have hX' := (mul_eq_zero.1 hX).resolve_left hbe.ne'
      have hY' := (mul_eq_zero.1 hY).resolve_left hal.ne'
      exact ⟨by linarith, by linarith⟩
  · right
    simp only [not_or, not_lt] at hn1
    obtain ⟨n1, n2, n3, n4⟩ := hn1
    refine ⟨?_, Or.inl (by linarith)⟩
    by_contra hc
    simp only [not_or, not_lt] at hc
    obtain ⟨c1, c2, c3, c4⟩ := hc
    have h1 : 0 < be * (w3 - w4) + al * (w3 - w5) := by
      nlinarith [mul_nonneg hbe.le n4, mul_pos hal (by linarith : 0 < w3 - w5)]
    have h2 : (1 - al - be) * (be * (w0 - w4) + al * (w0 - w5)) < 0 :=
      mul_neg_of_neg_of_pos hneg
        (by nlinarith [mul_nonneg hbe.le n2, mul_pos hal (by linarith : 0 < w0 - w5)])
    linarith

/-- `D` is the quadrilateral `0 4 3 5`: `x 3 - x 0 = al (x 5 - x 0) + be (x 4 - x 0)` with
`al, be > 0` and `al + be > 1` (facets `E`, `C`, `G`). -/
theorem par2546_quad {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    ∃ al be : ℝ, 0 < al ∧ 0 < be ∧ 1 < al + be ∧
      x 3 - x 0 = al • (x 5 - x 0) + be • (x 4 - x 0) := by
  have IS := F.inner_sub
  have zD0 := F.zero 3 0 (by decide); have zD3 := F.zero 3 3 (by decide)
  have zD4 := F.zero 3 4 (by decide); have zD5 := F.zero 3 5 (by decide)
  have hD6 := F.neg 3 6 (by decide)
  have zE0 := F.zero 4 0 (by decide); have zE4 := F.zero 4 4 (by decide)
  have zE6 := F.zero 4 6 (by decide)
  have hE3 := F.neg 4 3 (by decide); have hE5 := F.neg 4 5 (by decide)
  have zC0 := F.zero 2 0 (by decide); have zC5 := F.zero 2 5 (by decide)
  have hC3 := F.neg 2 3 (by decide); have hC4 := F.neg 2 4 (by decide)
  have zG3 := F.zero 6 3 (by decide); have zG5 := F.zero 6 5 (by decide)
  have hG0 := F.neg 6 0 (by decide); have hG4 := F.neg 6 4 (by decide)
  obtain ⟨al, hal'⟩ : ∃ al : ℝ, al * F.f 4 (x 5) = F.f 4 (x 3) :=
    ⟨_, div_mul_cancel₀ _ hE5.ne⟩
  obtain ⟨be, hbe'⟩ : ∃ be : ℝ, be * F.f 2 (x 4) = F.f 2 (x 3) :=
    ⟨_, div_mul_cancel₀ _ hC4.ne⟩
  have hal : 0 < al := by
    by_contra h; push Not at h
    linarith [mul_nonneg_of_nonpos_of_nonpos h hE5.le]
  have hbe : 0 < be := by
    by_contra h; push Not at h
    linarith [mul_nonneg_of_nonpos_of_nonpos h hC4.le]
  have hcr : cross (F.N 3) (F.N 4) ≠ 0 := by
    intro h
    have hb := h21_binet (F.N 3) (F.N 4) (x 5 - x 0) (x 6 - x 0)
    rw [h, inner_zero_left, IS 3 5 0, IS 4 6 0, IS 3 6 0, IS 4 5 0, zD5, zD0, zE6, zE0] at hb
    nlinarith only [hb, mul_pos_of_neg_of_neg hD6 hE5]
  obtain ⟨lam, hlam⟩ := h21_mul_cross hcr
    (by rw [IS, zD4, zD0]; ring : ⟪F.N 3, x 4 - x 0⟫ = 0)
    (by rw [IS, zE4, zE0]; ring : ⟪F.N 4, x 4 - x 0⟫ = 0)
  have hCc : ⟪F.N 2, cross (F.N 3) (F.N 4)⟫ ≠ 0 := by
    intro h0
    have : ⟪F.N 2, x 4 - x 0⟫ = 0 := by rw [hlam, inner_smul_right, h0, mul_zero]
    rw [IS, zC0] at this; linarith
  set v : ℝ³ := (x 3 - x 0) - al • (x 5 - x 0) - be • (x 4 - x 0) with hv
  have ev : ∀ t, ⟪F.N t, v⟫ =
      ⟪F.N t, x 3 - x 0⟫ - al * ⟪F.N t, x 5 - x 0⟫ - be * ⟪F.N t, x 4 - x 0⟫ := by
    intro t; rw [hv, inner_sub_right, inner_sub_right, inner_smul_right, inner_smul_right]
  have vD : ⟪F.N 3, v⟫ = 0 := by rw [ev, IS, IS, IS, zD3, zD0, zD5, zD4]; ring
  have vE : ⟪F.N 4, v⟫ = 0 := by
    rw [ev, IS, IS, IS, zE0, zE4]; linarith
  have vC : ⟪F.N 2, v⟫ = 0 := by
    rw [ev, IS, IS, IS, zC0, zC5]; linarith
  obtain ⟨μ, hμ⟩ := h21_mul_cross hcr vD vE
  have hμ0 : μ = 0 := by
    have : μ * ⟪F.N 2, cross (F.N 3) (F.N 4)⟫ = 0 := by
      rw [← inner_smul_right, ← hμ, vC]
    exact (mul_eq_zero.1 this).resolve_right hCc
  have hv0 : v = 0 := by rw [hμ, hμ0, zero_smul]
  have hdec : x 3 - x 0 = al • (x 5 - x 0) + be • (x 4 - x 0) := by
    have := hv0; rw [hv] at this
    linear_combination (norm := module) this
  have ed : ⟪F.N 6, x 3 - x 0⟫ =
      al * ⟪F.N 6, x 5 - x 0⟫ + be * ⟪F.N 6, x 4 - x 0⟫ := by
    rw [hdec, inner_add_right, inner_smul_right, inner_smul_right]
  rw [IS, IS, IS, zG3, zG5] at ed
  refine ⟨al, be, hal, hbe, ?_, hdec⟩
  by_contra h; push Not at h
  nlinarith [mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 h) hG0.le,
    mul_neg_of_pos_of_neg hbe hG4]

/-- Mixed diagonal signs of a 4-rim from the four pair differences. -/
theorem par2546_diag {x : Fin 7 → ℝ³} (c : ZMod 4 → Fin 7) (g : ℝ³)
    (hn : ⟪x (c 0), g⟫ - ⟪x (c 1), g⟫ < 0 ∨ ⟪x (c 0), g⟫ - ⟪x (c 3), g⟫ < 0 ∨
      ⟪x (c 2), g⟫ - ⟪x (c 1), g⟫ < 0 ∨ ⟪x (c 2), g⟫ - ⟪x (c 3), g⟫ < 0)
    (hp : 0 < ⟪x (c 0), g⟫ - ⟪x (c 1), g⟫ ∨ 0 < ⟪x (c 0), g⟫ - ⟪x (c 3), g⟫ ∨
      0 < ⟪x (c 2), g⟫ - ⟪x (c 1), g⟫ ∨ 0 < ⟪x (c 2), g⟫ - ⟪x (c 3), g⟫) :
    (∃ p ∈ diagPairs, ⟪x (c p.1) - x (c p.2), g⟫ < 0) ∧
    (∃ p ∈ diagPairs, 0 < ⟪x (c p.1) - x (c p.2), g⟫) := by
  constructor
  · rcases hn with h | h | h | h
    · exact ⟨(0, 1), by decide, by show ⟪x (c 0) - x (c 1), g⟫ < 0; rw [inner_sub_left]; exact h⟩
    · exact ⟨(0, 3), by decide, by show ⟪x (c 0) - x (c 3), g⟫ < 0; rw [inner_sub_left]; exact h⟩
    · exact ⟨(2, 1), by decide, by show ⟪x (c 2) - x (c 1), g⟫ < 0; rw [inner_sub_left]; exact h⟩
    · exact ⟨(2, 3), by decide, by show ⟪x (c 2) - x (c 3), g⟫ < 0; rw [inner_sub_left]; exact h⟩
  · rcases hp with h | h | h | h
    · exact ⟨(0, 1), by decide, by show 0 < ⟪x (c 0) - x (c 1), g⟫; rw [inner_sub_left]; exact h⟩
    · exact ⟨(0, 3), by decide, by show 0 < ⟪x (c 0) - x (c 3), g⟫; rw [inner_sub_left]; exact h⟩
    · exact ⟨(2, 1), by decide, by show 0 < ⟪x (c 2) - x (c 1), g⟫; rw [inner_sub_left]; exact h⟩
    · exact ⟨(2, 3), by decide, by show 0 < ⟪x (c 2) - x (c 3), g⟫; rw [inner_sub_left]; exact h⟩

set_option maxHeartbeats 1600000 in
/-- **Type 24, `25 ∥ 46` (`x 6 - x 4 = l (x 5 - x 2)`), off the double wall: Rupert.**  One view
`d = x 2 - x 5`; leaf P0234 (tilt `x 4 - x 2`) or leaf P0536 (tilt `x 2 - x 4`).  The excluded
double wall is `⟪x 0, x 5 - x 2⟫ = ⟪x 5, x 5 - x 2⟫ = ⟪x 4, x 5 - x 2⟫` (face `D` perpendicular to
the parallel edges).  No class, OB1, parallelogram or acuteness hypothesis. -/
theorem isRupert_par2546 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {l : ℝ}
    (hl : x 6 - x 4 = l • (x 5 - x 2))
    (hw : ¬(⟪x 0 - x 5, x 5 - x 2⟫ = 0 ∧ ⟪x 0 - x 4, x 5 - x 2⟫ = 0)) :
    IsRupert (univ.image x) := by
  obtain ⟨al, be, hal, hbe, hab, hq⟩ := par2546_quad F
  have IS := F.inner_sub
  have hx := Minimality.H24.SAT.inj_of_fac F
  set d := x 2 - x 5 with hd
  have hdd : 0 < ⟪d, d⟫ :=
    real_inner_self_pos.2 (fun h => absurd (hx (sub_eq_zero.1 h)) (by decide))
  -- facet values
  have zA2 := F.zero 0 2 (by decide); have hA5 := F.neg 0 5 (by decide)
  have zB6 := F.zero 1 6 (by decide); have hB4 := F.neg 1 4 (by decide)
  have zC2 := F.zero 2 2 (by decide); have zC5 := F.zero 2 5 (by decide)
  have hC4 := F.neg 2 4 (by decide)
  have zD5 := F.zero 3 5 (by decide); have hD2 := F.neg 3 2 (by decide)
  have zE4 := F.zero 4 4 (by decide); have zE6 := F.zero 4 6 (by decide)
  have hE2 := F.neg 4 2 (by decide)
  have zG2 := F.zero 6 2 (by decide); have zG5 := F.zero 6 5 (by decide)
  have hG4 := F.neg 6 4 (by decide)
  have zH2 := F.zero 7 2 (by decide); have zH6 := F.zero 7 6 (by decide)
  have hH4 := F.neg 7 4 (by decide); have hH5 := F.neg 7 5 (by decide)
  have zI4 := F.zero 8 4 (by decide); have zI6 := F.zero 8 6 (by decide)
  have hI2 := F.neg 8 2 (by decide)
  -- l < 0
  have hlneg : l < 0 := by
    have h1 : ⟪F.N 7, x 6 - x 4⟫ = l * ⟪F.N 7, x 5 - x 2⟫ := by rw [hl, inner_smul_right]
    rw [IS 7 6 4, IS 7 5 2, zH6, zH2] at h1
    by_contra h; push Not at h
    nlinarith [mul_nonneg h (neg_nonneg.2 hH5.le)]
  have hm : x 6 - x 4 = (-l) • d := by rw [hl, hd]; module
  have dinner : ∀ t, ⟪F.N t, x 6 - x 4⟫ = (-l) * ⟪F.N t, d⟫ := by
    intro t; rw [hm, inner_smul_right]
  -- the view d against the facet normals
  have dA : 0 < ⟪F.N 0, d⟫ := by rw [hd, IS, zA2]; linarith
  have dH : 0 < ⟪F.N 7, d⟫ := by rw [hd, IS, zH2]; linarith
  have dD : ⟪F.N 3, d⟫ < 0 := by rw [hd, IS, zD5]; linarith
  have dC : ⟪F.N 2, d⟫ = 0 := by rw [hd, IS, zC2, zC5]; ring
  have dG : ⟪F.N 6, d⟫ = 0 := by rw [hd, IS, zG2, zG5]; ring
  have dE : ⟪F.N 4, d⟫ = 0 := by
    have h := dinner 4
    rw [IS 4 6 4, zE6, zE4, sub_self] at h
    exact ((mul_eq_zero.1 h.symm).resolve_left (neg_ne_zero.2 hlneg.ne))
  have dI : ⟪F.N 8, d⟫ = 0 := by
    have h := dinner 8
    rw [IS 8 6 4, zI6, zI4, sub_self] at h
    exact ((mul_eq_zero.1 h.symm).resolve_left (neg_ne_zero.2 hlneg.ne))
  have dB : 0 < ⟪F.N 1, d⟫ := by
    have h := dinner 1
    rw [IS 1 6 4, zB6] at h
    by_contra hc; push Not at hc
    nlinarith [mul_nonneg (neg_nonneg.2 hlneg.le) (neg_nonneg.2 hc)]
  -- tilts
  have tE : 0 < ⟪F.N 4, x 4 - x 2⟫ := by rw [IS, zE4]; linarith
  have tI : 0 < ⟪F.N 8, x 4 - x 2⟫ := by rw [IS, zI4]; linarith
  have tC : ⟪F.N 2, x 4 - x 2⟫ < 0 := by rw [IS, zC2]; linarith
  have tG : ⟪F.N 6, x 4 - x 2⟫ < 0 := by rw [IS, zG2]; linarith
  have tE' : ⟪F.N 4, x 2 - x 4⟫ < 0 := by rw [IS, zE4]; linarith
  have tI' : ⟪F.N 8, x 2 - x 4⟫ < 0 := by rw [IS, zI4]; linarith
  have tC' : 0 < ⟪F.N 2, x 2 - x 4⟫ := by rw [IS, zC2]; linarith
  have tG' : 0 < ⟪F.N 6, x 2 - x 4⟫ := by rw [IS, zG2]; linarith
  -- leaf P0234
  obtain ⟨a1, hA1⟩ := exists_cellAt_of_lex (F := F) (U := U0234) (Dn := D0234) (u₀ := d)
    (v := x 4 - x 2)
    (by
      intro t ht; simp only [U0234, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact Or.inl dA
      · exact Or.inr ⟨dE, tE⟩
      · exact Or.inl dH
      · exact Or.inr ⟨dI, tI⟩)
    (by
      intro t ht; simp only [D0234, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact Or.inr ⟨by rw [dC]; simp, by linarith⟩
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by rw [dG]; simp, by linarith⟩)
  have hle1 : CellLe F U0234 D0234 d := by
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · simp only [U0234, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact dA.le
      · rw [dE]
      · exact dH.le
      · rw [dI]
    · simp only [D0234, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · rw [dC]
      · exact dD.le
      · rw [dG]
  -- leaf P0536
  obtain ⟨a2, hA2⟩ := exists_cellAt_of_lex (F := F) (U := U0536) (Dn := D0536) (u₀ := d)
    (v := x 2 - x 4)
    (by
      intro t ht; simp only [U0536, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact Or.inl dB
      · exact Or.inr ⟨dC, tC'⟩
      · exact Or.inr ⟨dG, tG'⟩
      · exact Or.inl dH)
    (by
      intro t ht; simp only [D0536, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by rw [dE]; simp, by linarith⟩
      · exact Or.inr ⟨by rw [dI]; simp, by linarith⟩)
  have hle2 : CellLe F U0536 D0536 d := by
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · simp only [U0536, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact dB.le
      · rw [dC]
      · rw [dG]
      · exact dH.le
    · simp only [D0536, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact dD.le
      · rw [dE]
      · rw [dI]
  -- depths
  have e25 : ⟪x 2, d⟫ - ⟪x 5, d⟫ = ⟪d, d⟫ := by rw [← inner_sub_left]
  have e64 : ⟪x 6, d⟫ - ⟪x 4, d⟫ = (-l) * ⟪d, d⟫ := by
    rw [← inner_sub_left, hm, inner_smul_left]; simp
  have eq3 : ⟪x 3, d⟫ = ⟪x 0, d⟫ + al * (⟪x 5, d⟫ - ⟪x 0, d⟫) + be * (⟪x 4, d⟫ - ⟪x 0, d⟫) := by
    have h := congrArg (fun v => ⟪v, d⟫) hq
    simp only [inner_add_left, inner_smul_left, inner_sub_left, RCLike.conj_to_real] at h
    linarith
  have hw' : ¬(⟪x 0, d⟫ = ⟪x 5, d⟫ ∧ ⟪x 0, d⟫ = ⟪x 4, d⟫) := by
    rintro ⟨h1, h2⟩
    apply hw
    have e : x 5 - x 2 = -d := by rw [hd]; abel
    rw [e, inner_neg_right, inner_neg_right, inner_sub_left, inner_sub_left]
    constructor <;> linarith
  rcases par2546_real ⟪x 0, d⟫ ⟪x 2, d⟫ ⟪x 3, d⟫ ⟪x 4, d⟫ ⟪x 5, d⟫ ⟪x 6, d⟫ al be (by linarith) (by nlinarith [mul_pos (neg_pos.2 hlneg) hdd])
      hal hbe hab eq3 hw' with ⟨hn, hp⟩ | ⟨hn, hp⟩
  · obtain ⟨h1, h2⟩ := par2546_diag (x := x) c0234 d hn hp
    exact leaf_P0234 F hA1 hle1 hle1 h1 h2
  · obtain ⟨h1, h2⟩ := par2546_diag (x := x) c0536 d hn hp
    exact leaf_P0536 F hA2 hle2 hle2 h1 h2

end Minimality.T24.Par
