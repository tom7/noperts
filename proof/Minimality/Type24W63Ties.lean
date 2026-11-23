module

public import Minimality.Type24E23

@[expose] public section

/-!
# Type 24: the `w63` / `E23` single views at depth ties (TIES24P T1, T2a and their `pi24` mirrors)

* `w63_closes_mustar_pos_nt` (T1): `w63_closes_mustar_pos` with the genericity hypothesis
  (all five depths on `{0, 2, 3, 4, 6}` distinct at `w = x 3 - x 6`) replaced by
  `¬ (z0 = z2 ∧ z2 = z4)`. Proof: only the 4-cycles `0 2 6 4` and `0 2 3 4` with first-level
  clauses; by the Radon dependency `R_02346` (signs `+ - + - +`) and `z3 > z6` both cycles are
  weakly separated only on the triple tie (`tl_sep_core`).
* `w63_closes_triple` (T2a): on the triple tie `z0 = z2 = z4`, if one of
  `⟪x0 - x2, x2 - x6⟫, ⟪x0 - x4, x2 - x6⟫, ⟪x0 - x2, x4 - x6⟫, ⟪x0 - x4, x4 - x6⟫` is negative,
  `LexAny` via the cycle `0 2 3 4` and the 3-level tilt `(w, x2 - x6, x4 - x6)` resp.
  `(w, x4 - x6, x2 - x6)`.
* `w63_closes_star`: T1 + T2a, i.e. `LexAny` unless `W63Star x` (triple tie and all four numbers `≥ 0`).
* `e23_closes_mu23_pos_nt`, `e23_closes_triple`, `e23_closes_star`: the `pi24` images at
  `E23 = x 3 - x 2`.
* `w63_closes_mustar_pos`, `e23_closes_mu23_pos`: corollaries under full distinctness on `{0,2,3,4,6}`
  (resp. `{0,2,3,5,6}`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.A20

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell
  Minimality.T24.Sym Minimality.T24.M4 Minimality.T24 Minimality.LexCell

/-! ### Real core of T1 -/

/-- **Separation core**: with Radon weights `+ - + - +` on `(h0, h2, h3, h4, h6)` and `h6 < h3`,
the 4-cycles `0 2 6 4` and `0 2 3 4` are both weakly separated only on the triple tie
`h0 = h2 = h4`. -/
theorem tl_sep_core {h0 h2 h3 h4 h6 m0 m2 m3 m4 m6 : ℝ}
    (hm0 : 0 < m0) (hm2 : m2 < 0) (hm3 : 0 < m3) (hm4 : m4 < 0) (hm6 : 0 < m6)
    (hsum : m0 + m2 + m3 + m4 + m6 = 0)
    (hrad : m0 * h0 + m2 * h2 + m3 * h3 + m4 * h4 + m6 * h6 = 0)
    (h36 : h6 < h3) (hnt : ¬ (h0 = h2 ∧ h2 = h4)) :
    (¬ (h2 ≤ h0 ∧ h2 ≤ h6 ∧ h4 ≤ h0 ∧ h4 ≤ h6) ∧ ¬ (h0 ≤ h2 ∧ h0 ≤ h4 ∧ h6 ≤ h2 ∧ h6 ≤ h4)) ∨
    (¬ (h2 ≤ h0 ∧ h2 ≤ h3 ∧ h4 ≤ h0 ∧ h4 ≤ h3) ∧ ¬ (h0 ≤ h2 ∧ h0 ≤ h4 ∧ h3 ≤ h2 ∧ h3 ≤ h4)) := by
  have key : ¬ (((h0 ≤ h2 ∧ h0 ≤ h4 ∧ h6 ≤ h2 ∧ h6 ≤ h4) ∨ (h2 ≤ h0 ∧ h2 ≤ h6 ∧ h4 ≤ h0 ∧ h4 ≤ h6)) ∧
      ((h0 ≤ h2 ∧ h0 ≤ h4 ∧ h3 ≤ h2 ∧ h3 ≤ h4) ∨ (h2 ≤ h0 ∧ h2 ≤ h3 ∧ h4 ≤ h0 ∧ h4 ≤ h3))) := by
    rintro ⟨⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩ | ⟨b1, b2, b3, b4⟩⟩
    · have ht2 : min h2 h4 ≤ h2 := min_le_left _ _
      have ht4 : min h2 h4 ≤ h4 := min_le_right _ _
      have ht0 : h0 ≤ min h2 h4 := le_min a1 a2
      have ht3 : h3 ≤ min h2 h4 := le_min b3 b4
      have e : min h2 h4 * (m0 + m2 + m3 + m4 + m6) = 0 := by rw [hsum, mul_zero]
      nlinarith [mul_nonneg hm0.le (sub_nonneg.2 ht0), mul_nonneg hm3.le (sub_nonneg.2 ht3),
        mul_pos hm6 (sub_pos.2 (lt_of_lt_of_le h36 ht3)),
        mul_nonneg (neg_nonneg.2 hm2.le) (sub_nonneg.2 ht2),
        mul_nonneg (neg_nonneg.2 hm4.le) (sub_nonneg.2 ht4)]
    · exact hnt ⟨le_antisymm a1 b1, le_antisymm (by linarith) (by linarith)⟩
    · exact hnt ⟨le_antisymm b1 a1, le_antisymm (by linarith) (by linarith)⟩
    · have ht2 : h2 ≤ max h2 h4 := le_max_left _ _
      have ht4 : h4 ≤ max h2 h4 := le_max_right _ _
      have ht0 : max h2 h4 ≤ h0 := max_le a1 a3
      have ht6 : max h2 h4 ≤ h6 := max_le a2 a4
      have e : max h2 h4 * (m0 + m2 + m3 + m4 + m6) = 0 := by rw [hsum, mul_zero]
      nlinarith [mul_nonneg hm0.le (sub_nonneg.2 ht0), mul_nonneg hm6.le (sub_nonneg.2 ht6),
        mul_pos hm3 (sub_pos.2 (lt_of_le_of_lt ht6 h36)),
        mul_nonneg (neg_nonneg.2 hm2.le) (sub_nonneg.2 ht2),
        mul_nonneg (neg_nonneg.2 hm4.le) (sub_nonneg.2 ht4)]
  by_cases hA : (h0 ≤ h2 ∧ h0 ≤ h4 ∧ h6 ≤ h2 ∧ h6 ≤ h4) ∨ (h2 ≤ h0 ∧ h2 ≤ h6 ∧ h4 ≤ h0 ∧ h4 ≤ h6)
  · exact Or.inr ⟨fun h => key ⟨hA, Or.inr h⟩, fun h => key ⟨hA, Or.inl h⟩⟩
  · exact Or.inl ⟨fun h => hA (Or.inr h), fun h => hA (Or.inl h)⟩

/-! ### Cycles and facet signs -/

private def tl_c_pp : ZMod 4 → Fin 7 := ![0, 2, 6, 4]
private def tl_c_mm : ZMod 4 → Fin 7 := ![0, 2, 3, 4]

private theorem tl_c_pp_inj : Function.Injective tl_c_pp := by decide
private theorem tl_c_mm_inj : Function.Injective tl_c_mm := by decide

private theorem tl_cyc_pp : S0xCycUD s0x_S24 tl_c_pp {2, 3, 6, 7, 8} {0, 1, 4, 5} := by decide
private theorem tl_cyc_mm : S0xCycUD s0x_S24 tl_c_mm {2, 3, 6} {0, 1, 4, 5, 7, 8} := by decide

private theorem tl_close_k4 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    {c : ZMod 4 → Fin 7} {U Dn : Finset (Fin 9)}
    (hc : Function.Injective c) (hcyc : S0xCycUD s0x_S24 c U Dn)
    (w d1 d2 : ℝ³)
    (hU : ∀ t ∈ U, LexPos3 ⟪F.N t, w⟫ ⟪F.N t, d1⟫ ⟪F.N t, d2⟫)
    (hD : ∀ t ∈ Dn, LexPos3 (-⟪F.N t, w⟫) (-⟪F.N t, d1⟫) (-⟪F.N t, d2⟫))
    (hA : Minimality.GenQuad.LexClause (x (c 1)) (x (c 3)) (x (c 0)) (x (c 2)) w d1 d2)
    (hB : Minimality.GenQuad.LexClause (x (c 0)) (x (c 2)) (x (c 1)) (x (c 3)) w d1 d2) :
    Minimality.Gen.LexAny F :=
  Minimality.GenQuad.lexAny_of_clauses F (k := 4) (by norm_num) hc hcyc w d1 d2
    hU hD (Minimality.GenQuad.clauses_four (p := fun i => x (c i)) hA hB)

/-- Facets `7 = 236` and `8 = 346` against the two edge directions `x 2 - x 6`, `x 4 - x 6`. -/
theorem tl_n78 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    ⟪F.N 7, x 2 - x 6⟫ = 0 ∧ ⟪F.N 7, x 4 - x 6⟫ < 0 ∧
    ⟪F.N 8, x 2 - x 6⟫ < 0 ∧ ⟪F.N 8, x 4 - x 6⟫ = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← F.hN, F.zero 7 2 (by decide), F.zero 7 6 (by decide), sub_self]
  · rw [← F.hN, F.zero 7 6 (by decide), sub_zero]; exact F.neg 7 4 (by decide)
  · rw [← F.hN, F.zero 8 6 (by decide), sub_zero]; exact F.neg 8 2 (by decide)
  · rw [← F.hN, F.zero 8 4 (by decide), F.zero 8 6 (by decide), sub_self]

/-- `z3 > z6` at `w = x 3 - x 6`. -/
theorem tl_h36 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    ⟪x 6, x 3 - x 6⟫ < ⟪x 3, x 3 - x 6⟫ := by
  have hne : x 3 - x 6 ≠ 0 := sub_ne_zero.mpr ((inj_of_fac F).ne (by decide))
  have h := real_inner_self_pos.mpr hne
  rw [inner_sub_left] at h
  linarith

/-- A peak `p` lex below a valley `q`, tied at level 1 and decided at level 2. -/
theorem tl_lexLt2 {p q b d1 d2 : ℝ³} (h0 : ⟪p, b⟫ = ⟪q, b⟫) (h1 : 0 < ⟪q - p, d1⟫) :
    LexLt3 (⟪p, b⟫, ⟪p, d1⟫, ⟪p, d2⟫) (⟪q, b⟫, ⟪q, d1⟫, ⟪q, d2⟫) := by
  rw [inner_sub_left] at h1
  unfold LexLt3 LexPos3
  exact Or.inr ⟨by simp [h0], Or.inl (by simp only; linarith)⟩

/-! ### T1 -/

/-- **T1** (TIES24P): `w63_closes_mustar_pos` with the genericity hypothesis weakened to
"no triple tie `z0 = z2 = z4`" at `w63 = x 3 - x 6`. -/
theorem w63_closes_mustar_pos_nt {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hc3 : 1 < oblX6 x 3) (hmu : 0 < mustar x)
    (hnt : ¬ (⟪x 0, x 3 - x 6⟫ = ⟪x 2, x 3 - x 6⟫ ∧ ⟪x 2, x 3 - x 6⟫ = ⟪x 4, x 3 - x 6⟫)) :
    Minimality.Gen.LexAny F := by
  have hfac := w63_facings_gt F hc3 hmu
  obtain ⟨hm0, hm2, hm3, hm4, hm6⟩ := radon02346_signs F
  rcases tl_sep_core hm0 hm2 hm3 hm4 hm6 (radon02346_sum x) (radon02346_depth F (x 3 - x 6))
      (tl_h36 F) hnt with ⟨hnA2, hnA1⟩ | ⟨hnB2, hnB1⟩
  · obtain ⟨n72, n74, n82, n84⟩ := tl_n78 F
    let d1 : ℝ³ := (-1 : ℝ) • (x 4 - x 6) + (-1 : ℝ) • (x 2 - x 6)
    have hd7' : 0 < ⟪F.N 7, d1⟫ := by
      simp only [d1, inner_add_right, real_inner_smul_right]; linarith
    have hd8' : 0 < ⟪F.N 8, d1⟫ := by
      simp only [d1, inner_add_right, real_inner_smul_right]; linarith
    have hU : ∀ t ∈ ({2, 3, 6, 7, 8} : Finset (Fin 9)),
        LexPos3 ⟪F.N t, x 3 - x 6⟫ ⟪F.N t, d1⟫ ⟪F.N t, (0 : ℝ³)⟫ := by
      intro t ht
      fin_cases t <;> try exact absurd ht (by decide)
      · exact Or.inl hfac.2.2.1
      · exact Or.inl hfac.2.2.2.1
      · exact Or.inl hfac.2.2.2.2.2.2.1
      · exact Or.inr ⟨hfac.2.2.2.2.2.2.2.1, Or.inl hd7'⟩
      · exact Or.inr ⟨hfac.2.2.2.2.2.2.2.2, Or.inl hd8'⟩
    have hD : ∀ t ∈ ({0, 1, 4, 5} : Finset (Fin 9)),
        LexPos3 (-⟪F.N t, x 3 - x 6⟫) (-⟪F.N t, d1⟫) (-⟪F.N t, (0 : ℝ³)⟫) := by
      intro t ht
      fin_cases t <;> try exact absurd ht (by decide)
      · exact Or.inl (neg_pos.mpr hfac.1)
      · exact Or.inl (neg_pos.mpr hfac.2.1)
      · exact Or.inl (neg_pos.mpr hfac.2.2.2.2.1)
      · exact Or.inl (neg_pos.mpr hfac.2.2.2.2.2.1)
    exact tl_close_k4 F tl_c_pp_inj tl_cyc_pp _ d1 0 hU hD
      (Minimality.GenQuad.lexClause_of_notM hnA2) (Minimality.GenQuad.lexClause_of_notM hnA1)
  · obtain ⟨n72, n74, n82, n84⟩ := tl_n78 F
    let d1 : ℝ³ := (1 : ℝ) • (x 4 - x 6) + (1 : ℝ) • (x 2 - x 6)
    have hd7' : 0 < -⟪F.N 7, d1⟫ := by
      simp only [d1, inner_add_right, real_inner_smul_right]; linarith
    have hd8' : 0 < -⟪F.N 8, d1⟫ := by
      simp only [d1, inner_add_right, real_inner_smul_right]; linarith
    have hU : ∀ t ∈ ({2, 3, 6} : Finset (Fin 9)),
        LexPos3 ⟪F.N t, x 3 - x 6⟫ ⟪F.N t, d1⟫ ⟪F.N t, (0 : ℝ³)⟫ := by
      intro t ht
      fin_cases t <;> try exact absurd ht (by decide)
      · exact Or.inl hfac.2.2.1
      · exact Or.inl hfac.2.2.2.1
      · exact Or.inl hfac.2.2.2.2.2.2.1
    have hD : ∀ t ∈ ({0, 1, 4, 5, 7, 8} : Finset (Fin 9)),
        LexPos3 (-⟪F.N t, x 3 - x 6⟫) (-⟪F.N t, d1⟫) (-⟪F.N t, (0 : ℝ³)⟫) := by
      intro t ht
      fin_cases t <;> try exact absurd ht (by decide)
      · exact Or.inl (neg_pos.mpr hfac.1)
      · exact Or.inl (neg_pos.mpr hfac.2.1)
      · exact Or.inl (neg_pos.mpr hfac.2.2.2.2.1)
      · exact Or.inl (neg_pos.mpr hfac.2.2.2.2.2.1)
      · exact Or.inr ⟨neg_eq_zero.mpr hfac.2.2.2.2.2.2.2.1, Or.inl hd7'⟩
      · exact Or.inr ⟨neg_eq_zero.mpr hfac.2.2.2.2.2.2.2.2, Or.inl hd8'⟩
    exact tl_close_k4 F tl_c_mm_inj tl_cyc_mm _ d1 0 hU hD
      (Minimality.GenQuad.lexClause_of_notM hnB2) (Minimality.GenQuad.lexClause_of_notM hnB1)

/-! ### T2a -/

/-- On the triple tie, `z3` lies strictly above the common level. -/
theorem tl_h34 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (htie : ⟪x 0, x 3 - x 6⟫ = ⟪x 2, x 3 - x 6⟫ ∧ ⟪x 2, x 3 - x 6⟫ = ⟪x 4, x 3 - x 6⟫) :
    ⟪x 4, x 3 - x 6⟫ < ⟪x 3, x 3 - x 6⟫ := by
  obtain ⟨_, _, hm3, _, hm6⟩ := radon02346_signs F
  have hrad := radon02346_depth F (x 3 - x 6)
  have hsum := radon02346_sum x
  have h36 := tl_h36 F
  rw [htie.1, htie.2] at hrad
  by_contra hle
  push Not at hle
  have e : ⟪x 4, x 3 - x 6⟫ * (mu0 x + mu2 x + mu3 x + mu4 x + mu6 x) = 0 := by
    rw [hsum, mul_zero]
  nlinarith [mul_nonneg hm3.le (sub_nonneg.2 hle),
    mul_pos hm6 (sub_pos.2 (lt_of_lt_of_le h36 hle))]

/-- The T2a leaf for one choice of the two tilt directions `d1, d2 ∈ {x2 - x6, x4 - x6}`. -/
private theorem tl_triple_core {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hc3 : 1 < oblX6 x 3) (hmu : 0 < mustar x)
    (htie : ⟪x 0, x 3 - x 6⟫ = ⟪x 2, x 3 - x 6⟫ ∧ ⟪x 2, x 3 - x 6⟫ = ⟪x 4, x 3 - x 6⟫)
    (d1 d2 : ℝ³)
    (h7 : LexPos3 (-⟪F.N 7, x 3 - x 6⟫) (-⟪F.N 7, d1⟫) (-⟪F.N 7, d2⟫))
    (h8 : LexPos3 (-⟪F.N 8, x 3 - x 6⟫) (-⟪F.N 8, d1⟫) (-⟪F.N 8, d2⟫))
    (hneg : 0 < ⟪x 2 - x 0, d1⟫ ∨ 0 < ⟪x 4 - x 0, d1⟫) :
    Minimality.Gen.LexAny F := by
  have hfac := w63_facings_gt F hc3 hmu
  have h34 := tl_h34 F htie
  have hU : ∀ t ∈ ({2, 3, 6} : Finset (Fin 9)),
      LexPos3 ⟪F.N t, x 3 - x 6⟫ ⟪F.N t, d1⟫ ⟪F.N t, d2⟫ := by
    intro t ht
    fin_cases t <;> try exact absurd ht (by decide)
    · exact Or.inl hfac.2.2.1
    · exact Or.inl hfac.2.2.2.1
    · exact Or.inl hfac.2.2.2.2.2.2.1
  have hD : ∀ t ∈ ({0, 1, 4, 5, 7, 8} : Finset (Fin 9)),
      LexPos3 (-⟪F.N t, x 3 - x 6⟫) (-⟪F.N t, d1⟫) (-⟪F.N t, d2⟫) := by
    intro t ht
    fin_cases t <;> try exact absurd ht (by decide)
    · exact Or.inl (neg_pos.mpr hfac.1)
    · exact Or.inl (neg_pos.mpr hfac.2.1)
    · exact Or.inl (neg_pos.mpr hfac.2.2.2.2.1)
    · exact Or.inl (neg_pos.mpr hfac.2.2.2.2.2.1)
    · exact h7
    · exact h8
  have hA : Minimality.GenQuad.LexClause (x 2) (x 4) (x 0) (x 3) (x 3 - x 6) d1 d2 := by
    rcases hneg with h | h
    · exact Or.inl (tl_lexLt2 htie.1 h)
    · exact Or.inr (Or.inr (Or.inl (tl_lexLt2 (htie.1.trans htie.2) h)))
  have hB : Minimality.GenQuad.LexClause (x 0) (x 3) (x 2) (x 4) (x 3 - x 6) d1 d2 := by
    apply Minimality.GenQuad.lexClause_of_notM
    rintro ⟨_, _, _, h⟩
    linarith
  exact tl_close_k4 F tl_c_mm_inj tl_cyc_mm _ d1 d2 hU hD hA hB

/-- **T2a** (TIES24P): on the triple tie `z0 = z2 = z4` at `w63`, one negative number among
`⟪x0 - x2, x2 - x6⟫, ⟪x0 - x4, x2 - x6⟫, ⟪x0 - x2, x4 - x6⟫, ⟪x0 - x4, x4 - x6⟫` gives `LexAny`
(cycle `0 2 3 4`, tilts `(x2 - x6, x4 - x6)` resp. `(x4 - x6, x2 - x6)`). -/
theorem w63_closes_triple {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hc3 : 1 < oblX6 x 3) (hmu : 0 < mustar x)
    (htie : ⟪x 0, x 3 - x 6⟫ = ⟪x 2, x 3 - x 6⟫ ∧ ⟪x 2, x 3 - x 6⟫ = ⟪x 4, x 3 - x 6⟫)
    (hneg : ⟪x 0 - x 2, x 2 - x 6⟫ < 0 ∨ ⟪x 0 - x 4, x 2 - x 6⟫ < 0 ∨
      ⟪x 0 - x 2, x 4 - x 6⟫ < 0 ∨ ⟪x 0 - x 4, x 4 - x 6⟫ < 0) :
    Minimality.Gen.LexAny F := by
  have hfac := w63_facings_gt F hc3 hmu
  obtain ⟨n72, n74, n82, n84⟩ := tl_n78 F
  have sw : ∀ a b d : ℝ³, ⟪a - b, d⟫ < 0 → 0 < ⟪b - a, d⟫ := by
    intro a b d h; rw [← neg_sub, inner_neg_left]; linarith
  rcases hneg with h | h | h | h
  · refine tl_triple_core F hc3 hmu htie (x 2 - x 6) (x 4 - x 6) ?_ ?_ (Or.inl (sw _ _ _ h))
    · exact Or.inr ⟨by rw [hfac.2.2.2.2.2.2.2.1, neg_zero],
        Or.inr ⟨by rw [n72, neg_zero], neg_pos.mpr n74⟩⟩
    · exact Or.inr ⟨by rw [hfac.2.2.2.2.2.2.2.2, neg_zero], Or.inl (neg_pos.mpr n82)⟩
  · refine tl_triple_core F hc3 hmu htie (x 2 - x 6) (x 4 - x 6) ?_ ?_ (Or.inr (sw _ _ _ h))
    · exact Or.inr ⟨by rw [hfac.2.2.2.2.2.2.2.1, neg_zero],
        Or.inr ⟨by rw [n72, neg_zero], neg_pos.mpr n74⟩⟩
    · exact Or.inr ⟨by rw [hfac.2.2.2.2.2.2.2.2, neg_zero], Or.inl (neg_pos.mpr n82)⟩
  · refine tl_triple_core F hc3 hmu htie (x 4 - x 6) (x 2 - x 6) ?_ ?_ (Or.inl (sw _ _ _ h))
    · exact Or.inr ⟨by rw [hfac.2.2.2.2.2.2.2.1, neg_zero], Or.inl (neg_pos.mpr n74)⟩
    · exact Or.inr ⟨by rw [hfac.2.2.2.2.2.2.2.2, neg_zero],
        Or.inr ⟨by rw [n84, neg_zero], neg_pos.mpr n82⟩⟩
  · refine tl_triple_core F hc3 hmu htie (x 4 - x 6) (x 2 - x 6) ?_ ?_ (Or.inr (sw _ _ _ h))
    · exact Or.inr ⟨by rw [hfac.2.2.2.2.2.2.2.1, neg_zero], Or.inl (neg_pos.mpr n74)⟩
    · exact Or.inr ⟨by rw [hfac.2.2.2.2.2.2.2.2, neg_zero],
        Or.inr ⟨by rw [n84, neg_zero], neg_pos.mpr n82⟩⟩

/-- Exact `w63`-failure locus (`(*)` of TIES24P section 2): triple tie `z0 = z2 = z4` at `w63`
and all four star inner products `≥ 0`. -/
def W63Star (x : Fin 7 → ℝ³) : Prop :=
  (⟪x 0, x 3 - x 6⟫ = ⟪x 2, x 3 - x 6⟫ ∧ ⟪x 2, x 3 - x 6⟫ = ⟪x 4, x 3 - x 6⟫) ∧
    0 ≤ ⟪x 0 - x 2, x 2 - x 6⟫ ∧ 0 ≤ ⟪x 0 - x 4, x 2 - x 6⟫ ∧
    0 ≤ ⟪x 0 - x 2, x 4 - x 6⟫ ∧ 0 ≤ ⟪x 0 - x 4, x 4 - x 6⟫

/-- **T1 + T2a**: `w63` closes unless `W63Star x` holds. -/
theorem w63_closes_star {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hc3 : 1 < oblX6 x 3) (hmu : 0 < mustar x) (h : ¬ W63Star x) :
    Minimality.Gen.LexAny F := by
  by_cases htie : ⟪x 0, x 3 - x 6⟫ = ⟪x 2, x 3 - x 6⟫ ∧ ⟪x 2, x 3 - x 6⟫ = ⟪x 4, x 3 - x 6⟫
  · apply w63_closes_triple F hc3 hmu htie
    by_contra hn
    simp only [not_or, not_lt] at hn
    exact h ⟨htie, hn⟩
  · exact w63_closes_mustar_pos_nt F hc3 hmu htie

/-- **SEED63 region theorem**: on `{1 < c3, 0 < mustar}` with distinct `w63`-depths on
`{0, 2, 3, 4, 6}`, `w63 = x 3 - x 6` gives `LexAny F` (corollary of `w63_closes_mustar_pos_nt`). -/
theorem w63_closes_mustar_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hc3 : 1 < oblX6 x 3) (hmu : 0 < mustar x)
    (hgen : ∀ i ∈ ({0, 2, 3, 4, 6} : Finset (Fin 7)),
      ∀ j ∈ ({0, 2, 3, 4, 6} : Finset (Fin 7)), i ≠ j → ⟪x i, x 3 - x 6⟫ ≠ ⟪x j, x 3 - x 6⟫) :
    Minimality.Gen.LexAny F :=
  w63_closes_mustar_pos_nt F hc3 hmu fun ⟨h02, _⟩ =>
    hgen 0 (by decide) 2 (by decide) (by decide) h02

/-! ### `E23` mirrors (`pi24` transport) -/

private theorem tl_hyps_sym {x : Fin 7 → ℝ³} (hb3 : 1 < oblX2 x 3) (hmu : 0 < mu23 x) :
    1 < oblX6 (x ∘ pi24) 3 ∧ 0 < mustar (x ∘ pi24) :=
  ⟨by simpa [oblX6_comp_pi24, pi24_3] using hb3, by rwa [mustar_comp_pi24]⟩

/-- **T1'**: `e23_closes_mu23_pos` with the genericity hypothesis weakened to "no triple tie
`z0 = z6 = z5`" at `E23 = x 3 - x 2`. -/
theorem e23_closes_mu23_pos_nt {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hb3 : 1 < oblX2 x 3) (hmu : 0 < mu23 x)
    (hnt : ¬ (⟪x 0, x 3 - x 2⟫ = ⟪x 6, x 3 - x 2⟫ ∧ ⟪x 6, x 3 - x 2⟫ = ⟪x 5, x 3 - x 2⟫)) :
    Minimality.Gen.LexAny F := by
  obtain ⟨hc3', hmu'⟩ := tl_hyps_sym hb3 hmu
  refine lexAny_sym F (w63_closes_mustar_pos_nt (sym24 F) hc3' hmu' ?_)
  simpa only [Function.comp_apply, pi24_0, pi24_2, pi24_3, pi24_4, pi24_6] using hnt

/-- **T2a'**: on the triple tie `z0 = z6 = z5` at `E23`, one negative number among
`⟪x0 - x6, x6 - x2⟫, ⟪x0 - x5, x6 - x2⟫, ⟪x0 - x6, x5 - x2⟫, ⟪x0 - x5, x5 - x2⟫` gives `LexAny`. -/
theorem e23_closes_triple {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hb3 : 1 < oblX2 x 3) (hmu : 0 < mu23 x)
    (htie : ⟪x 0, x 3 - x 2⟫ = ⟪x 6, x 3 - x 2⟫ ∧ ⟪x 6, x 3 - x 2⟫ = ⟪x 5, x 3 - x 2⟫)
    (hneg : ⟪x 0 - x 6, x 6 - x 2⟫ < 0 ∨ ⟪x 0 - x 5, x 6 - x 2⟫ < 0 ∨
      ⟪x 0 - x 6, x 5 - x 2⟫ < 0 ∨ ⟪x 0 - x 5, x 5 - x 2⟫ < 0) :
    Minimality.Gen.LexAny F := by
  obtain ⟨hc3', hmu'⟩ := tl_hyps_sym hb3 hmu
  refine lexAny_sym F (w63_closes_triple (sym24 F) hc3' hmu' ?_ ?_)
  · simpa only [Function.comp_apply, pi24_0, pi24_2, pi24_3, pi24_4, pi24_6] using htie
  · simpa only [Function.comp_apply, pi24_0, pi24_2, pi24_3, pi24_4, pi24_6] using hneg

/-- Exact `E23`-failure locus (`(*)'`, `pi24` mirror of `W63Star`): triple tie `z0 = z6 = z5`
at `E23` and all four star inner products `≥ 0`. -/
def E23Star (x : Fin 7 → ℝ³) : Prop :=
  (⟪x 0, x 3 - x 2⟫ = ⟪x 6, x 3 - x 2⟫ ∧ ⟪x 6, x 3 - x 2⟫ = ⟪x 5, x 3 - x 2⟫) ∧
    0 ≤ ⟪x 0 - x 6, x 6 - x 2⟫ ∧ 0 ≤ ⟪x 0 - x 5, x 6 - x 2⟫ ∧
    0 ≤ ⟪x 0 - x 6, x 5 - x 2⟫ ∧ 0 ≤ ⟪x 0 - x 5, x 5 - x 2⟫

/-- **T1' + T2a'** at `E23`: closes unless `E23Star x` holds. -/
theorem e23_closes_star {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hb3 : 1 < oblX2 x 3) (hmu : 0 < mu23 x) (h : ¬ E23Star x) :
    Minimality.Gen.LexAny F := by
  obtain ⟨hc3', hmu'⟩ := tl_hyps_sym hb3 hmu
  refine lexAny_sym F (w63_closes_star (sym24 F) hc3' hmu' ?_)
  simpa only [W63Star, Function.comp_apply, pi24_0, pi24_2, pi24_3, pi24_4, pi24_6] using h

/-- **E23 single-view theorem** (`pi24` mirror of `w63_closes_mustar_pos`): corollary of
`e23_closes_mu23_pos_nt`. -/
theorem e23_closes_mu23_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hb3 : 1 < oblX2 x 3) (hmu : 0 < mu23 x)
    (hgen : ∀ i ∈ ({0, 2, 3, 5, 6} : Finset (Fin 7)),
      ∀ j ∈ ({0, 2, 3, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 3 - x 2⟫ ≠ ⟪x j, x 3 - x 2⟫) :
    Minimality.Gen.LexAny F :=
  e23_closes_mu23_pos_nt F hb3 hmu fun ⟨h06, _⟩ =>
    hgen 0 (by decide) 6 (by decide) (by decide) h06

end Minimality.T24.A20
