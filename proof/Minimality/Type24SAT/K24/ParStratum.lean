module

public import Minimality.Type24SAT.K24.ParS

@[expose] public section

/-!
# Type 24, `D` a parallelogram, `E ∥ G` (and `C ∥ I`): the stratum theorems

* `par_of_KD`: the SAT zero literals `KD0435 = KD0534 = 0` give `x 3 = x 4 + x 5 - x 0`.
* `rect_slide_left`, `rect_slide_right`: on `R` (`05 ⊥ 23`, `05 ⊥ 06`) the front vertices `1 2 6` all lie beyond
  the plane through `0` orthogonal to `04` as soon as `2` does, and all short of the plane through `4` as soon as
  `6` does.
* `isRupert_eg_notR2`: the stratum `D` parallelogram, `E ∥ G` is Rupert outside the double-overhang piece
  `R'' = {05 ⊥ 23, 05 ⊥ 06, ⟪x 6 - x 0, x 2 - x 3⟫ ≥ 0, ⟪x 2 - x 0, x 4 - x 0⟫ ≤ 0 ≤ ⟪x 6 - x 4, x 4 - x 0⟫}`.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.Par
open Minimality Minimality.H21 Minimality.T24.SAT

/-- A vector orthogonal to `g` lies in the span of `e` and `n` when `e, n, g` are pairwise orthogonal and nonzero. -/
theorem orth_decomp {e n g v : ℝ³} (he : e ≠ 0) (hn : n ≠ 0) (hg : g ≠ 0) (hen : ⟪e, n⟫ = 0)
    (heg : ⟪e, g⟫ = 0) (hng : ⟪n, g⟫ = 0) (hv : ⟪v, g⟫ = 0) :
    ∃ a b : ℝ, v = a • e + b • n := by
  have hee : 0 < ⟪e, e⟫ := real_inner_self_pos.2 he
  have hnn : 0 < ⟪n, n⟫ := real_inner_self_pos.2 hn
  have hc : cross e n ≠ 0 := by
    intro h
    have hb := h21_binet e n e n
    rw [h, inner_zero_left, hen, real_inner_comm e n, hen] at hb
    nlinarith [mul_pos hee hnn]
  set a := ⟪v, e⟫ / ⟪e, e⟫
  set b := ⟪v, n⟫ / ⟪n, n⟫
  set r := v - a • e - b • n with hr
  have ha : a * ⟪e, e⟫ = ⟪v, e⟫ := div_mul_cancel₀ _ hee.ne'
  have hb : b * ⟪n, n⟫ = ⟪v, n⟫ := div_mul_cancel₀ _ hnn.ne'
  have r1 : ⟪e, r⟫ = 0 := by
    rw [hr, inner_sub_right, inner_sub_right, inner_smul_right, inner_smul_right, hen, real_inner_comm v e]
    linarith
  have r2 : ⟪n, r⟫ = 0 := by
    rw [hr, inner_sub_right, inner_sub_right, inner_smul_right, inner_smul_right, real_inner_comm e n, hen,
      real_inner_comm v n]
    linarith
  obtain ⟨μ, hμ⟩ := h21_mul_cross hc r1 r2
  obtain ⟨μ', hμ'⟩ := h21_mul_cross hc heg (by rw [real_inner_comm, ← real_inner_comm g n]; exact hng)
  have hrg : ⟪r, g⟫ = 0 := by
    rw [hr, inner_sub_left, inner_sub_left, inner_smul_left, inner_smul_left, hv, heg, hng]; simp
  have hcc : 0 < ⟪cross e n, cross e n⟫ := real_inner_self_pos.2 hc
  have hμ'0 : μ' ≠ 0 := by rintro rfl; rw [zero_smul] at hμ'; exact hg hμ'
  have : μ * μ' * ⟪cross e n, cross e n⟫ = 0 := by
    rw [hμ, hμ', inner_smul_left, inner_smul_right] at hrg; simpa [mul_assoc] using hrg
  have hμ0 : μ = 0 := by
    rcases mul_eq_zero.1 this with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact h
      · exact absurd h hμ'0
    · exact absurd h hcc.ne'
  refine ⟨a, b, ?_⟩
  have : r = 0 := by rw [hμ, hμ0, zero_smul]
  rw [hr] at this
  linear_combination (norm := module) this

variable {x : Fin 7 → ℝ³}

/-- **The parallelogram from the SAT zero literals.**  `KD0435 = det3 (x0 - x4) (x3 - x5) N_D = 0` and
`KD0534 = det3 (x0 - x5) (x3 - x4) N_D = 0` (type 24 facet data): `x 3 = x 4 + x 5 - x 0`. -/
theorem par_of_KD (F : S0xFac 9 s0x_S24 x)
    (hD : det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0) :
    x 3 = x 4 + x 5 - x 0 := by
  have IS := F.inner_sub
  have zD0 := F.zero 3 0 (by decide); have zD3 := F.zero 3 3 (by decide)
  have zD4 := F.zero 3 4 (by decide); have zD5 := F.zero 3 5 (by decide)
  have hD2 := F.neg 3 2 (by decide)
  have zE0 := F.zero 4 0 (by decide); have zE4 := F.zero 4 4 (by decide)
  have hE5 := F.neg 4 5 (by decide); have hE3 := F.neg 4 3 (by decide)
  have zC0 := F.zero 2 0 (by decide); have zC5 := F.zero 2 5 (by decide)
  have hC4 := F.neg 2 4 (by decide); have hC3 := F.neg 2 3 (by decide)
  -- a vanishing `det3` of two vectors in `D` makes their cross product vanish
  have cr0 : ∀ a b : ℝ³, ⟪F.N 3, a⟫ = 0 → ⟪F.N 3, b⟫ = 0 → det3 a b (F.N 3) = 0 → cross a b = 0 := by
    intro a b ha hb h0
    by_contra hc
    obtain ⟨μ, hμ⟩ := h21_mul_cross hc (by rw [real_inner_comm]; exact ha) (by rw [real_inner_comm]; exact hb)
    have h1 : μ * ⟪cross a b, cross a b⟫ = 0 := by
      rw [det3, hμ, inner_smul_right] at h0; exact h0
    have hcc : 0 < ⟪cross a b, cross a b⟫ := real_inner_self_pos.2 hc
    have hμ0 : μ = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact h
      · exact absurd h hcc.ne'
    have : ⟪F.N 3, x 2 - x 0⟫ = 0 := by rw [hμ, hμ0, zero_smul, inner_zero_left]
    rw [IS, zD0] at this; linarith
  have c1 := cr0 _ _ (by rw [IS, zD0, zD4]; ring) (by rw [IS, zD3, zD5]; ring) hD.1
  have c2 := cr0 _ _ (by rw [IS, zD0, zD5]; ring) (by rw [IS, zD3, zD4]; ring) hD.2
  -- Binet with the facets `E` and `C`
  have b1 := h21_binet (F.N 4) (F.N 2) (x 0 - x 4) (x 3 - x 5)
  rw [c1, inner_zero_right, IS 4 0 4, zE0, zE4, IS 2 0 4, zC0] at b1
  have b2 := h21_binet (F.N 2) (F.N 4) (x 0 - x 5) (x 3 - x 4)
  rw [c2, inner_zero_right, IS 2 0 5, zC0, zC5, IS 4 0 5, zE0] at b2
  have hE35 : ⟪F.N 4, x 3 - x 5⟫ = 0 := by
    have : ⟪F.N 4, x 3 - x 5⟫ * F.f 2 (x 4) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · linarith
  have hC34 : ⟪F.N 2, x 3 - x 4⟫ = 0 := by
    have : ⟪F.N 2, x 3 - x 4⟫ * F.f 4 (x 5) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · linarith
  -- `r = x3 - x4 - x5 + x0` is orthogonal to `N_D`, `N_E`, `N_C`
  set r := x 3 - x 4 - x 5 + x 0 with hr
  have rD : ⟪F.N 3, r⟫ = 0 := by
    rw [show r = (x 3 - x 0) - (x 4 - x 0) - (x 5 - x 0) by rw [hr]; abel, inner_sub_right, inner_sub_right,
      IS, IS, IS, zD3, zD4, zD5, zD0]; ring
  have rE : ⟪F.N 4, r⟫ = 0 := by
    rw [show r = (x 3 - x 5) - (x 4 - x 0) by rw [hr]; abel, inner_sub_right, hE35, IS, zE4, zE0]; ring
  have rC : ⟪F.N 2, r⟫ = 0 := by
    rw [show r = (x 3 - x 4) - (x 5 - x 0) by rw [hr]; abel, inner_sub_right, hC34, IS, zC5, zC0]; ring
  have hED : cross (F.N 4) (F.N 3) ≠ 0 := by
    intro h
    have hb := h21_binet (F.N 4) (F.N 3) (x 5 - x 0) (x 2 - x 0)
    rw [h, inner_zero_left, IS, IS, IS, IS, zE0, zD0, zD5] at hb
    nlinarith [mul_pos (neg_pos.2 hE5) (neg_pos.2 hD2)]
  obtain ⟨μ, hμ⟩ := h21_mul_cross hED rE rD
  obtain ⟨l, hl⟩ := h21_mul_cross hED (by rw [IS, zE4, zE0]; ring : ⟪F.N 4, x 4 - x 0⟫ = 0)
    (by rw [IS, zD4, zD0]; ring : ⟪F.N 3, x 4 - x 0⟫ = 0)
  have hCc : ⟪F.N 2, cross (F.N 4) (F.N 3)⟫ ≠ 0 := by
    intro h0
    have : ⟪F.N 2, x 4 - x 0⟫ = 0 := by rw [hl, inner_smul_right, h0, mul_zero]
    rw [IS, zC0] at this; linarith
  have hμ0 : μ = 0 := by
    have : μ * ⟪F.N 2, cross (F.N 4) (F.N 3)⟫ = 0 := by rw [← inner_smul_right, ← hμ, rC]
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h hCc
  have : r = 0 := by rw [hμ, hμ0, zero_smul]
  rw [hr] at this
  linear_combination (norm := module) this

/-- The rectangle frame on `R`: `e = x 4 - x 0`, `N_D`, `g = x 5 - x 0` are pairwise orthogonal, and `N_C`, `N_I`
are orthogonal to `g`. -/
theorem rect_frame (F : S0xFac 9 s0x_S24 x) (hP : x 3 = x 4 + x 5 - x 0)
    (hE : ⟪F.N 4, x 2 - x 3⟫ = 0) (hw : ⟪x 5 - x 0, x 2 - x 3⟫ = 0)
    (hs : ⟪x 5 - x 0, x 6 - x 0⟫ = 0) :
    ⟪x 4 - x 0, x 5 - x 0⟫ = 0 ∧ ⟪x 4 - x 0, F.N 3⟫ = 0 ∧ ⟪F.N 3, x 5 - x 0⟫ = 0 ∧
      ⟪F.N 2, x 5 - x 0⟫ = 0 ∧ ⟪F.N 8, x 5 - x 0⟫ = 0 := by
  obtain ⟨q, u, -, -, -, -, hdec⟩ := eg_decomp F hP hE
  have IS := F.inner_sub
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hdec, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_comm (x 5 - x 0) (x 2 - x 3), hw, real_inner_comm (x 5 - x 0) (x 6 - x 0), hs]; ring
  · rw [real_inner_comm, IS, F.zero 3 4 (by decide), F.zero 3 0 (by decide)]; ring
  · rw [IS, F.zero 3 5 (by decide), F.zero 3 0 (by decide)]; ring
  · rw [IS, F.zero 2 5 (by decide), F.zero 2 0 (by decide)]; ring
  · rw [show x 5 - x 0 = x 3 - x 4 by rw [hP]; abel, IS, F.zero 8 3 (by decide), F.zero 8 4 (by decide)]; ring

/-- **Left end.**  On `R`, if `2` lies beyond the plane through `0` orthogonal to `04`, so do `1` and `6`. -/
theorem rect_slide_left (F : S0xFac 9 s0x_S24 x) (hP : x 3 = x 4 + x 5 - x 0)
    (hE : ⟪F.N 4, x 2 - x 3⟫ = 0) (hw : ⟪x 5 - x 0, x 2 - x 3⟫ = 0)
    (hs : ⟪x 5 - x 0, x 6 - x 0⟫ = 0) (h2 : 0 < ⟪x 2 - x 0, x 4 - x 0⟫) :
    ∀ i, i ∉ s0x_S24 3 → 0 < ⟪x i - x 0, x 4 - x 0⟫ := by
  obtain ⟨heg, hen, hng, hCg, -⟩ := rect_frame F hP hE hw hs
  have IS := F.inner_sub
  have hx := Minimality.H24.SAT.inj_of_fac F
  have he : x 4 - x 0 ≠ 0 := fun h => absurd (hx (sub_eq_zero.1 h)) (by decide)
  have hg : x 5 - x 0 ≠ 0 := fun h => absurd (hx (sub_eq_zero.1 h)) (by decide)
  have hD2 := F.neg 3 2 (by decide)
  have hn : F.N 3 ≠ 0 := by
    intro h; have := IS 3 2 0; rw [h, inner_zero_left, F.zero 3 0 (by decide)] at this; linarith
  obtain ⟨a, b, hab⟩ := orth_decomp he hn hg hen heg hng hCg
  have fC : ∀ i, F.f 2 (x i) = a * ⟪x i - x 0, x 4 - x 0⟫ + b * F.f 3 (x i) := by
    intro i
    have h1 := IS 2 i 0
    have h2 := IS 3 i 0
    rw [F.zero 2 0 (by decide), sub_zero] at h1
    rw [F.zero 3 0 (by decide), sub_zero] at h2
    rw [← h1, ← h2, hab, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_comm (x i - x 0) (x 4 - x 0), real_inner_comm (x i - x 0) (F.N 3)]
  have hee : 0 < ⟪x 4 - x 0, x 4 - x 0⟫ := real_inner_self_pos.2 he
  have ha : a < 0 := by
    have := fC 4
    rw [F.zero 3 4 (by decide), mul_zero, add_zero] at this
    have hC4 := F.neg 2 4 (by decide)
    by_contra h; push Not at h; nlinarith
  have hb : b < 0 := by
    have := fC 2
    rw [F.zero 2 2 (by decide)] at this
    by_contra h; push Not at h; nlinarith [mul_pos (neg_pos.2 ha) h2]
  intro i hi
  have key : ∀ j : Fin 7, j ∉ s0x_S24 3 → j ∉ s0x_S24 2 → F.f 2 (x j) < 0 ∧ F.f 3 (x j) < 0 :=
    fun j h3 h2 => ⟨F.neg 2 j h2, F.neg 3 j h3⟩
  by_cases hi2 : i ∈ s0x_S24 2
  · have : i = 2 := by revert i; decide
    subst this; exact h2
  · obtain ⟨k1, k2⟩ := key i hi hi2
    have := fC i
    by_contra h; push Not at h; nlinarith [mul_pos (neg_pos.2 hb) (neg_pos.2 k2), mul_nonneg_of_nonpos_of_nonpos ha.le h]

/-- **Right end.**  On `R`, if `6` lies short of the plane through `4` orthogonal to `04`, so do `1` and `2`. -/
theorem rect_slide_right (F : S0xFac 9 s0x_S24 x) (hP : x 3 = x 4 + x 5 - x 0)
    (hE : ⟪F.N 4, x 2 - x 3⟫ = 0) (hw : ⟪x 5 - x 0, x 2 - x 3⟫ = 0)
    (hs : ⟪x 5 - x 0, x 6 - x 0⟫ = 0) (h6 : ⟪x 6 - x 0, x 4 - x 0⟫ < ⟪x 4 - x 0, x 4 - x 0⟫) :
    ∀ i, i ∉ s0x_S24 3 → ⟪x i - x 0, x 4 - x 0⟫ < ⟪x 4 - x 0, x 4 - x 0⟫ := by
  obtain ⟨heg, hen, hng, -, hIg⟩ := rect_frame F hP hE hw hs
  have IS := F.inner_sub
  have hx := Minimality.H24.SAT.inj_of_fac F
  have he : x 4 - x 0 ≠ 0 := fun h => absurd (hx (sub_eq_zero.1 h)) (by decide)
  have hg : x 5 - x 0 ≠ 0 := fun h => absurd (hx (sub_eq_zero.1 h)) (by decide)
  have hD2 := F.neg 3 2 (by decide)
  have hn : F.N 3 ≠ 0 := by
    intro h; have := IS 3 2 0; rw [h, inner_zero_left, F.zero 3 0 (by decide)] at this; linarith
  obtain ⟨a, b, hab⟩ := orth_decomp he hn hg hen heg hng hIg
  have fI : ∀ i, F.f 8 (x i) = a * (⟪x i - x 0, x 4 - x 0⟫ - ⟪x 4 - x 0, x 4 - x 0⟫) + b * F.f 3 (x i) := by
    intro i
    have h1 := IS 8 i 4
    have h2 := IS 3 i 4
    rw [F.zero 8 4 (by decide), sub_zero] at h1
    rw [F.zero 3 4 (by decide), sub_zero] at h2
    rw [← h1, ← h2, hab, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    have : ⟪x 4 - x 0, x i - x 4⟫ = ⟪x i - x 0, x 4 - x 0⟫ - ⟪x 4 - x 0, x 4 - x 0⟫ := by
      rw [show x i - x 4 = (x i - x 0) - (x 4 - x 0) by abel, inner_sub_right,
        real_inner_comm (x i - x 0) (x 4 - x 0)]
    rw [this]
  have hee : 0 < ⟪x 4 - x 0, x 4 - x 0⟫ := real_inner_self_pos.2 he
  have ha : 0 < a := by
    have := fI 0
    rw [F.zero 3 0 (by decide), mul_zero, add_zero, sub_self, inner_zero_left, zero_sub] at this
    have hI0 := F.neg 8 0 (by decide)
    by_contra h; push Not at h; nlinarith
  have hb : b < 0 := by
    have := fI 6
    rw [F.zero 8 6 (by decide)] at this
    have hD6 := F.neg 3 6 (by decide)
    by_contra h; push Not at h; nlinarith [mul_pos ha (sub_pos.2 h6)]
  intro i hi
  by_cases hi8 : i ∈ s0x_S24 8
  · have : i = 6 := by revert i; decide
    subst this; exact h6
  · have k1 := F.neg 8 i hi8
    have k2 := F.neg 3 i hi
    have := fI i
    by_contra h; push Not at h
    nlinarith [mul_pos (neg_pos.2 hb) (neg_pos.2 k2), mul_nonneg ha.le (sub_nonneg.2 h)]

/-- **The stratum `D` parallelogram, `E ∥ G`, outside the double overhang `R''`.**  `E ∥ G` enters only as
`⟪N_E, x 2 - x 3⟫ = 0`.  Cases: off the wall `05 ⊥ 23` (`isRupert_eg_offWall`); on it, `s < 0`, `h < 0` or `h, s > 0`
(`isRupert_eg_wall`); `h = 0 < s` (`isRupert_eg_h0`); `s = 0` without double overhang (`isRupert_eg_rect`). -/
theorem isRupert_eg_notR2 (F : S0xFac 9 s0x_S24 x) (hP : x 3 = x 4 + x 5 - x 0)
    (hE : ⟪F.N 4, x 2 - x 3⟫ = 0)
    (hR : ¬ (⟪x 5 - x 0, x 2 - x 3⟫ = 0 ∧ ⟪x 5 - x 0, x 6 - x 0⟫ = 0 ∧ 0 ≤ ⟪x 6 - x 0, x 2 - x 3⟫ ∧
      ⟪x 2 - x 0, x 4 - x 0⟫ ≤ 0 ∧ ⟪x 4 - x 0, x 4 - x 0⟫ ≤ ⟪x 6 - x 0, x 4 - x 0⟫)) :
    IsRupert (univ.image x) := by
  by_cases hw : ⟪x 5 - x 0, x 2 - x 3⟫ = 0
  swap
  · exact isRupert_eg_offWall F hP hE hw
  by_cases hW : ⟪x 5 - x 0, x 6 - x 0⟫ < 0 ∨ ⟪x 6 - x 0, x 2 - x 3⟫ < 0 ∨
      (0 < ⟪x 6 - x 0, x 2 - x 3⟫ ∧ 0 < ⟪x 5 - x 0, x 6 - x 0⟫)
  · exact isRupert_eg_wall F hP hE hw hW
  push Not at hW
  obtain ⟨hs0, hh0, hhs⟩ := hW
  rcases hs0.lt_or_eq with hs | hs
  · have hh : ⟪x 6 - x 0, x 2 - x 3⟫ = 0 := le_antisymm (not_lt.1 fun h => absurd (hhs h) (not_le.2 hs)) hh0
    exact isRupert_eg_h0 F hP hE hh hs
  · have hs' : ⟪x 5 - x 0, x 6 - x 0⟫ = 0 := hs.symm
    refine isRupert_eg_rect F hP hE hw hs' ?_
    by_cases h2 : ⟪x 2 - x 0, x 4 - x 0⟫ ≤ 0
    · have h6 : ⟪x 6 - x 0, x 4 - x 0⟫ < ⟪x 4 - x 0, x 4 - x 0⟫ := by
        by_contra h6; push Not at h6; exact hR ⟨hw, hs', hh0, h2, h6⟩
      exact Or.inr (rect_slide_right F hP hE hw hs' h6)
    · exact Or.inl (rect_slide_left F hP hE hw hs' (not_le.1 h2))

/-- **The `E ∥ G` stratum from the SAT-level facts** (outside `R''`): the zero literals `KD0435 = KD0534 = 0` and
`E:23 = 0` (`E:25 = 0` is not needed). -/
theorem isRupert_parEG_of_notR2 (F : S0xFac 9 s0x_S24 x)
    (hD : det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0)
    (hEG : ⟪F.N 4, x 2 - x 3⟫ = 0)
    (hR : ¬ (⟪x 5 - x 0, x 2 - x 3⟫ = 0 ∧ ⟪x 5 - x 0, x 6 - x 0⟫ = 0 ∧ 0 ≤ ⟪x 6 - x 0, x 2 - x 3⟫ ∧
      ⟪x 2 - x 0, x 4 - x 0⟫ ≤ 0 ∧ ⟪x 4 - x 0, x 4 - x 0⟫ ≤ ⟪x 6 - x 0, x 4 - x 0⟫)) :
    IsRupert (univ.image x) :=
  isRupert_eg_notR2 F (par_of_KD F hD) hEG hR

open Minimality.H24K.SAT in
/-- **The `C ∥ I` stratum outside `R''`** (the image of `isRupert_eg_notR2` under `σ = (2 6)(4 5)`). -/
theorem isRupert_ci_notR2 (F : S0xFac 9 s0x_S24 x) (hP : x 3 = x 4 + x 5 - x 0)
    (hC : ⟪F.N 2, x 6 - x 3⟫ = 0)
    (hR : ¬ (⟪x 4 - x 0, x 6 - x 3⟫ = 0 ∧ ⟪x 4 - x 0, x 2 - x 0⟫ = 0 ∧ 0 ≤ ⟪x 2 - x 0, x 6 - x 3⟫ ∧
      ⟪x 6 - x 0, x 5 - x 0⟫ ≤ 0 ∧ ⟪x 5 - x 0, x 5 - x 0⟫ ≤ ⟪x 2 - x 0, x 5 - x 0⟫)) :
    IsRupert (univ.image x) := by
  have h := isRupert_eg_notR2 (facSig F) (x := x ∘ wallSig)
    (by show x 3 = x 5 + x 4 - x 0; rw [hP]; abel) hC hR
  have e : Finset.univ.image (x ∘ wallSig) = Finset.univ.image x := by
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨wallSig i, by rw [wallSig_invol]⟩
  rwa [e] at h

/-- **The `C ∥ I` stratum from the SAT-level facts** (outside `R''`): `KD0435 = KD0534 = 0` and `C:36 = 0`. -/
theorem isRupert_parCI_of_notR2 (F : S0xFac 9 s0x_S24 x)
    (hD : det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0)
    (hCI : ⟪F.N 2, x 3 - x 6⟫ = 0)
    (hR : ¬ (⟪x 4 - x 0, x 6 - x 3⟫ = 0 ∧ ⟪x 4 - x 0, x 2 - x 0⟫ = 0 ∧ 0 ≤ ⟪x 2 - x 0, x 6 - x 3⟫ ∧
      ⟪x 6 - x 0, x 5 - x 0⟫ ≤ 0 ∧ ⟪x 5 - x 0, x 5 - x 0⟫ ≤ ⟪x 2 - x 0, x 5 - x 0⟫)) :
    IsRupert (univ.image x) :=
  isRupert_ci_notR2 F (par_of_KD F hD)
    (by rw [show x 6 - x 3 = -(x 3 - x 6) by abel, inner_neg_right, hCI, neg_zero]) hR

end Minimality.T24.Par
