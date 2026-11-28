module

public import Minimality.Type24OffOB1K0

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.T24.Stmt Minimality.T24.Q45
  Minimality.T24.Reg Minimality.T24.A19

/-!
# Type 24 off `OB1`: the B2 valley corners off the tie-section cone (job OSPEC28)

nopert229 notes/OPENSPECIAL-STRATEGY.md section 2p.  On the B2 branch `T234BrJ` the view `b = t234b` lies in the
direction plane of the tie plane, which is spanned by the two tie-section edges `u = x5 - x2`, `v = x6 - x2` at `x 2`.
The Cramer identity `b2c_span_id` writes `n234` in that basis:

  `⟪N, n234⟫ D = |E|² (t234C ⟪N, u⟫ - c25 ⟪N, v⟫)`,  `D = ⟪u, v × E⟫`, `c25 = ⟪x2 - x3, x2 - x5⟫ > 0`.

So for every facet through `x 2` the level-1 sign is a sign combination of its values at `x 5` and `x 6`:

* `025` (through `2`, `5`) and `235` (through `2`, `3`, `5`) have the same sign at `t234b` on the whole branch, and `235`
  is up: **`025` up** (`b2c_up2`).  This removes the `X6 < 0` corner (`012` down, `016` up, `025` down, `046` up).
* `012` (off `5`, `6`) and `236` (through `2`, `6`): with `t234C < 0` both coefficients have one sign and `236` is up:
  **`012` up** (`b2c_up0_of_neg`).

`046` (the tangent cone at `x 6` cannot decide it off the cone) by the Cramer identity of the edge `4 6` against
`346`: `f8(x0) ⟪N4, n⟫ ⟪x6 - x2, n⟫ X6 = -f4(x3) f8(x2) Qd X6` with
`Qd = ⟪x0 - x4, E⟫ ⟪x6 - x4, g⟫ - ⟪x0 - x4, g⟫ ⟪x6 - x4, E⟫` (`b2c_dn4_prod`): for `X6 > 0`, `046` is down when
`Qd > 0` (`b2c_dn4_of`; the census finds the converse on every sampled point).  Geometrically: the plane through the edge
`4 6` parallel to `b` separates `x 0` from `x 3`.  From the face `0345`, `(s + t - 1) Qd = X6 + t m k` (`m = ⟪x5 - x4,
E⟫ ≤ 0`, `k = ⟪x6 - x5, g⟫ = c25 - t234C`, `X6 - |E|² k = X5 > 0`), so **`Qd > 0` whenever the angle `0 4 3` is not
acute** (`b2c_qd_pos`), and an acute angle `0 4 3` needs an obtuse face angle at `0` (`⟪e4, e5⟫ < 0`).

Residue: on the branch only the special positions of the cone, `t234C < 0` with `Qd ≤ 0` (then `0 4 3` acute and
`⟪e4, e5⟫ < 0`), and `X6 < 0` with `012` edge-on at all three levels remain (`b2c_letters`, `B2CRes`).
`Q45ResWR2B` / **`OpenSpecialR2B`** (`openSpecialR2B_iff_R2U`) on top of `Q45ResWR2U`, and `Q45ResWR4` /
**`OpenSpecialR4`** (`openSpecialR4_iff_R3`) on top of OSPEC27's `Q45ResWR3`; chains `..._R2B`, `..._R4`.
-/

namespace Minimality.T24.OSpec

section B2C
open Minimality.LexCell

variable {x : Fin 7 → ℝ³}

/-- Cramer's rule dotted with `N`: `⟪N, d⟫ det[a, b, c] = ⟪N, a⟫ det[d, b, c] + ⟪N, b⟫ det[a, d, c] + ⟪N, c⟫ det[a, b, d]`. -/
theorem b2c_cramer (N a b c d : ℝ³) :
    ⟪N, d⟫ * ⟪a, cross b c⟫ =
      ⟪N, a⟫ * ⟪d, cross b c⟫ + ⟪N, b⟫ * ⟪a, cross d c⟫ + ⟪N, c⟫ * ⟪a, cross b d⟫ := by
  simp only [t234_inner3, cross_apply_zero, cross_apply_one, cross_apply_two]; ring

/-- `det[a, b, E × g] = ⟪a, E⟫ ⟪b, g⟫ - ⟪a, g⟫ ⟪b, E⟫`. -/
theorem b2c_binet (a b E g : ℝ³) : ⟪a, cross b (cross E g)⟫ = ⟪a, E⟫ * ⟪b, g⟫ - ⟪a, g⟫ * ⟪b, E⟫ := by
  simp only [t234_inner3, cross_apply_zero, cross_apply_one, cross_apply_two]; ring

/-- `det[E × g, v, E] = ⟪v, E⟫ ⟪E, g⟫ - ⟪v, g⟫ |E|²`. -/
theorem b2c_binet2 (v E g : ℝ³) : ⟪cross E g, cross v E⟫ = ⟪v, E⟫ * ⟪E, g⟫ - ⟪v, g⟫ * ⟪E, E⟫ := by
  simp only [t234_inner3, cross_apply_zero, cross_apply_one, cross_apply_two]; ring

/-- `det[u, E × g, E] = ⟪u, g⟫ |E|² - ⟪u, E⟫ ⟪E, g⟫`. -/
theorem b2c_binet3 (u E g : ℝ³) : ⟪u, cross (cross E g) E⟫ = ⟪u, g⟫ * ⟪E, E⟫ - ⟪u, E⟫ * ⟪E, g⟫ := by
  simp only [t234_inner3, cross_apply_zero, cross_apply_one, cross_apply_two]; ring

/-- **The view in the basis of two tie-plane vectors** (`u, v ⊥ E`): `⟪N, E × g⟫ ⟪u, v × E⟫ = |E|² (⟪u, g⟫ ⟪N, v⟫ -
⟪v, g⟫ ⟪N, u⟫)`. -/
theorem b2c_span_id (N E g u v : ℝ³) (hu : ⟪u, E⟫ = 0) (hv : ⟪v, E⟫ = 0) :
    ⟪N, cross E g⟫ * ⟪u, cross v E⟫ = ⟪E, E⟫ * (⟪u, g⟫ * ⟪N, v⟫ - ⟪v, g⟫ * ⟪N, u⟫) := by
  have c := b2c_cramer N u v E (cross E g)
  rw [b2c_binet2, b2c_binet3, b2c_binet, hu, hv] at c
  linear_combination c

/-- `D = det[x5 - x2, x6 - x2, x4 - x3]`. -/
noncomputable def b2cD (x : Fin 7 → ℝ³) : ℝ := ⟪x 5 - x 2, cross (x 6 - x 2) (x 4 - x 3)⟫

/-- `c25 = ⟪x2 - x3, x2 - x5⟫`. -/
noncomputable def b2cC25 (x : Fin 7 → ℝ³) : ℝ := ⟪x 2 - x 3, x 2 - x 5⟫

/-- The ties of `T234BrJ` as orthogonality to `E = x4 - x3`. -/
theorem b2c_ties (F : S0xFac 9 s0x_S24 x) (hB : T234BrJ F) :
    ⟪x 5 - x 2, x 4 - x 3⟫ = 0 ∧ ⟪x 6 - x 2, x 4 - x 3⟫ = 0 := by
  obtain ⟨⟨-, -, -, -, -, -, htie, -⟩, h56, -⟩ := hB
  constructor
  · simp only [t234_inner3, PiLp.sub_apply] at htie ⊢; linear_combination htie
  · simp only [t234_inner3, PiLp.sub_apply] at htie h56 ⊢; linear_combination htie + h56

/-- **The facet identity at `x 2`** on `T234BrJ`: `⟪N, n234⟫ D = |E|² (t234C ⟪N, x5 - x2⟫ - c25 ⟪N, x6 - x2⟫)`. -/
theorem b2c_fac_id (F : S0xFac 9 s0x_S24 x) (hB : T234BrJ F) (N : ℝ³) :
    ⟪N, n234 x⟫ * b2cD x = ⟪x 4 - x 3, x 4 - x 3⟫ * (t234C x * ⟪N, x 5 - x 2⟫ - b2cC25 x * ⟪N, x 6 - x 2⟫) := by
  obtain ⟨hu, hv⟩ := b2c_ties F hB
  rw [n234_eq, b2cD, b2c_span_id N _ _ _ _ hu hv, t234C, b2cC25]
  have e1 : ⟪x 5 - x 2, x 2 - x 3⟫ = -⟪x 2 - x 3, x 2 - x 5⟫ := by
    simp only [t234_inner3, PiLp.sub_apply]; ring
  have e2 : ⟪x 6 - x 2, x 2 - x 3⟫ = -⟪x 2 - x 3, x 2 - x 6⟫ := by
    simp only [t234_inner3, PiLp.sub_apply]; ring
  rw [e1, e2]; ring

/-- `c25 > 0` on the branch (`c25 = ⟪x5 - x3, d⟫ + |d|²`, `d = x2 - x5 ≠ 0`, `t234_da`). -/
theorem b2c_c25_pos (F : S0xFac 9 s0x_S24 x) (hB : T234BrJ F) : 0 < b2cC25 x := by
  obtain ⟨⟨s, t, hs, ht, hd, -, htie, h25⟩, -, -⟩ := hB
  have hda := t234_da hs ht hd htie h25
  have hd0 : x 2 - x 5 ≠ 0 := by
    intro h0
    have h3 := F.inner_sub 3 2 5
    rw [h0, inner_zero_right, F.zero 3 5 (by decide)] at h3
    have := F.neg 3 2 (by decide); linarith
  have hdd : 0 < ⟪x 2 - x 5, x 2 - x 5⟫ := real_inner_self_pos.mpr hd0
  have e : b2cC25 x = ⟪x 2 - x 5, x 5 - x 3⟫ + ⟪x 2 - x 5, x 2 - x 5⟫ := by
    rw [b2cC25]; simp only [t234_inner3, PiLp.sub_apply]; ring
  rw [e]; linarith

theorem b2c_ee_pos (F : S0xFac 9 s0x_S24 x) : 0 < ⟪x 4 - x 3, x 4 - x 3⟫ := by
  have := t234_lt34 F
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  rw [inner_sub_right, inner_sub_right] at this
  nlinarith [real_inner_comm (x 3) (x 4)]

/-- `⟪v, t234b⟫ ⟪w, t234b⟫ = ⟪v, n234⟫ ⟪w, n234⟫`. -/
theorem b2c_prod (v w : ℝ³) : ⟪v, t234b x⟫ * ⟪w, t234b x⟫ = ⟪v, n234 x⟫ * ⟪w, n234 x⟫ := by
  rcases t234b_cases x with e | e <;> rw [e]
  rw [inner_neg_right, inner_neg_right, neg_mul_neg]

/-- `235` is up at level 1 (strict) on `T234BrJ`. -/
theorem b2c_up6_pos (F : S0xFac 9 s0x_S24 x) (hB : T234BrJ F) : 0 < ⟪F.N 6, t234b x⟫ := by
  obtain ⟨⟨s, t, hs, ht, hd, hb1, htie, h25⟩, h56, h35⟩ := hB
  have hp := t234_up6_prod F hs ht hd htie h56 h35 h25
  have h5 := (t234_derived F ⟨s, t, hs, ht, hd, hb1, htie, h25⟩).1
  rw [← b2c_prod] at hp
  by_contra hc
  nlinarith [mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hc) h5.le]

/-- **`025` is up at `t234b` on the whole B2 branch**: `⟪N2, n⟫ D` and `⟪N6, n⟫ D` are `-|E|² c25 f(x6)` for the
facets `025` and `235`, so the two facets have one sign at level 1, and `235` is up. -/
theorem b2c_up2 (F : S0xFac 9 s0x_S24 x) (hB : T234BrJ F) : 0 < ⟪F.N 2, t234b x⟫ := by
  have I2 := b2c_fac_id F hB (F.N 2)
  have I6 := b2c_fac_id F hB (F.N 6)
  rw [F.inner_sub 2 5 2, F.inner_sub 2 6 2, F.zero 2 5 (by decide), F.zero 2 2 (by decide)] at I2
  rw [F.inner_sub 6 5 2, F.inner_sub 6 6 2, F.zero 6 5 (by decide), F.zero 6 2 (by decide)] at I6
  have f26 : F.f 2 (x 6) < 0 := F.neg 2 6 (by decide)
  have f66 : F.f 6 (x 6) < 0 := F.neg 6 6 (by decide)
  have hc := b2c_c25_pos F hB
  have hE := b2c_ee_pos F
  have hK : 0 < ⟪x 4 - x 3, x 4 - x 3⟫ * b2cC25 x := mul_pos hE hc
  have key : ⟪F.N 2, n234 x⟫ * ⟪F.N 6, n234 x⟫ * (b2cD x * b2cD x) =
      (⟪x 4 - x 3, x 4 - x 3⟫ * b2cC25 x) ^ 2 * (F.f 2 (x 6) * F.f 6 (x 6)) := by
    linear_combination (⟪F.N 6, n234 x⟫ * b2cD x) * I2 +
      (⟪x 4 - x 3, x 4 - x 3⟫ * (t234C x * (0 - 0) - b2cC25 x * (F.f 2 (x 6) - 0))) * I6
  have hpos : 0 < ⟪F.N 2, n234 x⟫ * ⟪F.N 6, n234 x⟫ := by
    by_contra hn
    have : ⟪F.N 2, n234 x⟫ * ⟪F.N 6, n234 x⟫ * (b2cD x * b2cD x) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hn) (mul_self_nonneg _)
    nlinarith [mul_pos (pow_pos hK 2) (mul_pos_of_neg_of_neg f26 f66)]
  rw [← b2c_prod] at hpos
  have h6 := b2c_up6_pos F hB
  by_contra hn
  nlinarith [mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hn) h6.le]

/-- `236` is up at level 1 (strict) when `t234C < 0` (`t234_prod7`). -/
theorem b2c_up7_pos (F : S0xFac 9 s0x_S24 x) (hB : T234BrJ F) (hc : t234C x < 0) : 0 < ⟪F.N 7, t234b x⟫ := by
  have hq := t234_z6 F hB.1
  obtain ⟨htau, e6, -⟩ := t234_tau_eqs F hB
  have htie26 : ⟪x 2, x 3 - x 4⟫ = ⟪x 6, x 3 - x 4⟫ := by
    obtain ⟨⟨-, -, -, -, -, -, htie, -⟩, h56, -⟩ := hB; exact htie.trans h56
  have hp := t234_prod7 F htie26
  rw [← b2c_prod, e6] at hp
  have f74 : F.f 7 (x 4) < 0 := F.neg 7 4 (by decide)
  have : ⟪F.N 7, t234b x⟫ * ⟪x 6 - x 2, t234b x⟫ < 0 := by
    rw [hp, ← t234C]; nlinarith [mul_pos (neg_pos.mpr f74) (mul_pos htau (neg_pos.mpr hc))]
  by_contra hn
  nlinarith [mul_nonneg_of_nonpos_of_nonpos (not_lt.mp hn) hq.le]

/-- **`012` is up at `t234b` when `t234C < 0`**: `⟪N0, n⟫ D = |E|² (t234C f0(x5) - c25 f0(x6))` and `⟪N7, n⟫ D = |E|²
t234C f7(x5)` are both positive multiples of `|E|²`, and `236` is up. -/
theorem b2c_up0_of_neg (F : S0xFac 9 s0x_S24 x) (hB : T234BrJ F) (hc : t234C x < 0) : 0 < ⟪F.N 0, t234b x⟫ := by
  have I0 := b2c_fac_id F hB (F.N 0)
  have I7 := b2c_fac_id F hB (F.N 7)
  rw [F.inner_sub 0 5 2, F.inner_sub 0 6 2, F.zero 0 2 (by decide)] at I0
  rw [F.inner_sub 7 5 2, F.inner_sub 7 6 2, F.zero 7 6 (by decide), F.zero 7 2 (by decide)] at I7
  have f05 : F.f 0 (x 5) < 0 := F.neg 0 5 (by decide)
  have f06 : F.f 0 (x 6) < 0 := F.neg 0 6 (by decide)
  have f75 : F.f 7 (x 5) < 0 := F.neg 7 5 (by decide)
  have hC := b2c_c25_pos F hB
  have hE := b2c_ee_pos F
  have hA : 0 < t234C x * (F.f 0 (x 5) - 0) - b2cC25 x * (F.f 0 (x 6) - 0) := by
    nlinarith [mul_pos_of_neg_of_neg hc f05, mul_pos hC (neg_pos.mpr f06)]
  have hB7 : 0 < t234C x * (F.f 7 (x 5) - 0) - b2cC25 x * (0 - 0) := by
    nlinarith [mul_pos_of_neg_of_neg hc f75]
  have key : ⟪F.N 0, n234 x⟫ * ⟪F.N 7, n234 x⟫ * (b2cD x * b2cD x) =
      ⟪x 4 - x 3, x 4 - x 3⟫ ^ 2 * ((t234C x * (F.f 0 (x 5) - 0) - b2cC25 x * (F.f 0 (x 6) - 0)) *
        (t234C x * (F.f 7 (x 5) - 0) - b2cC25 x * (0 - 0))) := by
    linear_combination (⟪F.N 7, n234 x⟫ * b2cD x) * I0 +
      (⟪x 4 - x 3, x 4 - x 3⟫ * (t234C x * (F.f 0 (x 5) - 0) - b2cC25 x * (F.f 0 (x 6) - 0))) * I7
  have hpos : 0 < ⟪F.N 0, n234 x⟫ * ⟪F.N 7, n234 x⟫ := by
    by_contra hn
    have : ⟪F.N 0, n234 x⟫ * ⟪F.N 7, n234 x⟫ * (b2cD x * b2cD x) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hn) (mul_self_nonneg _)
    nlinarith [mul_pos (pow_pos hE 2) (mul_pos hA hB7)]
  rw [← b2c_prod] at hpos
  have h7 := b2c_up7_pos F hB hc
  by_contra hn
  nlinarith [mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hn) h7.le]

/-! ### `046` through the edge `4 6` -/

/-- `Qd = det[x0 - x4, x6 - x4, n234] = ⟪x0 - x4, E⟫ ⟪x6 - x4, g⟫ - ⟪x0 - x4, g⟫ ⟪x6 - x4, E⟫` (`E = x4 - x3`,
`g = x2 - x3`): the side of `x 0` of the plane through the edge `4 6` parallel to the view. -/
noncomputable def b2cQd (x : Fin 7 → ℝ³) : ℝ :=
  ⟪x 0 - x 4, x 4 - x 3⟫ * ⟪x 6 - x 4, x 2 - x 3⟫ - ⟪x 0 - x 4, x 2 - x 3⟫ * ⟪x 6 - x 4, x 4 - x 3⟫

/-- **The `046` identity** (no branch hypothesis): `f8(x0) ⟪N4, n⟫ ⟪x6 - x2, n⟫ X6 = -f4(x3) f8(x2) Qd X6`
(Cramer for `046` and `346` in the basis `x0 - x4, x6 - x4, E`, and `t234_prod8`). -/
theorem b2c_dn4_prod (F : S0xFac 9 s0x_S24 x) :
    F.f 8 (x 0) * (⟪F.N 4, n234 x⟫ * ⟪x 6 - x 2, n234 x⟫) * t234X6 x =
      -(F.f 4 (x 3) * F.f 8 (x 2) * b2cQd x * t234X6 x) := by
  set E := x 4 - x 3 with hE
  set g := x 2 - x 3 with hg
  set u := x 0 - x 4 with hu
  set v := x 6 - x 4 with hv
  have c4 := b2c_cramer (F.N 4) u v E (cross E g)
  have c8 := b2c_cramer (F.N 8) u v E (cross E g)
  have n4u : ⟪F.N 4, u⟫ = 0 := by rw [hu, F.inner_sub 4 0 4, F.zero 4 0 (by decide), F.zero 4 4 (by decide)]; ring
  have n4v : ⟪F.N 4, v⟫ = 0 := by rw [hv, F.inner_sub 4 6 4, F.zero 4 6 (by decide), F.zero 4 4 (by decide)]; ring
  have n4E : ⟪F.N 4, E⟫ = -F.f 4 (x 3) := by rw [hE, F.inner_sub 4 4 3, F.zero 4 4 (by decide)]; ring
  have n8u : ⟪F.N 8, u⟫ = F.f 8 (x 0) := by rw [hu, F.inner_sub 8 0 4, F.zero 8 4 (by decide)]; ring
  have n8v : ⟪F.N 8, v⟫ = 0 := by rw [hv, F.inner_sub 8 6 4, F.zero 8 6 (by decide), F.zero 8 4 (by decide)]; ring
  have n8E : ⟪F.N 8, E⟫ = 0 := by rw [hE, F.inner_sub 8 4 3, F.zero 8 4 (by decide), F.zero 8 3 (by decide)]; ring
  rw [n4u, n4v, n4E, b2c_binet] at c4
  rw [n8u, n8v, n8E, b2c_binet2] at c8
  have hX : ⟪v, E⟫ * ⟪E, g⟫ - ⟪v, g⟫ * ⟪E, E⟫ = -t234X6 x := by
    rw [t234X6, hv, hE, hg]; simp only [t234_inner3, PiLp.sub_apply]; ring
  rw [hX] at c8
  have p8 := t234_prod8 F
  rw [← t234X6] at p8
  have hn : cross E g = n234 x := by rw [hE, hg, n234_eq]
  rw [hn] at c4 c8
  have hQ : ⟪u, E⟫ * ⟪v, g⟫ - ⟪u, g⟫ * ⟪v, E⟫ = b2cQd x := rfl
  rw [hQ] at c4
  linear_combination -(⟪x 6 - x 2, n234 x⟫ * ⟪F.N 8, n234 x⟫) * c4 +
    (⟪x 6 - x 2, n234 x⟫ * ⟪F.N 4, n234 x⟫) * c8 + (F.f 4 (x 3) * b2cQd x) * p8

/-- **`046` is down at `t234b` when `X6 > 0` and `Qd > 0`** (`b2c_dn4_prod`; `z6 < z2`). -/
theorem b2c_dn4_of (F : S0xFac 9 s0x_S24 x) (hB : T234Br F) (hX : 0 < t234X6 x) (hQ : 0 < b2cQd x) :
    T234Dn F (t234b x) 4 := by
  have hp := b2c_dn4_prod F
  rw [← b2c_prod] at hp
  have hq := t234_z6 F hB
  have f80 : F.f 8 (x 0) < 0 := F.neg 8 0 (by decide)
  have f43 : F.f 4 (x 3) < 0 := F.neg 4 3 (by decide)
  have f82 : F.f 8 (x 2) < 0 := F.neg 8 2 (by decide)
  have hP : 0 < ⟪F.N 4, t234b x⟫ * ⟪x 6 - x 2, t234b x⟫ := by
    have h1 : F.f 8 (x 0) * (⟪F.N 4, t234b x⟫ * ⟪x 6 - x 2, t234b x⟫) < 0 := by
      have : F.f 8 (x 0) * (⟪F.N 4, t234b x⟫ * ⟪x 6 - x 2, t234b x⟫) * t234X6 x < 0 := by
        rw [hp]; nlinarith [mul_pos (mul_pos (mul_pos_of_neg_of_neg f43 f82) hQ) hX]
      by_contra hn; nlinarith [mul_nonneg (not_lt.mp hn) hX.le]
    by_contra hn; nlinarith [mul_nonneg_of_nonpos_of_nonpos f80.le (not_lt.mp hn)]
  left
  by_contra hn
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith [not_lt.mp hn] : 0 ≤ ⟪F.N 4, t234b x⟫) hq.le]

/-- `X5 = |E|² ⟪x5 - x3, g⟫ - ⟪E, x5 - x3⟫ ⟪E, g⟫ > 0` on the branch (`t234_up3_prod`, `t234_triple_perp`). -/
theorem b2c_X5_pos (F : S0xFac 9 s0x_S24 x) (hB : T234Br F) :
    0 < ⟪x 4 - x 3, x 4 - x 3⟫ * ⟪x 5 - x 3, x 2 - x 3⟫ - ⟪x 4 - x 3, x 5 - x 3⟫ * ⟪x 4 - x 3, x 2 - x 3⟫ := by
  obtain ⟨s, t, hs, ht, hd, -, htie, h25⟩ := hB
  have hp := t234_up3_prod F hs ht hd htie h25
  have hNe : ⟪F.N 3, x 4 - x 3⟫ = 0 := by rw [F.inner_sub 3 4 3, F.zero 3 4 (by decide), F.zero 3 3 (by decide)]; ring
  have hNa : ⟪F.N 3, x 5 - x 3⟫ = 0 := by rw [F.inner_sub 3 5 3, F.zero 3 5 (by decide), F.zero 3 3 (by decide)]; ring
  have hNc : ⟪F.N 3, x 2 - x 3⟫ = F.f 3 (x 2) := by rw [F.inner_sub 3 2 3, F.zero 3 3 (by decide)]; ring
  have hT := t234_triple_perp (F.N 3) (x 4 - x 3) (x 5 - x 3) (x 2 - x 3) hNe hNa
  have hac : x 5 - x 2 = (x 5 - x 3) - (x 2 - x 3) := by abel
  rw [n234_eq, hac, hT, hNc] at hp
  have f32 : F.f 3 (x 2) < 0 := F.neg 3 2 (by decide)
  by_contra hn
  nlinarith [mul_nonneg_of_nonpos_of_nonpos f32.le (not_lt.mp hn)]

/-- **`Qd > 0` when `t234C < 0` and the angle `0 4 3` is not acute** (`T234BrL`): `(s + t - 1) Qd = X6 + t m k` with
`m = ⟪x5 - x4, E⟫ ≤ 0`, `k = ⟪x6 - x5, g⟫ = c25 - t234C > 0`, `t m + |E|² = (s + t - 1) ⟪x0 - x4, E⟫ ≥ 0` and
`X6 - |E|² k = X5 > 0`. -/
theorem b2c_qd_pos (F : S0xFac 9 s0x_S24 x) (hB : T234BrL F) (hc : t234C x < 0)
    (h043 : ⟪x 0 - x 4, x 3 - x 4⟫ ≤ 0) : 0 < b2cQd x := by
  have hX5 := b2c_X5_pos F hB.1.1
  have hC := b2c_c25_pos F hB.1
  obtain ⟨hu5, hv6⟩ := b2c_ties F hB.1
  obtain ⟨⟨⟨s, t, hs, ht, hd, -, htie, -⟩, h56, -⟩, h45⟩ := hB
  have hw : (s + t - 1) • (x 0 - x 4) = t • (x 5 - x 4) + (x 4 - x 3) := by
    have h3 : x 3 = x 0 + (s • (x 4 - x 0) + t • (x 5 - x 0)) := by rw [← hd]; abel
    rw [h3]; module
  have hwE := congrArg (fun z => ⟪z, x 4 - x 3⟫) hw
  have hwg := congrArg (fun z => ⟪z, x 2 - x 3⟫) hw
  simp only [real_inner_smul_left, inner_add_left] at hwE hwg
  -- the scalar relations
  have e043 : ⟪x 0 - x 4, x 3 - x 4⟫ = -⟪x 0 - x 4, x 4 - x 3⟫ := by
    simp only [t234_inner3, PiLp.sub_apply]; ring
  have em : ⟪x 5 - x 4, x 4 - x 3⟫ = ⟪x 6 - x 4, x 4 - x 3⟫ := by
    simp only [t234_inner3, PiLp.sub_apply] at hu5 hv6 ⊢; linear_combination hu5 - hv6
  have hm : ⟪x 5 - x 4, x 4 - x 3⟫ ≤ 0 := by
    have : ⟪x 5 - x 4, x 4 - x 3⟫ = -(⟪x 5, x 3 - x 4⟫ - ⟪x 4, x 3 - x 4⟫) := by
      simp only [t234_inner3, PiLp.sub_apply]; ring
    rw [this]; linarith
  have ek : ⟪x 6 - x 4, x 2 - x 3⟫ - ⟪x 5 - x 4, x 2 - x 3⟫ = b2cC25 x - t234C x := by
    rw [b2cC25, t234C]; simp only [t234_inner3, PiLp.sub_apply]; ring
  have eX : t234X6 x - ⟪x 4 - x 3, x 4 - x 3⟫ * (b2cC25 x - t234C x) =
      ⟪x 4 - x 3, x 4 - x 3⟫ * ⟪x 5 - x 3, x 2 - x 3⟫ - ⟪x 4 - x 3, x 5 - x 3⟫ * ⟪x 4 - x 3, x 2 - x 3⟫ := by
    rw [t234X6, b2cC25, t234C]
    simp only [t234_inner3, PiLp.sub_apply] at hu5 hv6 ⊢; linear_combination
      (-((x 4 0 - x 3 0) * (x 2 0 - x 3 0) + (x 4 1 - x 3 1) * (x 2 1 - x 3 1) +
        (x 4 2 - x 3 2) * (x 2 2 - x 3 2))) * (hv6 - hu5)
  have eX6 : t234X6 x = ⟪x 4 - x 3, x 4 - x 3⟫ * ⟪x 6 - x 4, x 2 - x 3⟫ -
      ⟪x 6 - x 4, x 4 - x 3⟫ * ⟪x 4 - x 3, x 2 - x 3⟫ := by
    rw [t234X6]; simp only [t234_inner3, PiLp.sub_apply]; ring
  have key : (s + t - 1) * b2cQd x =
      t234X6 x + t * ⟪x 5 - x 4, x 4 - x 3⟫ * (b2cC25 x - t234C x) := by
    rw [b2cQd, ← ek, eX6]
    linear_combination ⟪x 6 - x 4, x 2 - x 3⟫ * hwE - ⟪x 6 - x 4, x 4 - x 3⟫ * hwg +
      (t * ⟪x 5 - x 4, x 2 - x 3⟫) * em
  have hk : 0 < b2cC25 x - t234C x := by linarith
  have hA : 0 ≤ t * ⟪x 5 - x 4, x 4 - x 3⟫ + ⟪x 4 - x 3, x 4 - x 3⟫ := by
    have : 0 ≤ (s + t - 1) * ⟪x 0 - x 4, x 4 - x 3⟫ := mul_nonneg (by linarith) (by linarith)
    linarith
  have hpos : 0 < (s + t - 1) * b2cQd x := by
    rw [key]; nlinarith [mul_nonneg hA hk.le]
  exact pos_of_mul_pos_right hpos (by linarith)

/-- On `T234BrJ` an acute angle `0 4 3` needs an obtuse face angle at `0`: `⟪x0 - x4, x3 - x4⟫ = -((s - 1) |e4|² +
t ⟪e4, e5⟫)`. -/
theorem b2c_e45_neg (F : S0xFac 9 s0x_S24 x) (hB : T234Br F) (h : 0 < ⟪x 0 - x 4, x 3 - x 4⟫) :
    ⟪x 4 - x 0, x 5 - x 0⟫ < 0 := by
  obtain ⟨s, t, hs, ht, hd, -⟩ := hB
  have h34 : x 3 - x 4 = (s - 1) • (x 4 - x 0) + t • (x 5 - x 0) := by
    rw [show x 3 - x 4 = (x 3 - x 0) - (x 4 - x 0) by abel, hd]; module
  have h04 : x 0 - x 4 = -(x 4 - x 0) := by abel
  rw [h34, h04, inner_neg_left, inner_add_right, real_inner_smul_right, real_inner_smul_right] at h
  have hee : 0 ≤ ⟪x 4 - x 0, x 4 - x 0⟫ := real_inner_self_nonneg
  by_contra hn
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ s - 1) hee, mul_nonneg ht.le (not_lt.mp hn)]

/-! ### The residue on the branch -/

/-- A facet with a nonzero level-3 value is up or down. -/
theorem b2c_up_or_dn (F : S0xFac 9 s0x_S24 x) (b : ℝ³) (t : Fin 9) (h : ⟪F.N t, x 5 - x 6⟫ < 0) :
    T234Up F b t ∨ T234Dn F b t := by
  unfold T234Up T234Dn LexPos3
  rcases lt_trichotomy ⟪F.N t, b⟫ 0 with h1 | h1 | h1
  · right; left; linarith
  · rcases lt_trichotomy ⟪F.N t, x 4 - x 3⟫ 0 with h2 | h2 | h2
    · right; right; exact ⟨by rw [h1, neg_zero], Or.inl (by linarith)⟩
    · right; right; exact ⟨by rw [h1, neg_zero], Or.inr ⟨by rw [h2, neg_zero], by linarith⟩⟩
    · left; right; exact ⟨h1, Or.inl h2⟩
  · left; left; exact h1

theorem b2c_n1 (F : S0xFac 9 s0x_S24 x) : ⟪F.N 1, x 5 - x 6⟫ < 0 := by
  rw [F.inner_sub 1 5 6, F.zero 1 6 (by decide)]; have := F.neg 1 5 (by decide); linarith

theorem b2c_n4 (F : S0xFac 9 s0x_S24 x) : ⟪F.N 4, x 5 - x 6⟫ < 0 := by
  rw [F.inner_sub 4 5 6, F.zero 4 6 (by decide)]; have := F.neg 4 5 (by decide); linarith

/-- What is left of the T234 letters on the B2 branch after OSPEC28: special positions of the cone (`X6 = 0 = h5 - h4`
with `046` not down, `012` edge-on at all levels, `126` not down at `t234C = 0`), `t234C < 0` with `Qd ≤ 0` (an acute
angle `0 4 3` and an obtuse face angle at `0`), and `X6 < 0` with `012` edge-on at all levels. -/
def B2CLet {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  (0 ≤ t234X6 x ∧ 0 ≤ t234C x ∧
    ((t234X6 x = 0 ∧ ⟪x 4, x 3 - x 4⟫ = ⟪x 5, x 3 - x 4⟫ ∧ ¬ T234Dn F (t234b x) 4) ∨
      (¬ T234Up F (t234b x) 0 ∧ ¬ T234Dn F (t234b x) 0) ∨
      (t234C x = 0 ∧ ¬ T234Dn F (t234b x) 5))) ∨
  (t234C x < 0 ∧ b2cQd x ≤ 0 ∧ 0 < ⟪x 0 - x 4, x 3 - x 4⟫ ∧ ⟪x 4 - x 0, x 5 - x 0⟫ < 0) ∨
  (t234X6 x < 0 ∧ ¬ T234Up F (t234b x) 0 ∧ ¬ T234Dn F (t234b x) 0)

/-- **Off the T234 cells the branch is in `B2CLet`** (`b2c_up2`, `b2c_up0_of_neg`, `b2c_dn4_of`, `b2c_qd_pos`). -/
theorem b2c_letters (F : S0xFac 9 s0x_S24 x) (hB : T234BrL F) (hn : ¬ T234RedN F) : B2CLet F := by
  have u2 : T234Up F (t234b x) 2 := Or.inl (b2c_up2 F hB.1)
  rcases lt_or_ge (t234X6 x) 0 with hX | hX
  · -- `X6 < 0`
    right; right
    refine ⟨hX, ?_⟩
    have hc := t234C_pos_of_X6 F hB.1 hX
    by_contra h0
    apply hn
    refine ⟨fun h => absurd h (not_le.mpr hX), fun h => absurd h (not_lt.mpr hc.le), fun _ => ?_⟩
    have h0' : T234Up F (t234b x) 0 ∨ T234Dn F (t234b x) 0 := by
      by_contra h'; push Not at h'; exact h0 h'
    rcases h0' with u0 | d0 <;> rcases b2c_up_or_dn F (t234b x) 1 (b2c_n1 F) with u1 | d1 <;>
      rcases b2c_up_or_dn F (t234b x) 4 (b2c_n4 F) with u4 | d4
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨u0, u1⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨u0, u1⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨u0, d1, u4⟩)))))
    · exact Or.inr (Or.inl ⟨u0, d1, d4⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨d0, u1, u2⟩))))))
    · exact Or.inr (Or.inr (Or.inl ⟨d0, u2, d4⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨d0, d1, u2, u4⟩))))))
    · exact Or.inr (Or.inr (Or.inl ⟨d0, u2, d4⟩))
  rcases lt_or_ge (t234C x) 0 with hc | hc
  · -- `t234C < 0`
    right; left
    have hX6 : 0 < t234X6 x := by
      rcases hX.lt_or_eq with h | h
      · exact h
      · exfalso
        have := t234C_pos_of_X6 F hB.1
        -- `X6 = 0` with `t234C < 0` contradicts `X2 - X6 = |E|² t234C`, `X2 ≥ 0`
        have htie26 : ⟪x 2, x 3 - x 4⟫ = ⟪x 6, x 3 - x 4⟫ := by
          obtain ⟨⟨⟨-, -, -, -, -, -, htie, -⟩, h56, -⟩, -⟩ := hB; exact htie.trans h56
        have hEd : ⟪x 4 - x 3, x 2 - x 6⟫ = 0 := by
          simp only [t234_inner3, PiLp.sub_apply] at htie26 ⊢; linear_combination -htie26
        have hw : x 6 - x 3 = (x 2 - x 3) - (x 2 - x 6) := by abel
        have hX6' : t234X6 x = (⟪x 4 - x 3, x 4 - x 3⟫ * ⟪x 2 - x 3, x 2 - x 3⟫ - ⟪x 4 - x 3, x 2 - x 3⟫ ^ 2) -
            ⟪x 4 - x 3, x 4 - x 3⟫ * t234C x := by
          have e1 : ⟪x 4 - x 3, x 6 - x 3⟫ = ⟪x 4 - x 3, x 2 - x 3⟫ - ⟪x 4 - x 3, x 2 - x 6⟫ := by
            rw [hw, inner_sub_right]
          have e2 : ⟪x 6 - x 3, x 2 - x 3⟫ = ⟪x 2 - x 3, x 2 - x 3⟫ - ⟪x 2 - x 6, x 2 - x 3⟫ := by
            rw [hw, inner_sub_left]
          rw [t234X6, t234C, e1, e2, hEd, real_inner_comm (x 2 - x 3) (x 2 - x 6)]; ring
        have hCS := real_inner_mul_inner_self_le (x 4 - x 3) (x 2 - x 3)
        have hE := b2c_ee_pos F
        nlinarith [mul_pos hE (neg_pos.mpr hc)]
    have hnd4 : ¬ T234Dn F (t234b x) 4 := by
      intro d4
      apply hn
      refine ⟨fun _ h => absurd h (not_le.mpr hc), fun _ => ⟨d4, ?_⟩,
        fun h => absurd h (not_lt.mpr hX)⟩
      rcases b2c_up_or_dn F (t234b x) 1 (b2c_n1 F) with u1 | d1
      · exact Or.inr u1
      · exact Or.inl ⟨Or.inl (b2c_up0_of_neg F hB.1 hc), d1⟩
    have hQ : b2cQd x ≤ 0 := by
      by_contra hQ; exact hnd4 (b2c_dn4_of F hB.1.1 hX6 (not_le.mp hQ))
    have h043 : 0 < ⟪x 0 - x 4, x 3 - x 4⟫ := by
      by_contra h; exact absurd (b2c_qd_pos F hB hc (not_lt.mp h)) (not_lt.mpr hQ)
    exact ⟨hc, hQ, h043, b2c_e45_neg F hB.1.1 h043⟩
  · -- the cone
    left
    refine ⟨hX, hc, ?_⟩
    by_contra hC
    push Not at hC
    obtain ⟨c1, c2, c3⟩ := hC
    apply hn
    refine ⟨fun _ _ => ⟨?_, ?_⟩, fun h => absurd h (not_lt.mpr hc), fun h => absurd h (not_lt.mpr hX)⟩
    · by_contra h
      push Not at h
      obtain ⟨h1, h2, h3⟩ := h
      exact h3 (c1 (le_antisymm h1 hX) (le_antisymm hB.2 h2))
    · by_cases d0 : T234Dn F (t234b x) 0
      · exact Or.inr (Or.inl ⟨d0, u2⟩)
      · have u0 : T234Up F (t234b x) 0 := by
          by_contra u0; exact d0 (c2 u0)
        exact Or.inl ⟨u0, c3⟩

/-- The branch letters: on `T234BrL` the point is in `B2CLet`. -/
def B2CRes {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop := T234BrL F → B2CLet F

/-- `Q45ResWN` gives `B2CRes` for `F` and its mirror. -/
theorem b2cRes_of_N {F : S0xFac 9 s0x_S24 x} (h : Q45ResWN F) : B2CRes F ∧ B2CRes (Sym.sym24 F) := by
  obtain ⟨s, t, -, -, -, -, -, hA, hB⟩ := h
  exact ⟨fun hBr => b2c_letters F hBr (fun hR => hA (Or.inr ⟨hBr, hR⟩)),
    fun hBr => b2c_letters (Sym.sym24 F) hBr (fun hR => hB (Or.inr ⟨hBr, hR⟩))⟩

/-- `Q45ResWR2U` gives `Q45ResWN`. -/
theorem q45ResWN_of_R2U {F : S0xFac 9 s0x_S24 x} (h : Q45ResWR2U F) : Q45ResWN F :=
  q45ResWN_of_O (q45ResWO_of_P h.1.1.1.1)

/-! ### The narrowed Props -/

/-- `Q45ResWR2U` with the B2 / C2 branch letters `B2CRes` (main and mirror). -/
def Q45ResWR2B (F : S0xFac 9 s0x_S24 x) : Prop :=
  Q45ResWR2U F ∧ B2CRes F ∧ B2CRes (Sym.sym24 F)

theorem q45ResWR2B_of_R2U {F : S0xFac 9 s0x_S24 x} (h : Q45ResWR2U F) : Q45ResWR2B F :=
  ⟨h, b2cRes_of_N (q45ResWN_of_R2U h)⟩

/-- [OPEN] **The special piece with the B2 valley corners narrowed, Rupert form**: `OpenSpecialR2U` with `Q45ResWR2B`
in place of `Q45ResWR2U` (equivalent: `openSpecialR2B_iff_R2U`). -/
def OpenSpecialR2B : Prop := ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), ¬ H24K.SAT.OB1 x →
  1 ≤ oblX0 x 4 → 1 ≤ oblX0 x 5 →
  oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0 →
  0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3 →
  0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4 →
  0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5 →
  Q45ResWR2B F → HoleFull x F → IsRupert (univ.image x)

/-- [PROVED] `OpenSpecialR2B ↔ OpenSpecialR2U`. -/
theorem openSpecialR2B_iff_R2U : OpenSpecialR2B ↔ OpenSpecialR2U :=
  ⟨fun h x F hO h4 h5 b1 b2 b3 b4 hr hF => h x F hO h4 h5 b1 b2 b3 b4 (q45ResWR2B_of_R2U hr) hF,
    fun h x F hO h4 h5 b1 b2 b3 b4 hr hF => h x F hO h4 h5 b1 b2 b3 b4 hr.1 hF⟩

/-- [PROVED] Generic + special (B2 corners narrowed) assemble to `Open24Rupert`. -/
theorem open24Rupert_of_split_R2B (h1 : OpenOB1) (h2 : OpenSpecialR2B) : Open24Rupert :=
  open24Rupert_of_split_QU h1 (openSpecialQU_of_R2U (openSpecialR2B_iff_R2U.1 h2))

/-- `Q45ResWR3` (OSPEC27, K0 letters) with the B2 / C2 branch letters. -/
def Q45ResWR4 (F : S0xFac 9 s0x_S24 x) : Prop :=
  Q45ResWR3 F ∧ B2CRes F ∧ B2CRes (Sym.sym24 F)

theorem q45ResWR4_of_R3 {F : S0xFac 9 s0x_S24 x} (h : Q45ResWR3 F) : Q45ResWR4 F :=
  ⟨h, b2cRes_of_N (q45ResWN_of_R2U h.1)⟩

/-- [OPEN] **The special piece with the K0 letters (OSPEC27) and the B2 corners (OSPEC28) explicit, Rupert form**:
`OpenSpecialR3` with `Q45ResWR4` in place of `Q45ResWR3` (equivalent: `openSpecialR4_iff_R3`). -/
def OpenSpecialR4 : Prop := ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), ¬ H24K.SAT.OB1 x →
  1 ≤ oblX0 x 4 → 1 ≤ oblX0 x 5 →
  oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0 →
  0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3 →
  0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4 →
  0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5 →
  Q45ResWR4 F → HoleFull x F → IsRupert (univ.image x)

/-- [PROVED] `OpenSpecialR4 ↔ OpenSpecialR3`. -/
theorem openSpecialR4_iff_R3 : OpenSpecialR4 ↔ OpenSpecialR3 :=
  ⟨fun h x F hO h4 h5 b1 b2 b3 b4 hr hF => h x F hO h4 h5 b1 b2 b3 b4 (q45ResWR4_of_R3 hr) hF,
    fun h x F hO h4 h5 b1 b2 b3 b4 hr hF => h x F hO h4 h5 b1 b2 b3 b4 hr.1 hF⟩

/-- [PROVED] Generic + special (K0 letters and B2 corners explicit) assemble to `Open24Rupert`. -/
theorem open24Rupert_of_split_R4 (h1 : OpenOB1) (h2 : OpenSpecialR4) : Open24Rupert :=
  open24Rupert_of_split_R3 h1 (openSpecialR4_iff_R3.1 h2)

end B2C

end Minimality.T24.OSpec

namespace Minimality.T24.Cell

/-- [PROVED] Headline chain with `cells28` and `OSpec.OpenSpecialR2B` (OSPEC28). -/
theorem open24Rupert_of_cellCoverEmpty28_R2B (hN : CellCoverEmpty cells28) (hS : OSpec.OpenSpecialR2B) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmpty28_R2U hN (OSpec.openSpecialR2B_iff_R2U.1 hS)

/-- [PROVED] The `E4` cell chain with `OSpec.OpenSpecialR2B`. -/
theorem open24Rupert_of_cellCoverEmptyE4_28_R2B (hN : CellCoverEmptyE4 cells28) (hS : OSpec.OpenSpecialR2B) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmptyE4_28_R2U hN (OSpec.openSpecialR2B_iff_R2U.1 hS)

/-- [PROVED] The `E10` cell chain with `OSpec.OpenSpecialR2B`. -/
theorem open24Rupert_of_cellCoverEmptyE10_28_R2B (hN : CellCoverEmptyE10 cells28) (hS : OSpec.OpenSpecialR2B) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmptyE10_28_R2U hN (OSpec.openSpecialR2B_iff_R2U.1 hS)

/-- [PROVED] Headline chain with `cells28` and `OSpec.OpenSpecialR4` (OSPEC27 + OSPEC28). -/
theorem open24Rupert_of_cellCoverEmpty28_R4 (hN : CellCoverEmpty cells28) (hS : OSpec.OpenSpecialR4) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmpty28_R3 hN (OSpec.openSpecialR4_iff_R3.1 hS)

/-- [PROVED] The `E4` cell chain with `OSpec.OpenSpecialR4`. -/
theorem open24Rupert_of_cellCoverEmptyE4_28_R4 (hN : CellCoverEmptyE4 cells28) (hS : OSpec.OpenSpecialR4) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmptyE4_28_R3 hN (OSpec.openSpecialR4_iff_R3.1 hS)

/-- [PROVED] The `E10` cell chain with `OSpec.OpenSpecialR4`. -/
theorem open24Rupert_of_cellCoverEmptyE10_28_R4 (hN : CellCoverEmptyE10 cells28) (hS : OSpec.OpenSpecialR4) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmptyE10_28_R3 hN (OSpec.openSpecialR4_iff_R3.1 hS)

end Minimality.T24.Cell
