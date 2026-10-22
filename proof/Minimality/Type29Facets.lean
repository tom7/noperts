module

public import Minimality.Type29Cover
public import Minimality.Type21Switch

@[expose] public section

/-!
# Type 29 from its facets: the normal form (`FEWER-FACES-PROOFS.md` §21.0, Lemma 21.1)

A type-29 point set (`IsCap29` over the octahedron `O = K − 6` with its facets `F`) has a normal
form (`IsCap29.toNF29`): the frame `x 1; x 4 − x 1, x 5 − x 1, x 1 − x 3` is a basis
(`IsCap29.det_ne`) and every inequality of `NF29` is the sign of a facet function at a vertex,
read off as a ratio of determinants (`facet_ratio`, `IsCap29.nf29_core`).  Hence the class
theorems from the facets: `isRupert_type29_K4`, `isRupert_type29_K3`.
-/

namespace Minimality

open scoped RealInnerProductSpace
open Finset


/-- The ratio of a facet function at two points is the ratio of the determinants with the facet. -/
theorem facet_ratio {V : Finset ℝ³} {P Q R : ℝ³} (FF : FacetFn V P Q R) (y y' : ℝ³) :
    det3 (Q - P) (y - P) (R - P) * FF.f y' = det3 (Q - P) (y' - P) (R - P) * FF.f y :=
  det3_facet_prop FF.hN FF.hP FF.hQ (by rw [← FF.hN, FF.hR, FF.hP, sub_self]) y y'

theorem same_sign_pos {P Q f g : ℝ} (r : P * g = Q * f) (hf : f < 0) (hg : g < 0) (hQ : 0 < Q) :
    0 < P := by
  by_contra h; push Not at h
  nlinarith [mul_nonneg_of_nonpos_of_nonpos h hg.le, mul_neg_of_pos_of_neg hQ hf]

theorem same_sign_neg {P Q f g : ℝ} (r : P * g = Q * f) (hf : f < 0) (hg : g < 0) (hQ : Q < 0) :
    P < 0 := by
  by_contra h; push Not at h
  nlinarith [mul_nonpos_of_nonneg_of_nonpos h hg.le, mul_pos_of_neg_of_neg hQ hf]

theorem opp_sign {P Q f g : ℝ} (r : P * g = Q * f) (hf : 0 < f) (hg : g < 0) (hQ : 0 < Q) :
    P < 0 := by
  by_contra h; push Not at h
  nlinarith [mul_nonpos_of_nonneg_of_nonpos h hg.le, mul_pos hQ hf]

theorem ratio_sign {P Q D f g : ℝ} (hD : D ≠ 0) (e : P * D * g = Q * D * f) : P * g = Q * f := by
  have h : (P * g - Q * f) * D = 0 := by linear_combination e
  rcases mul_eq_zero.mp h with h | h
  · linarith
  · exact absurd h hD

set_option maxHeartbeats 1000000 in
/-- **Lemma 21.1 from the facets**: in the frame `o; E₁, E₂, E₃` with `x 1 = o`, `x 4 = o + E₁`,
`x 5 = o + E₂`, `x 3 = o − E₃`, the cap lies on `145` (`c6 = 0`) and every inequality of `NF29`
is the sign of a facet function at a vertex (`facet_ratio`: a vertex beneath a face has the
determinant sign of a reference vertex beneath it). -/
theorem IsCap29.nf29_core {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    {F : OctFacets (x 0) (x 4) (x 1) (x 3) (x 2) (x 5)} (hd : IsCap29 F (x 6))
    {o E₁ E₂ E₃ : ℝ³} (hD : det3 E₁ E₂ E₃ ≠ 0) {a0 b0 h0 a2 b2 h2 s t c6 : ℝ}
    (e0 : x 0 = nfP o E₁ E₂ E₃ a0 b0 (-h0)) (e1 : x 1 = nfP o E₁ E₂ E₃ 0 0 0)
    (e2 : x 2 = nfP o E₁ E₂ E₃ a2 b2 (-h2)) (e3 : x 3 = nfP o E₁ E₂ E₃ 0 0 (-1))
    (e4 : x 4 = nfP o E₁ E₂ E₃ 1 0 0) (e5 : x 5 = nfP o E₁ E₂ E₃ 0 1 0)
    (e6 : x 6 = nfP o E₁ E₂ E₃ s t c6) :
    c6 = 0 ∧ 0 < h0 ∧
      0 < h2 ∧
      a0 < 0 ∧
      b2 < 0 ∧
      a0 + b0 + h0 < 1 ∧
      a2 + b2 + h2 < 1 ∧
      0 < h2 * b0 - h0 * b2 ∧
      0 < h0 * a2 - h2 * a0 ∧
      0 < a0 * b2 - a2 * b0 ∧
      0 < a0 * b2 - a2 * b0 + (b0 * (1 - h2) - b2 * (1 - h0)) ∧
      0 < a0 * b2 - a2 * b0 + (a2 * (1 - h0) - a0 * (1 - h2)) ∧
      (b0 - 1 + h0) * a2 - a0 * b2 + a0 * (1 - h2) < 0 ∧
      0 < a0 * b2 + (1 - h2 - a2) * b0 - b2 * (1 - h0) ∧
      0 < s ∧
      0 < t ∧
      1 < s + t ∧
      0 < a0 * b2 - a2 * b0 + s * (b0 * (1 - h2) - b2 * (1 - h0)) + t *
          (a2 * (1 - h0) - a0 * (1 - h2)) ∧
      0 < -((b0 - 1 + h0) * s - a0 * t + a0) ∧
      0 < b2 * s + (1 - h2 - a2) * t - b2 := by
  have khh0 := facet_ratio F.a'bc' (x 0) (x 3)
  have dhh0y : det3 (x 1 - x 4) (x 0 - x 4) (x 5 - x 4) =
      (-h0) * det3 E₁ E₂ E₃ := by
    rw [e0, e1, e4, e5]; simp only [nfP_sub, det3_nfV, det3c]; ring
  have dhh0w : det3 (x 1 - x 4) (x 3 - x 4) (x 5 - x 4) =
      (-1) * det3 E₁ E₂ E₃ := by
    rw [e1, e3, e4, e5]; simp only [nfP_sub, det3_nfV, det3c]; ring
  rw [dhh0y, dhh0w] at khh0
  have rhh0 := ratio_sign hD khh0
  have fhh0y := F.a'bc'.neg (x 0) (by simp) (hx.ne (by decide)) (hx.ne (by decide))
    (hx.ne (by decide))
  have fhh0w := F.a'bc'.neg (x 3) (by simp) (hx.ne (by decide)) (hx.ne (by decide))
    (hx.ne (by decide))
  have ghh0 : 0 < h0 := by linarith [same_sign_neg rhh0 fhh0y fhh0w (by norm_num)]
  have khh2 := facet_ratio F.a'bc' (x 2) (x 3)
  have dhh2y : det3 (x 1 - x 4) (x 2 - x 4) (x 5 - x 4) =
      (-h2) * det3 E₁ E₂ E₃ := by
    rw [e1, e2, e4, e5]; simp only [nfP_sub, det3_nfV, det3c]; ring
  have dhh2w : det3 (x 1 - x 4) (x 3 - x 4) (x 5 - x 4) =
      (-1) * det3 E₁ E₂ E₃ := by
    rw [e1, e3, e4, e5]; simp only [nfP_sub, det3_nfV, det3c]; ring
  rw [dhh2y, dhh2w] at khh2
  have rhh2 := ratio_sign hD khh2
  have fhh2y := F.a'bc'.neg (x 2) (by simp) (hx.ne (by decide)) (hx.ne (by decide))
    (hx.ne (by decide))
  have fhh2w := F.a'bc'.neg (x 3) (by simp) (hx.ne (by decide)) (hx.ne (by decide))
    (hx.ne (by decide))
  have ghh2 : 0 < h2 := by linarith [same_sign_neg rhh2 fhh2y fhh2w (by norm_num)]
  have khc6 := facet_ratio F.a'bc' (x 6) (x 3)
  have dhc6y : det3 (x 1 - x 4) (x 6 - x 4) (x 5 - x 4) =
      (c6) * det3 E₁ E₂ E₃ := by
    rw [e1, e4, e5, e6]; simp only [nfP_sub, det3_nfV, det3c]; ring
  have dhc6w : det3 (x 1 - x 4) (x 3 - x 4) (x 5 - x 4) =
      (-1) * det3 E₁ E₂ E₃ := by
    rw [e1, e3, e4, e5]; simp only [nfP_sub, det3_nfV, det3c]; ring
  rw [dhc6y, dhc6w] at khc6
  have rhc6 := ratio_sign hD khc6
  have fhc6y := hd.a'bc'
  have fhc6w := F.a'bc'.neg (x 3) (by simp) (hx.ne (by decide)) (hx.ne (by decide))
    (hx.ne (by decide))
  have hc6 : c6 = 0 := by
    rw [fhc6y, mul_zero] at rhc6
    rcases mul_eq_zero.mp rhc6 with h | h
    · linarith
    · exact absurd h fhc6w.ne
  subst hc6
  have kt0 := facet_ratio F.a'b'c' (x 0) (x 1)
  have dt0y : det3 (x 3 - x 4) (x 0 - x 4) (x 5 - x 4) =
      (-a0 - b0 - h0 + 1) * det3 E₁ E₂ E₃ := by
    rw [e0, e3, e4, e5]; simp only [nfP_sub, det3_nfV, det3c]; ring
  have dt0w : det3 (x 3 - x 4) (x 1 - x 4) (x 5 - x 4) =
      (1) * det3 E₁ E₂ E₃ := by
    rw [e1, e3, e4, e5]; simp only [nfP_sub, det3_nfV, det3c]; ring
  rw [dt0y, dt0w] at kt0
  have rt0 := ratio_sign hD kt0
  have ft0y := F.a'b'c'.neg (x 0) (by simp) (hx.ne (by decide)) (hx.ne (by decide))
    (hx.ne (by decide))
  have ft0w := F.a'b'c'.neg (x 1) (by simp) (hx.ne (by decide)) (hx.ne (by decide))
    (hx.ne (by decide))
  have gt0 : a0 + b0 + h0 < 1 := by linarith [same_sign_pos rt0 ft0y ft0w (by norm_num)]
  have kt2 := facet_ratio F.a'b'c' (x 2) (x 1)
  have dt2y : det3 (x 3 - x 4) (x 2 - x 4) (x 5 - x 4) =
      (-a2 - b2 - h2 + 1) * det3 E₁ E₂ E₃ := by
    rw [e2, e3, e4, e5]; simp only [nfP_sub, det3_nfV, det3c]; ring
  have dt2w : det3 (x 3 - x 4) (x 1 - x 4) (x 5 - x 4) =
      (1) * det3 E₁ E₂ E₃ := by
    rw [e1, e3, e4, e5]; simp only [nfP_sub, det3_nfV, det3c]; ring
  rw [dt2y, dt2w] at kt2
  have rt2 := ratio_sign hD kt2
  have ft2y := F.a'b'c'.neg (x 2) (by simp) (hx.ne (by decide)) (hx.ne (by decide))
    (hx.ne (by decide))
  have ft2w := F.a'b'c'.neg (x 1) (by simp) (hx.ne (by decide)) (hx.ne (by decide))
    (hx.ne (by decide))
  have gt2 : a2 + b2 + h2 < 1 := by linarith [same_sign_pos rt2 ft2y ft2w (by norm_num)]
  have ktst := facet_ratio F.a'b'c' (x 6) (x 1)
  have dtsty : det3 (x 3 - x 4) (x 6 - x 4) (x 5 - x 4) =
      (-s - t + 1) * det3 E₁ E₂ E₃ := by
    rw [e3, e4, e5, e6]; simp only [nfP_sub, det3_nfV, det3c]; ring
  have dtstw : det3 (x 3 - x 4) (x 1 - x 4) (x 5 - x 4) =
      (1) * det3 E₁ E₂ E₃ := by
    rw [e1, e3, e4, e5]; simp only [nfP_sub, det3_nfV, det3c]; ring
  rw [dtsty, dtstw] at ktst
  have rtst := ratio_sign hD ktst
  have ftsty := hd.a'b'c'
  have ftstw := F.a'b'c'.neg (x 1) (by simp) (hx.ne (by decide)) (hx.ne (by decide))
    (hx.ne (by decide))
  have gtst : 1 < s + t := by linarith [opp_sign rtst ftsty ftstw (by norm_num)]
  have kta0 := facet_ratio F.abc' (x 3) (x 4)
  have dta0y : det3 (x 1 - x 0) (x 3 - x 0) (x 5 - x 0) =
      (-a0) * det3 E₁ E₂ E₃ := by
    rw [e0, e1, e3, e5]; simp only [nfP_sub, det3_nfV, det3c]; ring
  have dta0w : det3 (x 1 - x 0) (x 4 - x 0) (x 5 - x 0) =
      (h0) * det3 E₁ E₂ E₃ := by
    rw [e0, e1, e4, e5]; simp only [nfP_sub, det3_nfV, det3c]; ring
  rw [dta0y, dta0w] at kta0
  have rta0 := ratio_sign hD kta0
  have fta0y := F.abc'.neg (x 3) (by simp) (hx.ne (by decide)) (hx.ne (by decide))
    (hx.ne (by decide))
  have fta0w := F.abc'.neg (x 4) (by simp) (hx.ne (by decide)) (hx.ne (by decide))
    (hx.ne (by decide))
  have gta0 : a0 < 0 := by linarith [same_sign_pos rta0 fta0y fta0w ghh0]
  have ktF5 := facet_ratio F.abc' (x 2) (x 4)
  have dtF5y : det3 (x 1 - x 0) (x 2 - x 0) (x 5 - x 0) =
      (-a0 * h2 + a2 * h0) * det3 E₁ E₂ E₃ := by
    rw [e0, e1, e2, e5]; simp only [nfP_sub, det3_nfV, det3c]; ring
  have dtF5w : det3 (x 1 - x 0) (x 4 - x 0) (x 5 - x 0) =
      (h0) * det3 E₁ E₂ E₃ := by
    rw [e0, e1, e4, e5]; simp only [nfP_sub, det3_nfV, det3c]; ring
  rw [dtF5y, dtF5w] at ktF5
  have rtF5 := ratio_sign hD ktF5
  have ftF5y := F.abc'.neg (x 2) (by simp) (hx.ne (by decide)) (hx.ne (by decide))
    (hx.ne (by decide))
  have ftF5w := F.abc'.neg (x 4) (by simp) (hx.ne (by decide)) (hx.ne (by decide))
    (hx.ne (by decide))
  have gtF5 : 0 < h0 * a2 - h2 * a0 := by linarith [same_sign_pos rtF5 ftF5y ftF5w ghh0]
  have kts := facet_ratio F.abc' (x 6) (x 4)
  have dtsy : det3 (x 1 - x 0) (x 6 - x 0) (x 5 - x 0) =
      (h0 * s) * det3 E₁ E₂ E₃ := by
    rw [e0, e1, e5, e6]; simp only [nfP_sub, det3_nfV, det3c]; ring
  have dtsw : det3 (x 1 - x 0) (x 4 - x 0) (x 5 - x 0) =
      (h0) * det3 E₁ E₂ E₃ := by
    rw [e0, e1, e4, e5]; simp only [nfP_sub, det3_nfV, det3c]; ring
  rw [dtsy, dtsw] at kts
  have rts := ratio_sign hD kts
  have ftsy := hd.abc'
  have ftsw := F.abc'.neg (x 4) (by simp) (hx.ne (by decide)) (hx.ne (by decide))
    (hx.ne (by decide))
  have gts : 0 < s := (mul_pos_iff_of_pos_left ghh0).mp (same_sign_pos rts ftsy ftsw ghh0)
  have ktb2 := facet_ratio F.a'bc (x 3) (x 5)
  have dtb2y : det3 (x 1 - x 4) (x 3 - x 4) (x 2 - x 4) =
      (-b2) * det3 E₁ E₂ E₃ := by
    rw [e1, e2, e3, e4]; simp only [nfP_sub, det3_nfV, det3c]; ring
  have dtb2w : det3 (x 1 - x 4) (x 5 - x 4) (x 2 - x 4) =
      (h2) * det3 E₁ E₂ E₃ := by
    rw [e1, e2, e4, e5]; simp only [nfP_sub, det3_nfV, det3c]; ring
  rw [dtb2y, dtb2w] at ktb2
  have rtb2 := ratio_sign hD ktb2
  have ftb2y := F.a'bc.neg (x 3) (by simp) (hx.ne (by decide)) (hx.ne (by decide))
    (hx.ne (by decide))
  have ftb2w := F.a'bc.neg (x 5) (by simp) (hx.ne (by decide)) (hx.ne (by decide))
    (hx.ne (by decide))
  have gtb2 : b2 < 0 := by linarith [same_sign_pos rtb2 ftb2y ftb2w ghh2]
  have ktF4 := facet_ratio F.a'bc (x 0) (x 5)
  have dtF4y : det3 (x 1 - x 4) (x 0 - x 4) (x 2 - x 4) =
      (b0 * h2 - b2 * h0) * det3 E₁ E₂ E₃ := by
    rw [e0, e1, e2, e4]; simp only [nfP_sub, det3_nfV, det3c]; ring
  have dtF4w : det3 (x 1 - x 4) (x 5 - x 4) (x 2 - x 4) =
      (h2) * det3 E₁ E₂ E₃ := by
    rw [e1, e2, e4, e5]; simp only [nfP_sub, det3_nfV, det3c]; ring
  rw [dtF4y, dtF4w] at ktF4
  have rtF4 := ratio_sign hD ktF4
  have ftF4y := F.a'bc.neg (x 0) (by simp) (hx.ne (by decide)) (hx.ne (by decide))
    (hx.ne (by decide))
  have ftF4w := F.a'bc.neg (x 5) (by simp) (hx.ne (by decide)) (hx.ne (by decide))
    (hx.ne (by decide))
  have gtF4 : 0 < h2 * b0 - h0 * b2 := by linarith [same_sign_pos rtF4 ftF4y ftF4w ghh2]
  have ktt := facet_ratio F.a'bc (x 6) (x 5)
  have dtty : det3 (x 1 - x 4) (x 6 - x 4) (x 2 - x 4) =
      (h2 * t) * det3 E₁ E₂ E₃ := by
    rw [e1, e2, e4, e6]; simp only [nfP_sub, det3_nfV, det3c]; ring
  have dttw : det3 (x 1 - x 4) (x 5 - x 4) (x 2 - x 4) =
      (h2) * det3 E₁ E₂ E₃ := by
    rw [e1, e2, e4, e5]; simp only [nfP_sub, det3_nfV, det3c]; ring
  rw [dtty, dttw] at ktt
  have rtt := ratio_sign hD ktt
  have ftty := hd.a'bc
  have fttw := F.a'bc.neg (x 5) (by simp) (hx.ne (by decide)) (hx.ne (by decide))
    (hx.ne (by decide))
  have gtt : 0 < t := (mul_pos_iff_of_pos_left ghh2).mp (same_sign_pos rtt ftty fttw ghh2)
  have ktD := facet_ratio F.abc (x 3) (x 5)
  have dtDy : det3 (x 1 - x 0) (x 3 - x 0) (x 2 - x 0) =
      (-a0 * b2 + a2 * b0) * det3 E₁ E₂ E₃ := by
    rw [e0, e1, e2, e3]; simp only [nfP_sub, det3_nfV, det3c]; ring
  have dtDw : det3 (x 1 - x 0) (x 5 - x 0) (x 2 - x 0) =
      (a0 * h2 - a2 * h0) * det3 E₁ E₂ E₃ := by
    rw [e0, e1, e2, e5]; simp only [nfP_sub, det3_nfV, det3c]; ring
  rw [dtDy, dtDw] at ktD
  have rtD := ratio_sign hD ktD
  have ftDy := F.abc.neg (x 3) (by simp) (hx.ne (by decide)) (hx.ne (by decide))
    (hx.ne (by decide))
  have ftDw := F.abc.neg (x 5) (by simp) (hx.ne (by decide)) (hx.ne (by decide))
    (hx.ne (by decide))
  have gtD : 0 < a0 * b2 - a2 * b0 := by linarith [same_sign_neg rtD ftDy ftDw (by linarith [gtF5])]
  have ktDG4 := facet_ratio F.ab'c (x 4) (x 1)
  have dtDG4y : det3 (x 3 - x 0) (x 4 - x 0) (x 2 - x 0) =
      (a0 * b2 - a2 * b0 - b0 * h2 + b2 * h0 + b0 - b2) * det3 E₁ E₂ E₃ := by
    rw [e0, e2, e3, e4]; simp only [nfP_sub, det3_nfV, det3c]; ring
  have dtDG4w : det3 (x 3 - x 0) (x 1 - x 0) (x 2 - x 0) =
      (a0 * b2 - a2 * b0) * det3 E₁ E₂ E₃ := by
    rw [e0, e1, e2, e3]; simp only [nfP_sub, det3_nfV, det3c]; ring
  rw [dtDG4y, dtDG4w] at ktDG4
  have rtDG4 := ratio_sign hD ktDG4
  have ftDG4y := F.ab'c.neg (x 4) (by simp) (hx.ne (by decide)) (hx.ne (by decide))
    (hx.ne (by decide))
  have ftDG4w := F.ab'c.neg (x 1) (by simp) (hx.ne (by decide)) (hx.ne (by decide))
    (hx.ne (by decide))
  have gtDG4 : 0 < a0 * b2 - a2 * b0 + (b0 * (1 - h2) - b2 * (1 - h0)) :=
      by linarith [same_sign_pos rtDG4 ftDG4y ftDG4w gtD]
  have ktDG5 := facet_ratio F.ab'c (x 5) (x 1)
  have dtDG5y : det3 (x 3 - x 0) (x 5 - x 0) (x 2 - x 0) =
      (a0 * b2 + a0 * h2 - a2 * b0 - a2 * h0 - a0 + a2) * det3 E₁ E₂ E₃ := by
    rw [e0, e2, e3, e5]; simp only [nfP_sub, det3_nfV, det3c]; ring
  have dtDG5w : det3 (x 3 - x 0) (x 1 - x 0) (x 2 - x 0) =
      (a0 * b2 - a2 * b0) * det3 E₁ E₂ E₃ := by
    rw [e0, e1, e2, e3]; simp only [nfP_sub, det3_nfV, det3c]; ring
  rw [dtDG5y, dtDG5w] at ktDG5
  have rtDG5 := ratio_sign hD ktDG5
  have ftDG5y := F.ab'c.neg (x 5) (by simp) (hx.ne (by decide)) (hx.ne (by decide))
    (hx.ne (by decide))
  have ftDG5w := F.ab'c.neg (x 1) (by simp) (hx.ne (by decide)) (hx.ne (by decide))
    (hx.ne (by decide))
  have gtDG5 : 0 < a0 * b2 - a2 * b0 + (a2 * (1 - h0) - a0 * (1 - h2)) :=
      by linarith [same_sign_pos rtDG5 ftDG5y ftDG5w gtD]
  have kt023 := facet_ratio F.ab'c (x 6) (x 1)
  have dt023y : det3 (x 3 - x 0) (x 6 - x 0) (x 2 - x 0) =
      (a0 * h2 * t - a2 * h0 * t - b0 * h2 * s + b2 * h0 * s + a0 * b2
       - a0 * t - a2 * b0 + a2 * t + b0 * s - b2 * s) * det3 E₁ E₂ E₃ := by
    rw [e0, e2, e3, e6]; simp only [nfP_sub, det3_nfV, det3c]; ring
  have dt023w : det3 (x 3 - x 0) (x 1 - x 0) (x 2 - x 0) =
      (a0 * b2 - a2 * b0) * det3 E₁ E₂ E₃ := by
    rw [e0, e1, e2, e3]; simp only [nfP_sub, det3_nfV, det3c]; ring
  rw [dt023y, dt023w] at kt023
  have rt023 := ratio_sign hD kt023
  have ft023y := hd.ab'c
  have ft023w := F.ab'c.neg (x 1) (by simp) (hx.ne (by decide)) (hx.ne (by decide))
    (hx.ne (by decide))
  have gt023 : 0 < a0 * b2 - a2 * b0 + s * (b0 * (1 - h2) - b2 * (1 - h0)) + t *
      (a2 * (1 - h0) - a0 * (1 - h2)) := by linarith [same_sign_pos rt023 ft023y ft023w gtD]
  have ktE35 := facet_ratio F.ab'c' (x 2) (x 1)
  have dtE35y : det3 (x 3 - x 0) (x 2 - x 0) (x 5 - x 0) =
      (-a0 * b2 - a0 * h2 + a2 * b0 + a2 * h0 + a0 - a2) * det3 E₁ E₂ E₃ := by
    rw [e0, e2, e3, e5]; simp only [nfP_sub, det3_nfV, det3c]; ring
  have dtE35w : det3 (x 3 - x 0) (x 1 - x 0) (x 5 - x 0) =
      (a0) * det3 E₁ E₂ E₃ := by
    rw [e0, e1, e3, e5]; simp only [nfP_sub, det3_nfV, det3c]; ring
  rw [dtE35y, dtE35w] at ktE35
  have rtE35 := ratio_sign hD ktE35
  have ftE35y := F.ab'c'.neg (x 2) (by simp) (hx.ne (by decide)) (hx.ne (by decide))
    (hx.ne (by decide))
  have ftE35w := F.ab'c'.neg (x 1) (by simp) (hx.ne (by decide)) (hx.ne (by decide))
    (hx.ne (by decide))
  have gtE35 : (b0 - 1 + h0) * a2 - a0 * b2 + a0 * (1 - h2) < 0 :=
      by linarith [same_sign_neg rtE35 ftE35y ftE35w gta0]
  have kt035 := facet_ratio F.ab'c' (x 6) (x 1)
  have dt035y : det3 (x 3 - x 0) (x 6 - x 0) (x 5 - x 0) =
      (-a0 * t + b0 * s + h0 * s + a0 - s) * det3 E₁ E₂ E₃ := by
    rw [e0, e3, e5, e6]; simp only [nfP_sub, det3_nfV, det3c]; ring
  have dt035w : det3 (x 3 - x 0) (x 1 - x 0) (x 5 - x 0) =
      (a0) * det3 E₁ E₂ E₃ := by
    rw [e0, e1, e3, e5]; simp only [nfP_sub, det3_nfV, det3c]; ring
  rw [dt035y, dt035w] at kt035
  have rt035 := ratio_sign hD kt035
  have ft035y := hd.ab'c'
  have ft035w := F.ab'c'.neg (x 1) (by simp) (hx.ne (by decide)) (hx.ne (by decide))
    (hx.ne (by decide))
  have gt035 : 0 < -((b0 - 1 + h0) * s - a0 * t + a0) :=
      by linarith [same_sign_neg rt035 ft035y ft035w gta0]
  have ktE24 := facet_ratio F.a'b'c (x 0) (x 1)
  have dtE24y : det3 (x 3 - x 4) (x 0 - x 4) (x 2 - x 4) =
      (-a0 * b2 + a2 * b0 + b0 * h2 - b2 * h0 - b0 + b2) * det3 E₁ E₂ E₃ := by
    rw [e0, e2, e3, e4]; simp only [nfP_sub, det3_nfV, det3c]; ring
  have dtE24w : det3 (x 3 - x 4) (x 1 - x 4) (x 2 - x 4) =
      (b2) * det3 E₁ E₂ E₃ := by
    rw [e1, e2, e3, e4]; simp only [nfP_sub, det3_nfV, det3c]; ring
  rw [dtE24y, dtE24w] at ktE24
  have rtE24 := ratio_sign hD ktE24
  have ftE24y := F.a'b'c.neg (x 0) (by simp) (hx.ne (by decide)) (hx.ne (by decide))
    (hx.ne (by decide))
  have ftE24w := F.a'b'c.neg (x 1) (by simp) (hx.ne (by decide)) (hx.ne (by decide))
    (hx.ne (by decide))
  have gtE24 : 0 < a0 * b2 + (1 - h2 - a2) * b0 - b2 * (1 - h0) :=
      by linarith [same_sign_neg rtE24 ftE24y ftE24w gtb2]
  have kt234 := facet_ratio F.a'b'c (x 6) (x 1)
  have dt234y : det3 (x 3 - x 4) (x 6 - x 4) (x 2 - x 4) =
      (a2 * t - b2 * s + h2 * t + b2 - t) * det3 E₁ E₂ E₃ := by
    rw [e2, e3, e4, e6]; simp only [nfP_sub, det3_nfV, det3c]; ring
  have dt234w : det3 (x 3 - x 4) (x 1 - x 4) (x 2 - x 4) =
      (b2) * det3 E₁ E₂ E₃ := by
    rw [e1, e2, e3, e4]; simp only [nfP_sub, det3_nfV, det3c]; ring
  rw [dt234y, dt234w] at kt234
  have rt234 := ratio_sign hD kt234
  have ft234y := hd.a'b'c
  have ft234w := F.a'b'c.neg (x 1) (by simp) (hx.ne (by decide)) (hx.ne (by decide))
    (hx.ne (by decide))
  have gt234 : 0 < b2 * s + (1 - h2 - a2) * t - b2 :=
      by linarith [same_sign_neg rt234 ft234y ft234w gtb2]
  exact ⟨rfl, ghh0, ghh2, gta0, gtb2, gt0, gt2, gtF4, gtF5, gtD, gtDG4, gtDG5, gtE35, gtE24, gts,
        gtt, gtst, gt023, gt035, gt234⟩

/-- The frame determinant of type 29 is nonzero: the facets `015`, `124`, `145` vanish on three of
the four points `1, 4, 5, 3` each. -/
theorem IsCap29.det_ne {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (F : OctFacets (x 0) (x 4) (x 1) (x 3) (x 2) (x 5)) :
    det3 (x 4 - x 1) (x 5 - x 1) (x 1 - x 3) ≠ 0 := by
  have n1 := F.abc'.neg (x 4) (by simp) (hx.ne (by decide)) (hx.ne (by decide)) (hx.ne (by decide))
  have n2 := F.a'bc.neg (x 5) (by simp) (hx.ne (by decide)) (hx.ne (by decide)) (hx.ne (by decide))
  have n3 := F.a'bc'.neg (x 3) (by simp) (hx.ne (by decide)) (hx.ne (by decide))
    (hx.ne (by decide))
  have h := det3_ne_zero_of_affine3 F.abc'.hN F.a'bc.hN F.a'bc'.hN (x 1) (x 4) (x 5) (x 3) (by
    rw [F.abc'.hQ, F.abc'.hR, F.a'bc.hP, F.a'bc.hQ, F.a'bc'.hP, F.a'bc'.hQ, F.a'bc'.hR]
    exact fun h => mul_ne_zero n1.ne (mul_ne_zero n2.ne n3.ne) (by linear_combination h))
  have e : det3 (x 4 - x 1) (x 5 - x 1) (x 1 - x 3) = -det3 (x 4 - x 1) (x 5 - x 1) (x 3 - x 1) :=
      by
    simp only [det3_expand, PiLp.sub_apply]; ring
  rw [e]; exact neg_ne_zero.mpr h

/-- **Every type-29 point set has a normal form** (Lemma 21.1): for seven points with the
octahedron `O = K − 6` (`F`, opposite pairs `(0, 4)`, `(1, 3)`, `(2, 5)`) and the cap `6`
(`IsCap29`), the frame `x 1; x 4 − x 1, x 5 − x 1, x 1 − x 3` is a basis (`IsCap29.det_ne`), the
coordinates are Cramer ratios, and the inequalities of `NF29` are facet signs
(`IsCap29.nf29_core`). -/
noncomputable def IsCap29.toNF29 {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (F : OctFacets (x 0) (x 4) (x 1) (x 3) (x 2) (x 5)) (hd : IsCap29 F (x 6)) : NF29 x :=
  have hD := IsCap29.det_ne hx F
  have c0 := eq_nfP_cramer (o := x 1) hD (x 0)
  have c2 := eq_nfP_cramer (o := x 1) hD (x 2)
  have c6 := eq_nfP_cramer (o := x 1) hD (x 6)
  have e1 : x 1 = nfP (x 1) (x 4 - x 1) (x 5 - x 1) (x 1 - x 3) 0 0 0 := by
    simp only [nfP]; module
  have e3 : x 3 = nfP (x 1) (x 4 - x 1) (x 5 - x 1) (x 1 - x 3) 0 0 (-1) := by
    simp only [nfP]; module
  have e4 : x 4 = nfP (x 1) (x 4 - x 1) (x 5 - x 1) (x 1 - x 3) 1 0 0 := by
    simp only [nfP]; module
  have e5 : x 5 = nfP (x 1) (x 4 - x 1) (x 5 - x 1) (x 1 - x 3) 0 1 0 := by
    simp only [nfP]; module
  have H := hd.nf29_core hx hD (h0 := -(det3 (x 4 - x 1) (x 5 - x 1) (x 0 - x 1) /
      det3 (x 4 - x 1) (x 5 - x 1) (x 1 - x 3)))
    (h2 := -(det3 (x 4 - x 1) (x 5 - x 1) (x 2 - x 1) / det3 (x 4 - x 1) (x 5 - x 1) (x 1 - x 3)))
    (by rw [neg_neg]; exact c0) e1 (by rw [neg_neg]; exact c2) e3 e4 e5 c6
  { o := x 1, E₁ := x 4 - x 1, E₂ := x 5 - x 1, E₃ := x 1 - x 3, inj := hx,
    a0 := det3 (x 0 - x 1) (x 5 - x 1) (x 1 - x 3) / det3 (x 4 - x 1) (x 5 - x 1) (x 1 - x 3),
    b0 := det3 (x 4 - x 1) (x 0 - x 1) (x 1 - x 3) / det3 (x 4 - x 1) (x 5 - x 1) (x 1 - x 3),
    h0 := -(det3 (x 4 - x 1) (x 5 - x 1) (x 0 - x 1) / det3 (x 4 - x 1) (x 5 - x 1) (x 1 - x 3)),
    a2 := det3 (x 2 - x 1) (x 5 - x 1) (x 1 - x 3) / det3 (x 4 - x 1) (x 5 - x 1) (x 1 - x 3),
    b2 := det3 (x 4 - x 1) (x 2 - x 1) (x 1 - x 3) / det3 (x 4 - x 1) (x 5 - x 1) (x 1 - x 3),
    h2 := -(det3 (x 4 - x 1) (x 5 - x 1) (x 2 - x 1) / det3 (x 4 - x 1) (x 5 - x 1) (x 1 - x 3)),
    s := det3 (x 6 - x 1) (x 5 - x 1) (x 1 - x 3) / det3 (x 4 - x 1) (x 5 - x 1) (x 1 - x 3),
    t := det3 (x 4 - x 1) (x 6 - x 1) (x 1 - x 3) / det3 (x 4 - x 1) (x 5 - x 1) (x 1 - x 3),
    x0 := by rw [neg_neg]; exact c0
    x1 := e1
    x2 := by rw [neg_neg]; exact c2
    x3 := e3
    x4 := e4
    x5 := e5
    x6 := by rw [← H.1]; exact c6
    hD := hD
    hh0 := H.2.1, hh2 := H.2.2.1, ha0 := H.2.2.2.1, hb2 := H.2.2.2.2.1,
    t345_0 := H.2.2.2.2.2.1, t345_2 := H.2.2.2.2.2.2.1, hF4 := H.2.2.2.2.2.2.2.1,
    hF5 := H.2.2.2.2.2.2.2.2.1, hDD := H.2.2.2.2.2.2.2.2.2.1,
    hDG4 := H.2.2.2.2.2.2.2.2.2.2.1, hDG5 := H.2.2.2.2.2.2.2.2.2.2.2.1,
    hE35 := H.2.2.2.2.2.2.2.2.2.2.2.2.1, hE24 := H.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hs := H.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, ht := H.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hst := H.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, d023 := H.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    d035 := H.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    d234 := H.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 }

/-- **Type 29, class K4 (§21.1 with Theorem P), from the facets.**  Let `x 0, …, x 6` be a type-29
point set: `O = K − 6` an octahedron (`F`, opposite pairs `(0, 4)`, `(1, 3)`, `(2, 5)`) with the
cap `6` (`IsCap29`).  If its normal form (Lemma 21.1; all normal forms of `x` agree) is of class
K4 (`a2, b0 > 0`, `V ≠ 0`), off the special positions and with the genericity of the named tests
(`K4Gen`, `K4C1Gen` for K4a, their `σ`-images for K4b), then `K` is Rupert. -/
theorem isRupert_type29_K4 {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (F : OctFacets (x 0) (x 4) (x 1) (x 3) (x 2) (x 5)) (hd : IsCap29 F (x 6))
    (h : ∀ N : NF29 x, 0 < N.a2 ∧ 0 < N.b0 ∧
      ((N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0) < 0 ∧ K4Gen N ∧ K4C1Gen N) ∨
       (0 < N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0) ∧ K4Gen N.sigma ∧
        K4C1Gen N.sigma))) : IsRupert (univ.image x) := by
  obtain ⟨ha2, hb0, ⟨hV, G, G1⟩ | ⟨hV, G, G1⟩⟩ := h (IsCap29.toNF29 hx F hd)
  · exact NF29.isRupert_K4a_all _ ha2 hb0 hV G G1
  · exact NF29.isRupert_K4b_all _ ha2 hb0 hV G G1

/-- **Type 29, class K3 (§21.2 with Theorem P), from the facets.**  As `isRupert_type29_K4`, for
the class K3: K3a (`a2 < 0 < b0`, `V > 0`) or K3b (`a2 > 0 > b0`, `V < 0`). -/
theorem isRupert_type29_K3 {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (F : OctFacets (x 0) (x 4) (x 1) (x 3) (x 2) (x 5)) (hd : IsCap29 F (x 6))
    (h : ∀ N : NF29 x,
      (N.a2 < 0 ∧ 0 < N.b0 ∧ 0 < N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0) ∧
        K3Gen N ∧ K3C1Gen N) ∨
      (0 < N.a2 ∧ N.b0 < 0 ∧ N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0) < 0 ∧
        K3Gen N.sigma ∧ K3C1Gen N.sigma)) : IsRupert (univ.image x) := by
  obtain ⟨ha2, hb0, hV, G, G1⟩ | ⟨ha2, hb0, hV, G, G1⟩ := h (IsCap29.toNF29 hx F hd)
  · exact NF29.isRupert_K3a_all _ ha2 hb0 hV G G1
  · exact NF29.isRupert_K3b_all _ ha2 hb0 hV G G1

end Minimality

end
