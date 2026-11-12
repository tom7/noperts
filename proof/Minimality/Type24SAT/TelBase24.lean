module

public import Minimality.Type24SAT.FrameInst24

@[expose] public section

/-!
# Type 24, layer L4c: the TEL schema

The TEL rows of the type 24 encoder (WREL=128) are eager `notAllSame` rows: each line
`nas t_1 ... t_m` says that the strict signs of the terms `t_i` (a shape literal with a sign, or a constant `+-1`) are not all
true and not all false.  Soundness of a line is an identity `sum_i w_i * u_i = 0` with weights `w_i > 0` (products of
forced convexity values) and `u_i = s_i * val x lit_i` (or `+-1`).
-/

set_option autoImplicit false
open scoped RealInnerProductSpace

namespace Minimality.T24.SAT
open Minimality

/-- **TEL schema.**  An identity `sum c_i v_i = 0` with all `c_i > 0` (over a nonempty index set) forbids all `v_i`
strictly positive, and all `v_i` strictly negative. -/
theorem notAllSame_of_identity {ι : Type} (s : Finset ι) (hne : s.Nonempty) (c v : ι → ℝ)
    (hc : ∀ i ∈ s, 0 < c i) (h : ∑ i ∈ s, c i * v i = 0) :
    ¬ (∀ i ∈ s, 0 < v i) ∧ ¬ (∀ i ∈ s, v i < 0) := by
  constructor
  · intro hp
    have : 0 < ∑ i ∈ s, c i * v i := Finset.sum_pos (fun i hi => mul_pos (hc i hi) (hp i hi)) hne
    linarith
  · intro hn
    have : ∑ i ∈ s, c i * v i < 0 := Finset.sum_neg (fun i hi => mul_neg_of_pos_of_neg (hc i hi) (hn i hi)) hne
    linarith

/-- Convexity values are positive. -/
theorem cvpos {x : Nat → ℝ³} (hC : Convex24 x) (t v : Nat) (h : (t, v) ∈ cvList) : 0 < cv x t v := hC (t, v) h

theorem sumsq_zero (u v w : ℝ) (h : u * u + v * v + w * w = 0) : u = 0 ∧ v = 0 ∧ w = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith [mul_self_nonneg u, mul_self_nonneg v, mul_self_nonneg w]

theorem param_aux (a1 a2 a3 b1 b2 b3 c1 c2 c3 d1 d2 d3 : ℝ)
    (hq : (a2 * b3 - a3 * b2) * c1 + (a3 * b1 - a1 * b3) * c2 + (a1 * b2 - a2 * b1) * c3 = 0)
    (hd : (a2 * b3 - a3 * b2) * d1 + (a3 * b1 - a1 * b3) * d2 + (a1 * b2 - a2 * b1) * d3 ≠ 0) :
    ∃ al be : ℝ, c1 = al * a1 + be * b1 ∧ c2 = al * a2 + be * b2 ∧ c3 = al * a3 + be * b3 := by
  have hn : (a2 * b3 - a3 * b2) * (a2 * b3 - a3 * b2) + (a3 * b1 - a1 * b3) * (a3 * b1 - a1 * b3)
      + (a1 * b2 - a2 * b1) * (a1 * b2 - a2 * b1) ≠ 0 := by
    intro h0
    obtain ⟨h1, h2, h3⟩ := sumsq_zero _ _ _ h0
    apply hd; rw [h1, h2, h3]; ring
  refine ⟨((c2 * b3 - c3 * b2) * (a2 * b3 - a3 * b2) + (c3 * b1 - c1 * b3) * (a3 * b1 - a1 * b3)
      + (c1 * b2 - c2 * b1) * (a1 * b2 - a2 * b1)) / ((a2 * b3 - a3 * b2) * (a2 * b3 - a3 * b2)
      + (a3 * b1 - a1 * b3) * (a3 * b1 - a1 * b3) + (a1 * b2 - a2 * b1) * (a1 * b2 - a2 * b1)),
    ((a2 * c3 - a3 * c2) * (a2 * b3 - a3 * b2) + (a3 * c1 - a1 * c3) * (a3 * b1 - a1 * b3)
      + (a1 * c2 - a2 * c1) * (a1 * b2 - a2 * b1)) / ((a2 * b3 - a3 * b2) * (a2 * b3 - a3 * b2)
      + (a3 * b1 - a1 * b3) * (a3 * b1 - a1 * b3) + (a1 * b2 - a2 * b1) * (a1 * b2 - a2 * b1)), ?_, ?_, ?_⟩
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hn]; linear_combination (a2 * b3 - a3 * b2) * hq
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hn]; linear_combination (a3 * b1 - a1 * b3) * hq
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hn]; linear_combination (a1 * b2 - a2 * b1) * hq

/-- Parametrization of the planar quadrilateral: `x5 - x0 = al (x3 - x0) + be (x4 - x0)` (from `QuadD` and
`cv_{D,1} > 0`, which makes `x3 - x0`, `x4 - x0` independent).  With it every TEL identity is a polynomial identity. -/
theorem quad_param (x : Nat → ℝ³) (hC : Convex24 x) (hQ : QuadD x) :
    ∃ al be : ℝ, (pt x 5).x = (pt x 0).x + al * ((pt x 3).x - (pt x 0).x) + be * ((pt x 4).x - (pt x 0).x) ∧
      (pt x 5).y = (pt x 0).y + al * ((pt x 3).y - (pt x 0).y) + be * ((pt x 4).y - (pt x 0).y) ∧
      (pt x 5).z = (pt x 0).z + al * ((pt x 3).z - (pt x 0).z) + be * ((pt x 4).z - (pt x 0).z) := by
  have hq := quadD_det x hQ
  have hcv : 0 < cv x 3 1 := hC (3, 1) (by decide)
  rw [cv_eq_cv3, cv3_D] at hcv
  simp only [V3.det, V3.dot, V3.cr, V3.sub] at hq hcv
  obtain ⟨al, be, h1, h2, h3⟩ := param_aux ((pt x 3).x - (pt x 0).x) ((pt x 3).y - (pt x 0).y) ((pt x 3).z - (pt x 0).z)
    ((pt x 4).x - (pt x 0).x) ((pt x 4).y - (pt x 0).y) ((pt x 4).z - (pt x 0).z)
    ((pt x 5).x - (pt x 0).x) ((pt x 5).y - (pt x 0).y) ((pt x 5).z - (pt x 0).z)
    ((pt x 1).x - (pt x 0).x) ((pt x 1).y - (pt x 0).y) ((pt x 1).z - (pt x 0).z) (by linarith) (by linarith)
  exact ⟨al, be, by linarith, by linarith, by linarith⟩

end Minimality.T24.SAT
