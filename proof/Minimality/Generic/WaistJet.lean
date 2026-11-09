module

public import Minimality.Generic.CayleyJet
public import Minimality.PolygonHalfPlanes

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace
open Polynomial Minimality
namespace Waist

noncomputable def jc (n0 n1 h v0 v1 v2 z t2 t3 t4 u2 u3 u4 : ℝ) : ℕ → ℝ := fun k =>
  [ -h + n0*v0 + n1*v1,
    2*n0*v2,
    -h + n0*t2 - n0*v0 - 2*n0*v1*z + n1*u2 + 2*n1*v0*z + n1*v1,
    n0*t3 + n1*u3 + 2*n1*v2*z,
    -h*z^2 + n0*t2 + n0*t4 - n0*v0*z^2 + n1*u2 + n1*u4 - n1*v1*z^2,
    n0*t3 + n1*u3,
    n0*t2*z^2 + n0*t4 + n1*u2*z^2 + n1*u4,
    z^2*(n0*t3 + n1*u3),
    z^2*(n0*t4 + n1*u4) ].getD k 0

noncomputable def pj (a : ℕ → ℝ) : ℝ[X] := ∑ k ∈ Finset.range 9, C (a k) * X^k

lemma pj_coeff (a : ℕ → ℝ) (j : ℕ) : (pj a).coeff j = if j < 9 then a j else 0 := by
  simp [pj, coeff_C_mul, coeff_X_pow]

lemma pj_tc (a : ℕ → ℝ) (m : ℕ) (hm : m < 9) (h0 : ∀ i < m, a i = 0) (hneg : a m < 0) :
    (pj a).trailingCoeff < 0 := by
  have hc : (pj a).coeff m = a m := by rw [pj_coeff]; simp [hm]
  have hne : pj a ≠ 0 := by
    intro h; rw [h] at hc; simp at hc; linarith
  have h1 : (pj a).natTrailingDegree = m := by
    apply le_antisymm (natTrailingDegree_le_of_ne_zero (by rw [hc]; exact hneg.ne))
    apply le_natTrailingDegree hne
    intro i hi; rw [pj_coeff]; simp [lt_trans hi hm, h0 i hi]
  rw [trailingCoeff, h1, hc]; exact hneg

lemma N_eq (n : ℝ²) (h : ℝ) (v : ℝ³) (z t2 t3 t4 u2 u3 u4 : ℝ) :
    cayleyJetN n h ![0, X, C z * X^2]
      ![C t2 * X^2 + C t3 * X^3 + C t4 * X^4, C u2 * X^2 + C u3 * X^3 + C u4 * X^4] v
    = pj (jc (n 0) (n 1) h (v 0) (v 1) (v 2) z t2 t3 t4 u2 u3 u4) := by
  simp only [cayleyJetN, pj, jc, Finset.sum_range_succ, Finset.sum_range_zero]
  simp [map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat]
  ring

end Waist
