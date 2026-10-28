module

public import Minimality.Type08S.GT_Wrap4

@[expose] public section

set_option autoImplicit true

/-!
# GT wrapper, part 5: screen (y,z) orientation tests of K-edges from two facets

For `P, Q` on two facet planes `F1, F2` (an edge of K), `crossYZ P Q S` is, up to a positive factor
depending only on the edge, `Phi F1 F2 S := F1.ev S * F2.a - F2.ev S * F1.a`.  Hence the sign at
one reference point transfers to every `S` with `Phi S` of the same sign.
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- The silhouette functional of the edge `F1 ∩ F2` for the view along `x`. -/
def Phi (F1 F2 : Fc) (S : V3) : ℝ := F1.ev S * F2.a - F2.ev S * F1.a

theorem cp_real (p1 p2 p3 q1 q2 q3 Dx Dy Dz Xx Xy Xz : ℝ)
    (h1 : Dx * p1 + Dy * p2 + Dz * p3 = 0) (h2 : Dx * q1 + Dy * q2 + Dz * q3 = 0) :
    (Dy * Xz - Dz * Xy) * ((p2 * q3 - p3 * q2) ^ 2 + (p3 * q1 - p1 * q3) ^ 2 + (p1 * q2 - p2 * q1) ^ 2) =
      (Dx * (p2 * q3 - p3 * q2) + Dy * (p3 * q1 - p1 * q3) + Dz * (p1 * q2 - p2 * q1)) *
        ((p1 * Xx + p2 * Xy + p3 * Xz) * q1 - (q1 * Xx + q2 * Xy + q3 * Xz) * p1) := by
  linear_combination
    (Xz * ((p1 * q2 - p2 * q1) * p1 - (p2 * q3 - p3 * q2) * p3) -
      Xy * ((p2 * q3 - p3 * q2) * p2 - (p3 * q1 - p1 * q3) * p1)) * h2 -
    (Xz * ((p1 * q2 - p2 * q1) * q1 - (p2 * q3 - p3 * q2) * q3) -
      Xy * ((p2 * q3 - p3 * q2) * q2 - (p3 * q1 - p1 * q3) * q1)) * h1

theorem cross_planes_id (F1 F2 : Fc) (P Q S : V3)
    (h1P : F1.ev P = 0) (h1Q : F1.ev Q = 0) (h2P : F2.ev P = 0) (h2Q : F2.ev Q = 0) :
    crossYZ P Q S * ((F1.a * F2.b - F1.b * F2.a) ^ 2 + (F1.b * F2.c - F1.c * F2.b) ^ 2 +
        (F1.c * F2.a - F1.a * F2.c) ^ 2) =
      ((Q.x - P.x) * (F1.b * F2.c - F1.c * F2.b) + (Q.y - P.y) * (F1.c * F2.a - F1.a * F2.c) +
        (Q.z - P.z) * (F1.a * F2.b - F1.b * F2.a)) * Phi F1 F2 S := by
  simp only [Fc.ev] at h1P h1Q h2P h2Q
  have key := cp_real F1.a F1.b F1.c F2.a F2.b F2.c (Q.x - P.x) (Q.y - P.y) (Q.z - P.z)
    (S.x - P.x) (S.y - P.y) (S.z - P.z) (by linarith) (by linarith)
  have e1 : F1.a * (S.x - P.x) + F1.b * (S.y - P.y) + F1.c * (S.z - P.z) = F1.ev S := by
    simp only [Fc.ev]; linarith
  have e2 : F2.a * (S.x - P.x) + F2.b * (S.y - P.y) + F2.c * (S.z - P.z) = F2.ev S := by
    simp only [Fc.ev]; linarith
  rw [e1, e2] at key
  simp only [crossYZ, Phi]
  linear_combination key

theorem sq3_zero {x y z : ℝ} (h : x ^ 2 + y ^ 2 + z ^ 2 = 0) : x = 0 ∧ y = 0 ∧ z = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]

/-- Sign transfer along an edge `P Q = F1 ∩ F2`. -/
theorem cross_neg_of_planes (F1 F2 : Fc) (P Q S0 S : V3)
    (h1P : F1.ev P = 0) (h1Q : F1.ev Q = 0) (h2P : F2.ev P = 0) (h2Q : F2.ev Q = 0)
    (c0 : crossYZ P Q S0 < 0) (f0 : Phi F1 F2 S0 < 0) (f : Phi F1 F2 S < 0) :
    crossYZ P Q S < 0 := by
  have i0 := cross_planes_id F1 F2 P Q S0 h1P h1Q h2P h2Q
  have i := cross_planes_id F1 F2 P Q S h1P h1Q h2P h2Q
  set M := (F1.a * F2.b - F1.b * F2.a) ^ 2 + (F1.b * F2.c - F1.c * F2.b) ^ 2 +
        (F1.c * F2.a - F1.a * F2.c) ^ 2 with hM
  set T := (Q.x - P.x) * (F1.b * F2.c - F1.c * F2.b) + (Q.y - P.y) * (F1.c * F2.a - F1.a * F2.c) +
        (Q.z - P.z) * (F1.a * F2.b - F1.b * F2.a) with hT
  have hM0 : 0 ≤ M := by positivity
  have hM1 : 0 < M := by
    rcases hM0.lt_or_eq with h | h
    · exact h
    · exfalso
      have hz := sq3_zero (x := F1.a * F2.b - F1.b * F2.a) (y := F1.b * F2.c - F1.c * F2.b)
        (z := F1.c * F2.a - F1.a * F2.c) h.symm
      obtain ⟨z1, z2, z3⟩ := hz
      have e1 : F1.ev S0 = F1.a * (S0.x - P.x) + F1.b * (S0.y - P.y) + F1.c * (S0.z - P.z) := by
        simp only [Fc.ev] at h1P ⊢; linarith
      have e2 : F2.ev S0 = F2.a * (S0.x - P.x) + F2.b * (S0.y - P.y) + F2.c * (S0.z - P.z) := by
        simp only [Fc.ev] at h2P ⊢; linarith
      have : Phi F1 F2 S0 = 0 := by
        simp only [Phi]; rw [e1, e2]
        linear_combination (-(S0.y - P.y)) * z1 + (S0.z - P.z) * z3
      linarith
  have hT0 : 0 < T := by
    by_contra hh; push Not at hh
    nlinarith [mul_neg_of_neg_of_pos c0 hM1, mul_nonneg_of_nonpos_of_nonpos hh f0.le]
  by_contra hh; push Not at hh
  nlinarith [mul_pos hT0 (neg_pos.mpr f), mul_nonneg hh hM1.le]

end Type08Sp
end Minimality
