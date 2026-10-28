module

public import Minimality.Type08S.GT_Wrap11

@[expose] public section

set_option autoImplicit true

/-!
# GT wrapper, part 12: same-sign transfer along K-edges without a reference point

For an edge `P Q = F1 ∩ F2` and two vertices `S, S'` with `Phi S * Phi S' > 0`, the numbers
`crossYZ P Q S` and `crossYZ P Q S'` have the same sign (the edge is nondegenerate).  Chaining around
a cycle (consecutive edges share a triple) fixes all signs from one edge (`a'c`, computed directly).
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

theorem vec_id (n1x n1y n1z n2x n2y n2z vx vy vz : ℝ) :
    ((n1y*n2z-n1z*n2y)^2 + (n1z*n2x-n1x*n2z)^2 + (n1x*n2y-n1y*n2x)^2) * vx =
      (vx*(n1y*n2z-n1z*n2y) + vy*(n1z*n2x-n1x*n2z) + vz*(n1x*n2y-n1y*n2x)) * (n1y*n2z-n1z*n2y)
      + ((n1z*n2x-n1x*n2z) * n1z - (n1x*n2y-n1y*n2x) * n1y) * (n2x*vx+n2y*vy+n2z*vz)
      - ((n1z*n2x-n1x*n2z) * n2z - (n1x*n2y-n1y*n2x) * n2y) * (n1x*vx+n1y*vy+n1z*vz) := by ring

theorem vec_id_y (n1x n1y n1z n2x n2y n2z vx vy vz : ℝ) :
    ((n1y*n2z-n1z*n2y)^2 + (n1z*n2x-n1x*n2z)^2 + (n1x*n2y-n1y*n2x)^2) * vy =
      (vx*(n1y*n2z-n1z*n2y) + vy*(n1z*n2x-n1x*n2z) + vz*(n1x*n2y-n1y*n2x)) * (n1z*n2x-n1x*n2z)
      + ((n1x*n2y-n1y*n2x) * n1x - (n1y*n2z-n1z*n2y) * n1z) * (n2x*vx+n2y*vy+n2z*vz)
      - ((n1x*n2y-n1y*n2x) * n2x - (n1y*n2z-n1z*n2y) * n2z) * (n1x*vx+n1y*vy+n1z*vz) := by ring

theorem vec_id_z (n1x n1y n1z n2x n2y n2z vx vy vz : ℝ) :
    ((n1y*n2z-n1z*n2y)^2 + (n1z*n2x-n1x*n2z)^2 + (n1x*n2y-n1y*n2x)^2) * vz =
      (vx*(n1y*n2z-n1z*n2y) + vy*(n1z*n2x-n1x*n2z) + vz*(n1x*n2y-n1y*n2x)) * (n1x*n2y-n1y*n2x)
      + ((n1y*n2z-n1z*n2y) * n1y - (n1z*n2x-n1x*n2z) * n1x) * (n2x*vx+n2y*vy+n2z*vz)
      - ((n1y*n2z-n1z*n2y) * n2y - (n1z*n2x-n1x*n2z) * n2x) * (n1x*vx+n1y*vy+n1z*vz) := by ring

theorem cross_pos_prod (F1 F2 F3 : Fc) (P Q S S' : V3)
    (h1P : F1.ev P = 0) (h1Q : F1.ev Q = 0) (h2P : F2.ev P = 0) (h2Q : F2.ev Q = 0)
    (hne : F3.ev P ≠ F3.ev Q)
    (f : 0 < Phi F1 F2 S * Phi F1 F2 S') :
    0 < crossYZ P Q S * crossYZ P Q S' := by
  have i := cross_planes_id F1 F2 P Q S h1P h1Q h2P h2Q
  have i' := cross_planes_id F1 F2 P Q S' h1P h1Q h2P h2Q
  have hp1 : F1.a * (Q.x - P.x) + F1.b * (Q.y - P.y) + F1.c * (Q.z - P.z) = 0 := by
    simp only [Fc.ev] at h1P h1Q; linarith
  have hp2 : F2.a * (Q.x - P.x) + F2.b * (Q.y - P.y) + F2.c * (Q.z - P.z) = 0 := by
    simp only [Fc.ev] at h2P h2Q; linarith
  have vx := vec_id F1.a F1.b F1.c F2.a F2.b F2.c (Q.x - P.x) (Q.y - P.y) (Q.z - P.z)
  have vy := vec_id_y F1.a F1.b F1.c F2.a F2.b F2.c (Q.x - P.x) (Q.y - P.y) (Q.z - P.z)
  have vz := vec_id_z F1.a F1.b F1.c F2.a F2.b F2.c (Q.x - P.x) (Q.y - P.y) (Q.z - P.z)
  rw [hp1, hp2] at vx vy vz
  have hMe : (F1.a*F2.b-F1.b*F2.a)^2 + (F1.b*F2.c-F1.c*F2.b)^2 + (F1.c*F2.a-F1.a*F2.c)^2 = (F1.b*F2.c-F1.c*F2.b)^2 + (F1.c*F2.a-F1.a*F2.c)^2 + (F1.a*F2.b-F1.b*F2.a)^2 := by ring
  rw [hMe] at i i'
  generalize hM : (F1.b*F2.c-F1.c*F2.b)^2 + (F1.c*F2.a-F1.a*F2.c)^2 + (F1.a*F2.b-F1.b*F2.a)^2 = M at vx vy vz i i'
  generalize hT : (Q.x - P.x)*(F1.b*F2.c-F1.c*F2.b) + (Q.y - P.y)*(F1.c*F2.a-F1.a*F2.c) + (Q.z - P.z)*(F1.a*F2.b-F1.b*F2.a) = T at vx vy vz i i'
  have hM1 : 0 < M := by
    rcases (show 0 ≤ M by rw [← hM]; positivity).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← hM] at h
      obtain ⟨z1, z2, z3⟩ := sq3_zero (x := F1.b*F2.c-F1.c*F2.b) (y := F1.c*F2.a-F1.a*F2.c) (z := F1.a*F2.b-F1.b*F2.a) h.symm
      have e1 : F1.ev S = F1.a * (S.x - P.x) + F1.b * (S.y - P.y) + F1.c * (S.z - P.z) := by
        simp only [Fc.ev] at h1P ⊢; linarith
      have e2 : F2.ev S = F2.a * (S.x - P.x) + F2.b * (S.y - P.y) + F2.c * (S.z - P.z) := by
        simp only [Fc.ev] at h2P ⊢; linarith
      have : Phi F1 F2 S = 0 := by
        simp only [Phi]; rw [e1, e2]
        linear_combination (-(S.y - P.y)) * z3 + (S.z - P.z) * z2
      rw [this] at f; simp at f
  have hT0 : T ≠ 0 := by
    intro hT0
    rw [hT0] at vx vy vz
    have x0 : Q.x = P.x := by
      have := (mul_eq_zero.mp (by linarith : M * (Q.x - P.x) = 0)).resolve_left hM1.ne'; linarith
    have y0 : Q.y = P.y := by
      have := (mul_eq_zero.mp (by linarith : M * (Q.y - P.y) = 0)).resolve_left hM1.ne'; linarith
    have z0 : Q.z = P.z := by
      have := (mul_eq_zero.mp (by linarith : M * (Q.z - P.z) = 0)).resolve_left hM1.ne'; linarith
    apply hne; simp only [Fc.ev]; rw [x0, y0, z0]
  have key : crossYZ P Q S * crossYZ P Q S' * M ^ 2 = T ^ 2 * (Phi F1 F2 S * Phi F1 F2 S') := by
    calc crossYZ P Q S * crossYZ P Q S' * M ^ 2 = (crossYZ P Q S * M) * (crossYZ P Q S' * M) := by ring
      _ = (T * Phi F1 F2 S) * (T * Phi F1 F2 S') := by rw [i, i']
      _ = _ := by ring
  have h1 : 0 < T ^ 2 * (Phi F1 F2 S * Phi F1 F2 S') := mul_pos (by positivity) f
  rw [← key] at h1
  exact (mul_pos_iff_of_pos_right (by positivity)).mp h1

theorem crossYZ_cyc (P Q S : V3) : crossYZ P Q S = crossYZ Q S P := by simp only [crossYZ]; ring

end Type08Sp
end Minimality
