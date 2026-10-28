module

public import Minimality.Type08S.GT_Wrap16

@[expose] public section

set_option autoImplicit true

/-!
# GT wrapper, part 17: N2, `r2 = b2`: the corrected core (`2, a, c', b` collinear on the screen)

At `r2 = b2` the facet `Q_ab` contains the view direction `e`, so `2, a, c', b` are screen-collinear and
the strict `hcv` of `propH_n2_ge_eq` is false for the triple `(2, a, c')`.  The tilt breaks the tie:
for a triple in `Q_ab`, `n = (Q-P)x(S-P)` is parallel to the normal `(0, β, γ)`, so the tilt row is
`n_y + tt n_z = n_z (β/γ + tt)`, positive iff the xy-orientation `n_z` is.
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

def cxy (P Q S : V3) : ℝ := (Q.x - P.x) * (S.y - P.y) - (Q.y - P.y) * (S.x - P.x)

theorem lex_of_tilt {tt : ℝ} {P Q S : V3} (h0 : crossYZ P Q S = 0)
    (h : 0 < ((Q.z - P.z) * (S.x - P.x) - (Q.x - P.x) * (S.z - P.z)) + tt * cxy P Q S) :
    LexTest (-1) ⟨1, 0, 0⟩ ⟨0, -1, -tt⟩ P Q S := by
  right
  simp only [crossYZ] at h0
  simp only [cxy] at h
  refine ⟨?_, ?_⟩
  · simp only [tst, hdet]; linarith
  · simp only [tst, hdet]; nlinarith

/-- Cramer: an affine function vanishing at `P, Q`. -/
theorem cramer4 (g0 g1 g2 : ℝ) (P Q X Y : V3)
    (hP : g0 + g1 * P.x + g2 * P.y = 0) (hQ : g0 + g1 * Q.x + g2 * Q.y = 0) :
    (g0 + g1 * X.x + g2 * X.y) * cxy P Q Y = (g0 + g1 * Y.x + g2 * Y.y) * cxy P Q X := by
  simp only [cxy]
  have e1 : g0 + g1 * X.x + g2 * X.y = g1 * (X.x - P.x) + g2 * (X.y - P.y) := by linarith
  have e2 : g0 + g1 * Y.x + g2 * Y.y = g1 * (Y.x - P.x) + g2 * (Y.y - P.y) := by linarith
  have e3 : g1 * (Q.x - P.x) + g2 * (Q.y - P.y) = 0 := by linarith
  rw [e1, e2]
  have : g2 * (Q.x - P.x) = g2 * (Q.x - P.x) := rfl
  -- (g1 u + g2 v)(Qx cY - Qy cX) = ..., using g1 Qx' + g2 Qy' = 0
  linear_combination ((X.x - P.x) * (Y.y - P.y) - (X.y - P.y) * (Y.x - P.x)) * e3

theorem plane_aff (F G : Fc) (P Q X Y : V3) (hFc : F.c ≠ 0)
    (hP : F.ev P = 0) (hQ : F.ev Q = 0) (hX : F.ev X = 0) (hY : F.ev Y = 0)
    (gP : G.ev P = 0) (gQ : G.ev Q = 0) :
    G.ev X * cxy P Q Y = G.ev Y * cxy P Q X := by
  have key := cramer4 (F.c * G.d - G.c * F.d) (F.c * G.a - G.c * F.a) (F.c * G.b - G.c * F.b) P Q X Y
    (by simp only [Fc.ev] at hP gP; linear_combination F.c * gP - G.c * hP)
    (by simp only [Fc.ev] at hQ gQ; linear_combination F.c * gQ - G.c * hQ)
  have eX : F.c * G.ev X = (F.c * G.d - G.c * F.d) + (F.c * G.a - G.c * F.a) * X.x + (F.c * G.b - G.c * F.b) * X.y := by
    simp only [Fc.ev] at hX ⊢; linear_combination G.c * hX
  have eY : F.c * G.ev Y = (F.c * G.d - G.c * F.d) + (F.c * G.a - G.c * F.a) * Y.x + (F.c * G.b - G.c * F.b) * Y.y := by
    simp only [Fc.ev] at hY ⊢; linear_combination G.c * hY
  rw [← eX, ← eY] at key
  have : F.c * (G.ev X * cxy P Q Y - G.ev Y * cxy P Q X) = 0 := by linarith
  have := (mul_eq_zero.mp this).resolve_left hFc
  linarith

/-- For `n = (Q-P) x (S-P)` of a triple in a plane with normal `(α, β, γ)`: `n_y γ = n_z β`. -/
theorem tilt_parallel (F : Fc) (P Q S : V3) (hP : F.ev P = 0) (hQ : F.ev Q = 0) (hS : F.ev S = 0) :
    ((Q.z - P.z) * (S.x - P.x) - (Q.x - P.x) * (S.z - P.z)) * F.c = cxy P Q S * F.b := by
  simp only [Fc.ev] at hP hQ hS
  simp only [cxy]
  have hu : F.a * (Q.x - P.x) + F.b * (Q.y - P.y) + F.c * (Q.z - P.z) = 0 := by linarith
  have hv : F.a * (S.x - P.x) + F.b * (S.y - P.y) + F.c * (S.z - P.z) = 0 := by linarith
  linear_combination (S.x - P.x) * hu - (Q.x - P.x) * hv

theorem tilt_pos (F : Fc) (P Q S : V3) (hP : F.ev P = 0) (hQ : F.ev Q = 0) (hS : F.ev S = 0)
    (hb : 0 < F.b) (hc : 0 < F.c) {tt : ℝ} (htt : 0 < tt) (hn : 0 < cxy P Q S) :
    0 < ((Q.z - P.z) * (S.x - P.x) - (Q.x - P.x) * (S.z - P.z)) + tt * cxy P Q S := by
  have e := tilt_parallel F P Q S hP hQ hS
  have : 0 < ((Q.z - P.z) * (S.x - P.x) - (Q.x - P.x) * (S.z - P.z)) * F.c := by
    rw [e]; exact mul_pos hn hb
  have h1 : 0 < (Q.z - P.z) * (S.x - P.x) - (Q.x - P.x) * (S.z - P.z) := pos_of_mul_pos_left this hc.le
  nlinarith [mul_pos htt hn]

end Type08Sp
end Minimality
