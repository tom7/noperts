module

public import Minimality.Type08S.G6S

@[expose] public section

set_option autoImplicit true

/-!
# Lemma 08.S as a theorem about points in a frame (G6', explicit motion)
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- Point with frame coordinates `(X, Y, z)` from the origin `o`. -/
def pt (e1 e2 e3 o : ℝ³) (X Y z : ℝ) : ℝ³ := o + pc e1 e2 e3 X Y z

set_option hygiene false in
macro "rowt" : tactic => `(tactic| first | (left; linarith) | (right; exact ⟨by ring, by linarith⟩))

/-- **Lemma 08.S, explicit-motion core.**  `F(X,z) = f0 + f1 z + θ X`, `k = s/h`, tilt
`d = -(k e1 + e2)`, `ω = (-f1, k f1, θ)`, `τ = (k(f0+θL) - 1, f0, 0)` in the frame.
Rows: the ten rim rows of §41.2 and the triangle rows for `a, a'`. -/
theorem lemma08S_core (hF : Fr e1 e2 e3) (o : ℝ³)
    {L h X0 X1 C W B A P R t za f0 f1 θ k : ℝ}
    (hL : 0 < L) (hh : 0 < h) (hX : X0 < X1) (hWB : W < B) (hCA : C < A)
    (ht0 : 0 < t) (ht1 : t < 1) (hza : za < B + t * (R - B))
    (hF0C : 0 < f0 + f1 * C + θ * 0) (hFLW : 0 < f0 + f1 * W + θ * L)
    (hFLC : 0 < f0 + f1 * C + θ * L) (hFLP : 0 < f0 + f1 * P + θ * L)
    (hFXP : f0 + f1 * P + θ * X0 < 0) (hFXR : f0 + f1 * R + θ * X1 < 0)
    (hFLB : f0 + f1 * B + θ * L < 0) (hFLR : f0 + f1 * R + θ * L < 0)
    (hk1 : X1 - L < k * h) (hk2 : X0 < k * h)
    (hk3 : 0 < -X0 * (f0 + f1 * C + θ * 0) + h * (k * (f0 + f1 * C + θ * L) - 1))
    (hk4 : 0 < -X0 * (f0 + f1 * P + θ * X0) + h * (k * (f0 + f1 * P + θ * L) - 1 - θ * h))
    (hk5 : 0 < (X1 - L) * (f0 + f1 * R + θ * X1) - h * (k * (f0 + f1 * R + θ * L) - 1 - θ * h)) :
    IsRupert ({pt e1 e2 e3 o L 0 W, pt e1 e2 e3 o (L + t * (X1 - L)) (t * h) za,
      pt e1 e2 e3 o 0 0 A, pt e1 e2 e3 o L 0 B, pt e1 e2 e3 o X0 h P, pt e1 e2 e3 o 0 0 C,
      pt e1 e2 e3 o X1 h R} : Finset ℝ³) := by
  have hu : pc e1 e2 e3 0 0 1 ≠ 0 := by
    intro h0
    have := inner_pc hF 0 0 1 0 0 1
    rw [h0, inner_zero_left] at this; norm_num at this
  set ω := pc e1 e2 e3 (-f1) (k * f1) θ with hω
  set τ := pc e1 e2 e3 (k * (f0 + θ * L) - 1) f0 0 - cross ω o with hτ
  have p1 : 0 < (f0 + f1 * B + θ * L) * (X1 - L - k * h) :=
    mul_pos_of_neg_of_neg hFLB (by linarith)
  have p2 : 0 < (B - W) * (k * h - (X1 - L)) := mul_pos (by linarith) (by linarith)
  have p3 : 0 < (B - W) * L := mul_pos (by linarith) hL
  have p4 : 0 < L * (f0 + f1 * W + θ * L) := mul_pos hL hFLW
  have p5 : 0 < L * h := mul_pos hL hh
  have p6 : 0 < L * (f0 + f1 * C + θ * 0) := mul_pos hL hF0C
  have p7 : 0 < h * (X1 - X0) := mul_pos hh (by linarith)
  have p8 : 0 < (X0 - X1) * (f0 + f1 * P + θ * X0) := mul_pos_of_neg_of_neg (by linarith) hFXP
  have p9 : 0 < (X0 - X1) * (f0 + f1 * R + θ * X1) := mul_pos_of_neg_of_neg (by linarith) hFXR
  have p10 : 0 < (k * h - (X1 - L)) * (B + t * (R - B) - za) :=
    mul_pos (by linarith) (by linarith)
  have p11 : 0 < (1 - t) * h * L := mul_pos (mul_pos (by linarith) hh) hL
  have p12 : 0 < L * t * h := mul_pos (mul_pos hL ht0) hh
  have p13 : 0 < L * (A - C) := mul_pos hL (by linarith)
  have p14 : 0 < (A - C) * (k * h - X0) := mul_pos (by linarith) (by linarith)
  refine isRupert_of_motionCert _ (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (-k) (-1) 0) ω τ hu ?_
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- 2 = (L,0,W): y0 = c, y1 = b
    refine Or.inl ⟨pt e1 e2 e3 o 0 0 C, by simp, pt e1 e2 e3 o L 0 B, by simp, ?_, ?_, ?_⟩ <;>
    · simp only [TiltSign, pt, hω, hτ, vel_pc hF, add_sub_add_left_eq_sub, pc_sub, det3_pc hF]
      rowt
  · -- a
    refine Or.inr ⟨pt e1 e2 e3 o L 0 B, by simp, pt e1 e2 e3 o X1 h R, by simp,
      pt e1 e2 e3 o 0 0 C, by simp, ?_, ?_, ?_, ?_⟩ <;>
    · simp only [TiltSign, pt, hω, hτ, vel_pc hF, add_sub_add_left_eq_sub, pc_sub, det3_pc hF]
      rowt
  · -- a'
    refine Or.inr ⟨pt e1 e2 e3 o 0 0 C, by simp, pt e1 e2 e3 o L 0 W, by simp,
      pt e1 e2 e3 o X0 h P, by simp, ?_, ?_, ?_, ?_⟩ <;>
    · simp only [TiltSign, pt, hω, hτ, vel_pc hF, add_sub_add_left_eq_sub, pc_sub, det3_pc hF]
      rowt
  · -- b: y0 = 2, y1 = c'
    refine Or.inl ⟨pt e1 e2 e3 o L 0 W, by simp, pt e1 e2 e3 o X1 h R, by simp, ?_, ?_, ?_⟩ <;>
    · simp only [TiltSign, pt, hω, hτ, vel_pc hF, add_sub_add_left_eq_sub, pc_sub, det3_pc hF]
      rowt
  · -- b': y0 = c', y1 = c
    refine Or.inl ⟨pt e1 e2 e3 o X1 h R, by simp, pt e1 e2 e3 o 0 0 C, by simp, ?_, ?_, ?_⟩ <;>
    · simp only [TiltSign, pt, hω, hτ, vel_pc hF, add_sub_add_left_eq_sub, pc_sub, det3_pc hF]
      rowt
  · -- c: y0 = b', y1 = 2
    refine Or.inl ⟨pt e1 e2 e3 o X0 h P, by simp, pt e1 e2 e3 o L 0 W, by simp, ?_, ?_, ?_⟩ <;>
    · simp only [TiltSign, pt, hω, hτ, vel_pc hF, add_sub_add_left_eq_sub, pc_sub, det3_pc hF]
      rowt
  · -- c': y0 = b, y1 = b'
    refine Or.inl ⟨pt e1 e2 e3 o L 0 B, by simp, pt e1 e2 e3 o X0 h P, by simp, ?_, ?_, ?_⟩ <;>
    · simp only [TiltSign, pt, hω, hτ, vel_pc hF, add_sub_add_left_eq_sub, pc_sub, det3_pc hF]
      rowt

end Type08Sp
end Minimality
