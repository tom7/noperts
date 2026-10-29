module

public import Minimality.Type08S.G6Lem

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- Triangle (hidden-vertex) certificate: the second disjunct of `MotionCert`. -/
def TriCert (V : Finset ℝ³) (u₀ d x : ℝ³) : Prop :=
  ∃ a ∈ V, ∃ b ∈ V, ∃ c ∈ V, TiltSign (b - a) (c - a) u₀ d ∧ TiltSign (b - a) (x - a) u₀ d ∧
      TiltSign (c - b) (x - b) u₀ d ∧ TiltSign (a - c) (x - c) u₀ d

/-- Screen velocity components of the motion `ω = (w1,w2,w3)`, `τ = (t1,t2,0)` at a frame point. -/
def VX (w2 w3 t1 Y z : ℝ) : ℝ := w2 * z - w3 * Y + t1
def VY (w1 w3 t2 X z : ℝ) : ℝ := w3 * X - w1 * z + t2

/-- The five rim vertices `x' = (0,0,zp)`, `x = (0,0,zx)`, `f = (L,0,zf)`, `r`, `g` of a
split-corner rim in frame coordinates, plus a set `E` of other vertices. -/
noncomputable def rim5 (e1 e2 e3 o : ℝ³) (L zp zx zf Xr Yr zr Xg Yg zg : ℝ) (E : Finset ℝ³) :
    Finset ℝ³ :=
  ({o + pc e1 e2 e3 0 0 zp, o + pc e1 e2 e3 0 0 zx, o + pc e1 e2 e3 L 0 zf,
    o + pc e1 e2 e3 Xr Yr zr, o + pc e1 e2 e3 Xg Yg zg} : Finset ℝ³) ∪ E

set_option hygiene false in
macro "rowS" : tactic => `(tactic| first | (left; linarith) | (right; exact ⟨by ring, by linarith⟩))

/-- **Row form of the split corner (decoupled), any motion.**  Rim `(x', f, r, g, x)` ccw, the
corner `q` carries `x'` and `x` (`x` above `x'`), `F` edge-on along `Y = 0`; tilt `d = (s,-1,0)`;
motion `ω = (w1,w2,w3)`, `τ = (t1,t2,0)` (all in the frame).  Ten corner rows + convexity. -/
theorem sc5_core (hF : Fr e1 e2 e3) (o : ℝ³) (E : Finset ℝ³)
    {σ L s zp zx zf Xr Yr zr Xg Yg zg w1 w2 w3 t1 t2 : ℝ}
    (hL : 0 < L) (hzx : 0 < σ * (zx - zp))
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hYr : 0 < Yr)
    (hcg : 0 < Yg * Xr - Xg * Yr) (hs : 0 < Xg + s * Yg)
    -- velocities
    (h1 : 0 < VY w1 w3 t2 0 zp)
    (h2 : 0 < σ * (zx - zp) * (s * VY w1 w3 t2 0 zp + VX w2 w3 t1 0 zp))
    (h3 : 0 < σ * (zx - zp) * (s * VY w1 w3 t2 0 zx + VX w2 w3 t1 0 zx))
    (h4 : 0 < -Xg * VY w1 w3 t2 0 zx + Yg * VX w2 w3 t1 0 zx)
    (h5 : 0 < (Xr - L) * VY w1 w3 t2 L zf - Yr * VX w2 w3 t1 0 zf)
    (h6 : 0 < VY w1 w3 t2 L zf)
    (h7 : 0 < (Xg - Xr) * VY w1 w3 t2 Xr zr - (Yg - Yr) * VX w2 w3 t1 Yr zr)
    (h8 : 0 < (Xr - L) * VY w1 w3 t2 Xr zr - Yr * VX w2 w3 t1 Yr zr)
    (h9 : 0 < -Xg * VY w1 w3 t2 Xg zg + Yg * VX w2 w3 t1 Yg zg)
    (h10 : 0 < (Xg - Xr) * VY w1 w3 t2 Xg zg - (Yg - Yr) * VX w2 w3 t1 Yg zg)
    (hE : ∀ y ∈ E, TriCert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E)
      (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * s) (-σ) 0) y) :
    IsRupert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E) := by
  have hu : pc e1 e2 e3 0 0 1 ≠ 0 := by
    intro h0
    have := inner_pc hF 0 0 1 0 0 1
    rw [h0, inner_zero_left] at this; norm_num at this
  set ω := pc e1 e2 e3 w1 w2 w3 with hω
  set τ := pc e1 e2 e3 t1 t2 0 - cross ω o with hτ
  refine isRupert_of_motionCert _ (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * s) (-σ) 0) ω τ hu ?_
  intro x hx
  simp only [rim5, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx
  have q1 : 0 < L * (σ * (zx - zp)) := mul_pos hL hzx
  have q2 : 0 < L * VY w1 w3 t2 0 zp := mul_pos hL h1
  have q3 : 0 < σ * (zx - zp) * (Xg + s * Yg) := mul_pos hzx hs
  have q4 : 0 < L * Yr := mul_pos hL hYr
  have q5 : 0 < L * VY w1 w3 t2 L zf := mul_pos hL h6
  simp only [VX, VY] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 q2 q5
  have hmem : ∀ p ∈ ({o + pc e1 e2 e3 0 0 zp, o + pc e1 e2 e3 0 0 zx, o + pc e1 e2 e3 L 0 zf,
    o + pc e1 e2 e3 Xr Yr zr, o + pc e1 e2 e3 Xg Yg zg} : Finset ℝ³),
      p ∈ rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E := fun p hp => by
    simp only [rim5]; exact Finset.mem_union_left _ hp
  have m1 := hmem (o + pc e1 e2 e3 0 0 zp) (by simp)
  have m2 := hmem (o + pc e1 e2 e3 0 0 zx) (by simp)
  have m3 := hmem (o + pc e1 e2 e3 L 0 zf) (by simp)
  have m4 := hmem (o + pc e1 e2 e3 Xr Yr zr) (by simp)
  have m5 := hmem (o + pc e1 e2 e3 Xg Yg zg) (by simp)
  rcases hx with (rfl | rfl | rfl | rfl | rfl) | hx
  · -- x'
    refine Or.inl ⟨_, m2, _, m3, ?_, ?_, ?_⟩ <;>
    · simp only [TiltSign, hω, hτ, vel_pc hF, add_sub_add_left_eq_sub, pc_sub, det3_pc hF]
      rowS
  · -- x
    refine Or.inl ⟨_, m5, _, m1, ?_, ?_, ?_⟩ <;>
    · simp only [TiltSign, hω, hτ, vel_pc hF, add_sub_add_left_eq_sub, pc_sub, det3_pc hF]
      rowS
  · -- f
    refine Or.inl ⟨_, m1, _, m4, ?_, ?_, ?_⟩ <;>
    · simp only [TiltSign, hω, hτ, vel_pc hF, add_sub_add_left_eq_sub, pc_sub, det3_pc hF]
      rowS
  · -- r
    refine Or.inl ⟨_, m3, _, m5, ?_, ?_, ?_⟩ <;>
    · simp only [TiltSign, hω, hτ, vel_pc hF, add_sub_add_left_eq_sub, pc_sub, det3_pc hF]
      rowS
  · -- g
    refine Or.inl ⟨_, m4, _, m2, ?_, ?_, ?_⟩ <;>
    · simp only [TiltSign, hω, hτ, vel_pc hF, add_sub_add_left_eq_sub, pc_sub, det3_pc hF]
      rowS
  · exact Or.inr (hE x hx)

end Type08Sp
end Minimality
