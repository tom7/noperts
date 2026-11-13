module

public import Minimality.Type08S.P2QQ0c
public import Minimality.Type08S.SCk
public import Minimality.Type08S.SCn

@[expose] public section

set_option relaxedAutoImplicit true
set_option autoImplicit true
set_option relaxedAutoImplicit true

set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace W5

variable {e1 e2 e3 : ℝ³}

/-- An affine function with gradient `N` in frame coordinates about `o`. -/
theorem fcoord (hF : Fr e1 e2 e3) {f : ℝ³ → ℝ} {N : ℝ³} (hN : ∀ y z, f y - f z = ⟪N, y - z⟫)
    (o y : ℝ³) :
    f y - f o = ⟪N, e1⟫ * ⟪y - o, e1⟫ + ⟪N, e2⟫ * ⟪y - o, e2⟫ + ⟪N, e3⟫ * ⟪y - o, e3⟫ := by
  rw [hN]
  have h := hF.expand (y - o)
  conv_lhs => rw [h]
  simp only [inner_add_right, real_inner_smul_right]
  ring

/-- **Side lemma** (a facet through the F-side `xp f` seen in the plane `Y = 0`): `x` and `p`
on the same (negative) side forces `κ (L zp - zf Xp) > 0`. -/
theorem side_pos (hF : Fr e1 e2 e3) {f : ℝ³ → ℝ} {N : ℝ³} (hN : ∀ y z, f y - f z = ⟪N, y - z⟫)
    {xp x fp p : ℝ³} {κ : ℝ} (hxp : f xp = 0) (hf : f fp = 0) (hx : f x < 0) (hp : f p < 0)
    (hxe : x - xp = κ • e3) (hfY : ⟪fp - xp, e2⟫ = 0) (hpY : ⟪p - xp, e2⟫ = 0)
    (hL : 0 < ⟪fp - xp, e1⟫) :
    0 < κ * (⟪fp - xp, e1⟫ * ⟪p - xp, e3⟫ - ⟪fp - xp, e3⟫ * ⟪p - xp, e1⟫) := by
  have cf := fcoord hF hN xp fp
  have cx := fcoord hF hN xp x
  have cp := fcoord hF hN xp p
  have n31 : ⟪e3, e1⟫ = 0 := by rw [real_inner_comm]; exact hF.n13
  have n32 : ⟪e3, e2⟫ = 0 := by rw [real_inner_comm]; exact hF.n23
  have e1x : ⟪x - xp, e1⟫ = 0 := by rw [hxe, real_inner_smul_left, n31]; ring
  have e2x : ⟪x - xp, e2⟫ = 0 := by rw [hxe, real_inner_smul_left, n32]; ring
  have e3x : ⟪x - xp, e3⟫ = κ := by rw [hxe, real_inner_smul_left, hF.n33]; ring
  rw [hf, hxp, hfY] at cf
  rw [hxp, e1x, e2x, e3x] at cx
  rw [hpY, hxp] at cp
  have hCk : ⟪N, e3⟫ * κ < 0 := by linarith
  set L := ⟪fp - xp, e1⟫
  set S := L * ⟪p - xp, e3⟫ - ⟪fp - xp, e3⟫ * ⟪p - xp, e1⟫ with hS
  have hCS : ⟪N, e3⟫ * S < 0 := by
    have : ⟪N, e3⟫ * S = L * (f p - 0) := by
      rw [hS]; linear_combination (-L) * cp + ⟪p - xp, e1⟫ * cf
    nlinarith
  have hC0 : ⟪N, e3⟫ ≠ 0 := by intro h; rw [h] at hCk; simp at hCk
  have : 0 < (⟪N, e3⟫ * κ) * (⟪N, e3⟫ * S) := mul_pos_of_neg_of_neg hCk hCS
  have h2 : 0 < ⟪N, e3⟫ ^ 2 * (κ * S) := by nlinarith
  exact (pos_of_mul_pos_right h2 (sq_nonneg _)) 

/-- Nondegeneracy determinants of a `Norm08w` shape, through the normal form. -/
theorem det_ne08 {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d) :
    det3 (c' - a') (c - a') (b - a') ≠ 0 ∧ det3 (b' - d) (b - d) (c - d) ≠ 0 ∧
    det3 (b' - b) (d - b) (c' - b) ≠ 0 := by
  obtain ⟨o, E1, E2, E3, θ, hE, hθ, hpts, -⟩ := exists_nf08w N
  have key : ∀ i j k w : Fin 7, det3 (pts08 a a' b b' c c' d j - pts08 a a' b b' c c' d i)
      (pts08 a a' b b' c c' d k - pts08 a a' b b' c c' d i)
      (pts08 a a' b b' c c' d w - pts08 a a' b b' c c' d i) = det3 E1 E2 E3 * fc08 θ i j k w := by
    intro i j k w; rw [hpts]; exact det3_nf08 o E1 E2 E3 θ i j k w
  obtain ⟨p0, p1, p2, p3, p4, p5, -⟩ := facts08w θ hθ.1 hθ.2.1 hθ.2.2
  have q9 := hθ.1 8 (by decide) (by decide) (by decide)
  simp only [ineq08, Matrix.cons_val] at q9
  refine ⟨?_, ?_, ?_⟩
  · have h := key 1 5 4 2
    have e : fc08 θ 1 5 4 2 = θ 0 * (θ 4 + θ 5 - 1) := by
      simp only [fc08, cdet, cp08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; ring
    simp only [pts08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h
    rw [e] at h; rw [h]
    exact mul_ne_zero hE (mul_pos p0 q9).ne'
  · have h := key 6 3 2 4
    have e : fc08 θ 6 3 2 4 = θ 2 := by
      simp only [fc08, cdet, cp08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; ring
    simp only [pts08, Matrix.cons_val] at h
    rw [e] at h; rw [h]
    exact mul_ne_zero hE p2.ne'
  · have h := key 2 3 6 5
    have e : fc08 θ 2 3 6 5 = θ 3 * θ 0 := by
      simp only [fc08, cdet, cp08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; ring
    simp only [pts08, Matrix.cons_val] at h
    rw [e] at h; rw [h]
    exact mul_ne_zero hE (mul_pos p3 p0).ne'

theorem pos_of_neg_mul {B Y : ℝ} (hB : B < 0) (h : B * Y < 0) : 0 < Y := by
  by_contra hh; push Not at hh; nlinarith

theorem frame_N2 {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d) :
    ∃ (e1 e2 e3 : ℝ³) (κ : ℝ), Fr e1 e2 e3 ∧ κ ≠ 0 ∧ c - a' = κ • e3 ∧ ⟪b - a', e2⟫ = 0 ∧
      0 < ⟪b - a', e1⟫ ∧ 0 < ⟪c' - a', e2⟫ := by
  obtain ⟨e1, e2, e3, κ, hF, hκ, hu, hv2, hv1, hw2⟩ := frame_ex_pos (det_ne08 N).1
  exact ⟨e1, e2, e3, κ, hF, hκ, hu, hv2, hv1, hw2⟩

theorem sub_eq_pc (hF : Fr e1 e2 e3) (xp q : ℝ³) :
    q - xp = pc e1 e2 e3 ⟪q - xp, e1⟫ ⟪q - xp, e2⟫ ⟪q - xp, e3⟫ := by
  rw [pc]; exact hF.expand _

theorem frame_Kb {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d) :
    ∃ (e1 e2 e3 : ℝ³) (κ : ℝ), Fr e1 e2 e3 ∧ κ ≠ 0 ∧ b - d = κ • e3 ∧ ⟪c - d, e2⟫ = 0 ∧
      0 < ⟪c - d, e1⟫ ∧ 0 < ⟪b' - d, e2⟫ := by
  obtain ⟨e1, e2, e3, κ, hF, hκ, hu, hv2, hv1, hw2⟩ := frame_ex_pos (det_ne08 N).2.1
  exact ⟨e1, e2, e3, κ, hF, hκ, hu, hv2, hv1, hw2⟩

theorem frame_K2 {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d) :
    ∃ (e1 e2 e3 : ℝ³) (κ : ℝ), Fr e1 e2 e3 ∧ κ ≠ 0 ∧ d - b = κ • e3 ∧ ⟪c' - b, e2⟫ = 0 ∧
      0 < ⟪c' - b, e1⟫ ∧ 0 < ⟪b' - b, e2⟫ := by
  obtain ⟨e1, e2, e3, κ, hF, hκ, hu, hv2, hv1, hw2⟩ := frame_ex_pos (det_ne08 N).2.2
  exact ⟨e1, e2, e3, κ, hF, hκ, hu, hv2, hv1, hw2⟩

end W5
end Type08Sp
end Minimality
