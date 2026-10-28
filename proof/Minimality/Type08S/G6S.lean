module

public import Minimality.Generic.MotionCert

@[expose] public section

set_option autoImplicit true

/-!
# G6' : Lemma 08.S (split-corner criterion with spin) in an orthonormal frame at the view `ℓ`

Frame `(e1, e2, e3)` positively oriented orthonormal, `e3 = u` the view, `(X, Y, z)` the
coordinates of §41.0: `c = (0,0,C)`, `a' = (0,0,A)`, `2 = (L,0,W)`, `b = (L,0,B)`,
`b' = (X0,h,P)`, `c' = (X1,h,R)`, `a = (L + t (X1-L), t h, za)`; origin `o`.
The motion is `F(X,z) = f0 + f1 z + θ X`, `γ(z) = k F(L,z) - 1` (`k = s/h`), tilt
`d = -(k e1 + e2)`.  The conclusion is `isRupert_of_motionCert` with the 10 rows of §41.2
(rim `(b, c', b', c, 2)`) and the triangle rows for `a, a'`.
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

structure Fr (e1 e2 e3 : ℝ³) : Prop where
  n11 : ⟪e1, e1⟫ = 1
  n22 : ⟪e2, e2⟫ = 1
  n33 : ⟪e3, e3⟫ = 1
  n12 : ⟪e1, e2⟫ = 0
  n13 : ⟪e1, e3⟫ = 0
  n23 : ⟪e2, e3⟫ = 0
  c12 : cross e1 e2 = e3
  c23 : cross e2 e3 = e1
  c31 : cross e3 e1 = e2

theorem cross_add_l (a b c : ℝ³) : cross (a + b) c = cross a c + cross b c := by
  ext i; fin_cases i <;> simp [cross] <;> ring
theorem cross_add_r (a b c : ℝ³) : cross a (b + c) = cross a b + cross a c := by
  ext i; fin_cases i <;> simp [cross] <;> ring
theorem cross_smul_l (r : ℝ) (a b : ℝ³) : cross (r • a) b = r • cross a b := by
  ext i; fin_cases i <;> simp [cross] <;> ring
theorem cross_smul_r (r : ℝ) (a b : ℝ³) : cross a (r • b) = r • cross a b := by
  ext i; fin_cases i <;> simp [cross] <;> ring
theorem cross_self' (a : ℝ³) : cross a a = 0 := by
  ext i; fin_cases i <;> simp [cross] <;> ring
theorem cross_anti' (a b : ℝ³) : cross b a = - cross a b := by
  ext i; fin_cases i <;> simp [cross] <;> ring

/-- Frame coordinates. -/
def pc (e1 e2 e3 : ℝ³) (X Y z : ℝ) : ℝ³ := X • e1 + Y • e2 + z • e3

variable {e1 e2 e3 : ℝ³}

theorem cross_pc (hF : Fr e1 e2 e3) (a1 a2 a3 b1 b2 b3 : ℝ) :
    cross (pc e1 e2 e3 a1 a2 a3) (pc e1 e2 e3 b1 b2 b3) =
      pc e1 e2 e3 (a2 * b3 - a3 * b2) (a3 * b1 - a1 * b3) (a1 * b2 - a2 * b1) := by
  have c21 : cross e2 e1 = - e3 := by rw [cross_anti', hF.c12]
  have c32 : cross e3 e2 = - e1 := by rw [cross_anti', hF.c23]
  have c13 : cross e1 e3 = - e2 := by rw [cross_anti', hF.c31]
  simp only [pc, cross_add_l, cross_add_r, cross_smul_l, cross_smul_r, cross_self', hF.c12,
    hF.c23, hF.c31, c21, c32, c13, smul_zero]
  module

theorem inner_pc (hF : Fr e1 e2 e3) (a1 a2 a3 b1 b2 b3 : ℝ) :
    ⟪pc e1 e2 e3 a1 a2 a3, pc e1 e2 e3 b1 b2 b3⟫ = a1 * b1 + a2 * b2 + a3 * b3 := by
  simp only [pc, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    hF.n11, hF.n22, hF.n33, hF.n12, hF.n13, hF.n23, real_inner_comm e1 e2, real_inner_comm e1 e3,
    real_inner_comm e2 e3]
  ring

theorem det3_pc (hF : Fr e1 e2 e3) (a1 a2 a3 b1 b2 b3 c1 c2 c3 : ℝ) :
    det3 (pc e1 e2 e3 a1 a2 a3) (pc e1 e2 e3 b1 b2 b3) (pc e1 e2 e3 c1 c2 c3) =
      (a2 * b3 - a3 * b2) * c1 + (a3 * b1 - a1 * b3) * c2 + (a1 * b2 - a2 * b1) * c3 := by
  rw [det3, cross_pc hF, inner_pc hF]

theorem pc_sub (a1 a2 a3 b1 b2 b3 : ℝ) :
    pc e1 e2 e3 a1 a2 a3 - pc e1 e2 e3 b1 b2 b3 = pc e1 e2 e3 (a1 - b1) (a2 - b2) (a3 - b3) := by
  simp only [pc]; module

theorem vel_pc (hF : Fr e1 e2 e3) (o : ℝ³) (w1 w2 w3 t1 t2 t3 x1 x2 x3 : ℝ) :
    cross (pc e1 e2 e3 w1 w2 w3) (o + pc e1 e2 e3 x1 x2 x3) +
        (pc e1 e2 e3 t1 t2 t3 - cross (pc e1 e2 e3 w1 w2 w3) o) =
      pc e1 e2 e3 (w2 * x3 - w3 * x2 + t1) (w3 * x1 - w1 * x3 + t2) (w1 * x2 - w2 * x1 + t3) := by
  rw [cross_add_r, cross_pc hF]
  simp only [pc]; module

theorem ev_aff (a b : ℝ) (ha : 0 < a) : ∀ᶠ k in atTop, 0 < a * k + b := by
  filter_upwards [eventually_gt_atTop (-b / a)] with k hk
  have := (div_lt_iff₀ ha).1 hk
  nlinarith

end Type08Sp
end Minimality
