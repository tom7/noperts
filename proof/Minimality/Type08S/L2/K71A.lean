module

public import Minimality.Type08S.L2.K61Z

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace
namespace Minimality.Type08Sp.C2

theorem k71_gip (e1 e2 e3 : ℝ³) (x1 x2 x3 y1 y2 y3 : ℝ) :
    ⟪x1 • e1 + x2 • e2 + x3 • e3, y1 • e1 + y2 • e2 + y3 • e3⟫ =
      x1 * y1 * ⟪e1, e1⟫ + (x1 * y2 + x2 * y1) * ⟪e1, e2⟫ + (x1 * y3 + x3 * y1) * ⟪e1, e3⟫ +
      x2 * y2 * ⟪e2, e2⟫ + (x2 * y3 + x3 * y2) * ⟪e2, e3⟫ + x3 * y3 * ⟪e3, e3⟫ := by
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  rw [real_inner_comm e1 e2, real_inner_comm e1 e3, real_inner_comm e2 e3]
  ring

end Minimality.Type08Sp.C2
