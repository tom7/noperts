module

public import Minimality.Type08S.P2CR9

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# P-F extras for P3a: general determinant helper `det3_pts` and the extra picture facts.
-/

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

theorem vec_pc (hF : Fr e1 e2 e3) (O P Q : ℝ³) :
    P - Q = pc e1 e2 e3 (⟪P - O, e1⟫ - ⟪Q - O, e1⟫) (⟪P - O, e2⟫ - ⟪Q - O, e2⟫)
      (⟪P - O, e3⟫ - ⟪Q - O, e3⟫) := by
  have h := pc_coords hF O P
  have h' := pc_coords hF O Q
  rw [← pc_sub]
  conv_lhs => rw [h, h']
  abel

theorem det3_pts (hF : Fr e1 e2 e3) (O P1 Q1 P2 Q2 P3 Q3 : ℝ³) :
    det3 (P1 - Q1) (P2 - Q2) (P3 - Q3) =
      ((⟪P1 - O, e2⟫ - ⟪Q1 - O, e2⟫) * (⟪P2 - O, e3⟫ - ⟪Q2 - O, e3⟫) -
        (⟪P1 - O, e3⟫ - ⟪Q1 - O, e3⟫) * (⟪P2 - O, e2⟫ - ⟪Q2 - O, e2⟫)) * (⟪P3 - O, e1⟫ - ⟪Q3 - O, e1⟫) +
      ((⟪P1 - O, e3⟫ - ⟪Q1 - O, e3⟫) * (⟪P2 - O, e1⟫ - ⟪Q2 - O, e1⟫) -
        (⟪P1 - O, e1⟫ - ⟪Q1 - O, e1⟫) * (⟪P2 - O, e3⟫ - ⟪Q2 - O, e3⟫)) * (⟪P3 - O, e2⟫ - ⟪Q3 - O, e2⟫) +
      ((⟪P1 - O, e1⟫ - ⟪Q1 - O, e1⟫) * (⟪P2 - O, e2⟫ - ⟪Q2 - O, e2⟫) -
        (⟪P1 - O, e2⟫ - ⟪Q1 - O, e2⟫) * (⟪P2 - O, e1⟫ - ⟪Q2 - O, e1⟫)) * (⟪P3 - O, e3⟫ - ⟪Q3 - O, e3⟫) := by
  rw [vec_pc hF O P1 Q1, vec_pc hF O P2 Q2, vec_pc hF O P3 Q3, det3_pc hF]

end Type08Sp
end Minimality
