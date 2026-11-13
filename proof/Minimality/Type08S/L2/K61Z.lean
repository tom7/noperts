module

public import Minimality.Type08S.L2.K61A
public import Minimality.Type08S.L2.K61LexA
public import Minimality.Type08S.L2.K61LexAp
public import Minimality.Type08S.L2.K61LexB
public import Minimality.Type08S.L2.K61LexC
public import Minimality.Type08S.L2.K61LexD
public import Minimality.Type08S.L2.K61LexD0

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace
namespace Minimality.Type08Sp.C2

/-- The screen parameter of the K61 view `D:a'b' × P:abd`: `lam = -⟪b-d, a'-b'⟫ / ⟪a-d, a'-b'⟫`. -/
noncomputable def k61_lam (a a' b b' d : ℝ³) : ℝ := -⟪b - d, a' - b'⟫ / ⟪a - d, a' - b'⟫

/-- The depth direction `R = (b-d) + lam (a-d)` (so `⟪R, a'-b'⟫ = 0`). -/
noncomputable def k61_R (a a' b b' d : ℝ³) : ℝ³ := (b - d) + k61_lam a a' b b' d • (a - d)

theorem k61_tie {a a' b b' d : ℝ³} (hAv : ⟪a - d, a' - b'⟫ ≠ 0) :
    ⟪a' - b', k61_R a a' b b' d⟫ = 0 := by
  unfold k61_R k61_lam
  rw [inner_add_right, inner_smul_right, real_inner_comm (b - d) (a' - b'), real_inner_comm (a - d) (a' - b')]
  field_simp
  ring

end Minimality.Type08Sp.C2
