module

public import Minimality.Type08S.P2RS1
public import Minimality.Type08S.P2PF3

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# P3a core (frame level), part 1: points in a frame, row formulas, convexity of the screen quadrilateral.

`fpt O X Y z = O + X e1 + Y e2 + z e3`.  The cycle is `quad xx xf xr xg` (`x, f, r, g`), the view
`u₀ = κv e3`, the slide direction `e = c e1` (`c = κ κv`), `ρ = κv`.
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- A point with frame coordinates `(X, Y, z)` about the origin `O`. -/
def fpt (e1 e2 e3 O : ℝ³) (X Y z : ℝ) : ℝ³ := O + pc e1 e2 e3 X Y z

theorem fpt_sub (O : ℝ³) (X Y z X' Y' z' : ℝ) :
    fpt e1 e2 e3 O X Y z - fpt e1 e2 e3 O X' Y' z' = pc e1 e2 e3 (X - X') (Y - Y') (z - z') := by
  simp only [fpt, pc]; module

theorem pc_smul_e3 (hF : Fr e1 e2 e3) (κ : ℝ) : κ • e3 = pc e1 e2 e3 0 0 κ := by
  simp [pc]

theorem pc_smul_e1 (c : ℝ) : c • e1 = pc e1 e2 e3 c 0 0 := by
  simp [pc]

theorem pc_add (X Y z X' Y' z' : ℝ) :
    pc e1 e2 e3 X Y z + pc e1 e2 e3 X' Y' z' = pc e1 e2 e3 (X + X') (Y + Y') (z + z') := by
  simp only [pc]; module

theorem pc_smul (c X Y z : ℝ) :
    c • pc e1 e2 e3 X Y z = pc e1 e2 e3 (c * X) (c * Y) (c * z) := by
  simp only [pc]; module

theorem inner_pc_e1 (hF : Fr e1 e2 e3) (X Y z : ℝ) : ⟪pc e1 e2 e3 X Y z, e1⟫ = X := by
  have := inner_pc hF X Y z 1 0 0
  have h1 : e1 = pc e1 e2 e3 1 0 0 := by simp [pc]
  rw [← h1] at this; rw [this]; ring

theorem inner_pc_e2 (hF : Fr e1 e2 e3) (X Y z : ℝ) : ⟪pc e1 e2 e3 X Y z, e2⟫ = Y := by
  have := inner_pc hF X Y z 0 1 0
  have h1 : e2 = pc e1 e2 e3 0 1 0 := by simp [pc]
  rw [← h1] at this; rw [this]; ring

theorem inner_pc_e3 (hF : Fr e1 e2 e3) (X Y z : ℝ) : ⟪pc e1 e2 e3 X Y z, e3⟫ = z := by
  have := inner_pc hF X Y z 0 0 1
  have h1 : e3 = pc e1 e2 e3 0 0 1 := by simp [pc]
  rw [← h1] at this; rw [this]; ring

end Type08Sp
end Minimality
