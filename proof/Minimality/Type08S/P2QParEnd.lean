module

public import Minimality.Type08S.P2H3

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# The `ParEnd` definitions (persistent HDN with a top side parallel to the face)

Split out of `P2QDefs` so that the weak (`Norm08w`) closing files `P2QWP2H13` ... can use them before
the `P2FinalH` chain (which imports their `Norm08` wrappers).
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- Frame numbers of a persistent HDN with a top side parallel to the face (`Yr = Yg`) over the chord's line
(`Par5`) or over `f̄` (`CEf5`). -/
def ParEnd5 (L zx zf Xr Yr zr Xg Yg zg : ℝ) : Prop :=
  Yr = Yg ∧ (CEf5 L zx zf Xr Yr zr Xg Yg zg ∨ Par5 L zx zf Xr Yr zr Xg Yg zg)

/-- `ParEnd5` for N2's `K_c` in the canonical frame of `SC2N2` (`x' = a'`, `x = c`, `f = b`, `r = c'`, `g = b'`). -/
def ParEndN2 (a a' b b' c c' : ℝ³) : Prop :=
  ∃ (e1 e2 e3 : ℝ³) (κ : ℝ), Fr e1 e2 e3 ∧ κ ≠ 0 ∧ c - a' = κ • e3 ∧ ⟪b - a', e2⟫ = 0 ∧
    0 < ⟪b - a', e1⟫ ∧ 0 < ⟪c' - a', e2⟫ ∧ Rob4 κ ⟪b - a', e3⟫ ⟪c' - a', e3⟫ ⟪b' - a', e3⟫ ∧
    ParEnd5 ⟪b - a', e1⟫ κ ⟪b - a', e3⟫ ⟪c' - a', e1⟫ ⟪c' - a', e2⟫ ⟪c' - a', e3⟫ ⟪b' - a', e1⟫ ⟪b' - a', e2⟫
      ⟪b' - a', e3⟫

/-- `ParEnd5` for T4's `K_b` in the canonical frame of `SC2Kb` (`x' = d`, `x = b`, `f = c`, `r = b'`, `g = c'`). -/
def ParEndKb (b b' c c' d : ℝ³) : Prop :=
  ∃ (e1 e2 e3 : ℝ³) (κ : ℝ), Fr e1 e2 e3 ∧ κ ≠ 0 ∧ b - d = κ • e3 ∧ ⟪c - d, e2⟫ = 0 ∧
    0 < ⟪c - d, e1⟫ ∧ 0 < ⟪b' - d, e2⟫ ∧ Rob4 κ ⟪c - d, e3⟫ ⟪b' - d, e3⟫ ⟪c' - d, e3⟫ ∧
    ParEnd5 ⟪c - d, e1⟫ κ ⟪c - d, e3⟫ ⟪b' - d, e1⟫ ⟪b' - d, e2⟫ ⟪b' - d, e3⟫ ⟪c' - d, e1⟫ ⟪c' - d, e2⟫
      ⟪c' - d, e3⟫

/-- `ParEnd5` for T4's `K_2` in the canonical frame of `SC2K2` (`x' = b`, `x = d`, `f = c'`, `r = b'`, `g = c`). -/
def ParEndK2 (b b' c c' d : ℝ³) : Prop :=
  ∃ (e1 e2 e3 : ℝ³) (κ : ℝ), Fr e1 e2 e3 ∧ κ ≠ 0 ∧ d - b = κ • e3 ∧ ⟪c' - b, e2⟫ = 0 ∧
    0 < ⟪c' - b, e1⟫ ∧ 0 < ⟪b' - b, e2⟫ ∧ Rob4 κ ⟪c' - b, e3⟫ ⟪b' - b, e3⟫ ⟪c - b, e3⟫ ∧
    ParEnd5 ⟪c' - b, e1⟫ κ ⟪c' - b, e3⟫ ⟪b' - b, e1⟫ ⟪b' - b, e2⟫ ⟪b' - b, e3⟫ ⟪c - b, e1⟫ ⟪c - b, e2⟫
      ⟪c - b, e3⟫

/-- **`ParEnd`** (one of the three closings).  Used with `κ_a = 0` (`det3 (c - b) (b' - b) (c' - b) = 0`). -/
def ParEnd (a a' b b' c c' d : ℝ³) : Prop :=
  ParEndN2 a a' b b' c c' ∨ ParEndKb b b' c c' d ∨ ParEndK2 b b' c c' d

/-- `ParEnd`, each disjunct recorded together with the facet region under which the pipeline excludes it
(`RegN2` for `ParEndN2`, the strict T4 region `RegT4` for `ParEndKb`, `ParEndK2`). -/
def ParEndR {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c') (d : ℝ³) : Prop :=
  (RegN2 F ∧ ParEndN2 a a' b b' c c') ∨ (RegT4 F ∧ ParEndKb b b' c c' d) ∨ (RegT4 F ∧ ParEndK2 b b' c c' d)

end Type08Sp
end Minimality
