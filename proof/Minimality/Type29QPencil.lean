module

public import Minimality.Type29Leaves

@[expose] public section

/-!
# Type 29: Q-pencil algebra (`L1`, `L4`, `L5` of `A26-REFEREE`)

1. `f234_u23Q_sub` (`L4`): `N.f234.f (x 3 + N.u23Q x) - N.f234.f (x 3) = (N.h2 - 1) * N.DG4 * N.D ^ 2`
   (immediate from `f234_u23Q` in `Type29Leaves.lean`).
2. `q_quadrant_II` / `q_quadrant_IV` (`L5`): on weak `OB6` (`⟪x 4 - x 6, x 5 - x 6⟫ ≤ 0`),
   `u4 < 0 < u5` forces `⟪x 4 - x 6, u⟫ < 0 < ⟪x 5 - x 6, u⟫`, and symmetrically `0 < u4`, `u5 < 0`
   forces `⟪x 5 - x 6, u⟫ < 0 < ⟪x 4 - x 6, u⟫`.
3. `qpencil_depth_split` (`L1`): for any view `u = u4 • (x 4 - x 6) + u5 • (x 5 - x 6)` in plane `Q`,
   the depth of `v = α • (x 3 - x 6) + v4 • (x 4 - x 6) + v5 • (x 5 - x 6)` splits as
   `α * (u4 * g34 + u5 * g35) + ⟪v4 • (x 4 - x 6) + v5 • (x 5 - x 6), u⟫`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Minimality Minimality.H21

namespace Minimality.NF29

variable {x : Fin 7 → ℝ³}

/-- `L4`: `f234(x 3 + u23Q) - f234(x 3) = (h2 - 1) * DG4 * D ^ 2`. -/
theorem f234_u23Q_sub (N : NF29 x) :
    N.f234.f (x 3 + N.u23Q x) - N.f234.f (x 3) = (N.h2 - 1) * N.DG4 * N.D ^ 2 := by
  rw [f234_u23Q N]
  ring

/-- `L5` (quadrant II): on weak `OB6`, `u4 < 0 < u5` gives `⟪x4 - x6, u⟫ < 0 < ⟪x5 - x6, u⟫`. -/
theorem q_quadrant_II (x4 x5 x6 : ℝ³) {u4 u5 : ℝ}
    (hx4 : x4 ≠ x6) (hx5 : x5 ≠ x6) (hg45 : ⟪x4 - x6, x5 - x6⟫ ≤ 0)
    (hu4 : u4 < 0) (hu5 : 0 < u5) :
    let u := u4 • (x4 - x6) + u5 • (x5 - x6)
    ⟪x4 - x6, u⟫ < 0 ∧ 0 < ⟪x5 - x6, u⟫ := by
  have h44 : 0 < ⟪x4 - x6, x4 - x6⟫ := real_inner_self_pos.mpr (sub_ne_zero.mpr hx4)
  have h55 : 0 < ⟪x5 - x6, x5 - x6⟫ := real_inner_self_pos.mpr (sub_ne_zero.mpr hx5)
  dsimp
  simp only [inner_add_right, real_inner_smul_right]
  rw [real_inner_comm (x5 - x6) (x4 - x6)]
  constructor
  · linarith [mul_neg_of_neg_of_pos hu4 h44, mul_nonpos_of_nonneg_of_nonpos hu5.le hg45]
  · linarith [mul_nonneg_of_nonpos_of_nonpos hu4.le hg45, mul_pos hu5 h55]

/-- `L5` (quadrant IV): on weak `OB6`, `u5 < 0 < u4` gives `0 < ⟪x4 - x6, u⟫` and `⟪x5 - x6, u⟫ < 0`. -/
theorem q_quadrant_IV (x4 x5 x6 : ℝ³) {u4 u5 : ℝ}
    (hx4 : x4 ≠ x6) (hx5 : x5 ≠ x6) (hg45 : ⟪x4 - x6, x5 - x6⟫ ≤ 0)
    (hu4 : 0 < u4) (hu5 : u5 < 0) :
    let u := u4 • (x4 - x6) + u5 • (x5 - x6)
    0 < ⟪x4 - x6, u⟫ ∧ ⟪x5 - x6, u⟫ < 0 := by
  have h44 : 0 < ⟪x4 - x6, x4 - x6⟫ := real_inner_self_pos.mpr (sub_ne_zero.mpr hx4)
  have h55 : 0 < ⟪x5 - x6, x5 - x6⟫ := real_inner_self_pos.mpr (sub_ne_zero.mpr hx5)
  dsimp
  simp only [inner_add_right, real_inner_smul_right]
  rw [real_inner_comm (x5 - x6) (x4 - x6)]
  constructor
  · linarith [mul_pos hu4 h44, mul_nonneg_of_nonpos_of_nonpos hu5.le hg45]
  · linarith [mul_nonpos_of_nonneg_of_nonpos hu4.le hg45, mul_neg_of_neg_of_pos hu5 h55]

/-- `L1`: Q-pencil depth split for any vector `v` and any Q-plane view `u`. -/
theorem qpencil_depth_split (x3 x4 x5 x6 : ℝ³) (α v4 v5 u4 u5 : ℝ) :
    let v := α • (x3 - x6) + v4 • (x4 - x6) + v5 • (x5 - x6)
    let u := u4 • (x4 - x6) + u5 • (x5 - x6)
    ⟪v, u⟫ = α * (u4 * ⟪x3 - x6, x4 - x6⟫ + u5 * ⟪x3 - x6, x5 - x6⟫) +
      ⟪v4 • (x4 - x6) + v5 • (x5 - x6), u⟫ := by
  dsimp only
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  ring

end Minimality.NF29
