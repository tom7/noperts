module

public import Minimality.Type08S.G6B2
public import Minimality.Type08S.G6B3
public import Minimality.Type08S.G6B4
public import Minimality.Type08S.G6B5

@[expose] public section

set_option autoImplicit true

/-!
# G6' bridge, part 6: points in the frame, reflection of points, depth and foot translations
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

theorem sep_aff {ν k : ℝ} (hν : 0 < ν) (x y u v : ℝ) :
    Sep (ν * (x + k)) (ν * (y + k)) (ν * (u + k)) (ν * (v + k)) ↔ Sep x y u v := by
  simp only [Sep, max_le_iff, le_min_iff, mul_le_mul_iff_of_pos_left hν, add_le_add_iff_right]

theorem inner_pt_1 (hF : Fr e1 e2 e3) (o : ℝ³) (X Y z : ℝ) :
    ⟪pt e1 e2 e3 o X Y z, e1⟫ = ⟪o, e1⟫ + X := by
  simp only [pt, pc, inner_add_left, real_inner_smul_left, hF.n11, hF.n12, hF.n13,
    real_inner_comm e1 e2, real_inner_comm e1 e3]
  ring

theorem inner_pt_2 (hF : Fr e1 e2 e3) (o : ℝ³) (X Y z : ℝ) :
    ⟪pt e1 e2 e3 o X Y z, e2⟫ = ⟪o, e2⟫ + Y := by
  simp only [pt, pc, inner_add_left, real_inner_smul_left, hF.n22, hF.n12, hF.n23,
    real_inner_comm e1 e2, real_inner_comm e2 e3]
  ring

theorem inner_pt_3 (hF : Fr e1 e2 e3) (o : ℝ³) (X Y z : ℝ) :
    ⟪pt e1 e2 e3 o X Y z, e3⟫ = ⟪o, e3⟫ + z := by
  simp only [pt, pc, inner_add_left, real_inner_smul_left, hF.n33, hF.n13, hF.n23,
    real_inner_comm e1 e3, real_inner_comm e2 e3]
  ring

/-- The reflection in the plane `⟂ e1` in frame coordinates: `X ↦ -X`. -/
theorem refl_pt (hF : Fr e1 e2 e3) (o : ℝ³) (X Y z : ℝ) :
    pt e1 e2 e3 o X Y z - (2 * ⟪pt e1 e2 e3 o X Y z, e1⟫) • e1 =
      pt e1 e2 e3 (o - (2 * ⟪o, e1⟫) • e1) (-X) Y z := by
  rw [inner_pt_1 hF]
  simp only [pt, pc]
  module

end Type08Sp
end Minimality
