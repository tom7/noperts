module

public import Minimality.Type08S.G6E1

@[expose] public section

set_option autoImplicit true

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

theorem ccw4 {p r q1 q2 s t : ℝ} (hh : s < t) (hpr : r < p) (hq : q2 < q1) :
    IsCcwPolygon (quad (!₂[p, s] : ℝ²) !₂[q1, t] !₂[q2, t] !₂[r, s]) := by
  have hh' : 0 < t - s := sub_pos.mpr hh
  refine ⟨by norm_num, fun i j hij hj => ?_⟩
  rcases zmod4_pairs i j hij hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  simp [cross2, quad_0, quad_1, quad_2, quad_3, zmod4_add_one] <;>
  nlinarith [mul_pos hh' (sub_pos.mpr hpr), mul_pos hh' (sub_pos.mpr hq)]

theorem sep_comm' (x y u v : ℝ) : Sep x y u v ↔ Sep u v x y := by unfold Sep; tauto
theorem sep_swap (x y u v : ℝ) : Sep x y u v ↔ Sep x y v u := by
  simp only [Sep, max_comm u v, min_comm u v]
theorem sep_shift (k x y u v : ℝ) : Sep (k + x) (k + y) (k + u) (k + v) ↔ Sep x y u v := by
  simp only [Sep, max_add_add_left, min_add_add_left, add_le_add_iff_left]

end Type08Sp
end Minimality
