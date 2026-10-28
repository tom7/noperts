module

public import Minimality.Type08S.G6E3
public import Minimality.Type08S.G6H2

@[expose] public section

set_option autoImplicit true

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

theorem ccw4gen {x0 y0 x1 y1 x2 y2 x3 y3 : ℝ}
    (h02 : 0 < (x1 - x0) * (y2 - y0) - (y1 - y0) * (x2 - x0))
    (h03 : 0 < (x1 - x0) * (y3 - y0) - (y1 - y0) * (x3 - x0))
    (h13 : 0 < (x2 - x1) * (y3 - y1) - (y2 - y1) * (x3 - x1))
    (h10 : 0 < (x2 - x1) * (y0 - y1) - (y2 - y1) * (x0 - x1))
    (h20 : 0 < (x3 - x2) * (y0 - y2) - (y3 - y2) * (x0 - x2))
    (h21 : 0 < (x3 - x2) * (y1 - y2) - (y3 - y2) * (x1 - x2))
    (h31 : 0 < (x0 - x3) * (y1 - y3) - (y0 - y3) * (x1 - x3))
    (h32 : 0 < (x0 - x3) * (y2 - y3) - (y0 - y3) * (x2 - x3)) :
    IsCcwPolygon (quad (!₂[x0, y0] : ℝ²) !₂[x1, y1] !₂[x2, y2] !₂[x3, y3]) := by
  refine ⟨by norm_num, fun i j hij hj => ?_⟩
  rcases zmod4_pairs i j hij hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  simp [cross2, quad_0, quad_1, quad_2, quad_3, zmod4_add_one] <;>
  linarith [h02, h03, h13, h10, h20, h21, h31, h32]

end Type08Sp
end Minimality
