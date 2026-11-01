module

public import Minimality.Type08S.C2K5AB
public import Minimality.Type08S.C2K2B
public import Minimality.Type08S.C2FC1

@[expose] public section


/-!
# K5a / C: the first cell of QCE2 (`ζ(b,c) < 0`, i.e. `C > B`): pentagon `(a, d, b, a', b')` at `a - d`.
Frame form (`p = b-d, q = c-d, r = a-d`).
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

set_option maxHeartbeats 1600000 in
/-- Tilt tests of the rest point `c' = (1, 0, α1)` against the cycle `kCyc` (it lies over the vertex `b`). -/
theorem k5a_rest1 {D α1 α4 β6 γ6 v1 v2 v3 : ℝ} (hD : 0 < D) (hα1 : 0 < α1) (hβ6 : 0 < β6)
    (hγ6 : 0 < γ6) (hs : 1 < β6 + γ6) (hv2 : v2 < 0) (hc : 0 < γ6 * v1 + (1 - β6) * v2) :
    ∀ i : ZMod 5, TSc D (kCyc β6 γ6 α4 (i + 1) - kCyc β6 γ6 α4 i) ((1, 0, α1) - kCyc β6 γ6 α4 i)
      (v1, v2, v3) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have k1 := hD
  have ks := mul_pos hD (sub_pos.2 hs)
  have kv2 := mul_pos hD (neg_pos.2 hv2)
  have ka := mul_pos (mul_pos hD hα1) hc
  have kb := mul_pos (mul_pos hD hα1) (neg_pos.2 hv2)
  have kc := mul_pos (mul_pos hD hα1) hα1
  intro i
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, kCyc, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
