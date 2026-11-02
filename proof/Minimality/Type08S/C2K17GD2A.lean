module

public import Minimality.Type08S.C2K17GD1

@[expose] public section


set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- Tc `α4 = 1` cell A, ccw pentagon `a (1,0,0), c' (α1,β1,0), a' (0,1,1), c (0,0,1), d 0` in the frame `(p,q,r)`. -/
def k17gdA (α1 β1 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ := pc5 (1, 0, 0) (α1, β1, 0) (0, 1, 1) (0, 0, 1) (0, 0, 0)

set_option maxHeartbeats 3200000 in
theorem k17gdA_tsc {α1 β1 v1 v2 : ℝ} (hα1 : 1 < α1) (hβ1 : 0 < β1) (hv1 : 0 < v1) (hv2 : v2 < 0)
    (hc : 0 < α1 * (-v2) + (β1 - 1) * v1) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k17gdA α1 β1 (i + 1) - k17gdA α1 β1 i) (k17gdA α1 β1 j - k17gdA α1 β1 i) (v1, v2, 0) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have a1 := sub_pos.2 hα1
  have a2 := neg_pos.2 hv2
  have k1 := mul_pos a1 a2
  have k2 := mul_pos a1 hv1
  have k3 := mul_pos hβ1 a2
  have k4 := mul_pos hβ1 hv1
  have k5 := mul_pos a2 hv1
  have k6 := mul_pos hc hβ1
  have k7 := mul_pos hc a1
  have k8 := mul_pos hc hv1
  have k9 := mul_pos hc a2
  intro i j h1 h2'
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2' (by decide)).elim
    | (simp only [TSc, d3, k17gdA, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 3200000 in
theorem k17gdA_rest {α1 β1 γ4 v1 v2 : ℝ} (hα1 : 1 < α1) (hβ1 : 0 < β1) (hγ4 : 0 < γ4) (hv1 : 0 < v1) (hv2 : v2 < 0)
    (hc : 0 < α1 * (-v2) + (β1 - 1) * v1) :
    (∀ i : ZMod 5, TSc 1 (k17gdA α1 β1 (i + 1) - k17gdA α1 β1 i) ((0, 1, 0) - k17gdA α1 β1 i) (v1, v2, 0)) ∧
    (∀ i : ZMod 5, TSc 1 (k17gdA α1 β1 (i + 1) - k17gdA α1 β1 i) ((1, 0, γ4) - k17gdA α1 β1 i) (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have a1 := sub_pos.2 hα1
  have a2 := neg_pos.2 hv2
  have k1 := mul_pos a1 a2
  have k2 := mul_pos a1 hv1
  have k3 := mul_pos hβ1 a2
  have k4 := mul_pos hβ1 hv1
  have k5 := mul_pos a2 hv1
  have k6 := mul_pos hc hβ1
  have k7 := mul_pos hc a1
  have k8 := mul_pos hc hv1
  have k9 := mul_pos hc a2
  have g1 := mul_pos hγ4 a2
  have g2 := mul_pos hγ4 hv1
  have g3 := mul_pos (mul_pos hγ4 a2) hβ1
  have g4 := mul_pos (mul_pos hγ4 hv1) a1
  have g5 := mul_pos (mul_pos hγ4 hv1) hβ1
  have g6 := mul_pos (mul_pos hγ4 a2) a1
  have g7 := mul_pos hγ4 hc
  constructor <;> intro i <;>
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, k17gdA, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
