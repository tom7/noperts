module

public import Minimality.Type08S.C2K17GD2F

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

/-- Ta `α4 = 1`, cell C1, ccw pentagon `a (1,0,0), c' (α1,β1,0), a' (0,β6,1), b (0,1,0), d 0` in the frame `(p,q,r)`. -/
def k17gdC1 (α1 β1 β6 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ := pc5 (1, 0, 0) (α1, β1, 0) (0, β6, 1) (0, 1, 0) (0, 0, 0)

set_option maxHeartbeats 3200000 in
theorem k17gdC1_tsc_gt {α1 β1 v1 v2 : ℝ} {β6 : ℝ} (hα1 : 1 < α1) (hβ1 : 0 < β1) (hβ6 : 1 < β6) (hv1 : v1 < 0) (hv2 : v2 < 0)
    (hc : 0 < -(α1 - 1) * v2 + β1 * v1) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k17gdC1 α1 β1 β6 (i + 1) - k17gdC1 α1 β1 β6 i) (k17gdC1 α1 β1 β6 j - k17gdC1 α1 β1 β6 i) (v1, v2, 0) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have a1 := sub_pos.2 hα1
  have a2 := neg_pos.2 hv2
  have a3 := neg_pos.2 hv1
  have k1 := mul_pos a1 a2
  have k2 := mul_pos a1 a3
  have k3 := mul_pos hβ1 a2
  have k4 := mul_pos hβ1 a3
  have k5 := mul_pos a2 a3
  have k6 := mul_pos hc hβ1
  have k7 := mul_pos hc a1
  have k8 := mul_pos hc a3
  have k9 := mul_pos hc a2
  have a6 := sub_pos.2 hβ6
  have m1 := mul_pos a6 a2
  have m2 := mul_pos a6 a3
  have m3 := mul_pos (mul_pos a6 a2) hβ1
  have m4 := mul_pos (mul_pos a6 a3) a1
  have m5 := mul_pos (mul_pos a6 a3) hβ1
  have m6 := mul_pos (mul_pos a6 a2) a1
  have m7 := mul_pos a6 hc
  intro i j h1 h2'
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2' (by decide)).elim
    | (simp only [TSc, d3, k17gdC1, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 3200000 in
theorem k17gdC1_tsc_eq {α1 β1 v1 v2 : ℝ} (hα1 : 1 < α1) (hβ1 : 0 < β1) (hv1 : v1 < 0) (hv2 : v2 < 0)
    (hc : 0 < -(α1 - 1) * v2 + β1 * v1) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k17gdC1 α1 β1 1 (i + 1) - k17gdC1 α1 β1 1 i) (k17gdC1 α1 β1 1 j - k17gdC1 α1 β1 1 i) (v1, v2, 0) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have a1 := sub_pos.2 hα1
  have a2 := neg_pos.2 hv2
  have a3 := neg_pos.2 hv1
  have k1 := mul_pos a1 a2
  have k2 := mul_pos a1 a3
  have k3 := mul_pos hβ1 a2
  have k4 := mul_pos hβ1 a3
  have k5 := mul_pos a2 a3
  have k6 := mul_pos hc hβ1
  have k7 := mul_pos hc a1
  have k8 := mul_pos hc a3
  have k9 := mul_pos hc a2
  intro i j h1 h2'
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2' (by decide)).elim
    | (simp only [TSc, d3, k17gdC1, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 3200000 in
theorem k17gdC1_rest_gt {α1 β1 γ4 v1 v2 : ℝ} {β6 : ℝ} (hα1 : 1 < α1) (hβ1 : 0 < β1) (hβ6 : 1 < β6) (hγ4 : 0 < γ4)
    (hv1 : v1 < 0) (hv2 : v2 < 0) (hc : 0 < -(α1 - 1) * v2 + β1 * v1) :
    (∀ i : ZMod 5, TSc 1 (k17gdC1 α1 β1 β6 (i + 1) - k17gdC1 α1 β1 β6 i) ((0, 0, 1) - k17gdC1 α1 β1 β6 i) (v1, v2, 0)) ∧
    (∀ i : ZMod 5, TSc 1 (k17gdC1 α1 β1 β6 (i + 1) - k17gdC1 α1 β1 β6 i) ((1, 0, γ4) - k17gdC1 α1 β1 β6 i) (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have a1 := sub_pos.2 hα1
  have a2 := neg_pos.2 hv2
  have a3 := neg_pos.2 hv1
  have k1 := mul_pos a1 a2
  have k2 := mul_pos a1 a3
  have k3 := mul_pos hβ1 a2
  have k4 := mul_pos hβ1 a3
  have k5 := mul_pos a2 a3
  have k6 := mul_pos hc hβ1
  have k7 := mul_pos hc a1
  have k8 := mul_pos hc a3
  have k9 := mul_pos hc a2
  have a6 := sub_pos.2 hβ6
  have m1 := mul_pos a6 a2
  have m2 := mul_pos a6 a3
  have m3 := mul_pos (mul_pos a6 a2) hβ1
  have m4 := mul_pos (mul_pos a6 a3) a1
  have m5 := mul_pos (mul_pos a6 a3) hβ1
  have m6 := mul_pos (mul_pos a6 a2) a1
  have m7 := mul_pos a6 hc
  have g1 := mul_pos hγ4 a2
  have g2 := mul_pos hγ4 a3
  have g3 := mul_pos (mul_pos hγ4 a2) hβ1
  have g4 := mul_pos (mul_pos hγ4 a3) a1
  have g5 := mul_pos (mul_pos hγ4 a3) hβ1
  have g6 := mul_pos (mul_pos hγ4 a2) a1
  have g7 := mul_pos hγ4 hc
  constructor <;> intro i <;>
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, k17gdC1, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 3200000 in
theorem k17gdC1_rest_eq {α1 β1 γ4 v1 v2 : ℝ} (hα1 : 1 < α1) (hβ1 : 0 < β1) (hγ4 : 0 < γ4)
    (hv1 : v1 < 0) (hv2 : v2 < 0) (hc : 0 < -(α1 - 1) * v2 + β1 * v1) :
    (∀ i : ZMod 5, TSc 1 (k17gdC1 α1 β1 1 (i + 1) - k17gdC1 α1 β1 1 i) ((0, 0, 1) - k17gdC1 α1 β1 1 i) (v1, v2, 0)) ∧
    (∀ i : ZMod 5, TSc 1 (k17gdC1 α1 β1 1 (i + 1) - k17gdC1 α1 β1 1 i) ((1, 0, γ4) - k17gdC1 α1 β1 1 i) (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have a1 := sub_pos.2 hα1
  have a2 := neg_pos.2 hv2
  have a3 := neg_pos.2 hv1
  have k1 := mul_pos a1 a2
  have k2 := mul_pos a1 a3
  have k3 := mul_pos hβ1 a2
  have k4 := mul_pos hβ1 a3
  have k5 := mul_pos a2 a3
  have k6 := mul_pos hc hβ1
  have k7 := mul_pos hc a1
  have k8 := mul_pos hc a3
  have k9 := mul_pos hc a2
  have g1 := mul_pos hγ4 a2
  have g2 := mul_pos hγ4 a3
  have g3 := mul_pos (mul_pos hγ4 a2) hβ1
  have g4 := mul_pos (mul_pos hγ4 a3) a1
  have g5 := mul_pos (mul_pos hγ4 a3) hβ1
  have g6 := mul_pos (mul_pos hγ4 a2) a1
  have g7 := mul_pos hγ4 hc
  constructor <;> intro i <;>
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, k17gdC1, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

theorem k17gdC1_tsc {α1 β1 β6 v1 v2 : ℝ} (hα1 : 1 < α1) (hβ1 : 0 < β1) (hβ6 : 1 ≤ β6) (hv1 : v1 < 0) (hv2 : v2 < 0)
    (hc : 0 < -(α1 - 1) * v2 + β1 * v1) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k17gdC1 α1 β1 β6 (i + 1) - k17gdC1 α1 β1 β6 i) (k17gdC1 α1 β1 β6 j - k17gdC1 α1 β1 β6 i) (v1, v2, 0) := by
  rcases hβ6.lt_or_eq with h | h
  · exact k17gdC1_tsc_gt hα1 hβ1 h hv1 hv2 hc
  · subst h; exact k17gdC1_tsc_eq hα1 hβ1 hv1 hv2 hc

theorem k17gdC1_rest {α1 β1 β6 γ4 v1 v2 : ℝ} (hα1 : 1 < α1) (hβ1 : 0 < β1) (hβ6 : 1 ≤ β6) (hγ4 : 0 < γ4)
    (hv1 : v1 < 0) (hv2 : v2 < 0) (hc : 0 < -(α1 - 1) * v2 + β1 * v1) :
    (∀ i : ZMod 5, TSc 1 (k17gdC1 α1 β1 β6 (i + 1) - k17gdC1 α1 β1 β6 i) ((0, 0, 1) - k17gdC1 α1 β1 β6 i) (v1, v2, 0)) ∧
    (∀ i : ZMod 5, TSc 1 (k17gdC1 α1 β1 β6 (i + 1) - k17gdC1 α1 β1 β6 i) ((1, 0, γ4) - k17gdC1 α1 β1 β6 i) (v1, v2, 0)) := by
  rcases hβ6.lt_or_eq with h | h
  · exact k17gdC1_rest_gt hα1 hβ1 h hγ4 hv1 hv2 hc
  · subst h; exact k17gdC1_rest_eq hα1 hβ1 hγ4 hv1 hv2 hc

end C2
end Type08Sp
end Minimality
