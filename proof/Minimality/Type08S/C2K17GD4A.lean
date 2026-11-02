module

public import Minimality.Type08S.C2K17GD3C

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

set_option maxHeartbeats 3200000 in
/-- Cell C1 (`α4 < 1`, `β6 > 1`): the cone is just `v1 < 0`, `v2 < 0`. -/
theorem k17gdC1b_tsc {α1 β1 β6 v1 v2 : ℝ} (hα1 : 1 < α1) (hβ1 : 0 < β1) (hβ6 : 1 < β6) (hv1 : v1 < 0) (hv2 : v2 < 0) :
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
  have a6 := sub_pos.2 hβ6
  have m1 := mul_pos a6 a2
  have m2 := mul_pos a6 a3
  have m3 := mul_pos (mul_pos a6 a2) hβ1
  have m4 := mul_pos (mul_pos a6 a3) a1
  have m5 := mul_pos (mul_pos a6 a3) hβ1
  have m6 := mul_pos (mul_pos a6 a2) a1
  have m7 := mul_pos a6 a1
  have m8 := mul_pos a6 hβ1
  have m9 := mul_pos (mul_pos a6 a1) a2
  have m10 := mul_pos (mul_pos a6 a1) a3
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
theorem k17gdC1b_rest {α1 β1 β6 α4 γ4 v1 v2 : ℝ} (hα1 : 1 < α1) (hβ1 : 0 < β1) (hβ6 : 1 < β6) (hα4 : 0 < α4)
    (hα41 : α4 < 1) (hγ4 : 0 < γ4) (hv1 : v1 < 0) (hv2 : v2 < 0) :
    (∀ i : ZMod 5, TSc 1 (k17gdC1 α1 β1 β6 (i + 1) - k17gdC1 α1 β1 β6 i) ((0, 0, 1) - k17gdC1 α1 β1 β6 i) (v1, v2, 0)) ∧
    (∀ i : ZMod 5, TSc 1 (k17gdC1 α1 β1 β6 (i + 1) - k17gdC1 α1 β1 β6 i) ((α4, 0, γ4) - k17gdC1 α1 β1 β6 i) (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have a1 := sub_pos.2 hα1
  have a2 := neg_pos.2 hv2
  have a3 := neg_pos.2 hv1
  have k1 := mul_pos a1 a2
  have k2 := mul_pos a1 a3
  have k3 := mul_pos hβ1 a2
  have k4 := mul_pos hβ1 a3
  have k5 := mul_pos a2 a3
  have a6 := sub_pos.2 hβ6
  have m1 := mul_pos a6 a2
  have m2 := mul_pos a6 a3
  have m3 := mul_pos (mul_pos a6 a2) hβ1
  have m4 := mul_pos (mul_pos a6 a3) a1
  have m5 := mul_pos (mul_pos a6 a3) hβ1
  have m6 := mul_pos (mul_pos a6 a2) a1
  have m7 := mul_pos a6 a1
  have m8 := mul_pos a6 hβ1
  have g1 := mul_pos hγ4 a2
  have g2 := mul_pos hγ4 a3
  have g3 := mul_pos (mul_pos hγ4 a2) hβ1
  have g4 := mul_pos (mul_pos hγ4 a3) a1
  have g5 := mul_pos (mul_pos hγ4 a3) hβ1
  have g6 := mul_pos (mul_pos hγ4 a2) a1
  have f1 := sub_pos.2 hα41
  have f2 := mul_pos hα4 a2
  have f3 := mul_pos hα4 a3
  have f4 := mul_pos f1 a2
  have f5 := mul_pos f1 a3
  have f8 := mul_pos (mul_pos f1 hβ1) a2
  have f9 := mul_pos (mul_pos f1 hβ1) a3
  have f6 := mul_pos (mul_pos hγ4 a6) a2
  have f7 := mul_pos (mul_pos hγ4 a6) a3
  constructor <;> intro i <;>
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, k17gdC1, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

/-- Cell D (Ta `α4 < 1`, `⟪b-d,c-d⟫ = 0`, `⟪a-d,b-d⟫ > 0`): ccw pentagon `a, c', b', c, d` in the frame `(p, r, q)`:
`a (1,0,0), c' (α1,0,β1), b' (α4,γ4,0), c (0,1,0), d 0`. -/
def k17gdD (α1 β1 α4 γ4 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ := pc5 (1, 0, 0) (α1, 0, β1) (α4, γ4, 0) (0, 1, 0) (0, 0, 0)

set_option maxHeartbeats 3200000 in
theorem k17gdD_tsc {α1 β1 α4 γ4 v1 v2 : ℝ} (hα1 : 1 < α1) (hβ1 : 0 < β1) (hα4 : 0 < α4) (hα41 : α4 < 1)
    (hγ4 : 1 < γ4) (hv1 : v1 < 0) (hv2 : v2 < 0) (hc : 0 < -(γ4 - 1) * v1 + α4 * v2) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k17gdD α1 β1 α4 γ4 (i + 1) - k17gdD α1 β1 α4 γ4 i) (k17gdD α1 β1 α4 γ4 j - k17gdD α1 β1 α4 γ4 i) (v1, v2, 0) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have a1 := sub_pos.2 hα1
  have a2 := neg_pos.2 hv2
  have a3 := neg_pos.2 hv1
  have a4 := sub_pos.2 hα41
  have a5 := sub_pos.2 hγ4
  have k1 := mul_pos a1 a2
  have k2 := mul_pos a1 a3
  have k3 := mul_pos hβ1 a2
  have k4 := mul_pos hβ1 a3
  have k5 := mul_pos a2 a3
  have k6 := mul_pos hc hβ1
  have k7 := mul_pos hc a1
  have k8 := mul_pos hc a3
  have k9 := mul_pos hc a2
  have h1' := mul_pos hα4 a2
  have h2' := mul_pos hα4 a3
  have h3' := mul_pos a4 a2
  have h4' := mul_pos a4 a3
  have h5' := mul_pos a5 a2
  have h6' := mul_pos a5 a3
  have h7' := mul_pos (mul_pos hβ1 a5) a3
  have h8' := mul_pos (mul_pos hβ1 hα4) a2
  have h9' := mul_pos hc hα4
  have h10' := mul_pos hc a4
  intro i j h1 h2
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2 (by decide)).elim
    | (simp only [TSc, d3, k17gdD, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 3200000 in
theorem k17gdD_rest {α1 β1 α4 γ4 β6 v1 v2 : ℝ} (hα1 : 1 < α1) (hβ1 : 0 < β1) (hα4 : 0 < α4) (hα41 : α4 < 1)
    (hγ4 : 1 < γ4) (hβ6 : 1 < β6) (hv1 : v1 < 0) (hv2 : v2 < 0) (hc : 0 < -(γ4 - 1) * v1 + α4 * v2) :
    (∀ i : ZMod 5, TSc 1 (k17gdD α1 β1 α4 γ4 (i + 1) - k17gdD α1 β1 α4 γ4 i) ((0, 0, 1) - k17gdD α1 β1 α4 γ4 i) (v1, v2, 0)) ∧
    (∀ i : ZMod 5, TSc 1 (k17gdD α1 β1 α4 γ4 (i + 1) - k17gdD α1 β1 α4 γ4 i) ((0, 1, β6) - k17gdD α1 β1 α4 γ4 i) (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have a1 := sub_pos.2 hα1
  have a2 := neg_pos.2 hv2
  have a3 := neg_pos.2 hv1
  have a4 := sub_pos.2 hα41
  have a5 := sub_pos.2 hγ4
  have a6 := sub_pos.2 hβ6
  have k1 := mul_pos a1 a2
  have k2 := mul_pos a1 a3
  have k3 := mul_pos hβ1 a2
  have k4 := mul_pos hβ1 a3
  have k5 := mul_pos a2 a3
  have k6 := mul_pos hc hβ1
  have k7 := mul_pos hc a1
  have k8 := mul_pos hc a3
  have k9 := mul_pos hc a2
  have h1' := mul_pos hα4 a2
  have h2' := mul_pos hα4 a3
  have h3' := mul_pos a4 a2
  have h4' := mul_pos a4 a3
  have h5' := mul_pos a5 a2
  have h6' := mul_pos a5 a3
  have h7' := mul_pos (mul_pos hβ1 a5) a3
  have h8' := mul_pos (mul_pos hβ1 hα4) a2
  have h9' := mul_pos hc hα4
  have h10' := mul_pos hc a4
  have b1 := mul_pos a6 a2
  have b2 := mul_pos a6 a3
  have b3 := mul_pos a6 hc
  have b4 := mul_pos (mul_pos a6 a2) hβ1
  have b5 := mul_pos (mul_pos a6 a3) hβ1
  constructor <;> intro i <;>
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, k17gdD, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
