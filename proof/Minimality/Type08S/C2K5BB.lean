module

public import Minimality.Type08S.C2K5BA
public import Minimality.Type08S.C2K2B
public import Minimality.Type08S.C2FC1

@[expose] public section


/-!
# K5b / B: tilt tests of the two cells at the view `b - c` (frame `p = a-d`, `q = c-d`, `r = b-c`).
Screen `(x,y)`: `d = (0,0)`, `a = (1,0)`, `c ≡ b = (0,1)`, `b' ≡ c' = (α1,β1)`, `a' = (0,s)`, `s = β6+γ6`.
Frame points: `a=(1,0,0)`, `d=0`, `c=(0,1,0)`, `b=(0,1,1)`, `b'=(α1,β1,0)`, `c'=(α1,β1,β1)`, `a'=(0,s,β6)`.
Cell 1: ccw cycle `(a, b', a', b, d)` (tilt `v1 > 0`); cell 2: `(a, c', a', c, d)` (tilt `v1 < 0`).
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- Cell 1: ccw cycle `(a, b', a', b, d)`. -/
def k5b_cyc1 (α1 β1 β6 γ6 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  pc5 (1, 0, 0) (α1, β1, 0) (0, β6 + γ6, β6) (0, 1, 1) (0, 0, 0)

/-- Cell 2: ccw cycle `(a, c', a', c, d)`. -/
def k5b_cyc2 (α1 β1 β6 γ6 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  pc5 (1, 0, 0) (α1, β1, β1) (0, β6 + γ6, β6) (0, 1, 0) (0, 0, 0)

set_option maxHeartbeats 3200000 in
theorem k5b_cyc1_tsc {D α1 β1 β6 γ6 v1 v2 : ℝ} (hD : 0 < D) (hα1 : 0 < α1) (hβ1 : 0 < β1) (hβ6 : 0 < β6)
    (hγ6 : 0 < γ6) (hs : 1 < β6 + γ6) (hab : 1 < α1 + β1) (hcond : 0 < (α1 - 1) * (β6 + γ6) + β1)
    (hv1 : 0 < v1) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc D (k5b_cyc1 α1 β1 β6 γ6 (i + 1) - k5b_cyc1 α1 β1 β6 γ6 i)
        (k5b_cyc1 α1 β1 β6 γ6 j - k5b_cyc1 α1 β1 β6 γ6 i) (v1, v2, 0) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have k1 := hD
  have ka := mul_pos hD hα1
  have kb := mul_pos hD hβ1
  have kg := mul_pos hD hγ6
  have ks := mul_pos hD (sub_pos.2 hs)
  have kab := mul_pos hD (sub_pos.2 hab)
  have kc := mul_pos hD hcond
  have kas := mul_pos (mul_pos hD hα1) (sub_pos.2 hs)
  have kas' := mul_pos (mul_pos hD hα1) (add_pos hβ6 hγ6)
  have kgv := mul_pos (mul_pos hD hγ6) hv1
  have ksv := mul_pos (mul_pos hD (sub_pos.2 hs)) hv1
  intro i j h1 h2'
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2' (by decide)).elim
    | (simp only [TSc, d3, k5b_cyc1, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 3200000 in
theorem k5b_rest1_tsc {D α1 β1 β6 γ6 v1 v2 : ℝ} (hD : 0 < D) (hα1 : 0 < α1) (hβ1 : 0 < β1) (hβ6 : 0 < β6)
    (hγ6 : 0 < γ6) (hs : 1 < β6 + γ6) (hab : 1 < α1 + β1)
    (hv1 : 0 < v1) (hc1 : 0 < β1 * v1 - (α1 - 1) * v2) (hc2 : 0 < (β6 + γ6 - β1) * v1 + α1 * v2) :
    (∀ i : ZMod 5, TSc D (k5b_cyc1 α1 β1 β6 γ6 (i + 1) - k5b_cyc1 α1 β1 β6 γ6 i)
        ((0, 1, 0) - k5b_cyc1 α1 β1 β6 γ6 i) (v1, v2, 0)) ∧
    (∀ i : ZMod 5, TSc D (k5b_cyc1 α1 β1 β6 γ6 (i + 1) - k5b_cyc1 α1 β1 β6 γ6 i)
        ((α1, β1, β1) - k5b_cyc1 α1 β1 β6 γ6 i) (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have k1 := hD
  have ka := mul_pos hD hα1
  have kb := mul_pos hD hβ1
  have ks := mul_pos hD (sub_pos.2 hs)
  have kab := mul_pos hD (sub_pos.2 hab)
  have kas := mul_pos (mul_pos hD hα1) (sub_pos.2 hs)
  have ksv := mul_pos (mul_pos hD (sub_pos.2 hs)) hv1
  have kc1 := mul_pos (mul_pos hD hβ1) hc1
  have kc2 := mul_pos (mul_pos hD hβ1) hc2
  refine ⟨?_, ?_⟩ <;> intro i <;>
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, k5b_cyc1, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 3200000 in
theorem k5b_cyc2_tsc {D α1 β1 β6 γ6 v1 v2 : ℝ} (hD : 0 < D) (hα1 : 0 < α1) (hβ1 : 0 < β1) (hβ6 : 0 < β6)
    (hγ6 : 0 < γ6) (hs : 1 < β6 + γ6) (hab : 1 < α1 + β1) (hcond : 0 < (α1 - 1) * (β6 + γ6) + β1)
    (hv1 : v1 < 0) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc D (k5b_cyc2 α1 β1 β6 γ6 (i + 1) - k5b_cyc2 α1 β1 β6 γ6 i)
        (k5b_cyc2 α1 β1 β6 γ6 j - k5b_cyc2 α1 β1 β6 γ6 i) (v1, v2, 0) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have k1 := hD
  have ka := mul_pos hD hα1
  have kb := mul_pos hD hβ1
  have kg := mul_pos hD hγ6
  have kb6 := mul_pos hD hβ6
  have ks := mul_pos hD (sub_pos.2 hs)
  have kab := mul_pos hD (sub_pos.2 hab)
  have kc := mul_pos hD hcond
  have kas := mul_pos (mul_pos hD hα1) (sub_pos.2 hs)
  have kas' := mul_pos (mul_pos hD hα1) (add_pos hβ6 hγ6)
  have kgv := mul_pos (mul_pos hD hγ6) (neg_pos.2 hv1)
  have kb6v := mul_pos (mul_pos hD hβ6) (neg_pos.2 hv1)
  have ksv := mul_pos (mul_pos hD (sub_pos.2 hs)) (neg_pos.2 hv1)
  intro i j h1 h2'
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2' (by decide)).elim
    | (simp only [TSc, d3, k5b_cyc2, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 3200000 in
theorem k5b_rest2_tsc {D α1 β1 β6 γ6 v1 v2 : ℝ} (hD : 0 < D) (hα1 : 0 < α1) (hβ1 : 0 < β1) (hβ6 : 0 < β6)
    (hγ6 : 0 < γ6) (hs : 1 < β6 + γ6) (hab : 1 < α1 + β1)
    (hv1 : v1 < 0) (hc1 : 0 < -β1 * v1 + (α1 - 1) * v2) (hc2 : 0 < -(β6 + γ6 - β1) * v1 - α1 * v2) :
    (∀ i : ZMod 5, TSc D (k5b_cyc2 α1 β1 β6 γ6 (i + 1) - k5b_cyc2 α1 β1 β6 γ6 i)
        ((0, 1, 1) - k5b_cyc2 α1 β1 β6 γ6 i) (v1, v2, 0)) ∧
    (∀ i : ZMod 5, TSc D (k5b_cyc2 α1 β1 β6 γ6 (i + 1) - k5b_cyc2 α1 β1 β6 γ6 i)
        ((α1, β1, 0) - k5b_cyc2 α1 β1 β6 γ6 i) (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have k1 := hD
  have ka := mul_pos hD hα1
  have kb := mul_pos hD hβ1
  have ks := mul_pos hD (sub_pos.2 hs)
  have kab := mul_pos hD (sub_pos.2 hab)
  have kas := mul_pos (mul_pos hD hα1) (sub_pos.2 hs)
  have ksv := mul_pos (mul_pos hD (sub_pos.2 hs)) (neg_pos.2 hv1)
  have kc1 := mul_pos (mul_pos hD hβ1) hc1
  have kc2 := mul_pos (mul_pos hD hβ1) hc2
  have kbv := mul_pos (mul_pos hD hβ1) (neg_pos.2 hv1)
  refine ⟨?_, ?_⟩ <;> intro i <;>
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, k5b_cyc2, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
