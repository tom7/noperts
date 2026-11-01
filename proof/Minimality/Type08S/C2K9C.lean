module

public import Minimality.Type08S.C2K8J
public import Minimality.Type08S.C2K9B

@[expose] public section

/-!
# K9C: `TSc` tables for the cycles `k9Y1 = (b, d, c, b', c')` (cone `v1 > 0 > v2`) and
`k9Y2 = (a, d, c, b', c')` (cone `v1, v2 < 0`) at the view `b - d`; rest points `a`, `a'` (and `b` for `Y2`).
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

def k9Y1 (γ4 β1 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ := pc5 (0, 0, 1) (0, 0, 0) (1, 0, 0) (γ4, 1, 0) (0, 1, β1)
def k9Y2 (γ4 β1 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ := pc5 (0, 1, 0) (0, 0, 0) (1, 0, 0) (γ4, 1, 0) (0, 1, β1)

theorem k9Y1_inj {γ4 β1 : ℝ} (hγ4 : 0 < γ4) (hβ1 : 0 < β1) :
    ∀ i j, k9Y1 γ4 β1 i = k9Y1 γ4 β1 j → i = j := by
  intro i j h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [k9Y1, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith) | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; linarith)

theorem k9Y2_inj {γ4 β1 : ℝ} (hγ4 : 0 < γ4) (hβ1 : 0 < β1) :
    ∀ i j, k9Y2 γ4 β1 i = k9Y2 γ4 β1 j → i = j := by
  intro i j h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [k9Y2, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith) | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; linarith)

set_option maxHeartbeats 3200000 in
theorem k9_cyc1 {D γ4 β1 v1 v2 v3 : ℝ} (hD : 0 < D) (hγ4 : 0 < γ4) (hβ1 : 0 < β1)
    (hv1 : 0 < v1) (hv2 : v2 < 0) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc D (k9Y1 γ4 β1 (i + 1) - k9Y1 γ4 β1 i) (k9Y1 γ4 β1 j - k9Y1 γ4 β1 i) (v1, v2, v3) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add_one
  have hw : 0 < -v2 := by linarith
  have k1 := hD
  have kg4 := mul_pos hD hγ4
  have kb1 := mul_pos hD hβ1
  have kv1 := mul_pos hD hv1
  have kw := mul_pos hD hw
  have kg4v1 := mul_pos (mul_pos hD hγ4) hv1
  have kg4w := mul_pos (mul_pos hD hγ4) hw
  have kb1v1 := mul_pos (mul_pos hD hβ1) hv1
  have kb1w := mul_pos (mul_pos hD hβ1) hw
  intro i j h1 h2'
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2' (by decide)).elim
    | (simp only [TSc, d3, k9Y1, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 3200000 in
theorem k9_rest1_a {D γ4 β1 v1 v2 v3 : ℝ} (hD : 0 < D) (hγ4 : 0 < γ4) (hβ1 : 0 < β1)
    (hv1 : 0 < v1) (hv2 : v2 < 0) :
    ∀ i : ZMod 5, TSc D (k9Y1 γ4 β1 (i + 1) - k9Y1 γ4 β1 i) ((0, 1, 0) - k9Y1 γ4 β1 i) (v1, v2, v3) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add_one
  have hw : 0 < -v2 := by linarith
  have k1 := hD
  have kg4 := mul_pos hD hγ4
  have kb1 := mul_pos hD hβ1
  have kv1 := mul_pos hD hv1
  have kw := mul_pos hD hw
  have kg4v1 := mul_pos (mul_pos hD hγ4) hv1
  have kg4w := mul_pos (mul_pos hD hγ4) hw
  have kb1v1 := mul_pos (mul_pos hD hβ1) hv1
  have kb1w := mul_pos (mul_pos hD hβ1) hw
  intro i
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, k9Y1, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 3200000 in
theorem k9_rest1_a' {D γ4 β1 γ6 β6 v1 v2 v3 : ℝ} (hD : 0 < D) (hγ4 : 0 < γ4) (hβ1 : 0 < β1)
    (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hβ6 : 0 < β6) (hv1 : 0 < v1) (hv2 : v2 < 0) :
    ∀ i : ZMod 5, TSc D (k9Y1 γ4 β1 (i + 1) - k9Y1 γ4 β1 i) ((γ6, 0, β6) - k9Y1 γ4 β1 i) (v1, v2, v3) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add_one
  have hw : 0 < -v2 := by linarith
  have hg61 : 0 < 1 - γ6 := by linarith
  have k1 := hD
  have kg4 := mul_pos hD hγ4
  have kb1 := mul_pos hD hβ1
  have kg6 := mul_pos hD hγ6
  have kg61 := mul_pos hD hg61
  have kv1 := mul_pos hD hv1
  have kw := mul_pos hD hw
  have kg4v1 := mul_pos (mul_pos hD hγ4) hv1
  have kg4w := mul_pos (mul_pos hD hγ4) hw
  have kb1v1 := mul_pos (mul_pos hD hβ1) hv1
  have kb1w := mul_pos (mul_pos hD hβ1) hw
  have kg6w := mul_pos (mul_pos hD hγ6) hw
  have kg6v1 := mul_pos (mul_pos hD hγ6) hv1
  have kb6w := mul_pos (mul_pos hD hβ6) hw
  have kb6v1 := mul_pos (mul_pos hD hβ6) hv1
  intro i
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, k9Y1, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 3200000 in
theorem k9_cyc2 {D γ4 β1 v1 v2 v3 : ℝ} (hD : 0 < D) (hγ4 : 0 < γ4) (hβ1 : 0 < β1)
    (hv1 : v1 < 0) (hv2 : v2 < 0) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc D (k9Y2 γ4 β1 (i + 1) - k9Y2 γ4 β1 i) (k9Y2 γ4 β1 j - k9Y2 γ4 β1 i) (v1, v2, v3) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add_one
  have hw : 0 < -v2 := by linarith
  have hu : 0 < -v1 := by linarith
  have k1 := hD
  have kg4 := mul_pos hD hγ4
  have kb1 := mul_pos hD hβ1
  have ku := mul_pos hD hu
  have kw := mul_pos hD hw
  have kg4u := mul_pos (mul_pos hD hγ4) hu
  have kg4w := mul_pos (mul_pos hD hγ4) hw
  have kb1u := mul_pos (mul_pos hD hβ1) hu
  have kb1w := mul_pos (mul_pos hD hβ1) hw
  intro i j h1 h2'
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2' (by decide)).elim
    | (simp only [TSc, d3, k9Y2, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 3200000 in
theorem k9_rest2_b {D γ4 β1 v1 v2 v3 : ℝ} (hD : 0 < D) (hγ4 : 0 < γ4) (hβ1 : 0 < β1)
    (hv1 : v1 < 0) (hv2 : v2 < 0) :
    ∀ i : ZMod 5, TSc D (k9Y2 γ4 β1 (i + 1) - k9Y2 γ4 β1 i) ((0, 0, 1) - k9Y2 γ4 β1 i) (v1, v2, v3) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add_one
  have hw : 0 < -v2 := by linarith
  have hu : 0 < -v1 := by linarith
  have k1 := hD
  have kg4 := mul_pos hD hγ4
  have kb1 := mul_pos hD hβ1
  have ku := mul_pos hD hu
  have kw := mul_pos hD hw
  have kg4u := mul_pos (mul_pos hD hγ4) hu
  have kg4w := mul_pos (mul_pos hD hγ4) hw
  have kb1u := mul_pos (mul_pos hD hβ1) hu
  have kb1w := mul_pos (mul_pos hD hβ1) hw
  intro i
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, k9Y2, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 3200000 in
theorem k9_rest2_a' {D γ4 β1 γ6 β6 v1 v2 v3 : ℝ} (hD : 0 < D) (hγ4 : 0 < γ4) (hβ1 : 0 < β1)
    (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hβ6 : 0 < β6) (hv1 : v1 < 0) (hv2 : v2 < 0) :
    ∀ i : ZMod 5, TSc D (k9Y2 γ4 β1 (i + 1) - k9Y2 γ4 β1 i) ((γ6, 0, β6) - k9Y2 γ4 β1 i) (v1, v2, v3) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add_one
  have hw : 0 < -v2 := by linarith
  have hu : 0 < -v1 := by linarith
  have hg61 : 0 < 1 - γ6 := by linarith
  have k1 := hD
  have kg4 := mul_pos hD hγ4
  have kb1 := mul_pos hD hβ1
  have kg6 := mul_pos hD hγ6
  have kg61 := mul_pos hD hg61
  have ku := mul_pos hD hu
  have kw := mul_pos hD hw
  have kg4u := mul_pos (mul_pos hD hγ4) hu
  have kg4w := mul_pos (mul_pos hD hγ4) hw
  have kb1u := mul_pos (mul_pos hD hβ1) hu
  have kb1w := mul_pos (mul_pos hD hβ1) hw
  have kg6w := mul_pos (mul_pos hD hγ6) hw
  have kg6u := mul_pos (mul_pos hD hγ6) hu
  have kb6w := mul_pos (mul_pos hD hβ6) hw
  have kb6u := mul_pos (mul_pos hD hβ6) hu
  intro i
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, k9Y2, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
