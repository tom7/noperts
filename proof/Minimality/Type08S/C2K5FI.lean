module

public import Minimality.Type08S.C2K5FH

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- Box E frame `(p, r, a - c')`: points `a=(1,0,0)`, `c'=(1,0,-1)`, `b=(-m,0,-k)`, `a'=(-t m,1,-t k)`, `b'=(α4,γ4,0)`, `c=(0,1,0)`.
E1 ccw cycle `(a, b', a', b, d)`. -/
def k5fE1Cyc (m k t α4 γ4 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  pc5 (1, 0, 0) (α4, γ4, 0) (-t * m, 1, -t * k) (-m, 0, -k) (0, 0, 0)

set_option maxHeartbeats 1600000 in
theorem k5f_E1_cyc {m k t α4 γ4 v1 v2 : ℝ} (hm : 0 < m) (hk : 0 < k) (ht : 0 < t) (ht1 : t < 1)
    (hα4 : 1 < α4) (hγ4 : 1 < γ4) (hmγ : m * (γ4 - 1) < α4) (hv1 : v1 < 0) (hv2 : 0 < v2) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k5fE1Cyc m k t α4 γ4 (i + 1) - k5fE1Cyc m k t α4 γ4 i)
        (k5fE1Cyc m k t α4 γ4 j - k5fE1Cyc m k t α4 γ4 i) (v1, v2, 0) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have a1 := sub_pos.2 hα4
  have a2 := sub_pos.2 hγ4
  have a3 := sub_pos.2 ht1
  have a4 := mul_pos hm hk
  have a5 := neg_pos.2 hv1
  have g0 : 0 < γ4 := by linarith
  have a7 := mul_pos (mul_pos ht hm) g0
  have a8 := mul_pos ht hm
  have a9 := mul_pos ht hk
  have a10 := mul_pos a5 hv2
  have a11 := mul_pos hv2 g0
  have a12 := mul_pos a5 g0
  have a13 := mul_pos hv2 hk
  have a14 := mul_pos a5 hk
  have a15 := mul_pos hv2 a8
  have a16 := mul_pos a5 a8
  intro i j h1 h2'
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2' (by decide)).elim
    | (simp only [TSc, d3, k5fE1Cyc, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 1600000 in
theorem k5f_E1_rest {m k t α4 γ4 v1 v2 : ℝ} (hm : 0 < m) (hk : 0 < k) (ht : 0 < t) (ht1 : t < 1)
    (hα4 : 1 < α4) (hγ4 : 1 < γ4) (hmγ : m * (γ4 - 1) < α4) (hv1 : v1 < 0) (hv2 : 0 < v2) :
    ∀ t' ∈ [((1, 0, -1) : ℝ × ℝ × ℝ), (0, 1, 0)], ∀ i : ZMod 5,
      TSc 1 (k5fE1Cyc m k t α4 γ4 (i + 1) - k5fE1Cyc m k t α4 γ4 i)
        (t' - k5fE1Cyc m k t α4 γ4 i) (v1, v2, 0) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have a1 := sub_pos.2 hα4
  have a2 := sub_pos.2 hγ4
  have a3 := sub_pos.2 ht1
  have a4 := mul_pos hm hk
  have a5 := neg_pos.2 hv1
  have g0 : 0 < γ4 := by linarith
  have a7 := mul_pos (mul_pos ht hm) g0
  have a8 := mul_pos ht hm
  have a9 := mul_pos ht hk
  have a10 := mul_pos a5 hv2
  have a11 := mul_pos hv2 g0
  have a12 := mul_pos a5 g0
  have a13 := mul_pos hv2 hk
  have a14 := mul_pos a5 hk
  have a15 := mul_pos hv2 a8
  have a16 := mul_pos a5 a8
  intro t' ht' i
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht'
  rcases ht' with rfl | rfl <;>
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, k5fE1Cyc, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

/-- E2 ccw 4-cycle `(c', b', a', b)`. -/
def k5fE2Cyc (m k t α4 γ4 : ℝ) : ZMod 4 → ℝ × ℝ × ℝ :=
  ![(1, 0, -1), (α4, γ4, 0), (-t * m, 1, -t * k), (-m, 0, -k)]

theorem k5fE2Cyc_0 : k5fE2Cyc m k t α4 γ4 0 = (1, 0, -1) := rfl
theorem k5fE2Cyc_1 : k5fE2Cyc m k t α4 γ4 1 = (α4, γ4, 0) := rfl
theorem k5fE2Cyc_2 : k5fE2Cyc m k t α4 γ4 2 = (-t * m, 1, -t * k) := rfl
theorem k5fE2Cyc_3 : k5fE2Cyc m k t α4 γ4 3 = (-m, 0, -k) := rfl

set_option maxHeartbeats 1600000 in
theorem k5f_E2_cyc {m k t α4 γ4 v1 v2 : ℝ} (hm : 0 < m) (hk : 0 < k) (ht : 0 < t) (ht1 : t < 1)
    (hα4 : 1 < α4) (hγ4 : 1 < γ4) (hmγ : m * (γ4 - 1) < α4) (hv1 : 0 < v1) (hv2 : v2 < 0) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      TSc 1 (k5fE2Cyc m k t α4 γ4 (i + 1) - k5fE2Cyc m k t α4 γ4 i)
        (k5fE2Cyc m k t α4 γ4 j - k5fE2Cyc m k t α4 γ4 i) (v1, v2, 0) := by
  obtain ⟨s0, s1, s2, s3⟩ := z4_add
  have a1 := sub_pos.2 hα4
  have a2 := sub_pos.2 hγ4
  have a3 := sub_pos.2 ht1
  have a4 := mul_pos hm hk
  have a5 := neg_pos.2 hv2
  have g0 : 0 < γ4 := by linarith
  have a7 := mul_pos (mul_pos ht hm) g0
  have a8 := mul_pos ht hm
  have a9 := mul_pos ht hk
  have a10 := mul_pos a5 hv1
  have a11 := mul_pos hv1 g0
  have a12 := mul_pos a5 g0
  have a13 := mul_pos hv1 hk
  have a14 := mul_pos a5 hk
  have a15 := mul_pos hv1 a8
  have a16 := mul_pos a5 a8
  intro i j h1 h2'
  rcases z4_cases i with rfl | rfl | rfl | rfl <;>
    rcases z4_cases j with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2' (by decide)).elim
    | (simp only [TSc, d3, k5fE2Cyc_0, k5fE2Cyc_1, k5fE2Cyc_2, k5fE2Cyc_3, s0, s1, s2, s3,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 1600000 in
theorem k5f_E2_rest {m k t α4 γ4 v1 v2 : ℝ} (hm : 0 < m) (hk : 0 < k) (ht : 0 < t) (ht1 : t < 1)
    (hα4 : 1 < α4) (hγ4 : 1 < γ4) (hmγ : m * (γ4 - 1) < α4) (hv1 : 0 < v1) (hv2 : v2 < 0) :
    ∀ t' ∈ [((1, 0, 0) : ℝ × ℝ × ℝ), (0, 0, 0), (0, 1, 0)], ∀ i : ZMod 4,
      TSc 1 (k5fE2Cyc m k t α4 γ4 (i + 1) - k5fE2Cyc m k t α4 γ4 i)
        (t' - k5fE2Cyc m k t α4 γ4 i) (v1, v2, 0) := by
  obtain ⟨s0, s1, s2, s3⟩ := z4_add
  have a1 := sub_pos.2 hα4
  have a2 := sub_pos.2 hγ4
  have a3 := sub_pos.2 ht1
  have a4 := mul_pos hm hk
  have a5 := neg_pos.2 hv2
  have g0 : 0 < γ4 := by linarith
  have a7 := mul_pos (mul_pos ht hm) g0
  have a8 := mul_pos ht hm
  have a9 := mul_pos ht hk
  have a10 := mul_pos a5 hv1
  have a11 := mul_pos hv1 g0
  have a12 := mul_pos a5 g0
  have a13 := mul_pos hv1 hk
  have a14 := mul_pos a5 hk
  have a15 := mul_pos hv1 a8
  have a16 := mul_pos a5 a8
  intro t' ht' i
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht'
  rcases ht' with rfl | rfl | rfl <;>
  rcases z4_cases i with rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, k5fE2Cyc_0, k5fE2Cyc_1, k5fE2Cyc_2, k5fE2Cyc_3, s0, s1, s2, s3,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
