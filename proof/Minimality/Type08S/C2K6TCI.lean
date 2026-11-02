module

public import Minimality.Type08S.C2K6TCH

@[expose] public section

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

/-- Pc leaf 2 cycle `(a, c', b', c, d)` (counterclockwise) in the frame of leaf 1. -/
def k6t3_pcY (g e : ℝ) : ZMod 5 → ℝ × ℝ × ℝ := ![(1, 0, 0), (1, e, 0), (1, g, g), (0, 1, 1), (0, 0, 0)]

theorem k6t3_pcY_0 : k6t3_pcY g e 0 = (1, 0, 0) := rfl
theorem k6t3_pcY_1 : k6t3_pcY g e 1 = (1, e, 0) := rfl
theorem k6t3_pcY_2 : k6t3_pcY g e 2 = (1, g, g) := rfl
theorem k6t3_pcY_3 : k6t3_pcY g e 3 = (0, 1, 1) := rfl
theorem k6t3_pcY_4 : k6t3_pcY g e 4 = (0, 0, 0) := rfl

set_option maxHeartbeats 6400000 in
/-- Tilt test of the Pc leaf-2 pentagon, cone `0 < v1`, `v2 + (1 - g) v1 < 0`. -/
theorem k6t3_pc2_tsc {m g e v1 v2 : ℝ} (hm : 0 < m) (hm1 : m < 1) (hg : 0 < g) (he : 0 < e) (heg : e < g)
    (hv1 : 0 < v1) (hv2 : v2 + (1 - g) * v1 < 0) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k6t3_pcY g e (i + 1) - k6t3_pcY g e i) (k6t3_pcY g e j - k6t3_pcY g e i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (1 : ℝ), 1 - m), (0, m, 0)], ∀ i : ZMod 5,
      TSc 1 (k6t3_pcY g e (i + 1) - k6t3_pcY g e i) (t - k6t3_pcY g e i) (v1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  have nv := neg_pos.2 hv2
  have g1 : 0 < 1 - m := by linarith
  have k1 := mul_pos hg he
  have k2 := mul_pos (mul_pos hg he) hv1
  have k3 := mul_pos hm hv1
  have k5 := mul_pos hm nv
  have k6 := mul_pos hm g1
  have k7 := mul_pos hg hv1
  have k8 := mul_pos hg hm
  have k9 := sub_pos.2 heg
  have k10 := mul_pos he hv1
  constructor
  · intro i j h1 h2
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k6t3_pcY_0, k6t3_pcY_1, k6t3_pcY_2, k6t3_pcY_3, k6t3_pcY_4, f0, f1, f2, f3, f4, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k6t3_pcY_0, k6t3_pcY_1, k6t3_pcY_2, k6t3_pcY_3, k6t3_pcY_4, f0, f1, f2, f3, f4, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 6400000 in
/-- Lex part of the Pc leaf-2 pentagon (depth only): `u ≤ 0`, `0 ≤ t + A`. Depths: `a = u`, `c' = u + e t`,
`b' = u + g t + g A`, `c = t + A`, `d = 0`. -/
theorem k6t3_pc2_real {g e k0 U T B u t A : ℝ} (hg : 0 < g) (he : 0 < e) (heg : e < g) (hA : 0 < A)
    (hu : u < 0) (hw : 0 ≤ t + A)
    (hdep : ∀ i j : ZMod 5,
      k0 + (k6t3_pcY g e i).1 * U + (k6t3_pcY g e i).2.1 * T + (k6t3_pcY g e i).2.2 * B <
      k0 + (k6t3_pcY g e j).1 * U + (k6t3_pcY g e j).2.1 * T + (k6t3_pcY g e j).2.2 * B →
      (k6t3_pcY g e i).1 * u + (k6t3_pcY g e i).2.1 * t + (k6t3_pcY g e i).2.2 * A ≤
      (k6t3_pcY g e j).1 * u + (k6t3_pcY g e j).2.1 * t + (k6t3_pcY g e j).2.2 * A)
    (hinj : ∀ i j, k0 + (k6t3_pcY g e i).1 * U + (k6t3_pcY g e i).2.1 * T + (k6t3_pcY g e i).2.2 * B =
      k0 + (k6t3_pcY g e j).1 * U + (k6t3_pcY g e j).2.1 * T + (k6t3_pcY g e j).2.2 * B → i = j) :
    LexUni (fun _ => (0 : ℝ))
      (fun i => k0 + (k6t3_pcY g e i).1 * U + (k6t3_pcY g e i).2.1 * T + (k6t3_pcY g e i).2.2 * B) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  obtain ⟨s0, s1, s2, s3, s4⟩ := k5d_z5_sub
  refine k5d_uni_of_nopair (by decide) _ hinj ?_
  intro i j h1 h2 h3
  have p1 := mul_pos hg hA
  have p2 := mul_pos he hA
  rintro ⟨⟨h5, h6⟩, h7, h8⟩
  have d5 := hdep _ _ h5
  have d6 := hdep _ _ h6
  have d7 := hdep _ _ h7
  have d8 := hdep _ _ h8
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2 (by decide)).elim
    | exact (h3 (by decide)).elim
    | (simp only [k6t3_pcY_0, k6t3_pcY_1, k6t3_pcY_2, k6t3_pcY_3, k6t3_pcY_4, f0, f1, f2, f3, f4, s0, s1, s2, s3, s4] at d5 d6 d7 d8
       first
       | nlinarith
       | (rcases le_total 0 t with ht | ht
          · nlinarith [mul_nonneg he.le ht, mul_nonneg (sub_nonneg.2 heg.le) ht, mul_nonneg hg.le ht,
              mul_nonneg (sub_nonneg.2 heg.le) hw, mul_nonneg hg.le hw, mul_nonneg he.le hw,
              mul_nonneg (sub_nonneg.2 heg.le) (neg_nonneg.2 hu), mul_nonneg he.le (neg_nonneg.2 hu), mul_nonneg hg.le (neg_nonneg.2 hu)]
          · nlinarith [mul_nonneg he.le (neg_nonneg.2 ht), mul_nonneg (sub_nonneg.2 heg.le) (neg_nonneg.2 ht), mul_nonneg hg.le (neg_nonneg.2 ht),
              mul_nonneg (sub_nonneg.2 heg.le) hw, mul_nonneg hg.le hw, mul_nonneg he.le hw,
              mul_nonneg (sub_nonneg.2 heg.le) (neg_nonneg.2 hu), mul_nonneg he.le (neg_nonneg.2 hu), mul_nonneg hg.le (neg_nonneg.2 hu)]))

end C2
end Type08Sp
end Minimality
