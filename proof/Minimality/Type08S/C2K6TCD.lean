module

public import Minimality.Type08S.C2K6TCC

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

/-- Pc leaf 1 cycle `(a, b', a', b, d)` (counterclockwise) in the frame `(a - d, (b - d)/m, (c - a')/m)`,
`m = 1 - γ6`: `a = (1,0,0)`, `b' = (1,g,g)`, `a' = (0,1,1-m)`, `b = (0,m,0)`, `d = 0`;
the other points are `c = (0,1,1)`, `c' = (1,e,0)` with `e = β1 m`, `g = γ4`. -/
def k6t3_pcX (m g : ℝ) : ZMod 5 → ℝ × ℝ × ℝ := ![(1, 0, 0), (1, g, g), (0, 1, 1 - m), (0, m, 0), (0, 0, 0)]

theorem k6t3_pcX_0 : k6t3_pcX m g 0 = (1, 0, 0) := rfl
theorem k6t3_pcX_1 : k6t3_pcX m g 1 = (1, g, g) := rfl
theorem k6t3_pcX_2 : k6t3_pcX m g 2 = (0, 1, 1 - m) := rfl
theorem k6t3_pcX_3 : k6t3_pcX m g 3 = (0, m, 0) := rfl
theorem k6t3_pcX_4 : k6t3_pcX m g 4 = (0, 0, 0) := rfl

set_option maxHeartbeats 6400000 in
/-- Tilt test of the Pc leaf-1 pentagon, cone `v1 < 0`, `0 < v2 + (1 - g) v1`; needs `e < g` (c' under b'). -/
theorem k6t3_pc1_tsc {m g e v1 v2 : ℝ} (hm : 0 < m) (hm1 : m < 1) (hg : 0 < g) (he : 0 < e) (heg : e < g)
    (hv1 : v1 < 0) (hv2 : 0 < v2 + (1 - g) * v1) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k6t3_pcX m g (i + 1) - k6t3_pcX m g i) (k6t3_pcX m g j - k6t3_pcX m g i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (1 : ℝ), (1 : ℝ)), (1, e, 0)], ∀ i : ZMod 5,
      TSc 1 (k6t3_pcX m g (i + 1) - k6t3_pcX m g i) (t - k6t3_pcX m g i) (v1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  have nv := neg_pos.2 hv1
  have g1 : 0 < 1 - m := by linarith
  have k1 := mul_pos hg he
  have k2 := mul_pos (mul_pos hg he) nv
  have k3 := mul_pos hm nv
  have k4 := mul_pos (mul_pos hm g1) nv
  have k5 := mul_pos hm hv2
  have k6 := mul_pos hm g1
  have k7 := mul_pos hg nv
  have k8 := mul_pos hg hm
  have k9 := sub_pos.2 heg
  constructor
  · intro i j h1 h2
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k6t3_pcX_0, k6t3_pcX_1, k6t3_pcX_2, k6t3_pcX_3, k6t3_pcX_4, f0, f1, f2, f3, f4, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k6t3_pcX_0, k6t3_pcX_1, k6t3_pcX_2, k6t3_pcX_3, k6t3_pcX_4, f0, f1, f2, f3, f4, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 6400000 in
/-- Lex part of the Pc leaf-1 pentagon (depth only): `u > 0`.  Depths: `a = u`, `b' = u + g t + g A`,
`a' = t + (1-m) A`, `b = m t`, `d = 0`. -/
theorem k6t3_pc1_real {m g k0 U T B u t A : ℝ} (hm : 0 < m) (hm1 : m < 1) (hg : 0 < g) (hA : 0 < A) (hu : 0 < u)
    (hdep : ∀ i j : ZMod 5,
      k0 + (k6t3_pcX m g i).1 * U + (k6t3_pcX m g i).2.1 * T + (k6t3_pcX m g i).2.2 * B <
      k0 + (k6t3_pcX m g j).1 * U + (k6t3_pcX m g j).2.1 * T + (k6t3_pcX m g j).2.2 * B →
      (k6t3_pcX m g i).1 * u + (k6t3_pcX m g i).2.1 * t + (k6t3_pcX m g i).2.2 * A ≤
      (k6t3_pcX m g j).1 * u + (k6t3_pcX m g j).2.1 * t + (k6t3_pcX m g j).2.2 * A)
    (hinj : ∀ i j, k0 + (k6t3_pcX m g i).1 * U + (k6t3_pcX m g i).2.1 * T + (k6t3_pcX m g i).2.2 * B =
      k0 + (k6t3_pcX m g j).1 * U + (k6t3_pcX m g j).2.1 * T + (k6t3_pcX m g j).2.2 * B → i = j) :
    LexUni (fun _ => (0 : ℝ))
      (fun i => k0 + (k6t3_pcX m g i).1 * U + (k6t3_pcX m g i).2.1 * T + (k6t3_pcX m g i).2.2 * B) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  obtain ⟨s0, s1, s2, s3, s4⟩ := k5d_z5_sub
  refine k5d_uni_of_nopair (by decide) _ hinj ?_
  intro i j h1 h2 h3
  have g1 : 0 < 1 - m := by linarith
  have p1 := mul_pos hg hA
  have p2 := mul_pos hm hA
  have p3 := mul_pos g1 hA
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
    | (simp only [k6t3_pcX_0, k6t3_pcX_1, k6t3_pcX_2, k6t3_pcX_3, k6t3_pcX_4, f0, f1, f2, f3, f4, s0, s1, s2, s3, s4] at d5 d6 d7 d8
       first
       | nlinarith
       | (have hta : t + A < 0 := by
            by_contra hh
            push Not at hh
            nlinarith [mul_nonneg hg.le hh]
          nlinarith [mul_pos g1 (neg_pos.2 hta)]))

end C2
end Type08Sp
end Minimality
