module

public import Minimality.Type08S.C2K17CL

@[expose] public section


/-!
# K17C / P3M: TSc for S3.6b (pentagon `(c', b', c, a', b)`) and S3.4 (quadrilateral `(c', b', a', b)`) at `d - b`;
cone `v1 < 0`, `v2 < 0`; frame `(a - d, c - d, d - b)`.
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

def k17cS36bCyc (α1 β6 γ6 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  pc5 (α1, 0, -1) (α1, 1, 0) (0, 1, 0) (0, γ6, -β6) (0, 0, -1)

theorem k17cS36b_inj {α1 β6 γ6 : ℝ} (hα1 : 0 < α1) (hγ6 : 0 < γ6) (hb6 : 0 < β6) :
    ∀ i j : ZMod 5, k17cS36bCyc α1 β6 γ6 i = k17cS36bCyc α1 β6 γ6 j → i = j := by
  intro i j h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  have e3 := congrArg (fun t => t.2.2) h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [k17cS36bCyc, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4] at e1 e2 e3; linarith)

set_option maxHeartbeats 6400000 in
theorem k17cS36b_tsc {α1 β6 γ6 v1 v2 : ℝ} (hα1 : 1 < α1) (hb6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 ≤ 1)
    (hs : 1 < β6 + γ6) (hv1 : v1 < 0) (hv2 : v2 < 0) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k17cS36bCyc α1 β6 γ6 (i + 1) - k17cS36bCyc α1 β6 γ6 i)
        (k17cS36bCyc α1 β6 γ6 j - k17cS36bCyc α1 β6 γ6 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (1, 0, 0)], ∀ i : ZMod 5,
      TSc 1 (k17cS36bCyc α1 β6 γ6 (i + 1) - k17cS36bCyc α1 β6 γ6 i)
        (t - k17cS36bCyc α1 β6 γ6 i) (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have a0 : 0 < α1 := by linarith
  have a1 := sub_pos.2 hα1
  have w1 : 0 < -v1 := by linarith
  have w2 : 0 < -v2 := by linarith
  have h1 := mul_pos w1 w2
  have h2 := mul_pos a0 w1
  have h3 := mul_pos a0 w2
  have h4 := mul_pos hb6 w1
  have h5 := mul_pos hb6 w2
  have h6 := mul_pos hγ6 w1
  have h7 := mul_pos hγ6 w2
  have h8 := mul_pos (mul_pos a0 hb6) w2
  have h9 := mul_pos (mul_pos a0 hb6) w1
  have h10 := mul_pos (mul_pos a0 hγ6) w1
  have h11 := mul_pos (mul_pos a0 hγ6) w2
  have h12 := mul_pos a1 w1
  have h13 := mul_pos a1 w2
  rcases eq_or_lt_of_le hγ61 with hG | hG
  all_goals first | subst hG | skip
  all_goals
    try have g1 := sub_pos.2 hG
    try have h14 := mul_pos (mul_pos a0 g1) w1
    try have h15 := mul_pos (mul_pos a0 g1) w2
    try have h16 := mul_pos (mul_pos a0 g1) hb6
    constructor
    · intro i j h1' h2'
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
        rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact absurd rfl h1'
        | exact (h2' (by decide)).elim
        | (simp only [TSc, d3, k17cS36bCyc, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
            Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
           first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
    · intro t ht i
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;>
        rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
        (simp only [TSc, d3, k17cS36bCyc, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
            Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

def k17cS34Cyc (α1 β6 γ6 : ℝ) : ZMod 4 → ℝ × ℝ × ℝ :=
  ![(α1, 0, -1), (α1, 1, 0), (0, γ6, -β6), (0, 0, -1)]

theorem k17cS34Cyc_0 : k17cS34Cyc α1 β6 γ6 0 = (α1, 0, -1) := rfl
theorem k17cS34Cyc_1 : k17cS34Cyc α1 β6 γ6 1 = (α1, 1, 0) := rfl
theorem k17cS34Cyc_2 : k17cS34Cyc α1 β6 γ6 2 = (0, γ6, -β6) := rfl
theorem k17cS34Cyc_3 : k17cS34Cyc α1 β6 γ6 3 = (0, 0, -1) := rfl

theorem k17cS34_inj {α1 β6 γ6 : ℝ} (hα1 : 0 < α1) (hγ6 : 1 < γ6) :
    ∀ i j : ZMod 4, k17cS34Cyc α1 β6 γ6 i = k17cS34Cyc α1 β6 γ6 j → i = j := by
  intro i j h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  have e3 := congrArg (fun t => t.2.2) h
  rcases z4_cases i with rfl | rfl | rfl | rfl <;> rcases z4_cases j with rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [k17cS34Cyc_0, k17cS34Cyc_1, k17cS34Cyc_2, k17cS34Cyc_3] at e1 e2 e3; linarith)

set_option maxHeartbeats 6400000 in
theorem k17cS34_tsc {α1 β6 γ6 v1 v2 : ℝ} (hα1 : 1 < α1) (hb6 : 0 < β6) (hγ6 : 1 < γ6)
    (hv1 : v1 < 0) (hv2 : v2 < 0) :
    (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      TSc 1 (k17cS34Cyc α1 β6 γ6 (i + 1) - k17cS34Cyc α1 β6 γ6 i)
        (k17cS34Cyc α1 β6 γ6 j - k17cS34Cyc α1 β6 γ6 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (1, 0, 0), (0, 1, 0)], ∀ i : ZMod 4,
      TSc 1 (k17cS34Cyc α1 β6 γ6 (i + 1) - k17cS34Cyc α1 β6 γ6 i)
        (t - k17cS34Cyc α1 β6 γ6 i) (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3⟩ := z4_add
  have a0 : 0 < α1 := by linarith
  have a1 := sub_pos.2 hα1
  have g1 := sub_pos.2 hγ6
  have g0 : 0 < γ6 := by linarith
  have w1 : 0 < -v1 := by linarith
  have w2 : 0 < -v2 := by linarith
  have h1 := mul_pos w1 w2
  have h2 := mul_pos a0 w1
  have h3 := mul_pos a0 w2
  have h4 := mul_pos hb6 w1
  have h5 := mul_pos hb6 w2
  have h6 := mul_pos g0 w1
  have h7 := mul_pos g0 w2
  have h8 := mul_pos (mul_pos a0 hb6) w2
  have h9 := mul_pos (mul_pos a0 hb6) w1
  have h10 := mul_pos (mul_pos a0 g0) w1
  have h11 := mul_pos (mul_pos a0 g0) w2
  have h12 := mul_pos a1 w1
  have h13 := mul_pos a1 w2
  have h14 := mul_pos (mul_pos a0 g1) w1
  have h15 := mul_pos (mul_pos a0 g1) w2
  have h16 := mul_pos (mul_pos a0 g1) hb6
  have h17 := mul_pos (mul_pos a0 g1) a0
  constructor
  · intro i j h1' h2'
    rcases z4_cases i with rfl | rfl | rfl | rfl <;>
      rcases z4_cases j with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1'
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, k17cS34Cyc_0, k17cS34Cyc_1, k17cS34Cyc_2, k17cS34Cyc_3, s0, s1, s2, s3,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;>
      rcases z4_cases i with rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k17cS34Cyc_0, k17cS34Cyc_1, k17cS34Cyc_2, k17cS34Cyc_3, s0, s1, s2, s3,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
