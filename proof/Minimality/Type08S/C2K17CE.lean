module

public import Minimality.Type08S.C2K17CD

@[expose] public section


/-!
# K17C / P3E: the pentagon `(b, a', b', a, d)` at the view `a - d` (cells S3.3 / S3.6a): cycle, injectivity, TSc.
Frame `(P, Q, R) = (b - d, c - d, a - d)`; cone `v1 > 0 > v2`, `β6 v2 + (1-γ6) v1 < 0`, `γ6 v1 + (1-β6) v2 > 0`.
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

def k17cACyc (α1 β6 γ6 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  pc5 (1, 0, 0) (β6, γ6, 0) (0, 1, α1) (0, 0, 1) (0, 0, 0)

theorem k17cA_inj {α1 β6 γ6 : ℝ} (hα1 : 0 < α1) (hγ6 : 0 < γ6) (hb6 : 0 < β6) :
    ∀ i j : ZMod 5, k17cACyc α1 β6 γ6 i = k17cACyc α1 β6 γ6 j → i = j := by
  intro i j h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  have e3 := congrArg (fun t => t.2.2) h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [k17cACyc, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4] at e1 e2 e3; linarith)

set_option maxHeartbeats 6400000 in
theorem k17cA_tsc {α1 β6 γ6 v1 v2 : ℝ} (hα1 : 1 ≤ α1) (hb6 : 0 < β6) (hγ6 : 0 < γ6) (hs : 1 < β6 + γ6)
    (hv1 : 0 < v1) (hv2 : v2 < 0) (hc3 : β6 * v2 + (1 - γ6) * v1 < 0) (hc4 : 0 < γ6 * v1 + (1 - β6) * v2) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k17cACyc α1 β6 γ6 (i + 1) - k17cACyc α1 β6 γ6 i) (k17cACyc α1 β6 γ6 j - k17cACyc α1 β6 γ6 i)
        (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (1 : ℝ), (0 : ℝ)), (1, 0, α1)], ∀ i : ZMod 5,
      TSc 1 (k17cACyc α1 β6 γ6 (i + 1) - k17cACyc α1 β6 γ6 i) (t - k17cACyc α1 β6 γ6 i) (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have a0 : 0 < α1 := by linarith
  have w2 : 0 < -v2 := by linarith
  have c3 : 0 < -(β6 * v2 + (1 - γ6) * v1) := by linarith
  have h1 := mul_pos hv1 w2
  have h2 := mul_pos a0 hv1
  have h3 := mul_pos a0 w2
  have h4 := mul_pos hb6 hv1
  have h5 := mul_pos hb6 w2
  have h6 := mul_pos hγ6 hv1
  have h7 := mul_pos hγ6 w2
  have h8 := mul_pos a0 hc4
  have h9 := mul_pos a0 c3
  have h10 := mul_pos hb6 hc4
  have h11 := mul_pos hγ6 hc4
  have h12 := mul_pos hb6 c3
  have h13 := mul_pos hγ6 c3
  have h14 := mul_pos (mul_pos a0 hb6) hv1
  have h15 := mul_pos (mul_pos a0 hb6) w2
  have h16 := mul_pos (mul_pos a0 hγ6) hv1
  have h17 := mul_pos (mul_pos a0 hγ6) w2
  rcases eq_or_lt_of_le hα1 with hA | hA
  all_goals first | subst hA | skip
  all_goals
    try have a1 := sub_pos.2 hA
    try have h18 := mul_pos a1 hv1
    try have h19 := mul_pos a1 w2
    constructor
    · intro i j h1' h2'
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
        rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact absurd rfl h1'
        | exact (h2' (by decide)).elim
        | (simp only [TSc, d3, k17cACyc, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
            Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
           first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
    · intro t ht i
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;>
        rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
        (simp only [TSc, d3, k17cACyc, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
            Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
