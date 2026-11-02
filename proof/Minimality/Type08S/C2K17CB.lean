module

public import Minimality.Type08S.C2K17CA

@[expose] public section


/-!
# K17C / P3B: cell S3.5 at the view `d - b` (pentagon `(c', b', c, d, b)`), frame `(a - d, c - d, d - b)`.
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

theorem k17c_inner_fcomb_right (w p q r : ℝ³) (x y z : ℝ) :
    ⟪w, fcomb p q r x y z⟫ = x * ⟪w, p⟫ + y * ⟪w, q⟫ + z * ⟪w, r⟫ := by
  simp only [fcomb, inner_add_right, real_inner_smul_right]

/-- Pentagon for S3.5, rotated to start at the peak `b'`: `(b', c, d, b, c')`. -/
def k17cS35Cyc (α1 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  pc5 (α1, 1, 0) (0, 1, 0) (0, 0, 0) (0, 0, -1) (α1, 0, -1)

theorem k17cS35_inj {α1 : ℝ} (hα1 : 0 < α1) :
    ∀ i j : ZMod 5, k17cS35Cyc α1 i = k17cS35Cyc α1 j → i = j := by
  intro i j h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  have e3 := congrArg (fun t => t.2.2) h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [k17cS35Cyc, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4] at e1 e2 e3; linarith)

set_option maxHeartbeats 3200000 in
theorem k17cS35_tsc {α1 β6 γ6 v1 v2 : ℝ} (hα1 : 1 ≤ α1) (hb6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 ≤ 1)
    (hs : 1 < β6 + γ6) (hv1 : 0 < v1) (hv2 : v2 < 0) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k17cS35Cyc α1 (i + 1) - k17cS35Cyc α1 i) (k17cS35Cyc α1 j - k17cS35Cyc α1 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0, γ6, -β6)], ∀ i : ZMod 5,
      TSc 1 (k17cS35Cyc α1 (i + 1) - k17cS35Cyc α1 i) (t - k17cS35Cyc α1 i) (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have a0 : 0 < α1 := by linarith
  have w2 : 0 < -v2 := by linarith
  have h1 := mul_pos hv1 w2
  have h2 := mul_pos a0 hv1
  have h3 := mul_pos a0 w2
  have h4 := mul_pos hb6 hv1
  have h5 := mul_pos hb6 w2
  have h6 := mul_pos hγ6 hv1
  have h7 := mul_pos hγ6 w2
  have h8 := mul_pos (mul_pos a0 hb6) w2
  have h9 := mul_pos (mul_pos a0 hb6) hv1
  have h10 := mul_pos (mul_pos a0 hγ6) hv1
  have h11 := mul_pos (mul_pos a0 hγ6) w2
  rcases eq_or_lt_of_le hα1 with hA | hA <;> rcases eq_or_lt_of_le hγ61 with hG | hG
  all_goals first | subst hA | skip
  all_goals first | subst hG | skip
  all_goals
    try have a1 := sub_pos.2 hA
    try have g1 := sub_pos.2 hG
    try have h12 := mul_pos a1 hv1
    try have h13 := mul_pos a1 w2
    try have h14 := mul_pos (mul_pos a0 g1) hv1
    try have h15 := mul_pos (mul_pos a0 g1) w2
    try have h16 := mul_pos (mul_pos a0 g1) hb6
    constructor
    · intro i j h1' h2'
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
        rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact absurd rfl h1'
        | exact (h2' (by decide)).elim
        | (simp only [TSc, d3, k17cS35Cyc, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
            Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
           first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
    · intro t ht i
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;>
        rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
        (simp only [TSc, d3, k17cS35Cyc, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
            Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
