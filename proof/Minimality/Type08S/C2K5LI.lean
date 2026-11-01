module

public import Minimality.Type08S.C2K5LH

@[expose] public section


/-!
# K5L / I: K5c, FC-ac at `u0 = d - b` (QPc with `α4 > 1`), frame form

Frame `(P,Q,R) = (a - d, c - d, d - b)`; points over `d`:
`d = 0, a = (1,0,0), c = (0,1,0), b' = (α4,γ4,0), b = (0,0,-1), c' = (1,0,-β1), a' = (0,γ6,-β6)` (T': `α1 = 1`).
Face `Q_ac = (d, a, b', c)` (convex, affine); cone `v1 > 0, v2 > 0, γ4 v1 < (α4 - 1) v2` (nonempty iff `α4 > 1`).
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

def kqCyc (α4 γ4 : ℝ) : ZMod 4 → ℝ × ℝ × ℝ := ![(0, 0, 0), (1, 0, 0), (α4, γ4, 0), (0, 1, 0)]

theorem kqCyc_0 : kqCyc α4 γ4 0 = (0, 0, 0) := rfl
theorem kqCyc_1 : kqCyc α4 γ4 1 = (1, 0, 0) := rfl
theorem kqCyc_2 : kqCyc α4 γ4 2 = (α4, γ4, 0) := rfl
theorem kqCyc_3 : kqCyc α4 γ4 3 = (0, 1, 0) := rfl

set_option maxHeartbeats 3200000 in
theorem kq_tsc {α4 γ4 β1 β6 γ6 v1 v2 : ℝ} (hα4 : 1 < α4) (hγ4 : 0 < γ4) (hβ1 : 0 < β1) (hb6 : 0 < β6)
    (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hv1 : 0 < v1) (hv2 : 0 < v2) (hcone : γ4 * v1 < (α4 - 1) * v2) :
    (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      TSc 1 (kqCyc α4 γ4 (i + 1) - kqCyc α4 γ4 i) (kqCyc α4 γ4 j - kqCyc α4 γ4 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (0 : ℝ), (-1 : ℝ)), (1, 0, -β1), (0, γ6, -β6)], ∀ i : ZMod 4,
      TSc 1 (kqCyc α4 γ4 (i + 1) - kqCyc α4 γ4 i) (t - kqCyc α4 γ4 i) (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3⟩ := z4_add
  have a1 : 0 < α4 - 1 := by linarith
  have k1 := mul_pos hβ1 hv2
  have k2 := mul_pos hb6 hv1
  have k3 := mul_pos hβ1 (sub_pos.2 hcone)
  have k4 := mul_pos (sub_pos.2 hγ61) hb6
  have k5 := mul_pos a1 hγ6
  have k6 := mul_pos hγ4 hβ1
  have k7 := mul_pos hγ6 hb6
  have k8 := mul_pos (mul_pos a1 hγ6) hb6
  have k9 := mul_pos hb6 (sub_pos.2 hγ61)
  have k10 := mul_pos (sub_pos.2 hγ61) a1
  have k11 : 0 < α4 * (1 - γ6) := mul_pos (by linarith) (sub_pos.2 hγ61)
  constructor
  · intro i j h1 h2
    rcases z4_cases i with rfl | rfl | rfl | rfl <;>
      rcases z4_cases j with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, kqCyc_0, kqCyc_1, kqCyc_2, kqCyc_3, s0, s1, s2, s3, Prod.fst_sub, Prod.snd_sub,
          Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;>
      rcases z4_cases i with rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, kqCyc_0, kqCyc_1, kqCyc_2, kqCyc_3, s0, s1, s2, s3, Prod.fst_sub, Prod.snd_sub,
          Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

theorem kq_inj {α4 γ4 : ℝ} (hγ4 : 0 < γ4) (hα4 : 1 < α4) : ∀ i j : ZMod 4, kqCyc α4 γ4 i = kqCyc α4 γ4 j → i = j := by
  intro i j h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  rcases z4_cases i with rfl | rfl | rfl | rfl <;> rcases z4_cases j with rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [kqCyc_0, kqCyc_1, kqCyc_2, kqCyc_3] at e1 e2; linarith)

theorem k5c_fcac_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {α4 γ4 β1 β6 γ6 : ℝ}
    (hα4 : 1 < α4) (hγ4 : 0 < γ4) (hβ1 : 0 < β1) (hb6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hmem : ∀ i, fpoint P Q R d (kqCyc α4 γ4 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨
      y = fpoint P Q R d (α4, γ4, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, -1) ∨
      y = fpoint P Q R d (1, 0, -β1) ∨ y = fpoint P Q R d (0, γ6, -β6)) :
    HasLexCellAt V R := by
  have a1 : 0 < α4 - 1 := by linarith
  refine fc_cell V P Q R d hΔ (kqCyc α4 γ4) (β := α4) (γ := γ4) (by linarith) hγ4 (by linarith) ?_
    (kq_inj hγ4 hα4) hmem [((0 : ℝ), (0 : ℝ), (-1 : ℝ)), (1, 0, -β1), (0, γ6, -β6)] ?_
    (u1 := 1) (u2 := γ4 / (α4 - 1)) (t1 := 0) (t2 := 1) (lo := 0) (hi := 1) (by norm_num) (by norm_num)
    (fun v1 v2 => 0 < v1 ∧ 0 < v2 ∧ γ4 * v1 < (α4 - 1) * v2) ?_ ?_
  · simp only [kqCyc, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Prod.ext_iff]
    simp
  · intro y hy
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inl ⟨2, rfl⟩
    · exact Or.inl ⟨3, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
  · intro lam h0 h1
    have hq : γ4 / (α4 - 1) * (α4 - 1) = γ4 := div_mul_cancel₀ _ a1.ne'
    have hp : 0 < γ4 / (α4 - 1) := div_pos hγ4 a1
    refine ⟨by simp, by simp; nlinarith, ?_⟩
    simp only [mul_zero, add_zero, mul_one]
    nlinarith
  · intro v1 v2 ⟨hv1, hv2, hc⟩
    exact kq_tsc hα4 hγ4 hβ1 hb6 hγ6 hγ61 hv1 hv2 hc

end C2
end Type08Sp
end Minimality
