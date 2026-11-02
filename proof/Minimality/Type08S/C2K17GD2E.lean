module

public import Minimality.Type08S.C2K17GD2D

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
/-- **Tc `α4 = 1`, cell B** `(c', b', c, d, b)` at `q = b - d`, frame `(p, r, q)`.  Tilt `(-1, v2)`, `max 0 (1-γ4) < v2 < σ1`;
at the depth tie `⟪r,q⟫ = 0` (`z(c) = z(d)`) the tilt puts `c` below `d` iff `v2 ⟪r,r⟫ < ⟪p,r⟫`. -/
theorem k17gdB_frame (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p r q ≠ 0) {α1 β1 γ4 : ℝ}
    (hα1 : 1 < α1) (hβ1 : 0 < β1) (hγ4 : 0 < γ4) (hE : 0 ≤ 1 - β1 - α1 + α1 * γ4)
    (hrr : 0 < ⟪r, r⟫) (σ1 : ℝ) (hσ : max 0 (1 - γ4) < σ1)
    (hcase : ⟪r, q⟫ < 0 ∨ (⟪r, q⟫ = 0 ∧ σ1 * ⟪r, r⟫ ≤ ⟪p, r⟫))
    (hmem : ∀ i, fpoint p r q d (k17gdB α1 β1 γ4 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint p r q d (α1, 0, β1) ∨ y = fpoint p r q d (1, γ4, 0) ∨
      y = fpoint p r q d (0, 1, 0) ∨ y = fpoint p r q d (0, 0, 0) ∨ y = fpoint p r q d (0, 0, 1) ∨
      y = fpoint p r q d (1, 0, 0) ∨ y = fpoint p r q d (0, 1, 1)) :
    HasLexCellAt V q := by
  have hq0 : q ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  have hqq : 0 < ⟪q, q⟫ := real_inner_self_pos.2 hq0
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint p r q d t, q⟫ = ⟪d, q⟫ + t.1 * ⟪p, q⟫ + t.2.1 * ⟪r, q⟫ + t.2.2 * ⟪q, q⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  set σ0 := max 0 (1 - γ4) with hσ0
  have hσ00 : 0 ≤ σ0 := le_max_left _ _
  have hσ01 : 1 - γ4 ≤ σ0 := le_max_right _ _
  have hsg : 0 < σ1 - σ0 := by linarith
  refine cyc_cell V p r q d hΔ (k := 5) (by norm_num) (k17gdB α1 β1 γ4) (k17gdB_inj hα1 hβ1 hγ4) hmem
    [(1, 0, 0), (0, 1, 1)] ?_ (u1 := -1) (u2 := σ0) (t1 := 0) (t2 := σ1 - σ0) (lo := 0) (hi := 1)
    (by rw [show (-1:ℝ) * (σ1 - σ0) - σ0 * 0 = -(σ1 - σ0) by ring]; exact (neg_ne_zero.2 hsg.ne'))
    (by norm_num)
    (fun v1 v2 => v1 = -1 ∧ σ0 < v2 ∧ v2 < σ1) ?_ ?_ ?_
  · intro y hy
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by simp [k17gdB, pc5_0]⟩
    · exact Or.inl ⟨1, by simp [k17gdB, pc5_1]⟩
    · exact Or.inl ⟨2, by simp [k17gdB, pc5_2]⟩
    · exact Or.inl ⟨3, by simp [k17gdB, pc5_3]⟩
    · exact Or.inl ⟨4, by simp [k17gdB, pc5_4]⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
  · intro lam hl0 hl1
    refine ⟨by ring, by nlinarith, by nlinarith⟩
  · intro v1 v2 hv
    obtain ⟨h1, h2, h3⟩ := hv
    have hv1 : v1 < 0 := by rw [h1]; norm_num
    have hv2 : 0 < v2 := by linarith
    have hc : 0 < v2 + (1 - γ4) * v1 := by rw [h1]; linarith
    refine ⟨k17gdB_tsc hα1 hβ1 hγ4 hv1 hv2 hE hc, ?_⟩
    intro t ht i
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact (k17gdB_rest hα1 hβ1 hγ4 hv1 hv2 hE hc).1 i
    · exact (k17gdB_rest hα1 hβ1 hγ4 hv1 hv2 hE hc).2 i
  · intro v1 v2 hv hsep
    obtain ⟨h1, h2, h3⟩ := hv
    set z : ZMod 5 → ℝ := fun i => ⟪fpoint p r q d (k17gdB α1 β1 γ4 i), q⟫ with hzdef
    set w : ZMod 5 → ℝ := fun i => ⟪fpoint p r q d (k17gdB α1 β1 γ4 i), fcomb p r q v1 v2 0⟫ with hwdef
    have z0 : z 0 = ⟪d, q⟫ + α1 * ⟪p, q⟫ + β1 * ⟪q, q⟫ := by simp only [hzdef, k17gdB, pc5_0, hz]; ring
    have z1 : z 1 = ⟪d, q⟫ + ⟪p, q⟫ + γ4 * ⟪r, q⟫ := by simp only [hzdef, k17gdB, pc5_1, hz]; ring
    have z2 : z 2 = ⟪d, q⟫ + ⟪r, q⟫ := by simp only [hzdef, k17gdB, pc5_2, hz]; ring
    have z3 : z 3 = ⟪d, q⟫ := by simp only [hzdef, k17gdB, pc5_3, hz]; ring
    have z4 : z 4 = ⟪d, q⟫ + ⟪q, q⟫ := by simp only [hzdef, k17gdB, pc5_4, hz]; ring
    have h34 : LexLt (z 3, w 3) (z 4, w 4) := k17gd_ll (by rw [z3, z4]; linarith)
    have hkey : ∀ hqr : ⟪r, q⟫ ≤ 0, LexLt (z 1, w 1) (z 0, w 0) ∨ LexLt (z 1, w 1) (z 2, w 2) := by
      intro hqr
      rcases k17gdB_key (pq := ⟪p, q⟫) hα1 hβ1 hγ4 hE hqq hqr with k | k
      · left; exact k17gd_ll (by rw [z0, z1]; linarith)
      · right; exact k17gd_ll (by rw [z1, z2]; linarith)
    rcases hcase with hq | ⟨hq, hlit⟩
    · exact k17gd_lexUni5_B z w hsep (k17gd_ll (by rw [z2, z3]; linarith)) h34 (fun _ => hkey hq.le)
    · have h23 : LexLt (z 2, w 2) (z 3, w 3) := by
        refine k17gd_ll' (by rw [z2, z3, hq]; ring) ?_
        simp only [hwdef, k17gdB, pc5_2, pc5_3, k17f_wexp]
        have : v1 * (⟪d, p⟫ + (0:ℝ) * ⟪p, p⟫ + (1:ℝ) * ⟪p, r⟫ + (0:ℝ) * ⟪p, q⟫) +
            v2 * (⟪d, r⟫ + (0:ℝ) * ⟪p, r⟫ + (1:ℝ) * ⟪r, r⟫ + (0:ℝ) * ⟪r, q⟫) <
            v1 * (⟪d, p⟫ + (0:ℝ) * ⟪p, p⟫ + (0:ℝ) * ⟪p, r⟫ + (0:ℝ) * ⟪p, q⟫) +
            v2 * (⟪d, r⟫ + (0:ℝ) * ⟪p, r⟫ + (0:ℝ) * ⟪r, r⟫ + (0:ℝ) * ⟪r, q⟫) := by
          rw [h1]; nlinarith
        exact this
      exact k17gd_lexUni5_B z w hsep h23 h34 (fun _ => hkey hq.le)

end C2
end Type08Sp
end Minimality
