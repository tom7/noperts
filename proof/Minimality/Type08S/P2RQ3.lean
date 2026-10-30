module

public import Minimality.Type08S.P2RQ2
public import Minimality.Type08S.P2RKT3

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkR / R5a / Q3: **the 5-cycle cell in frame form** (`lexCell_P3Tp_n`, general `b' = (α,g,0)`).
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

set_option maxHeartbeats 1600000 in
/-- `V` consists of the seven frame points over `d` (`p = a-d`, `q = c-d`, `r = b-d`; `p ⊥ r`, `⟪q, r⟫ < 0`,
`β, g > 0`, `0 < h < 1`, `k > 0`), the cycle points lie in `V`: `V` has a lex cell at the base view `r`. -/
theorem r5A_hasLexCellAt (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0)
    (hpr : ⟪p, r⟫ = 0) (hqr : ⟪q, r⟫ < 0) {α β g h k : ℝ} (hα : 0 < α) (hαg : 1 < α + g) (hβ : 0 < β) (hg : 0 < g) (hh : 0 < h)
    (hh1 : h < 1) (hk : 0 < k)
    (hmem : ∀ i, fpoint p q r d (r5CycA α β g i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint p q r d (1, 0, β) ∨ y = fpoint p q r d (α, g, 0) ∨
      y = fpoint p q r d (0, 1, 0) ∨ y = fpoint p q r d (0, 0, 0) ∨ y = fpoint p q r d (0, 0, 1) ∨
      y = fpoint p q r d (1, 0, 0) ∨ y = fpoint p q r d (0, h, k)) :
    HasLexCellAt V r := by
  have hg1 : 0 < g := hg
  obtain ⟨μ, hμ, hμM, hP⟩ := exists_mu' p q r hΔ hpr (M := g / (1 + |α - 1|)) (by positivity)
  have hq : 0 < (α - 1) * μ - g * (-1) := by
    have h1 : |α - 1| * μ < g := by
      have h2 : μ * (1 + |α - 1|) < g := by rwa [lt_div_iff₀ (by positivity)] at hμM
      nlinarith [abs_nonneg (α - 1)]
    have := neg_abs_le (α - 1)
    nlinarith [abs_nonneg (α - 1)]
  have hr0 : r ≠ 0 := by rintro rfl; simp at hqr
  have hB : 0 < ⟪r, r⟫ := real_inner_self_pos.2 hr0
  set vv := fcomb p q r (-1) μ 0 with hvv
  set C := ⟪q, r⟫ with hCdef
  set B := ⟪r, r⟫ with hBdef
  set P := ⟪p, vv⟫ with hPdef
  have hz : ∀ i, ⟪fpoint p q r d (r5CycA α β g i), r⟫ =
      ⟪d, r⟫ + (r5CycA α β g i).2.1 * C + (r5CycA α β g i).2.2 * B := by
    intro i; rw [inner_fpoint, hpr]; ring
  have hw : ∀ i, ⟪fpoint p q r d (r5CycA α β g i), vv⟫ = ⟪d, vv⟫ + (r5CycA α β g i).1 * P +
      (r5CycA α β g i).2.1 * ⟪q, vv⟫ + (r5CycA α β g i).2.2 * ⟪r, vv⟫ := by
    intro i; rw [inner_fpoint]
  have hlex : LexUni (fun i => ⟪fpoint p q r d (r5CycA α β g i), r⟫)
      (fun i => ⟪fpoint p q r d (r5CycA α β g i), vv⟫) := by
    refine lexUni5_top _ _ ?_ ?_ ?_ ?_
    · intro i j hzij hwij
      simp only [hz, hw] at hzij hwij
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
        rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
        simp only [r5CycA, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4] at hzij hwij <;>
        first
        | rfl
        | (exfalso; nlinarith [mul_pos hg hB, mul_pos hβ hB, mul_neg_of_pos_of_neg hg hqr])
        | (exfalso; apply hP
           have hb : β = 1 := mul_right_cancel₀ hB.ne' (by linarith)
           subst hb; linarith)
        | (exfalso; apply hP
           have hb : g = 1 := mul_right_cancel₀ hqr.ne (by linarith)
           subst hb
           have h0 : α * P = 0 := by linarith
           exact (mul_eq_zero.1 h0).resolve_left hα.ne')
    · left; simp only [hz]; simp only [r5CycA, pc5_0, pc5_1]; nlinarith [mul_pos hβ hB, mul_neg_of_pos_of_neg hg hqr]
    · left; simp only [hz]; simp only [r5CycA, pc5_2, pc5_3]; nlinarith
    · left; simp only [hz]; simp only [r5CycA, pc5_3, pc5_4]; nlinarith
  have n0 : -(0 : ZMod 5) = 0 := by decide
  have n1 : -(1 : ZMod 5) = 4 := by decide
  have n2 : -(2 : ZMod 5) = 3 := by decide
  have n3 : -(3 : ZMod 5) = 2 := by decide
  have n4 : -(4 : ZMod 5) = 1 := by decide
  rcases hΔ.lt_or_gt with hneg | hpos
  · have hD : 0 < -det3 p q r := by linarith
    have hcyc := r5A_cyc (v1 := -1) (v2 := μ) (v3 := 0) hD hα hαg hβ hg (by norm_num) hμ hq
    have hr1 := r5A_rest (v1 := -1) (v2 := μ) (v3 := 0) hD hα hαg hβ hg hh hh1 hk (by norm_num) hμ hq
    refine ⟨5, inferInstance, fun i => fpoint p q r d (r5CycA α β g (-i)), fcomb p q r (-1) μ 0, ?_⟩
    refine lexCell_coord V p q r d (by norm_num) (fun i => r5CycA α β g (-i)) (-1, μ, 0) (fun i => hmem (-i))
      (hcyc_rev hcyc) ?_ (lexUni_neg hlex)
    intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [n0, r5CycA, pc5_0])).elim
    · exact (hyx 4 (by simp only [n4, r5CycA, pc5_1])).elim
    · exact (hyx 3 (by simp only [n3, r5CycA, pc5_2])).elim
    · exact (hyx 2 (by simp only [n2, r5CycA, pc5_3])).elim
    · exact (hyx 1 (by simp only [n1, r5CycA, pc5_4])).elim
    · exact ⟨_, rfl, hrest_rev hr1.1⟩
    · exact ⟨_, rfl, hrest_rev hr1.2⟩
  · have hcyc := r5A_cyc (v1 := -1) (v2 := μ) (v3 := 0) hpos hα hαg hβ hg (by norm_num) hμ hq
    have hr1 := r5A_rest (v1 := -1) (v2 := μ) (v3 := 0) hpos hα hαg hβ hg hh hh1 hk (by norm_num) hμ hq
    refine ⟨5, inferInstance, fun i => fpoint p q r d (r5CycA α β g i), fcomb p q r (-1) μ 0, ?_⟩
    refine lexCell_coord V p q r d (by norm_num) (r5CycA α β g) (-1, μ, 0) hmem hcyc ?_ hlex
    intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [r5CycA, pc5_0])).elim
    · exact (hyx 1 (by simp only [r5CycA, pc5_1])).elim
    · exact (hyx 2 (by simp only [r5CycA, pc5_2])).elim
    · exact (hyx 3 (by simp only [r5CycA, pc5_3])).elim
    · exact (hyx 4 (by simp only [r5CycA, pc5_4])).elim
    · exact ⟨_, rfl, hr1.1⟩
    · exact ⟨_, rfl, hr1.2⟩

end Type08Sp
end Minimality
