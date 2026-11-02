module

public import Minimality.Type08S.C2K17GB10

@[expose] public section


/-!
# K17GB / GB11: S1.9 cell and theorem (TaE double tie).
-/
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

theorem k17gbY9_inj {m κ μ lq β6 : ℝ} (hm : 0 < m) (hκ : 0 < κ) (hμ : 0 < μ) (hlq : κ < lq) (hb6 : 0 < β6) :
    ∀ i j, k17gbY9 m κ μ lq β6 i = k17gbY9 m κ μ lq β6 j → i = j := by
  intro i j h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [k17gbY9, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; nlinarith [h.1, h.2.1, h.2.2, mul_pos hb6 hκ]) | (exfalso; norm_num at h) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; nlinarith [mul_pos hb6 hκ])

set_option maxHeartbeats 12800000 in
/-- **S1.9 cell**: `(c',b',c,d,a)` at `b' - a'`, frame `(b-d, c-d, b'-a')`. -/
theorem k17gb_s19_cell {a a' b b' c c' d : ℝ³} {α1 α4 β1 γ4 β6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α4 • (a - d) + γ4 • (c - d))
    (ha' : a' = d + β6 • (b - d) + (1 : ℝ) • (c - d)) (hα1 : 1 < α1) (hβ1 : 1 < β1) (hα4 : 1 < α4)
    (hβ6 : 0 < β6) (hβ61 : β6 < 1) (hγ4 : 1 < γ4) (hpl : α4 * (1 - β1) = α1 * (1 - γ4))
    (E1 : ⟪b - a', a - c'⟫ = 0) (E2 : ⟪b - b', a - c'⟫ = 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hz1, hF1, hF2, hq, hu1⟩ := k17gb_s19_facts hdet hc' hb' ha' hα1 hβ1 hα4 hβ6 hβ61 hγ4 hpl E1 E2
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = α4⁻¹ := ⟨_, rfl⟩
  have hκα : κ * α4 = 1 := by rw [hκdef]; exact inv_mul_cancel₀ (by linarith)
  have hκ : 0 < κ := by rw [hκdef]; exact inv_pos.2 (by linarith)
  have hκ1 : κ < 1 := by nlinarith
  obtain ⟨μ, hμdef⟩ : ∃ μ, μ = κ * (γ4 - 1) := ⟨_, rfl⟩
  have hμ : 0 < μ := by rw [hμdef]; exact mul_pos hκ (by linarith)
  obtain ⟨lq, hlqdef⟩ : ∃ lq, lq = α1 * κ := ⟨_, rfl⟩
  have hlq : κ < lq := by rw [hlqdef]; nlinarith
  have hm : 0 < β1 - 1 := by linarith
  have hrel : μ * lq = (β1 - 1) * κ := by
    rw [hμdef, hlqdef]; linear_combination κ ^ 2 * hpl + κ * (β1 - 1) * hκα
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = β6 * (α1 + α4 * (β1 - 1)) / β1 := ⟨_, rfl⟩
  have hδ : β1 * δ = β6 * (α1 + α4 * (β1 - 1)) := by rw [hδdef]; field_simp
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hRdef : b' - a' = α4 • (a - d) + (-β6) • (b - d) + (γ4 - 1) • (c - d) := by rw [hb', ha']; module
  have hΔ : det3 (b - d) (c - d) (b' - a') ≠ 0 := by
    have e : det3 (b - d) (c - d) (b' - a') = α4 * det3 (a - d) (b - d) (c - d) := by
      rw [hRdef]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e]; exact mul_ne_zero (by linarith) hdet
  have Ea : fpoint (b - d) (c - d) (b' - a') d (β6 * κ, -μ, κ) = a := by
    rw [k17gb_fp, hRdef]
    calc d + (β6 * κ) • (b - d) + (-μ) • (c - d) + κ • (α4 • (a - d) + (-β6) • (b - d) + (γ4 - 1) • (c - d))
        = d + (κ * α4) • (a - d) + (κ * (γ4 - 1) - μ) • (c - d) := by module
      _ = a := by rw [hκα, show κ * (γ4 - 1) - μ = 0 by rw [hμdef]; ring]; simp
  have Ec' : fpoint (b - d) (c - d) (b' - a') d (1 + (β1 - 1) + β6 * lq, -(β1 - 1), lq) = c' := by
    rw [k17gb_fp, hRdef, hc']
    calc d + (1 + (β1 - 1) + β6 * lq) • (b - d) + (-(β1 - 1)) • (c - d) +
          lq • (α4 • (a - d) + (-β6) • (b - d) + (γ4 - 1) • (c - d))
        = d + (lq * α4) • (a - d) + β1 • (b - d) + (lq * (γ4 - 1) - (β1 - 1)) • (c - d) := by module
      _ = _ := by
        have h1 : lq * α4 = α1 := by rw [hlqdef]; linear_combination α1 * hκα
        have h2 : lq * (γ4 - 1) - (β1 - 1) = 0 := by
          rw [hlqdef]; linear_combination κ * hpl + (β1 - 1) * hκα
        rw [h1, h2]; simp
  have Eb' : fpoint (b - d) (c - d) (b' - a') d (β6, 1, 1) = b' := by
    rw [k17gb_fp]; rw [ha']; module
  have Ea' : fpoint (b - d) (c - d) (b' - a') d (β6, 1, 0) = a' := by rw [k17gb_fp, ha']; module
  have Eb : fpoint (b - d) (c - d) (b' - a') d (1, 0, 0) = b := by rw [k17gb_fp]; module
  have Ec : fpoint (b - d) (c - d) (b' - a') d (0, 1, 0) = c := by rw [k17gb_fp]; module
  have Ed : fpoint (b - d) (c - d) (b' - a') d (0, 0, 0) = d := by rw [k17gb_fp]; module
  have hw1 : ⟪a - c', c - d⟫ = (1 - β6) * ⟪a - c', b - d⟫ := by
    have : c - d = (1 - β6) • (b - d) + (-1 : ℝ) • (b - a') := by rw [ha']; module
    rw [this]; simp only [inner_smul_right, inner_add_right, hu1]; ring
  refine ⟨b' - a', k17gb_r0 hΔ, ?_⟩
  refine k8_cell_gen (V8 a a' b b' c c' d) (b - d) (c - d) (b' - a') d hΔ (k := 5) (by norm_num)
    (k17gbY9 (β1 - 1) κ μ lq β6) (k17gbY9_inj hm hκ hμ hlq hβ6)
    (u1 := α4 * (1 - β6)) (u2 := -α4) (t1 := δ) (t2 := 0) (by nlinarith [mul_pos (by linarith : (0:ℝ) < α4) hδ0])
    ?_ ?_ ?_ ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [k17gbY9, pc5_0, Ec']; simp [V8]
    · simp only [k17gbY9, pc5_1, Eb']; simp [V8]
    · simp only [k17gbY9, pc5_2, Ec]; simp [V8]
    · simp only [k17gbY9, pc5_3, Ed]; simp [V8]
    · simp only [k17gbY9, pc5_4, Ea]; simp [V8]
  · intro lam h0 h1 D hD
    refine (k17gb_s19_tsc hD hm hκ hκ1 hμ hlq hrel hβ6 hβ61 (by nlinarith) ?_).1
    have key : (1 + (β1 - 1)) * (α4 * (1 - β6) + lam * δ) + (1 + (β1 - 1) + β6 * lq - β6) * (-α4 + lam * 0) =
        -β6 * (1 - lam) * (α1 + α4 * (β1 - 1)) := by
      rw [hlqdef]; linear_combination lam * hδ + (-β6 * α1) * hκα
    rw [key]
    nlinarith [mul_pos (mul_pos hβ6 (sub_pos.2 h1)) (by nlinarith : (0:ℝ) < α1 + α4 * (β1 - 1))]
  · intro y hy hyx
    have hV : y = fpoint (b - d) (c - d) (b' - a') d (1 + (β1 - 1) + β6 * lq, -(β1 - 1), lq) ∨
        y = fpoint (b - d) (c - d) (b' - a') d (β6, 1, 1) ∨ y = fpoint (b - d) (c - d) (b' - a') d (0, 1, 0) ∨
        y = fpoint (b - d) (c - d) (b' - a') d (0, 0, 0) ∨ y = fpoint (b - d) (c - d) (b' - a') d (β6 * κ, -μ, κ) ∨
        y = fpoint (b - d) (c - d) (b' - a') d (1, 0, 0) ∨ y = fpoint (b - d) (c - d) (b' - a') d (β6, 1, 0) := by
      rw [Ec', Eb', Ec, Ed, Ea, Eb, Ea']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [k17gbY9, pc5_0])).elim
    · exact (hyx 1 (by simp only [k17gbY9, pc5_1])).elim
    · exact (hyx 2 (by simp only [k17gbY9, pc5_2])).elim
    · exact (hyx 3 (by simp only [k17gbY9, pc5_3])).elim
    · exact (hyx 4 (by simp only [k17gbY9, pc5_4])).elim
    · refine ⟨_, rfl, fun lam h0 h1 D hD i => ?_⟩
      refine (k17gb_s19_tsc hD hm hκ hκ1 hμ hlq hrel hβ6 hβ61 (by nlinarith) ?_).2 _ (by simp) i
      have key : (1 + (β1 - 1)) * (α4 * (1 - β6) + lam * δ) + (1 + (β1 - 1) + β6 * lq - β6) * (-α4 + lam * 0) =
          -β6 * (1 - lam) * (α1 + α4 * (β1 - 1)) := by
        rw [hlqdef]; linear_combination lam * hδ + (-β6 * α1) * hκα
      rw [key]
      nlinarith [mul_pos (mul_pos hβ6 (sub_pos.2 h1)) (by nlinarith : (0:ℝ) < α1 + α4 * (β1 - 1))]
    · refine ⟨_, rfl, fun lam h0 h1 D hD i => ?_⟩
      refine (k17gb_s19_tsc hD hm hκ hκ1 hμ hlq hrel hβ6 hβ61 (by nlinarith) ?_).2 _ (by simp) i
      have key : (1 + (β1 - 1)) * (α4 * (1 - β6) + lam * δ) + (1 + (β1 - 1) + β6 * lq - β6) * (-α4 + lam * 0) =
          -β6 * (1 - lam) * (α1 + α4 * (β1 - 1)) := by
        rw [hlqdef]; linear_combination lam * hδ + (-β6 * α1) * hκα
      rw [key]
      nlinarith [mul_pos (mul_pos hβ6 (sub_pos.2 h1)) (by nlinarith : (0:ℝ) < α1 + α4 * (β1 - 1))]
  · intro lam h0 h1 w hw hinj
    refine k17gb_lex5_s19 _ w hinj ?_ ?_ ?_
    · right
      refine ⟨?_, ?_⟩
      · simp only [k17gbY9, pc5_0, pc5_4, Ea, Ec']; exact hz1.symm
      · rw [hw, hw]
        simp only [k17gbY9, pc5_0, pc5_4, Ea, Ec']
        have hV : fcomb (b - d) (c - d) (b' - a') (α4 * (1 - β6) + lam * δ) (-α4 + lam * 0) 0 =
            (α4 * (1 - β6) + lam * δ) • (b - d) + (-α4 + lam * 0) • (c - d) := by simp [fcomb]
        rw [hV, ← sub_neg, ← inner_sub_left]
        simp only [inner_add_right, inner_smul_right, hw1]
        have : (α4 * (1 - β6) + lam * δ) + (-α4 + lam * 0) * (1 - β6) = lam * δ := by ring
        nlinarith [mul_pos h0 hδ0]
    · rcases hF1 with h | h
      · left; left; simp only [k17gbY9, pc5_1, pc5_2, Ec, Eb']; exact h
      · right; left; simp only [k17gbY9, pc5_2, pc5_3, Ec, Ed]; exact h
    · rcases hF2 with h | h
      · left; left; simp only [k17gbY9, pc5_2, pc5_3, Ec, Ed]; exact h
      · right; left; simp only [k17gbY9, pc5_3, pc5_4, Ed, Ea]; exact h

end C2
end Type08Sp
end Minimality
