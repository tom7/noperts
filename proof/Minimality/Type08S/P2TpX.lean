module

public import Minimality.Type08S.P2TpT

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# Lemma T′X (package 7, P1′a)  — sp08f §5
At `T'` (and `Norm08`), `K` is Rupert, with any HDNs and ties, unless the `ℓ`-maximum of `Q_ac` is attained
both in `{d, c}` and in `{a, b'}` (`QacTop`).  Theorem 24.1 at the view `ℓ = b - d` with the two mixed
sector cells `C1` (rim `(d,a,b',c,a',b)`), `C2` (rim `(d,a,c',b',c)`).
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

theorem max_aff (ν k x y : ℝ) (hν : 0 < ν) :
    max (ν * (k + x)) (ν * (k + y)) = ν * k + ν * max x y := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, max_eq_right (by nlinarith)]; ring
  · rw [max_eq_left h, max_eq_left (by nlinarith)]; ring

set_option maxHeartbeats 1600000 in
/-- **Lemma T′X.** -/
theorem close_Tp_X {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (hT' : IsT' a b c' d) (hq : ¬ QacTop a b b' c d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨e1, e2, e3, o, ν, v1, C0, w1, ha, w3, α4, β1, γ4, β6, γ6, hF, hν, hv1, hha, hα4, hγ4,
    hE, hβ1, hβ6, hγ6, hγ61, hcv, hu, hd, hb, hc, haa, ha', hb', hc', hiw, hiC⟩ := hTp_setup' N hT'
  -- the top of `Q_ac` in frame coordinates
  have hm : max 0 C0 ≠ max w3 (α4 * w3 + γ4 * C0) := by
    intro heq
    apply hq
    have key : ∀ x : ℝ³, ⟪x, b - d⟫ = ν * ⟪x, e3⟫ := by
      intro x; rw [hu, real_inner_smul_right]
    unfold QacTop
    rw [key, key, key, key, hd, hc, haa, hb', inner_pt_3 hF, inner_pt_3 hF, inner_pt_3 hF,
      inner_pt_3 hF, max_aff _ _ _ _ hν, max_aff _ _ _ _ hν]
    rw [← heq]
  have hσ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ σ * v1 < 0 := by
    rcases lt_or_gt_of_ne hv1 with h | h
    · exact ⟨1, Or.inl rfl, by linarith⟩
    · exact ⟨-1, Or.inr rfl, by linarith⟩
  obtain ⟨σ, hσ, hvσ⟩ := hσ
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hmem : ∀ p : ℝ³, (p = d ∨ p = a ∨ p = a' ∨ p = b ∨ p = b' ∨ p = c ∨ p = c') →
      p ∈ insert d ({a, a', b, b', c, c'} : Finset ℝ³) := by
    intro p hp; simp only [mem_insert, mem_singleton]; tauto
  have hVs : ∀ y ∈ insert d ({a, a', b, b', c, c'} : Finset ℝ³),
      y = d ∨ y = a ∨ y = a' ∨ y = b ∨ y = b' ∨ y = c ∨ y = c' := by
    intro y hy; simp only [mem_insert, mem_singleton] at hy; tauto
  rcases lt_or_gt_of_ne hm with hlt | hgt
  · -- top of `Q_ac` in `{a, b'}` : cell C2
    obtain ⟨t1, hp, h2, hne⟩ := exists_t_C2 (w1 := w1) hσσ hvσ hha hα4 hγ4
    refine tpX_C2 hF o hσ hν hha hα4 hγ4 hE hβ1 hβ6 hγ6 hγ61 hvσ hp (t1 := t1) (t2 := -1)
      (by norm_num) h2 hlt (Or.inr hne) _ ?_ ?_ ?_ ?_ ?_ ?_
    · intro y hy
      rcases hVs y hy with h | h | h | h | h | h | h <;> rw [h]
      · exact Or.inl hd
      · exact Or.inr (Or.inl haa)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha')))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hb)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hb')))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc))))
      · exact Or.inr (Or.inr (Or.inl hc'))
    · rw [← hd]; exact hmem _ (by simp)
    · rw [← haa]; exact hmem _ (by simp)
    · rw [← hc']; exact hmem _ (by simp)
    · rw [← hb']; exact hmem _ (by simp)
    · rw [← hc]; exact hmem _ (by simp)
  · -- top of `Q_ac` in `{d, c}` : cell C1
    obtain ⟨t1, ht1, hp, h2⟩ := exists_t_C1 (w1 := w1) hσσ hvσ hha hα4 hγ4
    refine tpX_C1 hF o hσ hν hha hα4 hγ4 hE hβ1 hβ6 hγ6 hγ61 hcv hvσ hp (t1 := t1) (t2 := 1)
      (by norm_num) ht1 h2 hgt _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro y hy
      rcases hVs y hy with h | h | h | h | h | h | h <;> rw [h]
      · exact Or.inl hd
      · exact Or.inr (Or.inl haa)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha'))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb)))))
      · exact Or.inr (Or.inr (Or.inl hb'))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hc)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hc')))))
    · rw [← hd]; exact hmem _ (by simp)
    · rw [← haa]; exact hmem _ (by simp)
    · rw [← hb']; exact hmem _ (by simp)
    · rw [← hc]; exact hmem _ (by simp)
    · rw [← ha']; exact hmem _ (by simp)
    · rw [← hb]; exact hmem _ (by simp)

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.close_Tp_X
