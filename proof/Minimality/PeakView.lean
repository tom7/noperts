module

public import Mathlib

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace

namespace Minimality.PeakView

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Lemma Pk, part 1 (local to global for a linear depth). `S` lies in `J + cone(K - J : K ∈ N)`
(what the facet description at the vertex `J` gives, `N` = neighbours).  If the depth `⟪·, w⟫`
drops along every `K - J`, then `J` is the unique maximum of the depth on `S`. -/
theorem peak_of_cone (S N : Finset V) (J w : V) (hS : ∀ x ∈ S, ∃ c : V → ℝ,
    (∀ K ∈ N, 0 ≤ c K) ∧ x - J = ∑ K ∈ N, c K • (K - J))
    (hw : ∀ K ∈ N, ⟪K - J, w⟫ < 0) : ∀ x ∈ S, x ≠ J → ⟪x, w⟫ < ⟪J, w⟫ := by
  intro x hx hne
  obtain ⟨c, hc, hxc⟩ := hS x hx
  have h1 : ⟪x - J, w⟫ = ∑ K ∈ N, c K * ⟪K - J, w⟫ := by
    rw [hxc, sum_inner]; simp [inner_smul_left]
  have h2 : ∃ K ∈ N, 0 < c K := by
    by_contra h
    push Not at h
    apply hne
    have : ∀ K ∈ N, c K = 0 := fun K hK => le_antisymm (h K hK) (hc K hK)
    have h0 : x - J = 0 := by
      rw [hxc]; exact Finset.sum_eq_zero fun K hK => by simp [this K hK]
    exact sub_eq_zero.mp h0
  obtain ⟨K0, hK0, hpos⟩ := h2
  have h3 : ∑ K ∈ N, c K * ⟪K - J, w⟫ < 0 := by
    apply Finset.sum_neg'
    · intro K hK; exact mul_nonpos_of_nonneg_of_nonpos (hc K hK) (hw K hK).le
    · exact ⟨K0, hK0, mul_neg_of_pos_of_neg hpos (hw K0 hK0)⟩
  have : ⟪x - J, w⟫ < 0 := h1 ▸ h3
  rw [inner_sub_left] at this
  linarith

/-- Lemma Pk, part 2 (angle criterion at the edge view `w = J - p`).  `p ∈ N` is a neighbour of `J`
and for every other neighbour `K` the angle `(p, J, K)` is acute (`0 < ⟪p - J, K - J⟫`).
Then `J` is the unique deepest point of `S` at the view `J - p`. -/
theorem peak_edge_view (S N : Finset V) (J p : V) (hp : p ∈ N) (hpJ : p ≠ J)
    (hS : ∀ x ∈ S, ∃ c : V → ℝ, (∀ K ∈ N, 0 ≤ c K) ∧ x - J = ∑ K ∈ N, c K • (K - J))
    (hacute : ∀ K ∈ N, K ≠ p → 0 < ⟪p - J, K - J⟫) :
    ∀ x ∈ S, x ≠ J → ⟪x, J - p⟫ < ⟪J, J - p⟫ := by
  apply peak_of_cone S N J (J - p) hS
  intro K hK
  by_cases hKp : K = p
  · subst hKp
    have : 0 < ⟪K - J, K - J⟫ := real_inner_self_pos.mpr (sub_ne_zero.mpr hpJ)
    have e : ⟪K - J, J - K⟫ = -⟪K - J, K - J⟫ := by
      rw [← inner_neg_right, neg_sub]
    linarith
  · have h := hacute K hK hKp
    have e : ⟪K - J, J - p⟫ = -⟪p - J, K - J⟫ := by
      rw [real_inner_comm, ← inner_neg_left, neg_sub]
    linarith

/-- The same at all views near `J - p`: strict drop along the finitely many `K - J` is open. -/
theorem peak_edge_view_eventually (S N : Finset V) (J p : V) (hp : p ∈ N) (hpJ : p ≠ J)
    (hS : ∀ x ∈ S, ∃ c : V → ℝ, (∀ K ∈ N, 0 ≤ c K) ∧ x - J = ∑ K ∈ N, c K • (K - J))
    (hacute : ∀ K ∈ N, K ≠ p → 0 < ⟪p - J, K - J⟫) :
    ∀ᶠ w in nhds (J - p), ∀ x ∈ S, x ≠ J → ⟪x, w⟫ < ⟪J, w⟫ := by
  have hw : ∀ K ∈ N, ⟪K - J, J - p⟫ < 0 := by
    intro K hK
    by_cases hKp : K = p
    · subst hKp
      have : 0 < ⟪K - J, K - J⟫ := real_inner_self_pos.mpr (sub_ne_zero.mpr hpJ)
      have e : ⟪K - J, J - K⟫ = -⟪K - J, K - J⟫ := by
        rw [← inner_neg_right, neg_sub]
      linarith
    · have h := hacute K hK hKp
      have e : ⟪K - J, J - p⟫ = -⟪p - J, K - J⟫ := by
        rw [real_inner_comm, ← inner_neg_left, neg_sub]
      linarith
  have : ∀ᶠ w in nhds (J - p), ∀ K ∈ N, ⟪K - J, w⟫ < 0 := by
    rw [Filter.eventually_all_finset]
    intro K hK
    have hc : Continuous fun w : V => ⟪K - J, w⟫ := continuous_const.inner continuous_id
    exact (hc.continuousAt.eventually (gt_mem_nhds (hw K hK)))
  exact this.mono fun w hw' => peak_of_cone S N J w hS hw'

end Minimality.PeakView
