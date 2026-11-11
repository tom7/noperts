module

public import Mathlib
public import MinimalityExtra
public import Minimality.ClusterLimit

/-!
# The Cluster Limit Lemma

Proof of `ClusterLimitLemma` of `MinimalityExtra.lean`, from `Minimality.clusterLimit`
(Minimality/ClusterLimit.lean). The off-plane hypothesis `det3 ... ≠ 0` is the triple product
`⟪cross (x₁ - x₀) (x₂ - x₀), p - x₀⟫ ≠ 0`.
-/

@[expose] public section

open scoped RealInnerProductSpace

namespace MinimalityExtra

/-- Proof of `ClusterLimitLemma`. -/
theorem clusterLimitLemma : ClusterLimitLemma := by
  intro x₀ x₁ x₂ p hT
  obtain ⟨R, hR, -, hρ, hV⟩ := Minimality.clusterLimit x₀ x₁ x₂ p (by
    intro h
    apply hT
    rw [← h]
    simp only [det3, Minimality.cross, PiLp.inner_apply]
    simp [Fin.sum_univ_three]
    ring)
  exact ⟨_, hρ, hV⟩

end MinimalityExtra
