module

public import Minimality.SecondOrder
public import Mathlib.Topology.Algebra.Polynomial

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace Topology
open Filter Polynomial

namespace Minimality

/-- A real polynomial with negative trailing coefficient is eventually negative on `0⁺`. -/
theorem cayleyJet_eventually_neg (p : ℝ[X]) (hp : p.trailingCoeff < 0) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), p.eval s < 0 := by
  have hne : p ≠ 0 := by rintro rfl; simp at hp
  set k := p.natTrailingDegree with hk
  have hdvd : (X : ℝ[X]) ^ k ∣ p := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hd
  obtain ⟨q, hq⟩ := hdvd
  have hq0 : q.eval 0 < 0 := by
    have : p.coeff k = q.coeff 0 := by
      rw [hq]; simpa using Polynomial.coeff_X_pow_mul q k 0
    rw [← Polynomial.coeff_zero_eq_eval_zero, ← this]
    exact hp
  have hc : ContinuousAt (fun s => q.eval s) 0 := q.continuousAt
  have ht := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
  filter_upwards [ht.eventually_lt_const hq0, self_mem_nhdsWithin] with s hs hs0
  have hs0' : (0:ℝ) < s := hs0
  rw [hq, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  exact mul_neg_of_pos_of_neg (by positivity) hs

end Minimality
