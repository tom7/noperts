module

public import Minimality.Basic

@[expose] public section

/-!
# Parity of parallel systems: the discrete core

FEWER-FACES-PROOFS.md, Proposition 8.2: at a generic view the number of
parallel force systems (a silhouette edge and its antipodal corner at a depth
strictly between the edge's endpoint depths) is odd. The rotating-calipers walk
over the antipodal vertex pairs (front `f`, back `b`) takes exactly one step per
edge over a half turn, ends at the reversed pair, and changes the sign of
`z f - z b` exactly at the parallel systems; so the statement reduces to the
fact below (`odd_card_sign_changes`). The geometric half (the walk) is not yet
formalized.
-/

namespace Minimality

open Finset

/-- A sequence of nonzero reals that ends at the negative of its start changes sign
an odd number of times. -/
theorem odd_card_sign_changes (g : ℕ → ℝ) (m : ℕ) (hg : ∀ t ≤ m, g t ≠ 0) (hm : g m = -g 0) :
    Odd ((range m).filter (fun t => g t * g (t + 1) < 0)).card := by
  -- parity of sign changes up to n records whether g n has the sign of g 0
  have key : ∀ n ≤ m, (Even ((range n).filter (fun t => g t * g (t + 1) < 0)).card ↔
      0 < g 0 * g n) := by
    intro n hn
    induction n with
    | zero =>
      simp only [range_zero, filter_empty, card_empty]
      simp only [Even.zero, true_iff]
      exact mul_self_pos.mpr (hg 0 (Nat.zero_le _))
    | succ n ih =>
      have ih := ih (by omega)
      have h0 := hg 0 (Nat.zero_le _); have hn' := hg n (by omega); have hn1 := hg (n + 1) hn
      rw [range_add_one, filter_insert]
      by_cases hc : g n * g (n + 1) < 0
      · rw [if_pos hc, card_insert_of_notMem (by simp), Nat.even_add_one, ih]
        constructor
        · intro h; by_contra h'; push_neg at h'
          have : 0 < g 0 * g n * (g n * g (n + 1)) := by nlinarith [mul_pos (mul_self_pos.mpr hn') (mul_self_pos.mpr h0)]
          nlinarith [sq_nonneg (g n), mul_self_pos.mpr hn']
        · intro h h2; nlinarith [mul_self_pos.mpr hn']
      · rw [if_neg hc, ih]
        push_neg at hc
        have hc' : 0 < g n * g (n + 1) := lt_of_le_of_ne hc (fun e => (mul_ne_zero hn' hn1) e.symm)
        constructor
        · intro h; nlinarith [mul_self_pos.mpr hn']
        · intro h; nlinarith [mul_self_pos.mpr hn']
  have := (key m le_rfl).not
  rw [hm] at this
  have h0 := hg 0 (Nat.zero_le _)
  have : ¬ Even ((range m).filter (fun t => g t * g (t + 1) < 0)).card := by
    rw [key m le_rfl, hm]; nlinarith [mul_self_pos.mpr h0]
  exact Nat.not_even_iff_odd.mp this

end Minimality

end
