module

public import Minimality.MaxwellRadonE

@[expose] public section


namespace Minimality.MRB

open Real Finset

theorem mrb_abel (z e : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), z k * e k =
      ∑ k ∈ Finset.range (n + 1), (z k - z (k + 1)) * (∑ m ∈ Finset.range (k + 1), e m)
        + z (n + 1) * (∑ m ∈ Finset.range (n + 1), e m) := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun k => (z k - z (k + 1)) *
      (∑ m ∈ Finset.range (k + 1), e m)) (n + 1), Finset.sum_range_succ e (n + 1)]
    ring

theorem mrb_rot (z : ℕ → ℝ) (s : ℕ) :
    ∑ k ∈ Finset.range (s + 1), z ((k + 1) % (s + 1)) = ∑ k ∈ Finset.range (s + 1), z k := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ' z]
  have : ∀ k ∈ Finset.range s, z ((k + 1) % (s + 1)) = z (k + 1) := by
    intro k hk
    rw [Nat.mod_eq_of_lt (by have := Finset.mem_range.1 hk; omega)]
  rw [Finset.sum_congr rfl this]
  simp

theorem mrb_delta_moment (r : ℕ) (hr : 1 ≤ r) (z e : ℕ → ℝ)
    (hclose : ∑ m ∈ Finset.range r, e m = 0) (hmom : ∑ k ∈ Finset.range r, z k * e k = 0) :
    ∑ k ∈ Finset.range r, (z k - z ((k + 1) % r)) * (∑ m ∈ Finset.range (k + 1), e m) = 0 := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have h := mrb_abel z e s
  rw [hclose, hmom, mul_zero, add_zero] at h
  rw [h]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  by_cases h1 : k + 1 < s + 1
  · rw [Nat.mod_eq_of_lt h1]
  · have : k = s := by omega
    subst this
    rw [hclose]; ring

theorem mrb_delta_zero (z : ℕ → ℝ) (s : ℕ) :
    ∑ k ∈ Finset.range (s + 1), (z k - z ((k + 1) % (s + 1))) = 0 := by
  rw [Finset.sum_sub_distrib, mrb_rot]; ring

end Minimality.MRB
