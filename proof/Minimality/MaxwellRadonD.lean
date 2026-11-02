module

public import Minimality.MaxwellRadonC

@[expose] public section


namespace Minimality.MRB

open Real Finset

/-- A crown: four cyclically ordered indices where `δ` alternates in sign. -/
def mrb_crown (r : ℕ) (δ : ℕ → ℝ) : Prop :=
  ∃ a b c d, a < b ∧ b < c ∧ c < d ∧ d < r ∧
    ((0 < δ a ∧ δ b < 0 ∧ 0 < δ c ∧ δ d < 0) ∨ (δ a < 0 ∧ 0 < δ b ∧ δ c < 0 ∧ 0 < δ d))

theorem mrb_chordA (r : ℕ) (X Y δ : ℕ → ℝ)
    (hO : ∀ i j k, i < j → j < k → k < r → 0 < mrb_O X Y i j k)
    (hne : ∀ i j, i < j → j < r → ¬ (X i = X j ∧ Y i = Y j))
    (h0 : ∑ k ∈ Finset.range r, δ k = 0)
    (hX : ∑ k ∈ Finset.range r, δ k * X k = 0)
    (hY : ∑ k ∈ Finset.range r, δ k * Y k = 0)
    {i j : ℕ} (hij : i < j) (hj : j < r)
    (hin : ∀ k, i < k → k < j → δ k ≤ 0)
    (hout : ∀ k, k < r → (k < i ∨ j < k) → 0 ≤ δ k) :
    ∀ k, k < r → δ k = 0 := by
  have hsum : ∑ k ∈ Finset.range r, δ k * mrb_O X Y i j k = 0 := by
    have : ∀ k, δ k * mrb_O X Y i j k = (X j - X i) * (δ k * Y k) - (Y j - Y i) * (δ k * X k)
        - ((X j - X i) * Y i - (Y j - Y i) * X i) * δ k := by
      intro k; unfold mrb_O; ring
    simp_rw [this]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, h0, hX, hY]; ring
  have hnn : ∀ k ∈ Finset.range r, 0 ≤ δ k * mrb_O X Y i j k := by
    intro k hk
    have hkr := Finset.mem_range.1 hk
    rcases lt_trichotomy k i with h | h | h
    · have := hO k i j h hij hj
      have h2 : mrb_O X Y i j k = mrb_O X Y k i j := by unfold mrb_O; ring
      rw [h2]; exact mul_nonneg (hout k hkr (Or.inl h)) this.le
    · subst h; have : mrb_O X Y k j k = 0 := by unfold mrb_O; ring
      rw [this]; simp
    · rcases lt_trichotomy k j with h' | h' | h'
      · have := hO i k j h h' hj
        have h2 : mrb_O X Y i j k = -mrb_O X Y i k j := by unfold mrb_O; ring
        rw [h2]; exact mul_nonneg_of_nonpos_of_nonpos (hin k h h') (by linarith)
      · subst h'; have : mrb_O X Y i k k = 0 := by unfold mrb_O; ring
        rw [this]; simp
      · exact mul_nonneg (hout k hkr (Or.inr h')) (hO i j k hij h' hkr).le
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum
  have hz2 : ∀ k, k < r → k ≠ i → k ≠ j → δ k = 0 := by
    intro k hkr h1 h2
    have := hz k (Finset.mem_range.2 hkr)
    have hne0 : mrb_O X Y i j k ≠ 0 := by
      rcases lt_or_gt_of_ne h1 with h | h
      · have := hO k i j h hij hj
        have h2 : mrb_O X Y i j k = mrb_O X Y k i j := by unfold mrb_O; ring
        rw [h2]; exact this.ne'
      · rcases lt_or_gt_of_ne h2 with h' | h'
        · have := hO i k j h h' hj
          have h2 : mrb_O X Y i j k = -mrb_O X Y i k j := by unfold mrb_O; ring
          rw [h2]; exact (neg_ne_zero.2 this.ne')
        · exact (hO i j k hij h' hkr).ne'
    exact (mul_eq_zero.1 this).resolve_right hne0
  have s0 : ∑ k ∈ Finset.range r, δ k = δ i + δ j :=
    Finset.sum_eq_add i j hij.ne (fun c hc h => hz2 c (Finset.mem_range.1 hc) h.1 h.2)
      (fun h => absurd (Finset.mem_range.2 (by omega)) h) (fun h => absurd (Finset.mem_range.2 hj) h)
  have sX : ∑ k ∈ Finset.range r, δ k * X k = δ i * X i + δ j * X j :=
    Finset.sum_eq_add i j hij.ne (fun c hc h => by rw [hz2 c (Finset.mem_range.1 hc) h.1 h.2]; ring)
      (fun h => absurd (Finset.mem_range.2 (by omega)) h) (fun h => absurd (Finset.mem_range.2 hj) h)
  have sY : ∑ k ∈ Finset.range r, δ k * Y k = δ i * Y i + δ j * Y j :=
    Finset.sum_eq_add i j hij.ne (fun c hc h => by rw [hz2 c (Finset.mem_range.1 hc) h.1 h.2]; ring)
      (fun h => absurd (Finset.mem_range.2 (by omega)) h) (fun h => absurd (Finset.mem_range.2 hj) h)
  have hδi : δ i = 0 := by
    by_contra hd
    apply hne i j hij hj
    have hj' : δ j = -δ i := by linarith
    have t1 : δ i * X i + δ j * X j = 0 := by rw [← sX]; exact hX
    have t2 : δ i * Y i + δ j * Y j = 0 := by rw [← sY]; exact hY
    rw [hj'] at t1 t2
    have e1 : δ i * (X i - X j) = 0 := by linear_combination t1
    have e2 : δ i * (Y i - Y j) = 0 := by linear_combination t2
    constructor
    · have := (mul_eq_zero.1 e1).resolve_left hd; linarith
    · have := (mul_eq_zero.1 e2).resolve_left hd; linarith
  have hδj : δ j = 0 := by linarith
  intro k hk
  by_cases h1 : k = i
  · rw [h1]; exact hδi
  by_cases h2 : k = j
  · rw [h2]; exact hδj
  exact hz2 k hk h1 h2

end Minimality.MRB
