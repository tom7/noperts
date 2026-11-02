module

public import Minimality.MaxwellRadonF

@[expose] public section


namespace Minimality.MRB

open Real Finset

/-- **Lemma MR-B** (balanced loads are level or crowned).  Normals at strictly increasing angles
`θ 0 < … < θ (r-1)` (within a window of length `< 2π`, e.g. in `[0, 2π)`), weights `L k > 0`, depths
`z k`; zero force and zero depth moment.  Then either all `z k` are equal, or `δ k = z k - z (k+1)`
(cyclically) has a crown: indices `a < b < c < d < r` with `δ a > 0, δ b < 0, δ c > 0, δ d < 0`
(or the opposite signs), i.e. z falls, rises, falls, rises. -/
theorem mrb_main (r : ℕ) (hr : 2 ≤ r) (θ L z : ℕ → ℝ)
    (hθ : ∀ i j, i < j → j < r → θ i < θ j)
    (hwin : θ (r - 1) < θ 0 + 2 * π)
    (hL : ∀ k, k < r → 0 < L k)
    (hF1 : ∑ k ∈ Finset.range r, L k * cos (θ k) = 0)
    (hF2 : ∑ k ∈ Finset.range r, L k * sin (θ k) = 0)
    (hM1 : ∑ k ∈ Finset.range r, z k * (L k * cos (θ k)) = 0)
    (hM2 : ∑ k ∈ Finset.range r, z k * (L k * sin (θ k)) = 0) :
    (∀ k, k < r → z k = z 0) ∨ mrb_crown r (fun k => z k - z ((k + 1) % r)) := by
  have hmono : ∀ i j, i ≤ j → j < r → θ i ≤ θ j := by
    intro i j h1 h2
    rcases h1.lt_or_eq with h | h
    · exact (hθ i j h h2).le
    · rw [h]
  have hwin' : ∀ i j, i < r → j < r → θ i - θ j < 2 * π := by
    intro i j hi hj
    have a1 := hmono i (r - 1) (by omega) (by omega)
    have a2 := hmono 0 j (by omega) hj
    linarith
  have hC1 : mrb_sy L θ (Finset.range r) = 0 := hF1
  have hC2 : mrb_sx L θ (Finset.range r) = 0 := by
    unfold mrb_sx; rw [Finset.sum_neg_distrib, hF2]; simp
  have hO := mrb_orient r θ L hθ hwin' hL hC1 hC2
  -- distinct vertices
  have hne : ∀ i j, i < j → j < r → ¬ (mrb_X L θ i = mrb_X L θ j ∧ mrb_Y L θ i = mrb_Y L θ j) := by
    intro i j hij hj ⟨hx, hy⟩
    by_cases h3 : 3 ≤ r
    · by_cases h1 : j + 1 < r
      · have := hO i j (j + 1) hij (by omega) h1
        unfold mrb_O at this; rw [← hx, ← hy] at this; nlinarith [this]
      · by_cases h2 : 1 ≤ i
        · have := hO (i - 1) i j (by omega) hij hj
          unfold mrb_O at this; rw [← hx, ← hy] at this; nlinarith [this]
        · have := hO i 1 j (by omega) (by omega) hj
          unfold mrb_O at this; rw [← hx, ← hy] at this; nlinarith [this]
    · have hr2 : r = 2 := by omega
      have hi : i = 0 := by omega
      have hj1 : j = 1 := by omega
      subst hi hj1
      subst hr2
      have e1 : mrb_X L θ 1 = 0 := by unfold mrb_X; exact hC2
      have e2 : mrb_Y L θ 1 = 0 := by unfold mrb_Y; exact hC1
      have e3 : mrb_X L θ 0 = -(L 0 * sin (θ 0)) := by simp [mrb_X, mrb_sx]
      have e4 : mrb_Y L θ 0 = L 0 * cos (θ 0) := by simp [mrb_Y, mrb_sy]
      rw [e1, e3] at hx; rw [e2, e4] at hy
      have hl := hL 0 (by omega)
      have := sin_sq_add_cos_sq (θ 0)
      have s0 : L 0 * sin (θ 0) = 0 := by linarith
      have c0 : L 0 * cos (θ 0) = 0 := by linarith
      have : L 0 ^ 2 = 0 := by nlinarith [sin_sq_add_cos_sq (θ 0)]
      have : L 0 = 0 := by simpa using this
      linarith
  set δ : ℕ → ℝ := fun k => z k - z ((k + 1) % r) with hδ
  have hr1 : 1 ≤ r := by omega
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have hdX : ∑ k ∈ Finset.range (s + 1), δ k * mrb_X L θ k = 0 := by
    have := mrb_delta_moment (s + 1) hr1 z (fun m => -(L m * sin (θ m))) hC2
      (by rw [show ∑ k ∈ Finset.range (s + 1), z k * -(L k * sin (θ k)) =
        -∑ k ∈ Finset.range (s + 1), z k * (L k * sin (θ k)) by simp [mul_neg, Finset.sum_neg_distrib], hM2]; simp)
    exact this
  have hdY : ∑ k ∈ Finset.range (s + 1), δ k * mrb_Y L θ k = 0 :=
    mrb_delta_moment (s + 1) hr1 z (fun m => L m * cos (θ m)) hC1 hM1
  have D : MRBData (s + 1) (mrb_X L θ) (mrb_Y L θ) δ :=
    ⟨hO, hne, mrb_delta_zero z s, hdX, hdY⟩
  by_cases hc : mrb_crown (s + 1) δ
  · exact Or.inr hc
  · left
    have hz := mrb_nocrown D hr hc
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      have h1 := hz k (by omega)
      simp only [hδ] at h1
      rw [Nat.mod_eq_of_lt hk] at h1
      rw [← ih (by omega)]; linarith

end Minimality.MRB
