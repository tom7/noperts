module

public import Minimality.MaxwellRadonH
public import Minimality.Thm73

@[expose] public section


namespace Minimality.MRB

open Real Finset

theorem mrb_localmax (zz : ℕ → ℝ) (hadj : ∀ n, zz n ≠ zz (n + 1)) (s e : ℕ) (hs : 1 ≤ s)
    (hse : s ≤ e) (hl : zz (s - 1) < zz s) (hr : zz (e + 1) < zz e) :
    ∃ m, s ≤ m ∧ m ≤ e ∧ zz (m - 1) < zz m ∧ zz (m + 1) < zz m := by
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (Finset.Icc s e) zz ⟨s, by simp [hse]⟩
  rw [Finset.mem_Icc] at hm
  refine ⟨m, hm.1, hm.2, ?_, ?_⟩
  · by_cases h : m = s
    · subst h; exact hl
    · have := hmax (m - 1) (by rw [Finset.mem_Icc]; omega)
      have h2 := hadj (m - 1)
      rw [show m - 1 + 1 = m by omega] at h2
      exact lt_of_le_of_ne this h2
  · by_cases h : m = e
    · subst h; exact hr
    · have := hmax (m + 1) (by rw [Finset.mem_Icc]; omega)
      exact lt_of_le_of_ne this (hadj m).symm

/-- A cyclically unimodal (injective, one strict local maximum) depth cycle has no crown. -/
theorem mrb_not_crown_of_unimodal {r : ℕ} [NeZero r] (hr : 2 ≤ r) (z : ℕ → ℝ)
    (hu : Minimality.IsCyclicUnimodal (fun i : ZMod r => z i.val)) :
    ¬ mrb_crown r (fun k => z k - z ((k + 1) % r)) := by
  rintro ⟨a, b, c, d, hab, hbc, hcd, hd, h⟩
  set zz : ℕ → ℝ := fun n => z (n % r) with hzz
  have hcast : ∀ n : ℕ, z ((n : ZMod r).val) = zz n := by
    intro n; simp [hzz, ZMod.val_natCast]
  haveI : Fact (1 < r) := ⟨by omega⟩
  have hadj : ∀ n, zz n ≠ zz (n + 1) := by
    intro n hn
    rw [← hcast, ← hcast] at hn
    have h2 := hu.1 hn
    push_cast at h2
    have h3 : (1 : ZMod r) = 0 := by simpa using h2.symm
    exact one_ne_zero h3
  -- two distinct local maxima contradict unimodality
  have hcontra : ∀ m1 m2 : ℕ, 1 ≤ m1 → 1 ≤ m2 → zz (m1 - 1) < zz m1 → zz (m1 + 1) < zz m1 →
      zz (m2 - 1) < zz m2 → zz (m2 + 1) < zz m2 → m1 % r ≠ m2 % r → False := by
    intro m1 m2 h1 h2 a1 a2 b1 b2 hne
    have mem : ∀ m : ℕ, 1 ≤ m → zz (m - 1) < zz m → zz (m + 1) < zz m →
        (m : ZMod r) ∈ Finset.univ.filter
          (fun i : ZMod r => z (i - 1).val < z i.val ∧ z (i + 1).val < z i.val) := by
      intro m hm p1 p2
      have e1 : (m : ZMod r) - 1 = ((m - 1 : ℕ) : ZMod r) := by
        rw [Nat.cast_sub hm]; simp
      have e2 : (m : ZMod r) + 1 = ((m + 1 : ℕ) : ZMod r) := by push_cast; ring
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [e1, e2, hcast, hcast, hcast]
      exact ⟨p1, p2⟩
    obtain ⟨x, hx⟩ := Finset.card_eq_one.1 hu.2
    have q1 := mem m1 h1 a1 a2
    have q2 := mem m2 h2 b1 b2
    rw [hx, Finset.mem_singleton] at q1 q2
    have : (m1 : ZMod r) = (m2 : ZMod r) := q1.trans q2.symm
    exact hne ((ZMod.natCast_eq_natCast_iff' m1 m2 r).1 this)
  have hmod_lt : ∀ n, n < r → n % r = n := fun n hn => Nat.mod_eq_of_lt hn
  have hδ : ∀ k, k < r → z k - z ((k + 1) % r) = zz k - zz (k + 1) := by
    intro k hk; simp only [hzz]; rw [Nat.mod_eq_of_lt hk]
  have per : ∀ n, zz (r + n) = zz n := by intro n; simp only [hzz]; rw [Nat.add_mod_left]
  beta_reduce at h
  rcases h with ⟨ha, hb, hc, hd'⟩ | ⟨ha, hb, hc, hd'⟩
  · have ha' := hδ a (by omega)
    have hb' := hδ b (by omega)
    have hc' := hδ c (by omega)
    have hd'' := hδ d (by omega)
    obtain ⟨m1, h1, h2, h3, h4⟩ := mrb_localmax zz hadj (b + 1) c (by omega) (by omega)
      (by simp only [Nat.add_sub_cancel]; linarith) (by linarith)
    obtain ⟨m2, g1, g2, g3, g4⟩ := mrb_localmax zz hadj (d + 1) (r + a) (by omega) (by omega)
      (by simp only [Nat.add_sub_cancel]; linarith)
      (by rw [show r + a + 1 = r + (a + 1) by ring, per, per]; linarith)
    refine hcontra m1 m2 (by omega) (by omega) h3 h4 g3 g4 ?_
    rw [Nat.mod_eq_of_lt (by omega : m1 < r)]
    by_cases hm : m2 < r
    · rw [Nat.mod_eq_of_lt hm]; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega : m2 - r < r)]; omega
  · have ha' := hδ a (by omega)
    have hb' := hδ b (by omega)
    have hc' := hδ c (by omega)
    have hd'' := hδ d (by omega)
    obtain ⟨m1, h1, h2, h3, h4⟩ := mrb_localmax zz hadj (a + 1) b (by omega) (by omega)
      (by simp only [Nat.add_sub_cancel]; linarith) (by linarith)
    obtain ⟨m2, g1, g2, g3, g4⟩ := mrb_localmax zz hadj (c + 1) d (by omega) (by omega)
      (by simp only [Nat.add_sub_cancel]; linarith) (by linarith)
    refine hcontra m1 m2 (by omega) (by omega) h3 h4 g3 g4 ?_
    rw [Nat.mod_eq_of_lt (by omega : m1 < r), Nat.mod_eq_of_lt (by omega : m2 < r)]; omega

/-- With a unimodal injective depth cycle, no balanced load exists (z would be constant). -/
theorem mrb_no_balanced_of_unimodal (r : ℕ) [NeZero r] (hr : 2 ≤ r) (θ L z : ℕ → ℝ)
    (hθ : ∀ i j, i < j → j < r → θ i < θ j)
    (hwin : θ (r - 1) < θ 0 + 2 * π)
    (hL : ∀ k, k < r → 0 < L k)
    (hF1 : ∑ k ∈ Finset.range r, L k * cos (θ k) = 0)
    (hF2 : ∑ k ∈ Finset.range r, L k * sin (θ k) = 0)
    (hM1 : ∑ k ∈ Finset.range r, z k * (L k * cos (θ k)) = 0)
    (hM2 : ∑ k ∈ Finset.range r, z k * (L k * sin (θ k)) = 0)
    (hu : Minimality.IsCyclicUnimodal (fun i : ZMod r => z i.val)) : False := by
  have hlev := mrb_level_of_no_crown r hr θ L z hθ hwin hL hF1 hF2 hM1 hM2
    (mrb_not_crown_of_unimodal hr z hu)
  haveI : Fact (1 < r) := ⟨by omega⟩
  have h0 := hlev 0 (by omega)
  have h1 := hlev 1 (by omega)
  have := hu.1 (a₁ := ((1 : ℕ) : ZMod r)) (a₂ := ((0 : ℕ) : ZMod r))
    (by simp only [ZMod.val_natCast]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; rw [h1])
  simp at this

end Minimality.MRB
