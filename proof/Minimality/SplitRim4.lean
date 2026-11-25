module

public import Minimality.SplitRows
public import Minimality.SilS0XA

@[expose] public section

/-!
# Split rows on a 4-rim give `RobUni` (`Task ED`, Carbon A60 Theorem 1.2(a), `k = 4`)

On any strict 4-rim `X : ZMod 4 → ℝ³` at view `w`, `SplitRows X w a c σ` forces `c` to be the
unique strict maximizer of the height `h(m) = ρ * det3 (X (a + 1) - X a) (X m - X a) w`
among `{a + 2, a + 3}`, which orders the depths `(z a, z (a + 1), z (a + 2), z (a + 3))` so that
`RobUni (fun i => ⟪X i, w⟫)` holds.
-/

set_option autoImplicit false

open scoped RealInnerProductSpace

namespace Minimality.GenPlus

open Minimality Minimality.H21 Minimality.Split

/-- **APPROVED (Task ED).**  On a strict 4-rim (all non-incident vertices strictly on one side of
every rim edge, orientation `ρ`), split rows give robust unimodality: a split cell on a 4-rim is
never needed beyond a lex cell. -/
theorem robUni_of_splitRows4 {X : ZMod 4 → ℝ³} {w : ℝ³} {ρ : ℝ} (hρ : ρ ≠ 0)
    (hcyc : ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 → 0 < ρ * det3 (X (i + 1) - X i) (X j - X i) w)
    {a c : ZMod 4} {σ : ℝ} (hS : SplitRows X w a c σ) : RobUni (fun i => ⟪X i, w⟫) := by
  let z : ZMod 4 → ℝ := fun i => ⟪X i, w⟫
  let h : ZMod 4 → ℝ := fun m => ρ * det3 (X (a + 1) - X a) (X m - X a) w
  let rise : ZMod 4 → ℝ := fun i => det3 (X (i + 1) - X i) (X (a + 1) - X a) w
  have ha2_ne_a : a + 2 ≠ a := by
    intro h0; have : (2 : ZMod 4) = 0 := by linear_combination h0
    revert this; decide
  have ha2_ne_a1 : a + 2 ≠ a + 1 := by
    intro h0; have : (1 : ZMod 4) = 0 := by linear_combination h0
    revert this; decide
  have ha3_ne_a : a + 3 ≠ a := by
    intro h0; have : (3 : ZMod 4) = 0 := by linear_combination h0
    revert this; decide
  have ha3_ne_a1 : a + 3 ≠ a + 1 := by
    intro h0; have : (2 : ZMod 4) = 0 := by linear_combination h0
    revert this; decide
  have ha1_ne_a : a + 1 ≠ a := by
    intro h0; have : (1 : ZMod 4) = 0 := by linear_combination h0
    revert this; decide
  have ha3_ne_a2 : a + 3 ≠ a + 2 := by
    intro h0; have : (1 : ZMod 4) = 0 := by linear_combination h0
    revert this; decide
  have ha11 : a + 1 + 1 = a + 2 := by rw [add_assoc]; rfl
  have ha21 : a + 2 + 1 = a + 3 := by rw [add_assoc]; rfl
  have ha31 : a + 3 + 1 = a := by rw [add_assoc, show (3 + 1 : ZMod 4) = 0 from rfl, add_zero]
  have hh2 : 0 < h (a + 2) := hcyc a (a + 2) ha2_ne_a ha2_ne_a1
  have hh3 : 0 < h (a + 3) := hcyc a (a + 3) ha3_ne_a ha3_ne_a1
  have hrise_a1 : -ρ * rise (a + 1) = h (a + 2) := by
    dsimp [h, rise]; rw [ha11]
    simp only [det3, Minimality.Split.inner3, PiLp.sub_apply, cross_0, cross_1, cross_2]; ring
  have hrise_a2 : -ρ * rise (a + 2) = h (a + 3) - h (a + 2) := by
    dsimp [h, rise]; rw [ha21]
    simp only [det3, Minimality.Split.inner3, PiLp.sub_apply, cross_0, cross_1, cross_2]; ring
  have hrise_a3 : -ρ * rise (a + 3) = -h (a + 3) := by
    dsimp [h, rise]; rw [ha31]
    simp only [det3, Minimality.Split.inner3, PiLp.sub_apply, cross_0, cross_1, cross_2]; ring
  have hdet_eq : ∀ u v : ℝ³, Minimality.Split.det3 u v w = det3 u v w := by
    intro u v
    simp only [Minimality.Split.det3, det3, Minimality.Split.inner3, cross_0, cross_1, cross_2]
  have hS' : ∀ i j : ZMod 4, i ≠ a → (j = i ∨ j = i + 1) → j ≠ c →
      0 < σ * ((z j - z c) * rise i) := by
    intro i j hi hij hjc
    have h_s := hS i j hi hij hjc
    dsimp [rise]
    rw [show ⟪X j - X c, w⟫ = z j - z c from inner_sub_left _ _ _, hdet_eq] at h_s
    exact h_s
  have hne23 : h (a + 2) ≠ h (a + 3) := by
    intro heq
    have h0 : rise (a + 2) = 0 := by
      have : -ρ * rise (a + 2) = 0 := by rw [hrise_a2, heq, sub_self]
      exact (mul_eq_zero.mp this).resolve_left (neg_ne_zero.mpr hρ)
    by_cases hc2 : a + 2 = c
    · have h1 := hS' (a + 2) (a + 3) ha2_ne_a (Or.inr ha21.symm) (fun h3 => by
        have h10 : (1 : ZMod 4) = 0 := by linear_combination h3 - hc2
        revert h10; decide)
      rw [h0, mul_zero, mul_zero] at h1
      exact lt_irrefl 0 h1
    · have h1 := hS' (a + 2) (a + 2) ha2_ne_a (Or.inl rfl) hc2
      rw [h0, mul_zero, mul_zero] at h1
      exact lt_irrefl 0 h1
  have h_sign_opp : ∀ {u v r1 r2 : ℝ}, 0 < (-ρ) * r1 → (-ρ) * r2 < 0 →
      0 < σ * (u * r1) → 0 < σ * (v * r2) → u * v < 0 := by
    intro u v r1 r2 hr1 hr2 h1 h2
    by_contra hnot; push Not at hnot
    have hpr : 0 < (σ * (u * r1)) * (σ * (v * r2)) := mul_pos h1 h2
    have heq : (σ * (u * r1)) * (σ * (v * r2)) =
        (σ / (-ρ)) ^ 2 * (u * v) * (((-ρ) * r1) * ((-ρ) * r2)) := by
      field_simp [neg_ne_zero.mpr hρ]
    rw [heq] at hpr
    have hle : (σ / (-ρ)) ^ 2 * (u * v) * (((-ρ) * r1) * ((-ρ) * r2)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (sq_nonneg _) hnot)
        (mul_nonpos_of_nonneg_of_nonpos hr1.le hr2.le)
    linarith
  have h_sign_same : ∀ {u v r1 : ℝ}, r1 ≠ 0 →
      0 < σ * (u * r1) → 0 < σ * (v * r1) → 0 < u * v := by
    intro u v r1 hr1 h1 h2
    by_contra hnot; push Not at hnot
    have hpr : 0 < (σ * (u * r1)) * (σ * (v * r1)) := mul_pos h1 h2
    have heq : (σ * (u * r1)) * (σ * (v * r1)) = (σ * r1) ^ 2 * (u * v) := by ring
    rw [heq] at hpr
    have hle : (σ * r1) ^ 2 * (u * v) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hnot
    linarith
  have h_zmod4 : ∀ x : ZMod 4, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by decide
  have h_rob4 : ∀ (z0 z1 z2 z3 : ℝ),
      ((z0 < z2 ∧ z3 < z2 ∧ z2 < z1) ∨ (z1 < z2 ∧ z2 < z0 ∧ z2 < z3)) ∨
      ((z1 < z3 ∧ z2 < z3 ∧ z3 < z0) ∨ (z0 < z3 ∧ z3 < z1 ∧ z3 < z2)) →
      RobUni (fun i : ZMod 4 =>
        if i = a then z0 else if i = a + 1 then z1 else if i = a + 2 then z2 else z3) := by
    intro z0 z1 z2 z3 hord B b c' d hb hbc hcd hd hnot
    have hb1 : b = 1 := by omega
    have hc2 : c' = 2 := by omega
    have hd3 : d = 3 := by omega
    subst hb1 hc2 hd3
    set f : ZMod 4 → ℝ := fun i =>
      if i = a then z0 else if i = a + 1 then z1 else if i = a + 2 then z2 else z3
    have hf0 : f a = z0 := by simp [f]
    have hf1 : f (a + 1) = z1 := by
      simp [f, ha1_ne_a]
    have hf2 : f (a + 2) = z2 := by
      simp [f, ha2_ne_a, ha2_ne_a1]
    have hf3 : f (a + 3) = z3 := by
      simp [f, ha3_ne_a, ha3_ne_a1, ha3_ne_a2]
    have hB : B = a ∨ B = a + 1 ∨ B = a + 2 ∨ B = a + 3 := by
      rcases h_zmod4 (B - a) with h0 | h1 | h2 | h3
      · left; linear_combination h0
      · right; left; linear_combination h1
      · right; right; left; linear_combination h2
      · right; right; right; linear_combination h3
    have h1n : ((1 : ℕ) : ZMod 4) = 1 := rfl
    have h2n : ((2 : ℕ) : ZMod 4) = 2 := rfl
    have h3n : ((3 : ℕ) : ZMod 4) = 3 := rfl
    rw [h1n, h2n, h3n] at hnot
    rcases hB with hB | hB | hB | hB <;> rw [hB] at hnot
    · rw [hf0, hf1, hf2, hf3] at hnot
      rcases hord with (⟨h02, h32, h21⟩ | ⟨h12, h20, h23⟩) | (⟨h13, h23, h30⟩ | ⟨h03, h31, h32⟩) <;>
        linarith [hnot.1, hnot.2.1, hnot.2.2.1, hnot.2.2.2]
    · rw [ha11, show a + 1 + 2 = a + 3 by rw [add_assoc]; rfl,
        show a + 1 + 3 = a by rw [add_assoc, show (1 + 3 : ZMod 4) = 0 from rfl, add_zero],
        hf0, hf1, hf2, hf3] at hnot
      rcases hord with (⟨h02, h32, h21⟩ | ⟨h12, h20, h23⟩) | (⟨h13, h23, h30⟩ | ⟨h03, h31, h32⟩) <;>
        linarith [hnot.1, hnot.2.1, hnot.2.2.1, hnot.2.2.2]
    · rw [ha21, show a + 2 + 2 = a by rw [add_assoc, show (2 + 2 : ZMod 4) = 0 from rfl, add_zero],
        show a + 2 + 3 = a + 1 by rw [add_assoc]; rfl,
        hf0, hf1, hf2, hf3] at hnot
      rcases hord with (⟨h02, h32, h21⟩ | ⟨h12, h20, h23⟩) | (⟨h13, h23, h30⟩ | ⟨h03, h31, h32⟩) <;>
        linarith [hnot.1, hnot.2.1, hnot.2.2.1, hnot.2.2.2]
    · rw [ha31, show a + 3 + 2 = a + 1 by rw [add_assoc]; rfl,
        show a + 3 + 3 = a + 2 by rw [add_assoc]; rfl,
        hf0, hf1, hf2, hf3] at hnot
      rcases hord with (⟨h02, h32, h21⟩ | ⟨h12, h20, h23⟩) | (⟨h13, h23, h30⟩ | ⟨h03, h31, h32⟩) <;>
        linarith [hnot.1, hnot.2.1, hnot.2.2.1, hnot.2.2.2]
  have hz_eq : z = fun i =>
      if i = a then z a else if i = a + 1 then z (a + 1) else if i = a + 2 then z (a + 2) else z (a + 3) := by
    ext i
    have hi : i = a ∨ i = a + 1 ∨ i = a + 2 ∨ i = a + 3 := by
      rcases h_zmod4 (i - a) with h0 | h1 | h2 | h3
      · left; linear_combination h0
      · right; left; linear_combination h1
      · right; right; left; linear_combination h2
      · right; right; right; linear_combination h3
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp [ha1_ne_a, ha2_ne_a, ha2_ne_a1, ha3_ne_a, ha3_ne_a1, ha3_ne_a2]
  rw [show (fun i => ⟪X i, w⟫) = z from rfl, hz_eq]
  refine h_rob4 (z a) (z (a + 1)) (z (a + 2)) (z (a + 3)) ?_
  rcases lt_or_gt_of_ne hne23 with hlt | hgt
  · -- `h (a + 2) < h (a + 3)`: maximizer is `a + 3`, so `c = a + 3`
    have hc3 : c = a + 3 := by
      by_contra hne
      have h1 := hS' (a + 2) (a + 3) ha2_ne_a (Or.inr ha21.symm) (fun h0 => hne h0.symm)
      have h2 := hS' (a + 3) (a + 3) ha3_ne_a (Or.inl rfl) (fun h0 => hne h0.symm)
      have hr2 : (-ρ) * rise (a + 2) > 0 := by linarith [hrise_a2]
      have hr3 : (-ρ) * rise (a + 3) < 0 := by linarith [hrise_a3]
      have hsq := h_sign_opp hr2 hr3 h1 h2
      linarith [sq_nonneg (z (a + 3) - z c)]
    subst hc3
    have s1 := hS' (a + 1) (a + 1) ha1_ne_a (Or.inl rfl) ha3_ne_a1.symm
    have s2 := hS' (a + 1) (a + 2) ha1_ne_a (Or.inr ha11.symm) (fun h0 => by
      have h10 : (1 : ZMod 4) = 0 := by linear_combination -h0
      revert h10; decide)
    have s3 := hS' (a + 3) a ha3_ne_a (Or.inr ha31.symm) ha3_ne_a.symm
    have hr1 : (-ρ) * rise (a + 1) > 0 := by linarith [hrise_a1]
    have hr3 : (-ρ) * rise (a + 3) < 0 := by linarith [hrise_a3]
    have hr1_ne : rise (a + 1) ≠ 0 := fun h0 => by rw [h0, mul_zero] at hr1; exact lt_irrefl 0 hr1
    have h12 := h_sign_same hr1_ne s1 s2
    have h13 := h_sign_opp hr1 hr3 s1 s3
    rcases lt_or_gt_of_ne (show z (a + 1) - z (a + 3) ≠ 0 from
        fun h0 => by rw [h0, zero_mul] at h12; exact lt_irrefl 0 h12) with hn | hp
    · have h2_neg : z (a + 2) - z (a + 3) < 0 := by nlinarith
      have h0_pos : 0 < z a - z (a + 3) := by nlinarith
      exact Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩)
    · have h2_pos : 0 < z (a + 2) - z (a + 3) := by nlinarith
      have h0_neg : z a - z (a + 3) < 0 := by nlinarith
      exact Or.inr (Or.inr ⟨by linarith, by linarith, by linarith⟩)
  · -- `h (a + 3) < h (a + 2)`: maximizer is `a + 2`, so `c = a + 2`
    have hc2 : c = a + 2 := by
      by_contra hne
      have h1 := hS' (a + 1) (a + 2) ha1_ne_a (Or.inr ha11.symm) (fun h0 => hne h0.symm)
      have h2 := hS' (a + 2) (a + 2) ha2_ne_a (Or.inl rfl) (fun h0 => hne h0.symm)
      have hr1 : (-ρ) * rise (a + 1) > 0 := by linarith [hrise_a1]
      have hr2 : (-ρ) * rise (a + 2) < 0 := by linarith [hrise_a2]
      have hsq := h_sign_opp hr1 hr2 h1 h2
      linarith [sq_nonneg (z (a + 2) - z c)]
    subst hc2
    have s1 := hS' (a + 1) (a + 1) ha1_ne_a (Or.inl rfl) ha2_ne_a1.symm
    have s2 := hS' (a + 3) (a + 3) ha3_ne_a (Or.inl rfl) (fun h0 => by
      have h10 : (1 : ZMod 4) = 0 := by linear_combination h0
      revert h10; decide)
    have s3 := hS' (a + 3) a ha3_ne_a (Or.inr ha31.symm) ha2_ne_a.symm
    have hr1 : (-ρ) * rise (a + 1) > 0 := by linarith [hrise_a1]
    have hr3 : (-ρ) * rise (a + 3) < 0 := by linarith [hrise_a3]
    have h12 := h_sign_opp hr1 hr3 s1 s2
    have h13 := h_sign_opp hr1 hr3 s1 s3
    rcases lt_or_gt_of_ne (show z (a + 1) - z (a + 2) ≠ 0 from
        fun h0 => by rw [h0, zero_mul] at h12; exact lt_irrefl 0 h12) with hn | hp
    · have h3_pos : 0 < z (a + 3) - z (a + 2) := by nlinarith
      have h0_pos : 0 < z a - z (a + 2) := by nlinarith
      exact Or.inl (Or.inr ⟨by linarith, by linarith, by linarith⟩)
    · have h3_neg : z (a + 3) - z (a + 2) < 0 := by nlinarith
      have h0_neg : z a - z (a + 2) < 0 := by nlinarith
      exact Or.inl (Or.inl ⟨by linarith, by linarith, by linarith⟩)

end Minimality.GenPlus
