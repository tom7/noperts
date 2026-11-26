module

public import Minimality.SplitRows
public import Minimality.SilS0XA
public import Minimality.RimOrder

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
open Finset

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
  have ha2_ne_a : a + 2 ≠ a := fun h0 => absurd (show (2 : ZMod 4) = 0 by linear_combination h0) (by decide)
  have ha2_ne_a1 : a + 2 ≠ a + 1 := fun h0 => absurd (show (1 : ZMod 4) = 0 by linear_combination h0) (by decide)
  have ha3_ne_a : a + 3 ≠ a := fun h0 => absurd (show (3 : ZMod 4) = 0 by linear_combination h0) (by decide)
  have ha3_ne_a1 : a + 3 ≠ a + 1 := fun h0 => absurd (show (2 : ZMod 4) = 0 by linear_combination h0) (by decide)
  have ha1_ne_a : a + 1 ≠ a := fun h0 => absurd (show (1 : ZMod 4) = 0 by linear_combination h0) (by decide)
  have ha3_ne_a2 : a + 3 ≠ a + 2 := fun h0 => absurd (show (1 : ZMod 4) = 0 by linear_combination h0) (by decide)
  have hh2 : 0 < h (a + 2) := hcyc a (a + 2) ha2_ne_a ha2_ne_a1
  have hh3 : 0 < h (a + 3) := hcyc a (a + 3) ha3_ne_a ha3_ne_a1
  have hrise_a1 : -ρ * rise (a + 1) = h (a + 2) := by
    dsimp [h, rise]; rw [add_assoc, show (1 + 1 : ZMod 4) = 2 by decide]
    simp only [det3, H21.inner3, PiLp.sub_apply, cross_apply_zero, cross_apply_one, cross_apply_two]; ring
  have hrise_a3 : -ρ * rise (a + 3) = -h (a + 3) := by
    dsimp [h, rise]; rw [add_assoc, show (3 + 1 : ZMod 4) = 0 by decide, add_zero]
    simp only [det3, H21.inner3, PiLp.sub_apply, cross_apply_zero, cross_apply_one, cross_apply_two]; ring
  have hopp : rise (a + 1) * rise (a + 3) < 0 := by
    have hmul : (-ρ * rise (a + 1)) * (-ρ * rise (a + 3)) < 0 := by rw [hrise_a1, hrise_a3]; nlinarith
    have hid : (-ρ * rise (a + 1)) * (-ρ * rise (a + 3)) = ρ ^ 2 * (rise (a + 1) * rise (a + 3)) := by ring
    rw [hid] at hmul
    exact neg_of_mul_neg_right hmul (sq_pos_of_ne_zero hρ).le
  have hdet_eq : ∀ u v : ℝ³, Minimality.Split.det3 u v w = det3 u v w := fun u v => by
    simp only [Minimality.Split.det3, det3, Minimality.Split.inner3,
      Minimality.Split.cross_0, Minimality.Split.cross_1, Minimality.Split.cross_2]
  have hS' : ∀ i j : ZMod 4, i ≠ a → (j = i ∨ j = i + 1) → j ≠ c →
      0 < σ * ((z j - z c) * rise i) := fun i j hi hij hjc => by
    have hs := hS i j hi hij hjc
    dsimp [rise]
    rwa [show ⟪X j - X c, w⟫ = z j - z c from inner_sub_left _ _ _, hdet_eq] at hs
  have h_opp_of_S : ∀ {u v : ℝ} {i1 i2 : ZMod 4},
      i1 = a + 1 → i2 = a + 3 → 0 < σ * (u * rise i1) → 0 < σ * (v * rise i2) → u * v < 0 := by
    rintro u v _ _ rfl rfl h1 h2
    have hσ_ne : σ ≠ 0 := fun h0 => by rw [h0, zero_mul] at h1; exact lt_irrefl 0 h1
    have hneg : σ ^ 2 * (rise (a + 1) * rise (a + 3)) < 0 :=
      mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hσ_ne) hopp
    have hprod : 0 < (σ ^ 2 * (rise (a + 1) * rise (a + 3))) * (u * v) := by
      have := mul_pos h1 h2; linarith
    exact neg_of_mul_pos_right hprod hneg.le
  have hc_mono : 0 < (z c - z (c - 1)) * (z (c + 1) - z c) := by
    have hc_cases : c = a ∨ c = a + 1 ∨ c = a + 2 ∨ c = a + 3 := by
      have h4 : ∀ x : ZMod 4, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by decide
      rcases h4 (c - a) with h0 | h1 | h2 | h3
      · left; linear_combination h0
      · right; left; linear_combination h1
      · right; right; left; linear_combination h2
      · right; right; right; linear_combination h3
    rcases hc_cases with rfl | rfl | rfl | rfl
    · have h1 := hS' (c + 1) (c + 1) ha1_ne_a (Or.inl rfl) ha1_ne_a
      have h3 := hS' (c + 3) (c + 3) ha3_ne_a (Or.inl rfl) ha3_ne_a
      have hopp_z := h_opp_of_S rfl rfl h1 h3
      rw [show c - 1 = c + 3 by rw [sub_eq_add_neg, show (-1 : ZMod 4) = 3 by decide]]
      nlinarith
    · have h1 := hS' (a + 1) (a + 2) ha1_ne_a (Or.inr (by rw [add_assoc]; ring_nf)) ha2_ne_a1
      have h3 := hS' (a + 3) a ha3_ne_a
        (Or.inr (by rw [add_assoc, show (3 + 1 : ZMod 4) = 0 by decide, add_zero])) ha1_ne_a.symm
      have hopp_z := h_opp_of_S rfl rfl h1 h3
      rw [show a + 1 - 1 = a by ring, show a + 1 + 1 = a + 2 by rw [add_assoc]; ring_nf]
      nlinarith
    · have h1 := hS' (a + 1) (a + 1) ha1_ne_a (Or.inl rfl) ha2_ne_a1.symm
      have h3 := hS' (a + 3) (a + 3) ha3_ne_a (Or.inl rfl) ha3_ne_a2
      have hopp_z := h_opp_of_S rfl rfl h1 h3
      rw [show a + 2 - 1 = a + 1 by ring, show a + 2 + 1 = a + 3 by rw [add_assoc]; ring_nf]
      nlinarith
    · have h1 := hS' (a + 1) (a + 2) ha1_ne_a (Or.inr (by rw [add_assoc]; ring_nf)) ha3_ne_a2.symm
      have h3 := hS' (a + 3) a ha3_ne_a
        (Or.inr (by rw [add_assoc, show (3 + 1 : ZMod 4) = 0 by decide, add_zero])) ha3_ne_a.symm
      have hopp_z := h_opp_of_S rfl rfl h1 h3
      rw [show a + 3 - 1 = a + 2 by ring,
        show a + 3 + 1 = a by rw [add_assoc, show (3 + 1 : ZMod 4) = 0 by decide, add_zero]]
      nlinarith
  exact robUni_of_monoCorners (by decide) {c} (by simp) (fun v hv => by
    rw [mem_singleton.1 hv]; exact hc_mono)

end Minimality.GenPlus
