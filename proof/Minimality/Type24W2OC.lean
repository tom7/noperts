module

public import Minimality.Type24RayCT
public import Minimality.Type24WallFoot126

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace Topology
open Finset Filter
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.HC Minimality.T24.SF Minimality.T24.Stmt
  Minimality.T24.M4 Minimality.T24.WallFoot126

namespace Minimality.T24.Cell

theorem w2oc_plucker (e₁ e₂ d y w : ℝ³) :
    Split.det3 e₁ e₂ w * Split.det3 d y w =
      Split.det3 d e₂ w * Split.det3 e₁ y w + Split.det3 e₁ d w * Split.det3 e₂ y w := by
  simp only [Split.det3]; ring

theorem w2oc_noMax {k : ℕ} [NeZero k] (hk : 3 ≤ k) {X : ZMod k → ℝ³} {w : ℝ³} {ρ : ℝ}
    (hcyc : ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 → 0 < ρ * Split.det3 (X (i + 1) - X i) (X j - X i) w)
    (a : ZMod k) :
    ∀ i : ZMod k, i ≠ a → i + 1 ≠ a →
      ρ * Split.det3 (X i - X a) (X (a + 1) - X a) w ≤ ρ * Split.det3 (X (i + 1) - X a) (X (a + 1) - X a) w →
      ρ * Split.det3 (X (i + 1) - X a) (X (a + 1) - X a) w <
        ρ * Split.det3 (X (i + 2) - X a) (X (a + 1) - X a) w := by
  have : Fact (1 < k) := ⟨by omega⟩
  let d : ℝ³ := X (a + 1) - X a
  let h : ZMod k → ℝ := fun j => Split.det3 (X j - X a) d w
  let g : ZMod k → ℝ := fun j => ρ * h j
  let rise : ZMod k → ℝ := fun i => Split.det3 (X (i + 1) - X i) d w
  have hrise_eq : ∀ i : ZMod k, rise i = h (i + 1) - h i := by
    intro i
    simp only [rise, h, d, Split.det3, PiLp.sub_apply]
    ring
  have ha_zero : g a = 0 := by
    simp only [g, h, d, Split.det3, PiLp.sub_apply]
    ring
  have ha1_zero : g (a + 1) = 0 := by
    simp only [g, h, d, Split.det3, PiLp.sub_apply]
    ring
  have hg_neg : ∀ j : ZMod k, j ≠ a → j ≠ a + 1 → g j < 0 := by
    intro j hja hja1
    have hc := hcyc a j hja hja1
    have hdet : Split.det3 (X (a + 1) - X a) (X j - X a) w = -h j := by
      simp only [h, d, Split.det3, PiLp.sub_apply]
      ring
    rw [hdet] at hc
    dsimp [g]
    linarith
  have h_no_max : ∀ i : ZMod k, i ≠ a → i + 1 ≠ a →
      g i ≤ g (i + 1) → g (i + 1) < g (i + 2) := by
    intro i hia hi1a hle
    have hi1_ne_a1 : i + 1 ≠ a + 1 := by
      intro h0
      apply hia
      linear_combination h0
    have hpl := w2oc_plucker (X (i + 1) - X i) (X (i + 2) - X (i + 1)) d (X (i + 1) - X a) w
    have h_e12 : 0 < ρ * Split.det3 (X (i + 1) - X i) (X (i + 2) - X (i + 1)) w := by
      have hi2_ne_i : i + 2 ≠ i := by
        intro h0
        have h2 : ((2 : ℕ) : ZMod k) = 0 := by push_cast; linear_combination h0
        have hv := congrArg ZMod.val h2
        rw [ZMod.val_zero, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)] at hv
        omega
      have hi2_ne_i1 : i + 2 ≠ i + 1 := by
        intro h0
        have : (1 : ZMod k) = 0 := by linear_combination h0
        exact one_ne_zero this
      have h_det : Split.det3 (X (i + 1) - X i) (X (i + 2) - X (i + 1)) w =
          Split.det3 (X (i + 1) - X i) (X (i + 2) - X i) w := by
        simp only [Split.det3, PiLp.sub_apply]
        ring
      rw [h_det]
      exact hcyc i (i + 2) hi2_ne_i hi2_ne_i1
    have h_dy : 0 < ρ * Split.det3 d (X (i + 1) - X a) w := by
      have h_eq : Split.det3 d (X (i + 1) - X a) w = -h (i + 1) := by
        simp only [h, d, Split.det3, PiLp.sub_apply]
        ring
      rw [h_eq]
      have hg_neg_i1 := hg_neg (i + 1) hi1a hi1_ne_a1
      dsimp [g] at hg_neg_i1
      linarith
    have h_e1y : ρ * Split.det3 (X (i + 1) - X i) (X (i + 1) - X a) w ≤ 0 := by
      have h_eq : Split.det3 (X (i + 1) - X i) (X (i + 1) - X a) w =
          -Split.det3 (X (i + 1) - X i) (X a - X i) w := by
        simp only [Split.det3, PiLp.sub_apply]
        ring
      rw [h_eq]
      have hc := hcyc i a hia.symm hi1a.symm
      linarith
    have h_e2y : ρ * Split.det3 (X (i + 2) - X (i + 1)) (X (i + 1) - X a) w ≤ 0 := by
      by_cases hi2a : i + 2 = a
      · have h_zero : Split.det3 (X (i + 2) - X (i + 1)) (X (i + 1) - X a) w = 0 := by
          rw [hi2a]
          simp only [Split.det3, PiLp.sub_apply]
          ring
        rw [h_zero, mul_zero]
      · have hi2_eq : i + 2 = (i + 1) + 1 := by ring
        have hc := hcyc (i + 1) a hi1a.symm (by rw [← hi2_eq]; exact Ne.symm hi2a)
        have h_eq : Split.det3 (X (i + 2) - X (i + 1)) (X (i + 1) - X a) w =
            -Split.det3 (X ((i + 1) + 1) - X (i + 1)) (X a - X (i + 1)) w := by
          rw [← hi2_eq]
          simp only [Split.det3, PiLp.sub_apply]
          ring
        rw [h_eq]
        linarith
    have h_de2 : ρ * Split.det3 d (X (i + 2) - X (i + 1)) w = -(g (i + 2) - g (i + 1)) := by
      have h_eq : Split.det3 d (X (i + 2) - X (i + 1)) w = -rise (i + 1) := by
        simp only [rise, d, Split.det3, PiLp.sub_apply]
        ring
      rw [h_eq, hrise_eq]
      have h12 : (i + 1) + 1 = i + 2 := by ring
      rw [h12]
      dsimp [g]
      ring
    have h_e1d : ρ * Split.det3 (X (i + 1) - X i) d w = g (i + 1) - g i := by
      change ρ * rise i = g (i + 1) - g i
      rw [hrise_eq]
      dsimp [g]
      ring
    have h_scaled :
        (ρ * Split.det3 (X (i + 1) - X i) (X (i + 2) - X (i + 1)) w) * (ρ * Split.det3 d (X (i + 1) - X a) w) =
        (ρ * Split.det3 d (X (i + 2) - X (i + 1)) w) * (ρ * Split.det3 (X (i + 1) - X i) (X (i + 1) - X a) w) +
        (ρ * Split.det3 (X (i + 1) - X i) d w) * (ρ * Split.det3 (X (i + 2) - X (i + 1)) (X (i + 1) - X a) w) := by
      linear_combination (ρ * ρ) * hpl
    rw [h_de2, h_e1d] at h_scaled
    by_contra h_not
    push Not at h_not
    have h_lhs : 0 < (ρ * Split.det3 (X (i + 1) - X i) (X (i + 2) - X (i + 1)) w) *
        (ρ * Split.det3 d (X (i + 1) - X a) w) := mul_pos h_e12 h_dy
    have h_t1 : -(g (i + 2) - g (i + 1)) *
        (ρ * Split.det3 (X (i + 1) - X i) (X (i + 1) - X a) w) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) h_e1y
    have h_t2 : (g (i + 1) - g i) *
        (ρ * Split.det3 (X (i + 2) - X (i + 1)) (X (i + 1) - X a) w) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) h_e2y
    linarith
  exact h_no_max

/-! ## Pentagon: unimodal heights give a strict apex (ZMod 5) -/

section Pent

variable {X : ZMod 5 → ℝ³} {w : ℝ³} {ρ : ℝ}

theorem w2oc_abs (hcyc : ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      0 < ρ * Split.det3 (X (i + 1) - X i) (X j - X i) w) (hρ : ρ = 1 ∨ ρ = -1) (a j : ZMod 5)
    (h0 : j ≠ a) (h1 : j ≠ a + 1) :
    |Split.det3 (X j - X a) (X (a + 1) - X a) w| = -(ρ * Split.det3 (X j - X a) (X (a + 1) - X a) w) := by
  have hc := hcyc a j h0 h1
  have e : Split.det3 (X j - X a) (X (a + 1) - X a) w = -Split.det3 (X (a + 1) - X a) (X j - X a) w := by
    simp only [Split.det3, PiLp.sub_apply]; ring
  rcases hρ with rfl | rfl
  · rw [one_mul] at hc; rw [e, abs_neg, abs_of_pos hc]; ring
  · rw [neg_one_mul] at hc; rw [e, abs_neg, abs_of_neg (by linarith)]; ring

theorem w2oc_ne_add (a n : ZMod 5) (h : n ≠ 0) : a + n ≠ a := fun e => h (by simpa using e)

theorem w2oc_far (a j : ZMod 5) (h0 : j ≠ a) (h1 : j ≠ a + 1) (h2 : j ≠ a + 2) : j = a + 3 ∨ j = a + 4 := by
  have key : ∀ d : ZMod 5, d ≠ 0 → d ≠ 1 → d ≠ 2 → d = 3 ∨ d = 4 := by decide
  have := key (j - a) (fun e => h0 (by linear_combination e)) (fun e => h1 (by linear_combination e))
    (fun e => h2 (by linear_combination e))
  rcases this with e | e
  · left; linear_combination e
  · right; linear_combination e

/-- Apex at `a + 2`: `g (a + 2) < g (a + 3)` makes `a + 2` the strict height maximiser. -/
theorem w2oc_extA (hcyc : ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      0 < ρ * Split.det3 (X (i + 1) - X i) (X j - X i) w) (hρ : ρ = 1 ∨ ρ = -1) (a : ZMod 5)
    (h : ρ * Split.det3 (X (a + 2) - X a) (X (a + 1) - X a) w <
      ρ * Split.det3 (X (a + 3) - X a) (X (a + 1) - X a) w) :
    ∀ j : ZMod 5, j ≠ a → j ≠ a + 1 → j ≠ a + 2 →
      |Split.det3 (X j - X a) (X (a + 1) - X a) w| < |Split.det3 (X (a + 2) - X a) (X (a + 1) - X a) w| := by
  have n2 : a + 2 ≠ a := w2oc_ne_add a 2 (by decide)
  have n3 : a + 3 ≠ a := w2oc_ne_add a 3 (by decide)
  have n4 : a + 4 ≠ a := w2oc_ne_add a 4 (by decide)
  have m2 : a + 2 ≠ a + 1 := fun e => by have := add_left_cancel e; revert this; decide
  have m3 : a + 3 ≠ a + 1 := fun e => by have := add_left_cancel e; revert this; decide
  have m4 : a + 4 ≠ a + 1 := fun e => by have := add_left_cancel e; revert this; decide
  have nm := w2oc_noMax (k := 5) (by norm_num) hcyc a (a + 2) n2 (by
    rw [show a + 2 + 1 = a + 3 by ring]; exact n3) (by
    rw [show a + 2 + 1 = a + 3 by ring]; exact h.le)
  rw [show a + 2 + 1 = a + 3 by ring, show a + 2 + 2 = a + 4 by ring] at nm
  intro j hj0 hj1 hj2
  rw [w2oc_abs hcyc hρ a j hj0 hj1, w2oc_abs hcyc hρ a (a + 2) n2 m2]
  rcases w2oc_far a j hj0 hj1 hj2 with rfl | rfl <;> linarith

/-- Apex at `a + 4`: `g (a + 4) < g (a + 3)` makes `a + 4` the strict height maximiser. -/
theorem w2oc_extB (hcyc : ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      0 < ρ * Split.det3 (X (i + 1) - X i) (X j - X i) w) (hρ : ρ = 1 ∨ ρ = -1) (a : ZMod 5)
    (h : ρ * Split.det3 (X (a + 4) - X a) (X (a + 1) - X a) w <
      ρ * Split.det3 (X (a + 3) - X a) (X (a + 1) - X a) w) :
    ∀ j : ZMod 5, j ≠ a → j ≠ a + 1 → j ≠ a + 4 →
      |Split.det3 (X j - X a) (X (a + 1) - X a) w| < |Split.det3 (X (a + 4) - X a) (X (a + 1) - X a) w| := by
  have n2 : a + 2 ≠ a := w2oc_ne_add a 2 (by decide)
  have n3 : a + 3 ≠ a := w2oc_ne_add a 3 (by decide)
  have n4 : a + 4 ≠ a := w2oc_ne_add a 4 (by decide)
  have m2 : a + 2 ≠ a + 1 := fun e => by have := add_left_cancel e; revert this; decide
  have m3 : a + 3 ≠ a + 1 := fun e => by have := add_left_cancel e; revert this; decide
  have m4 : a + 4 ≠ a + 1 := fun e => by have := add_left_cancel e; revert this; decide
  intro j hj0 hj1 hj4
  have hj : j = a + 2 ∨ j = a + 3 := by
    have key : ∀ d : ZMod 5, d ≠ 0 → d ≠ 1 → d ≠ 4 → d = 2 ∨ d = 3 := by decide
    rcases key (j - a) (fun e => hj0 (by linear_combination e)) (fun e => hj1 (by linear_combination e))
      (fun e => hj4 (by linear_combination e)) with e | e
    · left; linear_combination e
    · right; linear_combination e
  rw [w2oc_abs hcyc hρ a j hj0 hj1, w2oc_abs hcyc hρ a (a + 4) n4 m4]
  rcases hj with rfl | rfl
  · -- `g (a + 2) ≤ g (a + 4)` would force `g (a + 3) < g (a + 4)`
    by_contra hcon
    have hle : ρ * Split.det3 (X (a + 2) - X a) (X (a + 1) - X a) w ≤
        ρ * Split.det3 (X (a + 3) - X a) (X (a + 1) - X a) w := by linarith
    have nm := w2oc_noMax (k := 5) (by norm_num) hcyc a (a + 2) n2 (by
      rw [show a + 2 + 1 = a + 3 by ring]; exact n3) (by
      rw [show a + 2 + 1 = a + 3 by ring]; exact hle)
    rw [show a + 2 + 1 = a + 3 by ring, show a + 2 + 2 = a + 4 by ring] at nm
    linarith
  · linarith

end Pent


/-! ## The strict apex on the rim `0.4.6.2.5` -/

variable {x : Fin 7 → ℝ³}

/-- `z2 > z5 > z0, z4, z6` and the height of `5` over the projected edge `6 → 2` beats `0`'s:
apex `5` over the base edge `6 → 2`. -/
theorem w2oc_apexA {w : ℝ³} {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1)
    (hrim : ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      0 < ρ * Split.det3 (x (rP (i + 1)) - x (rP i)) (x (rP j) - x (rP i)) w)
    (hd : ρ * Split.det3 (x 5 - x 6) (x 2 - x 6) w < ρ * Split.det3 (x 0 - x 6) (x 2 - x 6) w)
    (z25 : ⟪x 5, w⟫ < ⟪x 2, w⟫) (z05 : ⟪x 0, w⟫ < ⟪x 5, w⟫) (z45 : ⟪x 4, w⟫ < ⟪x 5, w⟫)
    (z65 : ⟪x 6, w⟫ < ⟪x 5, w⟫) : ApexCert (fun i => x (rP i)) w := by
  refine ⟨2, 4, by decide, by decide, w2oc_extA (X := fun i => x (rP i)) hrim hρ 2 hd, -1, Or.inr rfl, ?_, ?_⟩
  · intro j hj
    have : j = 3 := by revert j; decide
    subst this
    show -1 * (⟪x 2, w⟫ - ⟪x 5, w⟫) < 0
    linarith
  · intro j hj
    have : j = 0 ∨ j = 1 ∨ j = 2 := by revert j; decide
    rcases this with rfl | rfl | rfl
    · show 0 < -1 * (⟪x 0, w⟫ - ⟪x 5, w⟫); linarith
    · show 0 < -1 * (⟪x 4, w⟫ - ⟪x 5, w⟫); linarith
    · show 0 < -1 * (⟪x 6, w⟫ - ⟪x 5, w⟫); linarith

/-- `z5 > z2 > z0, z4, z6` and the height of `2` over the projected edge `5 → 0` beats `6`'s:
apex `2` over the base edge `5 → 0`. -/
theorem w2oc_apexB {w : ℝ³} {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1)
    (hrim : ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      0 < ρ * Split.det3 (x (rP (i + 1)) - x (rP i)) (x (rP j) - x (rP i)) w)
    (hd : ρ * Split.det3 (x 2 - x 5) (x 0 - x 5) w < ρ * Split.det3 (x 6 - x 5) (x 0 - x 5) w)
    (z52 : ⟪x 2, w⟫ < ⟪x 5, w⟫) (z02 : ⟪x 0, w⟫ < ⟪x 2, w⟫) (z42 : ⟪x 4, w⟫ < ⟪x 2, w⟫)
    (z62 : ⟪x 6, w⟫ < ⟪x 2, w⟫) : ApexCert (fun i => x (rP i)) w := by
  refine ⟨4, 3, by decide, by decide, w2oc_extB (X := fun i => x (rP i)) hrim hρ 4 hd, 1, Or.inl rfl, ?_, ?_⟩
  · intro j hj
    have : j = 0 ∨ j = 1 ∨ j = 2 := by revert j; decide
    rcases this with rfl | rfl | rfl
    · show 1 * (⟪x 0, w⟫ - ⟪x 2, w⟫) < 0; linarith
    · show 1 * (⟪x 4, w⟫ - ⟪x 2, w⟫) < 0; linarith
    · show 1 * (⟪x 6, w⟫ - ⟪x 2, w⟫) < 0; linarith
  · intro j hj
    have : j = 4 := by revert j; decide
    subst this
    show 0 < 1 * (⟪x 5, w⟫ - ⟪x 2, w⟫)
    linarith


/-! ## Heights over the projected edges at the views `capView x η 1 cc` (frame computation) -/

theorem w2oc_rep (F : S0xFac 9 s0x_S24 x) (v : Fin 7) :
    x v - x 1 = oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1) := by
  rw [(type24OfFac F).rep v]; abel

/-- Heights over the projected edge `6 - 2` (screen height of `x 5` is its `e_a`-coordinate times `1 + cc`). -/
theorem w2oc_h62_5 (F : S0xFac 9 s0x_S24 x) (η cc : ℝ) :
    Split.det3 (x 5 - x 6) (x 2 - x 6) (capView x η 1 cc) =
      det24 x * (oblX0 x 5 * (1 + cc) - η * (oblX2 x 5 + oblX6 x 5 - 1)) := by
  have hrep := w2oc_rep F 5
  have e1 : x 5 - x 6 = oblX0 x 5 • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) + (oblX6 x 5 - 1) • (x 6 - x 1) := by
    linear_combination (norm := module) hrep
  have e2 : x 2 - x 6 = (0 : ℝ) • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) + (-1 : ℝ) • (x 6 - x 1) := by module
  have e3 : capView x η 1 cc = η • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) + cc • (x 6 - x 1) := rfl
  rw [e1, e2, e3, Split.det3_eq_minimality, M4.det3_frame]; ring

theorem w2oc_h62_0 (x : Fin 7 → ℝ³) (η cc : ℝ) :
    Split.det3 (x 0 - x 6) (x 2 - x 6) (capView x η 1 cc) = det24 x * ((1 + cc) + η) := by
  have e1 : x 0 - x 6 = (1 : ℝ) • (x 0 - x 1) + (0 : ℝ) • (x 2 - x 1) + (-1 : ℝ) • (x 6 - x 1) := by module
  have e2 : x 2 - x 6 = (0 : ℝ) • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) + (-1 : ℝ) • (x 6 - x 1) := by module
  have e3 : capView x η 1 cc = η • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) + cc • (x 6 - x 1) := rfl
  rw [e1, e2, e3, Split.det3_eq_minimality, M4.det3_frame]; ring

/-- Difference of the heights of `6` and `2` over the projected edge `5 - 0`. -/
theorem w2oc_hB (F : S0xFac 9 s0x_S24 x) (η cc : ℝ) :
    Split.det3 (x 6 - x 5) (x 0 - x 5) (capView x η 1 cc) - Split.det3 (x 2 - x 5) (x 0 - x 5) (capView x η 1 cc) =
      det24 x * ((1 - oblX0 x 5) * (1 + cc) + η * (oblX2 x 5 + oblX6 x 5)) := by
  have hrep := w2oc_rep F 5
  have lin : Split.det3 (x 6 - x 5) (x 0 - x 5) (capView x η 1 cc) -
      Split.det3 (x 2 - x 5) (x 0 - x 5) (capView x η 1 cc) =
      Split.det3 (x 6 - x 2) (x 0 - x 5) (capView x η 1 cc) := by
    simp only [Split.det3, PiLp.sub_apply]; ring
  have e1 : x 6 - x 2 = (0 : ℝ) • (x 0 - x 1) + (-1 : ℝ) • (x 2 - x 1) + (1 : ℝ) • (x 6 - x 1) := by module
  have e2 : x 0 - x 5 = (1 - oblX0 x 5) • (x 0 - x 1) + (-oblX2 x 5) • (x 2 - x 1) +
      (-oblX6 x 5) • (x 6 - x 1) := by
    linear_combination (norm := module) -hrep
  have e3 : capView x η 1 cc = η • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) + cc • (x 6 - x 1) := rfl
  rw [lin, e1, e2, e3, Split.det3_eq_minimality, M4.det3_frame]; ring

/-- `F.f 5 (x 5) < F.f 5 (x 0)` is `a5 > 1` (`5` farther than `0` from the plane of `126`). -/
theorem w2oc_a5 (F : S0xFac 9 s0x_S24 x) (h : F.f 5 (x 5) < F.f 5 (x 0)) : 1 < oblX0 x 5 := by
  have ev := M4.fac_eval F 5 5
  rw [F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)] at ev
  have := F.neg 5 0 (by decide)
  by_contra hcon
  push Not at hcon
  nlinarith

/-! ## The statement -/

/-- **W2-OC at a given `cc`** (type 24, order certificate in the pentagon `P = 0.4.6.2.5` on the wall line of
facet `126`).  At `w0 = capView x 0 1 cc = e_b + cc e_c`: the window `1/ω5 < cc < ω4` with `0345`, `235`, `346`
front (the other facets of `P` are automatic), `a5 > 1` (`5` strictly farther than `0` from the plane of `126`),
and `max (z0, z4, z6) < min (z2, z5)`, `z2 ≠ z5` for `z_v = ⟪x v - x 1, w0⟫`. -/
def W2OCAt (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) (cc : ℝ) : Prop :=
  0 < omega5 x ∧ 1 / omega5 x < cc ∧ cc < omega4 x ∧
    0 < ⟪F.N 3, capView x 0 1 cc⟫ ∧ 0 < ⟪F.N 6, capView x 0 1 cc⟫ ∧ 0 < ⟪F.N 8, capView x 0 1 cc⟫ ∧
    F.f 5 (x 5) < F.f 5 (x 0) ∧
    ⟪x 0 - x 1, capView x 0 1 cc⟫ < ⟪x 2 - x 1, capView x 0 1 cc⟫ ∧
    ⟪x 0 - x 1, capView x 0 1 cc⟫ < ⟪x 5 - x 1, capView x 0 1 cc⟫ ∧
    ⟪x 4 - x 1, capView x 0 1 cc⟫ < ⟪x 2 - x 1, capView x 0 1 cc⟫ ∧
    ⟪x 4 - x 1, capView x 0 1 cc⟫ < ⟪x 5 - x 1, capView x 0 1 cc⟫ ∧
    ⟪x 6 - x 1, capView x 0 1 cc⟫ < ⟪x 2 - x 1, capView x 0 1 cc⟫ ∧
    ⟪x 6 - x 1, capView x 0 1 cc⟫ < ⟪x 5 - x 1, capView x 0 1 cc⟫ ∧
    ⟪x 2 - x 1, capView x 0 1 cc⟫ ≠ ⟪x 5 - x 1, capView x 0 1 cc⟫

/-- **W2-OC:** `W2OCAt x F cc` for some `cc`. -/
def W2OC (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop := ∃ cc : ℝ, W2OCAt x F cc

theorem w2oc_ev_pos (A B : ℝ) (h : 0 < A) : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < A + η * B := by
  have hc : Continuous (fun η : ℝ => A + η * B) := by fun_prop
  have ht : Tendsto (fun η : ℝ => A + η * B) (𝓝 0) (𝓝 A) := by simpa using hc.tendsto 0
  exact nhdsWithin_le_nhds (ht.eventually (lt_mem_nhds h))

/-- The open cell `P` along the wall line (facet signs at `w0`, as in `wallP_lexAny`). -/
theorem w2oc_cellAt_eventually (F : S0xFac 9 s0x_S24 x) {cc : ℝ} (h5 : 0 < omega5 x) (hw5 : 1 / omega5 x < cc)
    (hw4 : cc < omega4 x)
    (h3 : 0 < ⟪F.N 3, capView x 0 1 cc⟫) (h6 : 0 < ⟪F.N 6, capView x 0 1 cc⟫)
    (h8 : 0 < ⟪F.N 8, capView x 0 1 cc⟫) :
    ∀ᶠ η : ℝ in 𝓝[>] 0, CellAt F cellP.U (univ \ cellP.U) (capView x η 1 cc) := by
  have hcc : 0 < cc := lt_trans (one_div_pos.mpr h5) hw5
  have hw5' : 1 < omega5 x * cc := by
    have := mul_lt_mul_of_pos_left hw5 h5
    rwa [mul_one_div_cancel h5.ne'] at this
  have hcell := wall126_cellAt_eventually F (U := {3, 6, 7, 8}) (Dn := {0, 1, 2, 4, 5}) (cc := cc)
    (fun t ht => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact h3
      · exact h6
      · rw [cap_f7]; nlinarith [F.neg 7 1 (by decide)]
      · exact h8)
    (fun t ht h5' => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl
      · rw [cap_f0]; exact mul_neg_of_pos_of_neg hcc (F.neg 0 6 (by decide))
      · rw [cap_f1]; linarith [F.neg 1 2 (by decide)]
      · rw [cap_f2]; nlinarith [F.neg 2 1 (by decide)]
      · rw [cap_f4]; nlinarith [F.neg 4 1 (by decide)]
      · exact absurd rfl h5')
  have e : (univ \ cellP.U : Finset (Fin 9)) = {0, 1, 2, 4, 5} := by decide
  rw [e]; exact hcell

/-- **W2-OC (apex form):** `W2OCAt x F cc` gives a view `w` of the open cell `P` (near the wall line at `cc`)
with a strict-apex order certificate on the rim `0.4.6.2.5`. -/
theorem w2oc_exists_apex {F : S0xFac 9 s0x_S24 x} {cc : ℝ} (h : W2OCAt x F cc) :
    ∃ w : ℝ³, CellAt F cellP.U (univ \ cellP.U) w ∧ ApexCert (fun i => x (cellP.r i)) w := by
  obtain ⟨h5, hw5, hw4, h3, h6, h8, hf, z02, z05, z42, z45, z62, z65, hne⟩ := h
  have hcc : 0 < cc := lt_trans (one_div_pos.mpr h5) hw5
  have ha5 := w2oc_a5 F hf
  have T := type24OfFac F
  have hD : det24 x ≠ 0 := T.det_ne
  have hcell := w2oc_cellAt_eventually F h5 hw5 hw4 h3 h6 h8
  -- the height inequalities along the wall line
  have evB5 := w2oc_ev_pos (oblX0 x 5 * (1 + cc)) (-(oblX2 x 5 + oblX6 x 5 - 1)) (by nlinarith)
  have evE := w2oc_ev_pos ((oblX0 x 5 - 1) * (1 + cc)) (-(oblX2 x 5 + oblX6 x 5)) (by nlinarith)
  have key : ∀ w, CellAt F cellP.U (univ \ cellP.U) w → ∀ η : ℝ, w = capView x η 1 cc →
      0 < oblX0 x 5 * (1 + cc) + η * (-(oblX2 x 5 + oblX6 x 5 - 1)) →
      0 < (oblX0 x 5 - 1) * (1 + cc) + η * (-(oblX2 x 5 + oblX6 x 5)) →
      ∃ ρ : ℝ, (ρ = 1 ∨ ρ = -1) ∧ ρ * det24 x < 0 ∧
        (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
          0 < ρ * Split.det3 (x (rP (i + 1)) - x (rP i)) (x (rP j) - x (rP i)) w) := by
    intro w hw η hη hB5 hE
    obtain ⟨ρ, hρ, hrim⟩ := rimSign_of_cell F cellP hw
    have hrim5 : ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
        0 < ρ * Split.det3 (x (rP (i + 1)) - x (rP i)) (x (rP j) - x (rP i)) w := hrim
    refine ⟨ρ, hρ, ?_, hrim5⟩
    have hO : 0 < ρ * Split.det3 (x 2 - x 6) (x 5 - x 6) w := hrim5 2 4 (by decide) (by decide)
    have e : Split.det3 (x 2 - x 6) (x 5 - x 6) w = -Split.det3 (x 5 - x 6) (x 2 - x 6) w := by
      simp only [Split.det3, PiLp.sub_apply]; ring
    rw [e, hη, w2oc_h62_5 F] at hO
    by_contra hcon
    push Not at hcon
    have : 0 ≤ ρ * det24 x * (oblX0 x 5 * (1 + cc) - η * (oblX2 x 5 + oblX6 x 5 - 1)) :=
      mul_nonneg hcon (by linarith)
    nlinarith
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- `z2 < z5`: base edge `5 - 0`, apex `2`
    have evz := (wall126_lt_eventually hlt).and ((wall126_lt_eventually z02).and
      ((wall126_lt_eventually z42).and (wall126_lt_eventually z62)))
    obtain ⟨η, hc, hB5, hE, l25, l02, l42, l62⟩ := (hcell.and (evB5.and (evE.and evz))).exists
    obtain ⟨ρ, hρ, hρD, hrim5⟩ := key _ hc η rfl (by linarith) (by linarith)
    refine ⟨_, hc, w2oc_apexB hρ hrim5 ?_ l25 l02 l42 l62⟩
    have hb := w2oc_hB F η cc
    have h1 : ρ * Split.det3 (x 2 - x 5) (x 0 - x 5) (capView x η 1 cc) -
        ρ * Split.det3 (x 6 - x 5) (x 0 - x 5) (capView x η 1 cc) =
        (ρ * det24 x) * ((oblX0 x 5 - 1) * (1 + cc) + η * (-(oblX2 x 5 + oblX6 x 5))) := by
      linear_combination (-ρ) * hb
    have := mul_neg_of_neg_of_pos hρD (show 0 < (oblX0 x 5 - 1) * (1 + cc) + η * (-(oblX2 x 5 + oblX6 x 5)) by
      linarith)
    linarith
  · -- `z5 < z2`: base edge `6 - 2`, apex `5`
    have evz := (wall126_lt_eventually hgt).and ((wall126_lt_eventually z05).and
      ((wall126_lt_eventually z45).and (wall126_lt_eventually z65)))
    obtain ⟨η, hc, hB5, hE, l52, l05, l45, l65⟩ := (hcell.and (evB5.and (evE.and evz))).exists
    obtain ⟨ρ, hρ, hρD, hrim5⟩ := key _ hc η rfl (by linarith) (by linarith)
    refine ⟨_, hc, w2oc_apexA hρ hrim5 ?_ l52 l05 l45 l65⟩
    have h1 : ρ * Split.det3 (x 5 - x 6) (x 2 - x 6) (capView x η 1 cc) -
        ρ * Split.det3 (x 0 - x 6) (x 2 - x 6) (capView x η 1 cc) =
        (ρ * det24 x) * ((oblX0 x 5 - 1) * (1 + cc) + η * (-(oblX2 x 5 + oblX6 x 5))) := by
      rw [w2oc_h62_5 F, w2oc_h62_0]; ring
    have := mul_neg_of_neg_of_pos hρD (show 0 < (oblX0 x 5 - 1) * (1 + cc) + η * (-(oblX2 x 5 + oblX6 x 5)) by
      linarith)
    linarith

/-- **W2-OC (cell form):** `W2OCAt x F cc` gives a cell certificate of the pentagon `P`. -/
theorem w2oc_exists_cellCert {F : S0xFac 9 s0x_S24 x} {cc : ℝ} (h : W2OCAt x F cc) :
    ∃ w : ℝ³, CellCert F cellP w := by
  obtain ⟨w, hcell, hA⟩ := w2oc_exists_apex h
  exact ⟨w, hcell, Or.inr (Or.inl hA)⟩

/-- **W2-OC (Split leaf):** `W2OC x F` gives `Gen.SplitAny F`. -/
theorem splitAny_of_w2oc {F : S0xFac 9 s0x_S24 x} (h : W2OC x F) : Gen.SplitAny F := by
  obtain ⟨cc, hcc⟩ := h
  obtain ⟨w, hcell, hA⟩ := w2oc_exists_apex hcc
  exact splitAny_of_cellApex F cellP hcell hA

/-- **W2-OC, `π_24` twin** (pair `{4, 6}`, `a4 > 1`): `W2OC (x ∘ Sym.pi24) (Sym.sym24 F)` gives `Gen.SplitAny F`. -/
theorem splitAny_of_w2oc_twin {F : S0xFac 9 s0x_S24 x}
    (h : W2OC (x ∘ Sym.pi24) (Sym.sym24 F)) : Gen.SplitAny F :=
  Sym.splitAny24_sym F (splitAny_of_w2oc h)

/-- **W2-OC in the cell cover:** a list containing `P` has empty cell-cover residue on `W2OC` (either side). -/
theorem not_cellCoverResidue_of_w2oc {L : List Cell24} (hL : cellP ∈ L) {F : S0xFac 9 s0x_S24 x}
    (h : W2OC x F ∨ W2OC (x ∘ Sym.pi24) (Sym.sym24 F)) : ¬ CellCoverResidue L x F := by
  intro hres
  rcases h with ⟨cc, h⟩ | ⟨cc, h⟩
  · obtain ⟨w, hw⟩ := w2oc_exists_cellCert h
    exact (hres.2.2.2 cellP hL w).1 hw
  · obtain ⟨w, hw⟩ := w2oc_exists_cellCert h
    exact (hres.2.2.2 cellP hL w).2 hw

/-- **W2-OC hole fact:** `HoleLeaf x F` excludes `W2OC x F`. -/
theorem holeLeaf_not_w2oc {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : ¬ W2OC x F :=
  fun h => hF.2.2.2.2.1 (splitAny_of_w2oc h)

/-- **W2-OC twin hole fact:** `HoleLeaf x F` excludes `W2OC (x ∘ Sym.pi24) (Sym.sym24 F)`. -/
theorem holeLeaf_not_w2oc_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) :
    ¬ W2OC (x ∘ Sym.pi24) (Sym.sym24 F) :=
  fun h => hF.2.2.2.2.1 (splitAny_of_w2oc_twin h)

end Minimality.T24.Cell
