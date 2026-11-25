module

public import Minimality.SplitRows

@[expose] public section

/-!
# SplitRows from a screen apex and a depth split (`Task EF`)

General `k ≥ 3` sufficiency of unimodal height `ρ * det3 (X j - X a) (X (a + 1) - X a) w`
together with depth separation at its strict minimiser `c` for `SplitRows X w a c σ`.
-/

set_option autoImplicit false

open scoped RealInnerProductSpace
open Minimality.Split

namespace Minimality.Split

/-- Plücker identity for `det3 · · w` in `ℝ³`:
`det3 e₁ e₂ w * det3 d y w = det3 d e₂ w * det3 e₁ y w + det3 e₁ d w * det3 e₂ y w`. -/
private theorem det3_plucker (e₁ e₂ d y w : ℝ³) :
    det3 e₁ e₂ w * det3 d y w = det3 d e₂ w * det3 e₁ y w + det3 e₁ d w * det3 e₂ y w := by
  simp only [det3]
  ring

/-- **APPROVED (Task EF).**  Sufficiency of "unimodal height + separated depths" for split rows
on a strict `k`-rim (`k ≥ 3`). -/
theorem splitRows_of_unimodal_separated {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    {X : ZMod k → ℝ³} {w : ℝ³} {ρ σ : ℝ}
    (hcyc : ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 →
      0 < ρ * det3 (X (i + 1) - X i) (X j - X i) w)
    {a c : ZMod k} (hca : c ≠ a) (hca1 : c ≠ a + 1)
    (hext : ∀ j : ZMod k, j ≠ a → j ≠ a + 1 → j ≠ c →
      ρ * det3 (X c - X a) (X (a + 1) - X a) w < ρ * det3 (X j - X a) (X (a + 1) - X a) w)
    (hfirst : ∀ j : ZMod k, (j - a - 1).val < (c - a - 1).val →
      σ * ρ * (⟪X j, w⟫ - ⟪X c, w⟫) < 0)
    (hsecond : ∀ j : ZMod k, (c - a - 1).val < (j - a - 1).val →
      0 < σ * ρ * (⟪X j, w⟫ - ⟪X c, w⟫)) :
    SplitRows X w a c σ := by
  have : Fact (1 < k) := ⟨by omega⟩
  let d : ℝ³ := X (a + 1) - X a
  let h : ZMod k → ℝ := fun j => det3 (X j - X a) d w
  let g : ZMod k → ℝ := fun j => ρ * h j
  let rise : ZMod k → ℝ := fun i => det3 (X (i + 1) - X i) d w
  have ha1_ne_a : a + 1 ≠ a := by
    intro h0
    have : (1 : ZMod k) = 0 := by linear_combination h0
    exact one_ne_zero this
  have ha2_ne_a : a + 2 ≠ a := by
    intro h0
    have h2 : ((2 : ℕ) : ZMod k) = 0 := by push_cast; linear_combination h0
    have hv := congrArg ZMod.val h2
    rw [ZMod.val_zero, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)] at hv
    omega
  have ha2_ne_a1 : a + 2 ≠ a + 1 := by
    intro h0
    have : (1 : ZMod k) = 0 := by linear_combination h0
    exact one_ne_zero this
  have hρ_ne : ρ ≠ 0 := by
    have hpos := hcyc a (a + 2) ha2_ne_a ha2_ne_a1
    intro h0
    rw [h0, zero_mul] at hpos
    exact lt_irrefl 0 hpos
  have hρ2 : 0 < ρ * ρ := mul_self_pos.mpr hρ_ne
  have hrise_eq : ∀ i : ZMod k, rise i = h (i + 1) - h i := by
    intro i
    simp only [rise, h, d, det3, PiLp.sub_apply]
    ring
  have ha_zero : g a = 0 := by
    simp only [g, h, d, det3, PiLp.sub_apply]
    ring
  have ha1_zero : g (a + 1) = 0 := by
    simp only [g, h, d, det3, PiLp.sub_apply]
    ring
  have hg_neg : ∀ j : ZMod k, j ≠ a → j ≠ a + 1 → g j < 0 := by
    intro j hja hja1
    have hc := hcyc a j hja hja1
    have hdet : det3 (X (a + 1) - X a) (X j - X a) w = -h j := by
      simp only [h, d, det3, PiLp.sub_apply]
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
    have hpl := det3_plucker (X (i + 1) - X i) (X (i + 2) - X (i + 1)) d (X (i + 1) - X a) w
    have h_e12 : 0 < ρ * det3 (X (i + 1) - X i) (X (i + 2) - X (i + 1)) w := by
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
      have h_det : det3 (X (i + 1) - X i) (X (i + 2) - X (i + 1)) w =
          det3 (X (i + 1) - X i) (X (i + 2) - X i) w := by
        simp only [det3, PiLp.sub_apply]
        ring
      rw [h_det]
      exact hcyc i (i + 2) hi2_ne_i hi2_ne_i1
    have h_dy : 0 < ρ * det3 d (X (i + 1) - X a) w := by
      have h_eq : det3 d (X (i + 1) - X a) w = -h (i + 1) := by
        simp only [h, d, det3, PiLp.sub_apply]
        ring
      rw [h_eq]
      have hg_neg_i1 := hg_neg (i + 1) hi1a hi1_ne_a1
      dsimp [g] at hg_neg_i1
      linarith
    have h_e1y : ρ * det3 (X (i + 1) - X i) (X (i + 1) - X a) w ≤ 0 := by
      have h_eq : det3 (X (i + 1) - X i) (X (i + 1) - X a) w =
          -det3 (X (i + 1) - X i) (X a - X i) w := by
        simp only [det3, PiLp.sub_apply]
        ring
      rw [h_eq]
      have hc := hcyc i a hia.symm hi1a.symm
      linarith
    have h_e2y : ρ * det3 (X (i + 2) - X (i + 1)) (X (i + 1) - X a) w ≤ 0 := by
      by_cases hi2a : i + 2 = a
      · have h_zero : det3 (X (i + 2) - X (i + 1)) (X (i + 1) - X a) w = 0 := by
          rw [hi2a]
          simp only [det3, PiLp.sub_apply]
          ring
        rw [h_zero, mul_zero]
      · have hi2_eq : i + 2 = (i + 1) + 1 := by ring
        have hc := hcyc (i + 1) a hi1a.symm (by rw [← hi2_eq]; exact Ne.symm hi2a)
        have h_eq : det3 (X (i + 2) - X (i + 1)) (X (i + 1) - X a) w =
            -det3 (X ((i + 1) + 1) - X (i + 1)) (X a - X (i + 1)) w := by
          rw [← hi2_eq]
          simp only [det3, PiLp.sub_apply]
          ring
        rw [h_eq]
        linarith
    have h_de2 : ρ * det3 d (X (i + 2) - X (i + 1)) w = -(g (i + 2) - g (i + 1)) := by
      have h_eq : det3 d (X (i + 2) - X (i + 1)) w = -rise (i + 1) := by
        simp only [rise, d, det3, PiLp.sub_apply]
        ring
      rw [h_eq, hrise_eq]
      have h12 : (i + 1) + 1 = i + 2 := by ring
      rw [h12]
      dsimp [g]
      ring
    have h_e1d : ρ * det3 (X (i + 1) - X i) d w = g (i + 1) - g i := by
      change ρ * rise i = g (i + 1) - g i
      rw [hrise_eq]
      dsimp [g]
      ring
    have h_scaled :
        (ρ * det3 (X (i + 1) - X i) (X (i + 2) - X (i + 1)) w) * (ρ * det3 d (X (i + 1) - X a) w) =
        (ρ * det3 d (X (i + 2) - X (i + 1)) w) * (ρ * det3 (X (i + 1) - X i) (X (i + 1) - X a) w) +
        (ρ * det3 (X (i + 1) - X i) d w) * (ρ * det3 (X (i + 2) - X (i + 1)) (X (i + 1) - X a) w) := by
      linear_combination (ρ * ρ) * hpl
    rw [h_de2, h_e1d] at h_scaled
    by_contra h_not
    push Not at h_not
    have h_lhs : 0 < (ρ * det3 (X (i + 1) - X i) (X (i + 2) - X (i + 1)) w) *
        (ρ * det3 d (X (i + 1) - X a) w) := mul_pos h_e12 h_dy
    have h_t1 : -(g (i + 2) - g (i + 1)) *
        (ρ * det3 (X (i + 1) - X i) (X (i + 1) - X a) w) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) h_e1y
    have h_t2 : (g (i + 1) - g i) *
        (ρ * det3 (X (i + 2) - X (i + 1)) (X (i + 1) - X a) w) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) h_e2y
    linarith
  let idx : ZMod k → ℕ := fun j => (j - a - 1).val
  have hidx_lt : ∀ j : ZMod k, idx j < k := fun j => ZMod.val_lt _
  have hidx_a1 : idx (a + 1) = 0 := by
    dsimp [idx]
    rw [show a + 1 - a - 1 = (0 : ZMod k) by ring, ZMod.val_zero]
  have hidx_a : idx a = k - 1 := by
    dsimp [idx]
    have hk1 : k - 1 < k := by omega
    rw [show a - a - 1 = ((k - 1 : ℕ) : ZMod k) by
      rw [Nat.cast_sub (by omega), ZMod.natCast_self]; ring,
      ZMod.val_natCast, Nat.mod_eq_of_lt hk1]
  have hidx_inj : ∀ j₁ j₂ : ZMod k, idx j₁ = idx j₂ → j₁ = j₂ := by
    intro j₁ j₂ h_eq
    have hv := ZMod.val_injective k h_eq
    linear_combination hv
  have hidx_ne_a : ∀ j : ZMod k, j ≠ a ↔ idx j < k - 1 := by
    intro j
    constructor
    · intro hja
      have hne : idx j ≠ idx a := fun h0 => hja (hidx_inj j a h0)
      rw [hidx_a] at hne
      have hlt := hidx_lt j
      omega
    · intro hlt heq
      subst heq
      rw [hidx_a] at hlt
      omega
  have hidx_succ : ∀ i : ZMod k, i ≠ a → idx (i + 1) = idx i + 1 := by
    intro i hia
    have hlt : idx i < k - 1 := (hidx_ne_a i).mp hia
    dsimp [idx] at hlt ⊢
    rw [show i + 1 - a - 1 = (i - a - 1) + 1 by ring, ZMod.val_add, ZMod.val_one k]
    exact Nat.mod_eq_of_lt (by omega)
  let c0 : ℕ := idx c
  have hc0_pos : 0 < c0 := by
    by_contra h0
    have hc0 : c0 = 0 := by omega
    apply hca1
    exact hidx_inj c (a + 1) (hc0.trans hidx_a1.symm)
  have hc0_lt : c0 < k - 1 := (hidx_ne_a c).mp hca
  have h_min : ∀ n : ℕ, n ≤ k - 1 → n ≠ c0 → g c < g (a + 1 + n) := by
    intro n hn hnc
    have hv : idx (a + 1 + (n : ZMod k)) = n := by
      dsimp [idx]
      rw [show a + 1 + (n : ZMod k) - a - 1 = (n : ZMod k) by ring, ZMod.val_natCast]
      exact Nat.mod_eq_of_lt (by omega)
    have hne_c : a + 1 + (n : ZMod k) ≠ c := by
      intro h0
      apply hnc
      rw [← hv, h0]
    by_cases hn0 : n = 0
    · subst hn0
      rw [Nat.cast_zero, add_zero, ha1_zero]
      exact hg_neg c hca hca1
    · by_cases hnk : n = k - 1
      · subst hnk
        have ha_eq : a + 1 + ((k - 1 : ℕ) : ZMod k) = a := by
          apply hidx_inj
          rw [hv, hidx_a]
        rw [ha_eq, ha_zero]
        exact hg_neg c hca hca1
      · have hne_a : a + 1 + (n : ZMod k) ≠ a := by
          rw [hidx_ne_a, hv]
          omega
        have hne_a1 : a + 1 + (n : ZMod k) ≠ a + 1 := by
          intro h0
          apply hn0
          rw [← hv, h0, hidx_a1]
        exact hext (a + 1 + n) hne_a hne_a1 hne_c
  have h_inc : ∀ n : ℕ, c0 ≤ n → n < k - 1 → g (a + 1 + n) < g (a + 1 + (n + 1 : ℕ)) := by
    intro n hcn
    induction n with
    | zero => omega
    | succ m ih =>
      intro hm1
      by_cases hmc : m + 1 = c0
      · have h0 : g c = g (a + 1 + ((m + 1 : ℕ) : ZMod k)) := by
          congr 1
          apply hidx_inj
          dsimp [idx]
          rw [show a + 1 + ((m + 1 : ℕ) : ZMod k) - a - 1 = ((m + 1 : ℕ) : ZMod k) by ring,
            ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
          exact hmc.symm
        rw [← h0]
        exact h_min (m + 2) (by omega) (by omega)
      · have hcm : c0 ≤ m := by omega
        have ihm := ih hcm (by omega)
        have h_eq1 : a + 1 + ((m + 1 : ℕ) : ZMod k) = (a + 1 + (m : ZMod k)) + 1 := by
          push_cast; ring
        have h_eq2 : a + 1 + ((m + 2 : ℕ) : ZMod k) = (a + 1 + (m : ZMod k)) + 2 := by
          push_cast; ring
        have hia : a + 1 + (m : ZMod k) ≠ a := by
          rw [hidx_ne_a]
          dsimp [idx]
          rw [show a + 1 + (m : ZMod k) - a - 1 = (m : ZMod k) by ring,
            ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
          omega
        have hi1a : (a + 1 + (m : ZMod k)) + 1 ≠ a := by
          rw [← h_eq1, hidx_ne_a]
          dsimp [idx]
          rw [show a + 1 + ((m + 1 : ℕ) : ZMod k) - a - 1 = ((m + 1 : ℕ) : ZMod k) by ring,
            ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
          omega
        rw [h_eq1, h_eq2]
        rw [h_eq1] at ihm
        exact h_no_max (a + 1 + m) hia hi1a ihm.le
  have h_dec : ∀ d : ℕ, 1 ≤ d → d ≤ c0 →
      g (a + 1 + (c0 - d + 1 : ℕ)) < g (a + 1 + (c0 - d : ℕ)) := by
    intro d hd1 hdc
    induction d with
    | zero => omega
    | succ m ih =>
      by_cases hm0 : m = 0
      · subst hm0
        have h0 : g c = g (a + 1 + (c0 : ZMod k)) := by
          congr 1
          apply hidx_inj
          dsimp [idx]
          rw [show a + 1 + (c0 : ZMod k) - a - 1 = (c0 : ZMod k) by ring,
            ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
        rw [show c0 - 1 + 1 = c0 by omega, ← h0]
        exact h_min (c0 - 1) (by omega) (by omega)
      · have ihm := ih (by omega) (by omega)
        have hsub : c0 - m = (c0 - (m + 1)) + 1 := by omega
        have h_eq1 : a + 1 + ((c0 - (m + 1) + 1 : ℕ) : ZMod k) =
            (a + 1 + ((c0 - (m + 1) : ℕ) : ZMod k)) + 1 := by
          push_cast; ring
        have h_eq2 : a + 1 + ((c0 - m + 1 : ℕ) : ZMod k) =
            (a + 1 + ((c0 - (m + 1) : ℕ) : ZMod k)) + 2 := by
          rw [hsub]
          push_cast; ring
        have hia : a + 1 + ((c0 - (m + 1) : ℕ) : ZMod k) ≠ a := by
          rw [hidx_ne_a]
          dsimp [idx]
          rw [show a + 1 + ((c0 - (m + 1) : ℕ) : ZMod k) - a - 1 =
              ((c0 - (m + 1) : ℕ) : ZMod k) by ring,
            ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
          omega
        have hi1a : (a + 1 + ((c0 - (m + 1) : ℕ) : ZMod k)) + 1 ≠ a := by
          rw [← h_eq1, hidx_ne_a]
          dsimp [idx]
          rw [show a + 1 + ((c0 - (m + 1) + 1 : ℕ) : ZMod k) - a - 1 =
              ((c0 - (m + 1) + 1 : ℕ) : ZMod k) by ring,
            ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
          omega
        have h_not_le : ¬ g (a + 1 + ((c0 - (m + 1) : ℕ) : ZMod k)) ≤
            g ((a + 1 + ((c0 - (m + 1) : ℕ) : ZMod k)) + 1) := by
          intro hle
          have hgt := h_no_max (a + 1 + ((c0 - (m + 1) : ℕ) : ZMod k)) hia hi1a hle
          rw [← h_eq1, show a + 1 + ((c0 - (m + 1) : ℕ) : ZMod k) + 2 =
            a + 1 + ((c0 - (m + 1) + 1 + 1 : ℕ) : ZMod k) by push_cast; ring] at hgt
          rw [hsub] at ihm
          linarith
        rw [h_eq1]
        exact lt_of_not_ge h_not_le
  intro i j hia hij hjc
  have hi_lt : idx i < k - 1 := (hidx_ne_a i).mp hia
  have hi_eq : i = a + 1 + (idx i : ZMod k) := by
    apply hidx_inj
    dsimp [idx]
    rw [show a + 1 + (idx i : ZMod k) - a - 1 = (idx i : ZMod k) by ring,
      ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have hi1_eq : i + 1 = a + 1 + ((idx i + 1 : ℕ) : ZMod k) := by
    push_cast
    linear_combination hi_eq
  have hinner : ⟪X j - X c, w⟫ = ⟪X j, w⟫ - ⟪X c, w⟫ := inner_sub_left _ _ _
  have hmul : ρ * ρ * (σ * (⟪X j - X c, w⟫ * rise i)) =
      (σ * ρ * (⟪X j, w⟫ - ⟪X c, w⟫)) * (g (i + 1) - g i) := by
    rw [hinner, hrise_eq]
    dsimp [g]
    ring
  have hpos_prod : 0 < (σ * ρ * (⟪X j, w⟫ - ⟪X c, w⟫)) * (g (i + 1) - g i) := by
    by_cases hic : idx i < c0
    · have hj_lt : idx j < c0 := by
        rcases hij with rfl | rfl
        · exact hic
        · rw [hidx_succ i hia]
          have hj_ne : idx (i + 1) ≠ c0 := fun h0 => hjc (hidx_inj (i + 1) c h0)
          rw [hidx_succ i hia] at hj_ne
          omega
      have hz := hfirst j hj_lt
      have hd := h_dec (c0 - idx i) (by omega) (by omega)
      rw [show c0 - (c0 - idx i) = idx i by omega] at hd
      rw [← hi_eq, ← hi1_eq] at hd
      exact mul_pos_of_neg_of_neg hz (sub_neg.mpr hd)
    · have hic_le : c0 ≤ idx i := by omega
      have hj_gt : c0 < idx j := by
        rcases hij with rfl | rfl
        · have hj_ne : idx j ≠ c0 := fun h0 => hjc (hidx_inj j c h0)
          omega
        · rw [hidx_succ i hia]
          omega
      have hz := hsecond j hj_gt
      have hi_inc := h_inc (idx i) hic_le hi_lt
      rw [← hi_eq, ← hi1_eq] at hi_inc
      exact mul_pos hz (sub_pos.mpr hi_inc)
  rw [← hmul] at hpos_prod
  exact pos_of_mul_pos_right hpos_prod hρ2.le

end Minimality.Split

end section
