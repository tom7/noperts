module

public import Minimality.TwoRayCell

@[expose] public section

/-!
# V1b: diagonal variant (a popped corner on ray P)

Cycle `(w, p, far_P, rest…, far_Q)` with `p = (s0, 0, z0)` the popped vertex of the quad `P` (on the diagonal
`w–far_P` in the screen, off it by `z0 σP > 0`); all of `w, p, far_P` are screen-collinear, the tie is broken by the
tilt `v₂ = σP`.  Other side points of ray P have `z σP < 0` (the other popped vertex).
-/

set_option autoImplicit true
set_option linter.unusedVariables false
open scoped RealInnerProductSpace
open Finset Filter

namespace Minimality
namespace TwoRay
open Type08Sp Type08Sp.C2

theorem natCast_ne_zero_zmod {k n : ℕ} (hn : 0 < n) (hnk : n < k) : (n : ZMod k) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have := Nat.le_of_dvd hn h
  omega

theorem mix_inside2 {k : ℕ} [NeZero k] (Y : ZMod k → ℝ × ℝ × ℝ) (a b i : ZMod k)
    (na : 0 ≤ cross2 (Y (i + 1) - Y i) (Y a - Y i)) (nb : 0 ≤ cross2 (Y (i + 1) - Y i) (Y b - Y i))
    (hab : 0 < cross2 (Y (i + 1) - Y i) (Y a - Y i) ∨ 0 < cross2 (Y (i + 1) - Y i) (Y b - Y i))
    (t : ℝ × ℝ × ℝ) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (h1 : t.1 = (1 - s) * (Y a).1 + s * (Y b).1) (h2 : t.2.1 = (1 - s) * (Y a).2.1 + s * (Y b).2.1) :
    0 < cross2 (Y (i + 1) - Y i) (t - Y i) := by
  have hid : cross2 (Y (i + 1) - Y i) (t - Y i) =
      (1 - s) * cross2 (Y (i + 1) - Y i) (Y a - Y i) + s * cross2 (Y (i + 1) - Y i) (Y b - Y i) := by
    simp only [cross2, Prod.fst_sub, Prod.snd_sub, h1, h2]; ring
  rw [hid]
  have hs1' : 0 < 1 - s := by linarith
  rcases hab with h | h <;> nlinarith

set_option maxHeartbeats 3200000 in
/-- **V1b** (frame form, diagonal variant). -/
theorem v1b_hasLexCellAt (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0) {k : ℕ} [NeZero k] (hk : 4 ≤ k)
    (Y : ZMod k → ℝ × ℝ × ℝ) {s0 z0 : ℝ} (hY0 : Y 0 = (0, 0, 0)) (hY1 : Y 1 = (s0, 0, z0))
    (hY2 : Y 2 = (1, 0, 0)) (hYm : Y (-1) = (0, 1, 0)) (hs0 : 0 < s0) (hs1 : s0 < 1)
    {σP σQ : ℝ} (hσP : σP ≠ 0) (hσQ : σQ ≠ 0) (hz0 : 0 < z0 * σP)
    (hmem : ∀ i, fpoint p q r d (Y i) ∈ V)
    (hconv : ∀ i j, j ≠ i → j ≠ i + 1 → ¬ (i = 0 ∧ j = 2) → ¬ (i = 1 ∧ j = 0) →
      0 < cross2 (Y (i + 1) - Y i) (Y j - Y i))
    (hdep : LexUni (fun i => ⟪fpoint p q r d (Y i), r⟫) (fun _ => 0))
    (hV : ∀ y ∈ V, (∀ j, y ≠ fpoint p q r d (Y j)) → ∃ t, y = fpoint p q r d t ∧
      ((∀ i, 0 < cross2 (Y (i + 1) - Y i) (t - Y i)) ∨
       (∃ s z : ℝ, t = (s, 0, z) ∧ 0 < s ∧ s < 1 ∧ z * σP < 0) ∨
       (∃ s z : ℝ, t = (0, s, z) ∧ 0 < s ∧ s < 1 ∧ z * σQ < 0))) :
    HasLexCellAt V r := by
  have n1 : (1 : ZMod k) ≠ 0 := by simpa using natCast_ne_zero_zmod (k := k) (n := 1) (by norm_num) (by omega)
  have n2 : (2 : ZMod k) ≠ 0 := by simpa using natCast_ne_zero_zmod (k := k) (n := 2) (by norm_num) (by omega)
  have n3 : (3 : ZMod k) ≠ 0 := by simpa using natCast_ne_zero_zmod (k := k) (n := 3) (by norm_num) (by omega)
  have hinj : ∀ i j, Y i = Y j → i = j := fun i j h => hdep.1 i j (by simp [h]) rfl
  have hv2 : ∀ lam : ℝ, σP + lam * 0 = σP := fun lam => by ring
  -- tie values
  have t02 : cross2 (Y (0 + 1) - Y 0) (Y 2 - Y 0) = 0 := by
    simp [zero_add, hY0, hY1, hY2, cross2]
  have t10 : cross2 (Y (1 + 1) - Y 1) (Y 0 - Y 1) = 0 := by
    have : (1 : ZMod k) + 1 = 2 := by norm_num
    rw [this]; simp only [hY0, hY1, hY2, cross2, Prod.fst_sub, Prod.snd_sub]; ring
  have hnn : ∀ i j, 0 ≤ cross2 (Y (i + 1) - Y i) (Y j - Y i) := by
    intro i j
    by_cases h1 : j = i
    · subst h1; simp [cross2]
    by_cases h2 : j = i + 1
    · subst h2; simp only [cross2]; ring_nf; exact le_refl _
    by_cases h3 : i = 0 ∧ j = 2
    · obtain ⟨rfl, rfl⟩ := h3; rw [t02]
    by_cases h4 : i = 1 ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := h4; rw [t10]
    exact (hconv i j h1 h2 h3 h4).le
  have hcyc : ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ D : ℝ, 0 < D → ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 →
      TSc D (Y (i + 1) - Y i) (Y j - Y i) (σQ + lam * (σQ / 2), σP + lam * 0, 0) := by
    intro lam hl0 hl1 D hD i j a b
    by_cases h3 : i = 0 ∧ j = 2
    · obtain ⟨rfl, rfl⟩ := h3
      right
      simp only [zero_add, hY0, hY1, hY2, d3, Prod.mk_sub_mk, Prod.fst_sub, Prod.snd_sub]
      refine ⟨by ring, ?_⟩
      nlinarith [mul_pos hD hz0]
    by_cases h4 : i = 1 ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := h4
      right
      have : (1 : ZMod k) + 1 = 2 := by norm_num
      rw [this]
      simp only [hY0, hY1, hY2, d3, Prod.mk_sub_mk, Prod.fst_sub, Prod.snd_sub]
      refine ⟨by ring, ?_⟩
      nlinarith [mul_pos hD hz0]
    exact tsc_of_cross hD (hconv i j a b h3 h4)
  refine k3_cell_gen V p q r d hΔ (by omega) Y hinj (u1 := σQ) (u2 := σP) (t1 := σQ / 2) (t2 := 0)
    (by intro h; apply mul_ne_zero hσP hσQ; linarith) hmem hcyc ?_
    (fun w _ => lexUni_any _ w hdep n1)
  intro y hy hyx
  obtain ⟨t, hyt, ht⟩ := hV y hy hyx
  refine ⟨t, hyt, ?_⟩
  intro lam hl0 hl1 D hD i
  rcases ht with hin | ⟨s, z, rfl, hs0', hs1', hz⟩ | ⟨s, z, rfl, hs0', hs1', hz⟩
  · exact tsc_of_cross hD (hin i)
  · -- side point on ray P
    by_cases hi0 : i = 0
    · subst hi0
      right
      simp only [zero_add, hY0, hY1, d3, Prod.mk_sub_mk, Prod.fst_sub, Prod.snd_sub]
      refine ⟨by ring, ?_⟩
      nlinarith [mul_pos hD (mul_pos hz0 hs0'), mul_pos hD (mul_pos hs0 (neg_pos.2 hz))]
    by_cases hi1 : i = 1
    · subst hi1
      right
      have : (1 : ZMod k) + 1 = 2 := by norm_num
      rw [this]
      simp only [hY1, hY2, d3, Prod.mk_sub_mk, Prod.fst_sub, Prod.snd_sub]
      refine ⟨by ring, ?_⟩
      have h1s : 0 < 1 - s := by linarith
      have h1s0 : 0 < 1 - s0 := by linarith
      nlinarith [mul_pos hD (mul_pos hz0 h1s), mul_pos hD (mul_pos h1s0 (neg_pos.2 hz))]
    · refine tsc_of_cross hD (mix_inside2 Y 0 2 i (hnn _ _) (hnn _ _) ?_ _ hs0' hs1' ?_ ?_)
      · by_cases him : i = -1
        · right
          refine hconv i 2 ?_ ?_ ?_ ?_
          · intro h; apply n3; subst him; linear_combination h
          · intro h; subst him; apply n2; linear_combination h
          · intro h; exact hi0 h.1
          · intro h; exact hi1 h.1
        · left
          refine hconv i 0 (fun h => hi0 h.symm) (fun h => him (by linear_combination -h)) ?_ ?_
          · intro h; exact hi0 h.1
          · intro h; exact hi1 h.1
      · simp [hY0, hY2]
      · simp [hY0, hY2]
  · -- side point on ray Q
    by_cases hi : i = -1
    · subst hi
      right
      simp only [neg_add_cancel, hYm, hY0, d3, Prod.mk_sub_mk, Prod.fst_sub, Prod.snd_sub]
      refine ⟨by ring, ?_⟩
      have hl : 0 < 1 + lam / 2 := by linarith
      nlinarith [mul_pos (mul_pos hD (neg_pos.2 hz)) hl]
    · refine tsc_of_cross hD (mix_inside2 Y 0 (-1) i (hnn _ _) (hnn _ _) ?_ _ hs0' hs1' ?_ ?_)
      · by_cases him : i = -2
        · left
          refine hconv i 0 ?_ ?_ ?_ ?_
          · intro h; apply n2; subst him; linear_combination h
          · intro h; apply hi; linear_combination -h
          · intro h; exact n2 (by linear_combination -h.2)
          · intro h; exact n3 (by linear_combination him - h.1)
        · right
          refine hconv i (-1) (fun h => hi h.symm) (fun h => him (by linear_combination -h)) ?_ ?_
          · intro h; exact n3 (by linear_combination -h.2)
          · intro h; exact n1 (by linear_combination -h.2)
      · simp [hY0, hYm]
      · simp [hY0, hYm]

end TwoRay
end Minimality

