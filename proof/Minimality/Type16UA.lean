module

public import Minimality.TwoRayCell

@[expose] public section


/-!
# U0: EV1, the two-ray cell at an edge view (type-free)

`TwoRay.v1_hasLexCellAt` with one more point over the corner `w = Y 0`: the other end of the viewed edge,
`t = (0, 0, z)` with `z σP < 0` and `z σQ < 0`.  Two forms: `ev1_hasLexCellAt` (distinct depths) and
`ev1_cell_gen` (tie variant: `hlex` as in `k3_cell_gen`, the second key is the tilt depth).
-/

set_option autoImplicit true
set_option linter.unusedVariables false
open scoped RealInnerProductSpace
open Finset Filter

namespace Minimality
namespace H16U
open TwoRay Type08Sp Type08Sp.C2

set_option maxHeartbeats 1600000 in
/-- **EV1, tie variant** (`hlex` is the `k3_cell_gen` hypothesis: the lex unimodality for every second key
that separates ties). -/
theorem h16u_ev1_cell_gen (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (Y : ZMod k → ℝ × ℝ × ℝ) (hY0 : Y 0 = (0, 0, 0)) (hY1 : Y 1 = (1, 0, 0)) (hYm : Y (-1) = (0, 1, 0))
    (hinj : ∀ i j, Y i = Y j → i = j)
    (hmem : ∀ i, fpoint p q r d (Y i) ∈ V)
    (hconv : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < TwoRay.cross2 (Y (i + 1) - Y i) (Y j - Y i))
    (hlex : ∀ w : ZMod k → ℝ, (∀ i j, ⟪fpoint p q r d (Y i), r⟫ = ⟪fpoint p q r d (Y j), r⟫ → w i = w j → i = j) →
      LexUni (fun i => ⟪fpoint p q r d (Y i), r⟫) w)
    {σP σQ : ℝ} (hσP : σP ≠ 0) (hσQ : σQ ≠ 0)
    (hV : ∀ y ∈ V, (∀ j, y ≠ fpoint p q r d (Y j)) → ∃ t, y = fpoint p q r d t ∧
      ((∀ i, 0 < TwoRay.cross2 (Y (i + 1) - Y i) (t - Y i)) ∨
       (∃ s z : ℝ, t = (s, 0, z) ∧ 0 < s ∧ s < 1 ∧ z * σP < 0) ∨
       (∃ s z : ℝ, t = (0, s, z) ∧ 0 < s ∧ s < 1 ∧ z * σQ < 0) ∨
       (∃ z : ℝ, t = (0, 0, z) ∧ z * σP < 0 ∧ z * σQ < 0))) :
    HasLexCellAt V r := by
  have h1 := one_ne_zero_zmod hk
  have h2 := two_ne_zero_zmod hk
  have hcyc : ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ D : ℝ, 0 < D → ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 →
      TSc D (Y (i + 1) - Y i) (Y j - Y i) (σQ + lam * (σQ / 2), σP + lam * 0, 0) :=
    fun _ _ _ D hD i j a b => tsc_of_cross hD (hconv i j a b)
  refine k3_cell_gen V p q r d hΔ hk Y hinj (u1 := σQ) (u2 := σP) (t1 := σQ / 2) (t2 := 0)
    (by intro h; apply mul_ne_zero hσP hσQ; linarith) hmem hcyc ?_ hlex
  intro y hy hyx
  obtain ⟨t, hyt, ht⟩ := hV y hy hyx
  refine ⟨t, hyt, ?_⟩
  intro lam hl0 hl1 D hD i
  rcases ht with hin | ⟨s, z, rfl, hs0, hs1, hz⟩ | ⟨s, z, rfl, hs0, hs1, hz⟩ | ⟨z, rfl, hzP, hzQ⟩
  · exact tsc_of_cross hD (hin i)
  · by_cases hi : i = 0
    · subst hi
      right
      simp only [zero_add, hY1, hY0, d3, Prod.mk_sub_mk]
      refine ⟨by ring, ?_⟩
      nlinarith [mul_pos hD (neg_pos.2 hz)]
    · refine tsc_of_cross hD (mix_inside Y hconv 0 1 i ?_ _ hs0 hs1 ?_ ?_)
      · by_cases hi0 : i + 1 = 0
        · right
          exact ⟨fun h => h2 (by linear_combination h + hi0), fun h => hi (by linear_combination -h)⟩
        · left
          exact ⟨fun h => hi h.symm, fun h => hi0 h.symm⟩
      · simp [hY0, hY1]
      · simp [hY0, hY1]
  · by_cases hi : i = -1
    · subst hi
      right
      simp only [neg_add_cancel, hYm, hY0, d3, Prod.mk_sub_mk]
      refine ⟨by ring, ?_⟩
      have hl : 0 < 1 + lam / 2 := by linarith
      nlinarith [mul_pos (mul_pos hD (neg_pos.2 hz)) hl]
    · refine tsc_of_cross hD (mix_inside Y hconv 0 (-1) i ?_ _ hs0 hs1 ?_ ?_)
      · by_cases hi0 : i = 0
        · right
          exact ⟨fun h => h1 (by subst hi0; linear_combination -h), fun h => h2 (by subst hi0; linear_combination -h)⟩
        · left
          exact ⟨fun h => hi0 h.symm, fun h => hi (by linear_combination -h)⟩
      · simp [hY0, hYm]
      · simp [hY0, hYm]
  · -- the other end of the viewed edge, over the corner `Y 0`
    by_cases hi : i = 0
    · subst hi
      right
      simp only [zero_add, hY1, hY0, d3, Prod.mk_sub_mk]
      refine ⟨by ring, ?_⟩
      nlinarith [mul_pos hD (neg_pos.2 hzP)]
    · by_cases hi' : i = -1
      · subst hi'
        right
        simp only [neg_add_cancel, hYm, hY0, d3, Prod.mk_sub_mk]
        refine ⟨by ring, ?_⟩
        have hl : 0 < 1 + lam / 2 := by linarith
        nlinarith [mul_pos (mul_pos hD (neg_pos.2 hzQ)) hl]
      · refine tsc_of_cross hD ?_
        have hj0 : (0 : ZMod k) ≠ i := fun h => hi h.symm
        have hj1 : (0 : ZMod k) ≠ i + 1 := by
          intro h; apply hi'; linear_combination -h
        have := hconv i 0 hj0 hj1
        simpa [TwoRay.cross2, hY0] using this

/-- **EV1** (distinct depths on the cycle). -/
theorem h16u_ev1_hasLexCellAt (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (Y : ZMod k → ℝ × ℝ × ℝ) (hY0 : Y 0 = (0, 0, 0)) (hY1 : Y 1 = (1, 0, 0)) (hYm : Y (-1) = (0, 1, 0))
    (hmem : ∀ i, fpoint p q r d (Y i) ∈ V)
    (hconv : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < TwoRay.cross2 (Y (i + 1) - Y i) (Y j - Y i))
    (hdep : LexUni (fun i => ⟪fpoint p q r d (Y i), r⟫) (fun _ => 0))
    {σP σQ : ℝ} (hσP : σP ≠ 0) (hσQ : σQ ≠ 0)
    (hV : ∀ y ∈ V, (∀ j, y ≠ fpoint p q r d (Y j)) → ∃ t, y = fpoint p q r d t ∧
      ((∀ i, 0 < TwoRay.cross2 (Y (i + 1) - Y i) (t - Y i)) ∨
       (∃ s z : ℝ, t = (s, 0, z) ∧ 0 < s ∧ s < 1 ∧ z * σP < 0) ∨
       (∃ s z : ℝ, t = (0, s, z) ∧ 0 < s ∧ s < 1 ∧ z * σQ < 0) ∨
       (∃ z : ℝ, t = (0, 0, z) ∧ z * σP < 0 ∧ z * σQ < 0))) :
    HasLexCellAt V r :=
  h16u_ev1_cell_gen V p q r d hΔ hk Y hY0 hY1 hYm (fun i j h => hdep.1 i j (by simp [h]) rfl) hmem hconv
    (fun w _ => lexUni_any _ w hdep (one_ne_zero_zmod hk)) hσP hσQ hV

end H16U
end Minimality
