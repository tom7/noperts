module

public import Minimality.Type16
public import Minimality.TwoRayCell

@[expose] public section

/-!
# V2 core: the triangle cell at the line of two planes (type-free, affine hypotheses)

`P`, `Q` facet functions (`fP`, `fQ`, negative off their facets), `w` common vertex, `A = far_P ∈ P`, `B = far_Q ∈ Q`,
`r` a direction in both planes.  Every other point `y` of `V` is
* inside: `fQ y < 0, fP y < 0, fQ y/fQ A + fP y/fP B < 1` (strictly inside the screen triangle `w, A, B`), or
* a side point of ray P: `fP y = 0`, `fQ A < fQ y < 0`, and `f3P y < 0` for an edge-facet function `f3P` through `w, A`
  (so all P-side points are on one side of the line `wA` in P's plane), or
* the same for Q.
Then `HasLexCellAt V r`, provided the depths of `w, A, B` along `r` are distinct (metric hypothesis only for
distinctness).
-/

set_option autoImplicit true
set_option linter.unusedVariables false
open scoped RealInnerProductSpace
open Finset Filter

namespace Minimality
namespace V2
open TwoRay Type08Sp Type08Sp.C2

theorem tt_gen (V : Finset ℝ³) (fP fQ f3P f3Q : ℝ³ → ℝ) (NP NQ N3P N3Q : ℝ³)
    (hP : ∀ y z, fP y - fP z = ⟪NP, y - z⟫) (hQ : ∀ y z, fQ y - fQ z = ⟪NQ, y - z⟫)
    (h3P : ∀ y z, f3P y - f3P z = ⟪N3P, y - z⟫) (h3Q : ∀ y z, f3Q y - f3Q z = ⟪N3Q, y - z⟫)
    (w A B r : ℝ³) (hwV : w ∈ V) (hAV : A ∈ V) (hBV : B ∈ V) (hr : r ≠ 0)
    (hPr : ⟪NP, r⟫ = 0) (hQr : ⟪NQ, r⟫ = 0)
    (hPw : fP w = 0) (hPA : fP A = 0) (hPB : fP B < 0) (hQw : fQ w = 0) (hQB : fQ B = 0) (hQA : fQ A < 0)
    (h3Pw : f3P w = 0) (h3PA : f3P A = 0) (h3Qw : f3Q w = 0) (h3QB : f3Q B = 0)
    (hwA : ⟪w, r⟫ ≠ ⟪A, r⟫) (hwB : ⟪w, r⟫ ≠ ⟪B, r⟫) (hAB : ⟪A, r⟫ ≠ ⟪B, r⟫)
    (hcls : ∀ y ∈ V, y ≠ w → y ≠ A → y ≠ B →
      (fQ y < 0 ∧ fP y < 0 ∧ fQ y * fP B + fP y * fQ A < fQ A * fP B) ∨
      (fP y = 0 ∧ fQ A < fQ y ∧ fQ y < 0 ∧ f3P y < 0) ∨
      (fQ y = 0 ∧ fP B < fP y ∧ fP y < 0 ∧ f3Q y < 0)) :
    HasLexCellAt V r := by
  have hv : ∀ {f : ℝ³ → ℝ} {N : ℝ³}, (∀ y z, f y - f z = ⟪N, y - z⟫) → ⟪N, r⟫ = 0 → f w = 0 → f (w + r) = 0 := by
    intro f N hf hNr hfw
    have := hf (w + r) w
    rw [add_sub_cancel_left, hNr] at this
    linarith
  have hPv := hv hP hPr hPw
  have hQv := hv hQ hQr hQw
  have hov : w ≠ w + r := by
    intro h; apply hr; have : w + r = w + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel this
  have hdet := frame16_det_ne hP hQ hPw hPv hPA hPB.ne hQw hQv hQB hQA.ne hov
  rw [add_sub_cancel_left] at hdet
  set p := A - w with hp
  set q := B - w with hq
  let Y : ZMod 3 → ℝ × ℝ × ℝ := fun i => if i = 0 then (0, 0, 0) else if i = 1 then (1, 0, 0) else (0, 1, 0)
  have hY0 : Y 0 = (0, 0, 0) := by simp [Y]
  have hY1 : Y 1 = (1, 0, 0) := by simp [Y]
  have hYm : Y (-1) = (0, 1, 0) := by
    have h1 : (-1 : ZMod 3) ≠ 0 := by decide
    have h2 : (-1 : ZMod 3) ≠ 1 := by decide
    simp [Y, h1, h2]
  have e0 : fpoint p q r w (Y 0) = w := by simp [hY0, fpoint, fcomb]
  have e1 : fpoint p q r w (Y 1) = A := by simp [hY1, fpoint, fcomb, hp]
  have e2 : fpoint p q r w (Y 2) = B := by
    have : Y 2 = (0, 1, 0) := by
      have h1 : (2 : ZMod 3) ≠ 0 := by decide
      have h2 : (2 : ZMod 3) ≠ 1 := by decide
      simp [Y, h1, h2]
    simp [this, fpoint, fcomb, hq]
  have hmem : ∀ i, fpoint p q r w (Y i) ∈ V := by
    intro i
    rcases zmod3_cases i with rfl | rfl | rfl
    · rw [e0]; exact hwV
    · rw [e1]; exact hAV
    · rw [e2]; exact hBV
  have hdist : ∀ i j, ⟪fpoint p q r w (Y i), r⟫ = ⟪fpoint p q r w (Y j), r⟫ → i = j := by
    intro i j h
    rcases zmod3_cases i with rfl | rfl | rfl <;> rcases zmod3_cases j with rfl | rfl | rfl <;>
      simp only [e0, e1, e2] at h <;>
      first
        | rfl
        | exact absurd h hwA | exact absurd h.symm hwA | exact absurd h hwB | exact absurd h.symm hwB
        | exact absurd h hAB | exact absurd h.symm hAB
  have hΔ : det3 p q r ≠ 0 := hdet
  have hY2 : Y 2 = (0, 1, 0) := by
    have h1 : (2 : ZMod 3) ≠ 0 := by decide
    have h2 : (2 : ZMod 3) ≠ 1 := by decide
    simp [Y, h1, h2]
  set σP : ℝ := if f3P (w + r) = 0 then 1 else f3P (w + r) with hσPdef
  set σQ : ℝ := if f3Q (w + r) = 0 then 1 else f3Q (w + r) with hσQdef
  have hσP : σP ≠ 0 := by
    rw [hσPdef]; split_ifs with h
    · exact one_ne_zero
    · exact h
  have hσQ : σQ ≠ 0 := by
    rw [hσQdef]; split_ifs with h
    · exact one_ne_zero
    · exact h
  refine v1_k3 V p q r w hΔ Y hY0 hY1 hYm hmem hdist hσP hσQ ?_
  intro y hy hyx
  have hyw : y ≠ w := fun h => hyx 0 (by rw [e0]; exact h)
  have hyA : y ≠ A := fun h => hyx 1 (by rw [e1]; exact h)
  have hyB : y ≠ B := fun h => hyx 2 (by rw [e2]; exact h)
  obtain ⟨zz, hzz⟩ := frame_coords hP hQ hPw hPv hPA hPB.ne hQw hQv hQB hQA.ne hov y
  refine ⟨(fQ y / fQ A, fP y / fP B, zz), ?_, ?_⟩
  · conv_lhs => rw [hzz]
    simp only [fpoint, fcomb, add_sub_cancel_left, hp, hq]
    abel
  have key3 : ∀ f : ℝ³ → ℝ, ∀ N : ℝ³, (∀ y z, f y - f z = ⟪N, y - z⟫) → f w = 0 →
      f y = fQ y / fQ A * f A + fP y / fP B * f B + zz * f (w + r) := by
    intro f N hf hfw
    have := affine_frame3 hf w A B (w + r) (fQ y / fQ A) (fP y / fP B) zz
    rw [← hzz, hfw] at this
    linarith
  rcases hcls y hy hyw hyA hyB with ⟨c1, c2, c3⟩ | ⟨c1, c2, c3, c4⟩ | ⟨c1, c2, c3, c4⟩
  · left
    have hs : 0 < fQ y / fQ A := div_pos_of_neg_of_neg c1 hQA
    have ht : 0 < fP y / fP B := div_pos_of_neg_of_neg c2 hPB
    have hst : fQ y / fQ A + fP y / fP B < 1 := by
      rw [div_add_div _ _ hQA.ne hPB.ne, div_lt_one (mul_pos_of_neg_of_neg hQA hPB)]
      nlinarith
    intro i
    rcases zmod3_cases i with rfl | rfl | rfl
    · simp only [cross2, hY0, hY1, show (0 : ZMod 3) + 1 = 1 from rfl, Prod.mk_sub_mk]
      simp only [TwoRay.cross2]
      linarith
    · simp only [cross2, hY1, hY2, show (1 : ZMod 3) + 1 = 2 from rfl, Prod.mk_sub_mk]
      simp only [TwoRay.cross2]
      linarith
    · simp only [cross2, hY2, hY0, show (2 : ZMod 3) + 1 = 0 from rfl, Prod.mk_sub_mk]
      simp only [TwoRay.cross2]
      linarith
  · right; left
    refine ⟨fQ y / fQ A, zz, ?_, div_pos_of_neg_of_neg c3 hQA, ?_, ?_⟩
    · simp [c1]
    · rw [div_lt_one_of_neg hQA]; exact c2
    · have := key3 f3P N3P h3P h3Pw
      have hz : f3P y = zz * f3P (w + r) := by rw [this]; simp [c1, h3PA]
      have hc : f3P (w + r) ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hz; linarith
      rw [hσPdef, if_neg hc, ← hz]; exact c4
  · right; right
    refine ⟨fP y / fP B, zz, ?_, div_pos_of_neg_of_neg c3 hPB, ?_, ?_⟩
    · simp [c1]
    · rw [div_lt_one_of_neg hPB]; exact c2
    · have := key3 f3Q N3Q h3Q h3Qw
      have hz : f3Q y = zz * f3Q (w + r) := by rw [this]; simp [c1, h3QB]
      have hc : f3Q (w + r) ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hz; linarith
      rw [hσQdef, if_neg hc, ← hz]; exact c4


end V2
end Minimality
