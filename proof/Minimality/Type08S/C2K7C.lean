module

public import Minimality.Type08S.C2K6
public import Minimality.Type08S.C2K7A

@[expose] public section

/-!
# K7 / C: the 5-cycle cell `(b, a', c, b', c')` at the view `R = b - d` (frame `(P, Q, R) = (c - d, a - d, b - d)`)
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem k7_wd (P Q R d : ℝ³) (s t : ℝ × ℝ × ℝ) (v1 v2 : ℝ) :
    ⟪fpoint P Q R d s, fcomb P Q R v1 v2 0⟫ - ⟪fpoint P Q R d t, fcomb P Q R v1 v2 0⟫ =
      (s.1 - t.1) * (v1 * ⟪P, P⟫ + v2 * ⟪P, Q⟫) + (s.2.1 - t.2.1) * (v1 * ⟪P, Q⟫ + v2 * ⟪Q, Q⟫) +
        (s.2.2 - t.2.2) * (v1 * ⟪P, R⟫ + v2 * ⟪Q, R⟫) := by
  simp only [fpoint, fcomb, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    inner_zero_right, real_inner_comm P Q, real_inner_comm P R, real_inner_comm Q R]
  ring

set_option maxHeartbeats 6400000 in
/-- **The cell at `R = b - d`**: `a' ~ b` and `c' ~ b'` tie at the view (`x = 0`, (B3)), `s = 0`. -/
theorem k7_hasLexCellAt (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0)
    {α1 β1 α4 β6 : ℝ} (hα1 : 1 < α1) (hβ1 : 0 < β1) (hα4 : 0 < α4) (hβ6 : 0 < β6)
    (hB : 0 < ⟪Q, R⟫) (hx : ⟪P, R⟫ + (β6 - 1) * ⟪R, R⟫ = 0) (hs : ⟪P, Q⟫ + (β6 - 1) * ⟪Q, R⟫ = 0)
    (hEq : α1 * ⟪Q, R⟫ + β1 * ⟪R, R⟫ = ⟪P, R⟫ + α4 * ⟪Q, R⟫)
    (hZ : α1 * ⟪Q, R⟫ + β1 * ⟪R, R⟫ < ⟪R, R⟫)
    (hy : 0 < ⟪P, P⟫ + (β6 - 1) * ⟪P, R⟫) (hfac : α4 * (1 - β1) < α1 * β6)
    (hCS : 0 < ⟪Q, Q⟫ * ⟪R, R⟫ - ⟪Q, R⟫ ^ 2)
    (hmem : ∀ i, fpoint P Q R d (k7Cyc α1 β1 α4 β6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, 0) ∨
      y = fpoint P Q R d (0, 0, 1) ∨ y = fpoint P Q R d (1, 0, β6) ∨ y = fpoint P Q R d (1, α4, 0) ∨
      y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (0, α1, β1)) :
    HasLexCellAt V R := by
  have hα1' : 0 < α1 := by linarith
  set Y := k7Cyc α1 β1 α4 β6 with hY
  have hr0 : R ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  have hA : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hr0
  -- the algebra
  set A := ⟪R, R⟫ with hAdef
  set Bp := ⟪Q, R⟫ with hBpdef
  set t := β1 + β6 - 1 with htdef
  have h2 : (α4 - α1) * Bp = t * A := by linear_combination (-1 : ℝ) * hEq - hx
  have ht : t < 0 := by
    by_contra hcon
    push Not at hcon
    have hfac' : α4 * (1 - β1) * Bp < α1 * β6 * Bp := mul_lt_mul_of_pos_right hfac hB
    have h3 : α4 * Bp = α1 * Bp + t * A := by linarith
    have h4 : A * (1 - β1) - α1 * Bp > 0 := by linarith
    nlinarith [mul_nonneg hcon h4.le, h3]
  have hg2 : ⟪P, Q⟫ + (α4 - α1) * ⟪Q, Q⟫ - β1 * Bp < 0 := by
    have hid : Bp * (⟪P, Q⟫ + (α4 - α1) * ⟪Q, Q⟫ - β1 * Bp) = t * (⟪Q, Q⟫ * A - Bp ^ 2) := by
      linear_combination Bp * hs + ⟪Q, Q⟫ * h2
    by_contra hcon
    push Not at hcon
    nlinarith [mul_nonneg hB.le hcon, mul_neg_of_neg_of_pos ht hCS]
  have hg1 : ⟪P, P⟫ + (α4 - α1) * ⟪P, Q⟫ - β1 * ⟪P, R⟫ = ⟪P, P⟫ + (β6 - 1) * ⟪P, R⟫ := by
    linear_combination (α4 - α1) * hs + (1 - β6) * h2 - t * hx
  set g2 := ⟪P, Q⟫ + (α4 - α1) * ⟪Q, Q⟫ - β1 * Bp with hg2def
  set y := ⟪P, P⟫ + (β6 - 1) * ⟪P, R⟫ with hydef
  set τ := (-g2) / (2 * y) with hτdef
  have hτ : 0 < τ := div_pos (by linarith) (by linarith)
  have hτy : τ * y = -g2 / 2 := by rw [hτdef]; field_simp
  obtain ⟨lam, hl0, hl1, hsep⟩ := exists_sep_tilt P Q R d hΔ Y (k7Cyc_inj hα1' hα4 hβ6)
    (u1 := 0) (u2 := 1) (t1 := τ) (t2 := 0) (by simp; exact hτ.ne') (lo := 0) (hi := 1) (by norm_num)
  set v1 := (0 : ℝ) + lam * τ with hv1def
  set v2 := (1 : ℝ) + lam * 0 with hv2def
  set vv := fcomb P Q R v1 v2 0 with hvv
  have hv1 : 0 < v1 := by rw [hv1def]; nlinarith [mul_pos hl0 hτ]
  have hv2 : 0 < v2 := by rw [hv2def]; norm_num
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hw01 : ⟪fpoint P Q R d (1, 0, β6), vv⟫ - ⟪fpoint P Q R d (0, 0, 1), vv⟫ = v1 * y := by
    rw [hvv, k7_wd]; dsimp only
    rw [hydef]; linear_combination v2 * hs
  have hw43 : ⟪fpoint P Q R d (0, α1, β1), vv⟫ - ⟪fpoint P Q R d (1, α4, 0), vv⟫ = -(v1 * y + v2 * g2) := by
    rw [hvv, k7_wd]; dsimp only
    rw [hydef, hg2def]; linear_combination (-v1) * hg1
  have hneg : v1 * y + v2 * g2 < 0 := by
    have : lam * (τ * y) < τ * y := by nlinarith [mul_pos hτ (by linarith : 0 < y)]
    rw [hv1def, hv2def]; nlinarith
  have hlexY : LexUni (fun i => ⟪fpoint P Q R d (Y i), R⟫) (fun i => ⟪fpoint P Q R d (Y i), vv⟫) := by
    refine lexUni5_v7 _ _ hsep ?_ ?_ ?_ ?_
    · right
      refine ⟨?_, ?_⟩
      · simp only [hY, k7Cyc, pc5_0, pc5_1, hz]; nlinarith
      · simp only [hY, k7Cyc, pc5_0, pc5_1]; nlinarith [mul_pos hv1 hy]
    · left; simp only [hY, k7Cyc, pc5_2, pc5_1, hz]; nlinarith [mul_pos hβ6 hA]
    · right
      refine ⟨?_, ?_⟩
      · simp only [hY, k7Cyc, pc5_3, pc5_4, hz]; nlinarith
      · simp only [hY, k7Cyc, pc5_3, pc5_4]; nlinarith
    · left; simp only [hY, k7Cyc, pc5_4, pc5_0, hz]; nlinarith
  have n0 : -(0 : ZMod 5) = 0 := by decide
  have n1 : -(1 : ZMod 5) = 4 := by decide
  have n2 : -(2 : ZMod 5) = 3 := by decide
  have n3 : -(3 : ZMod 5) = 2 := by decide
  have n4 : -(4 : ZMod 5) = 1 := by decide
  rcases hΔ.lt_or_gt with hneg' | hpos
  · have hD : 0 < -det3 P Q R := by linarith
    have hcyc := k7_cyc (β1 := β1) (v3 := 0) hD hα1' hα4 hβ6 hv1 hv2
    have hra := k7_rest_a (β1 := β1) (v3 := 0) hD hα1 hα4 hβ6 hβ1 hv1 hv2
    have hrd := k7_rest_d (α1 := α1) (β1 := β1) (α4 := α4) (β6 := β6) (v3 := 0) hD hα1' hα4 hβ6 hv1 hv2
    refine ⟨5, inferInstance, fun i => fpoint P Q R d (Y (-i)), vv, ?_⟩
    refine lexCell_coord V P Q R d (by norm_num) (fun i => Y (-i)) (v1, v2, 0)
      (fun i => hmem (-i)) (hcyc_rev hcyc) ?_ (lexUni_neg hlexY)
    intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, rfl, hrest_rev hra⟩
    · exact ⟨_, rfl, hrest_rev hrd⟩
    · exact (hyx 0 (by simp only [n0, hY, k7Cyc, pc5_0])).elim
    · exact (hyx 4 (by simp only [n4, hY, k7Cyc, pc5_1])).elim
    · exact (hyx 2 (by simp only [n2, hY, k7Cyc, pc5_3])).elim
    · exact (hyx 3 (by simp only [n3, hY, k7Cyc, pc5_2])).elim
    · exact (hyx 1 (by simp only [n1, hY, k7Cyc, pc5_4])).elim
  · have hcyc := k7_cyc (β1 := β1) (v3 := 0) hpos hα1' hα4 hβ6 hv1 hv2
    have hra := k7_rest_a (β1 := β1) (v3 := 0) hpos hα1 hα4 hβ6 hβ1 hv1 hv2
    have hrd := k7_rest_d (α1 := α1) (β1 := β1) (α4 := α4) (β6 := β6) (v3 := 0) hpos hα1' hα4 hβ6 hv1 hv2
    refine ⟨5, inferInstance, fun i => fpoint P Q R d (Y i), vv, ?_⟩
    refine lexCell_coord V P Q R d (by norm_num) Y (v1, v2, 0) hmem hcyc ?_ hlexY
    intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, rfl, hra⟩
    · exact ⟨_, rfl, hrd⟩
    · exact (hyx 0 (by simp only [hY, k7Cyc, pc5_0])).elim
    · exact (hyx 1 (by simp only [hY, k7Cyc, pc5_1])).elim
    · exact (hyx 3 (by simp only [hY, k7Cyc, pc5_3])).elim
    · exact (hyx 2 (by simp only [hY, k7Cyc, pc5_2])).elim
    · exact (hyx 4 (by simp only [hY, k7Cyc, pc5_4])).elim

end C2
end Type08Sp
end Minimality
