module

public import Minimality.Type08S.C2K17GD2C

@[expose] public section


set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem k17gdA_inj {α1 β1 : ℝ} (hα1 : 1 < α1) (hβ1 : 0 < β1) : ∀ i j, k17gdA α1 β1 i = k17gdA α1 β1 j → i = j := by
  intro i j h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [k17gdA, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; nlinarith)

theorem k17gdB_inj {α1 β1 γ4 : ℝ} (hα1 : 1 < α1) (hβ1 : 0 < β1) (hγ4 : 0 < γ4) :
    ∀ i j, k17gdB α1 β1 γ4 i = k17gdB α1 β1 γ4 j → i = j := by
  intro i j h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [k17gdB, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; nlinarith)

/-- Key inequality of cell B (uses the Gale inequality `E ≥ 0`). -/
theorem k17gdB_key {α1 β1 γ4 pq qr qq : ℝ} (hα1 : 1 < α1) (hβ1 : 0 < β1) (hγ4 : 0 < γ4)
    (hE : 0 ≤ 1 - β1 - α1 + α1 * γ4) (hqq : 0 < qq) (hqr : qr ≤ 0) :
    pq + γ4 * qr < α1 * pq + β1 * qq ∨ pq + γ4 * qr < qr := by
  by_contra hh
  push Not at hh
  obtain ⟨h1, h2⟩ := hh
  have a1 := sub_pos.2 hα1
  have y0 : 0 ≤ -qr := by linarith
  have e1 : (α1 - 1) * (-pq) ≥ γ4 * (-qr) + β1 * qq := by nlinarith
  have e2 : (-pq) ≤ (1 - γ4) * (-qr) := by nlinarith
  have e3 : (α1 - 1) * (-pq) ≤ (α1 - 1) * ((1 - γ4) * (-qr)) := mul_le_mul_of_nonneg_left e2 a1.le
  have e4 : (-qr) * (α1 - 1 - α1 * γ4) ≤ (-qr) * (-β1) := mul_le_mul_of_nonneg_left (by linarith) y0
  nlinarith [mul_pos hβ1 hqq]

set_option maxHeartbeats 3200000 in
/-- **Tc `α4 = 1`, cell A** `(a, c', a', c, d)` at `r`, frame `(p, q, r)`. -/
theorem k17gdA_frame (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0) {α1 β1 γ4 : ℝ}
    (hα1 : 1 < α1) (hβ1 : 0 < β1) (hγ4 : 0 < γ4)
    (hcase : 0 < ⟪q, r⟫ ∨ (⟪q, r⟫ = 0 ∧ α1 * ⟪p, r⟫ < ⟪r, r⟫ ∧ ⟪p, r⟫ ≠ 0))
    (hmem : ∀ i, fpoint p q r d (k17gdA α1 β1 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint p q r d (1, 0, 0) ∨ y = fpoint p q r d (α1, β1, 0) ∨
      y = fpoint p q r d (0, 1, 1) ∨ y = fpoint p q r d (0, 0, 1) ∨ y = fpoint p q r d (0, 0, 0) ∨
      y = fpoint p q r d (0, 1, 0) ∨ y = fpoint p q r d (1, 0, γ4)) :
    HasLexCellAt V r := by
  have hr0 : r ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  have hA : 0 < ⟪r, r⟫ := real_inner_self_pos.2 hr0
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint p q r d t, r⟫ = ⟪d, r⟫ + t.1 * ⟪p, r⟫ + t.2.1 * ⟪q, r⟫ + t.2.2 * ⟪r, r⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  obtain ⟨t1, ht1def⟩ : ∃ t1 : ℝ, t1 = α1 / (α1 + (β1 - 1) ^ 2 + 1) := ⟨_, rfl⟩
  have hden : 0 < α1 + (β1 - 1) ^ 2 + 1 := by positivity
  have ht1 : 0 < t1 := by rw [ht1def]; exact div_pos (by linarith) hden
  have ht1a : t1 < α1 := by
    rw [ht1def, div_lt_iff₀ hden]; nlinarith [sq_nonneg (β1 - 1)]
  have ht11 : t1 ≤ 1 ∨ True := Or.inr trivial
  refine cyc_cell V p q r d hΔ (k := 5) (by norm_num) (k17gdA α1 β1) (k17gdA_inj hα1 hβ1) hmem
    [(0, 1, 0), (1, 0, γ4)] ?_ (u1 := 0) (u2 := -1) (t1 := t1) (t2 := 0) (lo := 0) (hi := 1)
    (by rw [show (0:ℝ) * 0 - (-1) * t1 = t1 by ring]; exact ht1.ne') (by norm_num)
    (fun v1 v2 => 0 < v1 ∧ v2 < 0 ∧ 0 < α1 * (-v2) + (β1 - 1) * v1) ?_ ?_ ?_
  · intro y hy
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by simp [k17gdA, pc5_0]⟩
    · exact Or.inl ⟨1, by simp [k17gdA, pc5_1]⟩
    · exact Or.inl ⟨2, by simp [k17gdA, pc5_2]⟩
    · exact Or.inl ⟨3, by simp [k17gdA, pc5_3]⟩
    · exact Or.inl ⟨4, by simp [k17gdA, pc5_4]⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
  · intro lam hl0 hl1
    refine ⟨by nlinarith, by norm_num, ?_⟩
    simp only [mul_zero, add_zero, neg_mul, zero_add]
    rcases le_or_gt 1 β1 with hb | hb
    · nlinarith [mul_pos hl0 ht1, mul_nonneg (sub_nonneg.2 hb) (mul_pos hl0 ht1).le]
    · have : (1 - β1) * (lam * t1) < t1 := by nlinarith [mul_pos hl0 ht1]
      nlinarith
  · intro v1 v2 hv
    refine ⟨k17gdA_tsc hα1 hβ1 hv.1 hv.2.1 hv.2.2, ?_⟩
    intro t ht i
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact (k17gdA_rest hα1 hβ1 hγ4 hv.1 hv.2.1 hv.2.2).1 i
    · exact (k17gdA_rest hα1 hβ1 hγ4 hv.1 hv.2.1 hv.2.2).2 i
  · intro v1 v2 hv hsep
    have a1 := sub_pos.2 hα1
    set z : ZMod 5 → ℝ := fun i => ⟪fpoint p q r d (k17gdA α1 β1 i), r⟫ with hzdef
    set w : ZMod 5 → ℝ := fun i => ⟪fpoint p q r d (k17gdA α1 β1 i), fcomb p q r v1 v2 0⟫ with hwdef
    have z0 : z 0 = ⟪d, r⟫ + ⟪p, r⟫ := by simp only [hzdef, k17gdA, pc5_0, hz]; ring
    have z1 : z 1 = ⟪d, r⟫ + α1 * ⟪p, r⟫ + β1 * ⟪q, r⟫ := by simp only [hzdef, k17gdA, pc5_1, hz]; ring
    have z2 : z 2 = ⟪d, r⟫ + ⟪q, r⟫ + ⟪r, r⟫ := by simp only [hzdef, k17gdA, pc5_2, hz]; ring
    have z3 : z 3 = ⟪d, r⟫ + ⟪r, r⟫ := by simp only [hzdef, k17gdA, pc5_3, hz]; ring
    have z4 : z 4 = ⟪d, r⟫ := by simp only [hzdef, k17gdA, pc5_4, hz]; ring
    have h43 : LexLt (z 4, w 4) (z 3, w 3) := k17gd_ll (by rw [z4, z3]; linarith)
    rcases hcase with hq | ⟨hq, hlit, hp0⟩
    · refine k17gd_lexUni5_A z w hsep (k17gd_ll (by rw [z3, z2]; linarith)) h43 ?_
      rcases lt_or_ge ⟪p, r⟫ 0 with hp | hp
      · left; exact k17gd_ll (by rw [z0, z4]; linarith)
      · right; exact k17gd_ll (by rw [z0, z1]; nlinarith [mul_nonneg a1.le hp, mul_pos hβ1 hq])
    · have h0 : LexLt (z 0, w 0) (z 4, w 4) ∨ LexLt (z 0, w 0) (z 1, w 1) := by
        rcases lt_or_gt_of_ne hp0 with hp | hp
        · left; exact k17gd_ll (by rw [z0, z4]; linarith)
        · right; exact k17gd_ll (by rw [z0, z1, hq]; nlinarith)
      rcases lexLt_total (k17gd_ne5 hsep (show (2 : ZMod 5) ≠ 3 by decide)) with h23 | h32
      · exact k17gd_lexUni5_A2 z w hsep h23 h43 (k17gd_ll (by rw [z1, z2, hq]; linarith)) h0
      · exact k17gd_lexUni5_A z w hsep h32 h43 h0

end C2
end Type08Sp
end Minimality
