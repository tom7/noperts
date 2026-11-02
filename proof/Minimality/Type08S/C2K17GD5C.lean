module

public import Minimality.Type08S.C2K17GD5B

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

set_option maxHeartbeats 3200000 in
/-- Cell E1 `(a, b', a', b, d)` at `R = a - c'` on the tie `z(a') = z(b)`, `z(b) < z(b')`.  Cone and tilt segment of `k5f_E1_frame`. -/
theorem k17gdE1_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0)
    {m k t α4 γ4 : ℝ} (hm : 0 < m) (hk : 0 < k) (hk1 : k < 1) (ht : 0 < t) (ht1 : t < 1)
    (hα4 : 1 < α4) (hγ4 : 1 < γ4) (hrel : (γ4 - 1) * (m + k) = α4 * (1 - k))
    (hT : -t * ⟪P, R⟫ * m + ⟪Q, R⟫ - t * k * ⟪R, R⟫ = -m * ⟪P, R⟫ - k * ⟪R, R⟫)
    (hL : -m * ⟪P, R⟫ - k * ⟪R, R⟫ < α4 * ⟪P, R⟫ + γ4 * ⟪Q, R⟫)
    (hmem : ∀ i, fpoint P Q R d (k5fE1Cyc m k t α4 γ4 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (α4, γ4, 0) ∨
      y = fpoint P Q R d (-t * m, 1, -t * k) ∨ y = fpoint P Q R d (-m, 0, -k) ∨
      y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, -1) ∨ y = fpoint P Q R d (0, 1, 0)) :
    HasLexCellAt V R := by
  have hR0 : R ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  have hs : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hR0
  have hmγ : m * (γ4 - 1) < α4 := by nlinarith [mul_pos hk (sub_pos.2 hγ4)]
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hinjX : ∀ i j, k5fE1Cyc m k t α4 γ4 i = k5fE1Cyc m k t α4 γ4 j → i = j := by
    intro i j h
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      simp only [k5fE1Cyc, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4, Prod.mk.injEq] at h <;>
      first | rfl | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h) |
        (exfalso; obtain ⟨h1, h2, h3⟩ := h; nlinarith)
  have hb : -m * ⟪P, R⟫ - k * ⟪R, R⟫ < 0 := by
    by_contra hh; push Not at hh
    exact k17gd_E1_real (x := ⟪P, R⟫) (y := ⟪Q, R⟫) (s := ⟪R, R⟫) hm hk hk1 ht ht1 hα4 hγ4 hrel hs hh (by nlinarith) (by nlinarith)
  have hy : ⟪Q, R⟫ < 0 := by
    have : ⟪Q, R⟫ = -(1 - t) * (m * ⟪P, R⟫ + k * ⟪R, R⟫) := by nlinarith
    rw [this]; nlinarith [mul_pos (sub_pos.2 ht1) (show 0 < m * ⟪P, R⟫ + k * ⟪R, R⟫ by linarith)]
  refine cyc_cell V P Q R d hΔ (k := 5) (by norm_num) (k5fE1Cyc m k t α4 γ4) hinjX hmem
    [(1, 0, -1), (0, 1, 0)] ?_ (u1 := -1) (u2 := 1) (t1 := 1) (t2 := 0) (lo := 0) (hi := 1)
    (by norm_num) (by norm_num) (fun v1 v2 => v1 < 0 ∧ 0 < v2) ?_ ?_ ?_
  · intro y hy
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by simp [k5fE1Cyc, pc5_0]⟩
    · exact Or.inl ⟨1, by simp [k5fE1Cyc, pc5_1]⟩
    · exact Or.inl ⟨2, by simp [k5fE1Cyc, pc5_2]⟩
    · exact Or.inl ⟨3, by simp [k5fE1Cyc, pc5_3]⟩
    · exact Or.inl ⟨4, by simp [k5fE1Cyc, pc5_4]⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
  · intro lam hl0 hl1
    constructor <;> linarith
  · intro v1 v2 hv
    exact ⟨k5f_E1_cyc hm hk ht ht1 hα4 hγ4 hmγ hv.1 hv.2, k5f_E1_rest hm hk ht ht1 hα4 hγ4 hmγ hv.1 hv.2⟩
  · intro v1 v2 hv hsep
    set z : ZMod 5 → ℝ := fun i => ⟪fpoint P Q R d (k5fE1Cyc m k t α4 γ4 i), R⟫ with hzdef
    set w : ZMod 5 → ℝ := fun i => ⟪fpoint P Q R d (k5fE1Cyc m k t α4 γ4 i), fcomb P Q R v1 v2 0⟫ with hwdef
    have z0 : z 0 = ⟪d, R⟫ + ⟪P, R⟫ := by simp only [hzdef, k5fE1Cyc, pc5_0, hz]; ring
    have z1 : z 1 = ⟪d, R⟫ + α4 * ⟪P, R⟫ + γ4 * ⟪Q, R⟫ := by simp only [hzdef, k5fE1Cyc, pc5_1, hz]; ring
    have z2 : z 2 = ⟪d, R⟫ + (-t * m) * ⟪P, R⟫ + ⟪Q, R⟫ + (-t * k) * ⟪R, R⟫ := by
      simp only [hzdef, k5fE1Cyc, pc5_2, hz]; ring
    have z3 : z 3 = ⟪d, R⟫ + (-m) * ⟪P, R⟫ + (-k) * ⟪R, R⟫ := by simp only [hzdef, k5fE1Cyc, pc5_3, hz]; ring
    have z4 : z 4 = ⟪d, R⟫ := by simp only [hzdef, k5fE1Cyc, pc5_4, hz]; ring
    refine k17gd_lexUni5_E1 z w hsep (k17gd_ll (by rw [z3, z4]; linarith)) (k17gd_ll (by rw [z2, z1]; nlinarith)) ?_
    rcases lt_or_ge 0 ⟪P, R⟫ with hx | hx
    · left; exact k17gd_ll (by rw [z4, z0]; linarith)
    · right; exact k17gd_ll (by rw [z1, z0]; nlinarith [mul_nonneg (sub_pos.2 hα4).le (neg_nonneg.2 hx)])

set_option maxHeartbeats 3200000 in
/-- Cell E2 `(c', b', a', b)` at `R = a - c'` on the tie `z(a') = z(b)`, `z(b') < z(b)`. -/
theorem k17gdE2_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0)
    {m k t α4 γ4 : ℝ} (hm : 0 < m) (hk : 0 < k) (hk1 : k < 1) (ht : 0 < t) (ht1 : t < 1)
    (hα4 : 1 < α4) (hγ4 : 1 < γ4) (hrel : (γ4 - 1) * (m + k) = α4 * (1 - k))
    (hT : -t * ⟪P, R⟫ * m + ⟪Q, R⟫ - t * k * ⟪R, R⟫ = -m * ⟪P, R⟫ - k * ⟪R, R⟫)
    (hL : α4 * ⟪P, R⟫ + γ4 * ⟪Q, R⟫ < -m * ⟪P, R⟫ - k * ⟪R, R⟫)
    (hmem : ∀ i, fpoint P Q R d (k5fE2Cyc m k t α4 γ4 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (1, 0, -1) ∨ y = fpoint P Q R d (α4, γ4, 0) ∨
      y = fpoint P Q R d (-t * m, 1, -t * k) ∨ y = fpoint P Q R d (-m, 0, -k) ∨
      y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (0, 1, 0)) :
    HasLexCellAt V R := by
  have hR0 : R ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  have hs : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hR0
  have hmγ : m * (γ4 - 1) < α4 := by nlinarith [mul_pos hk (sub_pos.2 hγ4)]
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hinjX : ∀ i j, k5fE2Cyc m k t α4 γ4 i = k5fE2Cyc m k t α4 γ4 j → i = j := by
    intro i j h
    rcases z4_cases i with rfl | rfl | rfl | rfl <;>
      rcases z4_cases j with rfl | rfl | rfl | rfl <;>
      simp only [k5fE2Cyc_0, k5fE2Cyc_1, k5fE2Cyc_2, k5fE2Cyc_3, Prod.mk.injEq] at h <;>
      first | rfl | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h) |
        (exfalso; obtain ⟨h1, h2, h3⟩ := h; nlinarith)
  have hc : ⟪P, R⟫ - ⟪R, R⟫ < -m * ⟪P, R⟫ - k * ⟪R, R⟫ := by
    by_contra hh; push Not at hh
    exact k17gd_E2_real (x := ⟪P, R⟫) (y := ⟪Q, R⟫) (s := ⟪R, R⟫) hm hk hk1 ht ht1 hα4 hγ4 hrel hs (by nlinarith) hh hL
  refine cyc_cell V P Q R d hΔ (k := 4) (by norm_num) (k5fE2Cyc m k t α4 γ4) hinjX hmem
    [(1, 0, 0), (0, 0, 0), (0, 1, 0)] ?_ (u1 := 1) (u2 := -1) (t1 := -1) (t2 := 0) (lo := 0) (hi := 1)
    (by norm_num) (by norm_num) (fun v1 v2 => 0 < v1 ∧ v2 < 0) ?_ ?_ ?_
  · intro y hy
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by simp [k5fE2Cyc_0]⟩
    · exact Or.inl ⟨1, by simp [k5fE2Cyc_1]⟩
    · exact Or.inl ⟨2, by simp [k5fE2Cyc_2]⟩
    · exact Or.inl ⟨3, by simp [k5fE2Cyc_3]⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
  · intro lam hl0 hl1
    constructor <;> linarith
  · intro v1 v2 hv
    exact ⟨k5f_E2_cyc hm hk ht ht1 hα4 hγ4 hmγ hv.1 hv.2, k5f_E2_rest hm hk ht ht1 hα4 hγ4 hmγ hv.1 hv.2⟩
  · intro v1 v2 hv hsep
    set z : ZMod 4 → ℝ := fun i => ⟪fpoint P Q R d (k5fE2Cyc m k t α4 γ4 i), R⟫ with hzdef
    set w : ZMod 4 → ℝ := fun i => ⟪fpoint P Q R d (k5fE2Cyc m k t α4 γ4 i), fcomb P Q R v1 v2 0⟫ with hwdef
    have z0 : z 0 = ⟪d, R⟫ + ⟪P, R⟫ - ⟪R, R⟫ := by simp only [hzdef, k5fE2Cyc_0, hz]; ring
    have z1 : z 1 = ⟪d, R⟫ + α4 * ⟪P, R⟫ + γ4 * ⟪Q, R⟫ := by simp only [hzdef, k5fE2Cyc_1, hz]; ring
    have z2 : z 2 = ⟪d, R⟫ + (-t * m) * ⟪P, R⟫ + ⟪Q, R⟫ + (-t * k) * ⟪R, R⟫ := by
      simp only [hzdef, k5fE2Cyc_2, hz]; ring
    have z3 : z 3 = ⟪d, R⟫ + (-m) * ⟪P, R⟫ + (-k) * ⟪R, R⟫ := by simp only [hzdef, k5fE2Cyc_3, hz]; ring
    exact k17gd_lexUni4_E2 z w hsep (k17gd_ll (by rw [z1, z2]; nlinarith)) (k17gd_ll (by rw [z0, z3]; nlinarith))

end C2
end Type08Sp
end Minimality
