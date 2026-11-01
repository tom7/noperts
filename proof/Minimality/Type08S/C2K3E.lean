module

public import Minimality.Type08S.C2K3D

@[expose] public section

/-!
# C2 / K3E: the cell `Q4⁻ = (d, a, b', c', b)` (`β6 < 1`, `s₂ < 0`, `C ≥ 0`)

Tilt `v = (-1 + λ, -1)`; hides `c` and `a'` (rest points).  Lex (reversed cycle `(b', a, d, b, c')`):
`C > 0`: `lexUni5_top` (`a < b'`, `d < b`, `b < c'`); `C = 0`: rotation `(b', c', b, d, a)`, `lexUni5_adj` (right disjunct).
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- The ccw cycle `(d, a, b', c', b)` in the `c - d` frame. -/
def k3q4mCyc (γ4 β1 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  pc5 (0, 0, 0) (1, 0, 0) (1, 0, γ4) (1, β1, 0) (0, 1, 0)

set_option maxHeartbeats 3200000 in
theorem k3q4m_cyc {D γ4 β1 v1 v2 v3 : ℝ} (hD : 0 < D) (hγ4 : 0 < γ4) (hβ1 : 0 < β1)
    (hv1 : v1 < 0) (hv2 : v2 < 0) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc D (k3q4mCyc γ4 β1 (i + 1) - k3q4mCyc γ4 β1 i) (k3q4mCyc γ4 β1 j - k3q4mCyc γ4 β1 i) (v1, v2, v3) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have k1 := hD
  have kb1 := mul_pos hD hβ1
  have kg4 := mul_pos hD hγ4
  have kv1 := mul_pos hD (neg_pos.2 hv1)
  have kv2 := mul_pos hD (neg_pos.2 hv2)
  have kg4v1 := mul_pos (mul_pos hD hγ4) (neg_pos.2 hv1)
  have kg4v2 := mul_pos (mul_pos hD hγ4) (neg_pos.2 hv2)
  have kb1v1 := mul_pos (mul_pos hD hβ1) (neg_pos.2 hv1)
  have kb1v2 := mul_pos (mul_pos hD hβ1) (neg_pos.2 hv2)
  intro i j h1 h2'
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2' (by decide)).elim
    | (simp only [TSc, d3, k3q4mCyc, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 3200000 in
theorem k3q4m_rest {D γ4 β1 β6 γ6 v1 v2 v3 : ℝ} (hD : 0 < D) (hγ4 : 0 < γ4) (hβ1 : 0 < β1)
    (hβ6p : 0 < β6) (hβ6 : β6 < 1) (hγ6 : 0 < γ6) (hs : 1 < β6 + γ6) (hv1 : v1 < 0) (hv2 : v2 < 0) :
    (∀ i : ZMod 5, TSc D (k3q4mCyc γ4 β1 (i + 1) - k3q4mCyc γ4 β1 i) ((0, 0, 1) - k3q4mCyc γ4 β1 i) (v1, v2, v3)) ∧
    (∀ i : ZMod 5, TSc D (k3q4mCyc γ4 β1 (i + 1) - k3q4mCyc γ4 β1 i) ((0, β6, γ6) - k3q4mCyc γ4 β1 i)
      (v1, v2, v3)) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have k1 := hD
  have kb1 := mul_pos hD hβ1
  have kb6 := mul_pos hD hβ6p
  have kb61 := mul_pos hD (sub_pos.2 hβ6)
  have kg6 := mul_pos hD hγ6
  have kg4 := mul_pos hD hγ4
  have ks := mul_pos hD (sub_pos.2 hs)
  have kv1 := mul_pos hD (neg_pos.2 hv1)
  have kv2 := mul_pos hD (neg_pos.2 hv2)
  have kg6v1 := mul_pos (mul_pos hD hγ6) (neg_pos.2 hv1)
  have kg4v1 := mul_pos (mul_pos hD hγ4) (neg_pos.2 hv1)
  have kg4v2 := mul_pos (mul_pos hD hγ4) (neg_pos.2 hv2)
  have kb1v1 := mul_pos (mul_pos hD hβ1) (neg_pos.2 hv1)
  have kb1v2 := mul_pos (mul_pos hD hβ1) (neg_pos.2 hv2)
  have kb61v1 := mul_pos (mul_pos hD (sub_pos.2 hβ6)) (neg_pos.2 hv1)
  have kb6v1 := mul_pos (mul_pos hD hβ6p) (neg_pos.2 hv1)
  have ksv1 := mul_pos (mul_pos hD (sub_pos.2 hs)) (neg_pos.2 hv1)
  refine ⟨?_, ?_⟩ <;> intro i <;>
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, k3q4mCyc, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

theorem k3q4mCyc_inj {γ4 β1 : ℝ} (hγ4 : 0 < γ4) (hβ1 : 0 < β1) :
    ∀ i j, k3q4mCyc γ4 β1 i = k3q4mCyc γ4 β1 j → i = j := by
  intro i j h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [k3q4mCyc, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; linarith)

set_option maxHeartbeats 3200000 in
/-- **The cell `Q4⁻`** (frame form): `β6 < 1`, `C = ⟪q, r⟫ ≥ 0`, `s₂ = (1 - β1) C - B < 0`. -/
theorem k3q4m_hasLexCellAt (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0)
    {β1 γ4 β6 γ6 : ℝ} (hβ1 : 0 < β1) (hγ4 : 0 < γ4) (hβ6p : 0 < β6) (hβ6 : β6 < 1) (hγ6 : 0 < γ6)
    (hs : 1 < β6 + γ6)
    (hC : 0 ≤ ⟪q, r⟫) (hs2 : (1 - β1) * ⟪q, r⟫ - ⟪p, r⟫ < 0)
    (hmem : ∀ i, fpoint p q r d (k3q4mCyc γ4 β1 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint p q r d (0, 0, 1) ∨ y = fpoint p q r d (0, 0, 0) ∨
      y = fpoint p q r d (1, 0, 0) ∨ y = fpoint p q r d (1, β1, 0) ∨ y = fpoint p q r d (0, β6, γ6) ∨
      y = fpoint p q r d (0, 1, 0) ∨ y = fpoint p q r d (1, 0, γ4)) :
    HasLexCellAt V r := by
  set Y := k3q4mCyc γ4 β1 with hY
  have hr0 : r ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  have hA : 0 < ⟪r, r⟫ := real_inner_self_pos.2 hr0
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint p q r d t, r⟫ = ⟪d, r⟫ + t.1 * ⟪p, r⟫ + t.2.1 * ⟪q, r⟫ + t.2.2 * ⟪r, r⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  refine k3_cell_gen V p q r d hΔ (by norm_num) Y (k3q4mCyc_inj hγ4 hβ1) (u1 := -1) (u2 := -1)
    (t1 := 1) (t2 := 0) (by norm_num) hmem ?_ ?_ ?_
  · intro lam hl0 hl1 D hD
    exact k3q4m_cyc hD hγ4 hβ1 (by linarith) (by norm_num)
  · intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, rfl, fun lam hl0 hl1 D hD =>
        (k3q4m_rest hD hγ4 hβ1 hβ6p hβ6 hγ6 hs (by linarith) (by norm_num)).1⟩
    · exact (hyx 0 (by simp only [hY, k3q4mCyc, pc5_0])).elim
    · exact (hyx 1 (by simp only [hY, k3q4mCyc, pc5_1])).elim
    · exact (hyx 3 (by simp only [hY, k3q4mCyc, pc5_3])).elim
    · exact ⟨_, rfl, fun lam hl0 hl1 D hD =>
        (k3q4m_rest hD hγ4 hβ1 hβ6p hβ6 hγ6 hs (by linarith) (by norm_num)).2⟩
    · exact (hyx 4 (by simp only [hY, k3q4mCyc, pc5_4])).elim
    · exact (hyx 2 (by simp only [hY, k3q4mCyc, pc5_2])).elim
  · intro w hw
    rcases hC.lt_or_eq with hCp | hC0
    · have m0 : (2 : ZMod 5) - 0 = 2 := by decide
      have m1 : (2 : ZMod 5) - 1 = 1 := by decide
      have m2 : (2 : ZMod 5) - 2 = 0 := by decide
      have m3 : (2 : ZMod 5) - 3 = 4 := by decide
      have m4 : (2 : ZMod 5) - 4 = 3 := by decide
      apply lexUni_rev_shift (2 : ZMod 5)
      refine lexUni5_top _ _ (fun i j h1 h2 => sub_right_injective (hw _ _ h1 h2)) ?_ ?_ ?_
      · left; simp only [m1, m0, hY, k3q4mCyc, pc5_1, pc5_2, hz]; nlinarith [mul_pos hγ4 hA]
      · left; simp only [m2, m3, hY, k3q4mCyc, pc5_0, pc5_4, hz]; nlinarith
      · left; simp only [m3, m4, hY, k3q4mCyc, pc5_4, pc5_3, hz]; nlinarith
    · have t0 : (0 : ZMod 5) + 2 = 2 := by decide
      have t1 : (1 : ZMod 5) + 2 = 3 := by decide
      have t2 : (2 : ZMod 5) + 2 = 4 := by decide
      have t3 : (3 : ZMod 5) + 2 = 0 := by decide
      have t4 : (4 : ZMod 5) + 2 = 1 := by decide
      have hq0 : ⟪q, r⟫ = 0 := hC0.symm
      apply lexUni_of_shift (2 : ZMod 5)
      refine lexUni5_adj _ _ (fun i j h1 h2 => add_right_cancel (hw _ _ h1 h2)) ?_ ?_ ?_
      · left; simp only [t1, t0, hY, k3q4mCyc, pc5_3, pc5_2, hz]; nlinarith [mul_pos hγ4 hA]
      · left; simp only [t2, t1, hY, k3q4mCyc, pc5_4, pc5_3, hz]; nlinarith
      · right; left; simp only [t3, t4, hY, k3q4mCyc, pc5_0, pc5_1, hz]; nlinarith

end C2
end Type08Sp
end Minimality

