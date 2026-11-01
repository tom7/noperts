module

public import Minimality.Type08S.C2K8C

@[expose] public section

/-! # K8D: cell `Q4⁺` for `1 ≤ β6`, `C > 0`, with the tie `s₁ = 0` decided by the tilt. -/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- The ccw cycle `(d, a, b', c', a', b)` in the `c - d` frame. -/
def k8q4pCyc (γ4 β1 β6 γ6 : ℝ) : ZMod 6 → ℝ × ℝ × ℝ :=
  pc6 (0, 0, 0) (1, 0, 0) (1, 0, γ4) (1, β1, 0) (0, β6, γ6) (0, 1, 0)

set_option maxHeartbeats 3200000 in
theorem k8q4p_cyc {D γ4 β1 β6 γ6 v1 v2 v3 : ℝ} (hD : 0 < D) (hγ4 : 0 < γ4) (hβ1 : 0 < β1) (hβ6 : 1 ≤ β6)
    (hγ6 : 0 < γ6) (hs : 1 < β6 + γ6) (hv1 : v1 < 0) (hv2 : v2 < 0) (hcone : (1 - β1) * v1 + v2 < 0) :
    ∀ i j : ZMod 6, j ≠ i → j ≠ i + 1 →
      TSc D (k8q4pCyc γ4 β1 β6 γ6 (i + 1) - k8q4pCyc γ4 β1 β6 γ6 i)
        (k8q4pCyc γ4 β1 β6 γ6 j - k8q4pCyc γ4 β1 β6 γ6 i) (v1, v2, v3) := by
  rcases eq_or_lt_of_le hβ6 with h | h
  · subst h
    obtain ⟨s0, s1, s2, s3, s4, s5⟩ := z6_add_one
    have k1 := hD
    have kb1 := mul_pos hD hβ1
    have kgc := mul_pos (mul_pos hD hγ6) (neg_pos.2 hcone)
    have kc := mul_pos hD (neg_pos.2 hcone)
    have kb6 : (0:ℝ) < 1 := one_pos
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
    have ksv1 := mul_pos (mul_pos hD (sub_pos.2 hs)) (neg_pos.2 hv1)
    intro i j h1 h2'
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, k8q4pCyc, s0, s1, s2, s3, s4, s5, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; nlinarith)
         | (right; refine ⟨by ring, by nlinarith⟩))
  · 
    obtain ⟨s0, s1, s2, s3, s4, s5⟩ := z6_add_one
    have k1 := hD
    have kb1 := mul_pos hD hβ1
    have kgc := mul_pos (mul_pos hD hγ6) (neg_pos.2 hcone)
    have kc := mul_pos hD (neg_pos.2 hcone)
    have kb6 := mul_pos hD (lt_trans one_pos h)
    have kb61 := mul_pos hD (sub_pos.2 h)
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
    have kb61v1 := mul_pos (mul_pos hD (sub_pos.2 h)) (neg_pos.2 hv1)
    have ksv1 := mul_pos (mul_pos hD (sub_pos.2 hs)) (neg_pos.2 hv1)
    intro i j h1 h2'
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, k8q4pCyc, s0, s1, s2, s3, s4, s5, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; nlinarith)
         | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 3200000 in
theorem k8q4p_rest {D γ4 β1 β6 γ6 v1 v2 v3 : ℝ} (hD : 0 < D) (hγ4 : 0 < γ4) (hβ1 : 0 < β1) (hβ6 : 1 ≤ β6)
    (hγ6 : 0 < γ6) (hs : 1 < β6 + γ6) (hv1 : v1 < 0) (hv2 : v2 < 0) (hcone : (1 - β1) * v1 + v2 < 0) :
    ∀ i : ZMod 6, TSc D (k8q4pCyc γ4 β1 β6 γ6 (i + 1) - k8q4pCyc γ4 β1 β6 γ6 i)
      ((0, 0, 1) - k8q4pCyc γ4 β1 β6 γ6 i) (v1, v2, v3) := by
  rcases eq_or_lt_of_le hβ6 with h | h
  · subst h
    obtain ⟨s0, s1, s2, s3, s4, s5⟩ := z6_add_one
    have k1 := hD
    have kb1 := mul_pos hD hβ1
    have kgc := mul_pos (mul_pos hD hγ6) (neg_pos.2 hcone)
    have kc := mul_pos hD (neg_pos.2 hcone)
    have kb6 : (0:ℝ) < 1 := one_pos
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
    have ksv1 := mul_pos (mul_pos hD (sub_pos.2 hs)) (neg_pos.2 hv1)
    intro i
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k8q4pCyc, s0, s1, s2, s3, s4, s5, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))
  · 
    obtain ⟨s0, s1, s2, s3, s4, s5⟩ := z6_add_one
    have k1 := hD
    have kb1 := mul_pos hD hβ1
    have kgc := mul_pos (mul_pos hD hγ6) (neg_pos.2 hcone)
    have kc := mul_pos hD (neg_pos.2 hcone)
    have kb6 := mul_pos hD (lt_trans one_pos h)
    have kb61 := mul_pos hD (sub_pos.2 h)
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
    have kb61v1 := mul_pos (mul_pos hD (sub_pos.2 h)) (neg_pos.2 hv1)
    have ksv1 := mul_pos (mul_pos hD (sub_pos.2 hs)) (neg_pos.2 hv1)
    intro i
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k8q4pCyc, s0, s1, s2, s3, s4, s5, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

theorem k8q4pCyc_inj {γ4 β1 β6 γ6 : ℝ} (hγ4 : 0 < γ4) (hβ1 : 0 < β1) (hβ6 : 1 ≤ β6) (hγ6 : 0 < γ6) :
    ∀ i j, k8q4pCyc γ4 β1 β6 γ6 i = k8q4pCyc γ4 β1 β6 γ6 j → i = j := by
  intro i j h
  rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [k8q4pCyc, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; linarith)


set_option maxHeartbeats 3200000 in
/-- **`Q4⁺`, `1 ≤ β6`, `C > 0`**, caller tilt; `s₁ ≤ 0`, a tie `s₁ = 0` is decided by `w(a') < w(c')`. -/
theorem k8q4p_hasLexCellAt (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0)
    {β1 γ4 β6 γ6 u1 u2 t1 t2 : ℝ} (hβ1 : 0 < β1) (hγ4 : 0 < γ4) (hβ6 : 1 ≤ β6) (hγ6 : 0 < γ6)
    (hs : 1 < β6 + γ6) (hut : u1 * t2 - u2 * t1 ≠ 0)
    (hcone : ∀ lam : ℝ, 0 < lam → lam < 1 → u1 + lam * t1 < 0 ∧ u2 + lam * t2 < 0 ∧
      (1 - β1) * (u1 + lam * t1) + (u2 + lam * t2) < 0)
    (hC : 0 < ⟪q, r⟫) (hs1 : (β6 - β1) * ⟪q, r⟫ + γ6 * ⟪r, r⟫ - ⟪p, r⟫ ≤ 0)
    (hw : (β6 - β1) * ⟪q, r⟫ + γ6 * ⟪r, r⟫ - ⟪p, r⟫ = 0 → ∀ lam : ℝ, 0 < lam → lam < 1 →
      (u1 + lam * t1) * ⟪fpoint p q r d (0, β6, γ6) - fpoint p q r d (1, β1, 0), p⟫ +
        (u2 + lam * t2) * ⟪fpoint p q r d (0, β6, γ6) - fpoint p q r d (1, β1, 0), q⟫ < 0)
    (hmem : ∀ i, fpoint p q r d (k8q4pCyc γ4 β1 β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint p q r d (0, 0, 1) ∨ y = fpoint p q r d (0, 0, 0) ∨
      y = fpoint p q r d (1, 0, 0) ∨ y = fpoint p q r d (1, β1, 0) ∨ y = fpoint p q r d (0, β6, γ6) ∨
      y = fpoint p q r d (0, 1, 0) ∨ y = fpoint p q r d (1, 0, γ4)) :
    HasLexCellAt V r := by
  set Y := k8q4pCyc γ4 β1 β6 γ6 with hY
  have hr0 : r ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  have hA : 0 < ⟪r, r⟫ := real_inner_self_pos.2 hr0
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint p q r d t, r⟫ = ⟪d, r⟫ + t.1 * ⟪p, r⟫ + t.2.1 * ⟪q, r⟫ + t.2.2 * ⟪r, r⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  refine k8_cell_gen V p q r d hΔ (by norm_num) Y (k8q4pCyc_inj hγ4 hβ1 hβ6 hγ6) hut hmem ?_ ?_ ?_
  · intro lam hl0 hl1 D hD
    obtain ⟨h1, h2, h3⟩ := hcone lam hl0 hl1
    exact k8q4p_cyc hD hγ4 hβ1 hβ6 hγ6 hs h1 h2 h3
  · intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, rfl, fun lam hl0 hl1 D hD => by
        obtain ⟨h1, h2, h3⟩ := hcone lam hl0 hl1
        exact k8q4p_rest hD hγ4 hβ1 hβ6 hγ6 hs h1 h2 h3⟩
    · exact (hyx 0 (by simp only [hY, k8q4pCyc, pc6_0])).elim
    · exact (hyx 1 (by simp only [hY, k8q4pCyc, pc6_1])).elim
    · exact (hyx 3 (by simp only [hY, k8q4pCyc, pc6_3])).elim
    · exact (hyx 4 (by simp only [hY, k8q4pCyc, pc6_4])).elim
    · exact (hyx 5 (by simp only [hY, k8q4pCyc, pc6_5])).elim
    · exact (hyx 2 (by simp only [hY, k8q4pCyc, pc6_2])).elim
  · intro lam hl0 hl1 w hwd hw'
    have m0 : (2 : ZMod 6) - 0 = 2 := by decide
    have m1 : (2 : ZMod 6) - 1 = 1 := by decide
    have m2 : (2 : ZMod 6) - 2 = 0 := by decide
    have m3 : (2 : ZMod 6) - 3 = 5 := by decide
    have m4 : (2 : ZMod 6) - 4 = 4 := by decide
    have m5 : (2 : ZMod 6) - 5 = 3 := by decide
    apply lexUni_rev_shift (2 : ZMod 6)
    refine lexUni6_top2 _ _ (fun i j h1 h2 => sub_right_injective (hw' _ _ h1 h2)) ?_ ?_ ?_ ?_
    · left; simp only [m1, m0, hY, k8q4pCyc, pc6_1, pc6_2, hz]; nlinarith [mul_pos hγ4 hA]
    · left; simp only [m2, m3, hY, k8q4pCyc, pc6_0, pc6_5, hz]; nlinarith
    · left; simp only [m3, m4, hY, k8q4pCyc, pc6_5, pc6_4, hz]
      nlinarith [mul_nonneg (sub_nonneg.2 hβ6) hC.le, mul_pos hγ6 hA]
    · rcases hs1.lt_or_eq with h | h
      · left; left; simp only [m4, m5, hY, k8q4pCyc, pc6_4, pc6_3, hz]; nlinarith
      · left; right; refine ⟨?_, ?_⟩
        · simp only [m4, m5, hY, k8q4pCyc, pc6_4, pc6_3, hz]; nlinarith
        · rw [hwd, hwd]
          have := k8_wdiff p q r d (0, β6, γ6) (1, β1, 0) (u1 + lam * t1) (u2 + lam * t2)
          simp only [m4, m5, hY, k8q4pCyc, pc6_4, pc6_3]
          linarith [hw h lam hl0 hl1]

end C2
end Type08Sp
end Minimality
