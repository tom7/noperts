module

public import Minimality.Type08S.C2K8A

@[expose] public section

/-! # K8B: cell `Q1⁺` for `1 ≤ β6` with a tilt segment given by the caller, tie `s₁ = 0` decided by the tilt. -/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- The ccw cycle `(c, d, a, c', a')` in the `c - d` frame. -/
def k8q1pCyc (β1 β6 γ6 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ := pc5 (0, 0, 1) (0, 0, 0) (1, 0, 0) (1, β1, 0) (0, β6, γ6)

set_option maxHeartbeats 1600000 in
theorem k8q1p_cyc {D β1 β6 γ6 v1 v2 v3 : ℝ} (hD : 0 < D) (hβ1 : 0 < β1) (hβ6 : 1 ≤ β6) (hγ6 : 0 < γ6)
    (hv1 : 0 < v1) (hv2 : v2 < 0) (hcone : (1 - β1) * v1 + v2 < 0) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc D (k8q1pCyc β1 β6 γ6 (i + 1) - k8q1pCyc β1 β6 γ6 i) (k8q1pCyc β1 β6 γ6 j - k8q1pCyc β1 β6 γ6 i)
        (v1, v2, v3) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have k1 := hD
  have kb1 := mul_pos hD hβ1
  have kb6 := mul_pos hD (by linarith : (0:ℝ) < β6)
  have kb61 := mul_nonneg hD.le (sub_nonneg.2 hβ6)
  have kg6 := mul_pos hD hγ6
  have kv1 := mul_pos hD hv1
  have kv2 := mul_pos hD (neg_pos.2 hv2)
  have kgv1 := mul_pos (mul_pos hD hγ6) hv1
  have kgv2 := mul_pos (mul_pos hD hγ6) (neg_pos.2 hv2)
  have kbv1 := mul_pos (mul_pos hD hβ1) hv1
  have kgc := mul_pos (mul_pos hD hγ6) (neg_pos.2 hcone)
  have kc := mul_pos hD (neg_pos.2 hcone)
  have kb6v1 := mul_pos (mul_pos hD (by linarith : (0:ℝ) < β6)) hv1
  intro i j h1 h2'
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2' (by decide)).elim
    | (simp only [TSc, d3, k8q1pCyc, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 1600000 in
theorem k8q1p_rest {D β1 γ4 β6 γ6 v1 v2 v3 : ℝ} (hD : 0 < D) (hβ1 : 0 < β1) (hγ4 : 0 < γ4) (hβ6 : 1 ≤ β6)
    (hγ6 : 0 < γ6) (hs : 1 < β6 + γ6) (hv1 : 0 < v1) (hv2 : v2 < 0) (hcone : (1 - β1) * v1 + v2 < 0) :
    (∀ i : ZMod 5, TSc D (k8q1pCyc β1 β6 γ6 (i + 1) - k8q1pCyc β1 β6 γ6 i) ((0, 1, 0) - k8q1pCyc β1 β6 γ6 i)
      (v1, v2, v3)) ∧
    (∀ i : ZMod 5, TSc D (k8q1pCyc β1 β6 γ6 (i + 1) - k8q1pCyc β1 β6 γ6 i) ((1, 0, γ4) - k8q1pCyc β1 β6 γ6 i)
      (v1, v2, v3)) := by
  rcases eq_or_lt_of_le hβ6 with h | h
  · subst h
    obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
    have k1 := hD
    have kb1 := mul_pos hD hβ1
    have kb6 := mul_pos hD one_pos
    have kg6 := mul_pos hD hγ6
    have kg4 := mul_pos hD hγ4
    have kv1 := mul_pos hD hv1
    have kv2 := mul_pos hD (neg_pos.2 hv2)
    have kgv1 := mul_pos (mul_pos hD hγ6) hv1
    have kgv2 := mul_pos (mul_pos hD hγ6) (neg_pos.2 hv2)
    have kg4v1 := mul_pos (mul_pos hD hγ4) hv1
    have kg4v2 := mul_pos (mul_pos hD hγ4) (neg_pos.2 hv2)
    have ksv1 := mul_pos (mul_pos hD (sub_pos.2 hs)) hv1
    have kbv1 := mul_pos (mul_pos hD hβ1) hv1
    have kgc := mul_pos (mul_pos hD hγ6) (neg_pos.2 hcone)
    have kc := mul_pos hD (neg_pos.2 hcone)
    have kb6v1 := mul_pos (mul_pos hD one_pos) hv1
    refine ⟨?_, ?_⟩ <;> intro i <;>
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k8q1pCyc, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))
  · 
    obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
    have k1 := hD
    have kb1 := mul_pos hD hβ1
    have kb6 := mul_pos hD (by linarith : (0:ℝ) < β6)
    have kb61 := mul_pos hD (sub_pos.2 h)
    have kg6 := mul_pos hD hγ6
    have kg4 := mul_pos hD hγ4
    have kv1 := mul_pos hD hv1
    have kv2 := mul_pos hD (neg_pos.2 hv2)
    have kgv1 := mul_pos (mul_pos hD hγ6) hv1
    have kgv2 := mul_pos (mul_pos hD hγ6) (neg_pos.2 hv2)
    have kg4v1 := mul_pos (mul_pos hD hγ4) hv1
    have kg4v2 := mul_pos (mul_pos hD hγ4) (neg_pos.2 hv2)
    have ksv1 := mul_pos (mul_pos hD (sub_pos.2 hs)) hv1
    have kbv1 := mul_pos (mul_pos hD hβ1) hv1
    have kgc := mul_pos (mul_pos hD hγ6) (neg_pos.2 hcone)
    have kc := mul_pos hD (neg_pos.2 hcone)
    have kb6v1 := mul_pos (mul_pos hD (by linarith : (0:ℝ) < β6)) hv1
    have kb61v1 := mul_pos (mul_pos hD (sub_pos.2 h)) hv1
    refine ⟨?_, ?_⟩ <;> intro i <;>
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k8q1pCyc, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

theorem k8q1pCyc_inj {β1 β6 γ6 : ℝ} (hβ1 : 0 < β1) (hβ6 : 1 ≤ β6) (hγ6 : 0 < γ6) :
    ∀ i j, k8q1pCyc β1 β6 γ6 i = k8q1pCyc β1 β6 γ6 j → i = j := by
  intro i j h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [k8q1pCyc, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h)


set_option maxHeartbeats 3200000 in
/-- **The cell `Q1⁺`, `1 ≤ β6`**, tilt segment `(u + lam t)`; `s₁ ≥ 0`, a tie `s₁ = 0` is decided by the tilt. -/
theorem k8q1p_hasLexCellAt (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0)
    {β1 γ4 β6 γ6 u1 u2 t1 t2 : ℝ} (hβ1 : 0 < β1) (hγ4 : 0 < γ4) (hβ6 : 1 ≤ β6) (hγ6 : 0 < γ6)
    (hs : 1 < β6 + γ6) (hut : u1 * t2 - u2 * t1 ≠ 0)
    (hcone : ∀ lam : ℝ, 0 < lam → lam < 1 → 0 < u1 + lam * t1 ∧ u2 + lam * t2 < 0 ∧
      (1 - β1) * (u1 + lam * t1) + (u2 + lam * t2) < 0)
    (hC : 0 < ⟪q, r⟫) (hs1 : 0 ≤ (β6 - β1) * ⟪q, r⟫ + γ6 * ⟪r, r⟫ - ⟪p, r⟫)
    (hw : (β6 - β1) * ⟪q, r⟫ + γ6 * ⟪r, r⟫ - ⟪p, r⟫ = 0 → ∀ lam : ℝ, 0 < lam → lam < 1 →
      0 < (u1 + lam * t1) * ⟪fpoint p q r d (0, β6, γ6) - fpoint p q r d (1, β1, 0), p⟫ +
        (u2 + lam * t2) * ⟪fpoint p q r d (0, β6, γ6) - fpoint p q r d (1, β1, 0), q⟫)
    (hmem : ∀ i, fpoint p q r d (k8q1pCyc β1 β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint p q r d (0, 0, 1) ∨ y = fpoint p q r d (0, 0, 0) ∨
      y = fpoint p q r d (1, 0, 0) ∨ y = fpoint p q r d (1, β1, 0) ∨ y = fpoint p q r d (0, β6, γ6) ∨
      y = fpoint p q r d (0, 1, 0) ∨ y = fpoint p q r d (1, 0, γ4)) :
    HasLexCellAt V r := by
  set Y := k8q1pCyc β1 β6 γ6 with hY
  have hr0 : r ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  have hA : 0 < ⟪r, r⟫ := real_inner_self_pos.2 hr0
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint p q r d t, r⟫ = ⟪d, r⟫ + t.1 * ⟪p, r⟫ + t.2.1 * ⟪q, r⟫ + t.2.2 * ⟪r, r⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  refine k8_cell_gen V p q r d hΔ (by norm_num) Y (k8q1pCyc_inj hβ1 hβ6 hγ6) hut hmem ?_ ?_ ?_
  · intro lam hl0 hl1 D hD
    obtain ⟨h1, h2, h3⟩ := hcone lam hl0 hl1
    exact k8q1p_cyc hD hβ1 hβ6 hγ6 h1 h2 h3
  · intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [hY, k8q1pCyc, pc5_0])).elim
    · exact (hyx 1 (by simp only [hY, k8q1pCyc, pc5_1])).elim
    · exact (hyx 2 (by simp only [hY, k8q1pCyc, pc5_2])).elim
    · exact (hyx 3 (by simp only [hY, k8q1pCyc, pc5_3])).elim
    · exact (hyx 4 (by simp only [hY, k8q1pCyc, pc5_4])).elim
    · exact ⟨_, rfl, fun lam hl0 hl1 D hD => by
        obtain ⟨h1, h2, h3⟩ := hcone lam hl0 hl1
        exact (k8q1p_rest hD hβ1 hγ4 hβ6 hγ6 hs h1 h2 h3).1⟩
    · exact ⟨_, rfl, fun lam hl0 hl1 D hD => by
        obtain ⟨h1, h2, h3⟩ := hcone lam hl0 hl1
        exact (k8q1p_rest hD hβ1 hγ4 hβ6 hγ6 hs h1 h2 h3).2⟩
  · intro lam hl0 hl1 w hwd hw'
    refine lexUni5_top _ _ hw' ?_ ?_ ?_
    · left; simp only [hY, k8q1pCyc, pc5_0, pc5_1, hz]; nlinarith
    · left; simp only [hY, k8q1pCyc, pc5_2, pc5_3, hz]; nlinarith [mul_pos hβ1 hC]
    · rcases hs1.lt_or_eq with h | h
      · left; simp only [hY, k8q1pCyc, pc5_3, pc5_4, hz]; nlinarith
      · right; refine ⟨?_, ?_⟩
        · simp only [hY, k8q1pCyc, pc5_3, pc5_4, hz]; nlinarith
        · rw [hwd, hwd]
          have := k8_wdiff p q r d (0, β6, γ6) (1, β1, 0) (u1 + lam * t1) (u2 + lam * t2)
          simp only [hY, k8q1pCyc, pc5_3, pc5_4]
          linarith [hw h.symm lam hl0 hl1]

end C2
end Type08Sp
end Minimality
