module

public import Minimality.Type08S.C2K17GD3A

@[expose] public section


/-!
# K17GD / GD3: the slice `K6tTaA41` (Ta, `α4 = 1`, `β6 ≥ 1`), generic part `⟪b-d,c-d⟫ ≠ 0` (`ζ(d,b) = γ4 ⟪b-d,c-d⟫`)

Frame `(p,q,r) = (a-d,b-d,c-d)`, `c' = (α1,β1,0)`, `b' = (1,0,γ4)`, `a' = (0,β6,1)`; `κ_a = 0` gives `E = 1-β1-α1+α1γ4 = 0`.
* `⟪q,r⟫ > 0`: cell C1 `(a,c',a',b,d)` at `r`: cone `v1 < 0 > v2`, `(α1-1)(-v2) > β1(-v1)` (valid for all `β6 ≥ 1`);
  lex: `d < b < a'`, `a` not a peak.
* `⟪q,r⟫ < 0`: cell B `(c',b',c,d,b)` at `q` (as `K6tTcA41`, `k17gdB_frame6` has the extra rest point `a' = (0,1,β6)`).
* Leftover: `⟪q,r⟫ = 0`.  Includes `β6 = 1`, no case split needed.
-/
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
theorem k17gdB_restA6 {α1 β1 γ4 β6 v1 v2 : ℝ} (hα1 : 1 < α1) (hβ1 : 0 < β1) (hγ4 : 0 < γ4) (hβ6 : 0 < β6)
    (hv1 : v1 < 0) (hv2 : 0 < v2) (hE : 0 ≤ 1 - β1 - α1 + α1 * γ4) (hc : 0 < v2 + (1 - γ4) * v1) :
    ∀ i : ZMod 5, TSc 1 (k17gdB α1 β1 γ4 (i + 1) - k17gdB α1 β1 γ4 i) ((0, 1, β6) - k17gdB α1 β1 γ4 i) (v1, v2, 0) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have a1 := sub_pos.2 hα1
  have a2 := neg_pos.2 hv1
  have k1 := mul_pos a1 a2
  have k2 := mul_pos a1 hv2
  have k3 := mul_pos hβ1 a2
  have k4 := mul_pos hβ1 hv2
  have k5 := mul_pos a2 hv2
  have k6 := mul_pos hc hβ1
  have k7 := mul_pos hc a1
  have k8 := mul_pos hc hv2
  have k9 := mul_pos hc a2
  have g1 := mul_pos hγ4 a2
  have g2 := mul_pos hγ4 hv2
  have g3 := mul_pos (mul_pos hγ4 a2) hβ1
  have g4 := mul_pos (mul_pos hγ4 hv2) a1
  have g5 := mul_pos (mul_pos hγ4 hv2) hβ1
  have g6 := mul_pos (mul_pos hγ4 a2) a1
  have g7 := mul_pos hγ4 hc
  have b1 := mul_pos hβ6 a2
  have b2 := mul_pos hβ6 hv2
  have b3 := mul_pos hβ6 hc
  have b4 := mul_pos (mul_pos hβ6 a2) a1
  have b5 := mul_pos (mul_pos hβ6 hv2) a1
  have b6 := mul_pos (mul_pos hβ6 a2) hβ1
  have b7 := mul_pos (mul_pos hβ6 hv2) hβ1
  have b8 := mul_pos (mul_pos hβ6 a2) hγ4
  have b9 := mul_pos (mul_pos hβ6 hv2) hγ4
  intro i
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, k17gdB, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 3200000 in
/-- Cell B with a general rest point `a' = (0,1,β6)`: the proof of `k17gdB_frame` with `β6` in place of `1`. -/
theorem k17gdB_frame6 (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p r q ≠ 0) {α1 β1 γ4 β6 : ℝ}
    (hα1 : 1 < α1) (hβ1 : 0 < β1) (hγ4 : 0 < γ4) (hβ6 : 0 < β6) (hE : 0 ≤ 1 - β1 - α1 + α1 * γ4)
    (hrr : 0 < ⟪r, r⟫) (σ1 : ℝ) (hσ : max 0 (1 - γ4) < σ1)
    (hcase : ⟪r, q⟫ < 0 ∨ (⟪r, q⟫ = 0 ∧ σ1 * ⟪r, r⟫ ≤ ⟪p, r⟫))
    (hmem : ∀ i, fpoint p r q d (k17gdB α1 β1 γ4 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint p r q d (α1, 0, β1) ∨ y = fpoint p r q d (1, γ4, 0) ∨
      y = fpoint p r q d (0, 1, 0) ∨ y = fpoint p r q d (0, 0, 0) ∨ y = fpoint p r q d (0, 0, 1) ∨
      y = fpoint p r q d (1, 0, 0) ∨ y = fpoint p r q d (0, 1, β6)) :
    HasLexCellAt V q := by
  have hq0 : q ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  have hqq : 0 < ⟪q, q⟫ := real_inner_self_pos.2 hq0
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint p r q d t, q⟫ = ⟪d, q⟫ + t.1 * ⟪p, q⟫ + t.2.1 * ⟪r, q⟫ + t.2.2 * ⟪q, q⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  set σ0 := max 0 (1 - γ4) with hσ0
  have hσ00 : 0 ≤ σ0 := le_max_left _ _
  have hσ01 : 1 - γ4 ≤ σ0 := le_max_right _ _
  have hsg : 0 < σ1 - σ0 := by linarith
  refine cyc_cell V p r q d hΔ (k := 5) (by norm_num) (k17gdB α1 β1 γ4) (k17gdB_inj hα1 hβ1 hγ4) hmem
    [(1, 0, 0), (0, 1, β6)] ?_ (u1 := -1) (u2 := σ0) (t1 := 0) (t2 := σ1 - σ0) (lo := 0) (hi := 1)
    (by rw [show (-1:ℝ) * (σ1 - σ0) - σ0 * 0 = -(σ1 - σ0) by ring]; exact (neg_ne_zero.2 hsg.ne'))
    (by norm_num)
    (fun v1 v2 => v1 = -1 ∧ σ0 < v2 ∧ v2 < σ1) ?_ ?_ ?_
  · intro y hy
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by simp [k17gdB, pc5_0]⟩
    · exact Or.inl ⟨1, by simp [k17gdB, pc5_1]⟩
    · exact Or.inl ⟨2, by simp [k17gdB, pc5_2]⟩
    · exact Or.inl ⟨3, by simp [k17gdB, pc5_3]⟩
    · exact Or.inl ⟨4, by simp [k17gdB, pc5_4]⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
  · intro lam hl0 hl1
    refine ⟨by ring, by nlinarith, by nlinarith⟩
  · intro v1 v2 hv
    obtain ⟨h1, h2, h3⟩ := hv
    have hv1 : v1 < 0 := by rw [h1]; norm_num
    have hv2 : 0 < v2 := by linarith
    have hc : 0 < v2 + (1 - γ4) * v1 := by rw [h1]; linarith
    refine ⟨k17gdB_tsc hα1 hβ1 hγ4 hv1 hv2 hE hc, ?_⟩
    intro t ht i
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact (k17gdB_rest hα1 hβ1 hγ4 hv1 hv2 hE hc).1 i
    · exact k17gdB_restA6 hα1 hβ1 hγ4 hβ6 hv1 hv2 hE hc i
  · intro v1 v2 hv hsep
    obtain ⟨h1, h2, h3⟩ := hv
    set z : ZMod 5 → ℝ := fun i => ⟪fpoint p r q d (k17gdB α1 β1 γ4 i), q⟫ with hzdef
    set w : ZMod 5 → ℝ := fun i => ⟪fpoint p r q d (k17gdB α1 β1 γ4 i), fcomb p r q v1 v2 0⟫ with hwdef
    have z0 : z 0 = ⟪d, q⟫ + α1 * ⟪p, q⟫ + β1 * ⟪q, q⟫ := by simp only [hzdef, k17gdB, pc5_0, hz]; ring
    have z1 : z 1 = ⟪d, q⟫ + ⟪p, q⟫ + γ4 * ⟪r, q⟫ := by simp only [hzdef, k17gdB, pc5_1, hz]; ring
    have z2 : z 2 = ⟪d, q⟫ + ⟪r, q⟫ := by simp only [hzdef, k17gdB, pc5_2, hz]; ring
    have z3 : z 3 = ⟪d, q⟫ := by simp only [hzdef, k17gdB, pc5_3, hz]; ring
    have z4 : z 4 = ⟪d, q⟫ + ⟪q, q⟫ := by simp only [hzdef, k17gdB, pc5_4, hz]; ring
    have h34 : LexLt (z 3, w 3) (z 4, w 4) := k17gd_ll (by rw [z3, z4]; linarith)
    have hkey : ∀ hqr : ⟪r, q⟫ ≤ 0, LexLt (z 1, w 1) (z 0, w 0) ∨ LexLt (z 1, w 1) (z 2, w 2) := by
      intro hqr
      rcases k17gdB_key (pq := ⟪p, q⟫) hα1 hβ1 hγ4 hE hqq hqr with k | k
      · left; exact k17gd_ll (by rw [z0, z1]; linarith)
      · right; exact k17gd_ll (by rw [z1, z2]; linarith)
    rcases hcase with hq | ⟨hq, hlit⟩
    · exact k17gd_lexUni5_B z w hsep (k17gd_ll (by rw [z2, z3]; linarith)) h34 (fun _ => hkey hq.le)
    · have h23 : LexLt (z 2, w 2) (z 3, w 3) := by
        refine k17gd_ll' (by rw [z2, z3, hq]; ring) ?_
        simp only [hwdef, k17gdB, pc5_2, pc5_3, k17f_wexp]
        have : v1 * (⟪d, p⟫ + (0:ℝ) * ⟪p, p⟫ + (1:ℝ) * ⟪p, r⟫ + (0:ℝ) * ⟪p, q⟫) +
            v2 * (⟪d, r⟫ + (0:ℝ) * ⟪p, r⟫ + (1:ℝ) * ⟪r, r⟫ + (0:ℝ) * ⟪r, q⟫) <
            v1 * (⟪d, p⟫ + (0:ℝ) * ⟪p, p⟫ + (0:ℝ) * ⟪p, r⟫ + (0:ℝ) * ⟪p, q⟫) +
            v2 * (⟪d, r⟫ + (0:ℝ) * ⟪p, r⟫ + (0:ℝ) * ⟪r, r⟫ + (0:ℝ) * ⟪r, q⟫) := by
          rw [h1]; nlinarith
        exact this
      exact k17gd_lexUni5_B z w hsep h23 h34 (fun _ => hkey hq.le)

set_option maxHeartbeats 3200000 in
/-- **Ta `α4 = 1`, cell C1** `(a, c', a', b, d)` at `r`, frame `(p, q, r)`, for `⟪q,r⟫ > 0`, `β6 ≥ 1`. -/
theorem k17gdC1_frame (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0) {α1 β1 β6 γ4 : ℝ}
    (hα1 : 1 < α1) (hβ1 : 0 < β1) (hβ6 : 1 ≤ β6) (hγ4 : 0 < γ4) (hqr : 0 < ⟪q, r⟫)
    (hmem : ∀ i, fpoint p q r d (k17gdC1 α1 β1 β6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint p q r d (1, 0, 0) ∨ y = fpoint p q r d (α1, β1, 0) ∨
      y = fpoint p q r d (0, β6, 1) ∨ y = fpoint p q r d (0, 1, 0) ∨ y = fpoint p q r d (0, 0, 0) ∨
      y = fpoint p q r d (0, 0, 1) ∨ y = fpoint p q r d (1, 0, γ4)) :
    HasLexCellAt V r := by
  have hr0 : r ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  have hA : 0 < ⟪r, r⟫ := real_inner_self_pos.2 hr0
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint p q r d t, r⟫ = ⟪d, r⟫ + t.1 * ⟪p, r⟫ + t.2.1 * ⟪q, r⟫ + t.2.2 * ⟪r, r⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have a1 := sub_pos.2 hα1
  obtain ⟨t1, ht1def⟩ : ∃ t1 : ℝ, t1 = (α1 - 1) / (β1 + α1) := ⟨_, rfl⟩
  have hden : 0 < β1 + α1 := by linarith
  have ht1 : 0 < t1 := by rw [ht1def]; exact div_pos a1 hden
  have ht1e : t1 * (β1 + α1) = α1 - 1 := by rw [ht1def]; field_simp
  have hinj : ∀ i j, k17gdC1 α1 β1 β6 i = k17gdC1 α1 β1 β6 j → i = j := by
    intro i j h
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      simp only [k17gdC1, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4, Prod.mk.injEq] at h <;>
      first | rfl | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h) |
        (exfalso; obtain ⟨h1, h2, h3⟩ := h; nlinarith)
  refine cyc_cell V p q r d hΔ (k := 5) (by norm_num) (k17gdC1 α1 β1 β6) hinj hmem
    [(0, 0, 1), (1, 0, γ4)] ?_ (u1 := 0) (u2 := -1) (t1 := -t1) (t2 := 0) (lo := 0) (hi := 1)
    (by rw [show (0:ℝ) * 0 - (-1) * (-t1) = -t1 by ring]; exact (neg_ne_zero.2 ht1.ne')) (by norm_num)
    (fun v1 v2 => v1 < 0 ∧ v2 < 0 ∧ 0 < -(α1 - 1) * v2 + β1 * v1) ?_ ?_ ?_
  · intro y hy
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by simp [k17gdC1, pc5_0]⟩
    · exact Or.inl ⟨1, by simp [k17gdC1, pc5_1]⟩
    · exact Or.inl ⟨2, by simp [k17gdC1, pc5_2]⟩
    · exact Or.inl ⟨3, by simp [k17gdC1, pc5_3]⟩
    · exact Or.inl ⟨4, by simp [k17gdC1, pc5_4]⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
  · intro lam hl0 hl1
    refine ⟨by nlinarith [mul_pos hl0 ht1], by norm_num, ?_⟩
    simp only [mul_zero, add_zero, zero_add]
    nlinarith [mul_pos hl0 ht1, mul_pos hβ1 (mul_pos hl0 ht1), mul_pos hβ1 ht1, mul_pos hβ1 (mul_pos (sub_pos.2 hl1) ht1)]
  · intro v1 v2 hv
    refine ⟨k17gdC1_tsc hα1 hβ1 hβ6 hv.1 hv.2.1 hv.2.2, ?_⟩
    intro t ht i
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact (k17gdC1_rest hα1 hβ1 hβ6 hγ4 hv.1 hv.2.1 hv.2.2).1 i
    · exact (k17gdC1_rest hα1 hβ1 hβ6 hγ4 hv.1 hv.2.1 hv.2.2).2 i
  · intro v1 v2 hv hsep
    set z : ZMod 5 → ℝ := fun i => ⟪fpoint p q r d (k17gdC1 α1 β1 β6 i), r⟫ with hzdef
    set w : ZMod 5 → ℝ := fun i => ⟪fpoint p q r d (k17gdC1 α1 β1 β6 i), fcomb p q r v1 v2 0⟫ with hwdef
    have z0 : z 0 = ⟪d, r⟫ + ⟪p, r⟫ := by simp only [hzdef, k17gdC1, pc5_0, hz]; ring
    have z1 : z 1 = ⟪d, r⟫ + α1 * ⟪p, r⟫ + β1 * ⟪q, r⟫ := by simp only [hzdef, k17gdC1, pc5_1, hz]; ring
    have z2 : z 2 = ⟪d, r⟫ + β6 * ⟪q, r⟫ + ⟪r, r⟫ := by simp only [hzdef, k17gdC1, pc5_2, hz]; ring
    have z3 : z 3 = ⟪d, r⟫ + ⟪q, r⟫ := by simp only [hzdef, k17gdC1, pc5_3, hz]; ring
    have z4 : z 4 = ⟪d, r⟫ := by simp only [hzdef, k17gdC1, pc5_4, hz]; ring
    refine k17gd_lexUni5_A z w hsep (k17gd_ll (by rw [z3, z2]; nlinarith)) (k17gd_ll (by rw [z4, z3]; linarith)) ?_
    rcases lt_or_ge ⟪p, r⟫ 0 with hp | hp
    · left; exact k17gd_ll (by rw [z0, z4]; linarith)
    · right; exact k17gd_ll (by rw [z0, z1]; nlinarith [mul_nonneg a1.le hp, mul_pos hβ1 hqr])

end C2
end Type08Sp
end Minimality
