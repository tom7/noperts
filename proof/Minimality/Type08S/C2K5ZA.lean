module

public import Minimality.Type08S.C2K5LP

@[expose] public section


/-!
# K5Z / A: the QTc `α4 > 1` cells at `a - b'` for a general `a' = (β6, 1)` (no `κ_c = 0`)
Copies of `km1_tsc`, `km2_tsc`, `k5c_qtc1_frame`, `k5c_qtc2_frame` (C2K5LM, C2K5LO) with the `κ_c = 0` relation
`κ (1 - β6) = 1` replaced by `hbc : 1 < β1 + κ α1 (1 - β6)`: the only test that used it is the rest point `b = (1,0,0)`
against the edge `c' → a'` (screen orientation `κ α1 (1 - β6) + β1 - 1`).  `κ_c = 0` gives `hbc` from `α1 + β1 > 1`;
box D of QTa (`β1 > 1`, `β6 > 1`, `κ < 0`) gives it directly.
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

set_option maxHeartbeats 3200000 in
theorem k5z_km1_tsc {κ σ α1 β1 β6 v1 v2 : ℝ} (hκ : κ < 0) (hσ : σ < 0) (hα1 : 1 < α1) (hβ1 : 0 < β1)
    (hb6 : 1 < β6) (hbc : 1 < β1 + κ * α1 * (1 - β6)) (hE : (σ - 1) * (1 - β1) ≤ α1 * (σ - κ))
    (hv1 : 0 < v1) (hcone : κ * (α1 - 1) * v1 < β1 * v2) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (kmCyc1 κ σ α1 β1 β6 (i + 1) - kmCyc1 κ σ α1 β1 β6 i)
        (kmCyc1 κ σ α1 β1 β6 j - kmCyc1 κ σ α1 β1 β6 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0, κ, σ - 1)], ∀ i : ZMod 5,
      TSc 1 (kmCyc1 κ σ α1 β1 β6 (i + 1) - kmCyc1 κ σ α1 β1 β6 i) (t - kmCyc1 κ σ α1 β1 β6 i) (v1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  have nk : 0 < -κ := by linarith
  have ns : 0 < -σ := by linarith
  have a1 : 0 < α1 - 1 := by linarith
  have b6 : 0 < β6 - 1 := by linarith
  have h1 := mul_pos nk hv1
  have h2 := mul_pos ns hv1
  have h3 := mul_pos hβ1 nk
  have h4 := mul_pos (mul_pos nk a1) hv1
  have h5 := mul_pos nk b6
  have h6 := mul_pos hβ1 b6
  have h7 := mul_pos (mul_pos hβ1 nk) b6
  have h8 := mul_pos (mul_pos nk a1) b6
  have h9 := mul_pos ns a1
  have h10 := mul_pos (mul_pos ns a1) hv1
  have h11 := mul_pos ns (sub_pos.2 hcone)
  have h12 := mul_pos hβ1 ns
  have h13 := mul_pos (mul_pos hβ1 ns) b6
  have h14 := mul_pos nk (sub_pos.2 hcone)
  have h15 := mul_pos b6 (sub_pos.2 hcone)
  have h16 := mul_pos (mul_pos nk a1) (sub_pos.2 hcone)
  constructor
  · intro i j h1 h2
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, kmCyc1_0, kmCyc1_1, kmCyc1_2, kmCyc1_3, kmCyc1_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, kmCyc1_0, kmCyc1_1, kmCyc1_2, kmCyc1_3, kmCyc1_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 3200000 in
theorem k5z_km2_tsc {κ σ α1 β1 β6 v1 v2 : ℝ} (hκ : κ < 0) (hσ : σ < 0) (hα1 : 1 < α1) (hβ1 : 0 < β1)
    (hb6 : 1 < β6) (hbc : 1 < β1 + κ * α1 * (1 - β6)) (hE : (σ - 1) * (1 - β1) ≤ α1 * (σ - κ))
    (hv1 : v1 < 0) (hcone : β1 * v2 < κ * (α1 - 1) * v1) :
    (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      TSc 1 (kmCyc2 κ σ α1 β1 β6 (i + 1) - kmCyc2 κ σ α1 β1 β6 i)
        (kmCyc2 κ σ α1 β1 β6 j - kmCyc2 κ σ α1 β1 β6 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), κ, σ), (0, 0, 0), (1, 0, 0)], ∀ i : ZMod 4,
      TSc 1 (kmCyc2 κ σ α1 β1 β6 (i + 1) - kmCyc2 κ σ α1 β1 β6 i) (t - kmCyc2 κ σ α1 β1 β6 i) (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3⟩ := z4_add
  have nk : 0 < -κ := by linarith
  have ns : 0 < -σ := by linarith
  have a1 : 0 < α1 - 1 := by linarith
  have b6 : 0 < β6 - 1 := by linarith
  have nv : 0 < -v1 := by linarith
  have h1 := mul_pos nk nv
  have h2 := mul_pos ns nv
  have h3 := mul_pos hβ1 nk
  have h4 := mul_pos (mul_pos nk a1) nv
  have h5 := mul_pos nk b6
  have h6 := mul_pos hβ1 b6
  have h7 := mul_pos (mul_pos hβ1 nk) b6
  have h8 := mul_pos (mul_pos nk a1) b6
  have h9 := mul_pos ns a1
  have h10 := mul_pos (mul_pos ns a1) nv
  have h11 := mul_pos ns (sub_pos.2 hcone)
  have h12 := mul_pos hβ1 ns
  have h13 := mul_pos (mul_pos hβ1 ns) b6
  have h14 := mul_pos nk (sub_pos.2 hcone)
  have h15 := mul_pos b6 (sub_pos.2 hcone)
  have h16 := mul_pos (mul_pos nk a1) (sub_pos.2 hcone)
  have h17 : 0 < 1 - σ := by linarith
  have h18 := mul_pos h17 nv
  have h19 := mul_pos (sub_pos.2 hcone) h17
  constructor
  · intro i j h1 h2
    rcases z4_cases i with rfl | rfl | rfl | rfl <;>
      rcases z4_cases j with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, kmCyc2_0, kmCyc2_1, kmCyc2_2, kmCyc2_3, s0, s1, s2, s3,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;>
      rcases z4_cases i with rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, kmCyc2_0, kmCyc2_1, kmCyc2_2, kmCyc2_3, s0, s1, s2, s3,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 3200000 in
/-- Cell 1 (`⟪P,R⟫ < 0`): pentagon `(a, c', a', c, d)`. -/
theorem k5z_qtc1_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {κ σ α1 β1 β6 : ℝ}
    (hκ : κ < 0) (hσ : σ < 0) (hα1 : 1 < α1) (hβ1 : 0 < β1) (hb6 : 1 < β6) (hbc : 1 < β1 + κ * α1 * (1 - β6))
    (hE : (σ - 1) * (1 - β1) ≤ α1 * (σ - κ)) (hBz : ⟪P, R⟫ < 0)
    (hmem : ∀ i, fpoint P Q R d (kmCyc1 κ σ α1 β1 β6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, κ, σ) ∨ y = fpoint P Q R d (β1, κ * α1, α1 * σ) ∨
      y = fpoint P Q R d (β6, 1, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, 0) ∨
      y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (0, κ, σ - 1)) :
    HasLexCellAt V R := by
  have hR0 : R ≠ 0 := by intro h; apply hΔ; rw [h]; simp [det3_expand]
  have hA : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hR0
  have nk : 0 < -κ := by linarith
  have a1 : 0 < α1 - 1 := by linarith
  refine cyc_cell V P Q R d hΔ (k := 5) (by norm_num) (kmCyc1 κ σ α1 β1 β6)
    (km1_inj hκ hα1 hβ1 hb6) hmem [((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0, κ, σ - 1)] ?_
    (u1 := 1) (u2 := 0) (t1 := 0) (t2 := 1) (lo := 0) (hi := 1) (by norm_num) (by norm_num)
    (fun v1 v2 => 0 < v1 ∧ κ * (α1 - 1) * v1 < β1 * v2) ?_ ?_ ?_
  · intro y hy
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inl ⟨2, rfl⟩
    · exact Or.inl ⟨3, rfl⟩
    · exact Or.inl ⟨4, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
  · intro lam h0 h1
    refine ⟨by simp, ?_⟩
    simp only [mul_zero, add_zero, zero_add, mul_one]
    nlinarith [mul_pos nk a1, mul_pos hβ1 h0]
  · intro v1 v2 ⟨hv1, hc⟩
    exact k5z_km1_tsc hκ hσ hα1 hβ1 hb6 hbc hE hv1 hc
  · intro v1 v2 ⟨hv1, hc⟩ hL
    set v := fcomb P Q R v1 v2 0 with hv
    obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
    refine pent1_lexUni _ _ hL (κ := κ) (σ := σ) (α1 := α1) (β1 := β1) (β6 := β6) (bz := ⟪P, R⟫)
      (bw := ⟪P, v⟫) (cz := ⟪Q, R⟫) (cw := ⟪Q, v⟫) (A := ⟪R, R⟫) (uw := ⟪R, v⟫) hBz hA hκ hσ hα1.le hβ1
      (by linarith) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals simp only [kmCyc1_0, kmCyc1_1, kmCyc1_2, kmCyc1_3, kmCyc1_4, inner_fpoint]
    all_goals ring

set_option maxHeartbeats 3200000 in
/-- Cell 2 (`0 < ⟪P,R⟫`): quadrilateral `(b', c', a', c)`. -/
theorem k5z_qtc2_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {κ σ α1 β1 β6 : ℝ}
    (hκ : κ < 0) (hσ : σ < 0) (hα1 : 1 < α1) (hβ1 : 0 < β1) (hb6 : 1 < β6) (hbc : 1 < β1 + κ * α1 * (1 - β6))
    (hE : (σ - 1) * (1 - β1) ≤ α1 * (σ - κ)) (hBz : 0 < ⟪P, R⟫)
    (hmem : ∀ i, fpoint P Q R d (kmCyc2 κ σ α1 β1 β6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, κ, σ - 1) ∨ y = fpoint P Q R d (β1, κ * α1, α1 * σ) ∨
      y = fpoint P Q R d (β6, 1, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, κ, σ) ∨
      y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0)) :
    HasLexCellAt V R := by
  have hR0 : R ≠ 0 := by intro h; apply hΔ; rw [h]; simp [det3_expand]
  have hA : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hR0
  have nk : 0 < -κ := by linarith
  have a1 : 0 < α1 - 1 := by linarith
  refine cyc_cell V P Q R d hΔ (k := 4) (by norm_num) (kmCyc2 κ σ α1 β1 β6)
    (km2_inj hκ hα1 hβ1 hb6) hmem [((0 : ℝ), κ, σ), (0, 0, 0), (1, 0, 0)] ?_
    (u1 := -1) (u2 := 0) (t1 := 0) (t2 := -1) (lo := 0) (hi := 1) (by norm_num) (by norm_num)
    (fun v1 v2 => v1 < 0 ∧ β1 * v2 < κ * (α1 - 1) * v1) ?_ ?_ ?_
  · intro y hy
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inl ⟨2, rfl⟩
    · exact Or.inl ⟨3, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
  · intro lam h0 h1
    refine ⟨by simp, ?_⟩
    simp only [mul_zero, add_zero, zero_add, mul_one, mul_neg]
    nlinarith [mul_pos nk a1, mul_pos hβ1 h0]
  · intro v1 v2 ⟨hv1, hc⟩
    exact k5z_km2_tsc hκ hσ hα1 hβ1 hb6 hbc hE hv1 hc
  · intro v1 v2 ⟨hv1, hc⟩ hL
    set v := fcomb P Q R v1 v2 0 with hv
    obtain ⟨s0, s1, s2, s3⟩ := z4_add
    refine quad2_lexUni _ _ hL (zd := ⟪d, R⟫) (wd := ⟪d, v⟫) (κ := κ) (σ := σ) (α1 := α1) (β1 := β1)
      (β6 := β6) (bz := ⟪P, R⟫) (bw := ⟪P, v⟫) (cz := ⟪Q, R⟫) (cw := ⟪Q, v⟫) (A := ⟪R, R⟫) (uw := ⟪R, v⟫)
      hBz hA hκ hσ hα1 hβ1 (by linarith) hE ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals simp only [kmCyc2_0, kmCyc2_1, kmCyc2_2, kmCyc2_3, inner_fpoint]
    all_goals ring

end C2
end Type08Sp
end Minimality
