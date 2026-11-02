module

public import Minimality.Type08S.C2K16K

@[expose] public section


/-!
# K16 / L: H5 rule r2: unimodality lemma and frame lemma (pentagon `(b', a', b, d, a)` at view `c' - a'`)
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

/-- Pentagon indices `0 = b', 1 = a', 2 = b, 3 = d, 4 = a`: `a' < b < d` and not (`a ≤ d`, `a ≤ b'`). -/
theorem k16_pent_uni_r2 (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h12 : z 1 < z 2) (h23 : z 2 < z 3) (hbad : z 4 ≤ z 3 → z 4 ≤ z 0 → False) : LexUni z w := by
  obtain ⟨M, hM⟩ := exists_key z w hinj
  refine lexUni_of_key z w (fun i => M * z i + w i) hinj hM ?_
  have lt : ∀ i j, z i < z j → M * z i + w i < M * z j + w j := fun i j h => (hM i j).1 (Or.inl h)
  have back : ∀ i j, M * z i + w i < M * z j + w j → z i ≤ z j := by
    intro i j h
    rcases (hM i j).2 h with h' | ⟨h1, h2⟩
    · exact h'.le
    · exact h1.le
  have hk := k6m_key_inj z w hinj M hM
  refine k5d_uni_of_nopair (by decide) _ hk ?_
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_sub1
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  have k12 := lt _ _ h12
  have k23 := lt _ _ h23
  intro i j h1 h2 h3 ⟨⟨pi1, pi2⟩, ⟨pj1, pj2⟩⟩
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact h1 rfl
    | exact h2 (by decide)
    | exact h3 (by decide)
    | (simp only [s0, s1, s2, s3, s4, f0, f1, f2, f3, f4] at pi1 pi2 pj1 pj2
       first
       | linarith
       | exact hbad (back _ _ (by linarith)) (back _ _ (by linarith)))

set_option maxHeartbeats 3200000 in
theorem k16_r2_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {α1 β1 β6 γ6 g : ℝ}
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hb6 : 0 < β6) (hb61 : β6 < 1) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hσ : β1 < β6 + γ6) (hg : g * γ6 = 1)
    (hmem : ∀ i, fpoint P Q R d (k16R2Cyc α1 β1 β6 g i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (α1 * (1 + β1 * g), β1 * (β1 - β6) * g, -(β1 * g)) ∨
      y = fpoint P Q R d (α1, β1, -1) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, 0) ∨
      y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (α1, β1, 0) ∨
      y = fpoint P Q R d (α1 * g, (β1 - β6) * g, -g))
    (h12 : ⟪fpoint P Q R d (α1, β1, -1), R⟫ < ⟪fpoint P Q R d (0, 1, 0), R⟫)
    (h23 : ⟪fpoint P Q R d (0, 1, 0), R⟫ < ⟪fpoint P Q R d (0, 0, 0), R⟫)
    (hbad : ⟪fpoint P Q R d (1, 0, 0), R⟫ ≤ ⟪fpoint P Q R d (0, 0, 0), R⟫ →
      ⟪fpoint P Q R d (1, 0, 0), R⟫ ≤ ⟪fpoint P Q R d (α1 * (1 + β1 * g), β1 * (β1 - β6) * g, -(β1 * g)), R⟫ →
        False) :
    HasLexCellAt V R := by
  have hgp : 0 < g := by
    by_contra h; push Not at h; nlinarith
  have hα1' : 0 < α1 := by linarith
  have hb1 : 0 < β1 - 1 := by linarith
  refine cyc_cell V P Q R d hΔ (k := 5) (by norm_num) (k16R2Cyc α1 β1 β6 g)
    (k16R2_inj hα1' hβ1 hgp) hmem [(α1, β1, (0 : ℝ)), (α1 * g, (β1 - β6) * g, -g)] ?_
    (u1 := 0) (u2 := 1) (t1 := 1) (t2 := 0) (lo := 0) (hi := α1 / (β1 - 1)) (by norm_num)
    (div_pos hα1' hb1)
    (fun v1 v2 => (β1 - 1) * v1 < α1 * v2 ∧ -(β6 + γ6 - β1) * v1 < α1 * v2) ?_ ?_ ?_
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
    simp only [mul_zero, add_zero, zero_add, mul_one]
    have h2 : lam < α1 / (β1 - 1) := h1
    rw [lt_div_iff₀ hb1] at h2
    refine ⟨by linarith, ?_⟩
    nlinarith
  · intro v1 v2 ⟨hc1, hc2⟩
    exact k16R2_tsc hα1 hβ1 hb6 hb61 hγ6 hγ61 hσ hg hc1 hc2
  · intro v1 v2 ⟨hc1, hc2⟩ hL
    refine k16_pent_uni_r2 _ _ hL ?_ ?_ ?_
    · simpa only [k16R2Cyc_1, k16R2Cyc_2] using h12
    · simpa only [k16R2Cyc_2, k16R2Cyc_3] using h23
    · simpa only [k16R2Cyc_4, k16R2Cyc_3, k16R2Cyc_0] using hbad

end C2
end Type08Sp
end Minimality
