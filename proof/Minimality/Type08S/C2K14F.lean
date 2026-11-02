module

public import Minimality.Type08S.C2K14E

@[expose] public section


/-!
# K14 / F: M `α1 = 1`: the cell `(a, c', a', c, d)` at the view `c - d`, assuming `⟪a - d, b - d⟫ < 0`, `β6 > 1`
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

/-- Pentagon `(a, c', a', c, d)` (indices `0..4`) with `a < d < c` (depth) and not (`a' ≤ c`, `a' ≤ c'`, `a ≤ c'`). -/
theorem k14_pent_uni_a1 (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h04 : z 0 < z 4) (h43 : z 4 < z 3) (hbad : z 2 ≤ z 3 → z 2 ≤ z 1 → z 0 ≤ z 1 → False) : LexUni z w := by
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
  have k04 := lt _ _ h04
  have k43 := lt _ _ h43
  intro i j h1 h2 h3 ⟨⟨pi1, pi2⟩, ⟨pj1, pj2⟩⟩
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact h1 rfl
    | exact h2 (by decide)
    | exact h3 (by decide)
    | (simp only [s0, s1, s2, s3, s4, f0, f1, f2, f3, f4] at pi1 pi2 pj1 pj2
       first
       | linarith
       | exact hbad (back _ _ (by linarith)) (back _ _ (by linarith)) (back _ _ (by linarith)))

set_option maxHeartbeats 3200000 in
theorem k14_a1_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {β1 β6 γ6 : ℝ}
    (hβ1 : 1 < β1) (hb6 : 1 < β6) (hγ6 : 0 < γ6)
    (hmem : ∀ i, fpoint P Q R d (k14A1Cyc β1 β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (1, β1, 0) ∨
      y = fpoint P Q R d (0, β6, γ6) ∨ y = fpoint P Q R d (0, 0, 1) ∨ y = fpoint P Q R d (0, 0, 0) ∨
      y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (1, 0, β1))
    (h04 : ⟪fpoint P Q R d (1, 0, 0), R⟫ < ⟪fpoint P Q R d (0, 0, 0), R⟫)
    (h43 : ⟪fpoint P Q R d (0, 0, 0), R⟫ < ⟪fpoint P Q R d (0, 0, 1), R⟫)
    (hbad : ⟪fpoint P Q R d (0, β6, γ6), R⟫ ≤ ⟪fpoint P Q R d (0, 0, 1), R⟫ →
      ⟪fpoint P Q R d (0, β6, γ6), R⟫ ≤ ⟪fpoint P Q R d (1, β1, 0), R⟫ →
      ⟪fpoint P Q R d (1, 0, 0), R⟫ ≤ ⟪fpoint P Q R d (1, β1, 0), R⟫ → False) :
    HasLexCellAt V R := by
  refine cyc_cell V P Q R d hΔ (k := 5) (by norm_num) (k14A1Cyc β1 β6 γ6)
    (k14A1_inj (by linarith) (by linarith) hγ6) hmem [((0 : ℝ), (1 : ℝ), (0 : ℝ)), (1, 0, β1)] ?_
    (u1 := 1) (u2 := -1) (t1 := 0) (t2 := 1) (lo := 0) (hi := 1) (by norm_num) (by norm_num)
    (fun v1 v2 => 0 < v1 ∧ v2 < 0) ?_ ?_ ?_
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
    linarith
  · intro v1 v2 ⟨hv1, hc⟩
    exact k14A1_tsc hβ1 hb6 hγ6 hv1 hc
  · intro v1 v2 ⟨hv1, hc⟩ hL
    refine k14_pent_uni_a1 _ _ hL ?_ ?_ ?_
    · simpa only [k14A1Cyc_0, k14A1Cyc_4] using h04
    · simpa only [k14A1Cyc_4, k14A1Cyc_3] using h43
    · simpa only [k14A1Cyc_0, k14A1Cyc_1, k14A1Cyc_2, k14A1Cyc_3] using hbad

end C2
end Type08Sp
end Minimality
