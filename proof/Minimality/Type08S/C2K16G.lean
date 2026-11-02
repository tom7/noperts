module

public import Minimality.Type08S.C2K16F

@[expose] public section


/-!
# K16 / G: H5 rule r1: `⟪c - a', d - c⟫ < 0` plus the Coll5 relation closes (view `c - d`, pentagon `(c', b, a', c, b')`)
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

/-- Pentagon with strictly increasing depth along the index order (peak at `4`, valley at `0`). -/
theorem k16_pent_uni_chain (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h01 : z 0 < z 1) (h12 : z 1 < z 2) (h23 : z 2 < z 3) (h34 : z 3 < z 4) : LexUni z w := by
  obtain ⟨M, hM⟩ := exists_key z w hinj
  refine lexUni_of_key z w (fun i => M * z i + w i) hinj hM ?_
  have lt : ∀ i j, z i < z j → M * z i + w i < M * z j + w j := fun i j h => (hM i j).1 (Or.inl h)
  have hk := k6m_key_inj z w hinj M hM
  refine k5d_uni_of_nopair (by decide) _ hk ?_
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_sub1
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  have k01 := lt _ _ h01
  have k12 := lt _ _ h12
  have k23 := lt _ _ h23
  have k34 := lt _ _ h34
  intro i j h1 h2 h3 ⟨⟨pi1, pi2⟩, ⟨pj1, pj2⟩⟩
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact h1 rfl
    | exact h2 (by decide)
    | exact h3 (by decide)
    | (simp only [s0, s1, s2, s3, s4, f0, f1, f2, f3, f4] at pi1 pi2 pj1 pj2
       linarith)

set_option maxHeartbeats 3200000 in
theorem k16_r1_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {α1 β1 β6 γ6 : ℝ}
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hb6 : 0 < β6) (hb61 : β6 < 1) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hσ : β1 < β6 + γ6)
    (hmem : ∀ i, fpoint P Q R d (k16R1Cyc α1 β1 β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (α1, β1, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨
      y = fpoint P Q R d (0, β6, γ6) ∨ y = fpoint P Q R d (0, 0, 1) ∨ y = fpoint P Q R d (α1, 0, β1) ∨
      y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (0, 0, 0))
    (h01 : ⟪fpoint P Q R d (α1, β1, 0), R⟫ < ⟪fpoint P Q R d (0, 1, 0), R⟫)
    (h12 : ⟪fpoint P Q R d (0, 1, 0), R⟫ < ⟪fpoint P Q R d (0, β6, γ6), R⟫)
    (h23 : ⟪fpoint P Q R d (0, β6, γ6), R⟫ < ⟪fpoint P Q R d (0, 0, 1), R⟫)
    (h34 : ⟪fpoint P Q R d (0, 0, 1), R⟫ < ⟪fpoint P Q R d (α1, 0, β1), R⟫) :
    HasLexCellAt V R := by
  refine cyc_cell V P Q R d hΔ (k := 5) (by norm_num) (k16R1Cyc α1 β1 β6 γ6)
    (k16R1_inj (by linarith) hβ1 hb6 hγ6) hmem [((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0, 0, 0)] ?_
    (u1 := 1) (u2 := 1) (t1 := 0) (t2 := 1) (lo := 0) (hi := 1) (by norm_num) (by norm_num)
    (fun v1 v2 => 0 < v1 ∧ 0 < v2) ?_ ?_ ?_
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
  · intro v1 v2 ⟨hv1, hv2⟩
    exact k16R1_tsc hα1 hβ1 hb6 hb61 hγ6 hγ61 hσ hv1 hv2
  · intro v1 v2 ⟨hv1, hv2⟩ hL
    refine k16_pent_uni_chain _ _ hL ?_ ?_ ?_ ?_
    · simpa only [k16R1Cyc_0, k16R1Cyc_1] using h01
    · simpa only [k16R1Cyc_1, k16R1Cyc_2] using h12
    · simpa only [k16R1Cyc_2, k16R1Cyc_3] using h23
    · simpa only [k16R1Cyc_3, k16R1Cyc_4] using h34

end C2
end Type08Sp
end Minimality
