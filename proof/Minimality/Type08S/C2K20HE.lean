module

public import Minimality.Type08S.C2K20HD

@[expose] public section


/-!
# K20H5 / E: H5 rule r7 (line view `L14`): unimodality lemma, frame lemma and `k20_r7_hasLexCell`.
Rule: `(β1-1)(α1-1) γ6 < α1 β1 (1-β6)` and `⟪a' - c, w⟫ > 0` with `w = α1 (1-β6)(a-d) + (β1-1) γ6 (c-d)`
(the sign-normalized `det3[a-b'](c', b, a') < 0 ∧ ζ_{L14}(c, a') > 0` of the sampler rule 7, chirality-free).
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

/-- Pentagon with indices `0,1,2` not depth peaks (each has a strictly higher neighbour). -/
theorem k20_pent_uni3 (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h0 : z 0 < z 4 ∨ z 0 < z 1) (h1 : z 1 < z 0 ∨ z 1 < z 2) (h2 : z 2 < z 1 ∨ z 2 < z 3) : LexUni z w := by
  obtain ⟨M, hM⟩ := exists_key z w hinj
  refine lexUni_of_key z w (fun i => M * z i + w i) hinj hM ?_
  have lt : ∀ i j, z i < z j → M * z i + w i < M * z j + w j := fun i j h => (hM i j).1 (Or.inl h)
  have hk := k6m_key_inj z w hinj M hM
  refine k5d_uni_of_nopair (by decide) _ hk ?_
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_sub1
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  have k0 := h0.imp (lt 0 4) (lt 0 1)
  have k1 := h1.imp (lt 1 0) (lt 1 2)
  have k2 := h2.imp (lt 2 1) (lt 2 3)
  intro i j hij1 hij2 hij3 ⟨⟨pi1, pi2⟩, ⟨pj1, pj2⟩⟩
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact hij1 rfl
    | exact hij2 (by decide)
    | exact hij3 (by decide)
    | (simp only [s0, s1, s2, s3, s4, f0, f1, f2, f3, f4] at pi1 pi2 pj1 pj2
       rcases k0 with k0 | k0 <;> rcases k1 with k1 | k1 <;> rcases k2 with k2 | k2 <;> linarith)

set_option maxHeartbeats 3200000 in
theorem k20_r7_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {α β β6 γ6 μ ν : ℝ}
    (hα : 1 < α) (hβ : 1 < β) (hb6 : 0 < β6) (hb61 : β6 < 1) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hσ : β < β6 + γ6) (hμ : 0 < μ) (hν : 0 < ν) (hνμ : ν = γ6 * μ) (hνβ : ν * (β - 1) = 1)
    (hb : α - β * (α * (1 - β6)) * μ < 1)
    (hmem : ∀ i, fpoint P Q R d (k20R7Cyc α β β6 μ ν i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (-(α * (1 - β6) * μ), 0, μ) ∨ y = fpoint P Q R d (0, 0, 0) ∨
      y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (α, β, 0) ∨
      y = fpoint P Q R d (-(α * (1 - β6) * ν), β6, ν) ∨ y = fpoint P Q R d (0, 1, 0) ∨
      y = fpoint P Q R d (α - β * (α * (1 - β6)) * μ, 0, β * μ))
    (h0 : ⟪fpoint P Q R d (-(α * (1 - β6) * μ), 0, μ), R⟫ < ⟪fpoint P Q R d (-(α * (1 - β6) * ν), β6, ν), R⟫)
    (h1 : ⟪fpoint P Q R d (0, 0, 0), R⟫ < ⟪fpoint P Q R d (-(α * (1 - β6) * μ), 0, μ), R⟫)
    (h2 : ⟪fpoint P Q R d (1, 0, 0), R⟫ < ⟪fpoint P Q R d (0, 0, 0), R⟫ ∨
      ⟪fpoint P Q R d (1, 0, 0), R⟫ < ⟪fpoint P Q R d (α, β, 0), R⟫) :
    HasLexCellAt V R := by
  have hα0 : 0 < α := by linarith
  have hβ0 : 0 < β := by linarith
  refine cyc_cell V P Q R d hΔ (k := 5) (by norm_num) (k20R7Cyc α β β6 μ ν)
    (k20R7_inj hα0 hβ0 hb6 hμ hν) hmem [(0, (1 : ℝ), (0 : ℝ)), (α - β * (α * (1 - β6)) * μ, 0, β * μ)] ?_
    (u1 := -(α * ν)) (u2 := -1) (t1 := 1) (t2 := 0) (lo := 0) (hi := 1) (by norm_num)
    (by norm_num)
    (fun v1 v2 => v2 < 0 ∧ 0 < v1 - α * ν * v2) ?_ ?_ ?_
  · intro y hy
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inl ⟨2, rfl⟩
    · exact Or.inl ⟨3, rfl⟩
    · exact Or.inl ⟨4, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
  · intro lam h0' h1'
    refine ⟨by norm_num, ?_⟩
    nlinarith
  · intro v1 v2 ⟨hc1, hc2⟩
    exact k20R7_tsc hα hβ hb6 hb61 hγ6 hγ61 hσ hμ hν hνμ hνβ hb hc1 hc2
  · intro v1 v2 ⟨hc1, hc2⟩ hL
    refine k20_pent_uni3 _ _ hL ?_ ?_ ?_
    · left; simpa only [k20R7Cyc_0, k20R7Cyc_4] using h0
    · left; simpa only [k20R7Cyc_1, k20R7Cyc_0] using h1
    · simpa only [k20R7Cyc_2, k20R7Cyc_1, k20R7Cyc_3] using h2

end C2
end Type08Sp
end Minimality
