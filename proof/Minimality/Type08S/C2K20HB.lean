module

public import Minimality.Type08S.C2K20HA

@[expose] public section


/-!
# K20H5 / B: H5 rule r3: frame lemma and `k20_r3_hasLexCell`
Rule `⟪b' - a, v⟫ > 0` with `v = α1 (a - d) - (β6 + γ6 - β1)(c - d)`; no Coll5 relation, no chirality hypothesis.
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
theorem k20_r3_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {α β β6 w κ : ℝ}
    (hα : 1 < α) (hβ : 1 < β) (hb6 : 0 < β6) (hb61 : β6 < 1) (hκ : 0 < κ) (hw : w = κ * (β - β6) + 1)
    (hmem : ∀ i, fpoint P Q R d (k20R3Cyc α β κ i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, 0) ∨
      y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (α * (1 + β * κ), 0, -(β * κ)) ∨
      y = fpoint P Q R d (α, β, 0) ∨ y = fpoint P Q R d (α * κ, 0, -κ) ∨
      y = fpoint P Q R d (α * w, β6, -w))
    (h12 : ⟪fpoint P Q R d (0, 0, 0), R⟫ < ⟪fpoint P Q R d (1, 0, 0), R⟫)
    (h23 : ⟪fpoint P Q R d (1, 0, 0), R⟫ < ⟪fpoint P Q R d (α * (1 + β * κ), 0, -(β * κ)), R⟫)
    (h34 : ⟪fpoint P Q R d (α * (1 + β * κ), 0, -(β * κ)), R⟫ < ⟪fpoint P Q R d (α, β, 0), R⟫) :
    HasLexCellAt V R := by
  have hα0 : 0 < α := by linarith
  have hβ0 : 0 < β := by linarith
  refine cyc_cell V P Q R d hΔ (k := 5) (by norm_num) (k20R3Cyc α β κ)
    (k20R3_inj hα0 hβ0 hκ) hmem [(α * κ, (0 : ℝ), -κ), (α * w, β6, -w)] ?_
    (u1 := -(α * κ)) (u2 := 1) (t1 := -1) (t2 := 0) (lo := 0) (hi := 1) (by norm_num)
    (by norm_num)
    (fun v1 v2 => 0 < v2 ∧ v1 + α * κ * v2 < 0) ?_ ?_ ?_
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
    refine ⟨by norm_num, ?_⟩
    nlinarith
  · intro v1 v2 ⟨hc1, hc2⟩
    exact k20R3_tsc hα hβ hb6 hb61 hκ hw hc1 hc2
  · intro v1 v2 ⟨hc1, hc2⟩ hL
    refine k16_pent_uni_r2 _ _ hL ?_ ?_ ?_
    · simpa only [k20R3Cyc_1, k20R3Cyc_2] using h12
    · simpa only [k20R3Cyc_2, k20R3Cyc_3] using h23
    · intro h _
      have := h34
      simp only [k20R3Cyc_3, k20R3Cyc_4] at h
      linarith

end C2
end Type08Sp
end Minimality
