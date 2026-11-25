module

public import Minimality.Type24

@[expose] public section

/-!
# Outside `C̄` as one generic frame lemma

`isRupert_outsideCbar_frame`: a simple vertex `o` with neighbours `pa pb pc` such that every other
point lies in the oblique cone at `o` under the three side planes with ratios `wac wbc wab` is Rupert
unless `wac, wbc, wab > 0` and `Δ = wac wbc wab − wac − wbc − wab − 2 ≥ 0`.  If some ratio is `≤ 0`
the view `(1, ε, ε)` (weight 1 on that axis, `ε = 1/(2 + |wac| + |wbc| + |wab|)`) is the window view
(`isRupert_obliqueView_frame`); otherwise `Δ < 0` and Lemma CV (`isRupert_cornerView_frame`) applies.
`isRupert_type24_outside_Cbar''` is the type-24 corollary (same statement as
`isRupert_type24_outside_Cbar'`, one call).  Generic: no type-specific input.
-/

set_option autoImplicit false
open Finset
open scoped RealInnerProductSpace

namespace Minimality

/-- **Outside `C̄` in one frame lemma**: the whole outside-`C̄` argument in one frame lemma (window + corner view), for any simple
vertex `o` whose three neighbour pairs lie on side planes with shape ratios `wac wbc wab`. -/
theorem isRupert_outsideCbar_frame (V : Finset ℝ³) (o pa pb pc : ℝ³)
    (ha : pa ∈ V) (hb : pb ∈ V) (hc : pc ∈ V)
    (hD : vol3 (pa - o) (pb - o) (pc - o) ≠ 0) {wac wbc wab : ℝ}
    (hC : ¬ (0 < wac ∧ 0 < wbc ∧ 0 < wab ∧ 0 ≤ wac * wbc * wab - wac - wbc - wab - 2))
    (hV : ∀ v ∈ V, v ≠ pa → v ≠ pb → v ≠ pc → v = o ∨ ∃ A B C : ℝ,
      v = o + A • (pa - o) + B • (pb - o) + C • (pc - o) ∧ 0 < A ∧ 0 < B ∧
      0 < C ∧ B + C - wbc * A ≤ 1 ∧ A + C - wac * B ≤ 1 ∧ A + B - wab * C ≤ 1) :
    IsRupert V := by
  by_cases hω : wbc ≤ 0 ∨ wac ≤ 0 ∨ wab ≤ 0
  · -- window: weight 1 on the axis whose ratio is `≤ 0`, weight `ε` on the other two
    set ε := 1 / (2 + |wac| + |wbc| + |wab|) with hε
    have hε0 : 0 < ε := by positivity
    have hεs : ε * (2 + |wac| + |wbc| + |wab|) = 1 := by rw [hε]; field_simp
    have e1 : ε * wac < 1 := by nlinarith [le_abs_self wac, abs_nonneg wbc, abs_nonneg wab]
    have e2 : ε * wbc < 1 := by nlinarith [le_abs_self wbc, abs_nonneg wac, abs_nonneg wab]
    have e3 : ε * wab < 1 := by nlinarith [le_abs_self wab, abs_nonneg wac, abs_nonneg wbc]
    have key : ∀ {da db dc : ℝ}, 0 < da + db + dc → (∀ A B C : ℝ, 0 < A → 0 < B → 0 < C →
        B + C - wbc * A ≤ 1 → A + C - wac * B ≤ 1 → A + B - wab * C ≤ 1 →
        0 < A * (db + dc) + da * (1 - B - C) ∧ 0 < B * (da + dc) + db * (1 - A - C) ∧
        0 < C * (da + db) + dc * (1 - A - B)) → 0 < da → 0 < db → 0 < dc → IsRupert V := by
      intro da db dc hS hgen hda hdb hdc
      refine isRupert_obliqueView_frame V o pa pb pc ha hb hc hD hS ?_
      intro v hv h1 h2 h3
      rcases hV v hv h1 h2 h3 with rfl | ⟨A, B, C, rfl, hA, hB, hC', s1, s2, s3⟩
      · exact ⟨0, 0, 0, by simp, by linarith, by linarith, by linarith⟩
      · exact ⟨A, B, C, rfl, hgen A B C hA hB hC' s1 s2 s3⟩
    rcases hω with h | h | h
    · refine key (da := 1) (db := ε) (dc := ε) (by linarith) ?_ one_pos hε0 hε0
      intro A B C hA hB hC' s1 s2 s3
      refine ⟨by nlinarith [mul_nonpos_of_nonpos_of_nonneg h hA.le], ?_, ?_⟩
      · nlinarith [mul_pos hB (show 0 < 1 - ε * wac by linarith)]
      · nlinarith [mul_pos hC' (show 0 < 1 - ε * wab by linarith)]
    · refine key (da := ε) (db := 1) (dc := ε) (by linarith) ?_ hε0 one_pos hε0
      intro A B C hA hB hC' s1 s2 s3
      refine ⟨?_, by nlinarith [mul_nonpos_of_nonpos_of_nonneg h hB.le], ?_⟩
      · nlinarith [mul_pos hA (show 0 < 1 - ε * wbc by linarith)]
      · nlinarith [mul_pos hC' (show 0 < 1 - ε * wab by linarith)]
    · refine key (da := ε) (db := ε) (dc := 1) (by linarith) ?_ hε0 hε0 one_pos
      intro A B C hA hB hC' s1 s2 s3
      refine ⟨?_, ?_, by nlinarith [mul_nonpos_of_nonpos_of_nonneg h hC'.le]⟩
      · nlinarith [mul_pos hA (show 0 < 1 - ε * wbc by linarith)]
      · nlinarith [mul_pos hB (show 0 < 1 - ε * wac by linarith)]
  · push Not at hω
    obtain ⟨h1, h2, h3⟩ := hω
    have hΔ : wac * wbc * wab - wac - wbc - wab - 2 < 0 := by
      by_contra hn; exact hC ⟨h2, h1, h3, not_lt.mp hn⟩
    exact isRupert_cornerView_frame V o pa pb pc ha hb hc hD (by linarith) (by linarith)
      (by linarith) hΔ hV

/-- `isRupert_type24_outside_Cbar'` through the generic frame lemma `isRupert_outsideCbar_frame`. -/
theorem isRupert_type24_outside_Cbar'' {x : Fin 7 → ℝ³} (T : Type24 x)
    (hC : ¬ (0 < omega3 x ∧ 0 < omega4 x ∧ 0 < omega5 x ∧ 0 ≤ Delta24 x)) :
    IsRupert (univ.image x) := by
  have gen : ∀ v : Fin 7, v ≠ 0 → v ≠ 1 → v ≠ 2 → v ≠ 6 → ∃ A B C : ℝ,
      x v = x 1 + A • (x 0 - x 1) + B • (x 2 - x 1) + C • (x 6 - x 1) ∧ 0 < A ∧ 0 < B ∧
        0 < C ∧ B + C - omega3 x * A ≤ 1 ∧ A + C - omega4 x * B ≤ 1 ∧
        A + B - omega5 x * C ≤ 1 := by
    intro v h0 h1 h2 h6
    exact ⟨_, _, _, T.rep v, T.X0_pos (by simp [h1, h2, h6]), T.X2_pos (by simp [h0, h1, h6]),
      T.X6_pos (by simp [h0, h1, h2]), T.le236 v, T.le046 v, T.le025 v⟩
  refine isRupert_outsideCbar_frame (univ.image x) (x 1) (x 0) (x 2) (x 6) (Type24.mem 0)
    (Type24.mem 2) (Type24.mem 6) T.det_ne (wac := omega4 x) (wbc := omega3 x) (wab := omega5 x)
    (fun h => hC ⟨h.2.1, h.1, h.2.2.1, by unfold Delta24; linarith [h.2.2.2]⟩) ?_
  intro v hv h0 h2 h6
  obtain ⟨i, -, rfl⟩ := mem_image.mp hv
  rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl h0
  · exact Or.inl rfl
  · exact absurd rfl h2
  · exact Or.inr (gen 3 (by decide) (by decide) (by decide) (by decide))
  · exact Or.inr (gen 4 (by decide) (by decide) (by decide) (by decide))
  · exact Or.inr (gen 5 (by decide) (by decide) (by decide) (by decide))
  · exact absurd rfl h6

end Minimality
