module

public import Minimality.Type08S.C2K6TCB

@[expose] public section

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

theorem k6t3_c1_tt5b_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {α4 γ4 β1 β6 γ6 : ℝ}
    (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hs : 1 < α4 + γ4) (hβ1 : 0 < β1) (hb6 : 0 < β6) (hγ6 : 0 < γ6)
    (hg6 : γ6 = 1) (hγ41 : γ4 ≤ 1)
    (htie : α4 * ⟪P, R⟫ + γ4 * ⟪Q, R⟫ = ⟪Q, R⟫ - β6 * ⟪R, R⟫)
    (hζ : α4 * ⟪P, R⟫ + γ4 * ⟪Q, R⟫ < ⟪P, R⟫)
    (hF : α4 * (1 - β1) + γ4 * (1 - β6) < 1)
    (hmem : ∀ i, fpoint P Q R d (k5dX1 α4 γ4 β1 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨
      y = fpoint P Q R d (α4, γ4, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, -1) ∨
      y = fpoint P Q R d (1, 0, -β1) ∨ y = fpoint P Q R d (0, γ6, -β6)) :
    HasLexCellAt V R := by
  have hA := k5d_hA hΔ
  refine k5d_c1_core V P Q R d hΔ hα4 hγ4 hs hβ1 hb6 hγ6 (Or.inr hg6) hmem hVall ?_
  intro k0 U T B hfw hinj
  have hB : 0 < B := by
    have := hfw (0, 0, -1) (by simp [k5dL]) (0, 0, 0) (by simp [k5dL]) (by dsimp only; linarith)
    dsimp only at this; linarith
  exact k6t3_c1_tt5b_real (u := ⟪P, R⟫) (t := ⟪Q, R⟫) (A := ⟪R, R⟫) hα4 hγ4 hs hβ1 hb6 hγ41 hA hB htie hζ hF
    (k6t2_hdep (fun i => by simpa using k5dX1_mem α4 γ4 β1 β6 γ6 i) hfw) hinj

/-- **TT 5b, `γ4 ≤ 1`, `ζ(a,b') > 0`** (the part left over by `k6t2_TT`): the pentagon `(c',b',c,d,b)` at `d - b`.
The depth model alone is not enough; the facet `a'bc'` (`k6t3_facet_a'bc'`) supplies `α4(1-β1) + γ4(1-β6) < 1`. -/
theorem k6t3_tt5b_le {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT : IsT a' b c d)
    (hT' : IsT' a b c' d) (hζ2 : ⟪b' - a', d - b⟫ = 0) (hζ1 : 0 < ⟪a - b', d - b⟫)
    (hg : det3 (a - d) (b - d) (b' - c) * det3 (a - d) (b - d) (c - d) ≤ 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hΔ, hβ1, hα4p, hγ4, hαγ, hβ6, hγ6, hγ6s, hfar', hc', hb', ha',
    hmem7, hVall⟩ := k5d_setup W hT'
  have hg6 : γ6 = 1 := isT_gamma6 hdet ha' hT
  have hz2 : ⟪b' - a', d - b⟫ = (α4 * ⟪a - d, d - b⟫ + γ4 * ⟪c - d, d - b⟫) -
      (γ6 * ⟪c - d, d - b⟫ - β6 * ⟪d - b, d - b⟫) := by
    rw [hb', ha']; simp only [inner_sub_left, inner_add_left, real_inner_smul_left]; ring
  have hz1 : ⟪a - b', d - b⟫ = ⟪a - d, d - b⟫ - (α4 * ⟪a - d, d - b⟫ + γ4 * ⟪c - d, d - b⟫) := by
    rw [hb']; simp only [inner_sub_left, inner_add_left, real_inner_smul_left]; ring
  rw [k6t2_det_gamma4 hb'] at hg
  have hγ41 : γ4 ≤ 1 := by
    have : 0 < det3 (a - d) (b - d) (c - d) ^ 2 := by positivity
    nlinarith
  have hF0 := k6t3_facet_a'bc' W hc' hb' ha' hβ1 hγ6 hγ6s
  rw [hg6] at hF0
  have hF : α4 * (1 - β1) + γ4 * (1 - β6) < 1 := by nlinarith
  have hmemX : ∀ {n : ℕ} {X : ZMod n → ℝ × ℝ × ℝ}, (∀ i, X i ∈ k5dL α4 γ4 β1 β6 γ6) →
      ∀ i, fpoint (a - d) (c - d) (d - b) d (X i) ∈ V8 a a' b b' c c' d :=
    fun h i => hmem7 _ (h i)
  refine ⟨d - b, k5d_R_ne hΔ, ?_⟩
  rw [hg6] at hz2
  exact k6t3_c1_tt5b_frame _ _ _ _ _ hΔ hα4p hγ4 hαγ hβ1 hβ6 hγ6 hg6 hγ41 (by linarith) (by linarith) hF
    (hmemX (k5dX1_mem α4 γ4 β1 β6 γ6)) hVall

end C2
end Type08Sp
end Minimality
