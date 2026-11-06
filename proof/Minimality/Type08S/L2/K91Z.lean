module

public import Minimality.Type08S.L2.K86F
public import Minimality.Type08S.L2.K91F
public import Minimality.Type08S.L2.K86Lexc1c
public import Minimality.Type08S.L2.K86LexcD
public import Minimality.Type08S.L2.K86LexcAp
public import Minimality.Type08S.L2.K86LexcC

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace
namespace Minimality.Type08Sp.C2

set_option maxHeartbeats 6400000 in
/-- Combiner (no numerics-only facts) of the type 08 `U0 = 0` branch (corner C1).  `W = (b-d) + lam (a-d)`, `lam Av = -Bv`;
`ν Bc = β1 A`.  The `f*` hypotheses are side facts (chart of the U0 branch); they are numerics-only at this stage. -/
theorem k91_c1 {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 lam ν : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hU0 : k28l2aU0 a b c d α1 β1 = 0)
    (hα : 1 < α1) (hβ : 1 < β1) (hb6 : 1 < β6) (hg6 : 1 < γ6) (hσ : β1 < β6 + γ6)
    (hgW : 0 ≤ β6 * (α1 - 1) - β1 * (γ6 - 1))
    (hlamdef : lam * ⟪a - d, a' - b'⟫ = -⟪b - d, a' - b'⟫)
    (hνdef : ν * ⟪a - a', a - d⟫ = β1 * (-⟪a - a', c - d⟫))
    (hH : 0 ≤ ⟪c' - a', b' - c⟫)
    :
    HasLexCell (V8 a a' b b' c c' d) ∨
      (β6 * (α1 - 1) - β1 * (γ6 - 1) = 0 ∧ ⟪a' - b, (b - d) + lam • (a - d)⟫ = 0 ∧
        0 < α1 - (β1 - 1) * lam) := by
  obtain ⟨fAv, flam, fac, fpq, fU1, fU2, fzA, fzB, fAB, fCb, fB, fn⟩ :=
    k86_facts hC hM hrel hα hβ hb6 hg6 hσ hU0 hlamdef
  obtain ⟨gnu, glit, gdA, gdC, gdP, gtAC, gQ2⟩ :=
    k91_facts hC hM hrel hα hβ hb6 hg6 hσ hU0 hlamdef hνdef hH
  have hCC := hC
  have hc' := hC.2.1
  set W : ℝ³ := (b - d) + lam • (a - d) with hW
  by_cases hg : 0 < β6 * (α1 - 1) - β1 * (γ6 - 1)
  · left
    have hβ0 : β1 ≠ 0 := by linarith
    refine k86_c1c hCC rfl hα hβ gnu glit (by linarith) hb6 hg6 hσ gdA gdC (gdP hg)
      gtAC ?_ fB fn
    have h0 : ⟪a - a', (c - d) + (ν / β1) • (a - d)⟫ = 0 := by
      rw [inner_add_right, inner_smul_right]
      have : ν / β1 * ⟪a - a', a - d⟫ = -⟪a - a', c - d⟫ := by
        field_simp; linarith
      linarith
    rw [inner_sub_left] at h0; linarith
  · have hg0 : β6 * (α1 - 1) - β1 * (γ6 - 1) = 0 := le_antisymm (not_lt.1 hg) hgW
    have tBA : ⟪a', W⟫ = ⟪b', W⟫ := by
      have : ⟪a' - b', W⟫ = 0 := by
        rw [hW, inner_add_right, inner_smul_right, real_inner_comm (b - d) (a' - b'),
          real_inner_comm (a - d) (a' - b')]
        linarith
      rw [inner_sub_left] at this; linarith
    have tAB : ⟪b', W⟫ = ⟪a, W⟫ := by rw [inner_sub_left] at fAB; linarith
    have eA : ⟪a, W⟫ = ⟪d, W⟫ + ⟪a - d, W⟫ := by rw [← inner_add_left]; congr 1; abel
    have eB : ⟪b, W⟫ = ⟪d, W⟫ + ⟪b - d, W⟫ := by rw [← inner_add_left]; congr 1; abel
    have ec' : ⟪c', W⟫ = ⟪a, W⟫ + (α1 - 1) * ⟪a - d, W⟫ + β1 * ⟪b - d, W⟫ := by
      have : c' - a = (α1 - 1) • (a - d) + β1 • (b - d) := by rw [hc']; module
      have h2 : ⟪c' - a, W⟫ = (α1 - 1) * ⟪a - d, W⟫ + β1 * ⟪b - d, W⟫ := by
        rw [this, inner_add_left, inner_smul_left, inner_smul_left]; simp
      rw [inner_sub_left] at h2; linarith
    have hcb' : (α1 ≤ (β1 - 1) * lam) ∨ (β1 - 1) * lam < α1 := le_or_gt _ _
    rcases hcb' with hcb | hcb
    · left
      refine k86_cC hCC (by rw [one_smul]) hα hβ hb6 flam hg6 hσ fac hcb fpq fU1 fU2 fAv (gQ2 hg0 hcb) ?_ ?_ ?_ ?_
      ·
        have : ⟪c' - a', W⟫ = ⟪c' - b', W⟫ := by
          rw [inner_sub_left, inner_sub_left, tBA]
        rw [inner_sub_left] at this fCb; linarith
      · nlinarith [eA, ec']
      · exact tAB
      · exact tBA
    · have hcbp : 0 < α1 - (β1 - 1) * lam := by linarith
      rcases lt_trichotomy (⟪a' - b, W⟫) 0 with hz | hz | hz
      · left
        refine k86_cAp hCC (by rw [one_smul]) hα hβ hb6 flam hg6 hσ fac hcb fpq fU1 fU2 fAv ?_ ?_ ?_ ?_ ?_
        · nlinarith [eB, ec', fzA, fzB]
        · nlinarith [eA, ec', fzA, fzB]
        · exact tAB
        · exact tBA
        · rw [inner_sub_left] at hz; linarith
      · right; exact ⟨hg0, hz, hcbp⟩
      · left
        have hneg : ∀ x : ℝ³, ⟪x, (-1 : ℝ) • W⟫ = -⟪x, W⟫ := fun x => by
          rw [inner_smul_right]; ring
        refine k86_cD hCC rfl hα hβ hb6 flam hg6 hσ fac hcb fpq fU1 fU2 fAv ?_ ?_ ?_ ?_ ?_
        · rw [hneg, hneg]; linarith
        · rw [hneg, hneg]; linarith
        · rw [hneg, hneg]; exact congrArg Neg.neg tAB
        · rw [hneg, hneg]; exact congrArg Neg.neg tBA
        · rw [hneg, hneg]; rw [inner_sub_left] at hz; linarith
end Minimality.Type08Sp.C2
