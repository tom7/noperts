module

public import Minimality.Type08S.C2K6PJ

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2

/-- Leftover of QN2 for the D strata when `α1 ≤ 1` (the lex D cells need `α1 > 1`): `c' = d + α1 (a-d) + β1 (b-d)`. -/
def K6sDN2 (a a' b b' c c' d : ℝ³) : Prop :=
  det3 (c - b) (b' - b) (c' - b) = 0 ∧ ParEndN2 a a' b b' c c' ∧
    (K6sD1 a a' b b' c c' d ∨ K6sD2 a a' b b' c c' d) ∧
    ∃ α1 β1 : ℝ, c' = d + α1 • (a - d) + β1 • (b - d) ∧ α1 ≤ 1

set_option maxHeartbeats 3200000 in
/-- **QN2 on the tie slice** (S2): the tree of `k5b_qn2_hasLexCell` with weakened leaves N2, N1, N4 and the
`ρ_a = 0` stratum split; leftovers `M`, `D1`, `D2`. -/
theorem k6p_qn2_final {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hs : K5ZsN2 a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K6sMN2 a a' b b' c c' d ∨ K6sDN2 a a' b b' c c' d := by
  obtain ⟨hκ, h, -⟩ := hs
  obtain ⟨α1, α4, β1, γ4, β6, γ6, hP0, hα, hγ, e1, e2, e3, κ, hF, hκ0, hxe, hbe2, hL, hY, hYY, hcoll, hpers⟩ :=
    p0_n2_collpers W hκ h
  obtain ⟨hdet, hc', hb', ha', hα1, hβ1, h1, hα4, hγ4, h2, hβ6, hγ6, h3, hfa, hfb⟩ := hP0
  have hb1 : b' = d + α1 • (a - d) + β1 • (c - d) := by rw [hb', hα, hγ]
  have hbc : b' = c' - β1 • (b - c) := by rw [hb1, hc']; module
  obtain ⟨t, ht1, ht2, hrel0, hR⟩ := k5b_n2_rel (a := a) (α1 := α1) hβ1 hbc hF hxe hbe2 hL hcoll hpers
  obtain ⟨l1, l2, -, -, l5⟩ := k5b_lits hc' hb1
  rw [l5] at hrel0
  have hcond := k5b_cond1 W hdet hc' hb1 ha' hβ1
  have c1 := fun hex => k5b_use_cell1 hdet hc' hb1 ha' hα1 hβ1 hβ6 hγ6 h3 h1 hcond hex
  have c2 := fun hex => k5b_use_cell2 hdet hc' hb1 ha' hα1 hβ1 hβ6 hγ6 h3 h1 hcond hex
  rcases lt_trichotomy ⟪a - d, b - c⟫ 0 with hA | hA | hA
  · rcases lt_or_ge (α1 * ⟪a - d, b - c⟫ + β1 * ⟪c - d, b - c⟫) 0 with hB | hB
    · exact Or.inl (c1 (k5b_leaf_N3 hα1 hβ1 hβ6 hγ6 h3 h1 hcond hR ht1 ht2 hrel0 hA hB))
    · exact Or.inl (c2 (k6p_leaf_N4w hα1 hβ1 hβ6 hγ6 h3 h1 hcond hR ht1 ht2 hrel0 hA hB))
  · rcases lt_trichotomy (α1 * ⟪a - d, b - c⟫ + β1 * ⟪c - d, b - c⟫ + β1 * ⟪b - c, b - c⟫) 0 with hC | hC | hC
    · exact Or.inl (c1 (k6p_leaf_N2w hα1 hβ1 hβ6 hγ6 h3 h1 hcond hR ht1 ht2 hrel0 hA.symm.le hC.le (Or.inr hC)))
    · rcases lt_or_ge 1 α1 with hα11 | hα11
      · left
        have e : β1 * (⟪c - d, b - c⟫ + ⟪b - c, b - c⟫) = 0 := by rw [hA] at hC; linarith
        have hy : ⟪c - d, b - c⟫ = -⟪b - c, b - c⟫ := by
          rcases mul_eq_zero.mp e with h | h
          · exact absurd h hβ1.ne'
          · linarith
        exact k6p_D1_hasLexCell hdet hc' hb1 ha' hα11 hβ1 hβ6 hγ6 h3 h1 hcond hA hy
      · right; right
        refine ⟨hκ, h, Or.inl ⟨hA, ?_⟩, α1, β1, hc', hα11⟩
        rw [l1]; exact hC
    · rcases lt_trichotomy (α1 * ⟪a - d, b - c⟫ + β1 * ⟪c - d, b - c⟫) 0 with hB | hB | hB
      · right; left
        refine ⟨hκ, h, hA, ?_, ?_⟩
        · rw [l1]; exact hC
        · rw [l2]; exact hB
      · rcases lt_or_ge 1 α1 with hα11 | hα11
        · left
          have e : β1 * ⟪c - d, b - c⟫ = 0 := by rw [hA] at hB; linarith
          have hy : ⟪c - d, b - c⟫ = 0 := by
            rcases mul_eq_zero.mp e with h | h
            · exact absurd h hβ1.ne'
            · exact h
          exact k6p_D2_hasLexCell hdet hc' hb1 ha' hα11 hβ1 hβ6 hγ6 h3 h1 hcond hA hy
        · right; right
          refine ⟨hκ, h, Or.inr ⟨hA, ?_, ?_⟩, α1, β1, hc', hα11⟩
          · rw [l2]; exact hB
          · rw [l1]; exact hC
      · exact Or.inl (c2 (k6p_leaf_N1w hα1 hβ1 hβ6 hγ6 h3 h1 hcond hR ht1 ht2 hrel0 hA.symm.le hC (Or.inr hB)))
  · rcases lt_or_ge 0 (α1 * ⟪a - d, b - c⟫ + β1 * ⟪c - d, b - c⟫ + β1 * ⟪b - c, b - c⟫) with hC | hC
    · exact Or.inl (c2 (k6p_leaf_N1w hα1 hβ1 hβ6 hγ6 h3 h1 hcond hR ht1 ht2 hrel0 hA.le hC (Or.inl hA)))
    · exact Or.inl (c1 (k6p_leaf_N2w hα1 hβ1 hβ6 hγ6 h3 h1 hcond hR ht1 ht2 hrel0 hA.le hC (Or.inl hA)))


end C2
end Type08Sp
end Minimality
