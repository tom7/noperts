module

public import Minimality.Type08S.C2K6PC

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2

/-- Double-tie stratum D1: `ρ_a = 0` and `ζ(c',d) = 0` (view `b - c`). -/
def K6sD1 (a a' b b' c c' d : ℝ³) : Prop :=
  ⟪a - d, b - c⟫ = 0 ∧ ⟪c' - d, b - c⟫ = 0

/-- Double-tie stratum D2: `ρ_a = 0`, `ζ(b',d) = 0 < ζ(c',d)`. -/
def K6sD2 (a a' b b' c c' d : ℝ³) : Prop :=
  ⟪a - d, b - c⟫ = 0 ∧ ⟪b' - d, b - c⟫ = 0 ∧ 0 < ⟪c' - d, b - c⟫

set_option maxHeartbeats 3200000 in
/-- **QCEb on the tie slice** (S3): the tree of `k5b_qceb_hasLexCell` with the leaves K1, K4 weakened and the
`ρ_a = 0` stratum split; leftovers `M`, `D1`, `D2` (the latter two to be closed by the lex variants). -/
theorem k6p_qceb_w {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hfar1 : W.F.abc'.f c < W.F.abc'.f a') (hfar2 : W.F.a'bc.f c' < W.F.a'bc.f a)
    (hs : K5ZsCEb W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K6sMKb a a' b b' c c' d ∨ K6sD1 a a' b b' c c' d ∨
      K6sD2 a a' b b' c c' d := by
  obtain ⟨-, hκ, h, -⟩ := hs
  obtain ⟨α1, α4, β1, γ4, β6, γ6, hP0, hα, hγ, e1, e2, e3, κ, hF, hκ0, hxe, hce2, hL, hY, hYY, hcoll, hpers⟩ :=
    p0_kb_collpers W hκ h
  obtain ⟨hdet, hc', hb', ha', hα1, hβ1, h1, hα4, hγ4, h2, hβ6, hγ6, h3, hfa, hfb⟩ := hP0
  have hb1 : b' = d + α1 • (a - d) + β1 • (c - d) := by rw [hb', hα, hγ]
  have hγ61 : γ6 < 1 := hfa hfar1
  have hα11 : 1 < α1 := hfb hfar2
  obtain ⟨t, ht1, ht2, hrel0, hR⟩ := k5b_kb_rel (a := a) hβ1 hb1 hc' hF hxe hce2 hL hcoll hpers
  obtain ⟨l1, l2, l3, l4, l5⟩ := k5b_lits hc' hb1
  rw [l5] at hrel0
  have hcond : 0 < (α1 - 1) * (β6 + γ6) + β1 := by nlinarith
  have hab : 1 < α1 + β1 := h1
  have c1 := fun hex => k5b_use_cell1 hdet hc' hb1 ha' hα1 hβ1 hβ6 hγ6 h3 h1 hcond hex
  have c2 := fun hex => k5b_use_cell2 hdet hc' hb1 ha' hα1 hβ1 hβ6 hγ6 h3 h1 hcond hex
  rcases le_or_gt (α1 * ⟪a - d, b - c⟫ + β1 * ⟪c - d, b - c⟫ + β1 * ⟪b - c, b - c⟫) ⟪a - d, b - c⟫ with hC | hC
  · by_cases hD : α1 * ⟪a - d, b - c⟫ + β1 * ⟪c - d, b - c⟫ + β1 * ⟪b - c, b - c⟫ < ⟪a - d, b - c⟫ ∨
        ⟪a - d, b - c⟫ ≠ 0
    · exact Or.inl (c1 (k6p_leaf_K1w hα11 hβ1 hβ6 hγ6 hγ61 h3 hR ht1 ht2 hrel0 hC hD))
    · push Not at hD
      right; right; left
      refine ⟨hD.2, ?_⟩
      rw [l1]; linarith [hD.1, hD.2]
  · have hlt : ⟪a - d, b - c⟫ < α1 * ⟪a - d, b - c⟫ + β1 * ⟪c - d, b - c⟫ + β1 * ⟪b - c, b - c⟫ := hC
    rcases lt_trichotomy ⟪a - d, b - c⟫ 0 with hA | hA | hA
    · rcases lt_or_ge (α1 * ⟪a - d, b - c⟫ + β1 * ⟪c - d, b - c⟫) ⟪a - d, b - c⟫ with hB | hB
      · exact Or.inl (c1 (k5b_leaf_K3 hα11 hβ1 hβ6 hγ6 hγ61 h3 hR ht1 ht2 hrel0 hlt hA hB))
      · exact Or.inl (c2 (k6p_leaf_K4w hα11 hβ1 hβ6 hγ6 hγ61 h3 hR ht1 ht2 hrel0 hlt hA hB))
    · rcases lt_trichotomy (α1 * ⟪a - d, b - c⟫ + β1 * ⟪c - d, b - c⟫) 0 with hB | hB | hB
      · right; left
        refine ⟨hκ, h, hA, ?_, ?_⟩
        · rw [l1]; linarith
        · rw [l2]; exact hB
      · right; right; right
        refine ⟨hA, ?_, ?_⟩
        · rw [l2]; exact hB
        · rw [l1]; linarith
      · exact Or.inl (c2 (k6p_leaf_N1w hα1 hβ1 hβ6 hγ6 h3 h1 hcond hR ht1 ht2 hrel0 hA.symm.le
          (by linarith) (Or.inr hB)))
    · exact Or.inl (c2 (k6p_leaf_N1w hα1 hβ1 hβ6 hγ6 h3 h1 hcond hR ht1 ht2 hrel0 hA.le
        (by linarith) (Or.inl hA)))

end C2
end Type08Sp
end Minimality
