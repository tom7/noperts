module

public import Minimality.Type08S.C2K5BH

@[expose] public section


/-!
# K5b / I: the wrappers `k5b_qn2_hasLexCell` (QN2 = `ParEndN2`) and `k5b_qceb_hasLexCell` (QCEb = `ParEndKb`).
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- The depth literals of the trees in coordinates (`r = b - c`). -/
theorem k5b_lits {a b b' c c' d : ℝ³} {α1 β1 : ℝ}
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d)) :
    ⟪c' - d, b - c⟫ = α1 * ⟪a - d, b - c⟫ + β1 * ⟪c - d, b - c⟫ + β1 * ⟪b - c, b - c⟫ ∧
    ⟪b' - d, b - c⟫ = α1 * ⟪a - d, b - c⟫ + β1 * ⟪c - d, b - c⟫ ∧
    ⟪a - c', b - c⟫ = ⟪a - d, b - c⟫ - (α1 * ⟪a - d, b - c⟫ + β1 * ⟪c - d, b - c⟫ + β1 * ⟪b - c, b - c⟫) ∧
    ⟪a - b', b - c⟫ = ⟪a - d, b - c⟫ - (α1 * ⟪a - d, b - c⟫ + β1 * ⟪c - d, b - c⟫) ∧
    ⟪b' - c, b - c⟫ = α1 * ⟪a - d, b - c⟫ + (β1 - 1) * ⟪c - d, b - c⟫ := by
  have e1 : c' - d = α1 • (a - d) + β1 • (c - d) + β1 • (b - c) := by rw [hc']; module
  have e2 : b' - d = α1 • (a - d) + β1 • (c - d) := by rw [hb']; module
  have e3 : a - c' = (1 - α1) • (a - d) - β1 • (c - d) - β1 • (b - c) := by rw [hc']; module
  have e4 : a - b' = (1 - α1) • (a - d) - β1 • (c - d) := by rw [hb']; module
  have e5 : b' - c = α1 • (a - d) + (β1 - 1) • (c - d) := by rw [hb']; module
  simp only [e1, e2, e3, e4, e5, inner_add_left, inner_sub_left, inner_smul_left, RCLike.conj_to_real]
  refine ⟨trivial, trivial, ?_, ?_, trivial⟩ <;> ring

set_option maxHeartbeats 3200000 in
/-- **QN2.**  `ParEndN2` (planar, `κ_a = 0`) is closed by a lex cell at `b - c`; tree: `ρ_a = ⟪a-d, b-c⟫` and one of
`⟪c'-d, b-c⟫` (when `ρ_a > 0`) or `⟪b'-d, b-c⟫` (when `ρ_a < 0`); all three literals are leftovers when `0`. -/
theorem k5b_qn2_hasLexCell {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hκ : det3 (c - b) (b' - b) (c' - b) = 0) (h : ParEndN2 a a' b b' c c')
    (hρ : ⟪a - d, b - c⟫ ≠ 0) (hζc' : ⟪c' - d, b - c⟫ ≠ 0) (hζb' : ⟪b' - d, b - c⟫ ≠ 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨α1, α4, β1, γ4, β6, γ6, hP0, hα, hγ, e1, e2, e3, κ, hF, hκ0, hxe, hbe2, hL, hY, hYY, hcoll, hpers⟩ :=
    p0_n2_collpers W hκ h
  obtain ⟨hdet, hc', hb', ha', hα1, hβ1, h1, hα4, hγ4, h2, hβ6, hγ6, h3, hfa, hfb⟩ := hP0
  have hb1 : b' = d + α1 • (a - d) + β1 • (c - d) := by rw [hb', hα, hγ]
  have hbc : b' = c' - β1 • (b - c) := by rw [hb1, hc']; module
  obtain ⟨t, ht1, ht2, hrel0, hR⟩ := k5b_n2_rel (a := a) (α1 := α1) hβ1 hbc hF hxe hbe2 hL hcoll hpers
  obtain ⟨l1, l2, -, -, l5⟩ := k5b_lits hc' hb1
  rw [l5] at hrel0
  have hcond := k5b_cond1 W hdet hc' hb1 ha' hβ1
  rw [l1] at hζc'
  rw [l2] at hζb'
  rcases lt_or_gt_of_ne hρ with hA | hA
  · rcases lt_or_gt_of_ne hζb' with hB | hB
    · exact k5b_use_cell1 hdet hc' hb1 ha' hα1 hβ1 hβ6 hγ6 h3 h1 hcond
        (k5b_leaf_N3 hα1 hβ1 hβ6 hγ6 h3 h1 hcond hR ht1 ht2 hrel0 hA hB)
    · exact k5b_use_cell2 hdet hc' hb1 ha' hα1 hβ1 hβ6 hγ6 h3 h1 hcond
        (k5b_leaf_N4 hα1 hβ1 hβ6 hγ6 h3 h1 hcond hR ht1 ht2 hrel0 hA hB)
  · rcases lt_or_gt_of_ne hζc' with hC | hC
    · exact k5b_use_cell1 hdet hc' hb1 ha' hα1 hβ1 hβ6 hγ6 h3 h1 hcond
        (k5b_leaf_N2 hα1 hβ1 hβ6 hγ6 h3 h1 hcond hR ht1 ht2 hrel0 hA hC)
    · exact k5b_use_cell2 hdet hc' hb1 ha' hα1 hβ1 hβ6 hγ6 h3 h1 hcond
        (k5b_leaf_N1 hα1 hβ1 hβ6 hγ6 h3 h1 hcond hR ht1 ht2 hrel0 hA hC)

set_option maxHeartbeats 3200000 in
/-- **QCEb.**  `ParEndKb` (planar, `κ_a = 0`, `T4`-type far ends) is closed by a lex cell at `b - c`; tree: `ζ(a,c')`,
then `ρ_a`, then `ζ(a,b')` (when `ρ_a < 0`); the three literals are leftovers when `0`. -/
theorem k5b_qceb_hasLexCell {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hκ : det3 (c - b) (b' - b) (c' - b) = 0) (h : ParEndKb b b' c c' d)
    (hfar1 : W.F.abc'.f c < W.F.abc'.f a') (hfar2 : W.F.a'bc.f c' < W.F.a'bc.f a)
    (hζc' : ⟪a - c', b - c⟫ ≠ 0) (hρ : ⟪a - d, b - c⟫ ≠ 0) (hζb' : ⟪a - b', b - c⟫ ≠ 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨α1, α4, β1, γ4, β6, γ6, hP0, hα, hγ, e1, e2, e3, κ, hF, hκ0, hxe, hce2, hL, hY, hYY, hcoll, hpers⟩ :=
    p0_kb_collpers W hκ h
  obtain ⟨hdet, hc', hb', ha', hα1, hβ1, h1, hα4, hγ4, h2, hβ6, hγ6, h3, hfa, hfb⟩ := hP0
  have hb1 : b' = d + α1 • (a - d) + β1 • (c - d) := by rw [hb', hα, hγ]
  have hγ61 : γ6 < 1 := hfa hfar1
  have hα11 : 1 < α1 := hfb hfar2
  obtain ⟨t, ht1, ht2, hrel0, hR⟩ := k5b_kb_rel (a := a) hβ1 hb1 hc' hF hxe hce2 hL hcoll hpers
  obtain ⟨-, -, l3, l4, l5⟩ := k5b_lits hc' hb1
  rw [l5] at hrel0
  have hcond : 0 < (α1 - 1) * (β6 + γ6) + β1 := by nlinarith
  rw [l3] at hζc'
  rw [l4] at hζb'
  rcases lt_or_gt_of_ne hζc' with hC | hC
  · -- `ζ(a,c') < 0`
    rcases lt_or_gt_of_ne hρ with hA | hA
    · rcases lt_or_gt_of_ne hζb' with hB | hB
      · exact k5b_use_cell2 hdet hc' hb1 ha' hα1 hβ1 hβ6 hγ6 h3 h1 hcond
          (k5b_leaf_K4 hα11 hβ1 hβ6 hγ6 hγ61 h3 hR ht1 ht2 hrel0 (by linarith) hA (by linarith))
      · exact k5b_use_cell1 hdet hc' hb1 ha' hα1 hβ1 hβ6 hγ6 h3 h1 hcond
          (k5b_leaf_K3 hα11 hβ1 hβ6 hγ6 hγ61 h3 hR ht1 ht2 hrel0 (by linarith) hA (by linarith))
    · exact k5b_use_cell2 hdet hc' hb1 ha' hα1 hβ1 hβ6 hγ6 h3 h1 hcond
        (k5b_leaf_K2 hα11 hβ1 hβ6 hγ6 hγ61 h3 hR ht1 ht2 hrel0 (by linarith) hA)
  · exact k5b_use_cell1 hdet hc' hb1 ha' hα1 hβ1 hβ6 hγ6 h3 h1 hcond
      (k5b_leaf_K1 hα11 hβ1 hβ6 hγ6 hγ61 h3 hR ht1 ht2 hrel0 (by linarith))

end C2
end Type08Sp
end Minimality
