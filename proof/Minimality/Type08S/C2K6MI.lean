module

public import Minimality.Type08S.C2K6MH

@[expose] public section

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2

/-- Coordinates (QN2): the K6M frame data from `Norm08w` and `ParEndN2`. -/
theorem k6m_coords_n2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hκ : det3 (c - b) (b' - b) (c' - b) = 0) (h : ParEndN2 a a' b b' c c') :
    ∃ α1 β1 β6 γ6 : ℝ, det3 (a - d) (b - d) (c - d) ≠ 0 ∧
      c' = d + α1 • (a - d) + β1 • (b - d) ∧ b' = d + α1 • (a - d) + β1 • (c - d) ∧
      a' = d + β6 • (b - d) + γ6 • (c - d) ∧
      0 < α1 ∧ 0 < β1 ∧ 1 < α1 + β1 ∧ 0 < β6 ∧ 0 < γ6 ∧ 1 < β6 + γ6 := by
  obtain ⟨α1, α4, β1, γ4, β6, γ6, hP0, hα, hγ, -⟩ := p0_n2_collpers W hκ h
  obtain ⟨hdet, hc', hb', ha', hα1, hβ1, h1, hα4, hγ4, h2, hβ6, hγ6, h3, -, -⟩ := hP0
  refine ⟨α1, β1, β6, γ6, hdet, hc', ?_, ha', hα1, hβ1, h1, hβ6, hγ6, h3⟩
  rw [hb', hα, hγ]

/-- DN2 at `α1 = 1`: the named codim-6 leftover. -/
def K6sDN2one (a a' b b' c c' d : ℝ³) : Prop :=
  det3 (c - b) (b' - b) (c' - b) = 0 ∧ ParEndN2 a a' b b' c c' ∧
    (K6sD1 a a' b b' c c' d ∨ K6sD2 a a' b b' c c' d) ∧
    ∃ β1 : ℝ, c' = d + (1:ℝ) • (a - d) + β1 • (b - d)

/-- **DN2 wrapper**: `α1 < 1` closed by box B; the leftover is `α1 = 1`. -/
theorem k6m_dn2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hs : K6sDN2 a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K6sDN2one a a' b b' c c' d := by
  obtain ⟨hκ, h, hD, α, β, hc2, hα⟩ := hs
  obtain ⟨α1, β1, β6, γ6, hdet, hc', hb', ha', hα1, hβ1, h1, hβ6, hγ6, h3⟩ := k6m_coords_n2 W hκ h
  have hu := k5b_coeff3 hdet (x := α1) (y := β1) (z := 0) (x' := α) (y' := β) (z' := 0)
    (by have := hc'.symm.trans hc2; simpa [add_assoc] using this)
  obtain ⟨rfl, rfl, -⟩ := hu
  rcases lt_or_eq_of_le hα with hlt | heq
  · exact Or.inl (k6m_B_hasLexCell W hdet hc' hb' ha' hα1 hβ1 h1 hβ6 hγ6 hlt)
  · right
    refine ⟨hκ, h, hD, β1, ?_⟩
    rw [hc', heq]

end C2
end Type08Sp
end Minimality
