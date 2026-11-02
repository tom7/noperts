module

public import Minimality.Type08S.C2K17CO

@[expose] public section


/-!
# K17C / P3P: composition for the `β1 = 1` piece of `K6mBoundary` (as it appears in `K16LeftMN2 W` / `K16LeftMKb W`).
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

/-- The leftover of the `β1 = 1` piece: the codim-7 tie `ζ_{a-c'}(b, a') = 0`; the case `α1 = 1`, `γ6 ≤ 1`, `qr ≥ 0`,
`ζ < 0` (S3.6b needs `α1 > 1`); and the S3.6a leftover (no tilt of the cone works, `K17cBad`). -/
def K17cLeft (a a' b c c' d : ℝ³) (α1 β6 γ6 : ℝ) : Prop :=
  ⟪b - a', a - c'⟫ = 0 ∨
  (α1 = 1 ∧ γ6 ≤ 1 ∧ 0 ≤ ⟪b - d, c - d⟫ ∧ ⟪b - a', a - c'⟫ < 0) ∨
  (γ6 ≤ 1 ∧ 0 ≤ ⟪b - d, c - d⟫ ∧ 0 < ⟪b - a', a - c'⟫ ∧
    K17cBad β6 γ6 ⟪b - d, b - d⟫ ⟪b - d, c - d⟫ ⟪c - d, c - d⟫)

/-- `ζ_{a-c'}(b, a') = (β6 - 1) qq + γ6 qr` on the slice. -/
theorem k17c_zeta {a a' b c c' d : ℝ³} {α1 β6 γ6 : ℝ}
    (hc' : c' = d + α1 • (a - d) + (1 : ℝ) • (b - d)) (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hm0 : ⟪a - d, b - d⟫ = 0) (hpr : ⟪a - d, c - d⟫ = 0) :
    ⟪b - a', a - c'⟫ = (β6 - 1) * ⟪b - d, b - d⟫ + γ6 * ⟪b - d, c - d⟫ := by
  have e1 : b - a' = (1 - β6) • (b - d) + (-γ6) • (c - d) := by rw [ha']; module
  have e2 : a - c' = (1 - α1) • (a - d) + (-1 : ℝ) • (b - d) := by rw [hc']; module
  rw [e1, e2]
  have h1 := real_inner_comm (a - d) (b - d)
  have h2 := real_inner_comm (a - d) (c - d)
  have h3 := real_inner_comm (b - d) (c - d)
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, h1, h2, h3, hm0, hpr]
  ring

set_option maxHeartbeats 3200000 in
theorem k17c_boundary_core {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) {α1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + (1 : ℝ) • (b - d)) (hb' : b' = d + α1 • (a - d) + (1 : ℝ) • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 0 < α1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (h3 : 1 < β6 + γ6)
    (hM : K6sM a a' b b' c c' d) (hm0 : ⟪a - d, b - d⟫ = 0) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K17cLeft a a' b c c' d α1 β6 γ6 := by
  obtain ⟨hpr, hpp, hqq, hrr, hq1, -⟩ := k17c_gram hdet hc' hb' hM hm0
  have hz := k17c_zeta hc' ha' hm0 hpr
  rcases lt_or_ge α1 1 with hlt | hge
  · left
    exact k6m_B_hasLexCell W hdet (by simpa using hc') (by simpa using hb') ha' hα1 one_pos (by linarith) hβ6 hγ6 hlt
  have hgW := k6m_gWb W hdet (β1 := 1) (by simpa using hc') (by simpa using hb') ha'
  rcases le_or_gt γ6 1 with hγ61 | hγ61
  · -- γ6 ≤ 1
    rcases lt_or_ge ⟪b - d, c - d⟫ 0 with hqr | hqr
    · exact Or.inl (k17c_s35_hasLexCell hdet hc' hb' ha' hge hβ6 hγ6 h3 hγ61 hM hm0 hqr)
    rcases lt_trichotomy ⟪b - a', a - c'⟫ 0 with hzl | hz0 | hzg
    · rcases eq_or_lt_of_le hge with he | hgt
      · exact Or.inr (Or.inr (Or.inl ⟨he.symm, hγ61, hqr, hzl⟩))
      · exact Or.inl (k17c_s36b_hasLexCell hdet hc' hb' ha' hgt hβ6 hγ6 h3 hγ61 hM hm0 (by rw [← hz]; exact hzl))
    · exact Or.inr (Or.inl hz0)
    · by_cases hB : K17cBad β6 γ6 ⟪b - d, b - d⟫ ⟪b - d, c - d⟫ ⟪c - d, c - d⟫
      · exact Or.inr (Or.inr (Or.inr ⟨hγ61, hqr, hzg, hB⟩))
      · exact Or.inl (k17c_s36a_hasLexCell hdet hc' hb' ha' hge hβ6 hγ6 h3 hγ61 hM hm0 hB)
  · -- γ6 > 1, so α1 > 1
    have hgt : 1 < α1 := by
      by_contra hcon; push Not at hcon
      nlinarith [mul_nonneg hβ6.le (sub_nonneg.2 hcon)]
    rcases lt_trichotomy ⟪b - a', a - c'⟫ 0 with hzl | hz0 | hzg
    · exact Or.inl (k17c_s34_hasLexCell hdet hc' hb' ha' hgt hβ6 hγ61 hM hm0 (by rw [← hz]; exact hzl))
    · exact Or.inr (Or.inl hz0)
    · exact Or.inl (k17c_s33_hasLexCell hdet hc' hb' ha' hge hβ6 hγ6 h3 hγ61 hM hm0 (by rw [← hz]; exact hzg))

/-- **The `β1 = 1` piece of `K16LeftMN2 W`.** -/
theorem k17c_boundary_n2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hs : K6sMN2 a a' b b' c c' d) {α1 β1 β6 γ6 : ℝ} (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6)
    (h : β1 = 1) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K17cLeft a a' b c c' d α1 β6 γ6 := by
  obtain ⟨hdet, hc', hb', ha', hα1', hβ1', h1, hβ6', hγ6', h3⟩ := hC
  subst h
  have hrel := k17c_n2_rel W hs.1 hs.2.1 hs.2.2.1 hdet hc' ha' hγ6' h3
  exact k17c_boundary_core W hdet hc' hb' ha' hα1' hβ6' hγ6' h3 hs.2.2 (k17c_m_zero hα1' hrel)

/-- **The `β1 = 1` piece of `K16LeftMKb W`.** -/
theorem k17c_boundary_kb {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hs : K6sMKb a a' b b' c c' d) {α1 β1 β6 γ6 : ℝ} (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6)
    (h : β1 = 1) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K17cLeft a a' b c c' d α1 β6 γ6 := by
  obtain ⟨hdet, hc', hb', ha', hα1', hβ1', h1, hβ6', hγ6', h3⟩ := hC
  subst h
  have hrel := k17c_kb_rel W hs.1 hs.2.1 hs.2.2.1 hdet hb'
  exact k17c_boundary_core W hdet hc' hb' ha' hα1' hβ6' hγ6' h3 hs.2.2 (k17c_m_zero hα1' hrel)

end C2
end Type08Sp
end Minimality
