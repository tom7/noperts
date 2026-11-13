module

public import Minimality.Type08S.SCh

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true

set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- Frame coordinates by inner products. -/
theorem pc_coords (hF : Fr e1 e2 e3) (o p : ℝ³) :
    p = o + pc e1 e2 e3 ⟪p - o, e1⟫ ⟪p - o, e2⟫ ⟪p - o, e3⟫ := by
  have := hF.expand (p - o)
  rw [pc]; rw [← this]; abel

theorem Fr.neg_13 (hF : Fr e1 e2 e3) : Fr (-e1) e2 (-e3) where
  n11 := by simpa using hF.n11
  n22 := hF.n22
  n33 := by simpa using hF.n33
  n12 := by simpa using hF.n12
  n13 := by simpa using hF.n13
  n23 := by simpa using hF.n23
  c12 := by
    have := cross_smul_l (-1) e1 e2
    simp only [neg_smul, one_smul] at this; rw [this, hF.c12]
  c23 := by
    have := cross_smul_r (-1) e2 e3
    simp only [neg_smul, one_smul] at this; rw [this, hF.c23]
  c31 := by
    have h1 := cross_smul_l (-1) e3 (-e1)
    have h2 := cross_smul_r (-1) e3 e1
    simp only [neg_smul, one_smul] at h1 h2
    rw [h1, h2, hF.c31]; simp

/-- **Oriented frame at a view.**  `u = κ e3`, `v` edge-on (`⟪v,e2⟫ = 0`) with `⟪v,e1⟫ > 0`,
`⟪w,e2⟫ > 0` (right-handed; `κ` of either sign). -/
theorem frame_ex_pos {w u v : ℝ³} (hdet : det3 w u v ≠ 0) :
    ∃ e1 e2 e3 : ℝ³, ∃ κ : ℝ, Fr e1 e2 e3 ∧ κ ≠ 0 ∧ u = κ • e3 ∧ ⟪v, e2⟫ = 0 ∧ 0 < ⟪v, e1⟫ ∧
      0 < ⟪w, e2⟫ := by
  obtain ⟨e1, e2, e3, hF, hu1, hu2, hu3, hv2, hv1, hw2⟩ := frame_exists hdet
  have hu : u = ⟪u, e3⟫ • e3 := by
    have := hF.expand u; rw [hu1, hu2] at this; simpa using this
  rcases lt_or_gt_of_ne hv1 with h | h
  · refine ⟨-e1, e2, -e3, -⟪u, e3⟫, hF.neg_13, by simpa using hu3.ne', ?_, ?_, ?_, hw2⟩
    · rw [neg_smul, ← smul_neg] ; simpa using hu
    · simpa using hv2
    · simpa using h
  · exact ⟨e1, e2, e3, ⟪u, e3⟫, hF, hu3.ne', hu, hv2, h, hw2⟩

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.frame_ex_pos
