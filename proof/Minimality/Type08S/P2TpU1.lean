module

public import Minimality.Type08S.P2TpBase

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# T'X, cell C1 depth pattern (pure real lemma)
The 6-cycle `(d, a, b', c, a', b)` with depths `(0, a, α4 a + γ4 c, c, γ6 c + β6 ν, ν)` has exactly one
local maximum when the planar quadrilateral `(d, a, b', c)` has its top in `{d, c}` (strictly) and
`a'` is not tied with `b` or `c`.
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

theorem tpU1 {a c ν α4 γ4 β6 γ6 : ℝ} (hν : 0 < ν) (hα4 : 0 < α4) (hγ4 : 0 < γ4)
    (hE : 1 < α4 + γ4) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hconv : 1 < β6 + γ6)
    (hM : max a (α4 * a + γ4 * c) < max 0 c)
    (h1 : γ6 * c + β6 * ν ≠ ν) (h2 : γ6 * c + β6 * ν ≠ c) :
    QTop 6 (six 0 a (α4 * a + γ4 * c) c (γ6 * c + β6 * ν) ν) := by
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := z6_add_one
  obtain ⟨r0, r1, r2, r3, r4, r5⟩ := z6_sub_one
  have hMa : a < max 0 c := lt_of_le_of_lt (le_max_left _ _) hM
  have hMb : α4 * a + γ4 * c < max 0 c := lt_of_le_of_lt (le_max_right _ _) hM
  -- A has a larger neighbour
  have hA : a < 0 ∨ a < α4 * a + γ4 * c := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨ha0, hab⟩ := hcon
    rcases le_total c 0 with hc | hc
    · rw [max_eq_left hc] at hMa; linarith
    · rw [max_eq_right hc] at hMa hMb
      nlinarith [mul_nonneg ha0 (sub_nonneg.2 hE.le), mul_pos hγ4 (sub_pos.2 hMa)]
  -- B' has a larger neighbour
  have hB : α4 * a + γ4 * c < a ∨ α4 * a + γ4 * c < c := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨hba, hbc⟩ := hcon
    have hb0 : α4 * a + γ4 * c < 0 := by
      rcases le_total c 0 with hc | hc
      · rw [max_eq_left hc] at hMb; exact hMb
      · rw [max_eq_right hc] at hMb; linarith
    nlinarith [mul_nonneg hα4.le (sub_nonneg.2 hba), mul_nonneg hγ4.le (sub_nonneg.2 hbc)]
  have hD : (0:ℝ) < ν := hν
  have gD : (0:ℝ) < ν := hν
  have hcases : (γ6 * c + β6 * ν > ν ∧ γ6 * c + β6 * ν > c) ∨
      (γ6 * c + β6 * ν < ν ∧ γ6 * c + β6 * ν > c) ∨ (γ6 * c + β6 * ν > ν ∧ γ6 * c + β6 * ν < c) := by
    rcases lt_or_gt_of_ne h1 with p1 | p1 <;> rcases lt_or_gt_of_ne h2 with p2 | p2
    · exfalso
      nlinarith [mul_pos hν (sub_pos.2 hconv), mul_pos hγ6 (sub_pos.2 p1), mul_pos hγ6 (sub_pos.2 p2),
        mul_pos (sub_pos.2 hγ61) (sub_pos.2 p1)]
    · exact Or.inr (Or.inl ⟨p1, p2⟩)
    · exact Or.inr (Or.inr ⟨p1, p2⟩)
    · exact Or.inl ⟨p1, p2⟩
  rcases hcases with ⟨p1, p2⟩ | ⟨p1, p2⟩ | ⟨p1, p2⟩
  · refine ⟨4, fun i hi => ?_⟩
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [r0, r1, r2, r3, r4, r5, s0, s1, s2, s3, s4, s5, six_0, six_1, six_2, six_3, six_4,
        six_5] at hA hB ⊢
    · exact Or.inl gD
    · exact hA
    · exact hB
    · exact Or.inr p2
    · exact absurd rfl hi
    · exact Or.inl p1
  · refine ⟨5, fun i hi => ?_⟩
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [r0, r1, r2, r3, r4, r5, s0, s1, s2, s3, s4, s5, six_0, six_1, six_2, six_3, six_4,
        six_5] at hA hB ⊢
    · exact Or.inl gD
    · exact hA
    · exact hB
    · exact Or.inr p2
    · exact Or.inr p1
    · exact absurd rfl hi
  · refine ⟨3, fun i hi => ?_⟩
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [r0, r1, r2, r3, r4, r5, s0, s1, s2, s3, s4, s5, six_0, six_1, six_2, six_3, six_4,
        six_5] at hA hB ⊢
    · exact Or.inl gD
    · exact hA
    · exact hB
    · exact absurd rfl hi
    · exact Or.inl p2
    · exact Or.inl p1

end Type08Sp
end Minimality
