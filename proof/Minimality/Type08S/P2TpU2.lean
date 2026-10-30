module

public import Minimality.Type08S.P2TpBase

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# T'X, cell C2 depth pattern (pure real lemma)
The 5-cycle `(d, a, c', b', c)` with depths `(0, a, a + β1 ν, α4 a + γ4 c, c)` has exactly one local
maximum when the top of the planar quadrilateral `(d, a, b', c)` lies in `{a, b'}` (strictly) and
`c'` is not tied with `b'`.
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

theorem tpU2 {a c ν α4 γ4 β1 : ℝ} (hν : 0 < ν) (hα4 : 0 < α4) (hγ4 : 0 < γ4)
    (hE : 1 < α4 + γ4) (hβ1 : 0 < β1)
    (hM : max 0 c < max a (α4 * a + γ4 * c))
    (h1 : a + β1 * ν ≠ α4 * a + γ4 * c) :
    QTop 5 (quint 0 a (a + β1 * ν) (α4 * a + γ4 * c) c) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := zmod5_add_one
  obtain ⟨r0, r1, r2, r3, r4⟩ := zmod5_sub_one
  have hMc : c < max a (α4 * a + γ4 * c) := lt_of_le_of_lt (le_max_right _ _) hM
  have hM0 : 0 < max a (α4 * a + γ4 * c) := lt_of_le_of_lt (le_max_left _ _) hM
  have hD : 0 < c ∨ 0 < a := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨hc, ha⟩ := hcon
    rcases le_total a (α4 * a + γ4 * c) with h | h
    · rw [max_eq_right h] at hM0; nlinarith [mul_nonneg hα4.le (neg_nonneg.2 ha), mul_nonneg hγ4.le (neg_nonneg.2 hc)]
    · rw [max_eq_left h] at hM0; linarith
  have hC : c < α4 * a + γ4 * c ∨ c < 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨hcb, hc0⟩ := hcon
    have hmx : max 0 c = c := max_eq_right hc0
    rw [hmx] at hM
    have hac : c < a := by
      rcases le_total a (α4 * a + γ4 * c) with h | h
      · rw [max_eq_right h] at hM; linarith
      · rw [max_eq_left h] at hM; exact hM
    nlinarith [mul_pos hα4 (sub_pos.2 hac), mul_nonneg hc0 (sub_nonneg.2 hE.le)]
  have hA : a < a + β1 * ν := by nlinarith [mul_pos hβ1 hν]
  rcases lt_or_gt_of_ne h1 with p | p
  · refine ⟨3, fun i hi => ?_⟩
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp only [r0, r1, r2, r3, r4, s0, s1, s2, s3, s4, quint_0, quint_1, quint_2, quint_3,
        quint_4] at hD hC hA ⊢
    · rcases hD with h | h
      · exact Or.inl h
      · exact Or.inr h
    · exact Or.inr hA
    · exact Or.inr p
    · exact absurd rfl hi
    · exact hC.imp id id
  · refine ⟨2, fun i hi => ?_⟩
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp only [r0, r1, r2, r3, r4, s0, s1, s2, s3, s4, quint_0, quint_1, quint_2, quint_3,
        quint_4] at hD hC hA ⊢
    · rcases hD with h | h
      · exact Or.inl h
      · exact Or.inr h
    · exact Or.inr hA
    · exact absurd rfl hi
    · exact Or.inl p
    · exact hC.imp id id

end Type08Sp
end Minimality
