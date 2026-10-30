module

public import Minimality.Type08S.P2S2
public import Minimality.Type08S.G6B4

@[expose] public section

set_option relaxedAutoImplicit true
set_option autoImplicit true
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality

/-- The reflection `x ↦ x - 2⟪x,e⟫e` is additive, homogeneous, preserves inner products, and flips `det3`. -/
theorem refl_add (e p q : ℝ³) :
    (p + q) - (2 * ⟪p + q, e⟫) • e = (p - (2 * ⟪p, e⟫) • e) + (q - (2 * ⟪q, e⟫) • e) := by
  rw [inner_add_left]; module

theorem refl_smul (e p : ℝ³) (t : ℝ) :
    (t • p) - (2 * ⟪t • p, e⟫) • e = t • (p - (2 * ⟪p, e⟫) • e) := by
  rw [real_inner_smul_left]; module

theorem refl_inner (e p q : ℝ³) (he : ⟪e, e⟫ = 1) :
    ⟪p - (2 * ⟪p, e⟫) • e, q - (2 * ⟪q, e⟫) • e⟫ = ⟪p, q⟫ := by
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, he]
  rw [real_inner_comm e q]; ring

theorem refl_det (e p q r : ℝ³) (he : ⟪e, e⟫ = 1) :
    det3 (p - (2 * ⟪p, e⟫) • e) (q - (2 * ⟪q, e⟫) • e) (r - (2 * ⟪r, e⟫) • e) = - det3 p q r := by
  have h : det3 (p - (2 * ⟪p, e⟫) • e) (q - (2 * ⟪q, e⟫) • e) (r - (2 * ⟪r, e⟫) • e) =
      (1 - 2 * ⟪e, e⟫) * det3 p q r := by ex
  rw [h, he]; ring

theorem Tp_sep_core_neg (d A B C : ℝ³) {α4 β1 γ4 β6 γ6 : ℝ}
    (hH : det3 A C B < 0)
    (hα4 : 0 < α4) (hα : α4 < 1) (hγ4 : 0 < γ4) (hαγ : 1 < α4 + γ4) (hβ1 : 0 < β1)
    (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hsep : max (max 0 ⟪A, B⟫) (max (α4 * ⟪A, B⟫ + γ4 * ⟪C, B⟫) ⟪C, B⟫)
              < min ⟪B, B⟫ (⟪A, B⟫ + β1 * ⟪B, B⟫)) :
    IsRupert (insert d ({d + A, d + β6 • B + γ6 • C, d + B, d + α4 • A + γ4 • C, d + C,
      d + A + β1 • B} : Finset ℝ³)) := by
  classical
  let e : ℝ³ := EuclideanSpace.single 0 1
  have he : ⟪e, e⟫ = 1 := by simp [e]
  let f : ℝ³ → ℝ³ := fun x => x - (2 * ⟪x, e⟫) • e
  have hfa : ∀ p q, f (p + q) = f p + f q := fun p q => refl_add e p q
  have hfs : ∀ p t, f (t • p) = t • f p := fun p t => refl_smul e p t
  have hfi : ∀ p q, ⟪f p, f q⟫ = ⟪p, q⟫ := fun p q => refl_inner e p q he
  refine Type08Sp.isRupert_of_reflect e he _ ?_
  simp only [Finset.image_insert, Finset.image_singleton]
  show IsRupert (insert (f d) {f (d + A), f (d + β6 • B + γ6 • C), f (d + B), f (d + α4 • A + γ4 • C),
    f (d + C), f (d + A + β1 • B)})
  simp only [hfa, hfs]
  refine Tp_sep_core (f d) (f A) (f B) (f C) ?_ hα4 hα hγ4 hαγ hβ1 hβ6 hγ6 hγ61 ?_
  · have := refl_det e A C B he
    show 0 < det3 (A - (2 * ⟪A, e⟫) • e) (C - (2 * ⟪C, e⟫) • e) (B - (2 * ⟪B, e⟫) • e)
    rw [this]; linarith
  · simp only [hfi]; exact hsep

theorem Tp_sep_core_any (d A B C : ℝ³) {α4 β1 γ4 β6 γ6 : ℝ}
    (hH : det3 A C B ≠ 0)
    (hα4 : 0 < α4) (hα : α4 < 1) (hγ4 : 0 < γ4) (hαγ : 1 < α4 + γ4) (hβ1 : 0 < β1)
    (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hsep : max (max 0 ⟪A, B⟫) (max (α4 * ⟪A, B⟫ + γ4 * ⟪C, B⟫) ⟪C, B⟫)
              < min ⟪B, B⟫ (⟪A, B⟫ + β1 * ⟪B, B⟫)) :
    IsRupert (insert d ({d + A, d + β6 • B + γ6 • C, d + B, d + α4 • A + γ4 • C, d + C,
      d + A + β1 • B} : Finset ℝ³)) := by
  rcases lt_or_gt_of_ne hH with h | h
  · exact Tp_sep_core_neg d A B C h hα4 hα hγ4 hαγ hβ1 hβ6 hγ6 hγ61 hsep
  · exact Tp_sep_core d A B C h hα4 hα hγ4 hαγ hβ1 hβ6 hγ6 hγ61 hsep

end Minimality
