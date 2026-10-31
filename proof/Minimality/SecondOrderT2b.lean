module

public import Minimality.SecondOrderT2
public import Minimality.VirialQ

@[expose] public section

/-!
# Theorem T2(a)+(b): only flat balanced loads obstruct

With the virial bound `virial_secondOrder_nonpos` (every balanced load has second-order term ≤ 0), the obstruction
in `isRupert_of_secondOrder_noBalanced` reduces to a nonzero balanced load on the doubly tight pairs whose
second-order term is exactly 0 (`isRupert_of_secondOrder_noFlatLoad`).  nopert229/out/bottleneck/virial/draft.md §2.
-/

namespace Minimality
open scoped RealInnerProductSpace Matrix Topology
open Filter

theorem isRupert_of_secondOrder_noFlatLoad (V : Finset ℝ³) {ι : Type*} [Fintype ι] (n : ι → ℝ²) (h : ι → ℝ)
    (hpoly : {y : ℝ² | ∀ e, ⟪n e, y⟫ < h e} ⊆ proj_xy '' convexHull ℝ (V : Set ℝ³))
    (hS : ∀ y ∈ proj_xy '' convexHull ℝ (V : Set ℝ³), ∀ e, ⟪n e, y⟫ ≤ h e)
    (ω τ : ℝ³)
    (hweak : ∀ v ∈ V, ∀ e, ⟪n e, proj_xy v⟫ < h e ∨
      (⟪n e, proj_xy v⟫ = h e ∧ ⟪n e, screenVel ω τ v⟫ ≤ 0))
    (hQ0 : ∀ lam : V → ι → ℝ, (∀ v e, 0 ≤ lam v e) →
      (∀ v e, lam v e ≠ 0 → ⟪n e, proj_xy (v : ℝ³)⟫ = h e ∧ ⟪n e, screenVel ω τ v⟫ = 0) →
      (∃ v e, lam v e ≠ 0) →
      ∑ v, ∑ e, lam v e • n e = 0 →
      ∑ v, ∑ e, lam v e * ((proj_xy (v : ℝ³)) 0 * n e 1 - (proj_xy (v : ℝ³)) 1 * n e 0) = 0 →
      ∑ v, ∑ e, (lam v e * (v : ℝ³) 2) • n e = 0 →
      ∑ v, ∑ e, lam v e *
        ⟪n e, proj_xy ((crossMatrix ω).toEuclideanLin ((crossMatrix ω).toEuclideanLin (v : ℝ³)))⟫ ≠ 0) :
    IsRupert V := by
  classical
  refine isRupert_of_secondOrder_noBalanced V n h hpoly ω τ hweak ?_
  intro lam hl0 hsupp hne hF hT hD
  have hne0 := hQ0 lam hl0 hsupp hne hF hT hD
  let n' : V × ι → ℝ² := fun p => if lam p.1 p.2 ≠ 0 then n p.2 else 0
  have hn' : ∀ p : V × ι, lam p.1 p.2 • n' p = lam p.1 p.2 • n p.2 := by
    intro p
    by_cases hp : lam p.1 p.2 = 0
    · simp [hp]
    · simp [n', hp]
  have hF' : ∑ j : V × ι, lam j.1 j.2 • n' j = 0 := by
    rw [Fintype.sum_prod_type, ← hF]
    exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun e _ => hn' (v, e)
  have hD' : ∑ j : V × ι, (lam j.1 j.2 * (j.1 : ℝ³) 2) • n' j = 0 := by
    have : ∀ p : V × ι, (lam p.1 p.2 * (p.1 : ℝ³) 2) • n' p = (lam p.1 p.2 * (p.1 : ℝ³) 2) • n p.2 := by
      intro p
      by_cases hp : lam p.1 p.2 = 0
      · simp [hp]
      · simp [n', hp]
    rw [Fintype.sum_prod_type, ← hD]
    exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun e _ => this (v, e)
  have hT' : ∑ j : V × ι, lam j.1 j.2 * cross2 (proj_xy (j.1 : ℝ³)) (n' j) = 0 := by
    have : ∀ p : V × ι, lam p.1 p.2 * cross2 (proj_xy (p.1 : ℝ³)) (n' p) =
        lam p.1 p.2 * ((proj_xy (p.1 : ℝ³)) 0 * n p.2 1 - (proj_xy (p.1 : ℝ³)) 1 * n p.2 0) := by
      intro p
      by_cases hp : lam p.1 p.2 = 0
      · simp [hp]
      · simp [n', hp, cross2]
    rw [Fintype.sum_prod_type, ← hT]
    exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun e _ => this (v, e)
  have hout : ∀ j k : V × ι, ⟪n' j, proj_xy (k.1 : ℝ³) - proj_xy (j.1 : ℝ³)⟫ ≤ 0 := by
    intro j k
    by_cases hp : lam j.1 j.2 = 0
    · simp [n', hp]
    · have hj := (hsupp j.1 j.2 hp).1
      have hk := hS (proj_xy (k.1 : ℝ³)) ⟨k.1, subset_convexHull ℝ _ k.1.2, rfl⟩ j.2
      simp only [n', hp, ne_eq, not_false_eq_true, ite_true, inner_sub_right]
      linarith
  have hv := virial_secondOrder_nonpos (fun k : V × ι => proj_xy (k.1 : ℝ³)) n'
    (fun k => (k.1 : ℝ³) 2) (fun k => lam k.1 k.2) (fun k => hl0 _ _) hout hF' hT' hD'
    !₂[ω 0, ω 1] (ω 2)
  rw [Fintype.sum_prod_type] at hv
  have heq : ∑ v : V, ∑ e : ι, lam v e *
        ⟪n e, proj_xy ((crossMatrix ω).toEuclideanLin ((crossMatrix ω).toEuclideanLin (v : ℝ³)))⟫ =
      ∑ v : V, ∑ e : ι, lam v e * (⟪n' (v, e), !₂[ω 0, ω 1]⟫ * (⟪(!₂[ω 0, ω 1] : ℝ²), proj_xy (v : ℝ³)⟫ + ω 2 * (v : ℝ³) 2) - (‖(!₂[ω 0, ω 1] : ℝ²)‖ ^ 2 + ω 2 ^ 2) * ⟪n' (v, e), proj_xy (v : ℝ³)⟫) := by
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun e _ => ?_
    by_cases hp : lam v e = 0
    · simp [hp]
    · simp only [n', hp, ne_eq, not_false_eq_true, ite_true]
      congr 1
      have hnorm : ‖(!₂[ω 0, ω 1] : ℝ²)‖ ^ 2 = ω 0 ^ 2 + ω 1 ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_two]
      rw [hnorm]
      simp [Fin.sum_univ_two, crossMatrix, proj_xy,
        Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, PiLp.inner_apply]
      ring
  have hle : ∑ v : V, ∑ e : ι, lam v e *
        ⟪n e, proj_xy ((crossMatrix ω).toEuclideanLin ((crossMatrix ω).toEuclideanLin (v : ℝ³)))⟫ ≤ 0 := by
    rw [heq]; simpa using hv
  exact lt_of_le_of_ne hle hne0
end Minimality
