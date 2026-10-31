module

public import Minimality.SecondOrderT2b

@[expose] public section

/-!
# Second order with spin (plan specpos A1)

`virial_secondOrder_le`: for a balanced load (force, screen torque, depth), the second-order term of the motion
with screen axis `w` and spin `w2` is at most `-w2^2 * tr M`, where `tr M = Σ λ ⟪n, p⟫`.

`isRupert_of_secondOrder_spin`: a weakly inward first-order motion with spin about the view axis (`ω 2 ≠ 0`) is a
passage, because `tr M > 0` for every nonzero load (force balance against an interior point `o`).
-/

namespace Minimality
open scoped RealInnerProductSpace Matrix Topology
open Filter

private lemma spin_ip2 (a b : ℝ²) : ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

private lemma spin_nsq2 (a : ℝ²) : ‖a‖ ^ 2 = a 0 * a 0 + a 1 * a 1 := by
  rw [← real_inner_self_eq_norm_sq, spin_ip2]

/-- A1 core: the second-order term of a balanced load is at most `-ω₂² · tr M`. -/
theorem virial_secondOrder_le {ι : Type*} [Fintype ι] (p n : ι → ℝ²) (z lam : ι → ℝ)
    (hlam : ∀ j, 0 ≤ lam j) (hout : ∀ j k, ⟪n j, p k - p j⟫ ≤ 0)
    (hF : ∑ j, lam j • n j = 0) (hT : ∑ j, lam j * cross2 (p j) (n j) = 0)
    (hD : ∑ j, (lam j * z j) • n j = 0) (w : ℝ²) (w2 : ℝ) :
    ∑ j, lam j * (⟪n j, w⟫ * (⟪w, p j⟫ + w2 * z j) - (‖w‖ ^ 2 + w2 ^ 2) * ⟪n j, p j⟫) ≤
      -(w2 ^ 2) * ∑ j, lam j * ⟪n j, p j⟫ := by
  set Jw : ℝ² := !₂[-w 1, w 0] with hJ
  have hJ0 : Jw 0 = -w 1 := by simp [hJ]
  have hJ1 : Jw 1 = w 0 := by simp [hJ]
  have hMw := virial_psd p n lam hlam hout hF hT Jw
  have hDw : ∑ j, lam j * (⟪n j, w⟫ * z j) = 0 := by
    have := congrArg (fun v => ⟪v, w⟫) hD
    simp only [sum_inner, inner_smul_left, inner_zero_left] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [real_inner_comm]; ring
  have key : ∑ j, lam j * (⟪n j, w⟫ * (⟪w, p j⟫ + w2 * z j) - (‖w‖ ^ 2 + w2 ^ 2) * ⟪n j, p j⟫)
      = -(∑ j, lam j * (⟪Jw, p j⟫ * ⟪Jw, n j⟫)) - w2 ^ 2 * ∑ j, lam j * ⟪n j, p j⟫
        + w2 * ∑ j, lam j * (⟪n j, w⟫ * z j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [spin_ip2, spin_nsq2, hJ0, hJ1]; ring
  rw [key, hDw]
  nlinarith

/-- A1: a weakly inward first-order motion with spin about the view axis is a passage. -/
theorem isRupert_of_secondOrder_spin (V : Finset ℝ³) {ι : Type*} [Fintype ι] (n : ι → ℝ²) (h : ι → ℝ)
    (hpoly : {y : ℝ² | ∀ e, ⟪n e, y⟫ < h e} ⊆ proj_xy '' convexHull ℝ (V : Set ℝ³))
    (hS : ∀ y ∈ proj_xy '' convexHull ℝ (V : Set ℝ³), ∀ e, ⟪n e, y⟫ ≤ h e)
    (o : ℝ²) (ho : ∀ e, ⟪n e, o⟫ < h e)
    (ω τ : ℝ³) (hspin : ω 2 ≠ 0)
    (hweak : ∀ v ∈ V, ∀ e, ⟪n e, proj_xy v⟫ < h e ∨
      (⟪n e, proj_xy v⟫ = h e ∧ ⟪n e, screenVel ω τ v⟫ ≤ 0)) :
    IsRupert V := by
  classical
  refine isRupert_of_secondOrder_noBalanced V n h hpoly ω τ hweak ?_
  intro lam hl0 hsupp hne hF hT hD
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
  have hv := virial_secondOrder_le (fun k : V × ι => proj_xy (k.1 : ℝ³)) n'
    (fun k => (k.1 : ℝ³) 2) (fun k => lam k.1 k.2) (fun k => hl0 _ _) hout hF' hT' hD'
    !₂[ω 0, ω 1] (ω 2)
  simp only [Fintype.sum_prod_type] at hv
  have hS' : ∑ v : V, ∑ e : ι, lam v e * ⟪n' (v, e), proj_xy (v : ℝ³)⟫ =
      ∑ v : V, ∑ e : ι, lam v e * ⟪n e, proj_xy (v : ℝ³)⟫ := by
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun e _ => ?_
    by_cases hp : lam v e = 0
    · simp [hp]
    · simp [n', hp]
  have hSpos : 0 < ∑ v : V, ∑ e : ι, lam v e * ⟪n e, proj_xy (v : ℝ³)⟫ := by
    have hbal : ∑ v : V, ∑ e : ι, lam v e * ⟪n e, o⟫ = 0 := by
      have := congrArg (fun u => ⟪u, o⟫) hF
      simp only [sum_inner, inner_smul_left, inner_zero_left] at this
      rw [← this]
      refine Finset.sum_congr rfl fun v _ => ?_
      simp
    have : ∑ v : V, ∑ e : ι, lam v e * ⟪n e, proj_xy (v : ℝ³)⟫ =
        ∑ v : V, ∑ e : ι, lam v e * (h e - ⟪n e, o⟫) := by
      rw [show ∑ v : V, ∑ e : ι, lam v e * (h e - ⟪n e, o⟫) =
        ∑ v : V, ∑ e : ι, lam v e * h e - ∑ v : V, ∑ e : ι, lam v e * ⟪n e, o⟫ by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun e _ => by ring, hbal, sub_zero]
      refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun e _ => ?_
      by_cases hp : lam v e = 0
      · simp [hp]
      · rw [(hsupp v e hp).1]
    rw [this]
    obtain ⟨v0, e0, h0⟩ := hne
    have hpos : ∀ v e, 0 ≤ lam v e * (h e - ⟪n e, o⟫) := fun v e =>
      mul_nonneg (hl0 v e) (by linarith [ho e])
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun v => ∑ e : ι, lam v e * (h e - ⟪n e, o⟫))
      (fun v _ => Finset.sum_nonneg fun e _ => hpos v e) (Finset.mem_univ v0))
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun e => lam v0 e * (h e - ⟪n e, o⟫))
      (fun e _ => hpos v0 e) (Finset.mem_univ e0))
    exact mul_pos (lt_of_le_of_ne (hl0 _ _) (Ne.symm h0)) (by linarith [ho e0])
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
        ⟪n e, proj_xy ((crossMatrix ω).toEuclideanLin ((crossMatrix ω).toEuclideanLin (v : ℝ³)))⟫ ≤
      -(ω 2 ^ 2) * ∑ v : V, ∑ e : ι, lam v e * ⟪n e, proj_xy (v : ℝ³)⟫ := by
    rw [heq, ← hS']; simpa using hv
  have : 0 < ω 2 ^ 2 := by positivity
  nlinarith

end Minimality
