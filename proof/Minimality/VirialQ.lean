module

public import Minimality.Virial

@[expose] public section

namespace Minimality
open scoped RealInnerProductSpace

private lemma virial_ip2 (a b : ℝ²) : ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

private lemma virial_nsq2 (a : ℝ²) : ‖a‖ ^ 2 = a 0 * a 0 + a 1 * a 1 := by
  rw [← real_inner_self_eq_norm_sq, virial_ip2]

/-- Second-order term of the rotation `ω = (w, w2)` against a balanced outward load is
nonpositive (Theorem T2(b), step 6 of the virial draft). -/
theorem virial_secondOrder_nonpos {ι : Type*} [Fintype ι] (p n : ι → ℝ²) (z lam : ι → ℝ)
    (hlam : ∀ j, 0 ≤ lam j) (hout : ∀ j k, ⟪n j, p k - p j⟫ ≤ 0)
    (hF : ∑ j, lam j • n j = 0) (hT : ∑ j, lam j * cross2 (p j) (n j) = 0)
    (hD : ∑ j, (lam j * z j) • n j = 0) (w : ℝ²) (w2 : ℝ) :
    ∑ j, lam j * (⟪n j, w⟫ * (⟪w, p j⟫ + w2 * z j) - (‖w‖ ^ 2 + w2 ^ 2) * ⟪n j, p j⟫) ≤ 0 := by
  set Jw : ℝ² := !₂[-w 1, w 0] with hJ
  have hJ0 : Jw 0 = -w 1 := by simp [hJ]
  have hJ1 : Jw 1 = w 0 := by simp [hJ]
  have hMw := virial_psd p n lam hlam hout hF hT Jw
  have he0 := virial_psd p n lam hlam hout hF hT !₂[1, 0]
  have he1 := virial_psd p n lam hlam hout hF hT !₂[0, 1]
  -- depth term
  have hDw : ∑ j, lam j * (⟪n j, w⟫ * z j) = 0 := by
    have := congrArg (fun v => ⟪v, w⟫) hD
    simp only [sum_inner, inner_smul_left, inner_zero_left] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [real_inner_comm]; ring
  have htr : 0 ≤ ∑ j, lam j * ⟪n j, p j⟫ := by
    have : ∑ j, lam j * ⟪n j, p j⟫ =
        ∑ j, lam j * (⟪!₂[1, 0], p j⟫ * ⟪!₂[1, 0], n j⟫)
        + ∑ j, lam j * (⟪!₂[0, 1], p j⟫ * ⟪!₂[0, 1], n j⟫) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [virial_ip2]; simp; ring
    rw [this]; linarith
  have key : ∑ j, lam j * (⟪n j, w⟫ * (⟪w, p j⟫ + w2 * z j) - (‖w‖ ^ 2 + w2 ^ 2) * ⟪n j, p j⟫)
      = -(∑ j, lam j * (⟪Jw, p j⟫ * ⟪Jw, n j⟫)) - w2 ^ 2 * ∑ j, lam j * ⟪n j, p j⟫
        + w2 * ∑ j, lam j * (⟪n j, w⟫ * z j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [virial_ip2, virial_nsq2, hJ0, hJ1]; ring
  rw [key, hDw]
  have := mul_nonneg (sq_nonneg w2) htr
  nlinarith
