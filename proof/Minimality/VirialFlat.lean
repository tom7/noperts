module

public import Minimality.Virial

@[expose] public section

/-!
# Lemma V(b′): the flat case of the virial lemma

nopert229/out/bottleneck/virial/draft.md §5.  If the screen virial of a balanced, pairwise-outward load has
`bᵀMb = 0`, every load point carrying a force with nonzero `b`-component lies on one line
(`virial_flat_collinear`).  At a generic view this makes the T2 obstruction a special position: the b-carrying
silhouette vertices span a chord.
-/

namespace Minimality
open scoped RealInnerProductSpace

private lemma virialFlat_ipf (a b : ℝ²) : ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

private lemma virialFlat_quad_zero (α β : ℝ) (h : ∀ ε : ℝ, 0 ≤ α * ε + β * ε ^ 2) : α = 0 := by
  by_contra hα
  have hpos : 0 < |β| + 1 := by positivity
  set t := 1 / (|β| + 1) with ht
  have htpos : 0 < t := by positivity
  have hbt : β * t < 1 := by
    have h1 : β * t ≤ |β| * t := mul_le_mul_of_nonneg_right (le_abs_self β) htpos.le
    have h2 : |β| * t < 1 := by
      rw [ht, mul_one_div, div_lt_one hpos]; linarith
    linarith
  have := h (-α * t)
  have hα2 : 0 < α ^ 2 := by positivity
  have : 0 ≤ α ^ 2 * t * (β * t - 1) := by nlinarith
  have : α ^ 2 * t * (β * t - 1) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos hα2 htpos) (by linarith)
  linarith

private lemma virialFlat_grad_zero {ι : Type*} [Fintype ι] (p n : ι → ℝ²) (lam : ι → ℝ)
    (hpsd : ∀ a : ℝ², 0 ≤ ∑ j, lam j * (⟪a, p j⟫ * ⟪a, n j⟫))
    (hT : ∑ j, lam j * cross2 (p j) (n j) = 0) (b : ℝ²)
    (hb : ∑ j, lam j * (⟪b, p j⟫ * ⟪b, n j⟫) = 0) (c : ℝ²) :
    ∑ j, lam j * (⟪c, p j⟫ * ⟪b, n j⟫) = 0 := by
  have key : ∀ ε : ℝ, ∑ j, lam j * (⟪b + ε • c, p j⟫ * ⟪b + ε • c, n j⟫) =
      (∑ j, lam j * (⟪b, p j⟫ * ⟪b, n j⟫)) +
      ε * (2 * ∑ j, lam j * (⟪c, p j⟫ * ⟪b, n j⟫) +
        cross2 b c * ∑ j, lam j * cross2 (p j) (n j)) +
      ε ^ 2 * ∑ j, lam j * (⟪c, p j⟫ * ⟪c, n j⟫) := by
    intro ε
    have h1 : ∑ j, lam j * (⟪b + ε • c, p j⟫ * ⟪b + ε • c, n j⟫) =
        ∑ j, (lam j * (⟪b, p j⟫ * ⟪b, n j⟫) +
          ε * (2 * (lam j * (⟪c, p j⟫ * ⟪b, n j⟫)) +
            cross2 b c * (lam j * cross2 (p j) (n j))) +
          ε ^ 2 * (lam j * (⟪c, p j⟫ * ⟪c, n j⟫))) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [virialFlat_ipf, cross2, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [h1]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hq : ∀ ε : ℝ, 0 ≤ (2 * ∑ j, lam j * (⟪c, p j⟫ * ⟪b, n j⟫)) * ε +
      (∑ j, lam j * (⟪c, p j⟫ * ⟪c, n j⟫)) * ε ^ 2 := by
    intro ε
    have := hpsd (b + ε • c)
    rw [key, hb, hT] at this
    linarith
  have := virialFlat_quad_zero _ _ hq
  linarith

/-- Lemma V(b'): flat case. -/
theorem virial_flat_collinear {ι : Type*} [Fintype ι] (p n : ι → ℝ²) (lam : ι → ℝ)
    (hlam : ∀ j, 0 ≤ lam j)
    (hout : ∀ j k, ⟪n j, p k - p j⟫ ≤ 0)
    (hF : ∑ j, lam j • n j = 0) (hT : ∑ j, lam j * cross2 (p j) (n j) = 0) (b : ℝ²)
    (hb : ∑ j, lam j * (⟪b, p j⟫ * ⟪b, n j⟫) = 0) :
    ∃ o t : ℝ², t ≠ 0 ∧ ∀ j, lam j ≠ 0 → ⟪b, n j⟫ ≠ 0 → cross2 t (p j - o) = 0 := by
  classical
  by_cases hq : ∃ j, lam j ≠ 0 ∧ ⟪b, n j⟫ ≠ 0
  swap
  · refine ⟨0, !₂[1, 0], ?_, fun j h1 h2 => absurd ⟨j, h1, h2⟩ hq⟩
    intro h
    have := congrArg (fun v : ℝ² => v 0) h
    simp at this
  obtain ⟨j0, hl0, hψ0⟩ := hq
  have hgrad := virialFlat_grad_zero p n lam (virial_psd p n lam hlam hout hF hT) hT b hb
  set u : ℝ² := !₂[-b 1, b 0] with hu
  have hu0 : u 0 = -b 1 := by simp [hu]
  have hu1 : u 1 = b 0 := by simp [hu]
  have hNpos : 0 < b 0 * b 0 + b 1 * b 1 := by
    by_contra hN
    have h0 : b 0 = 0 := by nlinarith [mul_self_nonneg (b 0), mul_self_nonneg (b 1)]
    have h1 : b 1 = 0 := by nlinarith [mul_self_nonneg (b 0), mul_self_nonneg (b 1)]
    apply hψ0
    rw [virialFlat_ipf, h0, h1]; ring
  set N := b 0 * b 0 + b 1 * b 1 with hN
  -- coordinate functions
  set x : ι → ℝ := fun j => -b 1 * p j 0 + b 0 * p j 1 with hx
  set y : ι → ℝ := fun j => b 0 * p j 0 + b 1 * p j 1 with hy
  set ψ : ι → ℝ := fun j => b 0 * n j 0 + b 1 * n j 1 with hψ
  have hψi : ∀ j, ⟪b, n j⟫ = ψ j := fun j => by rw [virialFlat_ipf]
  have hSx : ∑ j, lam j * (ψ j * x j) = 0 := by
    have := hgrad u
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hψi, virialFlat_ipf, hu0, hu1]; simp only [hx]; ring
  have hSy : ∑ j, lam j * (ψ j * y j) = 0 := by
    have := hgrad b
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hψi, virialFlat_ipf]; simp only [hy]; ring
  have hS1 : ∑ j, lam j * ψ j = 0 := by
    have := congrArg (fun v : ℝ² => ⟪b, v⟫) hF
    simp only [inner_sum, inner_smul_right, inner_zero_right] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hψi]
  obtain ⟨jA, -, hA⟩ := Finset.exists_min_image Finset.univ x ⟨j0, Finset.mem_univ _⟩
  obtain ⟨jB, -, hB⟩ := Finset.exists_max_image Finset.univ x ⟨j0, Finset.mem_univ _⟩
  have hAj : ∀ j, x jA ≤ x j := fun j => hA j (Finset.mem_univ _)
  have hBj : ∀ j, x j ≤ x jB := fun j => hB j (Finset.mem_univ _)
  rcases (hAj jB).eq_or_lt with hAB | hAB
  · refine ⟨p jA, b, ?_, fun j _ _ => ?_⟩
    · intro h
      have h0 : b 0 = 0 := congrArg (fun v : ℝ² => v 0) h
      have h1 : b 1 = 0 := congrArg (fun v : ℝ² => v 1) h
      rw [h0, h1] at hN; rw [hN] at hNpos; simp at hNpos
    · have e1 := hAj j
      have e2 := hBj j
      have : x j = x jA := by linarith
      simp only [hx] at this
      simp only [cross2, PiLp.sub_apply]
      linarith
  · set D := x jB - x jA with hD
    have hDpos : 0 < D := by rw [hD]; linarith
    set E : ι → ℝ := fun j => (y j - y jA) * D - (x j - x jA) * (y jB - y jA) with hE
    have hkey : ∀ j, 0 ≤ lam j * (ψ j * E j) := by
      intro j
      refine mul_nonneg (hlam j) ?_
      have t1 := hout j jA
      have t2 := hout j jB
      rw [virialFlat_ipf] at t1 t2
      simp only [PiLp.sub_apply] at t1 t2
      have w1 : 0 ≤ x jB - x j := by linarith [hBj j]
      have w2 : 0 ≤ x j - x jA := by linarith [hAj j]
      have iden : N * ((x jB - x j) * (n j 0 * (p jA 0 - p j 0) + n j 1 * (p jA 1 - p j 1)) +
          (x j - x jA) * (n j 0 * (p jB 0 - p j 0) + n j 1 * (p jB 1 - p j 1))) =
          -(ψ j * E j) := by
        simp only [hN, hx, hy, hψ, hE, hD]; ring
      have : 0 ≤ -(N * ((x jB - x j) * (n j 0 * (p jA 0 - p j 0) + n j 1 * (p jA 1 - p j 1)) +
          (x j - x jA) * (n j 0 * (p jB 0 - p j 0) + n j 1 * (p jB 1 - p j 1)))) := by
        have a1 := mul_nonneg w1 (neg_nonneg.mpr t1)
        have a2 := mul_nonneg w2 (neg_nonneg.mpr t2)
        have := mul_nonneg hNpos.le (add_nonneg a1 a2)
        nlinarith
      rw [iden] at this
      linarith
    have hsum : ∑ j, lam j * (ψ j * E j) = 0 := by
      have h1 : ∑ j, lam j * (ψ j * E j) = ∑ j, (D * (lam j * (ψ j * y j))
          - (y jB - y jA) * (lam j * (ψ j * x j))
          - (y jA * D - x jA * (y jB - y jA)) * (lam j * ψ j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hE]; ring
      rw [h1]
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hSx, hSy, hS1]
      ring
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hkey j)).mp hsum
    refine ⟨p jA, p jB - p jA, ?_, fun j hl hψ' => ?_⟩
    · intro h
      have h0 : p jB 0 - p jA 0 = 0 := by simpa using congrArg (fun v : ℝ² => v 0) h
      have h1 : p jB 1 - p jA 1 = 0 := by simpa using congrArg (fun v : ℝ² => v 1) h
      have : D = 0 := by simp only [hD, hx]; linear_combination (-b 1) * h0 + (b 0) * h1
      linarith
    · have h0 := hz j (Finset.mem_univ _)
      rw [hψi] at hψ'
      have hE0 : E j = 0 := by
        rcases mul_eq_zero.mp h0 with h | h
        · exact absurd h hl
        · rcases mul_eq_zero.mp h with h | h
          · exact absurd h hψ'
          · exact h
      have : N * cross2 (p jB - p jA) (p j - p jA) = 0 := by
        have : N * cross2 (p jB - p jA) (p j - p jA) = -E j := by
          simp only [hN, hE, hD, hx, hy, cross2, PiLp.sub_apply]; ring
        rw [this, hE0]; ring
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hNpos.ne'
      · exact h

end Minimality
