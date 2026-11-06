module

public import Mathlib
public import MinimalityExtra

/-!
# Theorem T (torque forms): the algebraic content (proof of `TorqueForms`)

Symmetry, shear invariance for balanced loads, the torque identity
`Σ det (A x, A⁻ᵀ f) = √det g · tr (g⁻¹ S_f)` for `g = Aᵀ A`, and the signature and
horizontal-double-normal criterion of a parallel ray. All 2 x 2 computations.
-/

@[expose] public section

namespace MinimalityExtra

open Matrix

theorem inv2 (a b c d : ℝ) (h : a * d - b * c ≠ 0) :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ =
      !![d / (a * d - b * c), -b / (a * d - b * c); -c / (a * d - b * c), a / (a * d - b * c)] := by
  rw [Matrix.inv_def, Matrix.adjugate_fin_two_of, Matrix.det_fin_two_of, Ring.inverse_eq_inv']
  ext i j; fin_cases i <;> fin_cases j <;> simp [div_eq_inv_mul]

theorem torqueTerm_add_x (x x' f : Fin 2 → ℝ) :
    torqueTerm (x + x') f = torqueTerm x f + torqueTerm x' f := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [torqueTerm, tfJ] <;> ring

theorem torqueTerm_smul_x (c : ℝ) (x f : Fin 2 → ℝ) :
    torqueTerm (c • x) f = c • torqueTerm x f := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [torqueTerm, tfJ] <;> ring

theorem sum_torqueTerm_f {n : ℕ} (x : Fin 2 → ℝ) (g : Fin n → Fin 2 → ℝ) :
    ∑ i, torqueTerm x (g i) = torqueTerm x (∑ i, g i) := by
  ext r s; fin_cases r <;> fin_cases s <;>
    simp [torqueTerm, Matrix.sum_apply, Finset.sum_add_distrib, Finset.sum_div, Finset.mul_sum,
      Finset.sum_mul, Fin.sum_univ_two, mul_comm] <;>
    (try rw [← Finset.sum_add_distrib, Finset.sum_div])

theorem torqueTerm_smul_f (c : ℝ) (x f : Fin 2 → ℝ) :
    torqueTerm x (c • f) = c • torqueTerm x f := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [torqueTerm, tfJ] <;> ring

theorem torqueTerm_zero_f (x : Fin 2 → ℝ) : torqueTerm x 0 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [torqueTerm]

theorem torqueForm_symm {n : ℕ} (x f : Fin n → Fin 2 → ℝ) : (torqueForm x f)ᵀ = torqueForm x f := by
  ext i j
  simp only [torqueForm, Matrix.transpose_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  fin_cases i <;> fin_cases j <;> simp [torqueTerm] <;> ring

theorem torqueForm_shear {n : ℕ} (x f : Fin n → Fin 2 → ℝ) (z : Fin n → ℝ)
    (h1 : ∑ i, f i = 0) (h2 : ∑ i, z i • f i = 0) (a b : Fin 2 → ℝ) :
    torqueForm (fun i => x i + z i • a + b) f = torqueForm x f := by
  have e : ∀ i, torqueTerm (x i + z i • a + b) (f i) =
      torqueTerm (x i) (f i) + torqueTerm a (z i • f i) + torqueTerm b (f i) := by
    intro i
    rw [torqueTerm_add_x, torqueTerm_add_x, torqueTerm_smul_x, torqueTerm_smul_f]
  unfold torqueForm
  simp only [e, Finset.sum_add_distrib, sum_torqueTerm_f, h1, h2, torqueTerm_zero_f, add_zero]
theorem term_b (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.det ≠ 0) (x f : Fin 2 → ℝ) :
    tfDet (A *ᵥ x) ((Aᵀ)⁻¹ *ᵥ f) = A.det * ((Aᵀ * A)⁻¹ * torqueTerm x f).trace := by
  rw [Matrix.mul_inv_rev]
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, A = !![a, b; c, d] := ⟨_, _, _, _, Matrix.eta_fin_two A⟩
  have hd : a * d - b * c ≠ 0 := by simpa [Matrix.det_fin_two_of] using hA
  have hd' : a * d - c * b ≠ 0 := by rwa [mul_comm c b]
  have hT : (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ = !![a, c; b, d] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [hT, inv2 _ _ _ _ hd, inv2 _ _ _ _ hd']
  simp [tfDet, torqueTerm, tfJ, Matrix.trace_fin_two, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.mul_apply, Matrix.det_fin_two_of]
  field_simp
  ring

theorem torque_frame {n : ℕ} (x f : Fin n → Fin 2 → ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : 0 < A.det) :
    ∑ i, tfDet (A *ᵥ x i) ((Aᵀ)⁻¹ *ᵥ f i) =
      Real.sqrt (Aᵀ * A).det * ((Aᵀ * A)⁻¹ * torqueForm x f).trace := by
  have h : Real.sqrt (Aᵀ * A).det = A.det := by
    rw [Matrix.det_mul, Matrix.det_transpose, ← sq, Real.sqrt_sq hA.le]
  rw [h, torqueForm, Matrix.mul_sum, Matrix.trace_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => term_b A hA.ne' _ _

theorem parallel_ray (nn q c : Fin 2 → ℝ) (m : ℝ) (hm : m ≠ 0) (hn : nn ⬝ᵥ (q - c) ≠ 0) :
    (torqueForm ![q, c] ![m • nn, (-m) • nn]).det < 0 ∧
    ∀ g : Matrix (Fin 2) (Fin 2) ℝ, g.PosDef →
      (((g⁻¹ * torqueForm ![q, c] ![m • nn, (-m) • nn]).trace = 0) ↔
        tfJ nn ⬝ᵥ (g *ᵥ (q - c)) = 0) := by
  have hS : torqueForm ![q, c] ![m • nn, (-m) • nn] =
      torqueTerm q (m • nn) + torqueTerm c ((-m) • nn) := by
    simp [torqueForm, Fin.sum_univ_two]
  rw [hS]
  have hn' : nn 0 * (q 0 - c 0) + nn 1 * (q 1 - c 1) ≠ 0 := by
    simpa [dotProduct, Fin.sum_univ_two] using hn
  refine ⟨?_, ?_⟩
  · have key : (torqueTerm q (m • nn) + torqueTerm c ((-m) • nn)).det =
        -(m * (nn 0 * (q 0 - c 0) + nn 1 * (q 1 - c 1))) ^ 2 / 4 := by
      simp only [Matrix.det_fin_two, torqueTerm, tfJ]
      simp
      ring
    rw [key]
    have := (sq_pos_iff).2 (mul_ne_zero hm hn')
    linarith
  · intro g hg
    have hD := hg.det_pos
    have hh : ∀ i j, g i j = g j i := fun i j => by
      have := hg.isHermitian.apply j i
      simpa using this
    obtain ⟨p, r, r', s, rfl⟩ : ∃ p r r' s, g = !![p, r; r', s] :=
      ⟨_, _, _, _, Matrix.eta_fin_two g⟩
    have hr : r' = r := by simpa using hh 1 0
    subst hr
    simp only [Matrix.det_fin_two_of] at hD
    have hD' : p * s - r' * r' ≠ 0 := hD.ne'
    have hD'' : p * s - r' * r' ≠ 0 := hD'
    rw [inv2 _ _ _ _ (by simpa [mul_comm] using hD')]
    have key : (!![s / (p * s - r' * r'), -r' / (p * s - r' * r'); -r' / (p * s - r' * r'), p / (p * s - r' * r')]
          * (torqueTerm q (m • nn) + torqueTerm c ((-m) • nn))).trace =
        (-m / (p * s - r' * r')) * (tfJ nn ⬝ᵥ (!![p, r'; r', s] *ᵥ (q - c))) := by
      simp [torqueTerm, tfJ, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.mulVec, dotProduct]
      field_simp
      ring
    rw [key]
    have hk : (-m / (p * s - r' * r')) ≠ 0 := div_ne_zero (neg_ne_zero.2 hm) hD'
    simp [hk]

theorem torqueForms : TorqueForms :=
  ⟨fun _ x f => torqueForm_symm x f,
   fun _ x f z h1 h2 a b => torqueForm_shear x f z h1 h2 a b,
   fun _ x f A hA => torque_frame x f A hA,
   fun nn q c m hm hn => parallel_ray nn q c m hm hn⟩

end MinimalityExtra
