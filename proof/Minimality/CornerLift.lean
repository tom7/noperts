module

public import Mathlib
public import Minimality.CornerFibreGen

/-!
# The lift of a corner apex and Lemma R1 (maximal apexes)

Source: `CORNER-EQ-IDEAS3-FABLE.md` 1.1 (the lift) and 1.2 (Lemma R1).  Namespace `Minimality.CornerEQ`,
`Fin 3`.

## The lift (1.1)

For `ν ≥ 0` put `N = ∑ ν` and `M = liftM ν = 1 + ν 1ᵀ` (`liftM_apply`: `M i j = δ_ij + ν i`).
* `lift_gram_apply`: for symmetric `G`, `(Mᵀ G M)_ab = G_ab + (G ν)_a + (G ν)_b + νᵀ G ν`.
* `liftInv`: `M⁻¹ = 1 - (1 + N)⁻¹ • ν 1ᵀ` (`liftM_mul_liftInv`, `liftInv_mul_liftM`, `liftM_inv`),
  and `1ᵀ M = (1 + N) 1ᵀ` (`one_vecMul_liftM`).
* `liftY` (the map `y ↦ M⁻¹ y` on difference vectors, NOT on points; the point map is `liftPt` below):
  `y'_j = y_j - ν_j (∑ y) / (1 + N)` (`liftY_apply`) and
  `∑ y' = ∑ y / (1 + N)` (`sum_liftY`); `liftM_mulVec_liftY` gives back `M y' = y`.
* Cone: `ρ' ≥ 0 → M ρ' ≥ 0`, `ρ' > 0 → M ρ' > 0` (`liftM_mulVec_nonneg`, `liftM_mulVec_pos`):
  `C(x') = M (orthant) ⊆ C(x₆)`, interior into interior.
* Geometry, in any real vector space `V` (use `ℝ³`): the frame `E : Fin 3 → V` (`x_a = x₆ + E a`),
  `x' = x₆ - ∑ ν_a E a`.  `lift_point`: `(1 + N) x₆ = x' + ∑ ν_a x_a`, i.e. `x₆ ∈ conv(x', x_a)` with
  weights `(1, ν_a)/(1 + N)`; `lift_frame`: `x_a - x' = ∑_b M_ba E b` (the frame at `x'` is `E M`).

## Lemma R1 (1.2), the first-order part

For symmetric `G`:
* `lift_one_zero` (one zero): `G_ab = 0`, `G_ac < 0`, `G_bc < 0` give `ε > 0` with the three off-diagonal
  entries of `G'` for `ν = ε e_c` all `< 0`.  Explicit `ε`.  No distinctness of the indices is needed
  (the hypotheses already force the entries to be off-diagonal in the intended sense); here `a b c` are
  arbitrary.
* `lift_two_zeros` (two zeros, maximality; `a b c` pairwise distinct, so they list `Fin 3`): `G_ab = G_ac = 0`, `G` positive definite, `ν ≥ 0`, `ν ≠ 0`:
  NOT both `G'_ab ≤ 0` and `G'_ac ≤ 0`.  **This is exact, not first-order only**: the full quadratic term
  `νᵀ G ν > 0` only helps, and the first-order argument of 1.2 (multiply the two linear inequalities
  by `ν_b`, `ν_c` and add: `G_aa ν_a (ν_b + ν_c) + Q_bc(ν_b, ν_c) ≤ -(ν_b + ν_c) νᵀGν`) runs verbatim on
  the exact entries.  Hypotheses `G_bc < 0` and the nonpositivity of the other off-diagonals are not
  needed (the identity is sign free in `G_bc`; only `ν_b, ν_c ≥ 0` and positive definiteness enter), and
  the conclusion needs only the two entries `ab`, `ac`.

## The point map and the transfer

* `liftPt ν y = M⁻¹ (y + ν)`: frame coordinates at `x'` of the point with frame coordinates `y` at `x₆`
  (`liftPt_eq`: `liftY ν y + (1 + N)⁻¹ ν`; `liftPt_single`: fixes the unit vectors;
  `liftM_mulVec_liftPt`: `M (liftPt ν y) = y + ν`; `lift_coords`: `x' + ∑ (M liftPt y)_b E b = x₆ + ∑ y_b E b`;
  `lift_view`: the view `∑ ρ'_a (x_a - x')` is `∑ (M ρ')_b E b`).
* The transfer of leaves from `x'` to `x₆` is in `CornerTransfer.lean` (`cornerLeaf_lift`).
-/

set_option autoImplicit false

namespace Minimality.CornerEQ

open Finset Matrix

@[expose] public section

/-- `M = 1 + ν 1ᵀ`, i.e. `M i j = δ_ij + ν i`. -/
def liftM (ν : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ := 1 + vecMulVec ν (fun _ => 1)

/-- The inverse `1 - (1 + N)⁻¹ ν 1ᵀ`. -/
noncomputable def liftInv (ν : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  1 - (1 + ∑ i, ν i)⁻¹ • vecMulVec ν (fun _ => 1)

/-- The lift of a *difference vector*: `M⁻¹ y`.  (The lift of a *point* `y` of the frame coordinates is
`liftPt ν y = M⁻¹ (y + ν) = liftY ν y + (1 + N)⁻¹ ν`, see below.) -/
noncomputable def liftY (ν y : Fin 3 → ℝ) : Fin 3 → ℝ := liftInv ν *ᵥ y

theorem liftM_apply (ν : Fin 3 → ℝ) (i j : Fin 3) :
    liftM ν i j = (if i = j then 1 else 0) + ν i := by
  simp [liftM, vecMulVec_apply, Matrix.one_apply]

theorem liftM_mulVec (ν ρ : Fin 3 → ℝ) (i : Fin 3) :
    (liftM ν *ᵥ ρ) i = ρ i + ν i * ∑ j, ρ j := by
  simp [liftM, Matrix.mulVec, dotProduct, vecMulVec_apply, Fin.sum_univ_three,
    Matrix.one_apply, mul_add]
  fin_cases i <;> simp <;> ring

theorem lift_gram_apply (G : Matrix (Fin 3) (Fin 3) ℝ) (hG : G.IsSymm) (ν : Fin 3 → ℝ) (a b : Fin 3) :
    ((liftM ν)ᵀ * G * liftM ν) a b
      = G a b + (G *ᵥ ν) a + (G *ᵥ ν) b + ν ⬝ᵥ (G *ᵥ ν) := by
  have h10 : G 1 0 = G 0 1 := hG.apply 0 1
  have h20 : G 2 0 = G 0 2 := hG.apply 0 2
  have h21 : G 2 1 = G 1 2 := hG.apply 1 2
  simp only [Matrix.mul_apply, Matrix.transpose_apply, liftM_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]
  fin_cases a <;> fin_cases b <;> simp [h10, h20, h21] <;> ring

theorem liftM_mul_liftInv (ν : Fin 3 → ℝ) (hν : 0 ≤ ∑ i, ν i) :
    liftM ν * liftInv ν = 1 := by
  have h : (1 + ∑ i, ν i) ≠ 0 := (by linarith : (0:ℝ) < 1 + ∑ i, ν i).ne'
  ext i j
  simp only [liftM, liftInv, Matrix.mul_apply, Fin.sum_univ_three, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, Matrix.one_apply, Fin.sum_univ_three,
    smul_eq_mul] at *
  fin_cases i <;> fin_cases j <;> simp at * <;> field_simp <;> ring

theorem liftInv_mul_liftM (ν : Fin 3 → ℝ) (hν : 0 ≤ ∑ i, ν i) :
    liftInv ν * liftM ν = 1 := by
  have h : (1 + ∑ i, ν i) ≠ 0 := (by linarith : (0:ℝ) < 1 + ∑ i, ν i).ne'
  ext i j
  simp only [liftM, liftInv, Matrix.mul_apply, Fin.sum_univ_three, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, Matrix.one_apply, Fin.sum_univ_three,
    smul_eq_mul] at *
  fin_cases i <;> fin_cases j <;> simp at * <;> field_simp <;> ring

theorem liftM_inv (ν : Fin 3 → ℝ) (hν : 0 ≤ ∑ i, ν i) : (liftM ν)⁻¹ = liftInv ν :=
  Matrix.inv_eq_right_inv (liftM_mul_liftInv ν hν)

theorem one_vecMul_liftM (ν : Fin 3 → ℝ) :
    (fun _ : Fin 3 => (1 : ℝ)) ᵥ* liftM ν = (1 + ∑ i, ν i) • fun _ => 1 := by
  ext j
  simp [vecMul, dotProduct, liftM_apply, Fin.sum_univ_three]
  fin_cases j <;> simp <;> ring

theorem vecMulVec_one_mulVec (ν y : Fin 3 → ℝ) (j : Fin 3) :
    ((vecMulVec ν fun _ => (1 : ℝ)) *ᵥ y) j = ν j * ∑ i, y i := by
  simp [Matrix.mulVec, dotProduct, vecMulVec_apply, Finset.mul_sum]

theorem liftY_apply (ν y : Fin 3 → ℝ) (j : Fin 3) :
    liftY ν y j = y j - ν j * (∑ i, y i) / (1 + ∑ i, ν i) := by
  simp [liftY, liftInv, Matrix.sub_mulVec, Matrix.smul_mulVec, vecMulVec_one_mulVec]
  ring

theorem sum_liftY (ν y : Fin 3 → ℝ) (hν : 0 ≤ ∑ i, ν i) :
    ∑ j, liftY ν y j = (∑ i, y i) / (1 + ∑ i, ν i) := by
  have h : (1 + ∑ i, ν i) ≠ 0 := (by linarith : (0:ℝ) < 1 + ∑ i, ν i).ne'
  simp only [liftY_apply ν y, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_mul]
  field_simp
  ring

theorem liftM_mulVec_liftY (ν y : Fin 3 → ℝ) (hν : 0 ≤ ∑ i, ν i) :
    liftM ν *ᵥ liftY ν y = y := by
  rw [liftY, mulVec_mulVec, liftM_mul_liftInv ν hν, one_mulVec]

theorem liftM_mulVec_nonneg (ν ρ' : Fin 3 → ℝ) (hν : 0 ≤ ν) (hρ : 0 ≤ ρ') :
    0 ≤ liftM ν *ᵥ ρ' := fun i => by
  rw [liftM_mulVec]
  have h1 := hν i
  have h2 := hρ i
  have h3 : 0 ≤ ∑ j, ρ' j := Finset.sum_nonneg fun j _ => hρ j
  have := mul_nonneg h1 h3
  linarith

theorem liftM_mulVec_pos (ν ρ' : Fin 3 → ℝ) (hν : 0 ≤ ν) (hρ : ∀ i, 0 < ρ' i) :
    ∀ i, 0 < (liftM ν *ᵥ ρ') i := fun i => by
  rw [liftM_mulVec]
  have h1 := hν i
  have h2 := hρ i
  have h3 : 0 ≤ ∑ j, ρ' j := Finset.sum_nonneg fun j _ => (hρ j).le
  have := mul_nonneg h1 h3
  linarith

section Geometry

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- `x' = x₆ - ∑ ν_a E a`. -/
def liftPoint (x6 : V) (E : Fin 3 → V) (ν : Fin 3 → ℝ) : V := x6 - ∑ a, ν a • E a

theorem lift_point (x6 : V) (E : Fin 3 → V) (ν : Fin 3 → ℝ) :
    (1 + ∑ a, ν a) • x6 = liftPoint x6 E ν + ∑ a, ν a • (x6 + E a) := by
  simp only [liftPoint, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, add_smul, one_smul]
  abel

theorem lift_point' (x6 : V) (E : Fin 3 → V) (ν : Fin 3 → ℝ) (hν : 0 ≤ ∑ a, ν a) :
    x6 = (1 + ∑ a, ν a)⁻¹ • (liftPoint x6 E ν + ∑ a, ν a • (x6 + E a)) := by
  have h : (1 + ∑ a, ν a) ≠ 0 := by positivity
  rw [← lift_point, smul_smul, inv_mul_cancel₀ h, one_smul]

theorem lift_frame (x6 : V) (E : Fin 3 → V) (ν : Fin 3 → ℝ) (a : Fin 3) :
    (x6 + E a) - liftPoint x6 E ν = ∑ b, liftM ν b a • E b := by
  simp only [liftPoint, liftM_apply, add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul]
  simp [Finset.sum_ite_eq']

theorem lift_view (x6 : V) (E : Fin 3 → V) (ν ρ' : Fin 3 → ℝ) :
    ∑ a, ρ' a • ((x6 + E a) - liftPoint x6 E ν) = ∑ b, (liftM ν *ᵥ ρ') b • E b := by
  simp only [lift_frame, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Matrix.mulVec, dotProduct, Finset.sum_smul]
  exact Finset.sum_congr rfl fun a _ => by rw [mul_comm]

end Geometry

/-! ### The point map -/

/-- The lift of a point with frame coordinates `y` (at `x₆`) to its frame coordinates at `x'`:
`M⁻¹ (y + ν)`.  It fixes the unit vectors (`liftPt_single`: the points `x_a` are the same points). -/
noncomputable def liftPt (ν y : Fin 3 → ℝ) : Fin 3 → ℝ := liftInv ν *ᵥ (y + ν)

theorem liftPt_eq (ν y : Fin 3 → ℝ) (hν : 0 ≤ ∑ i, ν i) : liftPt ν y = liftY ν y + (1 + ∑ i, ν i)⁻¹ • ν := by
  ext j
  simp [liftPt, liftY, liftInv, Matrix.sub_mulVec, Matrix.smul_mulVec, vecMulVec_one_mulVec,
    Matrix.mulVec_add]
  have h : (1 + ∑ i, ν i) ≠ 0 := (by linarith : (0:ℝ) < 1 + ∑ i, ν i).ne'
  field_simp
  ring

theorem liftM_mulVec_liftPt (ν y : Fin 3 → ℝ) (hν : 0 ≤ ∑ i, ν i) :
    liftM ν *ᵥ liftPt ν y = y + ν := by
  rw [liftPt, mulVec_mulVec, liftM_mul_liftInv ν hν, one_mulVec]

theorem liftPt_single (ν : Fin 3 → ℝ) (hν : 0 ≤ ∑ i, ν i) (a : Fin 3) :
    liftPt ν (Pi.single a 1) = Pi.single a 1 := by
  have h2 : liftM ν *ᵥ (Pi.single a 1 : Fin 3 → ℝ) = Pi.single a 1 + ν := by
    ext i
    rw [liftM_mulVec]
    simp [Pi.single_apply]
  rw [liftPt, ← h2, mulVec_mulVec, liftInv_mul_liftM ν hν, one_mulVec]

section Geometry2

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- `O` seen from `x'` (frame `E M`, coordinates `liftPt`) is `O` seen from `x₆`. -/
theorem lift_coords (x6 : V) (E : Fin 3 → V) (ν y : Fin 3 → ℝ) (hν : 0 ≤ ∑ i, ν i) :
    liftPoint x6 E ν + ∑ b, (liftM ν *ᵥ liftPt ν y) b • E b = x6 + ∑ b, y b • E b := by
  rw [liftM_mulVec_liftPt ν y hν]
  simp only [liftPoint, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  abel

end Geometry2

/-! ### Lemma R1 -/

/-- Listing `Fin 3` by three indices. -/
theorem sum3 {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Fin 3 → ℝ) :
    ∑ i, f i = f a + f b + f c := by
  have : (Finset.univ : Finset (Fin 3)) = {a, b, c} := by
    ext i; simp; omega
  rw [this, Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
    Finset.sum_singleton]
  ring

theorem lift_one_zero (G : Matrix (Fin 3) (Fin 3) ℝ) (hG : G.IsSymm) {a b c : Fin 3}
    (h0 : G a b = 0) (h1 : G a c < 0) (h2 : G b c < 0) :
    ∃ ε : ℝ, 0 < ε ∧ ((liftM (Pi.single c ε))ᵀ * G * liftM (Pi.single c ε)) a b < 0
      ∧ ((liftM (Pi.single c ε))ᵀ * G * liftM (Pi.single c ε)) a c < 0
      ∧ ((liftM (Pi.single c ε))ᵀ * G * liftM (Pi.single c ε)) b c < 0 := by
  have hs : ∀ i j, G i j = G j i := fun i j => (hG.apply j i)
  set m := -max (G a c) (G b c) with hm
  have hm0 : 0 < m := by
    have := max_lt h1 h2; simp only [hm]; linarith
  have hma : G a c ≤ -m := by have := le_max_left (G a c) (G b c); simp only [hm]; linarith
  have hmb : G b c ≤ -m := by have := le_max_right (G a c) (G b c); simp only [hm]; linarith
  set ε := m / (|G c c| + 1) with hε
  have hpos : 0 < |G c c| + 1 := by positivity
  have he0 : 0 < ε := by positivity
  have hcc : ε * |G c c| < m := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ hpos]; nlinarith [abs_nonneg (G c c)]
  have hcc' : -m < ε * G c c := by
    have := neg_abs_le (G c c); nlinarith
  have hcc'' : ε * G c c < m := by
    have := le_abs_self (G c c); nlinarith
  have key : ∀ i j, ((liftM (Pi.single c ε))ᵀ * G * liftM (Pi.single c ε)) i j
      = G i j + ε * G i c + ε * G j c + ε * ε * G c c := by
    intro i j
    rw [lift_gram_apply G hG]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    ring
  refine ⟨ε, he0, ?_, ?_, ?_⟩
  · rw [key, h0]
    have : G a c + G b c + ε * G c c < 0 := by linarith
    nlinarith [mul_neg_of_pos_of_neg he0 this]
  · rw [key]
    have : G a c + ε * G c c < 0 := by linarith
    nlinarith [mul_neg_of_pos_of_neg (by linarith : 0 < 1 + ε) this]
  · rw [key]
    have : G b c + ε * G c c < 0 := by linarith
    nlinarith [mul_neg_of_pos_of_neg (by linarith : 0 < 1 + ε) this]

theorem lift_two_zeros (G : Matrix (Fin 3) (Fin 3) ℝ) (hG : G.IsSymm) (hpd : G.PosDef) {a b c : Fin 3}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (h1 : G a b = 0) (h2 : G a c = 0)
    (ν : Fin 3 → ℝ) (hν : 0 ≤ ν) (hν0 : ν ≠ 0) :
    ¬ (((liftM ν)ᵀ * G * liftM ν) a b ≤ 0 ∧ ((liftM ν)ᵀ * G * liftM ν) a c ≤ 0) := by
  have hs : ∀ i j, G i j = G j i := fun i j => (hG.apply j i)
  have hba : G b a = 0 := by rw [hs, h1]
  have hca : G c a = 0 := by rw [hs, h2]
  have hcb : G c b = G b c := hs c b
  have mv : ∀ (w : Fin 3 → ℝ) (i : Fin 3), (G *ᵥ w) i = G i a * w a + G i b * w b + G i c * w c := by
    intro w i
    simp only [Matrix.mulVec, dotProduct]; exact sum3 hab hac hbc _
  have dp : ∀ w : Fin 3 → ℝ, w ⬝ᵥ (G *ᵥ w) = w a * (G *ᵥ w) a + w b * (G *ᵥ w) b + w c * (G *ᵥ w) c := by
    intro w; simp only [dotProduct]; exact sum3 hab hac hbc _
  have hpos : ∀ w : Fin 3 → ℝ, w ≠ 0 → 0 < w ⬝ᵥ (G *ᵥ w) := fun w hw => by
    simpa using hpd.dotProduct_mulVec_pos hw
  have hnn : ∀ w : Fin 3 → ℝ, 0 ≤ w ⬝ᵥ (G *ᵥ w) := fun w => by
    by_cases hw : w = 0
    · simp [hw]
    · exact (hpos w hw).le
  have hnn' : ∀ w : Fin 3 → ℝ, 0 ≤ w a * (G *ᵥ w) a + w b * (G *ᵥ w) b + w c * (G *ᵥ w) c :=
    fun w => by rw [← dp]; exact hnn w
  set q := ν ⬝ᵥ (G *ᵥ ν) with hq
  have hGaa : 0 < G a a := by
    have := hpos (Pi.single a 1) (by simp)
    rw [dp] at this
    simp [mv, hab.symm, hac.symm] at this
    simpa using this
  -- the (b,c) quadratic form
  have hQ : 0 ≤ G b b * ν b ^ 2 + 2 * G b c * ν b * ν c + G c c * ν c ^ 2 := by
    have := hnn' (Function.update ν a 0)
    simp [mv, hab.symm, hac.symm, hcb] at this
    nlinarith [this]
  have hqe : q = G a a * ν a ^ 2 + (G b b * ν b ^ 2 + 2 * G b c * ν b * ν c + G c c * ν c ^ 2) := by
    rw [hq, dp]
    simp only [mv, hba, hca, h1, h2, hcb]
    ring
  have hqpos : 0 < q := hpos ν hν0
  have e1 : ((liftM ν)ᵀ * G * liftM ν) a b
      = G a a * ν a + G b b * ν b + G b c * ν c + q := by
    rw [lift_gram_apply G hG, mv, mv]; simp only [hba, h1, h2, hq]; ring
  have e2 : ((liftM ν)ᵀ * G * liftM ν) a c
      = G a a * ν a + G b c * ν b + G c c * ν c + q := by
    rw [lift_gram_apply G hG, mv, mv]; simp only [hca, h1, h2, hcb, hq]; ring
  rintro ⟨l1, l2⟩
  rw [e1] at l1
  rw [e2] at l2
  have ha := hν a
  have hb := hν b
  have hc := hν c
  simp only [Pi.zero_apply] at ha hb hc
  have comb : ν b * (G a a * ν a + G b b * ν b + G b c * ν c + q)
      + ν c * (G a a * ν a + G b c * ν b + G c c * ν c + q)
      = G a a * ν a * (ν b + ν c) + (G b b * ν b ^ 2 + 2 * G b c * ν b * ν c + G c c * ν c ^ 2)
        + q * (ν b + ν c) := by ring
  have le0 : ν b * (G a a * ν a + G b b * ν b + G b c * ν c + q)
      + ν c * (G a a * ν a + G b c * ν b + G c c * ν c + q) ≤ 0 := by
    have := mul_nonpos_of_nonneg_of_nonpos hb l1
    have := mul_nonpos_of_nonneg_of_nonpos hc l2
    linarith
  rcases (add_nonneg hb hc).eq_or_lt with h0 | hp
  · have hb0 : ν b = 0 := by linarith
    have hc0 : ν c = 0 := by linarith
    have hqe' : q = G a a * ν a ^ 2 := by rw [hqe, hb0, hc0]; ring
    have hna : ν a = 0 := by
      rw [hb0, hc0] at l1
      nlinarith [mul_nonneg hGaa.le ha, mul_nonneg (mul_nonneg hGaa.le ha) ha]
    apply hν0
    ext i
    have hi : i = a ∨ i = b ∨ i = c := by omega
    rcases hi with h | h | h <;> simp [h, hna, hb0, hc0]
  · have h3 : 0 < q * (ν b + ν c) := mul_pos hqpos hp
    nlinarith [mul_nonneg (mul_nonneg hGaa.le ha) (add_nonneg hb hc)]

end

end Minimality.CornerEQ
