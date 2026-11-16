module

public import Mathlib
public import Minimality.CornerLift

/-!
# Existence of a maximal lift (obtuse condition only)

Source: `CORNER-EQ-IDEAS3-FABLE.md` 1.2 (the Roof Lemma), without walls.  Namespace `Minimality.CornerEQ`,
`Fin 3`.  `Q G ν = (liftM ν)ᵀ G (liftM ν)` is the Gram matrix of the lifted apex.

* `liftSet G = {ν ≥ 0 | all off-diagonal entries of Q G ν are ≤ 0}`: the feasible lifts.
* `liftSet_isClosed`, `zero_mem_liftSet` (`G` obtuse), `liftSet_isBounded` (`G` positive definite, via
  `exists_quad_lower`: `m ‖ν‖² ≤ νᵀGν`), `liftSet_isCompact`.
* `exists_maximal_lift`: a `ν* ∈ liftSet G` maximizing `N = ∑ ν`.
* `liftM_mul` / `gram_comp`: lifting twice is lifting once, `liftM ν * liftM ν' = liftM (ν + liftM ν *ᵥ ν')`;
  the total has sum `N + (1 + N) N'` (`sum_liftTotal`).
* `maximal_no_further_lift`: at a maximizer no `ν' ≥ 0`, `ν' ≠ 0` gives a feasible lift of `G' = Q G ν*`.
* `lift_one_nonpos`: `lift_one_zero` with `G_ab ≤ 0` instead of `= 0` (so it also covers "no zero").
* `lift_posDef`: `Q G ν` is positive definite for `G` positive definite, `0 ≤ ∑ ν`.
* `exists_maximal_lift_two_zeros` (main): for `G` positive definite and obtuse there is a maximizer `ν*`
  of `N` on `liftSet G`, `G' = Q G ν*` is positive definite, and `G'` has two zero off-diagonal entries
  `G'_ab = G'_ac = 0` (`a b c` pairwise distinct).

Symmetry of `G` is only used through `PosDef`; obtuse is needed only for nonemptiness.
-/

set_option autoImplicit false

namespace Minimality.CornerEQ

open Finset Matrix

@[expose] public section

/-- The feasible lifts: `ν ≥ 0` with all off-diagonal entries of the lifted Gram matrix `≤ 0`. -/
def liftSet (G : Matrix (Fin 3) (Fin 3) ℝ) : Set (Fin 3 → ℝ) :=
  {ν | 0 ≤ ν ∧ ∀ a b, a ≠ b → ((liftM ν)ᵀ * G * liftM ν) a b ≤ 0}

theorem continuous_liftM : Continuous liftM :=
  continuous_pi fun i => continuous_pi fun j => by
    simp only [liftM_apply]
    exact continuous_const.add (continuous_apply i)

theorem continuous_liftGram (G : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 3) :
    Continuous fun ν : Fin 3 → ℝ => ((liftM ν)ᵀ * G * liftM ν) a b :=
  (((continuous_liftM.matrix_transpose).matrix_mul continuous_const).matrix_mul
    continuous_liftM).matrix_elem a b

theorem liftSet_isClosed (G : Matrix (Fin 3) (Fin 3) ℝ) : IsClosed (liftSet G) := by
  have : liftSet G = Set.Ici 0 ∩ ⋂ a, ⋂ b, ⋂ (_ : a ≠ b),
      {ν : Fin 3 → ℝ | ((liftM ν)ᵀ * G * liftM ν) a b ≤ 0} := by
    ext ν; simp [liftSet]
  rw [this]
  exact isClosed_Ici.inter (isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_iInter fun _ => isClosed_le (continuous_liftGram G a b) continuous_const)

theorem zero_mem_liftSet (G : Matrix (Fin 3) (Fin 3) ℝ) (hobt : ∀ a b, a ≠ b → G a b ≤ 0) :
    (0 : Fin 3 → ℝ) ∈ liftSet G := by
  refine ⟨le_rfl, fun a b hab => ?_⟩
  have : liftM (0 : Fin 3 → ℝ) = 1 := by simp [liftM]
  simpa [this] using hobt a b hab

/-- Positive definiteness gives a quadratic lower bound. -/
theorem exists_quad_lower (G : Matrix (Fin 3) (Fin 3) ℝ) (hpd : G.PosDef) :
    ∃ m : ℝ, 0 < m ∧ ∀ ν : Fin 3 → ℝ, m * ‖ν‖ ^ 2 ≤ ν ⬝ᵥ (G *ᵥ ν) := by
  have hcont : Continuous fun ν : Fin 3 → ℝ => ν ⬝ᵥ (G *ᵥ ν) := by
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    fun_prop
  have hne : (Metric.sphere (0 : Fin 3 → ℝ) 1).Nonempty := NormedSpace.sphere_nonempty.2 zero_le_one
  obtain ⟨x0, hx0, hmin⟩ := (isCompact_sphere (0 : Fin 3 → ℝ) 1).exists_isMinOn hne hcont.continuousOn
  have hx0n : ‖x0‖ = 1 := by simpa using hx0
  have hx0ne : x0 ≠ 0 := by rintro rfl; simp at hx0n
  have hm : 0 < x0 ⬝ᵥ (G *ᵥ x0) := by simpa using hpd.dotProduct_mulVec_pos hx0ne
  refine ⟨_, hm, fun ν => ?_⟩
  by_cases hν : ν = 0
  · simp [hν]
  have ht : 0 < ‖ν‖ := norm_pos_iff.2 hν
  set u := ‖ν‖⁻¹ • ν with hu
  have hun : ‖u‖ = 1 := by rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ ht.ne']
  have hνu : ν = ‖ν‖ • u := by rw [hu, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  have h1 : x0 ⬝ᵥ (G *ᵥ x0) ≤ u ⬝ᵥ (G *ᵥ u) := hmin (by simpa using hun)
  have h2 : ν ⬝ᵥ (G *ᵥ ν) = ‖ν‖ * ‖ν‖ * (u ⬝ᵥ (G *ᵥ u)) := by
    conv_lhs => rw [hνu]
    simp [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]; ring
  rw [h2]
  nlinarith [mul_pos ht ht]

theorem liftSet_isBounded (G : Matrix (Fin 3) (Fin 3) ℝ) (hpd : G.PosDef) :
    Bornology.IsBounded (liftSet G) := by
  have hG : G.IsSymm := by
    have := hpd.isHermitian
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using this
  obtain ⟨m, hm, hq⟩ := exists_quad_lower G hpd
  set B : ℝ := ∑ a, ∑ j, |G a j| with hB
  set D : ℝ := |G 0 1 + G 0 2 + G 1 2| + 2 * B with hD
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have key : ∀ ν ∈ liftSet G, ‖ν‖ ≤ D / (3 * m) + 1 := by
    rintro ν ⟨hν0, hν⟩
    set r := ‖ν‖ with hr
    have hr0 : 0 ≤ r := norm_nonneg _
    have hterm : ∀ a j, -(|G a j| * r) ≤ G a j * ν j := by
      intro a j
      have h1 : |ν j| ≤ r := by simpa [Real.norm_eq_abs] using norm_le_pi_norm ν j
      have : |G a j * ν j| ≤ |G a j| * r := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      linarith [neg_abs_le (G a j * ν j)]
    have hsum : -(B * r) ≤ ∑ a, (G *ᵥ ν) a := by
      have e : -(B * r) = ∑ a, ∑ j, -(|G a j| * r) := by
        simp [hB, Finset.sum_neg_distrib, Finset.sum_mul]
      rw [e]
      refine Finset.sum_le_sum fun a _ => ?_
      simp only [Matrix.mulVec, dotProduct]
      exact Finset.sum_le_sum fun j _ => hterm a j
    have h01 := hν 0 1 (by decide)
    have h02 := hν 0 2 (by decide)
    have h12 := hν 1 2 (by decide)
    rw [lift_gram_apply G hG] at h01 h02 h12
    have hq3 := hq ν
    rw [← hr] at hq3
    simp only [Fin.sum_univ_three] at hsum
    have hC := neg_abs_le (G 0 1 + G 0 2 + G 1 2)
    have hmain : 3 * (m * r ^ 2) ≤ -(G 0 1 + G 0 2 + G 1 2) + 2 * B * r := by linarith
    have hDnn : 0 ≤ D / (3 * m) := by positivity
    by_cases hr1 : r ≤ 1
    · linarith
    · push Not at hr1
      have hab : -(G 0 1 + G 0 2 + G 1 2) ≤ |G 0 1 + G 0 2 + G 1 2| * r := by
        nlinarith [neg_abs_le (G 0 1 + G 0 2 + G 1 2), abs_nonneg (G 0 1 + G 0 2 + G 1 2)]
      have h3 : 3 * m * r * r ≤ D * r := by rw [hD]; nlinarith
      have h4 : 3 * m * r ≤ D := le_of_mul_le_mul_right h3 (by linarith)
      have : r ≤ D / (3 * m) := by rw [le_div_iff₀ (by positivity)]; linarith
      linarith
  refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨D / (3 * m) + 1, fun ν hν => ?_⟩
  simpa using key ν hν

theorem liftSet_isCompact (G : Matrix (Fin 3) (Fin 3) ℝ) (hpd : G.PosDef) :
    IsCompact (liftSet G) :=
  Metric.isCompact_of_isClosed_isBounded (liftSet_isClosed G) (liftSet_isBounded G hpd)

theorem exists_maximal_lift (G : Matrix (Fin 3) (Fin 3) ℝ) (hpd : G.PosDef)
    (hobt : ∀ a b, a ≠ b → G a b ≤ 0) :
    ∃ ν ∈ liftSet G, ∀ ν' ∈ liftSet G, ∑ i, ν' i ≤ ∑ i, ν i := by
  obtain ⟨ν, hν, hmax⟩ := (liftSet_isCompact G hpd).exists_isMaxOn ⟨0, zero_mem_liftSet G hobt⟩
    (continuous_finsetSum _ fun i _ => continuous_apply i).continuousOn
  exact ⟨ν, hν, fun ν' hν' => hmax hν'⟩

/-! ### Composition -/

theorem liftM_mul (ν ν' : Fin 3 → ℝ) :
    liftM ν * liftM ν' = liftM (ν + liftM ν *ᵥ ν') := by
  ext i j
  simp only [Matrix.mul_apply, liftM_apply, Fin.sum_univ_three, Pi.add_apply, liftM_mulVec]
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem gram_comp (G : Matrix (Fin 3) (Fin 3) ℝ) (ν ν' : Fin 3 → ℝ) :
    (liftM ν')ᵀ * ((liftM ν)ᵀ * G * liftM ν) * liftM ν'
      = (liftM (ν + liftM ν *ᵥ ν'))ᵀ * G * liftM (ν + liftM ν *ᵥ ν') := by
  rw [← liftM_mul, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

theorem sum_liftTotal (ν ν' : Fin 3 → ℝ) :
    ∑ i, (ν + liftM ν *ᵥ ν') i = ∑ i, ν i + (1 + ∑ i, ν i) * ∑ i, ν' i := by
  simp only [Pi.add_apply, liftM_mulVec, Finset.sum_add_distrib, ← Finset.sum_mul]
  ring

theorem liftTotal_mem (G : Matrix (Fin 3) (Fin 3) ℝ) {ν ν' : Fin 3 → ℝ} (hν : ν ∈ liftSet G)
    (hν' : 0 ≤ ν')
    (hf : ∀ a b, a ≠ b → ((liftM ν')ᵀ * ((liftM ν)ᵀ * G * liftM ν) * liftM ν') a b ≤ 0) :
    ν + liftM ν *ᵥ ν' ∈ liftSet G :=
  ⟨add_nonneg hν.1 (liftM_mulVec_nonneg ν ν' hν.1 hν'), fun a b hab => by
    rw [← gram_comp]; exact hf a b hab⟩

/-- At a maximizer of `N` on `liftSet G` there is no further feasible lift. -/
theorem maximal_no_further_lift (G : Matrix (Fin 3) (Fin 3) ℝ) {ν : Fin 3 → ℝ} (hν : ν ∈ liftSet G)
    (hmax : ∀ ν' ∈ liftSet G, ∑ i, ν' i ≤ ∑ i, ν i) {ν' : Fin 3 → ℝ} (hν' : 0 ≤ ν')
    (hf : ∀ a b, a ≠ b → ((liftM ν')ᵀ * ((liftM ν)ᵀ * G * liftM ν) * liftM ν') a b ≤ 0) :
    ν' = 0 := by
  have h := hmax _ (liftTotal_mem G hν hν' hf)
  rw [sum_liftTotal] at h
  have hN : 0 ≤ ∑ i, ν i := Finset.sum_nonneg fun i _ => hν.1 i
  have hN' : 0 ≤ ∑ i, ν' i := Finset.sum_nonneg fun i _ => hν' i
  have h0 : ∑ i, ν' i = 0 := by nlinarith
  ext i
  exact (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hν' i).1 h0 i (Finset.mem_univ i)

/-! ### The shape at a maximum -/

/-- `lift_one_zero` with `G_ab ≤ 0` in place of `G_ab = 0` (the same proof). -/
theorem lift_one_nonpos (G : Matrix (Fin 3) (Fin 3) ℝ) (hG : G.IsSymm) {a b c : Fin 3}
    (h0 : G a b ≤ 0) (h1 : G a c < 0) (h2 : G b c < 0) :
    ∃ ε : ℝ, 0 < ε ∧ ((liftM (Pi.single c ε))ᵀ * G * liftM (Pi.single c ε)) a b < 0
      ∧ ((liftM (Pi.single c ε))ᵀ * G * liftM (Pi.single c ε)) a c < 0
      ∧ ((liftM (Pi.single c ε))ᵀ * G * liftM (Pi.single c ε)) b c < 0 := by
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
  have hcc'' : ε * G c c < m := by
    have := le_abs_self (G c c); nlinarith
  have key : ∀ i j, ((liftM (Pi.single c ε))ᵀ * G * liftM (Pi.single c ε)) i j
      = G i j + ε * G i c + ε * G j c + ε * ε * G c c := by
    intro i j
    rw [lift_gram_apply G hG]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    ring
  refine ⟨ε, he0, ?_, ?_, ?_⟩
  · rw [key]
    have : G a c + G b c + ε * G c c < 0 := by linarith
    nlinarith [mul_neg_of_pos_of_neg he0 this]
  · rw [key]
    have : G a c + ε * G c c < 0 := by linarith
    nlinarith [mul_neg_of_pos_of_neg (by linarith : 0 < 1 + ε) this]
  · rw [key]
    have : G b c + ε * G c c < 0 := by linarith
    nlinarith [mul_neg_of_pos_of_neg (by linarith : 0 < 1 + ε) this]

theorem lift_gram_symm (G : Matrix (Fin 3) (Fin 3) ℝ) (hG : G.IsSymm) (ν : Fin 3 → ℝ) (a b : Fin 3) :
    ((liftM ν)ᵀ * G * liftM ν) a b = ((liftM ν)ᵀ * G * liftM ν) b a := by
  rw [lift_gram_apply G hG, lift_gram_apply G hG, hG.apply a b]
  ring

/-- Off-diagonal nonpositivity of a symmetric matrix from the three entries of a listing. -/
theorem offdiag_of_three (P : Matrix (Fin 3) (Fin 3) ℝ) (hP : ∀ i j, P i j = P j i) {a b c : Fin 3}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (h1 : P a b ≤ 0) (h2 : P a c ≤ 0) (h3 : P b c ≤ 0) :
    ∀ x y, x ≠ y → P x y ≤ 0 := by
  intro x y hxy
  have hx : x = a ∨ x = b ∨ x = c := by omega
  have hy : y = a ∨ y = b ∨ y = c := by omega
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hxy
    | assumption
    | (rw [hP]; assumption)

/-- If `H` (symmetric, obtuse) admits no feasible lift, two off-diagonal entries vanish.  Positive
definiteness is not needed here. -/
theorem exists_two_zeros_of_maximal (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm)
    (hnp : ∀ a b, a ≠ b → H a b ≤ 0)
    (hmax : ∀ ν' : Fin 3 → ℝ, 0 ≤ ν' →
      (∀ a b, a ≠ b → ((liftM ν')ᵀ * H * liftM ν') a b ≤ 0) → ν' = 0) :
    ∃ a b c : Fin 3, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ H a b = 0 ∧ H a c = 0 := by
  have hs : ∀ i j, H i j = H j i := fun i j => hH.apply j i
  have nolift : ∀ {a b c : Fin 3}, a ≠ b → a ≠ c → b ≠ c → H a b ≤ 0 → H a c < 0 → H b c < 0 →
      False := by
    intro a b c hab hac hbc h0 h1 h2
    obtain ⟨ε, hε, e1, e2, e3⟩ := lift_one_nonpos H hH h0 h1 h2
    have hnn : 0 ≤ (Pi.single c ε : Fin 3 → ℝ) := fun i => by
      by_cases h : i = c
      · subst h; simpa using hε.le
      · simp [h]
    have := hmax _ hnn (offdiag_of_three _ (lift_gram_symm H hH _) hab hac hbc e1.le e2.le e3.le)
    have := congrFun this c
    simp at this
    exact hε.ne' this
  by_contra hno
  have n01 : ¬ (H 0 1 = 0 ∧ H 0 2 = 0) := fun h => hno ⟨0, 1, 2, by decide, by decide, by decide, h⟩
  have n02 : ¬ (H 1 0 = 0 ∧ H 1 2 = 0) := fun h => hno ⟨1, 0, 2, by decide, by decide, by decide, h⟩
  have n12 : ¬ (H 2 0 = 0 ∧ H 2 1 = 0) := fun h => hno ⟨2, 0, 1, by decide, by decide, by decide, h⟩
  have x := hnp 0 1 (by decide)
  have y := hnp 0 2 (by decide)
  have z := hnp 1 2 (by decide)
  have e10 := hs 1 0
  have e20 := hs 2 0
  have e21 := hs 2 1
  rcases x.lt_or_eq with x | x <;> rcases y.lt_or_eq with y | y <;> rcases z.lt_or_eq with z | z
  · exact nolift (a := 0) (b := 1) (c := 2) (by decide) (by decide) (by decide) x.le y z
  · exact nolift (a := 1) (b := 2) (c := 0) (by decide) (by decide) (by decide) z.le (by linarith)
      (by linarith)
  · exact nolift (a := 0) (b := 2) (c := 1) (by decide) (by decide) (by decide) y.le x (by linarith)
  · exact n12 ⟨by linarith, by linarith⟩
  · exact nolift (a := 0) (b := 1) (c := 2) (by decide) (by decide) (by decide) x.le y z
  · exact n02 ⟨by linarith, by linarith⟩
  · exact n01 ⟨by linarith, by linarith⟩
  · exact n01 ⟨by linarith, by linarith⟩

theorem lift_posDef (G : Matrix (Fin 3) (Fin 3) ℝ) (hpd : G.PosDef) (ν : Fin 3 → ℝ)
    (hν : 0 ≤ ∑ i, ν i) : ((liftM ν)ᵀ * G * liftM ν).PosDef := by
  have hinj : Function.Injective (liftM ν).mulVec := fun x y h => by
    have := congrArg (liftInv ν).mulVec h
    simpa [Matrix.mulVec_mulVec, liftInv_mul_liftM ν hν] using this
  have := hpd.conjTranspose_mul_mul_same hinj
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this

/-- **Existence of a maximal lift with two zeros** (obtuse condition only, no walls). -/
theorem exists_maximal_lift_two_zeros (G : Matrix (Fin 3) (Fin 3) ℝ) (hpd : G.PosDef)
    (hobt : ∀ a b, a ≠ b → G a b ≤ 0) :
    ∃ ν ∈ liftSet G, (∀ ν' ∈ liftSet G, ∑ i, ν' i ≤ ∑ i, ν i) ∧
      ((liftM ν)ᵀ * G * liftM ν).PosDef ∧
      ∃ a b c : Fin 3, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ((liftM ν)ᵀ * G * liftM ν) a b = 0 ∧
        ((liftM ν)ᵀ * G * liftM ν) a c = 0 := by
  have hG : G.IsSymm := by
    have := hpd.isHermitian
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using this
  obtain ⟨ν, hν, hmax⟩ := exists_maximal_lift G hpd hobt
  have hN : 0 ≤ ∑ i, ν i := Finset.sum_nonneg fun i _ => hν.1 i
  refine ⟨ν, hν, hmax, lift_posDef G hpd ν hN, ?_⟩
  have hs : ((liftM ν)ᵀ * G * liftM ν).IsSymm := by
    simp [Matrix.IsSymm, Matrix.transpose_mul, hG.eq, Matrix.mul_assoc]
  exact exists_two_zeros_of_maximal _ hs hν.2 fun ν' hν' hf =>
    maximal_no_further_lift G hν hmax hν' hf

end

end Minimality.CornerEQ
