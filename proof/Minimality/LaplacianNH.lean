module

public import Minimality.RimCellConv

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace Matrix

namespace Minimality.LaplacianNH

/-! ### 1.1 Laplacian form of a positive-definite-by-scaling Gram matrix -/

/-- Graph Laplacian of the triangle with conductances `g`. -/
def lap (g : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) : ℝ :=
  if i = j then ∑ k, (if k = i then 0 else g i k) else -g i j

/-- `C* G C* = diag(c*) + L(γ')` with `γ'_ij = γ_ij c*_i c*_j`, `γ = -G`, from `G c* = 1`. -/
theorem scaled_gram_eq_lap (G : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)
    (hc : G *ᵥ c = fun _ => 1) (i j : Fin 3) :
    c i * G i j * c j =
      (if i = j then c i else 0) + lap (fun a b => -G a b * c a * c b) i j := by
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  have h2 := congrFun hc 2
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1 h2
  fin_cases i <;> fin_cases j <;>
    simp only [lap, Fin.sum_univ_three, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Fin.reduceEq, ite_true, ite_false, add_zero, zero_add] <;>
    first | ring1 | linear_combination (c 0) * h0 | linear_combination (c 1) * h1 | linear_combination (c 2) * h2

/-- Hatted quadratic form: `x^T G x = sum c_i y_i^2 + sum_{i<j} (-G_ij) c_i c_j (y_i - y_j)^2`
for `x = c * y`, when `G` is symmetric and `G c = 1`. -/
theorem quad_hat (G : Matrix (Fin 3) (Fin 3) ℝ) (hs : G.IsSymm) (c y : Fin 3 → ℝ)
    (hc : G *ᵥ c = fun _ => 1) :
    (fun i => c i * y i) ⬝ᵥ (G *ᵥ fun i => c i * y i) =
      c 0 * y 0 ^ 2 + c 1 * y 1 ^ 2 + c 2 * y 2 ^ 2
        + (-G 0 1) * c 0 * c 1 * (y 0 - y 1) ^ 2 + (-G 0 2) * c 0 * c 2 * (y 0 - y 2) ^ 2
        + (-G 1 2) * c 1 * c 2 * (y 1 - y 2) ^ 2 := by
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  have h2 := congrFun hc 2
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1 h2 ⊢
  have s10 : G 1 0 = G 0 1 := hs.apply 0 1
  have s20 : G 2 0 = G 0 2 := hs.apply 0 2
  have s21 : G 2 1 = G 1 2 := hs.apply 1 2
  simp only [s10, s20, s21] at h0 h1 h2 ⊢
  linear_combination (c 0 * y 0 ^ 2) * h0 + (c 1 * y 1 ^ 2) * h1 + (c 2 * y 2 ^ 2) * h2

/-- Corollary: `c > 0`, `G c = 1`, `G` symmetric with nonpositive off-diagonal (`γ ≥ 0`)
give `G` positive definite (as a quadratic form). -/
theorem posDef_of_scaling (G : Matrix (Fin 3) (Fin 3) ℝ) (hs : G.IsSymm) (c : Fin 3 → ℝ)
    (hc : G *ᵥ c = fun _ => 1) (hpos : ∀ i, 0 < c i)
    (h01 : G 0 1 ≤ 0) (h02 : G 0 2 ≤ 0) (h12 : G 1 2 ≤ 0)
    (x : Fin 3 → ℝ) (hx : x ≠ 0) : 0 < x ⬝ᵥ (G *ᵥ x) := by
  set y : Fin 3 → ℝ := fun i => x i / c i with hy
  have hxy : x = fun i => c i * y i := by
    funext i; simp only [hy]; field_simp [(hpos i).ne']
  have key := quad_hat G hs c y hc
  rw [← hxy] at key
  rw [key]
  have : ∃ i, y i ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    apply hx; funext i; rw [hxy]; simp [hcon i]
  have a0 := hpos 0
  have a1 := hpos 1
  have a2 := hpos 2
  have t0 : 0 ≤ (-G 0 1) * c 0 * c 1 * (y 0 - y 1) ^ 2 := by
    have := neg_nonneg.mpr h01; positivity
  have t1 : 0 ≤ (-G 0 2) * c 0 * c 2 * (y 0 - y 2) ^ 2 := by
    have := neg_nonneg.mpr h02; positivity
  have t2 : 0 ≤ (-G 1 2) * c 1 * c 2 * (y 1 - y 2) ^ 2 := by
    have := neg_nonneg.mpr h12; positivity
  obtain ⟨i, hi⟩ := this
  have hy2 : 0 < y i ^ 2 := by positivity
  fin_cases i
  · have : 0 < c 0 * y 0 ^ 2 := mul_pos a0 hy2
    have : 0 ≤ c 1 * y 1 ^ 2 := by positivity
    have : 0 ≤ c 2 * y 2 ^ 2 := by positivity
    linarith
  · have : 0 < c 1 * y 1 ^ 2 := mul_pos a1 hy2
    have : 0 ≤ c 0 * y 0 ^ 2 := by positivity
    have : 0 ≤ c 2 * y 2 ^ 2 := by positivity
    linarith
  · have : 0 < c 2 * y 2 ^ 2 := mul_pos a2 hy2
    have : 0 ≤ c 0 * y 0 ^ 2 := by positivity
    have : 0 ≤ c 1 * y 1 ^ 2 := by positivity
    linarith

/-! ### 3.1 Lemma NH: no horizontal double normal at an obtuse apex pair -/

section NH
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Screen inner product at the view `u`: `<p,q> - <p,u><q,u>/<u,u>` (projection orthogonal to u). -/
noncomputable def scr (u p q : V) : ℝ := ⟪p, q⟫ - ⟪p, u⟫ * ⟪q, u⟫ / ⟪u, u⟫

/-- **Lemma NH.** Ends `J, M` above the apex `1` at the view `u` (`z = <., u>`), with
`<x_J - x_1, x_M - x_1> <= 0` (the Gram entry `G_JM <= 0`): the screen inner product of the two
edges is strictly negative. -/
theorem scr_neg_of_apex_pair {u eJ eM : V} (hu : u ≠ 0) (hJ : 0 < ⟪eJ, u⟫) (hM : 0 < ⟪eM, u⟫)
    (hJM : ⟪eM, eJ⟫ ≤ 0) : scr u eM eJ < 0 := by
  have : 0 < ⟪u, u⟫ := real_inner_self_pos.mpr hu
  unfold scr
  have : 0 < ⟪eM, u⟫ * ⟪eJ, u⟫ / ⟪u, u⟫ := by positivity
  linarith

/-- **Lemma NH, foot form.** Under the same hypotheses the foot of `x_M` on the screen line
through `x_1` and `x_J` has parameter `t = <eM,eJ>_scr / <eJ,eJ>_scr < 0` (strictly beyond the apex,
away from `J`), and `eJ` is not screen-null. -/
theorem foot_param_neg {u eJ eM : V} (hu : u ≠ 0) (hJ : 0 < ⟪eJ, u⟫) (hM : 0 < ⟪eM, u⟫)
    (hJM : ⟪eM, eJ⟫ ≤ 0) : 0 < scr u eJ eJ ∧ scr u eM eJ / scr u eJ eJ < 0 := by
  have hneg := scr_neg_of_apex_pair hu hJ hM hJM
  have hpos : 0 < scr u eJ eJ := by
    have huu : 0 < ⟪u, u⟫ := real_inner_self_pos.mpr hu
    unfold scr
    have h := real_inner_mul_inner_self_le eJ u
    rw [sub_pos, div_lt_iff₀ huu]
    refine lt_of_le_of_ne (by nlinarith [h]) ?_
    intro heq
    -- equality in Cauchy-Schwarz: eJ parallel to u, then eM . eJ > 0 contradicts hJM
    have hpar : ⟪eJ, u⟫ * ⟪eJ, u⟫ = ⟪eJ, eJ⟫ * ⟪u, u⟫ := heq
    have hz : ⟪⟪u, u⟫ • eJ - ⟪eJ, u⟫ • u, ⟪u, u⟫ • eJ - ⟪eJ, u⟫ • u⟫ = 0 := by
      simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
        real_inner_comm eJ u, RCLike.conj_to_real]
      nlinarith [hpar]
    have hv : ⟪u, u⟫ • eJ - ⟪eJ, u⟫ • u = 0 := inner_self_eq_zero.mp hz
    have huu' : 0 < ⟪u, u⟫ := huu
    have : ⟪eM, ⟪u, u⟫ • eJ - ⟪eJ, u⟫ • u⟫ = 0 := by rw [hv]; simp
    rw [inner_sub_right, inner_smul_right, inner_smul_right] at this
    nlinarith [mul_pos hM hJ, mul_nonpos_of_nonneg_of_nonpos huu.le hJM]
  exact ⟨hpos, div_neg_of_neg_of_pos hneg hpos⟩

end NH

/-! ### 1.2 Lemma CE (corner equator) as a corollary of PP* -/

open Minimality.RimCell in
/-- **Lemma CE.** Rim `y` of the solid `Y` (a cell rim, injective, `k >= 3`), a view `ρ` in the
closure of the open cell, the end direction `e_K = Pi.single K 1` in the closure of `convSet y`
(shape-only condition (i): `e_K ∈ cl Conv(R)`), and `(G ρ)_K < 0` with `G = E^T E`
(condition (ii): end `K` strictly below the apex at `ρ`). Then `Y.image (emb E)` is Rupert. -/
theorem rupert_of_corner_equator {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det)
    (y : ZMod k → Fin 3 → ℝ) (hy : Function.Injective y) (Y : Finset (Fin 3 → ℝ))
    (hyY : ∀ i, y i ∈ Y) {ρ : Fin 3 → ℝ} (K : Fin 3)
    (hρ : ρ ∈ closure (cellSet Y y)) (hK : Pi.single K (1 : ℝ) ∈ closure (convSet y))
    (hii : ((Eᵀ * E) *ᵥ ρ) K < 0) :
    IsRupert (Y.image (emb E)) := by
  refine isRupert_of_conv_pair_closure hk E hE y hy Y hyY hρ hK ?_
  have hsym : (Eᵀ * E)ᵀ = Eᵀ * E := by simp [Matrix.transpose_mul]
  have : ((Eᵀ * E) *ᵥ Pi.single K (1 : ℝ)) ⬝ᵥ ρ = ((Eᵀ * E) *ᵥ ρ) K := by
    have hM : ∀ i j, (Eᵀ * E) i j = (Eᵀ * E) j i := fun i j => (congrFun (congrFun hsym i) j).symm
    rw [Matrix.mulVec_single_one]
    simp only [dotProduct, Matrix.mulVec, Matrix.col_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [hM i K]
  rw [this]; exact hii

end Minimality.LaplacianNH
