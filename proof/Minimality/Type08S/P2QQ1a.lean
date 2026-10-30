module

public import Minimality.Type08S.P2QQ0b

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkQ / Q1a: helpers for density of the strict region (box around a moving centre).
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- `genPoly08 * gWc` as a polynomial. -/
noncomputable def genPolyC : MvPolynomial (Fin 6) ℝ :=
  genPoly08 * (MvPolynomial.X 5 * (1 - MvPolynomial.X 2 - MvPolynomial.X 3) -
    MvPolynomial.X 3 * (1 - MvPolynomial.X 4 - MvPolynomial.X 5))

theorem eval_genPolyC (θ : Fin 6 → ℝ) :
    MvPolynomial.eval θ genPolyC = MvPolynomial.eval θ genPoly08 * gWc θ := by
  simp [genPolyC, gWc]

theorem genPolyC_ne_zero : genPolyC ≠ 0 := by
  intro h
  have := congrArg (MvPolynomial.eval ![2, 3, 5, 7, 11, 13]) h
  rw [eval_genPolyC] at this
  simp [genPoly08, gWc] at this
  norm_num at this

/-- A nonzero polynomial is nonzero somewhere in every box. -/
theorem box_nonzero (P : MvPolynomial (Fin 6) ℝ) (hP : P ≠ 0) (c : Fin 6 → ℝ) (r : ℝ) (hr : 0 < r) :
    ∃ θ' : Fin 6 → ℝ, (∀ i, |θ' i - c i| < r) ∧ MvPolynomial.eval θ' P ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hP
  refine MvPolynomial.funext_set (R := ℝ) (σ := Fin 6) (p := P) (q := 0)
    (fun i => Set.Ioo (c i - r) (c i + r))
    (fun i => Set.Ioo_infinite (α := ℝ) (by linarith)) fun y hy => ?_
  rw [map_zero]
  refine hcon y fun i => ?_
  have := hy i (Set.mem_univ i)
  rw [abs_sub_lt_iff]; constructor <;> linarith [this.1, this.2]

theorem gWa_eq (x : Fin 6 → ℝ) : gWa x = x 2 - x 1 * x 2 - x 0 + x 0 * x 3 := by
  simp only [gWa]; ring

theorem gWb_eq (x : Fin 6 → ℝ) : gWb x = x 1 - x 1 * x 5 - x 4 + x 0 * x 4 := by
  simp only [gWb]; ring

theorem abs_prod_diff {p q p' q' r B : ℝ} (h1 : |p - p'| ≤ r) (h2 : |q| ≤ B) (h3 : |p'| ≤ B)
    (h4 : |q - q'| ≤ r) : |p * q - p' * q'| ≤ 2 * r * B := by
  have e : p * q - p' * q' = (p - p') * q + p' * (q - q') := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have hr : 0 ≤ r := (abs_nonneg _).trans h1
  have hB : 0 ≤ B := (abs_nonneg _).trans h2
  nlinarith [mul_le_mul h1 h2 (abs_nonneg _) hr, mul_le_mul h3 h4 (abs_nonneg _) hB]

theorem gWa_err {x c : Fin 6 → ℝ} {r B : ℝ} (hx : ∀ i, |x i - c i| ≤ r) (hxB : ∀ i, |x i| ≤ B)
    (hcB : ∀ i, |c i| ≤ B) : |gWa x - gWa c| ≤ r * (2 + 4 * B) := by
  rw [gWa_eq, gWa_eq]
  have p1 := abs_prod_diff (hx 1) (hxB 2) (hcB 1) (hx 2)
  have p2 := abs_prod_diff (hx 0) (hxB 3) (hcB 0) (hx 3)
  have q1 := abs_le.mp p1; have q2 := abs_le.mp p2
  have r1 := abs_le.mp (hx 2); have r2 := abs_le.mp (hx 0)
  rw [abs_le]
  constructor <;> nlinarith [q1.1, q1.2, q2.1, q2.2, r1.1, r1.2, r2.1, r2.2]

theorem gWb_err {x c : Fin 6 → ℝ} {r B : ℝ} (hx : ∀ i, |x i - c i| ≤ r) (hxB : ∀ i, |x i| ≤ B)
    (hcB : ∀ i, |c i| ≤ B) : |gWb x - gWb c| ≤ r * (2 + 4 * B) := by
  rw [gWb_eq, gWb_eq]
  have p1 := abs_prod_diff (hx 1) (hxB 5) (hcB 1) (hx 5)
  have p2 := abs_prod_diff (hx 0) (hxB 4) (hcB 0) (hx 4)
  have q1 := abs_le.mp p1; have q2 := abs_le.mp p2
  have r1 := abs_le.mp (hx 1); have r2 := abs_le.mp (hx 4)
  rw [abs_le]
  constructor <;> nlinarith [q1.1, q1.2, q2.1, q2.2, r1.1, r1.2, r2.1, r2.2]

/-- Core: approximants `θs n` within `t²` of the centre `θ + t v`, `t = 1/(n+1)`. -/
theorem seq_core (θ : Fin 6 → ℝ) (hθ : Ineq08w θ) (v : Fin 6 → ℝ) (a0 b0 : ℝ) (ha0 : 0 < a0)
    (hb0 : 0 < b0) (ha : ∀ t : ℝ, 0 < t → t ≤ 1 → a0 * t ≤ gWa (θ + t • v))
    (hb : ∀ t : ℝ, 0 < t → t ≤ 1 → b0 * t ≤ gWb (θ + t • v)) :
    ∃ θs : ℕ → Fin 6 → ℝ, Tendsto θs atTop (𝓝 θ) ∧
      (∀ n i, |θs n i - (θ i + (1 / ((n : ℝ) + 1)) * v i)| < (1 / ((n : ℝ) + 1)) ^ 2) ∧
      (∀ᶠ n in atTop, ∀ k, 0 < ineq08 (θs n) k) ∧
      ∀ n, MvPolynomial.eval (θs n) genPoly08 ≠ 0 := by
  have hbox : ∀ n : ℕ, ∃ θ' : Fin 6 → ℝ, (∀ i, |θ' i - (θ i + (1 / ((n : ℝ) + 1)) * v i)| <
      (1 / ((n : ℝ) + 1)) ^ 2) ∧ MvPolynomial.eval θ' genPolyC ≠ 0 := fun n =>
    box_nonzero _ genPolyC_ne_zero _ _ (by positivity)
  choose θs hθs hne using hbox
  have hne8 : ∀ n, MvPolynomial.eval (θs n) genPoly08 ≠ 0 := fun n h => by
    apply hne n; rw [eval_genPolyC, h, zero_mul]
  have hc : ∀ n, gWc (θs n) ≠ 0 := fun n h => by
    apply hne n; rw [eval_genPolyC, h, mul_zero]
  have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto θs atTop (𝓝 θ) := by
    refine tendsto_pi_nhds.mpr fun i => ?_
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨M, hM⟩ := exists_nat_one_div_lt (show 0 < ε / (2 + |v i|) by positivity)
    refine ⟨M, fun n hn => ?_⟩
    have h2 : 1 / ((n : ℝ) + 1) ≤ 1 / ((M : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hn 1
    set t := 1 / ((n : ℝ) + 1) with htdef
    have t0 : 0 < t := by positivity
    have t1 : t ≤ 1 := by
      rw [htdef, div_le_one (by positivity)]; have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
    have htM : t < ε / (2 + |v i|) := lt_of_le_of_lt h2 hM
    rw [lt_div_iff₀ (by positivity)] at htM
    have h1 := hθs n i
    rw [Real.dist_eq]
    have h3 : |t * v i| ≤ t * |v i| := by rw [abs_mul, abs_of_pos t0]
    have h4 := abs_sub_le (θs n i) (θ i + t * v i) (θ i)
    have h5 : |θ i + t * v i - θ i| = |t * v i| := by congr 1; ring
    nlinarith [abs_nonneg (v i)]
  refine ⟨θs, hlim, hθs, ?_, hne8⟩
  -- eventually strict
  have e1 : ∀ᶠ n in atTop, ∀ k, k ≠ 9 → k ≠ 10 → k ≠ 11 → 0 < ineq08 (θs n) k := by
    rw [eventually_all]; intro k
    by_cases h : k ≠ 9 ∧ k ≠ 10 ∧ k ≠ 11
    · exact ((((continuous_ineq08 k).tendsto θ).comp hlim).eventually
        (lt_mem_nhds (hθ.1 k h.1 h.2.1 h.2.2))).mono fun n hn _ _ _ => hn
    · exact Eventually.of_forall fun n h9 h10 h11 => absurd ⟨h9, h10, h11⟩ h
  set B : ℝ := ∑ i, (|θ i| + |v i|) + 1 with hB
  have hBi : ∀ i, |θ i| + |v i| + 1 ≤ B := fun i => by
    have := Finset.single_le_sum (f := fun i => |θ i| + |v i|) (fun j _ => by positivity)
      (Finset.mem_univ i)
    rw [hB]; linarith
  have hB0 : 0 ≤ B := by have := hBi 0; have := abs_nonneg (θ 0); have := abs_nonneg (v 0); linarith
  obtain ⟨M, hM⟩ := exists_nat_one_div_lt (show 0 < min (a0 / (2 + 4 * B)) (b0 / (2 + 4 * B)) by
    positivity)
  filter_upwards [e1, eventually_ge_atTop M] with n hn hnM
  have hU := gWU_neg_w0 (θs n) hn
  have t0 : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have h2 : 1 / ((n : ℝ) + 1) ≤ 1 / ((M : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hnM 1
  set t := 1 / ((n : ℝ) + 1) with htdef
  have t1 : t ≤ 1 := by
    rw [htdef, div_le_one (by positivity)]; have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have htM := lt_of_le_of_lt h2 hM
  have htA : t < a0 / (2 + 4 * B) := lt_of_lt_of_le htM (min_le_left _ _)
  have htB : t < b0 / (2 + 4 * B) := lt_of_lt_of_le htM (min_le_right _ _)
  rw [lt_div_iff₀ (by positivity)] at htA htB
  have hx : ∀ i, |θs n i - (θ + t • v) i| ≤ t ^ 2 := fun i => by
    have := hθs n i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; exact this.le
  have hcB1 : ∀ i, |(θ + t • v) i| ≤ B - 1 := fun i => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_pos t0]
    nlinarith [hBi i, abs_nonneg (v i), abs_nonneg (θ i)]
  have hcB : ∀ i, |(θ + t • v) i| ≤ B := fun i => by linarith [hcB1 i]
  have hxB : ∀ i, |θs n i| ≤ B := fun i => by
    have := hx i
    have h3 := abs_sub_abs_le_abs_sub (θs n i) ((θ + t • v) i)
    have : t ^ 2 ≤ 1 := by nlinarith
    linarith [hcB1 i, hx i]
  have eA := gWa_err hx hxB hcB
  have eB := gWb_err hx hxB hcB
  have pa := ha t t0 t1
  have pb := hb t t0 t1
  have gA : 0 < gWa (θs n) := by
    have := (abs_le.mp eA).1
    nlinarith
  have gB : 0 < gWb (θs n) := by
    have := (abs_le.mp eB).1
    nlinarith
  intro k
  by_cases h9 : k = 9
  · subst h9; simp only [ineq08]; simp; nlinarith
  by_cases h10 : k = 10
  · subst h10; simp only [ineq08]; simp; nlinarith
  by_cases h11 : k = 11
  · subst h11; simp only [ineq08]; simp; exact sq_pos_of_ne_zero (hc n)
  exact hn k h9 h10 h11

end Type08Sp
end Minimality
